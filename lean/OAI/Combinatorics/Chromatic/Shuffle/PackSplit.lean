import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.SymmetricSpace
import OAI.Combinatorics.Chromatic.Walls.Average

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
open ElementaryPositivity.SeparatedSymmetry
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {d e : I → ℕ}

noncomputable def packSplit (A : Cut d e) (i : I) :
    Fin (d i) ⊕ Fin (e i) ≃ Fin (d i+e i) :=
  (Equiv.sumCongr (leftEnum A i) ((rightEnum A i).trans
    ((Equiv.refl _).subtypeEquiv (by intro x; simp only [Finset.mem_compl, Equiv.refl_apply])))).trans
      (Equiv.sumCompl fun x => x ∈ (A i).val)

omit [Fintype I] [DecidableEq I] in
@[simp] lemma packSplit_inl (A : Cut d e) (i : I) (x : Fin (d i)) :
    packSplit A i (Sum.inl x) = leftEnum A i x := rfl
omit [Fintype I] [DecidableEq I] in
@[simp] lemma packSplit_inr (A : Cut d e) (i : I) (x : Fin (e i)) :
    packSplit A i (Sum.inr x) = rightEnum A i x := rfl

noncomputable def cutSplit (A : Cut d e) :
    ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ≃ (Σi,Fin (d i+e i)) :=
  (Equiv.sigmaSumDistrib _ _).symm.trans (Equiv.sigmaCongrRight (packSplit A))

omit [Fintype I] [DecidableEq I] in
@[simp] lemma cutSplit_inl (A : Cut d e) (x : Σi,Fin (d i)) :
    cutSplit A (Sum.inl x) = leftInput A x := rfl
omit [Fintype I] [DecidableEq I] in
@[simp] lemma cutSplit_inr (A : Cut d e) (x : Σi,Fin (e i)) :
    cutSplit A (Sum.inr x) = rightInput A x := rfl

omit [Fintype I] [DecidableEq I] in
lemma cutSplit_change (A B : Cut d e) :
    (cutSplit A).symm.trans (cutSplit B) =
      packAction (fun i => Fin (d i+e i)) (fun i => (packSplit A i).symm.trans (packSplit B i)) := by
  apply Equiv.ext
  intro x
  obtain ⟨y,rfl⟩ := (cutSplit A).surjective x
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  cases y with
  | inl x =>
    rcases x with ⟨i,x⟩
    change (⟨i,packSplit B i (Sum.inl x)⟩ : Σi,Fin (d i+e i)) =
      ⟨i,packSplit B i ((packSplit A i).symm (packSplit A i (Sum.inl x)))⟩
    rw [Equiv.symm_apply_apply]
  | inr x =>
    rcases x with ⟨i,x⟩
    change (⟨i,packSplit B i (Sum.inr x)⟩ : Σi,Fin (d i+e i)) =
      ⟨i,packSplit B i ((packSplit A i).symm (packSplit A i (Sum.inr x)))⟩
    rw [Equiv.symm_apply_apply]

omit [Fintype I] [DecidableEq I] in
lemma split_symmetric_independent (A B : Cut d e) (F : S (d+e)) :
    rename (cutSplit B) (rename (cutSplit A).symm F.val) = F.val := by
  rw [rename_rename]
  change rename ((cutSplit A).symm.trans (cutSplit B)) F.val = _
  rw [cutSplit_change]
  exact F.property _

omit [Fintype I] [DecidableEq I] in
lemma cutSplit_action (A : Cut d e)
    (σ : (∀i,Equiv.Perm (Fin (d i))) × (∀i,Equiv.Perm (Fin (e i)))) :
    (cutSplit A).symm.trans ((sumAction (packAction (fun i=>Fin (d i)))
      (packAction (fun i=>Fin (e i))) σ).trans (cutSplit A)) =
      packAction (fun i=>Fin (d i+e i)) (fun i =>
        (packSplit A i).symm.trans ((Equiv.sumCongr (σ.1 i) (σ.2 i)).trans (packSplit A i))) := by
  apply Equiv.ext
  intro x
  obtain ⟨y,rfl⟩ := (cutSplit A).surjective x
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  cases y with
  | inl x =>
    rcases x with ⟨i,x⟩
    change (⟨i,packSplit A i (Sum.inl (σ.1 i x))⟩ : Σi,Fin (d i+e i)) =
      ⟨i,packSplit A i ((Equiv.sumCongr (σ.1 i) (σ.2 i))
        ((packSplit A i).symm (packSplit A i (Sum.inl x))))⟩
    rw [Equiv.symm_apply_apply]; rfl
  | inr x =>
    rcases x with ⟨i,x⟩
    change (⟨i,packSplit A i (Sum.inr (σ.2 i x))⟩ : Σi,Fin (d i+e i)) =
      ⟨i,packSplit A i ((Equiv.sumCongr (σ.1 i) (σ.2 i))
        ((packSplit A i).symm (packSplit A i (Sum.inr x))))⟩
    rw [Equiv.symm_apply_apply]; rfl

omit [Fintype I] [DecidableEq I] in
lemma split_symmetric (A : Cut d e) (F : S (d+e)) :
    ∀ σ, rename (sumAction (packAction (fun i=>Fin (d i))) (packAction (fun i=>Fin (e i))) σ)
      (rename (cutSplit A).symm F.val) = rename (cutSplit A).symm F.val := by
  intro σ
  apply rename_injective (cutSplit A) (cutSplit A).injective
  simp only [rename_rename]
  have h := F.property (fun i => (packSplit A i).symm.trans
    ((Equiv.sumCongr (σ.1 i) (σ.2 i)).trans (packSplit A i)))
  change rename (packAction (fun i=>Fin (d i+e i)) (fun i => (packSplit A i).symm.trans
    ((Equiv.sumCongr (σ.1 i) (σ.2 i)).trans (packSplit A i)))) F.val = F.val at h
  rw [← cutSplit_action A σ] at h
  convert h using 1
  · rfl
  · simp

lemma split_symmetric_span (A : Cut d e) (F : S (d+e)) :
    rename (cutSplit A).symm F.val ∈ Submodule.span ℚ
      {q | ∃ (f : S d) (g : S e), q = rename Sum.inl f.val * rename Sum.inr g.val} := by
  have h := invariant_separated_span (packAction (fun i=>Fin (d i)))
    (packAction (fun i=>Fin (e i))) (rename (cutSplit A).symm F.val) (split_symmetric A F)
  apply Submodule.span_mono _ h
  rintro q ⟨f,g,hf,hg,rfl⟩
  exact ⟨⟨f,hf⟩,⟨g,hg⟩,rfl⟩

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {d e : I → ℕ}

noncomputable def firstCut (d e : I → ℕ) : Cut d e := fun i =>
  ⟨Finset.univ.map (Fin.castAddEmb (e i)), by simp⟩

noncomputable def localizeS (d : I → ℕ) :
    S d →ₗ[ℚ] FractionRing (MvPolynomial (Σi,Fin (d i)) ℚ) where
  toFun f := algebraMap _ _ f.val
  map_add' := by intro f g; exact map_add _ f.val g.val
  map_smul' := by
    intro r f
    change algebraMap _ _ (r • f.val) = r • algebraMap _ _ f.val
    exact map_rat_smul (algebraMap (MvPolynomial (Σi,Fin (d i)) ℚ)
      (FractionRing (MvPolynomial (Σi,Fin (d i)) ℚ))) r f.val

omit [Fintype I] [DecidableEq I] in
@[simp] lemma localizeS_apply (d : I → ℕ) (f : S d) :
    localizeS d f = algebraMap _ (FractionRing (MvPolynomial (Σi,Fin (d i)) ℚ)) f.val := rfl

omit [Fintype I] [DecidableEq I] in
lemma localizeS_injective (d : I → ℕ) : Function.Injective (localizeS d) := by
  intro f g h
  apply Subtype.ext
  exact IsFractionRing.injective _ (FractionRing (MvPolynomial (Σi,Fin (d i)) ℚ)) h

noncomputable def shuffleImage (a : I → I → ℕ) (d e : I → ℕ) : Submodule ℚ (S (d+e)) :=
  Submodule.span ℚ {q | ∃ (f : S d) (g : S e), q = shufflePolynomial a f g}

lemma rawShuffle_mem_localized_image (a : I → I → ℕ) (f : S d) (g : S e) :
    rawShuffle a f.val g.val ∈ (shuffleImage a d e).map (localizeS (d+e)) := by
  apply Submodule.mem_map.mpr
  exact ⟨shufflePolynomial a f g, Submodule.subset_span ⟨f,g,rfl⟩,
    shufflePolynomial_eq a f g⟩

noncomputable def tensorShuffle (a : I → I → ℕ) :
    MvPolynomial ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ℚ →ₗ[ℚ]
      FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ) where
  toFun p := ∑ A : Cut d e,
    algebraMap _ _ (rename (cutSplit A) p * ∏ i, ∏ j, cutFactor A i j (a i j)) /
      algebraMap _ _ (cutDenominator A)
  map_add' := by
    intro p q
    simp only [map_add, add_mul, add_div, Finset.sum_add_distrib]
  map_smul' := by
    let : DistribSMul ℚ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ)) :=
      (inferInstance : Module ℚ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))).toDistribMulAction.toDistribSMul
    intro r p
    simp only [map_smul, map_rat_smul, smul_mul_assoc, div_eq_mul_inv,
      Finset.smul_sum, RingHom.id_apply]

lemma tensorShuffle_decomposable (a : I → I → ℕ)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ) :
    tensorShuffle a (rename Sum.inl f * rename Sum.inr g) = rawShuffle a f g := by
  simp only [tensorShuffle, LinearMap.coe_mk, AddHom.coe_mk, map_mul, rename_rename,
    rawShuffle, cutNumerator]
  rfl

lemma tensorShuffle_restricted_mul (a : I → I → ℕ) (A₀ : Cut d e) (F : S (d+e))
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ) :
    tensorShuffle a (rename (cutSplit A₀).symm F.val *
      (rename Sum.inl f * rename Sum.inr g)) =
      localizeS (d+e) F * rawShuffle a f g := by
  dsimp only [Pi.add_apply] at *
  simp only [tensorShuffle, LinearMap.coe_mk, AddHom.coe_mk, map_mul,
    split_symmetric_independent, localizeS_apply, rawShuffle, cutNumerator,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  simp only [rename_rename]
  change (algebraMap _ _ F.val *
      (algebraMap _ _ (rename (leftInput A) f) * algebraMap _ _ (rename (rightInput A) g)) *
      algebraMap _ _ (∏ i, ∏ j, cutFactor A i j (a i j))) / algebraMap _ _ (cutDenominator A) = _
  simp only [mul_assoc, mul_div_assoc]
  rfl

theorem mul_shuffle_mem (a : I → I → ℕ) (F : S (d+e)) (f : S d) (g : S e) :
    F * shufflePolynomial a f g ∈ shuffleImage a d e := by
  let V := (shuffleImage a d e).map (localizeS (d+e))
  let T : MvPolynomial ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ℚ →ₗ[ℚ]
      FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ) :=
    (tensorShuffle a).comp (LinearMap.mulRight ℚ (rename Sum.inl f.val * rename Sum.inr g.val))
  have hT : Submodule.span ℚ
      {q | ∃ (f' : S d) (g' : S e), q = rename Sum.inl f'.val * rename Sum.inr g'.val}
      ≤ V.comap T := by
    apply Submodule.span_le.mpr
    rintro q ⟨f',g',rfl⟩
    change T (rename Sum.inl f'.val * rename Sum.inr g'.val) ∈ V
    dsimp only [T, LinearMap.comp_apply, LinearMap.mulRight_apply]
    have he : (rename Sum.inl f'.val * rename Sum.inr g'.val) *
        (rename Sum.inl f.val * rename Sum.inr g.val) =
        rename Sum.inl (f'*f).val * rename Sum.inr (g'*g).val := by
      simp only [Subalgebra.coe_mul, map_mul]
      ring
    rw [he, tensorShuffle_decomposable]
    exact rawShuffle_mem_localized_image a (f'*f) (g'*g)
  have h := hT (split_symmetric_span (firstCut d e) F)
  simp only [Submodule.mem_comap, T, LinearMap.comp_apply, LinearMap.mulRight_apply] at h
  rw [tensorShuffle_restricted_mul] at h
  obtain ⟨q,hq,he⟩ := Submodule.mem_map.mp h
  have eq : q = F * shufflePolynomial a f g := by
    apply localizeS_injective (d+e)
    rw [he]
    change _ = algebraMap _ _ (F.val * (shufflePolynomial a f g).val)
    rw [map_mul]
    exact congrArg (fun x => localizeS (d+e) F * x) (shufflePolynomial_eq a f g).symm
  exact eq ▸ hq

lemma shuffleImage_mul_mem (a : I → I → ℕ) (F : S (d+e))
    {q : S (d+e)} (hq : q ∈ shuffleImage a d e) : F*q ∈ shuffleImage a d e := by
  induction hq using Submodule.span_induction with
  | mem q hq => obtain ⟨f,g,rfl⟩ := hq; exact mul_shuffle_mem a F f g
  | zero => simp
  | add q r hq hr ihq ihr => simpa [mul_add] using (shuffleImage a d e).add_mem ihq ihr
  | smul c q hq ih => simpa [mul_smul_comm] using (shuffleImage a d e).smul_mem c ih

theorem destabilizing_mul_mem (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (F : S d) {q : S d} (hq : q ∈ destabilizingSpace a μ d) :
    F*q ∈ destabilizingSpace a μ d := by
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨u,v,h,f,g,hu,hv,hμ,rfl⟩ := hq
    subst d
    have hs : shuffleImage a u v ≤ destabilizingSpace a μ (u+v) := by
      apply Submodule.span_le.mpr
      rintro q ⟨f',g',rfl⟩
      exact Submodule.subset_span ⟨u,v,rfl,f',g',hu,hv,hμ,rfl⟩
    exact hs (mul_shuffle_mem a F f g)
  | zero => simp
  | add q r hq hr ihq ihr =>
    simpa [mul_add] using (destabilizingSpace a μ d).add_mem ihq ihr
  | smul c q hq ih =>
    simpa [mul_smul_comm] using (destabilizingSpace a μ d).smul_mem c ih

noncomputable def destabilizingIdeal (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    Ideal (S d) where
  carrier := destabilizingSpace a μ d
  zero_mem' := (destabilizingSpace a μ d).zero_mem
  add_mem' := (destabilizingSpace a μ d).add_mem
  smul_mem' := destabilizing_mul_mem a μ d

@[simp] lemma mem_destabilizingIdeal (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (f : S d) : f ∈ destabilizingIdeal a μ d ↔ f ∈ destabilizingSpace a μ d := Iff.rfl

end ElementaryPositivity.RawShuffle

end

end OAI
