import OAI.Probability.SignedSweeps.Irreducibility

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

lemma fiberSubgroup_sum_factor {A B I J : Type*} [Finite A] [Finite B]
    (c : A → I) (d : B → J) (g : fiberSubgroup (Sum.map c d)) :
    ∃ a : fiberSubgroup c, ∃ b : fiberSubgroup d, g.1 = a.1.sumCongr b.1 := by
  have hpres : Set.MapsTo g.1 (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro x ⟨a, rfl⟩
    have h := g.property (Sum.inl a)
    cases hx : g.1 (Sum.inl a) with
    | inl a' => exact ⟨a', rfl⟩
    | inr b' => simp [hx] at h
  obtain ⟨⟨a, b⟩, he⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hpres
  have hg : g.1 = a.sumCongr b := he.symm
  have ha : a ∈ fiberSubgroup c := by
    intro x
    have h := g.property (Sum.inl x)
    simpa only [hg, Equiv.sumCongr_apply, Sum.map_inl, Sum.inl.injEq] using h
  have hb : b ∈ fiberSubgroup d := by
    intro x
    have h := g.property (Sum.inr x)
    simpa only [hg, Equiv.sumCongr_apply, Sum.map_inr, Sum.inr.injEq] using h
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hg⟩

def blockEquiv {u v l n : ℕ} (h : u + v + l = n) :
    ((Fin u ⊕ Fin v) ⊕ Fin l) ≃ Fin n :=
  ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin l))).trans finSumFinEquiv).trans
    (finCongr h)

lemma blockEmbedding_eq {u v l n : ℕ} (h : u + v + l = n)
    (a : SymmetricGroup u) (b : SymmetricGroup v) (c : SymmetricGroup l) :
    blockEmbedding h a b c = (blockEquiv h).permCongr ((a.sumCongr b).sumCongr c) := rfl

def blockColoring {u v l n : ℕ} {I J : Type*} (h : u + v + l = n)
    (c : Fin u → I) (d : Fin v → J) : Fin n → ((I ⊕ J) ⊕ Unit) :=
  Sum.map (Sum.map c d) (fun _ => ()) ∘ (blockEquiv h).symm

lemma blockColoring_factor {u v l n : ℕ} {I J : Type*} (h : u + v + l = n)
    (c : Fin u → I) (d : Fin v → J) (g : fiberSubgroup (blockColoring h c d)) :
    ∃ a : fiberSubgroup c, ∃ b : fiberSubgroup d, ∃ e : SymmetricGroup l,
      g.1 = blockEmbedding h a.1 b.1 e := by
  let σ := (blockEquiv h).symm.permCongr g.1
  have hσ : σ ∈ fiberSubgroup (Sum.map (Sum.map c d) (fun _ : Fin l => ())) := by
    intro x
    have he := g.property (blockEquiv h x)
    simpa only [blockColoring, Function.comp_apply, Equiv.symm_apply_apply,
      σ, Equiv.permCongr_apply, Equiv.symm_symm] using he
  obtain ⟨ab, e, he⟩ := fiberSubgroup_sum_factor (Sum.map c d) (fun _ : Fin l => ()) ⟨σ, hσ⟩
  obtain ⟨a, b, hab⟩ := fiberSubgroup_sum_factor c d ab
  refine ⟨a, b, e.1, ?_⟩
  have hx := congrArg (blockEquiv h).permCongr he
  apply Equiv.ext
  intro x
  have hh := congrArg (fun t : SymmetricGroup n => t x) hx
  simpa only [σ, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    hab, blockEmbedding_eq] using hh

end SignedSweeps
end

noncomputable section
namespace SignedSweeps.Partition
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

def rowIndex {n : ℕ} (lam : Partition n) (x : Fin n) : Fin (lam.1.colLen 0) :=
  ⟨lam.rowOf x, lam.rowOf_lt x⟩

lemma colOf_lt {n : ℕ} (lam : Partition n) (x : Fin n) : lam.colOf x < lam.1.rowLen 0 :=
  (lam.colOf_lt_rowLen x).trans_le (lam.1.rowLen_anti 0 _ (Nat.zero_le _))

def colIndex {n : ℕ} (lam : Partition n) (x : Fin n) : Fin (lam.1.rowLen 0) :=
  ⟨lam.colOf x, lam.colOf_lt x⟩

end SignedSweeps.Partition
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

lemma fiberSubgroup_rowIndex {n : ℕ} (lam : Partition n) :
    fiberSubgroup lam.rowIndex = rowSubgroup lam := by
  ext g
  constructor
  · intro hg x
    exact congrArg Fin.val (hg x)
  · intro hg x
    exact Fin.ext (hg x)

lemma fiberSubgroup_colIndex {n : ℕ} (lam : Partition n) :
    fiberSubgroup lam.colIndex = colSubgroup lam := by
  ext g
  constructor
  · intro hg x
    exact congrArg Fin.val (hg x)
  · intro hg x
    exact Fin.ext (hg x)

def spechtRowVector {n : ℕ} (lam : Partition n) : Specht lam :=
  groupAverage ((spechtRepresentation lam).comp (rowSubgroup lam).subtype) (spechtGenerator lam)

lemma spechtRowVector_invariant {n : ℕ} (lam : Partition n) (a : rowSubgroup lam) :
    spechtRepresentation lam a.1 (spechtRowVector lam) = spechtRowVector lam :=
  groupAverage_invariant ((spechtRepresentation lam).comp (rowSubgroup lam).subtype) a (spechtGenerator lam)

lemma spechtRowVector_at_one {n : ℕ} (lam : Partition n) :
    spechtInclusion lam (spechtRowVector lam) 1 = 1 := by
  classical
  have h (a : rowSubgroup lam) :
      spechtInclusion lam (spechtRepresentation lam a.1 (spechtGenerator lam)) 1 = 1 := by
    change polytabloid lam (a.1⁻¹ * 1) = 1
    calc
      _ = polytabloid lam (1 * (a⁻¹).1) := by simp
      _ = polytabloid lam 1 := polytabloid_right_row lam a⁻¹ 1
      _ = 1 := polytabloid_at_one lam
  have hn : (Fintype.card (rowSubgroup lam) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [spechtRowVector, groupAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
    MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    smul_eq_mul, inv_mul_cancel₀ hn]

lemma spechtRowVector_ne_zero {n : ℕ} (lam : Partition n) : spechtRowVector lam ≠ 0 := by
  intro hz
  have h := spechtRowVector_at_one lam
  rw [hz, map_zero, PiLp.zero_apply] at h
  exact zero_ne_one h

lemma complex_tmul_ne_zero {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] {x : A} {y : B} (hx : x ≠ 0) (hy : y ≠ 0) :
    x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hx
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_eq_one ℂ hy
  intro h
  have he := congrArg (fun z => TensorProduct.lid ℂ ℂ (TensorProduct.map f g z)) h
  simp only [TensorProduct.map_tmul, hf, hg, TensorProduct.lid_tmul, one_smul,
    map_zero, one_ne_zero] at he

lemma signedOccurrence_colorCarrier {u v l n : ℕ} {h : u + v + l = n}
    {α : Partition u} {β : Partition v} {γ : Partition l} {lam : Partition n}
    (ho : SignedOccurrence h α β γ lam) :
    ∃ f : Specht γ →ₗ[ℂ] Specht lam, f ≠ 0 ∧
      ∀ g : fiberSubgroup (blockColoring h α.rowIndex β.transpose.colIndex),
        ∀ x : Specht γ, ∃ y, spechtRepresentation lam g.1 (f x) = f y := by
  obtain ⟨F, hF, hFint⟩ := ho
  let v := spechtRowVector α ⊗ₜ[ℂ] spechtGenerator β.transpose
  let f := F.comp (TensorProduct.mk ℂ (Specht α ⊗[ℂ] Specht β.transpose) (Specht γ) v)
  refine ⟨f, ?_, ?_⟩
  · intro he
    have hz : f (spechtGenerator γ) = 0 := by rw [he, LinearMap.zero_apply]
    have ht : v ⊗ₜ[ℂ] spechtGenerator γ = 0 := hF (hz.trans (map_zero F).symm)
    exact complex_tmul_ne_zero
      (complex_tmul_ne_zero (spechtRowVector_ne_zero α) (spechtGenerator_ne_zero β.transpose))
      (spechtGenerator_ne_zero γ) ht
  · intro g x
    obtain ⟨a, b, e, he⟩ := blockColoring_factor h α.rowIndex β.transpose.colIndex g
    have ha : a.1 ∈ rowSubgroup α := by rw [← fiberSubgroup_rowIndex]; exact a.property
    have hb : b.1 ∈ colSubgroup β.transpose := by rw [← fiberSubgroup_colIndex]; exact b.property
    refine ⟨complexSign _ b.1 • spechtRepresentation γ e x, ?_⟩
    dsimp only [f, LinearMap.comp_apply, TensorProduct.mk_apply]
    rw [he, ← hFint]
    simp only [TensorProduct.map_tmul,
      v, spechtRowVector_invariant α ⟨a.1, ha⟩, spechtGenerator_column_action β.transpose ⟨b.1, hb⟩,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul, map_smul]

end SignedSweeps
end

end OAI
