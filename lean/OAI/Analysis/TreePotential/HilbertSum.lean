import OAI.Analysis.TreePotential.FreeRoot

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

/-! The outer Hilbert sum: full dual description and reflexivity. Finite-height blocks need not be finite dimensional. -/


section L2Duality
variable {I : Type*} [decidableI : DecidableEq I] (E : I → Type*) [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)]

abbrev HilbertSum := lp E 2

lemma single_hilbert_upper (x : ∀ i, E i) (hx : ∀ i, ‖x i‖ ≤ 1)
    (A : Finset I) (a : I → ℝ) :
    ‖∑ i ∈ A, a i • lp.single 2 i (x i)‖ ≤ Real.sqrt (∑ i ∈ A, (a i)^2) := by
  classical
  have he := lp.norm_sum_single (E := E) (p := 2) (by norm_num)
    (fun i => a i • x i) A
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, lp.single_smul] at he
  have hb : ∑ i ∈ A, ‖a i • x i‖^2 ≤ ∑ i ∈ A, (a i)^2 := by
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hs : ‖x i‖^2 ≤ 1 := by nlinarith [norm_nonneg (x i), hx i]
    nlinarith [sq_nonneg (a i)]
  exact (Real.le_sqrt (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).mpr
    (he.trans_le hb)

def l2Dual : HilbertSum (fun i => StrongDual ℝ (E i)) →L[ℝ]
    StrongDual ℝ (HilbertSum E) :=
  lp.dualPairing 2 2 (fun i => ContinuousLinearMap.id ℝ (StrongDual ℝ (E i)))
    (K := 1) (fun _ => ContinuousLinearMap.norm_id_le)

lemma l2Dual_apply {I : Type*} [DecidableEq I] (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (f : HilbertSum (fun i => StrongDual ℝ (E i))) (x : HilbertSum E) :
    l2Dual E f x = ∑' i, f i (x i) := rfl

lemma l2Dual_norm_le {I : Type*} [DecidableEq I] (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (f : HilbertSum (fun i => StrongDual ℝ (E i))) :
    ‖l2Dual E f‖ ≤ ‖f‖ := by
  simpa using (l2Dual E).le_of_opNorm_le (lp.norm_dualPairing _ _) f

lemma l2Dual_single (f : HilbertSum (fun i => StrongDual ℝ (E i))) (i : I) (x : E i) :
    l2Dual E f (lp.single 2 i x) = f i x := by
  classical
  rw [l2Dual_apply, tsum_eq_single i]
  · simp
  · intro j hj
    simp [lp.single_apply, Pi.single_eq_of_ne hj]

def dualRestriction (φ : StrongDual ℝ (HilbertSum E)) (i : I) : StrongDual ℝ (E i) := by
  classical
  exact φ.comp (lp.singleContinuousLinearMap ℝ E 2 i)

@[simp] lemma dualRestriction_apply (φ : StrongDual ℝ (HilbertSum E)) (i : I) (x : E i) :
    dualRestriction E φ i x = φ (lp.single 2 i x) := rfl

/-- Finite coefficient inequality, obtained using almost norming block vectors.
No block dual functional is assumed to attain its norm. -/
lemma dualRestriction_sum_sq_le (φ : StrongDual ℝ (HilbertSum E)) (A : Finset I) :
    ∑ i ∈ A, ‖dualRestriction E φ i‖^2 ≤ ‖φ‖^2 := by
  classical
  let C := ∑ i ∈ A, ‖dualRestriction E φ i‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / (2*C+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hex : ∀ i, ∃ x : E i, ‖x‖ < 1 ∧
      ‖dualRestriction E φ i‖ - δ < ‖dualRestriction E φ i x‖ := by
    intro i
    exact (dualRestriction E φ i).exists_lt_apply_of_lt_opNorm (by linarith)
  choose x hx hfx using hex
  have hl := hilbert_upper_eval_sq_sum (fun i => lp.single 2 i (x i))
    (single_hilbert_upper E x (fun i => (hx i).le)) φ A
  have hb : ∑ i ∈ A, ‖dualRestriction E φ i‖^2 ≤
      (∑ i ∈ A, (φ (lp.single 2 i (x i)))^2) + 2*δ*C := by
    rw [Finset.mul_sum, Finset.sum_add_distrib.symm]
    apply Finset.sum_le_sum
    intro i hi
    have hbound := (dualRestriction E φ i).le_opNorm (x i)
    have hab : ‖dualRestriction E φ i (x i)‖ ≤ ‖dualRestriction E φ i‖ :=
      hbound.trans (by nlinarith [norm_nonneg (dualRestriction E φ i), hx i])
    have hclose := hfx i
    have hs := sq_nonneg (‖dualRestriction E φ i‖ - ‖dualRestriction E φ i (x i)‖)
    have hprod := mul_nonneg (le_of_lt hδ)
      (show 0 ≤ ‖dualRestriction E φ i‖ from norm_nonneg _)
    simp only [Real.norm_eq_abs, dualRestriction_apply] at hab hclose hs
    nlinarith [sq_abs (φ (lp.single 2 i (x i))), abs_nonneg (φ (lp.single 2 i (x i)))]
  have hd : δ * (2*C+1) = ε := div_mul_cancel₀ ε (by positivity)
  nlinarith

lemma dualRestriction_mem (φ : StrongDual ℝ (HilbertSum E)) :
    Memℓp (dualRestriction E φ) 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  exact summable_of_sum_le (fun _ => sq_nonneg _) (dualRestriction_sum_sq_le E φ)

def dualPieces (φ : StrongDual ℝ (HilbertSum E)) :
    HilbertSum (fun i => StrongDual ℝ (E i)) := ⟨dualRestriction E φ, dualRestriction_mem E φ⟩

lemma dualPieces_norm_le (φ : StrongDual ℝ (HilbertSum E)) : ‖dualPieces E φ‖ ≤ ‖φ‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg _)
  intro A
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, dualPieces] using dualRestriction_sum_sq_le E φ A

@[simp] lemma l2Dual_dualPieces (φ : StrongDual ℝ (HilbertSum E)) :
    l2Dual E (dualPieces E φ) = φ := by
  classical
  apply lp.ext_continuousLinearMap (by norm_num)
  intro i
  ext x
  exact l2Dual_single E (dualPieces E φ) i x

@[simp] lemma dualPieces_l2Dual (f : HilbertSum (fun i => StrongDual ℝ (E i))) :
    dualPieces E (l2Dual E f) = f := by
  classical
  apply Subtype.ext
  funext i
  ext x
  exact l2Dual_single E f i x

lemma l2Dual_norm (f : HilbertSum (fun i => StrongDual ℝ (E i))) : ‖l2Dual E f‖ = ‖f‖ := by
  apply le_antisymm (l2Dual_norm_le E f)
  simpa only [dualPieces_l2Dual] using dualPieces_norm_le E (l2Dual E f)

/-- Isometric dual description of arbitrary outer l2 sums. -/
def l2DualEquiv : HilbertSum (fun i => StrongDual ℝ (E i)) ≃ₗᵢ[ℝ]
    StrongDual ℝ (HilbertSum E) :=
  LinearIsometryEquiv.ofSurjective
    { (l2Dual E).toLinearMap with norm_map' := l2Dual_norm E }
    (fun φ => ⟨dualPieces E φ, l2Dual_dualPieces E φ⟩)

end L2Duality

/-- Reflexive means the canonical embedding onto the continuous bidual is
surjective, not merely that the space is isomorphic to some Hilbert space. -/
def IsReflexive (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E)

section Reflexivity
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma hilbert_reflexive {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℝ K] [CompleteSpace K] : IsReflexive K := by
  intro Ψ
  let R := (InnerProductSpace.toDual ℝ K).toContinuousLinearEquiv
  let χ : K →L[ℝ] ℝ := Ψ.comp R.toContinuousLinearMap
  let x := R.symm χ
  refine ⟨x, ?_⟩
  ext φ
  change φ x = Ψ φ
  have hχ : ∀ z : K, inner ℝ x z = χ z := fun z => InnerProductSpace.toDual_symm_apply
  calc
    φ x = inner ℝ (R.symm φ) x := InnerProductSpace.toDual_symm_apply.symm
    _ = inner ℝ x (R.symm φ) := real_inner_comm _ _
    _ = χ (R.symm φ) := hχ _
    _ = Ψ φ := by simp [χ]

lemma reflexive_equiv (e : E ≃L[ℝ] H) (hH : IsReflexive H) : IsReflexive E := by
  intro Ψ
  let pre : StrongDual ℝ H →L[ℝ] StrongDual ℝ E :=
    (ContinuousLinearMap.compL ℝ E H ℝ).flip e.toContinuousLinearMap
  obtain ⟨h, hh⟩ := hH (Ψ.comp pre)
  refine ⟨e.symm h, ?_⟩
  ext φ
  have he := DFunLike.congr_fun hh (φ.comp e.symm.toContinuousLinearMap)
  have hc : (φ.comp e.symm.toContinuousLinearMap).comp e.toContinuousLinearMap = φ := by
    ext x
    simp
  change φ (e.symm h) = Ψ ((φ.comp e.symm.toContinuousLinearMap).comp e.toContinuousLinearMap) at he
  rwa [hc] at he

end Reflexivity

/-- Reflexivity is preserved by the outer Hilbert sum; this proof includes the
non-uniformly Hilbert-equivalent blocks used in both path-cost constructions. -/
theorem hilbertSum_reflexive {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (hE : ∀ i, IsReflexive (E i)) : IsReflexive (HilbertSum E) := by
  classical
  intro Ψ
  let χ := Ψ.comp (l2Dual E)
  let G := dualPieces (fun i => StrongDual ℝ (E i)) χ
  choose x hx using fun i => hE i (G i)
  have hnorm : ∀ i, ‖x i‖ = ‖G i‖ := by
    intro i
    rw [← (NormedSpace.inclusionInDoubleDualLi ℝ).norm_map (x i)]
    exact congrArg norm (hx i)
  have hm : Memℓp x 2 := by
    apply memℓp_gen
    simpa only [hnorm] using (lp.hasSum_norm (p := 2) (by norm_num) G).summable
  let z : HilbertSum E := ⟨x, hm⟩
  refine ⟨z, ?_⟩
  ext φ
  change φ z = Ψ φ
  rw [← l2Dual_dualPieces E φ]
  change l2Dual E (dualPieces E φ) z = χ (dualPieces E φ)
  rw [← l2Dual_dualPieces (fun i => StrongDual ℝ (E i)) χ]
  rw [l2Dual_apply, l2Dual_apply]
  apply tsum_congr
  intro i
  exact DFunLike.congr_fun (hx i) ((dualPieces E φ) i)

lemma linearBlock_reflexive (n : ℕ) : IsReflexive (LinearBlock n) :=
  reflexive_equiv (linearBlockHilbertEquiv n) hilbert_reflexive

abbrev LinearOuter := HilbertSum (fun n : ℕ => LinearBlock (n+1))

theorem linearOuter_reflexive : IsReflexive LinearOuter :=
  hilbertSum_reflexive _ (fun _ => linearBlock_reflexive _)



end BoundedTreePotentials

end

end OAI
