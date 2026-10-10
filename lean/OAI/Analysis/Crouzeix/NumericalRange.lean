import Mathlib
import OAI.Analysis.Crouzeix.Definitions

namespace OAI

/-! Compact numerical closure, supremum norms, and spectral containment. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem norm_le_of_mem_numericalRange (A : Operator H) {z : ℂ}
    (hz : z ∈ numericalRange A) : ‖z‖ ≤ ‖A‖ := by
  obtain ⟨x, hx, rfl⟩ := hz
  calc
    ‖⟪x, A x⟫_ℂ‖ ≤ ‖x‖ * ‖A x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm x) (norm_nonneg x)
    _ = ‖A‖ := by rw [hx]; ring

theorem numericalRange_subset_closedBall (A : Operator H) :
    numericalRange A ⊆ Metric.closedBall 0 ‖A‖ := by
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    norm_le_of_mem_numericalRange A hz

theorem numericalClosure_subset_closedBall (A : Operator H) :
    numericalClosure A ⊆ Metric.closedBall 0 ‖A‖ :=
  closure_minimal (numericalRange_subset_closedBall A) Metric.isClosed_closedBall

theorem isCompact_numericalClosure (A : Operator H) : IsCompact (numericalClosure A) :=
  (isCompact_closedBall (0 : ℂ) ‖A‖).of_isClosed_subset isClosed_closure
    (numericalClosure_subset_closedBall A)

theorem numericalRange_nonempty [Nontrivial H] (A : Operator H) :
    (numericalRange A).Nonempty := by
  obtain ⟨x, hx⟩ := exists_norm_eq H (show (0 : ℝ) ≤ 1 by norm_num)
  exact ⟨⟪x, A x⟫_ℂ, x, hx, rfl⟩

theorem numericalClosure_nonempty [Nontrivial H] (A : Operator H) :
    (numericalClosure A).Nonempty :=
  (numericalRange_nonempty A).mono subset_closure

@[simp]
theorem numericalRange_eq_empty [Subsingleton H] (A : Operator H) :
    numericalRange A = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro z ⟨x, hx, _⟩
  have : x = 0 := Subsingleton.elim _ _
  simp [this] at hx

@[simp]
theorem supNorm_empty {E : Type*} [NormedAddCommGroup E] (F : ℂ → E) :
    supNorm ∅ F = 0 := by simp [supNorm]

instance amplificationSubsingleton [Subsingleton H] (m : ℕ) :
    Subsingleton (Amplification H m) := by
  have hz (x : Amplification H m) : x = 0 := by
    refine UniformSpace.Completion.induction_on x
      (isClosed_eq continuous_id continuous_const) ?_
    intro a
    rw [Subsingleton.elim a 0, UniformSpace.Completion.coe_zero]
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem zeroConclusion [Subsingleton H] (A : Operator H) : ZeroConclusion A := by
  have hemp := numericalRange_eq_empty A
  have hzero : ∀ m (T : Operator (Amplification H m)), T = 0 := by
    intro m T
    exact Subsingleton.elim _ _
  refine ⟨hemp, ?_, ?_, ?_⟩
  · intro m d B
    rw [hzero m (polynomialEval A B), hemp, supNorm_empty]
    simp
  · intro m U F
    rw [hzero m (matrixHolomorphicEval A U F), hemp, supNorm_empty]
    simp
  · intro m R
    rw [hzero m (matrixRationalEval A R), hemp, supNorm_empty]
    simp

theorem supNorm_le {E : Type*} [NormedAddCommGroup E] {S : Set ℂ}
    {F : ℂ → E} {C : ℝ} (hC : 0 ≤ C) (hF : ∀ z ∈ S, ‖F z‖ ≤ C) :
    supNorm S F ≤ C := by
  apply csSup_le ⟨0, by simp⟩
  intro b hb
  rcases hb with rfl | ⟨z, hz, rfl⟩
  · exact hC
  · exact hF z hz

theorem supNorm_bddAbove {E : Type*} [NormedAddCommGroup E] {S : Set ℂ}
    {F : ℂ → E} (hS : IsCompact S) (hF : ContinuousOn F S) :
    BddAbove (insert 0 ((fun z => ‖F z‖) '' S)) :=
  (hS.bddAbove_image hF.norm).insert 0

theorem supNorm_nonneg {E : Type*} [NormedAddCommGroup E] {S : Set ℂ}
    {F : ℂ → E} (hb : BddAbove (insert 0 ((fun z => ‖F z‖) '' S))) :
    0 ≤ supNorm S F :=
  le_csSup hb (by simp)

theorem norm_le_supNorm {E : Type*} [NormedAddCommGroup E] {S : Set ℂ}
    {F : ℂ → E} (hb : BddAbove (insert 0 ((fun z => ‖F z‖) '' S)))
    {z : ℂ} (hz : z ∈ S) : ‖F z‖ ≤ supNorm S F :=
  le_csSup hb (Set.mem_insert_of_mem 0 ⟨z, hz, rfl⟩)

theorem supNorm_mono {E : Type*} [NormedAddCommGroup E] {S T : Set ℂ}
    {F : ℂ → E} (hST : S ⊆ T)
    (hb : BddAbove (insert 0 ((fun z => ‖F z‖) '' T))) :
    supNorm S F ≤ supNorm T F := by
  apply csSup_le_csSup hb ⟨0, by simp⟩
  exact Set.insert_subset_insert (Set.image_mono hST)

theorem supNorm_attained {E : Type*} [NormedAddCommGroup E] {S : Set ℂ}
    {F : ℂ → E} (hS : IsCompact S) (hne : S.Nonempty) (hF : ContinuousOn F S) :
    ∃ z ∈ S, supNorm S F = ‖F z‖ := by
  obtain ⟨z, hz, hmax⟩ := hS.exists_isMaxOn hne hF.norm
  refine ⟨z, hz, le_antisymm ?_ ?_⟩
  · exact supNorm_le (norm_nonneg _) hmax
  · exact norm_le_supNorm (supNorm_bddAbove hS hF) hz

theorem supNorm_closure {E : Type*} [NormedAddCommGroup E] {S : Set ℂ}
    {F : ℂ → E} (hS : IsCompact (closure S)) (hF : ContinuousOn F (closure S)) :
    supNorm S F = supNorm (closure S) F := by
  have hbK := supNorm_bddAbove hS hF
  have hsub : insert 0 ((fun z => ‖F z‖) '' S) ⊆
      insert 0 ((fun z => ‖F z‖) '' closure S) :=
    Set.insert_subset_insert (Set.image_mono subset_closure)
  have hbS := hbK.mono hsub
  apply le_antisymm (supNorm_mono subset_closure hbK)
  have hc : IsClosed (closure S ∩ (fun z => ‖F z‖) ⁻¹' Iic (supNorm S F)) :=
    hF.norm.preimage_isClosed_of_isClosed isClosed_closure isClosed_Iic
  have hs : S ⊆ closure S ∩ (fun z => ‖F z‖) ⁻¹' Iic (supNorm S F) := by
    intro z hz
    exact ⟨subset_closure hz, norm_le_supNorm hbS hz⟩
  apply supNorm_le (supNorm_nonneg hbS)
  intro z hz
  exact (closure_minimal hs hc hz).2

theorem continuous_matrixPolynomial {m d : ℕ} (B : Fin (d + 1) → Coeff m) :
    Continuous (matrixPolynomial B) := by
  unfold matrixPolynomial
  exact continuous_finsetSum _ fun k _ => (continuous_id.pow _).smul continuous_const

theorem polynomial_sup_eq_max [Nontrivial H] (A : Operator H)
    {m d : ℕ} (B : Fin (d + 1) → Coeff m) :
    supNorm (numericalRange A) (matrixPolynomial B) =
      supNorm (numericalClosure A) (matrixPolynomial B) ∧
    ∃ z ∈ numericalClosure A,
      supNorm (numericalClosure A) (matrixPolynomial B) = ‖matrixPolynomial B z‖ := by
  have hc : ContinuousOn (matrixPolynomial B) (numericalClosure A) :=
    (continuous_matrixPolynomial B).continuousOn
  exact ⟨supNorm_closure (isCompact_numericalClosure A) hc,
    supNorm_attained (isCompact_numericalClosure A) (numericalClosure_nonempty A) hc⟩

theorem operator_lower_bound_of_inner (T : Operator H) {δ : ℝ}
    (hδ : ∀ x : H, ‖x‖ = 1 → δ ≤ ‖⟪x, T x⟫_ℂ‖) (x : H) :
    δ * ‖x‖ ≤ ‖T x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let v : H := (‖x‖ : ℂ)⁻¹ • x
  have hv : ‖v‖ = 1 := by simp [v, norm_smul, hn]
  have hb : δ ≤ ‖T v‖ := by
    calc
      δ ≤ ‖⟪v, T v⟫_ℂ‖ := hδ v hv
      _ ≤ ‖v‖ * ‖T v‖ := norm_inner_le_norm _ _
      _ = ‖T v‖ := by rw [hv, one_mul]
  calc
    δ * ‖x‖ ≤ ‖T v‖ * ‖x‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = ‖T x‖ := by
      simp only [v, map_smul, norm_smul, norm_inv, Complex.norm_real, norm_norm]
      rw [mul_right_comm, inv_mul_cancel₀ hn, one_mul]

theorem isUnit_of_inner_lower_bound [CompleteSpace H] (T : Operator H)
    {δ : ℝ} (hδpos : 0 < δ) (hb : ∀ x : H, ‖x‖ = 1 → δ ≤ ‖⟪x, T x⟫_ℂ‖) :
    IsUnit T := by
  have lower := operator_lower_bound_of_inner T hb
  have lowerAdj : ∀ y, δ * ‖y‖ ≤ ‖(ContinuousLinearMap.adjoint T) y‖ := by
    apply operator_lower_bound_of_inner
    intro y hy
    rw [T.adjoint_inner_right, norm_inner_symm]
    exact hb y hy
  let C : NNReal := ⟨δ⁻¹, inv_nonneg.mpr hδpos.le⟩
  have anti : AntilipschitzWith C T := by
    apply T.antilipschitz_of_bound
    intro x
    have hh := mul_le_mul_of_nonneg_left (lower x) (inv_nonneg.mpr hδpos.le)
    change ‖x‖ ≤ δ⁻¹ * ‖T x‖
    simpa only [← mul_assoc, inv_mul_cancel₀ hδpos.ne', one_mul] using hh
  have hclosed : IsClosed (T.range : Set H) :=
    anti.isClosed_range T.uniformContinuous
  have hak : (ContinuousLinearMap.adjoint T).ker = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro x y hxy
    change (ContinuousLinearMap.adjoint T) x = (ContinuousLinearMap.adjoint T) y at hxy
    have hnorm := lowerAdj (x - y)
    have hz : (ContinuousLinearMap.adjoint T) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    rw [hz, norm_zero] at hnorm
    have : ‖x - y‖ ≤ 0 := by nlinarith
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hr : T.range.topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, T.orthogonal_range, hak]
  rw [hclosed.submodule_topologicalClosure_eq] at hr
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨anti.injective, LinearMap.range_eq_top.mp hr⟩

theorem spectrum_subset_numericalClosure [CompleteSpace H] (A : Operator H) :
    spectrum ℂ A ⊆ numericalClosure A := by
  intro lam hspec
  by_contra hlam
  have hopen : IsOpen (numericalClosure A)ᶜ := isClosed_closure.isOpen_compl
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen lam hlam
  have hsep : ∀ z ∈ numericalRange A, δ ≤ ‖lam - z‖ := by
    intro z hz
    by_contra hlt
    have hb : z ∈ Metric.ball lam δ := by
      simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using lt_of_not_ge hlt
    exact hball hb (subset_closure hz)
  have hu : IsUnit (algebraMap ℂ (Operator H) lam - A) := by
    apply isUnit_of_inner_lower_bound _ hδ
    intro x hx
    have he : ⟪x, (algebraMap ℂ (Operator H) lam - A) x⟫_ℂ = lam - ⟪x, A x⟫_ℂ := by
      simp [ContinuousLinearMap.algebraMap_apply, inner_self_eq_norm_sq_to_K, hx]
    rw [he]
    exact hsep _ ⟨x, hx, rfl⟩
  exact (spectrum.mem_iff.mp hspec) hu

end CrouzeixHilbert
end

end OAI
