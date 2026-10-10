import OAI.Geometry.NodalSets.Coefficients.RealFiniteCoefficientL2Bound
import OAI.Geometry.NodalSets.Elliptic.RealInteriorWeakAddLemmas

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_localized_commutator_derivative_bound {n : ℕ} {K : Set (Coord n)}
    (hK : IsCompact K) (C : Coord n → Fin n → Fin n → ℝ)
    (hC : ∀ a j, ContDiff ℝ ∞ (fun x ↦ C x a j))
    (chi : Coord n → ℝ) (hc : ContDiff ℝ ∞ chi) (hs : tsupport chi ⊆ K)
    (k j i : Fin n) :
    ∃ B > 0, ∀ (U : Fin n → Coord n → ℝ) (H : Fin n → Fin n → Coord n → ℝ),
      (∀ a, MemLp (U a) 2 (volume.restrict K)) →
      (∀ a l, MemLp (H a l) 2 (volume.restrict K)) →
      let G := realWeakGradientCommutator C U k j
      let DG := realWeakGradientCommutatorDerivative C U H k j i
      MemLp (fun x ↦ chi x*DG x+coordPartial chi x i*G x) 2 volume ∧
      (∫ x, (chi x*DG x+coordPartial chi x i*G x)^2) ≤
        B*((∑ a, ∫ x in K, (U a x)^2)+(∑ a, ∫ x in K, (H a i x)^2)) := by
  let A := fun x a ↦ chi x*coordPartial (fun y ↦ C y a j) x k
  let D := fun x a ↦ chi x*coordPartial (fun y ↦ coordPartial (fun z ↦ C z a j) y k) x i+
    coordPartial chi x i*coordPartial (fun y ↦ C y a j) x k
  have hA (a : Fin n) : Continuous (fun x ↦ A x a) :=
    hc.continuous.mul (real_coordPartial_smooth _ (hC a j) k).continuous
  have hD (a : Fin n) : Continuous (fun x ↦ D x a) :=
    (hc.continuous.mul (real_coordPartial_smooth _ (real_coordPartial_smooth _ (hC a j) k) i).continuous).add
      ((real_coordPartial_smooth chi hc i).continuous.mul (real_coordPartial_smooth _ (hC a j) k).continuous)
  obtain ⟨B1,hB1,hb1⟩ := real_compact_finite_coefficient_L2_bound hK A hA
  obtain ⟨B2,hB2,hb2⟩ := real_compact_finite_coefficient_L2_bound hK D hD
  refine ⟨2*(B1+B2),by positivity,fun U H hU hH ↦ ?_⟩
  dsimp only
  let S := fun x ↦ chi x*realWeakGradientCommutatorDerivative C U H k j i x+
    coordPartial chi x i*realWeakGradientCommutator C U k j x
  have heq : S = fun x ↦ (∑ a, A x a*H a i x)+(∑ a, D x a*U a x) := by
    funext x
    dsimp [S,realWeakGradientCommutator,realWeakGradientCommutatorDerivative]
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    dsimp [A,D]
    ring
  have h1 := hb1 (fun a ↦ H a i) (fun a ↦ hH a i)
  have h2 := hb2 U hU
  have hloc : MemLp S 2 (volume.restrict K) := by rw [heq]; exact h1.1.add h2.1
  have hz (x : Coord n) (hx : x ∉ K) : S x=0 := by
    have hdz : coordPartial chi x i=0 := image_eq_zero_of_notMem_tsupport
      (f := fun y ↦ coordPartial chi y i)
      (fun ht ↦ hx (hs (tsupport_fderiv_apply_subset ℝ (Pi.single i 1) ht)))
    dsimp [S]
    rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hs ht)),hdz,zero_mul,zero_mul,add_zero]
  have hglob : MemLp S 2 volume := by
    have hind : K.indicator S=S := by
      funext x
      by_cases hx : x ∈ K
      · exact indicator_of_mem hx S
      · rw [indicator_of_notMem hx,hz x hx]
    rw [← hind]
    exact (memLp_indicator_iff_restrict hK.measurableSet).mpr hloc
  refine ⟨hglob,?_⟩
  change (∫ x, (S x)^2) ≤ _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) (fun x hx ↦ by rw [hz x hx]; norm_num)]
  rw [heq]
  have ha := real_L2_add_square_bound (volume.restrict K) _ _ h1.1 h2.1
  have h0U : 0 ≤ ∑ a, ∫ x in K, (U a x)^2 := Finset.sum_nonneg (fun _ _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))
  have h0H : 0 ≤ ∑ a, ∫ x in K, (H a i x)^2 := Finset.sum_nonneg (fun _ _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))
  nlinarith [h1.2,h2.2,mul_nonneg hB1.le h0U,mul_nonneg hB2.le h0H]

end
end Yau

end OAI
