import OAI.Geometry.NodalSets.Coefficients.RealFiniteCoefficientL2Bound

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_localized_derivative_quadratic {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (chi : Coord n → ℝ) (hc : ContDiff ℝ ∞ chi) (hs : tsupport chi ⊆ K)
    (i : Fin n) :
    ∃ C > 0, ∀ (u g : Coord n → ℝ), MemLp u 2 (volume.restrict K) →
      MemLp g 2 (volume.restrict K) →
      MemLp (fun x ↦ chi x*g x+coordPartial chi x i*u x) 2 volume ∧
        (∫ x, (chi x*g x+coordPartial chi x i*u x)^2) ≤
          C*((∫ x in K, (u x)^2)+(∫ x in K, (g x)^2)) := by
  obtain ⟨A,hA,hAb⟩ := real_compact_multiplier_bound hK chi hc.continuous
  obtain ⟨B,hB,hBb⟩ := real_compact_multiplier_bound hK (fun x ↦ coordPartial chi x i)
    (real_coordPartial_smooth chi hc i).continuous
  refine ⟨2*(A+B),by positivity,fun u g hu hg ↦ ?_⟩
  have hga := hAb g hg
  have hub := hBb u hu
  have hglob : MemLp (fun x ↦ chi x*g x+coordPartial chi x i*u x) 2 volume := by
    exact (real_compact_localL2_product hK chi g hc.continuous hs hg).add
      (real_compact_localL2_product hK (fun x ↦ coordPartial chi x i) u
        (real_coordPartial_smooth chi hc i).continuous
        ((tsupport_fderiv_apply_subset ℝ (Pi.single i 1)).trans hs) hu)
  refine ⟨hglob,?_⟩
  have hdsub : tsupport (fun x ↦ coordPartial chi x i) ⊆ K :=
    (tsupport_fderiv_apply_subset ℝ (Pi.single i 1)).trans hs
  have hsame : (∫ x, (chi x*g x+coordPartial chi x i*u x)^2) =
      ∫ x in K, (chi x*g x+coordPartial chi x i*u x)^2 := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hs ht)),
      image_eq_zero_of_notMem_tsupport (f := fun y ↦ coordPartial chi y i) (fun ht ↦ hx (hdsub ht))]
    norm_num
  rw [hsame]
  have hsum : (∫ x in K, (chi x*g x+coordPartial chi x i*u x)^2) ≤
      2*(∫ x in K, (chi x*g x)^2)+2*(∫ x in K, (coordPartial chi x i*u x)^2) := by
    rw [← integral_const_mul,← integral_const_mul,
      ← integral_add (hga.1.integrable_sq.const_mul 2) (hub.1.integrable_sq.const_mul 2)]
    apply integral_mono (hga.1.add hub.1).integrable_sq
      ((hga.1.integrable_sq.const_mul 2).add (hub.1.integrable_sq.const_mul 2))
    intro x
    change (chi x*g x+coordPartial chi x i*u x)^2 ≤ 2*(chi x*g x)^2+2*(coordPartial chi x i*u x)^2
    nlinarith [sq_nonneg (chi x*g x-coordPartial chi x i*u x)]
  have h0u : 0 ≤ ∫ x in K, (u x)^2 := integral_nonneg (fun x ↦ sq_nonneg _)
  have h0g : 0 ≤ ∫ x in K, (g x)^2 := integral_nonneg (fun x ↦ sq_nonneg _)
  nlinarith [hga.2,hub.2,mul_nonneg hA.le h0u,mul_nonneg hB.le h0g]

end
end Yau

end OAI
