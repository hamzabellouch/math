import OAI.NumberTheory.JointDickman.Analysis.MellinSieveRegularity
import OAI.NumberTheory.JointDickman.Analysis.MellinSieveQuadratic

namespace OAI

/-! # The Mellin sieve profile: full integral and truncation error -/
namespace JointDickman
open MeasureTheory Complex

lemma mellinSieveFunction_atom (N t x : ℝ) :
    mellinSieveFunction N t x =
      Complex.exp (((-Real.log N*t : ℝ) : ℂ)*I)*mellinSieveAtom N t x := by
  unfold mellinSieveFunction mellinSieveAtom
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

lemma integral_mellinSieveFunction (N t : ℝ) :
    (∫ x in Set.Ioi (0:ℝ), mellinSieveFunction N t x) = mellinSieveMainKernel N t := by
  simp_rw [mellinSieveFunction_atom]
  rw [integral_const_mul, integral_mellinSieveAtom]
  rfl

lemma mellinSieveFunction_tail_norm {N B : ℝ} (hN : 0 < N) (hNB : N ≤ B) (t : ℝ) :
    (∫ x in Set.Ioi B, ‖mellinSieveFunction N t x‖) = N^3/(2*B^2) := by
  have hB : 0 < B := hN.trans_le hNB
  have he (x : ℝ) (hx : x ∈ Set.Ioi B) :
      ‖mellinSieveFunction N t x‖ = N^3*x^(-3:ℝ) := by
    have hNx := hNB.trans hx.le
    rw [norm_mellinSieveFunction, abs_of_nonneg (mellinSieveWeight_nonneg hN.le
      (hN.le.trans hNx)), mellinSieveWeight_right hN hNx,
      Real.rpow_neg (hN.le.trans hNx), Real.rpow_ofNat]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) hB]
  norm_num only [neg_add_cancel_left, show (-3:ℝ)+1 = -2 by norm_num]
  rw [Real.rpow_neg hB.le, Real.rpow_two]
  ring

lemma mellinSieveFunction_tail_integrable {N B : ℝ} (hN : 0 < N) (hNB : N ≤ B) (t : ℝ) :
    IntegrableOn (mellinSieveFunction N t) (Set.Ioi B) := by
  have hB : 0 < B := hN.trans_le hNB
  have hm : AEStronglyMeasurable (mellinSieveFunction N t) (volume.restrict (Set.Ioi B)) :=
    ((mellinSieveFunction_continuousOn hN t).mono (by
      intro x hx
      exact (hB.trans hx).le)).aestronglyMeasurable measurableSet_Ioi
  apply (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) hB).const_mul (N^3) |>.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mellinSieveFunction, abs_of_nonneg (mellinSieveWeight_nonneg hN.le
    (hB.trans hx).le), mellinSieveWeight_right hN (hNB.trans hx.le),
    Real.rpow_neg (hB.trans hx).le, Real.rpow_ofNat]
  exact le_of_eq (by ring)

lemma mellinSieveFunction_integrable {N : ℝ} (hN : 0 < N) (t : ℝ) :
    IntegrableOn (mellinSieveFunction N t) (Set.Ioi 0) := by
  have hleft : IntegrableOn (mellinSieveFunction N t) (Set.Ioc 0 N) :=
    ((mellinSieveFunction_continuousOn hN t).mono Set.Icc_subset_Ici_self).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hright := mellinSieveFunction_tail_integrable hN le_rfl t
  have hu : Set.Ioc (0:ℝ) N ∪ Set.Ioi N = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (h | h) <;> linarith [hN]
    · intro hx
      by_cases hxN : x ≤ N
      · exact Or.inl ⟨hx,hxN⟩
      · exact Or.inr (lt_of_not_ge hxN)
  rw [← hu]
  exact hleft.union hright

/-- Truncating the full transform beyond the profile's maximum costs only
its elementary cubic tail. -/
theorem mellinSieveFunction_integral_error {N B : ℝ} (hN : 0 < N) (hNB : N ≤ B) (t : ℝ) :
    ‖(∫ x in (0:ℝ)..B, mellinSieveFunction N t x) - mellinSieveMainKernel N t‖ ≤
      N^3/(2*B^2) := by
  have hB := hN.trans_le hNB
  have hi := mellinSieveFunction_integrable hN t
  have hu : Set.Ioc (0:ℝ) B ∪ Set.Ioi B = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (h | h) <;> linarith [hB]
    · intro hx
      by_cases hxB : x ≤ B
      · exact Or.inl ⟨hx,hxB⟩
      · exact Or.inr (lt_of_not_ge hxB)
  have he := setIntegral_union (f := mellinSieveFunction N t)
    (s := Set.Ioc 0 B) (t := Set.Ioi B) (by
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact (not_lt_of_ge hx.2) hy)
    measurableSet_Ioi (hi.mono_set Set.Ioc_subset_Ioi_self)
    (hi.mono_set (Set.Ioi_subset_Ioi hB.le))
  rw [hu, integral_mellinSieveFunction] at he
  rw [intervalIntegral.integral_of_le hB.le, he,
    show ((∫ x in Set.Ioc (0:ℝ) B, mellinSieveFunction N t x) -
      ((∫ x in Set.Ioc (0:ℝ) B, mellinSieveFunction N t x)+
        ∫ x in Set.Ioi B, mellinSieveFunction N t x)) =
      -(∫ x in Set.Ioi B, mellinSieveFunction N t x) by ring, norm_neg]
  exact (norm_integral_le_integral_norm _).trans_eq (mellinSieveFunction_tail_norm hN hNB t)

end JointDickman

end OAI
