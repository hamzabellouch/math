import OAI.NumberTheory.TotientAsymptotic.MertensReciprocal

namespace OAI

/-! Uniform reciprocal-prime mass in the intervals used for normality. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma primesUpTo_mem {x : ℝ} (hx : 0≤x) {p : ℕ} :
    p∈primesUpTo x ↔ p.Prime ∧ (p:ℝ)≤x := by
  simp only [primesUpTo,Finset.mem_filter,Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_,hpx⟩,hpp⟩
    exact ⟨hpp,(Nat.le_floor_iff hx).mp hpx⟩
  · rintro ⟨hpp,hpx⟩
    exact ⟨⟨hpp.two_le,(Nat.le_floor_iff hx).mpr hpx⟩,hpp⟩

lemma prime_interval_sum_eq (N : ℕ) {U T : ℝ} (hU : 2≤U) (hUT : U≤T) (hT : T≤N) :
    (∑ p ∈ ((Finset.Icc 2 N).filter Nat.Prime).filter
      (fun p : ℕ => U<(p:ℝ) ∧ (p:ℝ)≤T),(p:ℝ)⁻¹) =
      primeReciprocalLE T-primeReciprocalLE U := by
  classical
  have hU0 : 0≤U := by linarith
  have hT0 : 0≤T := hU0.trans hUT
  have hsub : primesUpTo U ⊆ primesUpTo T := by
    intro p hp
    obtain ⟨hpp,hpU⟩ := (primesUpTo_mem hU0).mp hp
    exact (primesUpTo_mem hT0).mpr ⟨hpp,hpU.trans hUT⟩
  have hs : ((Finset.Icc 2 N).filter Nat.Prime).filter
      (fun p : ℕ => U<(p:ℝ) ∧ (p:ℝ)≤T) = primesUpTo T \ primesUpTo U := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_sdiff,
      primesUpTo_mem hU0,primesUpTo_mem hT0]
    constructor
    · rintro ⟨⟨⟨_,_⟩,hpp⟩,hpU,hpT⟩
      exact ⟨⟨hpp,hpT⟩,fun h => (not_le_of_gt hpU) h.2⟩
    · rintro ⟨⟨hpp,hpT⟩,hnot⟩
      have hpU : U<(p:ℝ) := lt_of_not_ge (fun h => hnot ⟨hpp,h⟩)
      have hpN : p≤N := by exact_mod_cast hpT.trans hT
      exact ⟨⟨⟨hpp.two_le,hpN⟩,hpp⟩,hpU,hpT⟩
  rw [hs,Finset.sum_sdiff_eq_sub hsub]
  rfl

lemma primeReciprocalLE_bounded_error : ∃ D : ℝ, 0<D ∧ ∀ x : ℝ, 2≤x →
    |primeReciprocalLE x-B x|≤D := by
  obtain ⟨C,hC,hM⟩ := primeReciprocalLE_mertens
  refine ⟨2*C+|Mertens.M|,by positivity,?_⟩
  intro x hx
  have hlog : (1/2:ℝ)<Real.log x := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<2) hx
    linarith [Real.log_two_gt_d9]
  have hquot : C/Real.log x≤2*C := by
    apply (div_le_iff₀ (by linarith : 0<Real.log x)).mpr
    nlinarith
  calc
    _ = |(primeReciprocalLE x-B x-Mertens.M)+Mertens.M| := by congr 1; ring
    _ ≤ |primeReciprocalLE x-B x-Mertens.M|+|Mertens.M| := abs_add_le _ _
    _ ≤ _ := add_le_add ((hM x hx).trans hquot) le_rfl

end TotientAsymptotic

end

end OAI
