import OAI.NumberTheory.TwoPoint.Halasz.HalaszRootScale

namespace OAI

/-! One explicit polynomial threshold for the root scale, and its
induced threshold for the summation endpoint. -/
namespace TwoPointCorrelations

def halaszIterationRootThreshold (R₀ k : ℕ) : ℕ := R₀+(2*(k^2*k)+1)^2+k+2

def halaszIterationThreshold (R₀ k : ℕ) : ℕ :=
  (halaszIterationRootThreshold R₀ k)^k+(4*k^2)^2+2^k+1

lemma halasz_iteration_threshold_pos (R₀ k : ℕ) : 0<halaszIterationThreshold R₀ k := by
  unfold halaszIterationThreshold
  exact Nat.zero_lt_succ _

lemma halasz_iteration_scale {R₀ k N : ℕ} (hk : 2≤k)
    (hN : halaszIterationThreshold R₀ k<N) :
    2^k≤N ∧ (4*(k:ℝ)^2)^2<(N:ℝ) ∧ R₀≤halaszRootScale N k ∧
      (2*(k^2*k)+1)^2≤halaszRootScale N k ∧ k<halaszRootScale N k := by
  have hparts : (halaszIterationRootThreshold R₀ k)^k<N ∧
      (4*k^2)^2<N ∧ 2^k<N := by
    unfold halaszIterationThreshold at hN
    generalize (halaszIterationRootThreshold R₀ k)^k=a at *
    generalize (4*k^2)^2=b at *
    generalize 2^k=c at *
    omega
  have hsmall := hparts.2.1
  have htwo := hparts.2.2.le
  have hT := hparts.1.le
  have hroot := halasz_root_scale_large (by omega : 0<k) hT
  have hR0 : R₀≤halaszIterationRootThreshold R₀ k := by
    unfold halaszIterationRootThreshold
    omega
  have hm : (2*(k^2*k)+1)^2≤halaszIterationRootThreshold R₀ k := by
    unfold halaszIterationRootThreshold
    omega
  have hkt : k<halaszIterationRootThreshold R₀ k := by
    unfold halaszIterationRootThreshold
    omega
  exact ⟨htwo,by exact_mod_cast hsmall,hR0.trans hroot.le,hm.trans hroot.le,hkt.trans hroot⟩

end TwoPointCorrelations

end OAI
