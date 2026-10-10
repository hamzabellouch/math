import OAI.MeasureTheory.Falconer.Estimates.ActualFarBuffer
import OAI.MeasureTheory.Falconer.Recursion.PrefixPolicyGeometry

namespace OAI

namespace PlanarFalconer

theorem uniform_source_ceiling_slack {sig kap : ℝ}
    (hsig : 0 < sig) (hgap : sig < kap/1000) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀,
      ⌈10*sig*(N:ℝ)⌉₊ < sourcePolicyBlock N kap ∧
      10*sig*(N:ℝ) ≤ (sourcePolicyBlock N kap:ℝ) ∧
      sig*(N:ℝ) ≤ (sourcePolicyBlock N kap:ℝ) := by
  obtain ⟨N₀,h₀⟩ := exists_nat_gt (1/sig)
  refine ⟨max 1 N₀,by omega,?_⟩
  intro N hN
  have hNs : 1/sig < (N:ℝ) := h₀.trans_le (Nat.cast_le.mpr (by omega))
  have hsigN : 1 < sig*(N:ℝ) := by
    have := (div_lt_iff₀ hsig).mp hNs
    linarith
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 10*sig*(N:ℝ) by positivity)
  have hblock := source_policy_block_lower N kap
  have hgapN : 1000*sig*(N:ℝ) ≤ kap*N :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  have hlt : (⌈10*sig*(N:ℝ)⌉₊:ℝ) < (sourcePolicyBlock N kap:ℝ) := by linarith
  exact ⟨Nat.cast_lt.mp hlt,by linarith,by linarith⟩

theorem direct_buffer_eq_length {N L q a v : ℕ} {sig : ℝ}
    (hceil : ⌈10*sig*(N:ℝ)⌉₊ < q) (hw : a+100*q < v)
    (hdirect : v-2*sourceFarBuffer N L sig ≤ a) :
    sourceFarBuffer N L sig = L ∧ v ≤ a+2*L ∧ 0 < L := by
  have hv : v ≤ a+2*sourceFarBuffer N L sig := by omega
  have hL : ⌈10*sig*(N:ℝ)⌉₊ ≤ L := by
    by_contra h
    have he : sourceFarBuffer N L sig = ⌈10*sig*(N:ℝ)⌉₊ := max_eq_right (by omega)
    rw [he] at hv
    omega
  have he : sourceFarBuffer N L sig = L := max_eq_left hL
  rw [he] at hv
  exact ⟨he,hv,by omega⟩

end PlanarFalconer

end OAI
