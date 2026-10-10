import OAI.MeasureTheory.Falconer.Fourier.PolicyJetData
import OAI.MeasureTheory.Falconer.Recursion.PrefixPolicyGeometry

namespace OAI

/-! # The actual high-prefix shell supplies the graph scales -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor policyDepth)

theorem policy_prefix_graph_scales {m : ℕ} (P : PolicyJetData m)
    (hσ : 0 < P.σ) (hleft : P.a₀ = P.a)
    (hwide : P.a+100*P.q < P.t₀) (hq : P.σ*(P.N:ℝ) ≤ P.q)
    (hhigh : (P.t₀:ℝ) ≤ P.t+P.σ*P.N)
    (hprefix : 2*policyDepth P.policy P.N P.q P.a P.t₀ ≤ P.a+P.t₀) :
    let p := policyDepth P.policy P.N P.q P.a P.t₀
    P.a < p ∧ p < P.t ∧ p ≤ P.N ∧ PolicyDescriptor.parallel P.a p ∈ P.list ∧
      (p:ℝ)-P.a ≤ (P.t:ℝ)-p+2*P.σ*P.N ∧
      (P.longest:ℝ) ≤ (P.t:ℝ)-p+2*P.σ*P.N ∧
      10*P.σ*P.N ≤ (P.t:ℝ)-p := by
  let p := policyDepth P.policy P.N P.q P.a P.t₀
  have hg := PlanarFalconer.prefix_policy_geometry P.policy P.q_pos P.base_N hwide hprefix
  have hap : P.a < p := hg.1
  have hpN : p ≤ P.N := hg.2.1.trans P.base_N
  have hpref : 2*(p:ℝ) ≤ (P.a:ℝ)+P.t₀ := by exact_mod_cast hprefix
  have hwideR : (P.a:ℝ)+100*P.q < P.t₀ := by exact_mod_cast hwide
  have hσN : 0 < P.σ*(P.N:ℝ) := mul_pos hσ (Nat.cast_pos.mpr P.N_pos)
  have hfreq : 10*P.σ*P.N < (P.t:ℝ)-p := by nlinarith
  have hpt : p < P.t := by
    have hh : (p:ℝ) < P.t := by nlinarith
    exact_mod_cast hh
  have hlong : P.longest ≤ (P.t₀-P.a)/2 := by
    apply Finset.sup_le
    intro b hb
    have hb' := (Finset.mem_filter.mp hb).1
    rw [hleft] at hb'
    exact PlanarFalconer.policyDescriptor_length_le_half P.policy P.q_pos hb'
  have hlongR : 2*(P.longest:ℝ) ≤ (P.t₀:ℝ)-P.a := by
    have hh : P.a+2*P.longest ≤ P.t₀ := by omega
    have hhR : (P.a:ℝ)+2*P.longest ≤ P.t₀ := by exact_mod_cast hh
    linarith
  refine ⟨hap,hpt,hpN,?_,by nlinarith,by nlinarith,hfreq.le⟩
  apply Finset.mem_filter.mpr
  refine ⟨?_,hap⟩
  simpa only [hleft] using hg.2.2.2.2

theorem policy_prefix_inverse_scales {m : ℕ} (P : PolicyJetData m)
    (hσ : 0 < P.σ) (hleft : P.a₀ = P.a)
    (hwide : P.a+100*P.q < P.t₀) (hq : P.σ*(P.N:ℝ) ≤ P.q)
    (hhigh : (P.t₀:ℝ) ≤ P.t+P.σ*P.N) :
    20*P.σ*(P.N:ℝ) ≤ (P.t:ℝ)-P.a ∧
      (P.longest:ℝ) ≤ ((P.t:ℝ)-P.a)/2+P.σ*P.N := by
  have hwideR : (P.a:ℝ)+100*P.q < P.t₀ := by exact_mod_cast hwide
  have hσN : 0 ≤ P.σ*(P.N:ℝ) := mul_nonneg hσ.le (Nat.cast_nonneg _)
  have hlong : P.longest ≤ (P.t₀-P.a)/2 := by
    apply Finset.sup_le
    intro b hb
    have hb' := (Finset.mem_filter.mp hb).1
    rw [hleft] at hb'
    exact PlanarFalconer.policyDescriptor_length_le_half P.policy P.q_pos hb'
  have hlongR : 2*(P.longest:ℝ) ≤ (P.t₀:ℝ)-P.a := by
    have hh : P.a+2*P.longest ≤ P.t₀ := by omega
    have hhR : (P.a:ℝ)+2*P.longest ≤ P.t₀ := by exact_mod_cast hh
    linarith
  constructor <;> nlinarith

end Falconer

end OAI
