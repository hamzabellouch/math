import OAI.MeasureTheory.Falconer.Estimates.PolicyPrefixScales
import OAI.MeasureTheory.Falconer.Recursion.DirectPolicyWitness

namespace OAI

/-! # The two policy witnesses used by the same graph estimate -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)

namespace PolicyJetData
variable {m : ℕ}

structure GraphGeometry (P : PolicyJetData m) where
  p : ℕ
  g : ℕ
  ap : P.a ≤ p
  pN : p ≤ P.N
  ag : P.a ≤ g
  gp : g ≤ p
  gap : (g:ℝ)-P.a ≤ P.σ*P.N
  depth : (p:ℝ)-P.a ≤ (P.t:ℝ)-p+2*P.σ*P.N
  length : (P.longest:ℝ) ≤ (P.t:ℝ)-p+2*P.σ*P.N
  frequency : 10*P.σ*P.N ≤ (P.t:ℝ)-p
  parallel : PolicyDescriptor.parallel g p ∈ P.list

def directGeometry (P : PolicyJetData m) (d : PolicyDescriptor)
    (hd : PlanarFalconer.DirectPolicyWitness P.policy P.N P.q P.a₀ P.t₀ P.a P.t P.σ d) :
    P.GraphGeometry where
  p := descriptorAnchor d
  g := max P.a (descriptorAnchor d-descriptorLength d)
  ap := hd.anchor_gt.le
  pN := hd.anchor_lt.le.trans (P.base_right.trans P.base_N)
  ag := le_max_left _ _
  gp := hd.g_lt.le
  gap := hd.g_slack
  depth := by simpa only [Nat.cast_sub hd.anchor_gt.le] using hd.depth_scale
  length := by simpa only [longest,list,hd.maximal] using hd.length_scale
  frequency := hd.frequency_slack
  parallel := hd.companion

noncomputable def prefixGeometry (P : PolicyJetData m) (hσ : 0 < P.σ) (hleft : P.a₀ = P.a)
    (hwide : P.a+100*P.q < P.t₀) (hq : P.σ*(P.N:ℝ) ≤ P.q)
    (hhigh : (P.t₀:ℝ) ≤ P.t+P.σ*P.N)
    (hprefix : 2*PlanarFalconer.policyDepth P.policy P.N P.q P.a P.t₀ ≤ P.a+P.t₀) :
    P.GraphGeometry := by
  have hs := policy_prefix_graph_scales P hσ hleft hwide hq hhigh hprefix
  exact {
    p := PlanarFalconer.policyDepth P.policy P.N P.q P.a P.t₀
    g := P.a
    ap := hs.1.le
    pN := hs.2.2.1
    ag := le_rfl
    gp := hs.1.le
    gap := by simpa only [sub_self] using mul_nonneg hσ.le (Nat.cast_nonneg P.N)
    depth := hs.2.2.2.2.1
    length := hs.2.2.2.2.2.1
    frequency := hs.2.2.2.2.2.2
    parallel := hs.2.2.2.1 }

end PolicyJetData
end Falconer

end OAI
