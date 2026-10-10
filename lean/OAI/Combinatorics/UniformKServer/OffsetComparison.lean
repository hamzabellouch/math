import Mathlib
import OAI.Combinatorics.UniformKServer.EpochExpectation

namespace OAI

noncomputable section
                                       
section

namespace UniformKServer.OffsetComparison
open EpochExpectation EpochShadow BitSampling
theorem comparison {n k b : ℕ} (hk : 0 < k) (hk2 : 2 ≤ k) (d : RationalMetric n)
    (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀ s r, ∑ j, N s r j = 2^b)
    (hLazy : ∀ s r j, (∃ i, s.2 i = r) → s.2 j ≠ r → N s r j = 0)
    (u s c : Configuration n k) (hu : Function.Injective u) (M R : ℕ)
    (D δ a E : ℝ) (hD : 0 ≤ D) (hδ : 0 ≤ δ) (ha : 0 ≤ a)
    (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (hcap : R * (k+1) * D ≤ (M+1) * δ)
    (hTable : ∀ w : List (Fin n), w.length ≤ horizon k M →
      BitSampling.mean (BitSampling.runCost N hN next (charge d) ([],u) w) ≤
        a * offlineCost d u w + E + D)
    (raw : List (Fin n)) (hR : blockCount (k:=k) ∅ raw ≤ R)
    (g : History n k) (hg : g.map Prod.fst = raw) :
    (∀ coins, (epochTrace hk M N hN u raw coins).map Prod.fst = raw) ∧
    BitSampling.mean (fun coins => costAlong d s (epochTrace hk M N hN u raw coins)) ≤
      2*a*costAlong d c g + (2*a+1)*k*D+2*E+2*D := by
  have hl := selector_lazy N hN hLazy
  refine ⟨fun coins => (epoch_virtual_bound hk d _ (hl _) u hu M R D δ hD hδ
    hdiam hsep hcap raw hR).1, ?_⟩
  let w := keptTail M (initial u) raw
  have hw : w.length ≤ horizon k M := by
    simpa only [w, kept_tail_full] using (filter_bounds M u raw).2.2
  have hsub : w.Sublist (g.map Prod.fst) := by
    rw [hg]; exact kept_sublist M (initial u) raw
  obtain ⟨g',hgg',hew⟩ := List.sublist_map_iff.mp hsub
  have hopt : offlineCost d u w ≤ costAlong d c g + k*D := by
    rw [hew]
    exact (subsequence_cost_transfer d u c g' g hgg' D hdiam).2.2
  have ht := hTable w hw
  have hb := mean_mono
    (fun coins => costAlong d s (epochTrace hk M N hN u raw coins))
    (fun coins => 2 * BitSampling.runCost N hN next (charge d) ([],u) w coins + k*D)
    (fun coins => by
      have hh := epoch_actual_bound hk d _ (hl (extend coins)) u s hu M R D δ hD hδ
        hdiam hsep hcap raw hR
      simpa only [epochTrace, shadow_full] using hh)
  rw [BitSampling.mean_add, mean_mul, BitSampling.mean_const] at hb
  have hmul := mul_le_mul_of_nonneg_left hopt ha
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hKD := mul_le_mul_of_nonneg_right hk' hD
  nlinarith


end UniformKServer.OffsetComparison

end


end

end OAI
