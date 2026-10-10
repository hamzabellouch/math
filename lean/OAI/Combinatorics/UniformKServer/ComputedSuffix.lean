import Mathlib
import OAI.Combinatorics.UniformKServer.AutomaticEpoch
import OAI.Combinatorics.UniformKServer.EpochPartition

namespace OAI

namespace UniformKServer.ComputedSuffix
open EffectiveLP EpochShadow EpochPartition

abbrev Tape {n k : ℕ} (M H : ℕ) (u : Configuration n k) (raw : List (Fin n)) :=
  Fin (keptTail M (initial u) raw).length → Fin (AutomaticTable.bitWidth k H) → Bool

def epochTrace {n k : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k)
    (M : ℕ) (raw : List (Fin n)) (coins : Tape M (horizon k M) u.val raw) : History n k :=
  EpochExpectation.epochTrace (NeZero.pos k) M (AutomaticEpoch.counts d u (horizon k M))
    (AutomaticEpoch.total d u (horizon k M)) u.val raw coins

/-- Independent unbiased tapes are sampled at consecutive epochs. The actual
entering configuration is retained as random state, never reset to u. -/
noncomputable def expected {n k : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k)
    (M : ℕ) : Configuration n k → List (List (Fin n)) → ℝ
  | _, [] => 0
  | s, raw::es => BitSampling.mean (fun coins : Tape M (horizon k M) u.val raw =>
      let g := epochTrace d u M raw coins
      costAlong d s g + expected d u M (finish s g) es)

theorem epoch_sum {n k : ℕ} [NeZero k] (hk2 : 2 ≤ k)
    (d : RationalMetric n) (u : Config n k) (M R : ℕ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 0 ≤ δ) (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (hcap : R * (k+1) * D ≤ (M+1) * δ)
    (es : List (List (Fin n))) (hR : ∀ e ∈ es, blockCount (k:=k) ∅ e ≤ R)
    (s c : Configuration n k) (g : History n k) (hg : g.map Prod.fst = es.flatten) :
    expected d u M s es ≤
      2*(AutomaticTable.coefficient d u (horizon k M) : ℝ)*costAlong d c g +
      (2*(AutomaticTable.coefficient d u (horizon k M) : ℝ)+2)*k*D*es.length := by
  have ha : 0 ≤ (AutomaticTable.coefficient d u (horizon k M) : ℝ) := by
    exact_mod_cast (AutomaticTable.construct d u (horizon k M) D hD hdiam).1
  induction es generalizing s c g with
  | nil =>
    have hgn : g = [] := List.map_eq_nil_iff.mp hg
    simp [expected, hgn, costAlong]
  | cons e es ih =>
    obtain ⟨g₁,g₂,rfl,hg₁,hg₂⟩ := RawBlockCharge.split_history g e es.flatten hg
    have htail := ih (fun e he => hR e (by simp [he]))
    obtain ⟨hN,hE⟩ := AutomaticEpoch.construct hk2 d u M R D δ hD hδ hdiam hsep hcap
    have hep := (hE e (hR e (by simp)) s c g₁ hg₁).2
    change BitSampling.mean (fun coins : Tape M (horizon k M) u.val e =>
      costAlong d s (epochTrace d u M e coins)) ≤ _ at hep
    have hm := EpochExpectation.mean_mono
      (fun coins : Tape M (horizon k M) u.val e =>
        costAlong d s (epochTrace d u M e coins) +
          expected d u M (finish s (epochTrace d u M e coins)) es)
      (fun coins : Tape M (horizon k M) u.val e =>
        costAlong d s (epochTrace d u M e coins) +
          (2*(AutomaticTable.coefficient d u (horizon k M) : ℝ)*
            costAlong d (finish c g₁) g₂ +
          (2*(AutomaticTable.coefficient d u (horizon k M) : ℝ)+2)*k*D*es.length))
      (fun coins => add_le_add (le_refl _) (htail _ (finish c g₁) g₂ hg₂))
    simp only [BitSampling.mean_add, BitSampling.mean_const] at hm
    change BitSampling.mean _ ≤ _
    rw [BitSampling.mean_add, RawBlockCharge.cost_append]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith


/-- Complete unbounded-suffix comparison for the actually computed policy.
The sharp logarithmic estimate on its coefficient is still the companion
existence obligation, not an assumption or a conclusion of this theorem. -/
theorem suffix {n k : ℕ} [NeZero k] (hk2 : 2 ≤ k)
    (d : RationalMetric n) (u : Config n k) (M R : ℕ) (hR : 0 < R) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 0 ≤ δ) (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (hcap : R * (k+1) * D ≤ (M+1) * δ) (hRD : k*D ≤ R*δ)
    (pre w : List (Fin n)) (original actual : Configuration n k) :
    expected d u M actual (epochs k R hR w) ≤
      (4*(AutomaticTable.coefficient d u (horizon k M) : ℝ)+2)*
        offlineCost d original (pre++w) +
      (2*(AutomaticTable.coefficient d u (horizon k M) : ℝ)+2)*k*D := by
  let a : ℝ := AutomaticTable.coefficient d u (horizon k M)
  have ha : 0 ≤ a := by
    dsimp [a]
    exact_mod_cast (AutomaticTable.construct d u (horizon k M) D hD hdiam).1
  obtain ⟨g,hg,hcost⟩ := OfflineDynamic.optRat_attained d original (pre++w)
  rw [← OfflineDynamic.offline_eq_optRat] at hcost
  obtain ⟨gp,gw,rfl,hgp,hgw⟩ := RawBlockCharge.split_history g pre w hg
  have hcostw : costAlong d (finish original gp) gw ≤ offlineCost d original (pre++w) := by
    rw [← hcost, RawBlockCharge.cost_append]
    exact le_add_of_nonneg_left (costAlong_nonneg d original gp)
  have he := epoch_sum hk2 d u M R D δ hD hδ hdiam hsep hcap
    (epochs k R hR w) (epoch_blocks k R hR w) actual (finish original gp) gw
    (by rw [epochs_flatten]; exact hgw)
  have hc := epoch_charge (NeZero.pos k) d R hR δ hδ hsep pre w original
  have hc' : (((epochs k R hR w).length-1 : ℕ) : ℝ)*((k:ℝ)*D) ≤
      offlineCost d original (pre++w) := by
    have hh := mul_le_mul_of_nonneg_left hRD
      (show (0:ℝ) ≤ (((epochs k R hR w).length-1 : ℕ) : ℝ) by positivity)
    exact hh.trans (by simpa only [mul_assoc] using hc)
  have hn : (epochs k R hR w).length ≤ (epochs k R hR w).length-1+1 := by omega
  have hn' : ((epochs k R hR w).length : ℝ) ≤
      (((epochs k R hR w).length-1 : ℕ) : ℝ)+1 := by exact_mod_cast hn
  have hbase : 0 ≤ (2*a+2)*(k:ℝ)*D := by positivity
  have hcount := mul_le_mul_of_nonneg_left hn' hbase
  have hcharge := mul_le_mul_of_nonneg_left hc' (show 0 ≤ 2*a+2 by positivity)
  have hcompare := mul_le_mul_of_nonneg_left hcostw (show 0 ≤ 2*a by positivity)
  change expected d u M actual (epochs k R hR w) ≤
    (4*a+2)*offlineCost d original (pre++w)+(2*a+2)*k*D
  change expected d u M actual (epochs k R hR w) ≤
    2*a*costAlong d (finish original gp) gw+(2*a+2)*k*D*(epochs k R hR w).length at he
  nlinarith


end UniformKServer.ComputedSuffix



end OAI
