import OAI.Dynamics.StandardMap.EndpointObservations

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
noncomputable def bridgeLeft (b : Bool) (j l : ArrayTestIndex) : EndpointObservation :=
  if b then testEndpoint j else shortfallEndpoint l
noncomputable def bridgeRight (b : Bool) (j l : ArrayTestIndex) : EndpointObservation :=
  if b then shortfallEndpoint l else testEndpoint j
def DyadicBridgeExclusions (d : DistanceArray) : Prop :=
  ∀ (u v : DyadicTime) (q : ℕ) (j l : ArrayTestIndex) (b : Bool),
    (u:ℝ)<(v:ℝ) → (1:ℝ)/(2:ℝ)^q≤((v:ℝ)-(u:ℝ))/1000 →
    (bridgeLeft b j l).inWindow u q → (bridgeRight b j l).inWindow v q →
    0<(bridgeLeft b j l).value d → 0<(bridgeRight b j l).value d →
    d.val u v≤(999/1000:ℝ)*((v:ℝ)-(u:ℝ))
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (K : S.LimitLaws)
lemma endpoint_bridge_ae (select : Bool) (u v : DyadicTime) (huv : (u:ℝ)<(v:ℝ))
    (W H : EndpointObservation) (q : ℕ) (hq : (1:ℝ)/(2:ℝ)^q≤((v:ℝ)-(u:ℝ))/1000)
    (hW : W.inWindow u q) (hH : H.inWindow v q) (j : ArrayTestIndex)
    (htest : (∀d,W.value d=clippedTest j d) ∨ (∀d,H.value d=clippedTest j d)) :
    ∀ᵐ d ∂K.selected S select,0< W.value d.val → 0< H.value d.val →
      d.val.val u v≤(999/1000:ℝ)*((v:ℝ)-(u:ℝ)) := by
  have hh (a c : ℚ) : ∀ᵐ d ∂K.selected S select,
      0<(a:ℝ) → 0<(c:ℝ) → ¬ d.val∈endpointBridgeEvent u v W H a c := by
    by_cases ha : 0<(a:ℝ)
    · by_cases hc : 0<(c:ℝ)
      · have hn : ∀ᵐ d ∂K.selected S select,¬d.val∈endpointBridgeEvent u v W H a c :=
          ae_iff.mpr (by simpa only [not_not] using S.endpoint_bridge_null K select u v huv W H q hq hW hH j htest a c ha hc)
        filter_upwards [hn] with d hd
        exact fun _ _ => hd
      · exact Eventually.of_forall fun d _ hc' => (hc hc').elim
    · exact Eventually.of_forall fun d ha' _ => (ha ha').elim
  filter_upwards [ae_all_iff.mpr (fun a => ae_all_iff.mpr (hh a))] with d hd
  intro hw hh
  obtain ⟨a,ha0,ha⟩ := exists_rat_btwn hw
  obtain ⟨c,hc0,hc⟩ := exists_rat_btwn hh
  by_contra hn
  exact hd a c ha0 hc0 ⟨lt_of_not_ge hn,ha,hc⟩
lemma dyadicBridge_aeselected (select : Bool) : ∀ᵐ d ∂K.selected S select,DyadicBridgeExclusions d.val := by
  have hh (u v : DyadicTime) (q : ℕ) (j l : ArrayTestIndex) (b : Bool) :
      ∀ᵐ d ∂K.selected S select,
      (u:ℝ)<(v:ℝ) → (1:ℝ)/(2:ℝ)^q≤((v:ℝ)-(u:ℝ))/1000 →
      (bridgeLeft b j l).inWindow u q → (bridgeRight b j l).inWindow v q →
      0<(bridgeLeft b j l).value d.val → 0<(bridgeRight b j l).value d.val →
      d.val.val u v≤(999/1000:ℝ)*((v:ℝ)-(u:ℝ)) := by
    by_cases h : (u:ℝ)<(v:ℝ) ∧ (1:ℝ)/(2:ℝ)^q≤((v:ℝ)-(u:ℝ))/1000 ∧
        (bridgeLeft b j l).inWindow u q ∧ (bridgeRight b j l).inWindow v q
    · have he : (∀d,(bridgeLeft b j l).value d=clippedTest j d) ∨
          (∀d,(bridgeRight b j l).value d=clippedTest j d) := by
        cases b <;> simp [bridgeLeft,bridgeRight]
      filter_upwards [S.endpoint_bridge_ae K select u v h.1 _ _ q h.2.1 h.2.2.1 h.2.2.2 j he] with d hd
      exact fun _ _ _ _ => hd
    · exact Eventually.of_forall fun d h1 h2 h3 h4 => (h ⟨h1,h2,h3,h4⟩).elim
  exact ae_all_iff.mpr fun u => ae_all_iff.mpr fun v => ae_all_iff.mpr fun q =>
    ae_all_iff.mpr fun j => ae_all_iff.mpr fun l => ae_all_iff.mpr (hh u v q j l)
end CriticalScaleSequence
end StandardMapEntropy

end OAI
