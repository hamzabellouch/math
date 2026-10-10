import Mathlib
import OAI.Probability.Ballisticity.Estimates.ObservedCharges

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

theorem observedAdvance_total_charge {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    {b R s c q L : ℝ} (hb : 0≤b) (hR : b≤R) (hc : 0≤c) (hq : 0≤q)
    (K : ℕ) (hK : 0<K) (k : ℝ → ℕ)
    (hk : ∀ i : Lattice d × Lattice d, signedHeight e i.1=signedHeight e i.2 →
      b<pairGap f i → pairGap f i<R → 0<k (pairGap f i))
    (hdrift : ∀ i : Lattice d × Lattice d, signedHeight e i.1=signedHeight e i.2 →
      observedStateGain f b R c q i+observedStatePotential f b R i ≤
      ∫ P, observedStatePotential f b R
        (pairOrigin (commonCutObserver (realPosition (step e)) (fun j => pairGap f j<R)
          (observedAdvanceRule e f b K k) P))
        ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2)
    (hmean : ∀ i : Lattice d × Lattice d, signedHeight e i.1=signedHeight e i.2 →
      (∫⁻ P, observedCharge e f b R s K k P
        ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2) ≤
      ENNReal.ofReal L*ENNReal.ofReal (observedStateGain f b R c q i))
    (i : Lattice d × Lattice d) (hi : signedHeight e i.1=signedHeight e i.2) :
    let next := commonCutObserver (realPosition (step e)) (fun j => pairGap f j<R)
      (observedAdvanceRule e f b K k)
    (∫⁻ P, ⨆ N, observerRewardSum next (observedCharge e f b R s K k) N P
      ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2) ≤
      ENNReal.ofReal L*ENNReal.ofReal ((2*R)^((3:ℝ)/2)-observedStatePotential f b R i) := by
  let ℓ := realPosition (step e)
  let μ := fun j : Lattice d × Lattice d => sharedConditionedPairLaw ν ℓ j.1 j.2
  let active := fun j => pairGap f j<R
  let B := observedAdvanceRule e f b K k
  let next := commonCutObserver ℓ active B
  let K' := observedAdvanceBound f b K k
  let reward := fun P : Path d × Path d => ENNReal.ofReal (observedStateGain f b R c q (pairOrigin P))
  let bound := fun P => ENNReal.ofReal L*reward P
  let : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
    sharedConditionedPairLaw_probability ν ℓ j.1 j.2
      (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans j.1 j.2))
  have hK' : ∀ j : Lattice d × Lattice d,
      signedHeight e j.1=signedHeight e j.2 → active j → 0<K' j := by
    intro j hj ha
    by_cases hu : pairGap f j≤b
    · simpa only [K',observedAdvanceBound,ite_eq_left hu] using hK
    · simpa only [K',observedAdvanceBound,ite_eq_right hu] using hk j hj (lt_of_not_ge hu) ha
  have hB : ∀ j, active j → ∀ z w, signedHeight e j.1+K' j≤ signedHeight e z → B j (z,w) := by
    intro j _ z w hz
    exact observedAdvanceRule_height e f b K k j z w hz
  have hreward : Measurable reward :=
    ((measurable_of_countable (observedStateGain f b R c q)).comp measurable_pairOrigin).ennreal_ofReal
  have hbound : Measurable bound := measurable_const.mul hreward
  have hm : ∀ j, signedHeight e j.1=signedHeight e j.2 →
      (∫⁻ P, observedCharge e f b R s K k P ∂μ j) ≤ ∫⁻ P, bound P ∂μ j := by
    intro j hj
    have he : bound =ᵐ[μ j] (fun _ => ENNReal.ofReal L*ENNReal.ofReal (observedStateGain f b R c q j)) := by
      filter_upwards [pairOrigin_ae ν ℓ htrans j.1 j.2] with P hP
      simp only [bound,reward,hP]
    rw [lintegral_congr_ae he]
    simpa using hmean j hj
  have hc' := restart_reward_comparison_total μ pairOrigin next
    (fun j => signedHeight e j.1=signedHeight e j.2)
    (observedCharge e f b R s K k) bound
    (measurable_commonCutObserver ℓ active B) (measurable_observedCharge e f b R s K k) hbound
    (fun j hj g hg => commonCutObserver_restart ν hue e htrans active B K' hK' hB j hj g hg)
    (fun j hj => commonCutObserver_sameHeight ν hue e htrans active B K' hK' hB j hj)
    hm i hi
  calc
    (∫⁻ P, ⨆ N, observerRewardSum next (observedCharge e f b R s K k) N P ∂μ i)
        ≤ ∫⁻ P, ⨆ N, observerRewardSum next bound N P ∂μ i := hc'
    _ = ENNReal.ofReal L*(∫⁻ P, ⨆ N, observerRewardSum next reward N P ∂μ i) := by
      simp only [bound,observerRewardSum_mul,← ENNReal.mul_iSup]
      exact lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)
    _ ≤ ENNReal.ofReal L*ENNReal.ofReal ((2*R)^((3:ℝ)/2)-observedStatePotential f b R i) :=
      mul_le_mul_right (observedAdvance_total_gain ν hue e f htrans hb hR hc hq K hK k hk hdrift i hi) _

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

def SmallCommonLayer {d : ℕ} (e f : Direction d) (s : ℝ) (H : ℤ) :
    Set (Path d × Path d) :=
  {P | ∃ n m, P.1 ∈ FirstLayerHit (signedHeight e) H n ∧
    P.2 ∈ FirstLayerHit (signedHeight e) H m ∧
    P.1 ∈ FutureNoDrop (realPosition (step e)) n ∧
    P.2 ∈ FutureNoDrop (realPosition (step e)) m ∧
    |signedCoordinate f (P.1 n-P.2 m)| ≤ s}

lemma measurableSet_smallCommonLayer {d : ℕ} (e f : Direction d) (s : ℝ) (H : ℤ) :
    MeasurableSet (SmallCommonLayer e f s H) := by
  unfold SmallCommonLayer
  simp only [Set.ofPred_exists,Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro m
  refine ((measurableSet_firstLayerHit _ _ _).preimage measurable_fst).inter ?_
  refine ((measurableSet_firstLayerHit _ _ _).preimage measurable_snd).inter ?_
  refine ((measurableSet_futureNoDrop _ _).preimage measurable_fst).inter ?_
  refine ((measurableSet_futureNoDrop _ _).preimage measurable_snd).inter ?_
  apply measurableSet_le _ measurable_const
  exact ((measurable_of_countable (signedCoordinate f)).comp
    (((measurable_pi_apply n).comp measurable_fst).sub
      ((measurable_pi_apply m).comp measurable_snd))).abs

lemma firstLayerHit_suffix_iff_of_record {d : ℕ} (e : Direction d) (X : Path d)
    {n k : ℕ} {H : ℤ} (hr : StrictRecord (realPosition (step e)) X n)
    (hH : signedHeight e (X n) ≤ H) :
    (fun j => X (n+j)) ∈ FirstLayerHit (signedHeight e) H k ↔
      X ∈ FirstLayerHit (signedHeight e) H (n+k) := by
  constructor
  · rintro ⟨he,hpre⟩
    refine ⟨he,?_⟩
    intro j hj
    by_cases hjn : j < n
    · have h := hr j hjn
      rw [signedHeight_projection,signedHeight_projection] at h
      have h' : signedHeight e (X j) < signedHeight e (X n) := by exact_mod_cast h
      exact h'.trans_le hH
    · have h := hpre (j-n) (by omega)
      simpa only [Nat.add_sub_cancel' (Nat.le_of_not_gt hjn)] using h
  · rintro ⟨he,hpre⟩
    refine ⟨he,fun j hj => hpre (n+j) (by omega)⟩

lemma firstLayerHit_time_ge_record {d : ℕ} (e : Direction d) (X : Path d)
    {n k : ℕ} {H : ℤ} (hr : StrictRecord (realPosition (step e)) X n)
    (hH : signedHeight e (X n) ≤ H) (hk : X ∈ FirstLayerHit (signedHeight e) H k) :
    n ≤ k := by
  by_contra hh
  have h := hr k (Nat.lt_of_not_ge hh)
  rw [signedHeight_projection,signedHeight_projection,hk.1] at h
  have : H < signedHeight e (X n) := by exact_mod_cast h
  omega

lemma futureNoDrop_suffix_iff {d : ℕ} (ℓ : Vector d) (X : Path d) (n k : ℕ) :
    (fun j => X (n+j)) ∈ FutureNoDrop ℓ k ↔ X ∈ FutureNoDrop ℓ (n+k) := by
  simp only [FutureNoDrop,Set.mem_ofPred_eq,Nat.add_assoc]

lemma smallCommonLayer_suffix_iff {d : ℕ} (e f : Direction d) (s : ℝ)
    (P : Path d × Path d) {n m : ℕ} (hc : CommonTrueRecord (realPosition (step e)) P n m)
    {H : ℤ} (hH : signedHeight e (P.1 n) ≤ H) :
    commonPairSuffix n m P ∈ SmallCommonLayer e f s H ↔ P ∈ SmallCommonLayer e f s H := by
  have he : signedHeight e (P.1 n)=signedHeight e (P.2 m) := by
    have hh := hc.2.2
    rw [signedHeight_projection,signedHeight_projection] at hh
    exact_mod_cast hh
  have hH' : signedHeight e (P.2 m) ≤ H := by rwa [← he]
  constructor
  · rintro ⟨j,k,hj,hk,hD,hE,hgap⟩
    refine ⟨n+j,m+k,(firstLayerHit_suffix_iff_of_record e P.1 hc.1.1 hH).mp hj,
      (firstLayerHit_suffix_iff_of_record e P.2 hc.2.1.1 hH').mp hk,
      (futureNoDrop_suffix_iff _ _ n j).mp hD,(futureNoDrop_suffix_iff _ _ m k).mp hE,hgap⟩
  · rintro ⟨j,k,hj,hk,hD,hE,hgap⟩
    have hnj := firstLayerHit_time_ge_record e P.1 hc.1.1 hH hj
    have hmk := firstLayerHit_time_ge_record e P.2 hc.2.1.1 hH' hk
    have hj' : P.1 ∈ FirstLayerHit (signedHeight e) H (n+(j-n)) := by simpa only [Nat.add_sub_cancel' hnj] using hj
    have hk' : P.2 ∈ FirstLayerHit (signedHeight e) H (m+(k-m)) := by simpa only [Nat.add_sub_cancel' hmk] using hk
    refine ⟨j-n,k-m,(firstLayerHit_suffix_iff_of_record e P.1 hc.1.1 hH).mpr hj',
      (firstLayerHit_suffix_iff_of_record e P.2 hc.2.1.1 hH').mpr hk',?_,?_,?_⟩
    · apply (futureNoDrop_suffix_iff _ _ n (j-n)).mpr
      simpa only [Nat.add_sub_cancel' hnj] using hD
    · apply (futureNoDrop_suffix_iff _ _ m (k-m)).mpr
      simpa only [Nat.add_sub_cancel' hmk] using hE
    · simpa only [commonPairSuffix,Nat.add_sub_cancel' hnj,Nat.add_sub_cancel' hmk] using hgap

lemma firstLayerHit_recordIndexPosition_all {d : ℕ} (e : Direction d)
    (x : Lattice d) (X : Path d) (hx : X 0=x)
    (hD : X ∈ NoDrop (realPosition (step e)) x)
    (hnn : ∀ n, ∃ f, X (n+1)=X n+step f) {H n : ℕ}
    (hn : X ∈ FirstLayerHit (signedHeight e) (signedHeight e x+H) n) :
    recordIndexPosition (realPosition (step e)) H (fun j => X j-x)=X n-x := by
  by_cases hH : H=0
  · subst H
    have hn0 : n=0 := by
      by_contra hh
      have h := hn.2 0 (Nat.pos_of_ne_zero hh)
      rw [hx] at h
      simp only [Nat.cast_zero,add_zero,lt_self_iff_false] at h
    subst n
    rw [recordIndexPosition,recordIndexTime_zero]
  · exact firstLayerHit_recordIndexPosition_translated e x X hx hD hnn (Nat.pos_of_ne_zero hH) hn

lemma physicalFirstHitGap_at_common {d : ℕ} (e f : Direction d)
    (P : Path d × Path d) (hxy : signedHeight e (P.1 0)=signedHeight e (P.2 0))
    (hD : P.1 ∈ NoDrop (realPosition (step e)) (P.1 0))
    (hE : P.2 ∈ NoDrop (realPosition (step e)) (P.2 0))
    (hnn : ∀ n, ∃ g, P.1 (n+1)=P.1 n+step g)
    (hmm : ∀ n, ∃ g, P.2 (n+1)=P.2 n+step g)
    {H n m : ℕ} (hn : P.1 ∈ FirstLayerHit (signedHeight e) (signedHeight e (P.1 0)+H) n)
    (hm : P.2 ∈ FirstLayerHit (signedHeight e) (signedHeight e (P.1 0)+H) m) :
    physicalFirstHitGap (realPosition (step e)) f (P.1 0) (P.2 0) H P =
      signedCoordinate f (P.1 n-P.2 m) := by
  have h1 := firstLayerHit_recordIndexPosition_all e (P.1 0) P.1 rfl hD hnn hn
  have h2 := firstLayerHit_recordIndexPosition_all e (P.2 0) P.2 rfl hE hmm (by rwa [← hxy])
  simp only [physicalFirstHitGap,firstHitPairGap,h1,h2,signedCoordinate_sub]
  ring

lemma smallCommonLayer_iff_physical {d : ℕ} (e f : Direction d) (s : ℝ)
    (P : Path d × Path d) (hxy : signedHeight e (P.1 0)=signedHeight e (P.2 0))
    (hD : P.1 ∈ NoDrop (realPosition (step e)) (P.1 0))
    (hE : P.2 ∈ NoDrop (realPosition (step e)) (P.2 0))
    (hnn : ∀ n, ∃ g, P.1 (n+1)=P.1 n+step g)
    (hmm : ∀ n, ∃ g, P.2 (n+1)=P.2 n+step g) (H : ℕ) :
    P ∈ SmallCommonLayer e f s (signedHeight e (P.1 0)+H) ↔
      P ∈ CommonLayer (realPosition (step e)) (signedHeight e) (signedHeight e (P.1 0)+H) ∧
        |physicalFirstHitGap (realPosition (step e)) f (P.1 0) (P.2 0) H P| ≤ s := by
  constructor
  · rintro ⟨n,m,hn,hm,hF,hG,hgap⟩
    exact ⟨⟨n,m,hn,hm,hF,hG⟩,by rw [physicalFirstHitGap_at_common e f P hxy hD hE hnn hmm hn hm]; exact hgap⟩
  · rintro ⟨⟨n,m,hn,hm,hF,hG⟩,hgap⟩
    exact ⟨n,m,hn,hm,hF,hG,by rw [← physicalFirstHitGap_at_common e f P hxy hD hE hnn hmm hn hm]; exact hgap⟩

end DirectionalTransience

end

end

end OAI
