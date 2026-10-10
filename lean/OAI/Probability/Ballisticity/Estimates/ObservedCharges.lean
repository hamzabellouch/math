import Mathlib
import OAI.Probability.Ballisticity.Estimates.ObservedDrift

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

def observerShrinkEvent {d : ℕ} (e f : Direction d) (k : ℝ → ℕ)
    (i : Lattice d × Lattice d) : Set (Path d × Path d) :=
  {P | ∃ h ≤ k (pairGap f i),
    |physicalFirstHitGap (realPosition (step e)) f i.1 i.2 h P| ≤ pairGap f i/2}

lemma measurableSet_observerShrinkEvent {d : ℕ} (e f : Direction d) (k : ℝ → ℕ)
    (i : Lattice d × Lattice d) : MeasurableSet (observerShrinkEvent e f k i) := by
  unfold observerShrinkEvent
  simp only [Set.ofPred_exists,Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro h
  exact (MeasurableSet.const _).inter
    (measurableSet_le (measurable_physicalFirstHitGap _ _ _ _ h |>.abs) measurable_const)

noncomputable def observedCharge {d : ℕ} (e f : Direction d) (b R s : ℝ)
    (K : ℕ) (k : ℝ → ℕ) (P : Path d × Path d) : ℝ≥0∞ :=
  let i := pairOrigin P
  if pairGap f i<R then
    if pairGap f i≤2*s then observedAdvanceBound f b K k i else
      (observerShrinkEvent e f k i).indicator (fun _ => (k (pairGap f i) : ℝ≥0∞)) P
  else 0

lemma measurable_observedCharge {d : ℕ} (e f : Direction d) (b R s : ℝ)
    (K : ℕ) (k : ℝ → ℕ) : Measurable (observedCharge e f b R s K k) := by
  have h : Measurable (fun Z : (Path d × Path d) × (Lattice d × Lattice d) =>
      if pairGap f Z.2<R then
        if pairGap f Z.2≤2*s then (observedAdvanceBound f b K k Z.2 : ℝ≥0∞) else
          (observerShrinkEvent e f k Z.2).indicator (fun _ => (k (pairGap f Z.2):ℝ≥0∞)) Z.1
      else 0) := by
    apply measurable_from_prod_countable_left
    intro i
    dsimp only
    by_cases ha : pairGap f i<R
    · simp only [ite_eq_left ha]
      by_cases hn : pairGap f i≤2*s
      · simp only [ite_eq_left hn]; exact measurable_const
      · simp only [ite_eq_right hn]
        exact measurable_const.indicator (measurableSet_observerShrinkEvent e f k i)
    · simp only [ite_eq_right ha]; exact measurable_const
  let g : (Path d × Path d) → (Path d × Path d) × (Lattice d × Lattice d) :=
    fun P => (P,pairOrigin P)
  have hg : Measurable g := measurable_id.prodMk measurable_pairOrigin
  have hh := h.comp hg
  unfold observedCharge
  simpa only [Function.comp_def,g] using hh

lemma observedCharge_mean {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (b R s : ℝ) (K : ℕ) (k : ℝ → ℕ) (i : Lattice d × Lattice d) :
    (∫⁻ P, observedCharge e f b R s K k P
      ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2) =
    if pairGap f i<R then
      if pairGap f i≤2*s then (observedAdvanceBound f b K k i : ℝ≥0∞) else
        (k (pairGap f i):ℝ≥0∞)*sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2
          (observerShrinkEvent e f k i)
    else 0 := by
  let ℓ := realPosition (step e)
  let μ := sharedConditionedPairLaw ν ℓ i.1 i.2
  let : IsProbabilityMeasure μ := sharedConditionedPairLaw_probability ν ℓ i.1 i.2
    (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans i.1 i.2))
  have he : (observedCharge e f b R s K k) =ᵐ[μ]
      (fun P => if pairGap f i<R then
        if pairGap f i≤2*s then (observedAdvanceBound f b K k i : ℝ≥0∞) else
          (observerShrinkEvent e f k i).indicator (fun _ => (k (pairGap f i):ℝ≥0∞)) P
        else 0) := by
    filter_upwards [pairOrigin_ae ν ℓ htrans i.1 i.2] with P hP
    simp only [observedCharge,hP]
  rw [lintegral_congr_ae he]
  split_ifs
  · simp
  · exact lintegral_indicator_const (measurableSet_observerShrinkEvent e f k i) _
  · simp

lemma observedCharge_mean_le {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    {b R s c q L δ : ℝ} (hL : 0≤L) (hbs : b≤2*s)
    (K : ℕ) (k : ℝ → ℕ) (i : Lattice d × Lattice d)
    (hlower : (K:ℝ)≤L*(q*((2*b)^((3:ℝ)/2)-b^((3:ℝ)/2))))
    (hnear : b<pairGap f i → pairGap f i≤2*s → pairGap f i<R →
      (k (pairGap f i):ℝ)≤L*(c*(pairGap f i)^((3:ℝ)/2)))
    (hfar : 2*s<pairGap f i → pairGap f i<R →
      (k (pairGap f i):ℝ)*δ≤L*(c*(pairGap f i)^((3:ℝ)/2)))
    (hshrink : 2*s<pairGap f i → pairGap f i<R →
      (sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2).real
        (observerShrinkEvent e f k i)≤δ) :
    (∫⁻ P, observedCharge e f b R s K k P
      ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2) ≤
      ENNReal.ofReal L*ENNReal.ofReal (observedStateGain f b R c q i) := by
  rw [observedCharge_mean ν hue e f htrans]
  by_cases ha : pairGap f i<R
  · simp only [ite_eq_left ha,observedStateGain]
    by_cases hn : pairGap f i≤2*s
    · simp only [ite_eq_left hn]
      by_cases hb : pairGap f i≤b
      · simp only [observedAdvanceBound,ite_eq_left hb]
        rw [← ENNReal.ofReal_mul hL,← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal hlower
      · simp only [observedAdvanceBound,ite_eq_right hb]
        rw [← ENNReal.ofReal_mul hL,← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (hnear (lt_of_not_ge hb) hn ha)
    · have hb : ¬pairGap f i≤b := fun h => hn (h.trans hbs)
      simp only [ite_eq_right hn,ite_eq_right hb]
      rw [← ENNReal.ofReal_mul hL]
      let μ := sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2
      have : IsProbabilityMeasure μ := sharedConditionedPairLaw_probability ν _ i.1 i.2
        (ne_of_gt (sharedNoDropMass_pos ν hue _ (signed_direction_unit e) htrans i.1 i.2))
      rw [← ofReal_measureReal (μ := μ),← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      exact (mul_le_mul_of_nonneg_left (hshrink (lt_of_not_ge hn) ha) (Nat.cast_nonneg _)).trans
        (hfar (lt_of_not_ge hn) ha)
  · simp only [ite_eq_right ha,observedStateGain,ENNReal.ofReal_zero,mul_zero,le_refl]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

lemma commonLayer_before_selected_bound {d : ℕ} (e : Direction d)
    (B : Lattice d × Lattice d → Prop) (P : Path d × Path d)
    (hxy : signedHeight e (P.1 0)=signedHeight e (P.2 0))
    (K : ℕ) (hK : 0 < K)
    (hB : ∀ z w, signedHeight e (P.1 0)+K  ≤  signedHeight e z → B (z,w))
    {n m h : ℕ} (hcut : selectedBoundaryAt (realPosition (step e)) B P n m)
    (hh : signedHeight e (P.1 0)+h < signedHeight e (P.1 n))
    (hC : P ∈ CommonLayer (realPosition (step e)) (signedHeight e)
      (signedHeight e (P.1 0)+h)) : h < K := by
  by_contra hnot
  have hKh : K ≤ h := Nat.le_of_not_gt hnot
  obtain ⟨j,k,hj,hk,hD,hE⟩ := hC
  have hposj : 0 < j := by
    by_contra hn
    have hj0 : j=0 := by omega
    have hjH := hj.1
    rw [hj0] at hjH
    omega
  have hposk : 0 < k := by
    by_contra hn
    have hk0 : k=0 := by omega
    have hkH := hk.1
    rw [hk0] at hkH
    omega
  have hheq : signedHeight e (P.1 n)=signedHeight e (P.2 m) := by
    have he := hcut.2.2.1.2.2
    rw [signedHeight_projection,signedHeight_projection] at he
    exact_mod_cast he
  have hjn : j  <  n := by
    by_contra h
    have hnle : n ≤ j := Nat.le_of_not_gt h
    rcases eq_or_lt_of_le hnle with he | hl
    · have hjH := hj.1
      rw [← he] at hjH
      omega
    · have hnH := hj.2 n hl
      omega
  have hkm : k  <  m := by
    by_contra h
    have hmle : m ≤ k := Nat.le_of_not_gt h
    rcases eq_or_lt_of_le hmle with he | hl
    · have hkH := hk.1
      rw [← he] at hkH
      omega
    · have hmH := hk.2 m hl
      omega
  apply hcut.2.2.2.2 j k hposj hjn hposk hkm
  · apply hB
    rw [hj.1]
    exact add_le_add_right (by exact_mod_cast hKh) _
  · refine ⟨⟨firstLayerHit_record _ _ (signedHeight_projection e) _ j P.1 hj,hD⟩,
      ⟨firstLayerHit_record _ _ (signedHeight_projection e) _ k P.2 hk,hE⟩,?_⟩
    rw [signedHeight_projection,signedHeight_projection,hj.1,hk.1]

noncomputable def allocatedSmallCuts {d : ℕ} (e f : Direction d) (s : ℝ)
    (P : Path d × Path d) (n : ℕ) : Finset ℕ :=
  (Finset.range (signedHeight e (P.1 n)-signedHeight e (P.1 0)).toNat).filter fun h =>
    P ∈ CommonLayer (realPosition (step e)) (signedHeight e) (signedHeight e (P.1 0)+h) ∧
      |physicalFirstHitGap (realPosition (step e)) f (P.1 0) (P.2 0) h P| ≤ s

lemma allocatedSmallCuts_card_le {d : ℕ} (e f : Direction d) (s : ℝ)
    (B : Lattice d × Lattice d → Prop) (P : Path d × Path d)
    (hxy : signedHeight e (P.1 0)=signedHeight e (P.2 0))
    (K : ℕ) (hK : 0 < K)
    (hB : ∀ z w, signedHeight e (P.1 0)+K  ≤  signedHeight e z → B (z,w))
    {n m : ℕ} (hcut : selectedBoundaryAt (realPosition (step e)) B P n m) :
    (allocatedSmallCuts e f s P n).card ≤ K := by
  have hsub : allocatedSmallCuts e f s P n ⊆ Finset.range K := by
    intro h hh
    obtain ⟨hh,hC,hgap⟩ := Finset.mem_filter.mp hh
    apply Finset.mem_range.mpr
    apply commonLayer_before_selected_bound e B P hxy K hK hB hcut _ hC
    have hh' := Finset.mem_range.mp hh
    omega
  exact (Finset.card_le_card hsub).trans_eq (Finset.card_range K)

lemma allocatedSmallCuts_nonempty_shrink {d : ℕ} (e f : Direction d) (b s : ℝ)
    (K : ℕ) (k : ℝ → ℕ) (P : Path d × Path d)
    (hxy : signedHeight e (P.1 0)=signedHeight e (P.2 0))
    (hbs : b ≤ 2*s) (hfar : 2*s < pairGap f (pairOrigin P))
    (hk : 0 < k (pairGap f (pairOrigin P))) {n m : ℕ}
    (hcut : selectedBoundaryAt (realPosition (step e))
      (observedAdvanceRule e f b K k (pairOrigin P)) P n m)
    (hex : (allocatedSmallCuts e f s P n).Nonempty) :
    P ∈ observerShrinkEvent e f k (pairOrigin P) := by
  obtain ⟨h,hh⟩ := hex
  obtain ⟨hh,hC,hgap⟩ := Finset.mem_filter.mp hh
  have hupper : ¬pairGap f (pairOrigin P) ≤ b := fun h => not_lt_of_ge (h.trans hbs) hfar
  have hKn : observedAdvanceBound f b K k (pairOrigin P)=k (pairGap f (pairOrigin P)) :=
    ite_eq_right hupper
  have hlt := commonLayer_before_selected_bound e
    (observedAdvanceRule e f b K k (pairOrigin P)) P hxy
    (observedAdvanceBound f b K k (pairOrigin P)) (by rwa [hKn])
    (observedAdvanceRule_height e f b K k (pairOrigin P)) hcut
    (by have hh' := Finset.mem_range.mp hh; omega) hC
  refine ⟨h,?_,?_⟩
  · rw [hKn] at hlt
    exact hlt.le
  · exact hgap.trans (by linarith)

lemma allocatedSmallCuts_le_charge {d : ℕ} (e f : Direction d) {b R s : ℝ}
    (hbs : b ≤ 2*s) (K : ℕ) (k : ℝ → ℕ) (P : Path d × Path d)
    (hxy : signedHeight e (P.1 0)=signedHeight e (P.2 0))
    (ha : pairGap f (pairOrigin P) < R)
    (hK : 0 < observedAdvanceBound f b K k (pairOrigin P)) {n m : ℕ}
    (hcut : selectedBoundaryAt (realPosition (step e))
      (observedAdvanceRule e f b K k (pairOrigin P)) P n m) :
    ((allocatedSmallCuts e f s P n).card : ℝ≥0∞) ≤ observedCharge e f b R s K k P := by
  have hcard := allocatedSmallCuts_card_le e f s
    (observedAdvanceRule e f b K k (pairOrigin P)) P hxy
    (observedAdvanceBound f b K k (pairOrigin P)) hK
    (observedAdvanceRule_height e f b K k (pairOrigin P)) hcut
  simp only [observedCharge,ite_eq_left ha]
  by_cases hn : pairGap f (pairOrigin P) ≤ 2*s
  · simp only [ite_eq_left hn]
    exact_mod_cast hcard
  · simp only [ite_eq_right hn]
    have hb : ¬pairGap f (pairOrigin P) ≤ b := fun h => hn (h.trans hbs)
    have hKn : observedAdvanceBound f b K k (pairOrigin P)=k (pairGap f (pairOrigin P)) :=
      ite_eq_right hb
    by_cases hex : (allocatedSmallCuts e f s P n).Nonempty
    · have hs := allocatedSmallCuts_nonempty_shrink e f b s K k P hxy hbs
        (lt_of_not_ge hn) (by rwa [← hKn]) hcut hex
      rw [Set.indicator_of_mem hs]
      rw [hKn] at hcard
      exact_mod_cast hcard
    · rw [Finset.not_nonempty_iff_eq_empty.mp hex,Finset.card_empty]
      simp only [Nat.cast_zero]
      exact zero_le

end DirectionalTransience

end

end

end OAI
