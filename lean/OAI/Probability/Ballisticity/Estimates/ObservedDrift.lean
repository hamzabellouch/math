import Mathlib
import OAI.Probability.Ballisticity.Crossings.LowerObservedCut
import OAI.Probability.Ballisticity.Estimates.RestartLyapunov
import OAI.Probability.Ballisticity.Crossings.CommonCutObserver

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

def pairGap {d : ℕ} (f : Direction d) (i : Lattice d × Lattice d) : ℝ :=
  |signedCoordinate f (i.1-i.2)|

noncomputable def observedAdvanceRule {d : ℕ} (e f : Direction d) (b : ℝ)
    (K : ℕ) (k : ℝ → ℕ) (i uv : Lattice d × Lattice d) : Prop :=
  if pairGap f i ≤ b then lowerCutCriterion e f (signedHeight e i.1) b K uv else
    ((signedHeight e i.1+k (pairGap f i) : ℤ) : ℝ) ≤ dot (realPosition uv.1) (realPosition (step e))

noncomputable def observedAdvanceBound {d : ℕ} (f : Direction d) (b : ℝ)
    (K : ℕ) (k : ℝ → ℕ) (i : Lattice d × Lattice d) : ℕ :=
  if pairGap f i ≤ b then K else k (pairGap f i)

lemma observedAdvanceRule_height {d : ℕ} (e f : Direction d) (b : ℝ)
    (K : ℕ) (k : ℝ → ℕ) (i : Lattice d × Lattice d) (z w : Lattice d)
    (hz : signedHeight e i.1+observedAdvanceBound f b K k i ≤ signedHeight e z) :
    observedAdvanceRule e f b K k i (z,w) := by
  by_cases hu : pairGap f i≤b
  · simpa only [observedAdvanceRule,ite_eq_left hu] using
      lowerCutCriterion_height e f (signedHeight e i.1) b K z w
        (by simpa only [observedAdvanceBound,ite_eq_left hu] using hz)
  · simp only [observedAdvanceRule,ite_eq_right hu,signedHeight_projection]
    exact_mod_cast (show signedHeight e i.1+(k (pairGap f i):ℤ) ≤ signedHeight e z from
      by simpa only [observedAdvanceBound,ite_eq_right hu] using hz)

noncomputable def observedStatePotential {d : ℕ} (f : Direction d) (b R : ℝ)
    (i : Lattice d × Lattice d) : ℝ := observedPotential b R (signedCoordinate f (i.1-i.2))

noncomputable def observedStateGain {d : ℕ} (f : Direction d) (b R c q : ℝ)
    (i : Lattice d × Lattice d) : ℝ :=
  if pairGap f i<R then
    if pairGap f i≤b then q*((2*b)^((3:ℝ)/2)-b^((3:ℝ)/2)) else c*(pairGap f i)^((3:ℝ)/2)
  else 0

lemma observedStatePotential_upper {d : ℕ} (f : Direction d) (i : Lattice d × Lattice d)
    {b R : ℝ} (hb : b≤pairGap f i) (hR : pairGap f i≤R) :
    observedStatePotential f b R i=(pairGap f i)^((3:ℝ)/2) := by
  have hi := observedPotential_upper_start hb (abs_nonneg _) hR
  simpa only [observedStatePotential,observedPotential,pairGap,abs_abs] using hi

lemma observedStateGain_nonneg {d : ℕ} (f : Direction d) {b R c q : ℝ}
    (hb : 0≤b) (hc : 0≤c) (hq : 0≤q) (i : Lattice d × Lattice d) :
    0≤observedStateGain f b R c q i := by
  unfold observedStateGain
  split_ifs
  · exact mul_nonneg hq (sub_nonneg.mpr (Real.rpow_le_rpow hb (by linarith) (by norm_num)))
  · exact mul_nonneg hc (Real.rpow_nonneg (abs_nonneg _) _)
  · exact le_rfl

lemma commonCutObserver_potential {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (active : Lattice d × Lattice d → Prop)
    (B : (Lattice d × Lattice d) → (Lattice d × Lattice d) → Prop)
    (i : Lattice d × Lattice d) (ha : active i) (φ : Lattice d × Lattice d → ℝ) :
    (∫ P, φ (pairOrigin (commonCutObserver ℓ active B P)) ∂sharedConditionedPairLaw ν ℓ i.1 i.2) =
    ∫ P, φ (selectedBoundaryData ℓ (B i) P).endpoints ∂sharedConditionedPairLaw ν ℓ i.1 i.2 := by
  apply integral_congr_ae
  filter_upwards [pairOrigin_ae ν ℓ htrans i.1 i.2] with P hP
  simp only [commonCutObserver,hP,ite_eq_left ha,pairOrigin_selectedBoundarySuffix]

lemma observedAdvance_drift {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    {b R c q : ℝ} (hb : 0≤b) (hR : b≤R) (K : ℕ) (hK : 0<K) (k : ℝ → ℕ)
    (hupper : ∀ i : Lattice d × Lattice d, signedHeight e i.1=signedHeight e i.2 →
      b<pairGap f i → pairGap f i<R →
      (pairGap f i)^((3:ℝ)/2)+c*(pairGap f i)^((3:ℝ)/2) ≤
        ∫ P, observedStatePotential f b R
          (boundaryData (realPosition (step e)) ((signedHeight e i.1+k (pairGap f i):ℤ):ℝ) P).endpoints
          ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2)
    (hlower : ∀ i : Lattice d × Lattice d, signedHeight e i.1=signedHeight e i.2 →
      pairGap f i≤b → q≤(sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2).real
        (layerPairTruthEvent (realPosition (step e)) (signedHeight e) i.1 i.2
          (signedHeight e i.1+K) {uv | 2*b≤|signedCoordinate f uv.1-signedCoordinate f uv.2|}))
    (i : Lattice d × Lattice d) (hi : signedHeight e i.1=signedHeight e i.2) :
    observedStateGain f b R c q i+observedStatePotential f b R i ≤
      ∫ P, observedStatePotential f b R
        (pairOrigin (commonCutObserver (realPosition (step e)) (fun j => pairGap f j<R)
          (observedAdvanceRule e f b K k) P))
        ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2 := by
  let ℓ := realPosition (step e)
  by_cases ha : pairGap f i<R
  · rw [commonCutObserver_potential ν ℓ htrans (fun j => pairGap f j<R)
      (observedAdvanceRule e f b K k) i ha]
    by_cases hu : pairGap f i≤b
    · have hd := shared_lower_selected_potential_drift ν hue e f htrans i.1 i.2 hi hb hR K hK
        (hlower i hi hu)
      have hp : observedStatePotential f b R i=b^((3:ℝ)/2) :=
        observedPotential_lower_start hb hu hR
      have hRule : observedAdvanceRule e f b K k i = lowerCutCriterion e f (signedHeight e i.1) b K := by
        funext uv
        simp only [observedAdvanceRule,ite_eq_left hu]
      rw [hRule,hp]
      simp only [observedStateGain,ite_eq_left ha,ite_eq_left hu]
      simpa only [observedStatePotential,add_comm] using hd
    · have hd := hupper i hi (lt_of_not_ge hu) ha
      have hp := observedStatePotential_upper f i (le_of_lt (lt_of_not_ge hu)) ha.le
      have hRule : observedAdvanceRule e f b K k i =
          (fun uv => ((signedHeight e i.1+k (pairGap f i):ℤ):ℝ) ≤ dot (realPosition uv.1) ℓ) := by
        funext uv
        simp only [observedAdvanceRule,ite_eq_right hu,ℓ]
      rw [hRule,selectedBoundaryData_height,hp]
      simpa only [observedStateGain,ite_eq_left ha,ite_eq_right hu,add_comm] using hd
  · have : IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ i.1 i.2) :=
      sharedConditionedPairLaw_probability ν ℓ i.1 i.2
        (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans i.1 i.2))
    have he : (fun P => observedStatePotential f b R
        (pairOrigin (commonCutObserver ℓ (fun j => pairGap f j<R)
          (observedAdvanceRule e f b K k) P))) =ᵐ[sharedConditionedPairLaw ν ℓ i.1 i.2]
        (fun _ => observedStatePotential f b R i) := by
      filter_upwards [pairOrigin_ae ν ℓ htrans i.1 i.2] with P hP
      simp only [commonCutObserver,hP,ite_eq_right ha]
    rw [integral_congr_ae he,integral_const]
    simp only [observedStateGain,ite_eq_right ha,zero_add,probReal_univ,smul_eq_mul,one_mul,le_refl]

theorem observedAdvance_total_gain {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    {b R c q : ℝ} (hb : 0≤b) (hR : b≤R) (hc : 0≤c) (hq : 0≤q)
    (K : ℕ) (hK : 0<K) (k : ℝ → ℕ)
    (hk : ∀ i : Lattice d × Lattice d, signedHeight e i.1=signedHeight e i.2 →
      b<pairGap f i → pairGap f i<R → 0<k (pairGap f i))
    (hdrift : ∀ i : Lattice d × Lattice d, signedHeight e i.1=signedHeight e i.2 →
      observedStateGain f b R c q i+observedStatePotential f b R i ≤
      ∫ P, observedStatePotential f b R
        (pairOrigin (commonCutObserver (realPosition (step e)) (fun j => pairGap f j<R)
          (observedAdvanceRule e f b K k) P))
        ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2)
    (i : Lattice d × Lattice d) (hi : signedHeight e i.1=signedHeight e i.2) :
    let next := commonCutObserver (realPosition (step e)) (fun j => pairGap f j<R)
      (observedAdvanceRule e f b K k)
    (∫⁻ P, ⨆ N, observerRewardSum next (fun Q =>
        ENNReal.ofReal (observedStateGain f b R c q (pairOrigin Q))) N P
      ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2) ≤
      ENNReal.ofReal ((2*R)^((3:ℝ)/2)-observedStatePotential f b R i) := by
  let ℓ := realPosition (step e)
  let μ := fun j : Lattice d × Lattice d => sharedConditionedPairLaw ν ℓ j.1 j.2
  let active := fun j => pairGap f j<R
  let B := observedAdvanceRule e f b K k
  let next := commonCutObserver ℓ active B
  let K' := observedAdvanceBound f b K k
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
  apply restart_bounded_potential_total μ pairOrigin next
    (fun j => signedHeight e j.1=signedHeight e j.2)
    (observedStatePotential f b R) (observedStateGain f b R c q) ((2*R)^((3:ℝ)/2))
    measurable_pairOrigin (measurable_commonCutObserver ℓ active B)
    (fun j _ => pairOrigin_ae ν ℓ htrans j.1 j.2)
    (fun j hj g hg => commonCutObserver_restart ν hue e htrans active B K' hK' hB j hj g hg)
    (fun j hj => commonCutObserver_sameHeight ν hue e htrans active B K' hK' hB j hj)
    (fun j => ⟨observedPotential_nonneg' _ _ _ (hb.trans hR),observedPotential_le _ _ _⟩)
    (observedStateGain_nonneg f hb hc hq) hdrift i hi

end DirectionalTransience

end

end

end OAI
