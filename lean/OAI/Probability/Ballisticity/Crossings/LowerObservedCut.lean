import Mathlib
import OAI.Probability.Ballisticity.Crossings.FirstLayerHitConcat
import OAI.Probability.Ballisticity.Estimates.ObservedPotential

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

lemma commonTrueRecord_time_eq {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    {n m j k : ℕ} (hn : CommonTrueRecord ℓ P n m) (hj : CommonTrueRecord ℓ P j k)
    (he : n=j) : m=k := by
  have hlt := commonTrueRecord_time_order ℓ P hn hj
  have hgt := commonTrueRecord_time_order ℓ P hj hn
  omega

lemma selectedBoundaryAt_le {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop)
    (P : Path d × Path d) {n m j k : ℕ} (hn : selectedBoundaryAt ℓ B P n m)
    (hj : 0<j) (hk : 0<k) (hc : CommonTrueRecord ℓ P j k) (hB : B (P.1 j,P.2 k)) :
    n≤j ∧ m≤k := by
  have hnle : n≤j := by
    by_contra h
    have hjn : j<n := by omega
    exact hn.2.2.2.2 j k hj hjn hk
      ((commonTrueRecord_time_order ℓ P hc hn.2.2.1).mp hjn) hB hc
  refine ⟨hnle,?_⟩
  rcases hnle.eq_or_lt with he | he
  · exact (commonTrueRecord_time_eq ℓ P hn.2.2.1 hc he).le
  · exact ((commonTrueRecord_time_order ℓ P hn.2.2.1 hc).mp he).le

def lowerCutCriterion {d : ℕ} (e f : Direction d) (h : ℤ) (b : ℝ) (K : ℕ)
    (uv : Lattice d × Lattice d) : Prop :=
  2*b ≤ |signedCoordinate f (uv.1-uv.2)| ∨ h+K ≤ signedHeight e uv.1

lemma lowerCutCriterion_height {d : ℕ} (e f : Direction d) (h : ℤ) (b : ℝ) (K : ℕ)
    (z w : Lattice d) (hz : h+(K:ℤ) ≤ signedHeight e z) : lowerCutCriterion e f h b K (z,w) := Or.inr hz

lemma lowerCut_selected_escape {d : ℕ} (e f : Direction d) (h : ℤ) (b : ℝ) (K : ℕ)
    (P : Path d × Path d) {n m j k : ℕ}
    (hn : selectedBoundaryAt (realPosition (step e)) (lowerCutCriterion e f h b K) P n m)
    (hj : 0<j) (hk : 0<k) (hc : CommonTrueRecord (realPosition (step e)) P j k)
    (hJ : signedHeight e (P.1 j)=h+K)
    (hgap : 2*b≤|signedCoordinate f (P.1 j-P.2 k)|) :
    2*b≤|signedCoordinate f (P.1 n-P.2 m)| := by
  have hh := selectedBoundaryAt_le (realPosition (step e)) (lowerCutCriterion e f h b K)
    P hn hj hk hc (Or.inl hgap)
  rcases hn.2.2.2.1 with hx | hx
  · exact hx
  · change h+(K:ℤ) ≤ signedHeight e (P.1 n) at hx
    have he : n=j := by
      apply hh.1.eq_or_lt.resolve_right
      intro hnj
      have ht := hc.1.1 n hnj
      rw [signedHeight_projection,signedHeight_projection] at ht
      have hi : signedHeight e (P.1 n)<signedHeight e (P.1 j) := by exact_mod_cast ht
      omega
    have he' := commonTrueRecord_time_eq (realPosition (step e)) P hn.2.2.1 hc he
    simpa only [he,he'] using hgap

lemma lowerCut_escape_event {d : ℕ} (e f : Direction d) (x y : Lattice d)
    (b : ℝ) (K : ℕ) (P : Path d × Path d)
    (hs : selectedBoundaryAt (realPosition (step e))
      (lowerCutCriterion e f (signedHeight e x) b K) P
      (selectedBoundaryTimes (realPosition (step e)) (lowerCutCriterion e f (signedHeight e x) b K) P).1
      (selectedBoundaryTimes (realPosition (step e)) (lowerCutCriterion e f (signedHeight e x) b K) P).2)
    (hE : P ∈ layerPairTruthEvent (realPosition (step e)) (signedHeight e) x y
      (signedHeight e x+K) {uv | 2*b≤|signedCoordinate f uv.1-signedCoordinate f uv.2|}) :
    2*b≤|signedCoordinate f
      ((selectedBoundaryData (realPosition (step e)) (lowerCutCriterion e f (signedHeight e x) b K) P).endpoints.1-
        (selectedBoundaryData (realPosition (step e)) (lowerCutCriterion e f (signedHeight e x) b K) P).endpoints.2)| := by
  obtain ⟨nm,hpre,hno⟩ := Set.mem_iUnion.mp hE
  have h1 := hpre.1.1.1
  have h2 := hpre.1.1.2
  have hgap := hpre.1.2
  rw [selectedBoundaryData_endpoints]
  refine lowerCut_selected_escape e f (signedHeight e x) b K P
    (j := nm.1+1) (k := nm.2+1) hs (Nat.succ_pos _) (Nat.succ_pos _) ?_ h1.1 ?_
  · exact ⟨⟨firstLayerHit_record _ _ (signedHeight_projection e) _ _ _ h1,hno.1⟩,
      ⟨firstLayerHit_record _ _ (signedHeight_projection e) _ _ _ h2,hno.2⟩,
      by rw [signedHeight_projection,signedHeight_projection,h1.1,h2.1]⟩
  · simpa only [Set.mem_ofPred_eq,signedCoordinate_sub] using hgap

theorem shared_lower_selected_potential_drift {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (x y : Lattice d) (hxy : signedHeight e x=signedHeight e y)
    {b R q : ℝ} (hb : 0≤b) (hR : b≤R) (K : ℕ) (hK : 0<K)
    (hq : q≤(sharedConditionedPairLaw ν (realPosition (step e)) x y).real
      (layerPairTruthEvent (realPosition (step e)) (signedHeight e) x y
        (signedHeight e x+K) {uv | 2*b≤|signedCoordinate f uv.1-signedCoordinate f uv.2|})) :
    b^((3:ℝ)/2)+q*((2*b)^((3:ℝ)/2)-b^((3:ℝ)/2)) ≤
      ∫ P, observedPotential b R
        (signedCoordinate f
          ((selectedBoundaryData (realPosition (step e)) (lowerCutCriterion e f (signedHeight e x) b K) P).endpoints.1-
            (selectedBoundaryData (realPosition (step e)) (lowerCutCriterion e f (signedHeight e x) b K) P).endpoints.2))
        ∂sharedConditionedPairLaw ν (realPosition (step e)) x y := by
  let ℓ := realPosition (step e)
  let μ := sharedConditionedPairLaw ν ℓ x y
  let : IsProbabilityMeasure μ := sharedConditionedPairLaw_probability ν ℓ x y
    (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans x y))
  let B := lowerCutCriterion e f (signedHeight e x) b K
  let E := layerPairTruthEvent ℓ (signedHeight e) x y (signedHeight e x+K)
    {uv | 2*b≤|signedCoordinate f uv.1-signedCoordinate f uv.2|}
  have hE : MeasurableSet E := measurableSet_layerPairTruthEvent _ _ _ _ _ _
  let Z := fun P : Path d × Path d => signedCoordinate f
    ((selectedBoundaryData ℓ B P).endpoints.1-(selectedBoundaryData ℓ B P).endpoints.2)
  have hZ : Measurable Z := (measurable_of_countable (fun F : BoundaryData d =>
    signedCoordinate f (F.endpoints.1-F.endpoints.2))).comp (measurable_selectedBoundaryData ℓ B)
  have hgain : 0≤(2*b)^((3:ℝ)/2)-b^((3:ℝ)/2) := sub_nonneg.mpr
    (Real.rpow_le_rpow hb (by linarith) (by norm_num))
  have hI := integral_mono_ae
    ((integrable_const (b^((3:ℝ)/2))).add
      ((integrable_const ((2*b)^((3:ℝ)/2)-b^((3:ℝ)/2))).indicator hE))
    (integrable_observedPotential μ Z hZ b R (hb.trans hR))
    (show (fun P => b^((3:ℝ)/2)+E.indicator
      (fun _ => (2*b)^((3:ℝ)/2)-b^((3:ℝ)/2)) P) ≤ᵐ[μ]
      (fun P => observedPotential b R (Z P)) from ?_)
  · simp only [Pi.add_apply] at hI
    rw [integral_add (integrable_const _) ((integrable_const _).indicator hE),
      integral_const,integral_indicator_const _ hE] at hI
    simp only [probReal_univ,smul_eq_mul,one_mul] at hI
    exact (add_le_add_right (mul_le_mul_of_nonneg_right hq hgain) _).trans hI
  · filter_upwards [shared_selectedBoundaryTimes_spec ν hue ℓ (signed_direction_unit e) htrans
      (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) x y hxy K hK B
      (lowerCutCriterion_height e f (signedHeight e x) b K)] with P hP
    by_cases hPE : P∈E
    · rw [Set.indicator_of_mem hPE]
      have hg := lowerCut_escape_event e f x y b K P hP hPE
      have hbound := observedPotential_lower_gain hb hR hg
      dsimp only [Z] at hbound ⊢
      linarith
    · rw [Set.indicator_of_notMem hPE,add_zero]
      exact observedPotential_above_floor hb hR

end DirectionalTransience

end

end

end OAI
