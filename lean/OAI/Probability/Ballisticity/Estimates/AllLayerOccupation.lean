import Mathlib
import OAI.Probability.Ballisticity.Estimates.OccupationAlgebra
import OAI.Probability.Ballisticity.Crossings.CommonCutCounting

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

lemma physical_small_gap_prefix {d : ℕ} (e f : Direction d) (x y : Lattice d)
    (hxy : signedHeight e x=signedHeight e y) (P : Path d × Path d)
    (hP : (P.1 ∈ RegularPath (realPosition (step e)) x ∧ P.1 ∈ NoDrop (realPosition (step e)) x) ∧
      (P.2 ∈ RegularPath (realPosition (step e)) y ∧ P.2 ∈ NoDrop (realPosition (step e)) y))
    {H : ℕ} (hH : 0 < H) (s : ℝ)
    (hgap : |physicalFirstHitGap (realPosition (step e)) f x y H P| ≤ s) :
    P ∈ layerPairEvent (realPosition (step e)) (signedHeight e) x y
      (signedHeight e x+H) {uv | |signedCoordinate f uv.1-signedCoordinate f uv.2| ≤ s} := by
  have ht1 : Tendsto (fun n => (signedHeight e (P.1 n):ℝ)) atTop atTop := by
    simpa only [TransientPaths,Set.mem_ofPred_eq,signedHeight_projection] using hP.1.1.2.2
  have ht2 : Tendsto (fun n => (signedHeight e (P.2 n):ℝ)) atTop atTop := by
    simpa only [TransientPaths,Set.mem_ofPred_eq,signedHeight_projection] using hP.2.1.2.2
  obtain ⟨n,hn⟩ := firstLayerHit_exists (signedHeight e) (signedHeight_step_le e)
    P.1 hP.1.1.2.1 ht1 (signedHeight e x+H) (by rw [hP.1.1.1]; omega)
  obtain ⟨m,hm⟩ := firstLayerHit_exists (signedHeight e) (signedHeight_step_le e)
    P.2 hP.2.1.2.1 ht2 (signedHeight e x+H) (by rw [hP.2.1.1]; omega)
  have hn0 : 0 < n := by
    by_contra h
    have hnz : n=0 := by omega
    have hh := hn.1
    rw [hnz,hP.1.1.1] at hh
    omega
  have hm0 : 0 < m := by
    by_contra h
    have hmz : m=0 := by omega
    have hh := hm.1
    rw [hmz,hP.2.1.1] at hh
    omega
  have he1 := firstLayerHit_recordIndexPosition_all e x P.1 hP.1.1.1 hP.1.2 hP.1.1.2.1 hn
  have he2 := firstLayerHit_recordIndexPosition_all e y P.2 hP.2.1.1 hP.2.2 hP.2.1.2.1 (by rwa [← hxy])
  have he : physicalFirstHitGap (realPosition (step e)) f x y H P=
      signedCoordinate f (P.1 n)-signedCoordinate f (P.2 m) := by
    simp only [physicalFirstHitGap,firstHitPairGap,he1,he2,signedCoordinate_sub]
    ring
  apply Set.mem_iUnion.mpr
  refine ⟨(n-1,m-1),?_⟩
  have hnz : n-1+1=n := by omega
  have hmz : m-1+1=m := by omega
  simp only [layerPairPrefix,hnz,hmz,Set.mem_inter_iff,Set.mem_prod,Set.mem_ofPred_eq]
  exact ⟨⟨⟨hn,hm⟩,by rwa [he] at hgap⟩,⟨fun j _ => hP.1.2 j,fun j _ => hP.2.2 j⟩⟩

lemma layer_truth_small_subset {d : ℕ} (e f : Direction d) (x y : Lattice d)
    (H : ℤ) (s : ℝ) :
    layerPairTruthEvent (realPosition (step e)) (signedHeight e) x y H
      {uv | |signedCoordinate f uv.1-signedCoordinate f uv.2| ≤ s} ⊆ SmallCommonLayer e f s H := by
  intro P hP
  obtain ⟨nm,hp,ht⟩ := Set.mem_iUnion.mp hP
  exact ⟨nm.1+1,nm.2+1,hp.1.1.1,hp.1.1.2,ht.1,ht.2,by simpa only [signedCoordinate_sub,Set.mem_ofPred_eq] using hp.1.2⟩

lemma physical_small_gap_truth_domination {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (x y : Lattice d) (hxy : signedHeight e x=signedHeight e y) {H : ℕ} (hH : 0 < H)
    (s : ℝ) (c : ℝ≥0∞) (hc : ∀ u v, c ≤ sharedNoDropMass ν (realPosition (step e)) u v) :
    c*sharedConditionedPairLaw ν (realPosition (step e)) x y
      {P | |physicalFirstHitGap (realPosition (step e)) f x y H P| ≤ s} ≤
    sharedConditionedPairLaw ν (realPosition (step e)) x y
      (SmallCommonLayer e f s (signedHeight e x+H)) := by
  let ℓ := realPosition (step e)
  let E : Set (Lattice d × Lattice d) := {uv | |signedCoordinate f uv.1-signedCoordinate f uv.2| ≤ s}
  apply (mul_le_mul' le_rfl (measure_mono_ae ?_)).trans
    ((shared_layer_truth_domination ν ℓ (signedHeight e) (signedHeight_projection e) x y
      (signedHeight e x+H) E c hc).trans (measure_mono (layer_truth_small_subset e f x y _ s)))
  filter_upwards [sharedConditioned_regularPath ν ℓ htrans x y] with P hP
  exact physical_small_gap_prefix e f x y hxy P hP hH s

lemma smallCommonCount_lintegral {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (x y : Lattice d) (s : ℝ) (H : ℕ) :
    (∫⁻ P, (smallCommonCount e f s H P:ℝ≥0∞) ∂sharedConditionedPairLaw ν (realPosition (step e)) x y) =
      ∑ j ∈ Finset.range H, sharedConditionedPairLaw ν (realPosition (step e)) x y
        (SmallCommonLayer e f s (signedHeight e x+j)) := by
  let μ := sharedConditionedPairLaw ν (realPosition (step e)) x y
  calc
    _ = ∫⁻ P, ∑ j ∈ Finset.range H,
        (SmallCommonLayer e f s (signedHeight e x+j)).indicator (fun _ => (1:ℝ≥0∞)) P ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [sharedConditioned_regularPath ν (realPosition (step e)) htrans x y] with P hP
      simp only [smallCommonCount,hP.1.1.1,Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs with hPj <;> simp [Set.indicator,hPj]
    _ = _ := by
      rw [lintegral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [lintegral_indicator_const (measurableSet_smallCommonLayer e f s _),one_mul]
      · intro j hj
        exact measurable_const.indicator (measurableSet_smallCommonLayer e f s _)

theorem all_layers_occupation_le {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (x y : Lattice d) (hxy : signedHeight e x=signedHeight e y)
    (s : ℝ) (H : ℕ) (c : ℝ≥0∞) (hc : ∀ u v, c ≤ sharedNoDropMass ν (realPosition (step e)) u v) :
    c*(∑ j ∈ Finset.range H, sharedConditionedPairLaw ν (realPosition (step e)) x y
      {P | |physicalFirstHitGap (realPosition (step e)) f x y j P| ≤ s}) ≤ c+
      (∫⁻ P, (smallCommonCount e f s H P:ℝ≥0∞) ∂sharedConditionedPairLaw ν (realPosition (step e)) x y) := by
  let ℓ := realPosition (step e)
  let μ := sharedConditionedPairLaw ν ℓ x y
  let : IsProbabilityMeasure μ := sharedConditionedPairLaw_probability ν ℓ x y
    (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans x y))
  rw [smallCommonCount_lintegral ν e f htrans x y s H,Finset.mul_sum]
  cases H with
  | zero => simp
  | succ H =>
    rw [Finset.sum_range_succ',Finset.sum_range_succ']
    calc
      _ ≤ (∑ j ∈ Finset.range H, μ (SmallCommonLayer e f s (signedHeight e x+(j+1))))+c := by
        apply add_le_add
        · exact Finset.sum_le_sum fun j _ =>
            physical_small_gap_truth_domination ν e f htrans x y hxy (Nat.succ_pos j) s c hc
        · simpa only [mul_one] using (mul_le_mul' (le_refl c) (show μ _ ≤ 1 from prob_le_one))
      _ ≤ _ := by
        rw [add_comm _ c]
        simp only [Nat.cast_add,Nat.cast_one,Nat.cast_zero]
        exact add_le_add_right (le_add_right le_rfl) c

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

noncomputable def occupationMacroConstant (A : ℝ) : ℝ :=
  max ((2:ℝ)^((7:ℝ)/4)) (A^2)*(2*A)^((3:ℝ)/2)

lemma occupationMacroConstant_pos {A : ℝ} (hA : 0 < A) : 0 < occupationMacroConstant A := by
  apply mul_pos
  · exact (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).trans_le (le_max_left _ _)
  · exact Real.rpow_pos_of_pos (mul_pos (by norm_num) hA) _

lemma occupation_coefficient_normalization {r n A : ℝ} (hr : 0 < r) (hn : 0 < n)
    (hA : 0 ≤ A) (C q M b ρ δ : ℝ) :
    occupationCoefficient (max ((2:ℝ)^((7:ℝ)/4)) (A^2)*n/r^((3:ℝ)/2)) C q M b r ρ A δ*
      (2*(A*r))^((3:ℝ)/2)/n =
    occupationMacroConstant A*(C*(b/r)^((1:ℝ)/4)/(q*((2:ℝ)^((3:ℝ)/2)-1))+
      M*(2*ρ)^((1:ℝ)/4)+M*A^((1:ℝ)/4)*δ) := by
  have hrp : r^((3:ℝ)/2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hr _)
  have he : 2*(A*r)=(2*A)*r := by ring
  rw [he,Real.mul_rpow (by positivity) hr.le]
  unfold occupationCoefficient occupationMacroConstant
  field_simp

lemma real_sum_le_of_ennreal_count {ι : Type*} [MeasurableSpace ι] {μ : Measure ι}
    [IsFiniteMeasure μ] (E : ℕ → Set ι) (H : ℕ) (B : ℝ) (F : Set ι)
    (hB : 0 ≤ B)
    (hb : (∑ j ∈ Finset.range H, μ (E j)) ≤ ENNReal.ofReal B+H*μ F) :
    (∑ j ∈ Finset.range H, μ.real (E j)) ≤ B+(H:ℝ)*μ.real F := by
  have hm : (H:ℝ≥0∞)*μ F ≠ ⊤ := ENNReal.mul_ne_top (by simp) (measure_ne_top μ _)
  have he := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,hm⟩) hb
  simpa only [ENNReal.toReal_sum (fun _ _ => measure_ne_top μ _),ENNReal.toReal_add ENNReal.ofReal_ne_top hm,
    ENNReal.toReal_ofReal hB,ENNReal.toReal_mul,ENNReal.toReal_natCast,measureReal_def] using he

lemma real_all_layer_bound {ι : Type*} [MeasurableSpace ι] {μ : Measure ι}
    [IsFiniteMeasure μ] (E F : ℕ → Set ι) (H : ℕ) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hb : c*(∑ j ∈ Finset.range H, μ (E j)) ≤ c+(∑ j ∈ Finset.range H, μ (F j))) :
    c.toReal*(∑ j ∈ Finset.range H, μ.real (E j)) ≤ c.toReal+(∑ j ∈ Finset.range H, μ.real (F j)) := by
  have hs : (∑ j ∈ Finset.range H, μ (F j)) ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun _ _ => measure_ne_top μ _)
  have he := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hc,hs⟩) hb
  simpa only [ENNReal.toReal_sum (fun _ _ => measure_ne_top μ _),ENNReal.toReal_add hc hs,
    ENNReal.toReal_mul,measureReal_def] using he

end DirectionalTransience

end

end

end OAI
