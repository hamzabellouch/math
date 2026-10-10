import Mathlib
import OAI.Probability.Ballisticity.Crossings.BoundaryFirstHits
import OAI.Probability.Ballisticity.Walk.BoundaryPathCoordinates
import OAI.Probability.Ballisticity.Estimates.SharedEndpointTests

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma boundaryTimes_height_identity {d : ℕ} (e : Direction d)
    (x y : Lattice d) (hxy : signedHeight e x = signedHeight e y)
    (H : ℕ) (hH : 0 < H) (P : Path d × Path d)
    (hx : P.1 ∈ RegularPath (realPosition (step e)) x)
    (hy : P.2 ∈ RegularPath (realPosition (step e)) y)
    (hc : ∃ k : ℕ, P ∈ CommonLayer (realPosition (step e)) (signedHeight e) (signedHeight e x+H+k)) :
    let ℓ := realPosition (step e)
    let J := H+commonOffset ℓ (signedHeight e) (signedHeight e x+H) P
    let nm := boundaryTimes ℓ ((signedHeight e x+H : ℤ) : ℝ) P
    signedHeight e (P.1 nm.1) = signedHeight e x+J ∧
      signedHeight e (P.2 nm.2) = signedHeight e y+J := by
  dsimp only
  let ℓ := realPosition (step e)
  obtain ⟨n,m,hn,hm,hD,hE⟩ := commonOffset_spec ℓ (signedHeight e) (signedHeight e x+H) P hc
  have hb := firstCommonLayer_boundaryAt ℓ (signedHeight e) (signedHeight_projection e)
    (signedHeight e x+H) P (by rw [hx.1]; omega) (by rw [hy.1,← hxy]; omega)
    n m hn hm hD hE
  rw [boundaryTimes_eq ℓ _ P hb]
  constructor
  · simpa only [Nat.cast_add,add_assoc] using hn.1
  · simpa only [← hxy,Nat.cast_add,add_assoc] using hm.1

lemma boundarySuffix_record_identity {d : ℕ} (e : Direction d)
    (x y : Lattice d) (hxy : signedHeight e x = signedHeight e y)
    (H : ℕ) (hH : 0 < H) (P : Path d × Path d)
    (hx : P.1 ∈ RegularPath (realPosition (step e)) x)
    (hy : P.2 ∈ RegularPath (realPosition (step e)) y)
    (hD : P.1 ∈ NoDrop (realPosition (step e)) x)
    (hE : P.2 ∈ NoDrop (realPosition (step e)) y)
    (hc : ∃ k : ℕ, P ∈ CommonLayer (realPosition (step e)) (signedHeight e) (signedHeight e x+H+k))
    (j : ℕ) :
    let ℓ := realPosition (step e)
    let L := ((signedHeight e x+H : ℤ) : ℝ)
    let S := boundarySuffix ℓ L P
    let z := boundaryTerminal (boundaryData ℓ L P)
    let J := H+commonOffset ℓ (signedHeight e) (signedHeight e x+H) P
    recordIndexPosition ℓ (j+J) (fun k => P.1 k-x) =
      recordIndexPosition ℓ j (fun k => S.1 k-z.1)+(z.1-x) ∧
    recordIndexPosition ℓ (j+J) (fun k => P.2 k-y) =
      recordIndexPosition ℓ j (fun k => S.2 k-z.2)+(z.2-y) := by
  dsimp only
  let ℓ := realPosition (step e)
  let L := ((signedHeight e x+H : ℤ) : ℝ)
  let nm := boundaryTimes ℓ L P
  have hb : BoundaryAt ℓ L P nm.1 nm.2 := by
    obtain ⟨n,m,hn,hm,hDn,hEm⟩ := commonOffset_spec ℓ (signedHeight e) (signedHeight e x+H) P hc
    apply boundaryTimes_spec
    exact ⟨n,m,firstCommonLayer_boundaryAt ℓ (signedHeight e) (signedHeight_projection e)
      (signedHeight e x+H) P (by rw [hx.1]; omega) (by rw [hy.1,← hxy]; omega)
      n m hn hm hDn hEm⟩
  obtain ⟨hn,hm⟩ := boundaryTimes_height_identity e x y hxy H hH P hx hy hc
  constructor
  · simpa only [boundarySuffix,boundaryTerminal_data,commonPairSuffix] using
      translated_recordIndexPosition_suffix e x P.1 hx hD nm.1 _ hb.1 hb.2.2.1.1 hn j
  · simpa only [boundarySuffix,boundaryTerminal_data,commonPairSuffix] using
      translated_recordIndexPosition_suffix e y P.2 hy hE nm.2 _ hb.2.1 hb.2.2.1.2.1 hm j

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

theorem shared_common_shift_at_any_height_small {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (e : Direction d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ))
    (hstep : ∀ z f, height (z+step f) ≤ height z+1)
    (x y : ℕ → Lattice d) (hxy : ∀ i, height (x i) = height (y i))
    (H J : ℕ → ℕ) (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) :
    Tendsto (fun i => (sharedConditionedPairLaw ν ℓ (x i) (y i)).real {P |
      let k := commonOffset ℓ height (height (x i)+H i) P
      r i ≤ |signedCoordinate e (recordIndexPosition ℓ (J i+k) (fun n => P.1 n-x i))-
        signedCoordinate e (recordIndexPosition ℓ (J i) (fun n => P.1 n-x i))| ∨
      r i ≤ |signedCoordinate e (recordIndexPosition ℓ (J i+k) (fun n => P.2 n-y i))-
        signedCoordinate e (recordIndexPosition ℓ (J i) (fun n => P.2 n-y i))|}) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨R,hR⟩ := shared_common_overshoot_tight ν hue ℓ hℓ htrans height hproj hstep
    (show 0 < ε/2 by positivity)
  have hfin := shared_finite_increment_small ν hue ℓ hℓ e htrans R x y J r hr
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hfin.eventually (gt_mem_nhds (show (0:ℝ) < ε/2 by positivity)))
  refine ⟨N,fun i hi => ?_⟩
  let μ := sharedConditionedPairLaw ν ℓ (x i) (y i)
  have hq := ne_of_gt (sharedNoDropMass_positive ν hue ℓ hℓ htrans (x i) (y i))
  let : IsProbabilityMeasure μ := sharedConditionedPairLaw_probability ν ℓ (x i) (y i) hq
  let A := {P : Path d × Path d |
      let k := commonOffset ℓ height (height (x i)+H i) P
      r i ≤ |signedCoordinate e (recordIndexPosition ℓ (J i+k) (fun n => P.1 n-x i))-
        signedCoordinate e (recordIndexPosition ℓ (J i) (fun n => P.1 n-x i))| ∨
      r i ≤ |signedCoordinate e (recordIndexPosition ℓ (J i+k) (fun n => P.2 n-y i))-
        signedCoordinate e (recordIndexPosition ℓ (J i) (fun n => P.2 n-y i))|}
  let B := NoCommonInterval ℓ height (height (x i)+H i) R
  let C := {P : Path d × Path d | (fun n => P.1 n-x i) ∈ FiniteHitOscillation ℓ e (J i) R (r i) ∨
    (fun n => P.2 n-y i) ∈ FiniteHitOscillation ℓ e (J i) R (r i)}
  have hsub : A ⊆ B ∪ C := by
    intro P hP
    by_cases hk : R < commonOffset ℓ height (height (x i)+H i) P
    · exact Or.inl (commonOffset_gt_subset ℓ height _ R hk)
    · apply Or.inr
      rcases hP with hP | hP
      · exact Or.inl ⟨_,by omega,hP⟩
      · exact Or.inr ⟨_,by omega,hP⟩
  have hh := (ENNReal.toReal_mono (measure_ne_top μ (B ∪ C)) (measure_mono (μ := μ) hsub)).trans (measureReal_union_le B C)
  change μ.real A ≤ μ.real B + μ.real C at hh
  have hb : μ.real B < ε/2 := hR (x i) (y i) (hxy i) (H i)
  have hc : μ.real C < ε/2 := hN i hi
  change dist (μ.real A) 0 < ε
  rw [Real.dist_eq,sub_zero,abs_of_nonneg measureReal_nonneg]
  linarith

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma recordIndexPosition_at_zero {d : ℕ} (ℓ : Vector d) (X : Path d) :
    recordIndexPosition ℓ 0 X = X 0 := by simp [recordIndexPosition,recordIndexTime_zero]

noncomputable def centeredHitIncrement {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r : ℝ) (H k : ℕ) (x : Lattice d) (X : Path d) : ℝ :=
  (signedCoordinate f (recordIndexPosition ℓ (H+k) (fun j => X j-x))-
    signedCoordinate f (recordIndexPosition ℓ H (fun j => X j-x))-(k:ℝ)*θ)/r

lemma measurable_centeredHitIncrement {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r : ℝ) (H k : ℕ) (x : Lattice d) : Measurable (centeredHitIncrement ℓ f θ r H k x) := by
  apply Measurable.div_const
  apply Measurable.sub_const
  apply Measurable.sub
  · exact ((measurable_of_countable (signedCoordinate f)).comp (measurable_recordIndexPosition ℓ _)).comp (by fun_prop)
  · exact ((measurable_of_countable (signedCoordinate f)).comp (measurable_recordIndexPosition ℓ _)).comp (by fun_prop)

lemma boundary_centered_increment_identity {d : ℕ} (e f : Direction d)
    (x y : Lattice d) (hxy : signedHeight e x = signedHeight e y)
    (H : ℕ) (hH : 0 < H) (P : Path d × Path d)
    (hx : P.1 ∈ RegularPath (realPosition (step e)) x)
    (hy : P.2 ∈ RegularPath (realPosition (step e)) y)
    (hD : P.1 ∈ NoDrop (realPosition (step e)) x)
    (hE : P.2 ∈ NoDrop (realPosition (step e)) y)
    (hc : ∃ k : ℕ, P ∈ CommonLayer (realPosition (step e)) (signedHeight e) (signedHeight e x+H+k))
    (k : ℕ) (θ r : ℝ) (b : Bool) :
    let ℓ := realPosition (step e)
    let L := ((signedHeight e x+H : ℤ) : ℝ)
    let K := commonOffset ℓ (signedHeight e) (signedHeight e x+H) P
    centeredFirstHit ℓ f θ r k (pairSide b (boundaryTerminal (boundaryData ℓ L P)))
      (pairSide b (boundarySuffix ℓ L P)) =
    centeredHitIncrement ℓ f θ r (H+K) k (pairSide b (x,y)) (pairSide b P) := by
  dsimp only
  have h0 := boundarySuffix_record_identity e x y hxy H hH P hx hy hD hE hc 0
  have hk := boundarySuffix_record_identity e x y hxy H hH P hx hy hD hE hc k
  dsimp only at h0 hk
  simp only [zero_add,recordIndexPosition_at_zero,boundarySuffix,commonPairSuffix,
    Nat.add_zero,boundaryTerminal_data,sub_self,zero_add] at h0
  cases b
  · simp only [pairSide,Bool.false_eq_true,ite_false,centeredFirstHit,centeredHitIncrement]
    rw [show H+commonOffset (realPosition (step e)) (signedHeight e) (signedHeight e x+H) P+k =
      k+(H+commonOffset (realPosition (step e)) (signedHeight e) (signedHeight e x+H) P) by omega]
    rw [hk.1,h0.1]
    simp only [signedCoordinate_add,signedCoordinate_sub,boundaryTerminal_data]
    ring
  · simp only [pairSide,ite_true,centeredFirstHit,centeredHitIncrement]
    rw [show H+commonOffset (realPosition (step e)) (signedHeight e) (signedHeight e x+H) P+k =
      k+(H+commonOffset (realPosition (step e)) (signedHeight e) (signedHeight e x+H) P) by omega]
    rw [hk.2,h0.2]
    simp only [signedCoordinate_add,signedCoordinate_sub,boundaryTerminal_data]
    ring

theorem shared_boundary_increment_replacement {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i) = signedHeight e (y i))
    (H k : ℕ → ℕ) (hH : ∀ i, 0 < H i) (θ r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (b : Bool) (ε : ℝ) (hε : 0 < ε) :
    let ℓ := realPosition (step e)
    let L := fun i => ((signedHeight e (x i)+H i : ℤ) : ℝ)
    Tendsto (fun i => (sharedConditionedPairLaw ν ℓ (x i) (y i)).real {P |
      ε ≤ |centeredHitIncrement ℓ f (θ i) (r i) (H i) (k i) (pairSide b (x i,y i)) (pairSide b P)-
        centeredFirstHit ℓ f (θ i) (r i) (k i)
          (pairSide b (boundaryTerminal (boundaryData ℓ (L i) P)))
          (pairSide b (boundarySuffix ℓ (L i) P))|}) atTop (𝓝 0) := by
  dsimp only
  let ℓ := realPosition (step e)
  let μ := fun i => sharedConditionedPairLaw ν ℓ (x i) (y i)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => sharedConditionedPairLaw_probability ν ℓ _ _
    (ne_of_gt (sharedNoDropMass_positive ν hue ℓ (signed_direction_unit e) htrans _ _))
  let U := fun (i j : ℕ) (P : Path d × Path d) => signedCoordinate f (recordIndexPosition ℓ j
    (fun n => pairSide b P n-pairSide b (x i,y i)))
  let K := fun (i : ℕ) (P : Path d × Path d) => commonOffset ℓ (signedHeight e) (signedHeight e (x i)+H i) P
  let A := fun (J : ℕ → ℕ) i => {P : Path d × Path d | (ε/2)*r i ≤ |U i (J i+K i P) P-U i (J i) P|}
  have hA (J : ℕ → ℕ) : Tendsto (fun i => (μ i).real (A J i)) atTop (𝓝 0) := by
    have hh := shared_common_shift_at_any_height_small ν hue ℓ (signed_direction_unit e) f htrans
      (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) x y hxy H J
      (fun i => (ε/2)*r i) (hr.const_mul_atTop (by positivity))
    apply squeeze_zero (fun _ => measureReal_nonneg) _ hh
    intro i
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro P hP
    cases b
    · exact Or.inl hP
    · exact Or.inr hP
  have hsum := (hA H).add (hA (fun i => H i+k i))
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hsum
  filter_upwards [hr.eventually (eventually_gt_atTop (0:ℝ))] with i hri
  apply le_trans _ (measureReal_union_le (A H i) (A (fun j => H j+k j) i))
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [sharedConditioned_regularPath ν ℓ htrans (x i) (y i),
    shared_common_boundary_exists ν hue ℓ (signed_direction_unit e) htrans (signedHeight e)
      (signedHeight_projection e) (signedHeight_step_le e) (x i) (y i) (hxy i) (H i)] with P hP hc
  intro hh
  have he := boundary_centered_increment_identity e f (x i) (y i) (hxy i) (H i) (hH i) P
    hP.1.1 hP.2.1 hP.1.2 hP.2.2 hc (k i) (θ i) (r i) b
  dsimp only at he
  change ε ≤ |_ - _| at hh
  rw [he] at hh
  change P ∈ A H i ∪ A (fun j => H j+k j) i
  by_contra hnot
  simp only [Set.mem_union,not_or, A,Set.mem_ofPred_eq,not_le] at hnot
  have hdiff : |(U i (H i+k i) P-U i (H i) P-(k i:ℝ)*θ i)/r i-
      (U i (H i+K i P+k i) P-U i (H i+K i P) P-(k i:ℝ)*θ i)/r i| < ε := by
    have huv : |(U i (H i+k i) P-U i (H i) P-(k i:ℝ)*θ i)-
        (U i (H i+K i P+k i) P-U i (H i+K i P) P-(k i:ℝ)*θ i)| ≤
        |U i (H i+k i+K i P) P-U i (H i+k i) P|+|U i (H i+K i P) P-U i (H i) P| := by
      rw [show H i+K i P+k i = H i+k i+K i P by omega]
      calc
        _ = |-(U i (H i+k i+K i P) P-U i (H i+k i) P)+
            (U i (H i+K i P) P-U i (H i) P)| := by congr 1; ring
        _ ≤ |-(U i (H i+k i+K i P) P-U i (H i+k i) P)|+
            |U i (H i+K i P) P-U i (H i) P| := abs_add_le _ _
        _ = _ := by rw [abs_neg]
    rw [← sub_div,abs_div,abs_of_pos hri,div_lt_iff₀ hri]
    linarith [hnot.1,hnot.2]
  exact not_lt_of_ge hh hdiff

end DirectionalTransience

end

end

end OAI
