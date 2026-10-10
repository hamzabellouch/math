import Mathlib
import OAI.Probability.Ballisticity.Estimates.SharedConditionedContactBound
import OAI.Probability.Ballisticity.Walk.RegularPath

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma coordinate_lanes_disjoint {d : ℕ} (f : Direction d) (x y : Lattice d)
    (c R : ℝ) (hR : 0 < R) (hxy : R ≤ |signedCoordinate f (y-x)|) :
    Disjoint {z | |signedCoordinate f z-(signedCoordinate f x+c)| < R/3}
      {z | |signedCoordinate f z-(signedCoordinate f y+c)| < R/3} := by
  apply Set.disjoint_left.mpr
  intro z hx hy
  change |signedCoordinate f z-(signedCoordinate f x+c)| < R/3 at hx
  change |signedCoordinate f z-(signedCoordinate f y+c)| < R/3 at hy
  have he : signedCoordinate f (y-x) =
      (signedCoordinate f z-(signedCoordinate f x+c))-(signedCoordinate f z-(signedCoordinate f y+c)) := by
    rw [signedCoordinate_sub]
    ring
  have hh := abs_sub (signedCoordinate f z-(signedCoordinate f x+c))
    (signedCoordinate f z-(signedCoordinate f y+c))
  rw [← he] at hh
  have hlt := add_lt_add hx hy
  have h := hxy.trans hh
  linarith

lemma shared_contact_endpoint_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (x y : Lattice d) (hxy : signedHeight e x = signedHeight e y)
    {k : ℕ} (hk : 0 < k) (θ : ℝ) {r a : ℝ} (hr : 0 < r) (ha : 0 < a)
    (hsep : a*r ≤ |signedCoordinate f (y-x)|) :
    let ℓ := realPosition (step e)
    let μ := sharedConditionedPairLaw ν ℓ x y
    μ.real (PrefixContact (Strip ℓ x k)) ≤ 2*(
      μ.real {Z | a/3 ≤ |scaledRecordEndpoint ℓ f θ r k x Z.1|}+
      μ.real {Z | a/3 ≤ |scaledRecordEndpoint ℓ f θ r k y Z.2|}) := by
  let ℓ := realPosition (step e)
  let μ := sharedConditionedPairLaw ν ℓ x y
  let : IsProbabilityMeasure μ := sharedConditionedPairLaw_probability ν ℓ x y
    (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans x y))
  let U := {z | dot (realPosition x) ℓ ≤ dot (realPosition z) ℓ}
  let T := Upper ℓ x k
  let A := {z | |signedCoordinate f z-(signedCoordinate f x+(k:ℝ)*θ)| < (a/3)*r}
  let B := {z | |signedCoordinate f z-(signedCoordinate f y+(k:ℝ)*θ)| < (a/3)*r}
  have hp : dot (realPosition x) ℓ = dot (realPosition y) ℓ := by
    simp only [ℓ,signedHeight_projection,hxy]
  have hAB : Disjoint A B := by
    have hh := coordinate_lanes_disjoint f x y ((k:ℝ)*θ) (a*r) (mul_pos ha hr) hsep
    have he : a / 3 * r = a * r / 3 := by ring
    simpa only [A,B,he] using hh
  have hS : U \ T = Strip ℓ x k := by
    ext z
    change (dot (realPosition x) ℓ ≤ dot (realPosition z) ℓ ∧
      ¬ dot (realPosition x) ℓ + (k:ℝ) ≤ dot (realPosition z) ℓ) ↔
      (dot (realPosition x) ℓ ≤ dot (realPosition z) ℓ ∧
      dot (realPosition z) ℓ < dot (realPosition x) ℓ + (k:ℝ))
    exact and_congr_right fun _ => not_le
  have he₁ : μ (Prod.fst ⁻¹' (SurvivingLane U T A)ᶜ) =
      μ {Z | a/3 ≤ |scaledRecordEndpoint ℓ f θ r k x Z.1|} := by
    apply measure_congr
    filter_upwards [sharedConditioned_regularPath ν ℓ htrans x y] with Z hZ
    apply propext
    exact not_congr (open_lane_record_iff e f x Z.1 hZ.1.1 hZ.1.2 hk θ r (a/3) hr) |>.trans not_lt
  have he₂ : μ (Prod.snd ⁻¹' (SurvivingLane U T B)ᶜ) =
      μ {Z | a/3 ≤ |scaledRecordEndpoint ℓ f θ r k y Z.2|} := by
    apply measure_congr
    filter_upwards [sharedConditioned_regularPath ν ℓ htrans x y] with Z hZ
    have hU : U = {z | dot (realPosition y) ℓ ≤ dot (realPosition z) ℓ} := by unfold U; rw [hp]
    have hT : T = Upper ℓ y k := by unfold T Upper; rw [hp]
    apply propext
    change (Z.2 ∉ SurvivingLane U T B) ↔ _
    rw [hU,hT]
    exact not_congr (open_lane_record_iff e f y Z.2 hZ.2.1 hZ.2.2 hk θ r (a/3) hr) |>.trans not_lt
  have hb := shared_conditioned_contact_bound ν ℓ x y hp T A B hAB
  change μ (PrefixContact (U \ T)) ≤ 2*(_+_) at hb
  rw [hS,he₁,he₂] at hb
  have hh := ENNReal.toReal_mono (show 2*(μ _+μ _) ≠ ∞ by finiteness) hb
  simpa only [Measure.real,ENNReal.toReal_mul,ENNReal.toReal_ofNat,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] using hh

theorem shared_contact_limsup {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hrpos : ∀ i, 0 < r i)
    (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i) = signedHeight e (y i))
    {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (hsep : ∀ i, a*r i ≤ |signedCoordinate f (y i-x i)|) :
    let ℓ := realPosition (step e)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    limsup (fun i => (sharedConditionedPairLaw ν ℓ (x i) (y i)).real
      (PrefixContact (Strip ℓ (x i) (⌊t*n i⌋₊ : ℝ)))) atTop ≤
      8*Real.exp (-commonMeanWidth ν ℓ*a^2/(9*t)) := by
  let ℓ := realPosition (step e)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let θ := fun i => recordMedianSlope ν ℓ (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)) f (r i)
  let μ := fun i => sharedConditionedPairLaw ν ℓ (x i) (y i)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => sharedConditionedPairLaw_probability ν ℓ (x i) (y i)
    (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans (x i) (y i)))
  let F := fun i (Z : Path d × Path d) => scaledRecordEndpoint ℓ f (θ i) (r i) ⌊t*n i⌋₊ (x i) Z.1
  let G := fun i (Z : Path d × Path d) => scaledRecordEndpoint ℓ f (θ i) (r i) ⌊t*n i⌋₊ (y i) Z.2
  have hF (i : ℕ) : Measurable (F i) := (measurable_scaledRecordEndpoint _ _ _ _ _ _).comp measurable_fst
  have hG (i : ℕ) : Measurable (G i) := (measurable_scaledRecordEndpoint _ _ _ _ _ _).comp measurable_snd
  let p := fun i => (μ i).real {Z | a/3 ≤ |F i Z|}
  let q := fun i => (μ i).real {Z | a/3 ≤ |G i Z|}
  let c := fun i => (μ i).real (PrefixContact (Strip ℓ (x i) (⌊t*n i⌋₊ : ℝ)))
  have hM : 0 < commonMeanWidth ν ℓ := lt_of_lt_of_le (by norm_num : (0:ℝ)<1)
    (commonMeanWidth_ge_one ν ℓ htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e))
  have hv : 0 < t/(2*commonMeanWidth ν ℓ) := div_pos ht (mul_pos (by norm_num) hM)
  have hh := shared_endpoint_limits ν hue e f hef htrans r hrpos hr x y hxy ht
  have hcoe : ((t/(2*commonMeanWidth ν (realPosition (step e)))).toNNReal : ℝ) =
      t/(2*commonMeanWidth ν ℓ) := Real.coe_toNNReal _ hv.le
  let R := 2*Real.exp (-(a/3)^2/(2*(t/(2*commonMeanWidth ν ℓ))))
  have hp : limsup p atTop ≤ R := by
    have hh' := distribution_abs_limsup μ F hF _ (by simpa only [hcoe] using hv)
      hh.1 (a/3) (by positivity)
    simpa only [hcoe] using hh'
  have hq : limsup q atTop ≤ R := by
    have hh' := distribution_abs_limsup μ G hG _ (by simpa only [hcoe] using hv)
      hh.2 (a/3) (by positivity)
    simpa only [hcoe] using hh'
  have hn := recordFluctuationScale_tendsto ν hue e f hef htrans r hr.1
  have hk : ∀ᶠ i in atTop, 0 < ⌊t*n i⌋₊ := by
    have hn' : Tendsto (fun i => t*n i) atTop atTop := hn.const_mul_atTop ht
    filter_upwards [hn'.eventually_ge_atTop 1] with i hi
    exact Nat.floor_pos.mpr hi
  have hb : ∀ᶠ i in atTop, c i ≤ 2*(p i+q i) := hk.mono fun i hi =>
    shared_contact_endpoint_bound ν hue e f htrans (x i) (y i) (hxy i) hi (θ i) (hrpos i) ha (hsep i)
  have hb₁ : IsBoundedUnder (· ≤ ·) atTop p := by
    refine ⟨1, ?_⟩
    change ∀ᶠ i in atTop, _ ≤ (1:ℝ)
    exact Eventually.of_forall fun i => measureReal_le_one
  have hb₂ : IsBoundedUnder (· ≤ ·) atTop q := by
    refine ⟨1, ?_⟩
    change ∀ᶠ i in atTop, _ ≤ (1:ℝ)
    exact Eventually.of_forall fun i => measureReal_le_one
  have hc₁ : IsCoboundedUnder (· ≤ ·) atTop c :=
    (show IsBoundedUnder (· ≥ ·) atTop c from ⟨0,
      (show ∀ᶠ i in atTop, 0 ≤ c i from Eventually.of_forall fun i => measureReal_nonneg)⟩).isCoboundedUnder_le
  have hc₂ : IsBoundedUnder (· ≤ ·) atTop c := by
    refine ⟨1, ?_⟩
    change ∀ᶠ i in atTop, _ ≤ (1:ℝ)
    exact Eventually.of_forall fun i => measureReal_le_one
  have hc : limsup c atTop ≤ 4*R := (limsup_le_iff hc₁ hc₂).mpr (by
    intro b hb'
    have hp' := eventually_lt_of_limsup_lt (hp.trans_lt (show R < R+(b-4*R)/8 by linarith)) hb₁
    have hq' := eventually_lt_of_limsup_lt (hq.trans_lt (show R < R+(b-4*R)/8 by linarith)) hb₂
    filter_upwards [hb,hp',hq'] with i hi hp' hq'
    linarith)
  have he : -(a/3)^2/(2*(t/(2*commonMeanWidth ν ℓ))) = -commonMeanWidth ν ℓ*a^2/(9*t) := by
    field_simp
    ring
  simpa only [R,he,← mul_assoc,show (4:ℝ)*2=8 by norm_num] using hc

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
