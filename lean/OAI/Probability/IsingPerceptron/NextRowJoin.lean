import Mathlib
import OAI.Probability.IsingPerceptron.MomentLogLimit

namespace OAI

/-! Next Row Join. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def prefixExtend {A : Type*} (m : ℕ) (a : A) (x : Fin m → A) (i : ℕ) : A :=
  if h : i < m then x ⟨i,h⟩ else a

lemma measurable_prefixExtend {A : Type*} [MeasurableSpace A] (m : ℕ) (a : A) :
    Measurable (prefixExtend m a) := by
  apply Measurable.of_eval
  intro i
  unfold prefixExtend
  split_ifs <;> fun_prop

lemma prefixExtend_coe {A : Type*} (m : ℕ) (a : A) (x : Fin m → A) (i : Fin m) :
    prefixExtend m a x i = x i := by simp [prefixExtend,i.isLt]

lemma integral_next_row_of_prefixInvariant {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure B) [IsProbabilityMeasure Q]
    (m : ℕ) (F : (ℕ → A) × B × A → ℝ) (hF : Measurable F)
    (hpref : ∀ x y : ℕ → A, (∀ i : Fin m, x i = y i) → ∀ b a, F (x,b,a) = F (y,b,a)) :
    (∫ z : (ℕ → A) × B, F (z.1,z.2,z.1 m)
      ∂(Measure.infinitePi (fun _ : ℕ => P)).prod Q) =
    ∫ z : ((ℕ → A) × B) × A, F (z.1.1,z.1.2,z.2)
      ∂((Measure.infinitePi (fun _ : ℕ => P)).prod Q).prod P := by
  let a := (nonempty_of_isProbabilityMeasure P).some
  let H : (Fin m → A) × B × A → ℝ := fun z => F (prefixExtend m a z.1,z.2)
  have hH : Measurable H := hF.comp (((measurable_prefixExtend m a).comp measurable_fst).prodMk measurable_snd)
  have he (x : ℕ → A) (b : B) (a' : A) : F (x,b,a') = H ((fun i => x i),b,a') :=
    hpref x _ (fun i => (prefixExtend_coe m a (fun j : Fin m => x j) i).symm) b a'
  simp_rw [he]
  exact integral_next_row_of_prefix P Q m H hH

lemma measurable_random_cgf_one {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {F : Ω × X → ℝ} (hF : Measurable F) :
    Measurable (fun ω => cgf (fun x => F (ω,x)) (ν ω) 1) := by
  simpa only [cgf,mgf,one_mul,referencePartition] using (measurable_random_referencePartition hν hF).log

def enrichedFreshRowCGF {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) (φ : A → Spin N → ℝ)
    (z : EnrichedCylinderData n A × A) : ℝ :=
  cgf (fun s : Spin N × LabeledLeaf n => φ z.2 s.1) (enrichedGibbs n h u ν φ z.1) 1

lemma measurable_enrichedFreshRowCGF {N : ℕ} {A : Type*} [MeasurableSpace A]
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) : Measurable (enrichedFreshRowCGF n h u ν φ) := by
  apply measurable_random_cgf_one
    (ν := fun z : EnrichedCylinderData n A × A => enrichedGibbs n h u ν φ z.1)
    (F := fun z : (EnrichedCylinderData n A × A) × (Spin N × LabeledLeaf n) => φ z.1.2 z.2.1)
    ((measurable_enrichedGibbs n h u ν hm).comp measurable_fst)
  exact measurable_from_prod_countable_left (fun s =>
    (measurable_pi_apply s.1).comp (hm.comp measurable_snd))

lemma enrichedGibbs_prefix_congr {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) (φ : A → Spin N → ℝ)
    (m : ℕ) (x y : ℕ → A) (he : ∀ i : Fin m, x i = y i)
    (t : LabeledTree n) (g : ℕ → ℝ) :
    enrichedGibbs n h u ν φ (enrichedCountJoin (m,((x,t),g))) =
      enrichedGibbs n h u ν φ (enrichedCountJoin (m,((y,t),g))) := by
  have heq : (fun i : Fin m => x i) = fun i : Fin m => y i := funext he
  unfold enrichedGibbs enrichedHamiltonian enrichedCountJoin
  dsimp only
  rw [heq]

 

theorem enrichedNextPatternCGF_eq_independent {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) (m : ℕ) :
    (∫ z, enrichedNextPatternCGF n h u ν φ m z ∂enrichedFixedLaw P n b) =
      ∫ z : EnrichedFixedData n A × A,
        enrichedFreshRowCGF n h u ν φ (enrichedCountJoin (m,z.1),z.2)
        ∂(enrichedFixedLaw P n b).prod P := by
  let R := Measure.infinitePi (fun _ : ℕ => P)
  let T := (labeledCascadeLaw n b : Measure (LabeledTree n))
  let Q := T.prod gaussianCoordinates
  let F : (ℕ → A) × (LabeledTree n × (ℕ → ℝ)) × A → ℝ := fun z =>
    enrichedFreshRowCGF n h u ν φ (enrichedCountJoin (m,((z.1,z.2.1.1),z.2.1.2)),z.2.2)
  have hF : Measurable F := (measurable_enrichedFreshRowCGF n h u ν hm).comp (by
    unfold enrichedCountJoin; fun_prop)
  have he := integral_next_row_of_prefixInvariant P Q m F hF (by
    intro x y hxy z a
    unfold F enrichedFreshRowCGF
    rw [enrichedGibbs_prefix_congr n h u ν φ m x y hxy])
  have hleft : Measurable (fun z : (ℕ → A) × (LabeledTree n × (ℕ → ℝ)) => F (z.1,z.2,z.1 m)) :=
    hF.comp (by fun_prop)
  have hright : Measurable (fun z : ((ℕ → A) × (LabeledTree n × (ℕ → ℝ))) × A => F (z.1.1,z.1.2,z.2)) :=
    hF.comp (by fun_prop)
  have hl := (measurePreserving_prodAssoc R T gaussianCoordinates).hasLaw.integral_comp hleft.aestronglyMeasurable
  have hr := ((measurePreserving_prodAssoc R T gaussianCoordinates).prod
    (MeasurePreserving.id P)).hasLaw.integral_comp hright.aestronglyMeasurable
  calc
    _ = ∫ z : (ℕ → A) × (LabeledTree n × (ℕ → ℝ)), F (z.1,z.2,z.1 m) ∂(R.prod Q) := hl
    _ = _ := he
    _ = _ := hr.symm

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma abs_enrichedFreshRowCGF_le {N : ℕ} {A : Type*}
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} {K : ℝ} (hφ : ∀ y x, |φ y x| ≤ K)
    (z : EnrichedCylinderData n A × A) : |enrichedFreshRowCGF n h u ν φ z| ≤ K :=
  abs_cgf_one_le _ (measurable_of_countable _) (fun s => hφ z.2 s.1)

lemma enrichedFreshRowCGF_integrable {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hφ : ∀ y x, |φ y x| ≤ K) :
    Integrable (enrichedFreshRowCGF n h u ν φ) ((enrichedCylinderLaw P r n b).prod P) :=
  Integrable.of_bound (measurable_enrichedFreshRowCGF n h u ν hm).aestronglyMeasurable K
    (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using abs_enrichedFreshRowCGF_le n h u ν hφ z))

lemma enrichedNextPatternCGF_mean {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hφ : ∀ y x, |φ y x| ≤ K) :
    (∫ m, ∫ z, enrichedNextPatternCGF n h u ν φ m z ∂enrichedFixedLaw P n b ∂poissonMeasure r) =
      ∫ z, enrichedFreshRowCGF n h u ν φ z ∂(enrichedCylinderLaw P r n b).prod P := by
  simp_rw [enrichedNextPatternCGF_eq_independent P n b h u ν hm]
  let F := enrichedFreshRowCGF n h u ν φ
  let Q := enrichedFixedLaw P n b
  let J : (ℕ × EnrichedFixedData n A) × A → EnrichedCylinderData n A × A :=
    Prod.map enrichedCountJoin id
  have hJ := (enrichedCountJoin_preserving P r n b).prod (MeasurePreserving.id P)
  have hi := hJ.integrable_comp_of_integrable (enrichedFreshRowCGF_integrable P r n b h u ν hm hφ)
  have hA := measurePreserving_prodAssoc (poissonMeasure r) Q P
  have hiA := (hA.symm MeasurableEquiv.prodAssoc).integrable_comp_of_integrable hi
  calc
    _ = ∫ z : ℕ × (EnrichedFixedData n A × A), F (enrichedCountJoin (z.1,z.2.1),z.2.2)
        ∂(poissonMeasure r).prod (Q.prod P) := (integral_prod _ hiA).symm
    _ = ∫ z : (ℕ × EnrichedFixedData n A) × A, F (J z)
        ∂((poissonMeasure r).prod Q).prod P :=
      (hA.hasLaw.integral_comp (hiA.aestronglyMeasurable)).symm
    _ = _ := hJ.hasLaw.integral_comp (measurable_enrichedFreshRowCGF n h u ν hm).aestronglyMeasurable

 
theorem enrichedMeanPressure_fresh_time_derivative {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => -enrichedMeanPressure P (Real.toNNReal (N*s)) n b h u ν φ)
      (-(∫ z, enrichedFreshRowCGF n h u ν φ z
        ∂(enrichedCylinderLaw P (Real.toNNReal (N*t)) n b).prod P)) t := by
  simpa only [enrichedNextPatternCGF_mean P _ n b h u ν hm hφ] using
    enrichedMeanPressure_time_derivative hN n b hb hh h0 u hu ν P hm hK hφ ht

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

 

def spinRowCoefficients {N : ℕ} (x : Spin N) : ℕ →₀ ℝ :=
  featureCoefficients Fin.val (spinCoordinate x)

lemma spinRowCoefficients_cross {N : ℕ} (x y : Spin N) :
    cylinderCross (spinRowCoefficients x) (spinRowCoefficients y) = spinOverlap x y := by
  rw [spinRowCoefficients,spinRowCoefficients,
    featureCoefficients_diagonal Fin.val Fin.val (fun _ _ h => Fin.ext h)]
  simpa using spinCoordinate_cross x y

lemma cylinderField_spinRow {N : ℕ} (x : Spin N) (g : ℕ → ℝ) :
    cylinderField (spinRowCoefficients x) g =
      (∑ i : Fin N, g i * spinValue (x i)) / Real.sqrt (N:ℝ) := by
  rw [spinRowCoefficients,cylinderField_feature]
  simp only [spinCoordinate, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

def gaussianRowActivation {N : ℕ} (f : ℝ → ℝ) (g : ℕ → ℝ) (x : Spin N) : ℝ :=
  f (cylinderField (spinRowCoefficients x) g)

lemma measurable_gaussianRowActivation {N : ℕ} {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (gaussianRowActivation (N := N) f) := by
  apply Measurable.of_eval
  intro x
  exact hf.comp (measurable_cylinderField _)

lemma freshRowCGF_gaussian {N : ℕ} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν] (f : ℝ → ℝ)
    (z : EnrichedCylinderData n (ℕ → ℝ) × (ℕ → ℝ)) :
    enrichedFreshRowCGF n h u ν (gaussianRowActivation f) z =
      Real.log (freshPatternFactor (enrichedGibbs n h u ν (gaussianRowActivation f) z.1)
        (fun s => spinRowCoefficients s.1) f z.2) := by
  simp only [enrichedFreshRowCGF,cgf,mgf,one_mul,freshPatternFactor,gaussianRowActivation]

 

theorem enriched_gaussian_fresh_limit
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop)
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (H : ℝ) (hH : ∀ k, h k n ≤ H)
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, u k j ∈ Icc (1:ℝ) 2)
    (ν : (k : ℕ) → Measure (Spin (N k))) [∀ k, IsProbabilityMeasure (ν k)]
    {f : ℝ → ℝ} (hf : Continuous f) (K : ℝ) (hK : ∀ x, |f x| ≤ K)
    (r : ℕ → ℝ≥0) (α : ℝ) (hr : ∀ k, (r k:ℝ) ≤ α*N k)
    (hmin : ∀ k (v : Fin (N k) → ℝ), (∀ j, v j ∈ Icc (1:ℝ) 2) →
      enrichedPerturbationObjective gaussianCoordinates (r k) n b (h k) (ν k) (gaussianRowActivation f) (u k) ≤
        enrichedPerturbationObjective gaussianCoordinates (r k) n b (h k) (ν k) (gaussianRowActivation f) v)
    (μ : ProbabilityMeasure JointArray)
    (hL : Tendsto (fun k => enrichedArrayLaw gaussianCoordinates (r k) n b (h k) (u k) (ν k)
      (measurable_gaussianRowActivation hf.measurable)) atTop (𝓝 μ))
    (q : OverlapPath)
    (hq : quantileFunction ((μ : Measure JointArray).map (fun x => spinArray x 0 1)) =ᵐ[pathMeasure] q.val) :
    Tendsto (fun k => ∫ z, enrichedFreshRowCGF n (h k) (u k) (ν k) (gaussianRowActivation f) z
      ∂(enrichedCylinderLaw gaussianCoordinates (r k) n b).prod gaussianCoordinates)
      atTop (𝓝 (patternFunctional f q)) := by
  have hφ : ∀ k (y : ℕ → ℝ) (x : Spin (N k)), |gaussianRowActivation f y x| ≤ K :=
    fun k y x => hK _
  have hGG := enriched_minimizers_jointGG N hN hNlim n b hb h hh h0 H hH u hu ν
    (fun _ => ℕ → ℝ) (fun _ => gaussianCoordinates) (fun _ => gaussianRowActivation f)
    (fun _ => measurable_gaussianRowActivation hf.measurable) K ((abs_nonneg (f 0)).trans (hK 0))
    hφ r α hr hmin μ hL
  simp_rw [freshRowCGF_gaussian]
  exact freshPattern_array_limit
    (fun k => enrichedCylinderLaw gaussianCoordinates (r k) n b)
    (fun k => enrichedGibbs n (h k) (u k) (ν k) (gaussianRowActivation f))
    (fun k => measurable_enrichedGibbs n (h k) (u k) (ν k) (measurable_gaussianRowActivation hf.measurable))
    (fun k s => spinRowCoefficients s.1) (fun k => enrichedJointEntry (N := N k) n)
    (fun k s t => spinRowCoefficients_cross s.1 t.1)
    (fun k s => spinOverlap_self (hN k) s.1) μ hL
    (hGG.real_map (f := fun x => x.1.1) (by fun_prop)) q hq hf hK

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma left_derivative_nonpos_of_min {F : ℝ → ℝ} {D t : ℝ}
    (hD : HasDerivAt F D t)
    (hmin : ∀ᶠ a in 𝓝[>] (0:ℝ), F t ≤ F (t-a)) : D ≤ 0 := by
  have hDf : HasDerivAt F D (t-id 0) := by simpa using hD
  have hd := hDf.comp 0 ((hasDerivAt_id (0:ℝ)).const_sub t)
  simp only [mul_neg_one] at hd
  have hn := right_derivative_nonneg_of_min hd.hasDerivWithinAt (by simpa only [Function.comp_apply, sub_zero] using hmin)
  linarith

 

theorem enriched_time_minimum_fresh {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) {r rmax : ℝ≥0} (hr : 0 < r) (hrmax : r≤rmax) (v : ℝ)
    (hmin : ∀ s : ℝ≥0, s≤rmax →
      -enrichedMeanPressure P r n b h u ν φ+((r:ℝ)/N)*v ≤
        -enrichedMeanPressure P s n b h u ν φ+((s:ℝ)/N)*v) :
    v ≤ ∫ z, enrichedFreshRowCGF n h u ν φ z ∂(enrichedCylinderLaw P r n b).prod P := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  let t : ℝ := (r:ℝ)/N
  have ht : 0<t := div_pos (by exact_mod_cast hr) hn
  have hrt : Real.toNNReal ((N:ℝ)*t)=r := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (mul_nonneg hn.le ht.le)]
    dsimp only [t]
    field_simp
  have hd := (enrichedMeanPressure_fresh_time_derivative hN n b hb hh h0 u hu ν P hm hK hφ ht).add
    ((hasDerivAt_id t).mul_const v)
  simp only [one_mul,hrt] at hd
  have hm' : ∀ᶠ a in 𝓝[>] (0:ℝ),
      -enrichedMeanPressure P (Real.toNNReal (N*t)) n b h u ν φ+t*v ≤
        -enrichedMeanPressure P (Real.toNNReal (N*(t-a))) n b h u ν φ+(t-a)*v := by
    have he : ∀ᶠ a in 𝓝[>] (0:ℝ), a<t :=
      (eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds
    filter_upwards [he,self_mem_nhdsWithin] with a ha ha'
    let s := Real.toNNReal ((N:ℝ)*(t-a))
    have hs0 : 0≤(N:ℝ)*(t-a) := mul_nonneg hn.le (sub_nonneg.mpr ha.le)
    have hs : s≤rmax := by
      apply le_trans _ hrmax
      rw [← hrt]
      exact Real.toNNReal_le_toNNReal (mul_le_mul_of_nonneg_left (sub_le_self t ha'.le) hn.le)
    have H := hmin s hs
    rw [hrt]
    have hsval : (s:ℝ)/N=t-a := by
      rw [show (s:ℝ)=(N:ℝ)*(t-a) from Real.coe_toNNReal _ hs0]
      field_simp
    simpa only [hsval] using H
  have H := left_derivative_nonpos_of_min hd hm'
  linarith

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

 

theorem no_interior_contact_sequence
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop)
    (n : ℕ) (ζ : Fin (n+2) → ℝ) (hz : StrictMono ζ) (hz0 : ζ 0=0) (hz1 : ζ (Fin.last (n+1))=1)
    (q : OverlapPath) (v : Fin (n+1) → ℝ) (hq : finiteStepFunction ζ v =ᵐ[pathMeasure] q.val)
    {f : ℝ → ℝ} (F : BoundedC2Data f) (S H : ℝ) (α : ℝ≥0) {δ : ℝ} (hδ : 0 < δ)
    (p : (k : ℕ) → ContactParameter n (N k))
    (hp : ∀ k, p k∈contactRegion n (N k) (α*(N k:ℝ≥0)) H)
    (hcap : ∀ k, (∑ i, (p k).2.1 i) < H) (hr0 : ∀ k, 0 < (p k).1)
    (hmin : ∀ k, IsMinOn (enrichedContactObjective gaussianCoordinates n (chainExponent ζ) (spinLaw (N k))
      (gaussianRowActivation f) (fun i => chainWeight ζ i*v i) S (patternFunctional f q+δ))
      (contactRegion n (N k) (α*(N k:ℝ≥0)) H) (p k)) : False := by
  let b := chainExponent ζ
  have hb := chainExponent_admissible hz hz0 hz1
  let h := fun k => finiteFieldPath (p k).2.1
  let u := fun k => (p k).2.2
  let r := fun k => (p k).1
  have hp' k := contactRegion_nonneg (hp k)
  have hh k := monotone_finiteFieldPath (hp' k).2.2.1
  have h0 k := finiteFieldPath_nonneg (hp' k).2.2.1 0
  have hu k := (hp' k).2.2.2.2
  have hub k j : |u k j| ≤ 2 := abs_le.mpr ⟨by linarith [(hu k j).1],(hu k j).2⟩
  have hH k : h k n ≤ H := by dsimp only [h]; rw [finiteFieldPath_last]; exact (hp' k).2.2.2.1
  have hr k : (r k:ℝ) ≤ (α:ℝ)*N k := by exact_mod_cast (hp' k).2.1
  have hpert k := enriched_contact_perturbation_minimum gaussianCoordinates b (spinLaw (N k))
    (gaussianRowActivation f) (fun i => chainWeight ζ i*v i) S (patternFunctional f q+δ) (hp k) (hmin k)
  let L := fun k => enrichedArrayLaw gaussianCoordinates (r k) n b (h k) (u k) (spinLaw (N k))
    (measurable_gaussianRowActivation F.mf)
  obtain ⟨μ,ns,hns,hL⟩ := jointArrayLaw_subsequence L
  have hN' := hNlim.comp hns.tendsto_atTop
  have hord := enriched_minimizers_ordered (N ∘ ns) (fun k => hN (ns k)) hN' n b hb
    (h ∘ ns) (fun k => hh (ns k)) (fun k => h0 (ns k)) H (fun k => hH (ns k))
    (fun k => u (ns k)) (fun k => hu (ns k)) (fun k => spinLaw (N (ns k)))
    (fun _ => ℕ → ℝ) (fun _ => gaussianCoordinates) (fun _ => gaussianRowActivation f)
    (fun _ => measurable_gaussianRowActivation F.mf) F.K ((abs_nonneg (f 0)).trans (F.bf 0))
    (fun _ _ _ => F.bf _) (r ∘ ns) α (fun k => hr (ns k)) (fun k => hpert (ns k)) μ hL
  let ν := (μ : Measure JointArray).map (fun x => spinArray x 0 1)
  let : IsProbabilityMeasure ν := inferInstance
  have hν := jointSpin_unit_support hord.1
  have hmono := monotone_quantileFunction hν
  have hbound := quantileFunction_mem hν
  let Q := overlapPathOfMonotone (quantileFunction ν) hmono hbound
  have hQ := overlapPathOfMonotone_ae (quantileFunction ν) hmono hbound
  have htail := enriched_contact_nodal_tails (N ∘ ns) (fun k => hN (ns k)) hN' n ζ hz hz0 hz1 v
    S (patternFunctional f q+δ) H α (fun k => p (ns k)) (fun k => hp (ns k)) (fun k => hcap (ns k))
    (fun k => spinLaw (N (ns k))) (fun _ => ℕ → ℝ) (fun _ => gaussianCoordinates)
    (fun _ => gaussianRowActivation f) (fun _ => measurable_gaussianRowActivation F.mf)
    F.K ((abs_nonneg (f 0)).trans (F.bf 0)) (fun _ _ _ => F.bf _)
    (fun k => hmin (ns k)) μ hL
  obtain ⟨q',hqq,hqmono,hqb⟩ := overlapPath_representative q
  have ht := nodal_tails_imply_all_tails ζ hz hz0 hz1 v hmono hqmono (hq.trans hqq.symm) htail
  have hV : patternFunctional f Q ≤ patternFunctional f q := by
    apply patternFunctional_tail_order F Q q
    intro s hs
    rw [← tail_integral_representative Q hQ hs.1,← tail_integral_representative q hqq hs.1]
    exact ht s hs
  have hfresh := enriched_gaussian_fresh_limit (N ∘ ns) (fun k => hN (ns k)) hN' n b hb
    (h ∘ ns) (fun k => hh (ns k)) (fun k => h0 (ns k)) H (fun k => hH (ns k))
    (fun k => u (ns k)) (fun k => hu (ns k)) (fun k => spinLaw (N (ns k)))
    F.continuous F.K F.bf (r ∘ ns) α (fun k => hr (ns k)) (fun k => hpert (ns k)) μ hL Q hQ
  have htlim : patternFunctional f q+δ ≤ patternFunctional f Q := by
    apply ge_of_tendsto hfresh
    apply Eventually.of_forall
    intro k
    exact enriched_time_minimum_fresh (hN (ns k)) n b hb (hh (ns k)) (h0 (ns k))
      (u (ns k)) (hub (ns k)) (spinLaw (N (ns k))) gaussianCoordinates
      (measurable_gaussianRowActivation F.mf) ((abs_nonneg (f 0)).trans (F.bf 0))
      (fun _ _ => F.bf _) (hr0 (ns k)) (hp' (ns k)).2.1 (patternFunctional f q+δ)
      (enriched_contact_time_minimum gaussianCoordinates b (spinLaw (N (ns k))) (gaussianRowActivation f)
        (fun i => chainWeight ζ i*v i) S (patternFunctional f q+δ) (hp (ns k)) (hmin (ns k)))
  linarith

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma perturbation_square_sum_le (N : ℕ) :
    (∑ j : Fin N, (perturbationWeight j)^2) ≤ 1 := by
  calc
    _ ≤ ∑ j : Fin N, perturbationWeight j := Finset.sum_le_sum (fun j _ =>
      by nlinarith [perturbationWeight_nonneg j,perturbationWeight_le_one j])
    _ ≤ 1 := by rw [perturbationWeight_sum]; have := pow_nonneg (by norm_num : (0:ℝ)≤1/2) N; linarith

lemma enrichedMeanPressure_zero_perturbation_cost {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    |enrichedMeanPressure P r n b h u ν φ-enrichedMeanPressure P r n b h 0 ν φ| ≤
      8*(perturbationScale N)^2 := by
  have H := enrichedMeanPressure_perturbation_lipschitz hN n b hb hh h0 hu
    (u := u) (v := 0) (by intro j; simp) ν P hm hK hφ r
  refine H.trans ?_
  have he (j : Fin N) : (4*(perturbationAmplitude N j)^2/(N:ℝ))*|u j-(0 : Fin N → ℝ) j| ≤
      (8*(perturbationScale N)^2)*(perturbationWeight j)^2 := by
    rw [perturbationAmplitude_sq]
    simp only [Pi.zero_apply,sub_zero]
    have hN' : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    have hr : 4*((N:ℝ)*(perturbationScale N)^2*(perturbationWeight j)^2)/(N:ℝ) =
        4*(perturbationScale N)^2*(perturbationWeight j)^2 := by field_simp
    rw [hr]
    nlinarith [mul_le_mul_of_nonneg_left (hu j)
      (show 0≤4*(perturbationScale N)^2*(perturbationWeight j)^2 by positivity)]
  calc
    _ ≤ ∑ j : Fin N, (8*(perturbationScale N)^2)*(perturbationWeight j)^2 := Finset.sum_le_sum (fun j _ => he j)
    _ = (8*(perturbationScale N)^2)*(∑ j : Fin N, (perturbationWeight j)^2) := by rw [Finset.mul_sum]
    _ ≤ 8*(perturbationScale N)^2 := by
      simpa using mul_le_mul_of_nonneg_left (perturbation_square_sum_le N)
        (show 0≤8*(perturbationScale N)^2 by positivity)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma isingEntropy_chain_lower {n : ℕ} (ζ : Fin (n+2) → ℝ) (hz : StrictMono ζ)
    (hz0 : ζ 0=0) (hz1 : ζ (Fin.last (n+1))=1)
    (q : OverlapPath) (v : Fin (n+1) → ℝ)
    (hq : finiteStepFunction ζ v =ᵐ[pathMeasure] q.val)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    ((magneticFieldValue n (chainExponent ζ) h+
      (∑ i : Fin (n+1), (chainWeight ζ i*v i)*h i)/2 : ℝ) : EReal) ≤ isingEntropy q := by
  have H := le_iSup (fun h : FieldStep =>
    ((fieldRecursion h+(∫ u, stepFunction h u*q.val u ∂pathMeasure)/2 : ℝ) : EReal))
      (chainFieldStep n ζ hz hz0 hz1 h hh h0)
  have he : (∫ u, stepFunction (chainFieldStep n ζ hz hz0 hz1 h hh h0) u*q.val u ∂pathMeasure) =
      ∑ i : Fin (n+1), (chainWeight ζ i*v i)*h i := by
    calc
      _ = ∫ u, finiteStepFunction ζ (fun i => h i) u*finiteStepFunction ζ v u ∂pathMeasure := by
        apply integral_congr_ae
        filter_upwards [hq] with u hu
        rw [← hu]
        rfl
      _ = _ := by
        rw [integral_finiteStepFunction_mul ζ hz hz0 hz1]
        apply Finset.sum_congr rfl
        intro i _
        unfold chainWeight
        ring
  rw [fieldRecursion_chain,he] at H
  exact H

lemma magneticFieldValue_entropy_le {n : ℕ} (ζ : Fin (n+2) → ℝ) (hz : StrictMono ζ)
    (hz0 : ζ 0=0) (hz1 : ζ (Fin.last (n+1))=1)
    (q : OverlapPath) (v : Fin (n+1) → ℝ)
    (hq : finiteStepFunction ζ v =ᵐ[pathMeasure] q.val)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) {S : ℝ}
    (hS : isingEntropy q ≤ (S:EReal)) :
    magneticFieldValue n (chainExponent ζ) h+
      (∑ i : Fin (n+1), (chainWeight ζ i*v i)*h i)/2 ≤ S := by
  exact_mod_cast (isingEntropy_chain_lower ζ hz hz0 hz1 q v hq h hh h0).trans hS

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma enrichedMeanPressure_magnetic_upper {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    enrichedMeanPressure P r n b h u (spinLaw N) φ  ≤ 
      magneticFieldValue n b h+(K/N)*(r:ℝ)+8*(perturbationScale N)^2 := by
  have Ht := enrichedMeanPressure_time_lipschitz hN n b hb hh h0 u hu (spinLaw N) P hm hK hφ r 0
  have Hu := enrichedMeanPressure_zero_perturbation_cost hN n b hb hh h0 u hu (spinLaw N) P hm hK hφ 0
  rw [enrichedMeanPressure_initial_zero hN n b hb hh h0 P hm hK hφ] at Hu
  simp only [NNReal.coe_zero,sub_zero,abs_of_nonneg r.coe_nonneg] at Ht
  linarith [(abs_le.mp Ht).2,(abs_le.mp Hu).2]

lemma enrichedContactObjective_initial_lower {N n : ℕ} (hN : 0 < N)
    (ζ : Fin (n+2) → ℝ) (hz : StrictMono ζ) (hz0 : ζ 0=0) (hz1 : ζ (Fin.last (n+1))=1)
    (q : OverlapPath) (v : Fin (n+1) → ℝ) (hq : finiteStepFunction ζ v =ᵐ[pathMeasure] q.val)
    {S : ℝ} (hS : isingEntropy q ≤ (S:EReal)) (a : Fin (n+1) → ℝ) (ha : ∀ i, 0 ≤ a i)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (V : ℝ)
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) :
    -8*(perturbationScale N)^2 ≤ enrichedContactObjective P n (chainExponent ζ) (spinLaw N) φ
      (fun i => chainWeight ζ i*v i) S V (0,a,u) := by
  have Hp := enrichedMeanPressure_magnetic_upper hN n (chainExponent ζ) (chainExponent_admissible hz hz0 hz1)
    (monotone_finiteFieldPath ha) (finiteFieldPath_nonneg ha 0) u hu P hm hK hφ 0
  have Hs := magneticFieldValue_entropy_le ζ hz hz0 hz1 q v hq (finiteFieldPath a)
    (monotone_finiteFieldPath ha) (finiteFieldPath_nonneg ha 0) hS
  have Hpen : 0 ≤ ∑ j : Fin N, perturbationWeight j*(u j-3/2)^2 :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (perturbationWeight_nonneg j) (sq_nonneg _))
  simp only [NNReal.coe_zero,mul_zero,add_zero] at Hp
  simp only [enrichedContactObjective,NNReal.coe_zero,zero_div,zero_mul,add_zero]
  linarith

lemma enrichedContactObjective_cap_lower {N n : ℕ} (hN : 0 < N)
    (ζ : Fin (n+2) → ℝ) (hz : StrictMono ζ) (hz0 : ζ 0=0) (hz1 : ζ (Fin.last (n+1))=1)
    (q : Fin (n+1) → ℝ) (hq : ∀ i, q i ≤ 1)
    (a : Fin (n+1) → ℝ) (ha : ∀ i, 0 ≤ a i) (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    {α : ℝ} (_hα : 0 ≤ α) (r : ℝ≥0) (hr : (r:ℝ) ≤ α*N) (S V : ℝ)
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) :
    (chainWeight ζ (Fin.last n)*(1-q (Fin.last n))/2)*(∑ i, a i)-
      (∫ z : ℝ, |z| ∂gaussianReal 0 1)*Real.sqrt (∑ i, a i)-
      (∑ i : Fin n, Real.log 2/chainExponent ζ i)-α*K-α*|V|+S-8*(perturbationScale N)^2  ≤ 
        enrichedContactObjective P n (chainExponent ζ) (spinLaw N) φ
          (fun i => chainWeight ζ i*q i) S V (r,a,u) := by
  let h := finiteFieldPath a
  have hh := monotone_finiteFieldPath ha
  have h0 := finiteFieldPath_nonneg ha 0
  have Hp := enrichedMeanPressure_magnetic_upper hN n (chainExponent ζ) (chainExponent_admissible hz hz0 hz1)
    hh h0 u hu P hm hK hφ r
  have Hg := magneticFieldValue_chain_growth ζ hz hz0 hz1 h hh h0
  have Hs := field_sum_last_lower n (chainWeight ζ) (fun i => h i) q
    (fun i => (chainWeight_pos hz i).le) (fun i => finiteFieldPath_nonneg ha i) hq
  have Hsum : (∑ i : Fin (n+1), chainWeight ζ i*h i)-
      (∑ i : Fin (n+1), (chainWeight ζ i*q i)*h i) =
      ∑ i : Fin (n+1), chainWeight ζ i*(1-q i)*h i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have Hsqrt := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hh (Nat.zero_le n)))
    (integral_nonneg (fun z : ℝ => abs_nonneg z) : 0 ≤ ∫ z : ℝ, |z| ∂gaussianReal 0 1)
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have ht : (r:ℝ)/N ≤ α := (div_le_iff₀ hn).mpr hr
  have ht0 : 0 ≤ (r:ℝ)/N := div_nonneg r.coe_nonneg hn.le
  have Ht := mul_le_mul_of_nonneg_right ht hK
  have HV : -α*|V| ≤ (r:ℝ)/N*V := by
    have H₁ := mul_le_mul_of_nonneg_left (neg_abs_le V) ht0
    have H₂ := mul_le_mul_of_nonneg_right ht (abs_nonneg V)
    nlinarith
  have Hpen : 0 ≤ ∑ j : Fin N, perturbationWeight j*(u j-3/2)^2 :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (perturbationWeight_nonneg j) (sq_nonneg _))
  have last : h n=∑ i, a i := finiteFieldPath_last a
  have last' : h (Fin.last n)=∑ i, a i := last
  rw [last'] at Hs
  rw [finiteFieldPath_last] at Hsqrt
  simp only [enrichedContactObjective]
  have he : (K/(N:ℝ))*(r:ℝ)=((r:ℝ)/N)*K := by ring
  rw [he] at Hp
  change _ ≤ -enrichedMeanPressure P r n (chainExponent ζ) h u (spinLaw N) φ-
    (∑ i, (chainWeight ζ i*q i)*h i)/2+S+(r:ℝ)/N*V+_ 
  nlinarith

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma exists_coercive_sqrt_cap {a : ℝ} (ha : 0 < a) (G C : ℝ) :
    ∃ H : ℝ, 0 < H ∧ 1 < a*H-G*Real.sqrt H-C := by
  let t := 1+(|G|+|C|+1)/a
  have ht : 1 ≤ t := by
    dsimp [t]
    have : 0 ≤ (|G|+|C|+1)/a := by positivity
    linarith
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have he : a*t=a+|G|+|C|+1 := by dsimp [t]; field_simp; ring
  refine ⟨t^2,by positivity,?_⟩
  rw [Real.sqrt_sq ht0]
  have hG := mul_le_mul_of_nonneg_right (le_abs_self G) ht0
  have hC := le_abs_self C
  have hCt := mul_le_mul_of_nonneg_left ht (add_nonneg (abs_nonneg C) zero_le_one)
  have hat : 0 < a*t := mul_pos ha (lt_of_lt_of_le zero_lt_one ht)
  nlinarith [mul_nonneg (abs_nonneg G) ht0]

lemma contact_cap_exists {n : ℕ} (ζ : Fin (n+2) → ℝ) (hz : StrictMono ζ)
    (q : Fin (n+1) → ℝ) (hq : q (Fin.last n) < 1) (α K V S : ℝ) :
    ∃ H : ℝ, 0 < H ∧ 1 <
      (chainWeight ζ (Fin.last n)*(1-q (Fin.last n))/2)*H-
      (∫ z : ℝ, |z| ∂gaussianReal 0 1)*Real.sqrt H-
      (∑ i : Fin n, Real.log 2/chainExponent ζ i)-α*K-α*|V|+S := by
  obtain ⟨H,hH,hh⟩ := exists_coercive_sqrt_cap
    (a := chainWeight ζ (Fin.last n)*(1-q (Fin.last n))/2)
    (by apply div_pos; exact mul_pos (chainWeight_pos hz _) (sub_pos.mpr hq); norm_num)
    (∫ z : ℝ, |z| ∂gaussianReal 0 1)
    ((∑ i : Fin n, Real.log 2/chainExponent ζ i)+α*K+α*|V|-S)
  exact ⟨H,hH,by linarith⟩

end IsingPerceptron

end

end OAI
