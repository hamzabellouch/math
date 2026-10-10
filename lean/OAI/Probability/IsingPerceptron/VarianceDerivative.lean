import Mathlib
import OAI.Probability.IsingPerceptron.EnrichedCGF

namespace OAI

/-! Variance Derivative. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma hasDerivWithinAt_sqrt_comp_zero {H A : ℝ → ℝ}
    (hH : ∀ t, HasDerivAt H (t*A t) t) (hA : ContinuousAt A 0) :
    HasDerivWithinAt (fun a => H (Real.sqrt a)) (A 0 / 2) (Ici 0) 0 := by
  have hquot : Tendsto (fun t => (H t-H 0)/t^2) (𝓝[>] (0:ℝ)) (𝓝 (A 0/2)) := by
    apply HasDerivAt.lhopital_zero_nhdsGT
      (f' := fun t => t*A t) (g' := fun t => 2*t)
    · exact Eventually.of_forall (fun t => (hH t).sub_const (H 0))
    · exact Eventually.of_forall (fun t => by simpa using (hasDerivAt_id t).fun_pow 2)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_ne_zero (by norm_num) (ne_of_gt ht)
    · simpa using ((hH 0).continuousAt.fun_sub (continuousAt_const (y := H 0))).tendsto.mono_left nhdsWithin_le_nhds
    · simpa using ((continuousAt_id : ContinuousAt (fun t : ℝ => t) 0).fun_pow 2).tendsto.mono_left nhdsWithin_le_nhds
    · have h : Tendsto (fun t => A t/2) (𝓝[>] (0:ℝ)) (𝓝 (A 0/2)) :=
        (hA.div_const 2).tendsto.mono_left nhdsWithin_le_nhds
      apply h.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : 0 < t := ht
      field_simp [ht0.ne']
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using Real.continuous_sqrt.continuousAt.tendsto.mono_left
        (show 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ) from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact Real.sqrt_pos.mpr ht
  apply HasDerivWithinAt.Ici_of_Ioi
  rw [hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ) ∉ Ioi 0 by simp)]
  apply (hquot.comp hsqrt).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp [slope_def_field,Real.sq_sqrt (le_of_lt ht)]

lemma hasDerivWithinAt_sqrt_comp {H A : ℝ → ℝ}
    (hH : ∀ t, HasDerivAt H (t*A t) t) (hA : Continuous A)
    {a : ℝ} (ha : 0 ≤ a) :
    HasDerivWithinAt (fun a => H (Real.sqrt a)) (A (Real.sqrt a)/2) (Ici 0) a := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa using hasDerivWithinAt_sqrt_comp_zero hH hA.continuousAt
  · have h := (hH (Real.sqrt a)).comp a (Real.hasDerivAt_sqrt (ne_of_gt ha))
    have hd : Real.sqrt a * A (Real.sqrt a) * (1 / (2*Real.sqrt a)) = A (Real.sqrt a)/2 := by
      field_simp [(Real.sqrt_pos.mpr ha).ne']
    simpa only [Function.comp_def,hd] using h.hasDerivWithinAt (s := Ici 0)

 

theorem hasDerivWithinAt_random_cylinder_variance {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {K d : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    (hdiag : ∀ x, cylinderCross (a x) (a x) = d) {v : ℝ} (hv : 0 ≤ v) :
    HasDerivWithinAt (fun v => ∫ z : Ω × (ℕ → ℝ),
        cgf (fun x => cylinderField (a x) z.2) (ν z.1) (Real.sqrt v)
        ∂P.prod gaussianCoordinates)
      ((d-randomReplicaAverage P ν a (Real.sqrt v)
        (fun σ : Fin 2 → X => cylinderCross (a (σ 1)) (a (σ 0))))/2) (Ici 0) v := by
  apply hasDerivWithinAt_sqrt_comp
    (H := fun t => ∫ z : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (a x) z.2) (ν z.1) t ∂P.prod gaussianCoordinates)
    (A := fun t => d-randomReplicaAverage P ν a t (fun σ : Fin 2 → X => cylinderCross (a (σ 1)) (a (σ 0))))
  · exact hasDerivAt_random_cylinder_covariance hν a ha hdiag
  · apply Continuous.fun_sub continuous_const
    apply continuous_randomReplicaAverage hν a ha (C := max K 0)
    · exact le_max_right _ _
    · intro σ
      have h := abs_cylinderCross_le (a (σ 1)) (a (σ 0))
      have h1 := ha (σ 1)
      have h0 := ha (σ 0)
      exact (by linarith : |cylinderCross (a (σ 1)) (a (σ 0))| ≤ K).trans (le_max_left _ _)
  · exact hv

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussian_sum_identDistrib {Ω X : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (a b c : X → ℕ →₀ ℝ) (t : ℝ)
    (hc : ∀ x y, cylinderCross (c x) (c y) = cylinderCross (a x) (a y)+t^2*cylinderCross (b x) (b y)) :
    IdentDistrib
      (fun z : (Ω × (ℕ → ℝ)) × (ℕ → ℝ) =>
        (z.1.1,fun x => cylinderField (a x) z.1.2+t*cylinderField (b x) z.2))
      (fun z : Ω × (ℕ → ℝ) => (z.1,fun x => cylinderField (c x) z.2))
      ((P.prod gaussianCoordinates).prod gaussianCoordinates) (P.prod gaussianCoordinates) := by
  let f : ((ℕ → ℝ) × (ℕ → ℝ)) → (X → ℝ) :=
    fun z x => cylinderField (a x) z.1+t*cylinderField (b x) z.2
  let g : (ℕ → ℝ) → (X → ℝ) := fun z x => cylinderField (c x) z
  have hf : Measurable f := by
    unfold f; apply Measurable.of_eval; intro x
    exact ((measurable_cylinderField (a x)).comp measurable_fst).add
      (((measurable_cylinderField (b x)).comp measurable_snd).const_mul t)
  have hg : Measurable g := by unfold g; apply Measurable.of_eval; intro x; exact measurable_cylinderField _
  have hp : MeasurePreserving (MeasurableEquiv.prodAssoc : ((Ω × (ℕ → ℝ)) × (ℕ → ℝ)) → Ω × ((ℕ → ℝ) × (ℕ → ℝ)))
      ((P.prod gaussianCoordinates).prod gaussianCoordinates) (P.prod (gaussianCoordinates.prod gaussianCoordinates)) :=
    ⟨MeasurableEquiv.prodAssoc.measurable,Measure.prodAssoc_prod⟩
  refine ⟨((measurable_id.prodMap hf).comp hp.measurable).aemeasurable,
    (measurable_id.prodMap hg).aemeasurable,?_⟩
  change ((P.prod gaussianCoordinates).prod gaussianCoordinates).map
    ((Prod.map id f) ∘ MeasurableEquiv.prodAssoc) =
      (P.prod gaussianCoordinates).map (Prod.map id g)
  rw [← Measure.map_map (measurable_id.prodMap hf) hp.measurable,hp.map_eq,
    ← Measure.map_prod_map P (gaussianCoordinates.prod gaussianCoordinates) measurable_id hf,
    ← Measure.map_prod_map P gaussianCoordinates measurable_id hg]
  rw [show (gaussianCoordinates.prod gaussianCoordinates).map f = gaussianCoordinates.map g from
    cylinder_independent_sum_law a b c t hc]

lemma random_cgf_insertion_eq {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {H : Ω × X → ℝ} (hH : Measurable H)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) (ν ω))
    (b : X → ℕ →₀ ℝ) {K : ℝ} (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    ∀ᵐ z ∂P.prod gaussianCoordinates,
      cgf (fun x => cylinderField (b x) z.2) (gibbsProbability (ν z.1) (fun x => H (z.1,x))) t =
        Real.log (∫ x, Real.exp (H (z.1,x)+t*cylinderField (b x) z.2) ∂ν z.1)-
          Real.log (∫ x, Real.exp (H (z.1,x)) ∂ν z.1) := by
  have hη := measurable_gibbsProbability hν hH
  have ht := random_cylinder_all_exp_ae (P := P) hη b hb
  have he' := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := gaussianCoordinates)).tendsto_ae.eventually he
  filter_upwards [ht,he'] with z ht he
  have hi := ht t
  rw [gibbsProbability_eq_tilted _ _ he,integrable_tilted_iff he] at hi
  have hisum : Integrable (fun x => Real.exp (H (z.1,x)+t*cylinderField (b x) z.2)) (ν z.1) := by
    simpa only [smul_eq_mul,← Real.exp_add] using hi
  exact cgf_fold _ _ _ _ he hisum

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron
variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma scalarShiftLaw_amplitude (μ : ProbabilityMeasure (I → ℝ)) (t : ℝ) :
    ((μ : Measure (I → ℝ)).prod (gaussianReal 0 1)).map
      (fun p : (I → ℝ) × ℝ => fun x => p.1 x+t*p.2) =
      (scalarShiftLaw μ (NNReal.mk (t^2) (sq_nonneg t)) : Measure (I → ℝ)) := by
  have hp : MeasurePreserving (fun p : (I → ℝ) × ℝ => (p.1,t*p.2))
      ((μ : Measure (I → ℝ)).prod (gaussianReal 0 1))
      ((μ : Measure (I → ℝ)).prod (gaussianReal 0 (NNReal.mk (t^2) (sq_nonneg t)))) :=
    (MeasurePreserving.id _).prod ⟨by fun_prop,by simpa using gaussianReal_map_const_mul (μ := 0) (v := 1) t⟩
  change ((μ : Measure (I → ℝ)).prod (gaussianReal 0 1)).map
    ((fun p : (I → ℝ) × ℝ => fun x => p.1 x+p.2) ∘ (fun p => (p.1,t*p.2))) = _
  rw [← Measure.map_map (by fun_prop) hp.measurable,hp.map_eq]
  rfl

def edgeGaussianTag (n : ℕ) (v : ForestVertex n) : ℕ :=
  Encodable.encode (nodeAddress n (some v))

lemma edgeGaussianTag_injective (n : ℕ) : Function.Injective (edgeGaussianTag n) := by
  intro v w h
  exact Option.some.inj (nodeAddress_injective n (Encodable.encode_inj.mp h))

def edgeGaussianCoordinates (n : ℕ) (g : ℕ → ℝ) : ForestVertex n → ℝ :=
  fun v => g (edgeGaussianTag n v)

lemma edgeGaussianCoordinates_preserving (n : ℕ) :
    MeasurePreserving (edgeGaussianCoordinates n) gaussianCoordinates
      (Measure.infinitePi (fun _ : ForestVertex n => gaussianReal 0 1)) :=
  gaussian_pullback_measurePreserving (edgeGaussianTag n) (edgeGaussianTag_injective n)

 

def scalarCoordinateInsert (n : ℕ) (a : ℕ → ℝ)
    (p : (LabeledTree n × (ForestVertex n → I → ℝ)) × (ℕ → ℝ)) :
    LabeledTree n × (ForestVertex n → I → ℝ) :=
  (p.1.1,fun v x => p.1.2 v x+a (forestVertexDepth n v)*edgeGaussianCoordinates n p.2 v)

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma scalarCoordinateInsert_preserving (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (a : ℕ → ℝ) :
    MeasurePreserving (scalarCoordinateInsert n a) ((cascadeCoordinateLaw n b μ).prod gaussianCoordinates)
      (cascadeCoordinateLaw n b (fun i => scalarShiftLaw (μ i) (NNReal.mk (a i^2) (sq_nonneg _)))) := by
  let P := Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure (I → ℝ)))
  let Q := Measure.infinitePi (fun _ : ForestVertex n => gaussianReal 0 1)
  have hp : MeasurePreserving (fun p : (ForestVertex n → I → ℝ) × (ForestVertex n → ℝ) =>
      fun v => (p.1 v,p.2 v)) (P.prod Q)
      (Measure.infinitePi (fun v : ForestVertex n =>
        (μ (forestVertexDepth n v) : Measure (I → ℝ)).prod (gaussianReal 0 1))) :=
    ⟨by fun_prop,infinitePi_prod_join _ _⟩
  have hs : MeasurePreserving (fun p : ForestVertex n → (I → ℝ) × ℝ =>
      fun v x => (p v).1 x+a (forestVertexDepth n v)*(p v).2)
      (Measure.infinitePi (fun v : ForestVertex n =>
        (μ (forestVertexDepth n v) : Measure (I → ℝ)).prod (gaussianReal 0 1)))
      (Measure.infinitePi (fun v : ForestVertex n =>
        (scalarShiftLaw (μ (forestVertexDepth n v)) (NNReal.mk (a (forestVertexDepth n v)^2) (sq_nonneg _)) : Measure (I → ℝ)))) := by
    refine ⟨by fun_prop,?_⟩
    rw [Measure.infinitePi_map_pi (f := fun v (p : (I → ℝ) × ℝ) =>
      fun x => p.1 x+a (forestVertexDepth n v)*p.2) _ (fun _ => by fun_prop)]
    congr 1
    funext v
    exact scalarShiftLaw_amplitude _ _
  have hq := (hs.comp hp).comp ((MeasurePreserving.id P).prod (edgeGaussianCoordinates_preserving n))
  have ha : MeasurePreserving (MeasurableEquiv.prodAssoc :
      ((LabeledTree n × (ForestVertex n → I → ℝ)) × (ℕ → ℝ)) →
      LabeledTree n × ((ForestVertex n → I → ℝ) × (ℕ → ℝ)))
      ((cascadeCoordinateLaw n b μ).prod gaussianCoordinates)
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (P.prod gaussianCoordinates)) :=
    ⟨MeasurableEquiv.prodAssoc.measurable,Measure.prodAssoc_prod⟩
  exact ((MeasurePreserving.id _).prod hq).comp ha

lemma forestVertexDepth_edgeAt (n : ℕ) (γ : LabeledLeaf n) (i : Fin n) :
    forestVertexDepth n (edgeAt n γ i) = i := by
  have h := nodeAddress_nodeAt_length n γ i.succ
  rw [nodeAt_succ,nodeAddress_length_some] at h
  exact Nat.add_right_cancel h

def labelLevelCoefficients (n : ℕ) (d : Fin n) (s : I × LabeledLeaf n) : ℕ →₀ ℝ :=
  Finsupp.single (edgeGaussianTag n (edgeAt n s.2 d)) 1

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma cascadeCoordinateEnergy_insert (n : ℕ) (d : Fin n) (t : ℝ) (H : I → ℝ)
    (p : (LabeledTree n × (ForestVertex n → I → ℝ)) × (ℕ → ℝ)) (s : I × LabeledLeaf n) :
    cascadeCoordinateEnergy n H (scalarCoordinateInsert n (fun i => if i = d then t else 0) p) s =
      cascadeCoordinateEnergy n H p.1 s+t*cylinderField (labelLevelCoefficients n d s) p.2 := by
  classical
  simp only [cascadeCoordinateEnergy,scalarCoordinateInsert,Finset.sum_add_distrib,
    forestVertexDepth_edgeAt]
  have he : (∑ i : Fin n, (if (i:ℕ) = d then t else 0)*edgeGaussianCoordinates n p.2 (edgeAt n s.2 i)) =
      t*edgeGaussianCoordinates n p.2 (edgeAt n s.2 d) := by
    rw [Finset.sum_eq_single d]
    · simp
    · intro i _ hi; rw [ite_eq_right (by intro h; exact hi (Fin.ext h)),zero_mul]
    · simp
  rw [he,labelLevelCoefficients,cylinderField,Finsupp.sum_single_index (by simp),one_mul]
  dsimp only [edgeGaussianCoordinates]
  ring

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma labelLevelCoefficients_diag (n : ℕ) (d : Fin n) (s : I × LabeledLeaf n) :
    cylinderCross (labelLevelCoefficients n d s) (labelLevelCoefficients n d s) = 1 := by
  simp [labelLevelCoefficients,cylinderCross_single_left]

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma labelLevelCoefficients_bound (n : ℕ) (d : Fin n) (s : I × LabeledLeaf n) :
    (labelLevelCoefficients n d s).sum (fun _ c => c^2) ≤ 1 := by
  simp [labelLevelCoefficients,Finsupp.sum_single_index]

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma labelLevelCoefficients_cross (n : ℕ) (d : Fin n) (s t : I × LabeledLeaf n) :
    cylinderCross (labelLevelCoefficients n d s) (labelLevelCoefficients n d t) =
      if (labeledAddress n s.2).take (d+1) = (labeledAddress n t.2).take (d+1) then 1 else 0 := by
  classical
  have he : edgeGaussianTag n (edgeAt n t.2 d) = edgeGaussianTag n (edgeAt n s.2 d) ↔
      (labeledAddress n s.2).take (d+1) = (labeledAddress n t.2).take (d+1) := by
    rw [edgeGaussianTag,edgeGaussianTag,Encodable.encode_inj,← nodeAt_succ,← nodeAt_succ,
      nodeAddress_nodeAt,nodeAddress_nodeAt]
    exact eq_comm
  simp only [labelLevelCoefficients,cylinderCross_single_left,one_mul,Finsupp.single_apply,he]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma externalFieldCoefficients_cross {N : ℕ} (n : ℕ) {h : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (s t : Spin N × LabeledLeaf n) :
    cylinderCross (externalFieldCoefficients n h s) (externalFieldCoefficients n h t) =
      h (labeledCommonDepth n s.2 t.2) * ∑ i, spinValue (s.1 i)*spinValue (t.1 i) := by
  exact treeField_path_cross n s.2 t.2 hh h0 _ _

lemma monotone_field_add {h l : ℕ → ℝ} (hh : Monotone h) (hl : Monotone l)
    {a : ℝ} (ha : 0 ≤ a) : Monotone (fun i => h i+a*l i) := by
  intro i j hij
  exact add_le_add (hh hij) (mul_le_mul_of_nonneg_left (hl hij) ha)

lemma field_add_nonneg {h l : ℕ → ℝ} (h0 : 0 ≤ h 0) (l0 : 0 ≤ l 0)
    {a : ℝ} (ha : 0 ≤ a) : 0 ≤ h 0+a*l 0 := add_nonneg h0 (mul_nonneg ha l0)

lemma enrichedCoefficients_field_add_cross {N : ℕ} (n : ℕ) {h l : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hl : Monotone l) (l0 : 0 ≤ l 0)
    (u : Fin N → ℝ) {a : ℝ} (ha : 0 ≤ a) (s t : Spin N × LabeledLeaf n) :
    cylinderCross (enrichedCoefficients n (fun i => h i+a*l i) u s)
        (enrichedCoefficients n (fun i => h i+a*l i) u t) =
      cylinderCross (enrichedCoefficients n h u s) (enrichedCoefficients n h u t) +
        a*cylinderCross (externalFieldCoefficients n l s) (externalFieldCoefficients n l t) := by
  unfold enrichedCoefficients
  rw [cylinderCross_tagged_sum,cylinderCross_tagged_sum]
  simp only [Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ]
  rw [externalFieldCoefficients_cross n (monotone_field_add hh hl ha) (field_add_nonneg h0 l0 ha),
    externalFieldCoefficients_cross n hh h0,externalFieldCoefficients_cross n hl l0]
  ring

lemma enriched_field_add_law {N : ℕ} (n : ℕ) {h l : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hl : Monotone l) (l0 : 0 ≤ l 0)
    (u : Fin N → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    (gaussianCoordinates.prod gaussianCoordinates).map
      (fun g s => cylinderField (enrichedCoefficients n h u s) g.1+
        Real.sqrt a*cylinderField (externalFieldCoefficients n l s) g.2) =
      gaussianCoordinates.map (fun g s => cylinderField (enrichedCoefficients n (fun i => h i+a*l i) u s) g) := by
  apply cylinder_independent_sum_law
  intro s t
  rw [Real.sq_sqrt ha]
  exact enrichedCoefficients_field_add_cross n hh h0 hl l0 u ha s t

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma referenceReplicaMean_fold {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H G : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν)
    (heg : Integrable (fun x => Real.exp (H x+G x)) ν)
    {r : ℕ} (D : (Fin r → X) → ℝ) :
    referenceReplicaMean (gibbsProbability ν H) G D =
      referenceReplicaMean ν (fun x => H x+G x) D := by
  rw [gibbsProbability_eq_tilted ν H he]
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted he
  have hg : Integrable (fun x => Real.exp (G x)) (ν.tilted H) := by
    rw [integrable_tilted_iff he]
    simpa only [smul_eq_mul,← Real.exp_add] using heg
  rw [referenceReplicaMean_eq_tilted _ _ hg,referenceReplicaMean_eq_tilted _ _ heg,
    tilted_tilted he]
  rfl

def enrichedHamiltonian {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (φ : A → Spin N → ℝ) (p : EnrichedCylinderData n A)
    (s : Spin N × LabeledLeaf n) : ℝ :=
  patternBase φ (fun i : Fin p.1.1.1 => p.1.1.2 i) s.1 +
    cylinderField (enrichedCoefficients n h u s) p.2

lemma measurable_enrichedHamiltonian {N : ℕ} {A : Type*} [MeasurableSpace A]
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) {φ : A → Spin N → ℝ}
    (hm : Measurable φ) :
    Measurable (fun p : EnrichedCylinderData n A × (Spin N × LabeledLeaf n) =>
      enrichedHamiltonian n h u φ p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro s
  unfold enrichedHamiltonian
  have hg : Measurable (fun p : EnrichedCylinderData n A => (p.1.1,s.1)) :=
    measurable_fst.fst.prodMk measurable_const
  exact ((measurable_patternBase_infinite hm).comp hg).add
    ((measurable_cylinderField (enrichedCoefficients n h u s)).comp measurable_snd)

def enrichedReplicaAverage {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) (φ : A → Spin N → ℝ)
    {m : ℕ} (D : (Fin m → Spin N × LabeledLeaf n) → ℝ) : ℝ :=
  ∫ p, referenceReplicaMean (labeledSpinReference n ν p.1.2)
    (enrichedHamiltonian n h u φ p) D ∂enrichedCylinderLaw P r n b

lemma measurable_enrichedReplicaMean {N : ℕ} {A : Type*} [MeasurableSpace A]
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} (hm : Measurable φ)
    {m : ℕ} (D : (Fin m → Spin N × LabeledLeaf n) → ℝ) :
    Measurable (fun p : EnrichedCylinderData n A =>
      referenceReplicaMean (labeledSpinReference n ν p.1.2) (enrichedHamiltonian n h u φ p) D) := by
  exact measurable_random_referenceReplicaMean
    (ν := fun p : EnrichedCylinderData n A => labeledSpinReference n ν p.1.2)
    ((measurable_labeledSpinReference n ν).comp measurable_fst.snd)
    (measurable_enrichedHamiltonian n h u hm)
    ((measurable_of_countable D).comp measurable_snd)

lemma enrichedHamiltonian_insert {N : ℕ} {A : Type*}
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (j : Fin N) (φ : A → Spin N → ℝ)
    (v : ℝ) (p : EnrichedFrozenData n j A × (ℕ → ℝ)) (s : Spin N × LabeledLeaf n) :
    enrichedHamiltonian n h (Function.update u j v) φ (enrichedInsert n j p) s =
      enrichedFrozenHamiltonian n h u j φ p.1 s + (perturbationAmplitude N j*v)*
        cylinderField (monomialCoefficients n (monomialIndex j).1 (monomialIndex j).2 s) p.2 := by
  unfold enrichedHamiltonian enrichedInsert
  dsimp only
  rw [cylinderField_enriched_insert]
  simp only [enrichedFrozenHamiltonian,perturbationAmplitude,add_assoc]

 

theorem enrichedReplicaAverage_eq_random {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (j : Fin N) {v : ℝ} (hv : |v| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0)
    {m : ℕ} (D : (Fin m → Spin N × LabeledLeaf n) → ℝ) :
    enrichedReplicaAverage P r n b h (Function.update u j v) ν φ D =
      randomReplicaAverage (enrichedFrozenLaw P r n b j) (enrichedFrozenReference n h u j ν φ)
        (monomialCoefficients n (monomialIndex j).1 (monomialIndex j).2)
        (perturbationAmplitude N j*v) D := by
  have hp := enrichedInsert_preserving P r n b j
  unfold enrichedReplicaAverage randomReplicaAverage
  rw [← integral_comp_preserving_ae hp
    (measurable_enrichedReplicaMean n h (Function.update u j v) ν hm D).aestronglyMeasurable]
  apply integral_congr_ae
  have he0 := (Measure.quasiMeasurePreserving_fst
    (μ := enrichedFrozenLaw P r n b j) (ν := gaussianCoordinates)).tendsto_ae.eventually
      (enrichedFrozen_exp_ae hN n b hh h0 u hu j ν P hK hφ r)
  have he := enrichedInserted_exp_ae hN n b hh h0 u hu j hv ν P hK hφ r
  filter_upwards [he0,he] with p hp0 hp1
  change referenceReplicaMean (labeledSpinReference n ν p.1.1.2)
    (enrichedHamiltonian n h (Function.update u j v) φ (enrichedInsert n j p)) D = _
  have hfun : enrichedHamiltonian n h (Function.update u j v) φ (enrichedInsert n j p) =
      (fun s => enrichedFrozenHamiltonian n h u j φ p.1 s + (perturbationAmplitude N j*v)*
        cylinderField (monomialCoefficients n (monomialIndex j).1 (monomialIndex j).2 s) p.2) := by
    funext s
    exact enrichedHamiltonian_insert n h u j φ v p s
  rw [hfun]
  exact (referenceReplicaMean_fold _ _ _ hp0 hp1 D).symm

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def enrichedFieldFunctional {N : ℕ} {A : Type*} (n : ℕ) (d : ℝ)
    (ν : Measure (Spin N)) (φ : A → Spin N → ℝ)
    (p : EnrichedCylinderBase n A × ((Spin N × LabeledLeaf n) → ℝ)) : ℝ :=
  (Real.log (∫ s, Real.exp (patternBase φ (fun i : Fin p.1.1.1 => p.1.1.2 i) s.1+p.2 s)
    ∂labeledSpinReference n ν p.1.2)-N*d/2)/N

lemma measurable_enrichedFieldFunctional {N : ℕ} {A : Type*} [MeasurableSpace A]
    (n : ℕ) (d : ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) :
    Measurable (enrichedFieldFunctional n d ν φ) := by
  have hH : Measurable (fun p : (EnrichedCylinderBase n A × ((Spin N × LabeledLeaf n) → ℝ)) ×
      (Spin N × LabeledLeaf n) =>
      patternBase φ (fun i : Fin p.1.1.1.1 => p.1.1.1.2 i) p.2.1 + p.1.2 p.2) := by
    apply measurable_from_prod_countable_left
    intro s
    have hp : Measurable (fun p : EnrichedCylinderBase n A × ((Spin N × LabeledLeaf n) → ℝ) => (p.1.1,s.1)) :=
      measurable_fst.fst.prodMk measurable_const
    exact ((measurable_patternBase_infinite hm).comp hp).add
      ((measurable_pi_apply s).comp measurable_snd)
  exact (((measurable_random_referencePartition
    (ν := fun p : EnrichedCylinderBase n A × ((Spin N × LabeledLeaf n) → ℝ) => labeledSpinReference n ν p.1.2)
    ((measurable_labeledSpinReference n ν).comp measurable_fst.snd) hH).log).sub_const _).div_const _

def enrichedGibbsReference {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) (φ : A → Spin N → ℝ)
    (p : EnrichedCylinderData n A) : Measure (Spin N × LabeledLeaf n) :=
  gibbsProbability (labeledSpinReference n ν p.1.2) (enrichedHamiltonian n h u φ p)

instance enrichedGibbsReference_probability {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν] (φ : A → Spin N → ℝ)
    (p : EnrichedCylinderData n A) : IsProbabilityMeasure (enrichedGibbsReference n h u ν φ p) := by
  unfold enrichedGibbsReference
  infer_instance

lemma measurable_enrichedGibbsReference {N : ℕ} {A : Type*} [MeasurableSpace A]
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) : Measurable (enrichedGibbsReference n h u ν φ) :=
  measurable_gibbsProbability
    (ν := fun p : EnrichedCylinderData n A => labeledSpinReference n ν p.1.2)
    ((measurable_labeledSpinReference n ν).comp measurable_fst.snd)
    (measurable_enrichedHamiltonian n h u hm)

def enrichedFieldInsertedPressure {N : ℕ} {A : Type*} (n : ℕ) (h l : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) (φ : A → Spin N → ℝ) (a : ℝ)
    (p : EnrichedCylinderData n A × (ℕ → ℝ)) : ℝ :=
  enrichedFieldFunctional n (h n+a*l n) ν φ (p.1.1,fun s =>
    cylinderField (enrichedCoefficients n h u s) p.1.2 +
      Real.sqrt a*cylinderField (externalFieldCoefficients n l s) p.2)

lemma enrichedFieldInsertedPressure_law {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b : ℕ → ℝ)
    {h l : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0) (hl : Monotone l) (l0 : 0 ≤ l 0)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν] {φ : A → Spin N → ℝ}
    (hm : Measurable φ) {a : ℝ} (ha : 0 ≤ a) :
    IdentDistrib (enrichedFieldInsertedPressure n h l u ν φ a)
      (enrichedCylinderPressure n (fun i => h i+a*l i) u ν φ)
      ((enrichedCylinderLaw P r n b).prod gaussianCoordinates) (enrichedCylinderLaw P r n b) := by
  have he := gaussian_sum_identDistrib (enrichedCylinderBaseLaw P r n b)
    (enrichedCoefficients n h u) (externalFieldCoefficients n l)
    (enrichedCoefficients n (fun i => h i+a*l i) u) (Real.sqrt a) (fun s t => by
      rw [Real.sq_sqrt ha]
      exact enrichedCoefficients_field_add_cross n hh h0 hl l0 u ha s t)
  exact he.comp (measurable_enrichedFieldFunctional n (h n+a*l n) ν hm)

lemma enrichedField_cgf_eq {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    {h l : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0) (hl : Monotone l) (l0 : 0 ≤ l 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) (a : ℝ) :
    ∀ᵐ z ∂(enrichedCylinderLaw P r n b).prod gaussianCoordinates,
      enrichedFieldInsertedPressure n h l u ν φ a z =
        enrichedCylinderPressure n h u ν φ z.1 +
        (cgf (fun s => cylinderField (externalFieldCoefficients n l s) z.2)
          (enrichedGibbsReference n h u ν φ z.1) (Real.sqrt a))/N-a*l n/2 := by
  have he := random_cgf_insertion_eq
    (ν := fun p : EnrichedCylinderData n A => labeledSpinReference n ν p.1.2)
    ((measurable_labeledSpinReference n ν).comp measurable_fst.snd)
    (measurable_enrichedHamiltonian n h u hm)
    (enrichedCylinder_exp_ae hN n b hh h0 u hu ν P hK hφ r)
    (externalFieldCoefficients n l)
    (fun s => (externalFieldCoefficients_variance n hl l0 s).le) (Real.sqrt a)
  filter_upwards [he] with z hz
  change cgf _ (enrichedGibbsReference n h u ν φ z.1) (Real.sqrt a) = _ at hz
  rw [hz]
  unfold enrichedFieldInsertedPressure enrichedFieldFunctional enrichedCylinderPressure enrichedHamiltonian
  simp only [add_assoc]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma enrichedMeanPressure_field_insert {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h l : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hl : Monotone l) (l0 : 0 ≤ l 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) {a : ℝ} (ha : 0 ≤ a) :
    enrichedMeanPressure P r n b (fun i => h i+a*l i) u ν φ =
      enrichedMeanPressure P r n b h u ν φ +
      (∫ z : EnrichedCylinderData n A × (ℕ → ℝ),
        cgf (fun s => cylinderField (externalFieldCoefficients n l s) z.2)
          (enrichedGibbsReference n h u ν φ z.1) (Real.sqrt a)
        ∂(enrichedCylinderLaw P r n b).prod gaussianCoordinates)/N-a*l n/2 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hib := (enrichedCylinderPressure_field_cap hN n b hb hh h0 (le_refl (h n)) u hu ν P hm hK hφ r
    (α := (r:ℝ)/N) (by rw [div_mul_cancel₀ _ hn])).1.integrable (by norm_num)
  have hib' := hib.comp_fst gaussianCoordinates
  have hic := integrable_random_cylinder_cgf (P := enrichedCylinderLaw P r n b)
    (measurable_enrichedGibbsReference n h u ν hm) (externalFieldCoefficients n l)
    (fun s => (externalFieldCoefficients_variance n hl l0 s).le) (Real.sqrt a)
  change Integrable (fun p : EnrichedCylinderData n A × (ℕ → ℝ) =>
    enrichedCylinderPressure n h u ν φ p.1) ((enrichedCylinderLaw P r n b).prod gaussianCoordinates) at hib'
  change (∫ z, enrichedCylinderPressure n (fun i => h i+a*l i) u ν φ z ∂enrichedCylinderLaw P r n b) = _
  rw [← (enrichedFieldInsertedPressure_law P r n b hh h0 hl l0 u ν hm ha).integral_eq,
    integral_congr_ae (enrichedField_cgf_eq hN n b hh h0 hl l0 u hu ν P hm hK hφ r a)]
  have hs := integral_sub (hib'.add (hic.div_const (N:ℝ))) (integrable_const (a*l n/2))
  simp only [Pi.add_apply] at hs
  rw [hs]
  have hadd := integral_add hib' (hic.div_const (N:ℝ))
  rw [hadd,integral_div]
  rw [integral_fun_fst (fun p : EnrichedCylinderData n A => enrichedCylinderPressure n h u ν φ p)]
  simp [enrichedMeanPressure]

lemma randomReplicaAverage_zero_fold {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] (ν : Ω → Measure X)
    [∀ ω, IsProbabilityMeasure (ν ω)] (H : Ω → X → ℝ)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H ω x)) (ν ω))
    (b : X → ℕ →₀ ℝ) {m : ℕ} (D : (Fin m → X) → ℝ) :
    randomReplicaAverage P (fun ω => gibbsProbability (ν ω) (H ω)) b 0 D =
      ∫ ω, referenceReplicaMean (ν ω) (H ω) D ∂P := by
  unfold randomReplicaAverage
  have he' := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := gaussianCoordinates)).tendsto_ae.eventually he
  calc
    _ = ∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1) (H z.1) D ∂P.prod gaussianCoordinates := by
      apply integral_congr_ae
      filter_upwards [he'] with z hz
      simp only [zero_mul]
      simpa only [add_zero] using referenceReplicaMean_fold (ν z.1) (H z.1) (fun _ => 0) hz (by simpa using hz) D
    _ = _ := by rw [integral_fun_fst (fun ω => referenceReplicaMean (ν ω) (H ω) D),probReal_univ,one_smul]

 

theorem enrichedMeanPressure_field_derivative {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h l : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hl : Monotone l) (l0 : 0 ≤ l 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    HasDerivWithinAt (fun a => -enrichedMeanPressure P r n b (fun i => h i+a*l i) u ν φ)
      (enrichedReplicaAverage P r n b h u ν φ (fun σ : Fin 2 → Spin N × LabeledLeaf n =>
        spinOverlap (σ 1).1 (σ 0).1*l (labeledCommonDepth n (σ 1).2 (σ 0).2))/2) (Ici 0) 0 := by
  let η := enrichedGibbsReference n h u ν φ
  let Q := enrichedCylinderLaw P r n b
  let E : ℝ → ℝ := fun a => ∫ z : EnrichedCylinderData n A × (ℕ → ℝ),
    cgf (fun s => cylinderField (externalFieldCoefficients n l s) z.2) (η z.1) (Real.sqrt a)
    ∂Q.prod gaussianCoordinates
  have hd := hasDerivWithinAt_random_cylinder_variance
    (P := Q) (measurable_enrichedGibbsReference n h u ν hm) (externalFieldCoefficients n l)
    (fun s => (externalFieldCoefficients_variance n hl l0 s).le)
    (d := N*l n) (fun s => by rw [cylinderCross_self,externalFieldCoefficients_variance n hl l0])
    (v := 0) (by norm_num)
  let D : (Fin 2 → Spin N × LabeledLeaf n) → ℝ := fun σ =>
    spinOverlap (σ 1).1 (σ 0).1*l (labeledCommonDepth n (σ 1).2 (σ 0).2)
  have he := randomReplicaAverage_zero_fold (P := Q)
    (fun p : EnrichedCylinderData n A => labeledSpinReference n ν p.1.2)
    (enrichedHamiltonian n h u φ)
    (enrichedCylinder_exp_ae hN n b hh h0 u hu ν P hK hφ r)
    (externalFieldCoefficients n l)
    (fun σ : Fin 2 → Spin N × LabeledLeaf n =>
      cylinderCross (externalFieldCoefficients n l (σ 1)) (externalFieldCoefficients n l (σ 0)))
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hc : (fun σ : Fin 2 → Spin N × LabeledLeaf n =>
      cylinderCross (externalFieldCoefficients n l (σ 1)) (externalFieldCoefficients n l (σ 0))) =
        (fun σ => (N:ℝ)*D σ) := by
    funext σ
    rw [externalFieldCoefficients_cross n hl l0]
    dsimp [D,spinOverlap]
    field_simp
  rw [hc] at he
  simp only [referenceReplicaMean_const_mul,integral_const_mul] at he
  change randomReplicaAverage Q η (externalFieldCoefficients n l) 0 (fun σ => (N:ℝ)*D σ) =
      (N:ℝ)*enrichedReplicaAverage P r n b h u ν φ D at he
  rw [Real.sqrt_zero,hc,he] at hd
  change HasDerivWithinAt E (((N:ℝ)*l n-(N:ℝ)*enrichedReplicaAverage P r n b h u ν φ D)/2) (Ici 0) 0 at hd
  have hmain := ((hd.div_const (N:ℝ)).const_add (enrichedMeanPressure P r n b h u ν φ)).fun_sub
    (((hasDerivAt_id (0:ℝ)).mul_const (l n)).div_const 2).hasDerivWithinAt
  have hnmain := hmain.neg
  have hval : -(((N:ℝ)*l n-(N:ℝ)*enrichedReplicaAverage P r n b h u ν φ D)/2/N-l n/2) =
      enrichedReplicaAverage P r n b h u ν φ D/2 := by field_simp; ring
  simp only [one_mul] at hnmain
  rw [hval] at hnmain
  apply hnmain.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with a ha
    exact congrArg Neg.neg (enrichedMeanPressure_field_insert hN n b hb hh h0 hl l0 u hu ν P hm hK hφ r ha)
  · exact congrArg Neg.neg (enrichedMeanPressure_field_insert hN n b hb hh h0 hl l0 u hu ν P hm hK hφ r (a := 0) (by norm_num))

end IsingPerceptron

end

end OAI
