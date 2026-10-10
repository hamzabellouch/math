import Mathlib

namespace OAI

/-!
# Five-ball Hausdorff comparison for integral varifolds

Integral varifolds are modeled by rectifiable weighted measures and tangent projections.
Smooth graphs provide the regular-locus model. The supporting results establish local
finiteness, Hausdorff domination, first-variation integrability, and smooth graph embeddings.

A five-ball covering gives quantitative Hausdorff comparison from local lower ball-mass
bounds, and localization gives the corresponding null-set comparison for integral varifolds.
The lower bounds and weight-nullness are hypotheses: stationary monotonicity, weighted
almost-everywhere regularity, and the geometric-measure bridge are not proved here. Thus
neither stationary integral-varifold almost-everywhere regularity nor its round-sphere
corollary is established.
-/

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology InnerProductSpace

namespace StationaryVarifolds

 
abbrev Euclidean (d : ℕ) := EuclideanSpace ℝ (Fin d)

 
abbrev PlaneEnd (d : ℕ) := Euclidean d →L[ℝ] Euclidean d

instance planeEndMeasurableSpace (d : ℕ) : MeasurableSpace (PlaneEnd d) := borel _
instance planeEndBorelSpace (d : ℕ) : BorelSpace (PlaneEnd d) := ⟨rfl⟩

 
def CountablyRectifiable (m d : ℕ) (E : Set (Euclidean d)) : Prop :=
  ∃ (A : ℕ → Set (Euclidean m)) (f : ℕ → Euclidean m → Euclidean d)
    (L : ℕ → ℝ≥0),
    (∀ i, LipschitzOnWith (L i) (f i) (A i)) ∧
    μH[(m : ℝ)] (E \ ⋃ i, f i '' A i) = 0

 

def IsApproximateTangentPlane (m d : ℕ) (E : Set (Euclidean d))
    (x : Euclidean d) (T : Submodule ℝ (Euclidean d)) : Prop :=
  Module.finrank ℝ T = m ∧
  ∀ ε : ℝ, 0 < ε →
    Tendsto
      (fun r : ℝ =>
        μH[(m : ℝ)] (E ∩ ball x r ∩
          {y | ε * ‖y - x‖ < ‖(y - x) - T.starProjection (y - x)‖}) /
        ENNReal.ofReal r ^ m)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞))

 

def rectifiableWeight (m d : ℕ) (E : Set (Euclidean d))
    (θ : Euclidean d → ℕ) : Measure (Euclidean d) :=
  (μH[(m : ℝ)].restrict E).withDensity (fun x => (θ x : ℝ≥0∞))

 

structure IntegralVarifold (m n : ℕ) (U : Set (Euclidean (m + n))) where
  carrier : Set (Euclidean (m + n))
  carrier_subset : carrier ⊆ U
  carrier_measurable : NullMeasurableSet carrier μH[(m : ℝ)]
  rectifiable : CountablyRectifiable m (m + n) carrier
  multiplicity : Euclidean (m + n) → ℕ
  multiplicity_measurable : AEMeasurable multiplicity (μH[(m : ℝ)].restrict carrier)
  multiplicity_pos : ∀ x ∈ carrier, 0 < multiplicity x
  locally_finite : ∀ K : Set (Euclidean (m + n)), IsCompact K → K ⊆ U →
    rectifiableWeight m (m + n) carrier multiplicity K < ⊤
  plane : Euclidean (m + n) → PlaneEnd (m + n)
  plane_measurable : AEMeasurable plane (rectifiableWeight m (m + n) carrier multiplicity)
  plane_tangent : ∀ᵐ x ∂(μH[(m : ℝ)].restrict carrier),
    ∃ T : Submodule ℝ (Euclidean (m + n)),
      IsApproximateTangentPlane m (m + n) carrier x T ∧ plane x = T.starProjection

 
def tangentialDivergence {d : ℕ} (P : Euclidean d → PlaneEnd d)
    (X : Euclidean d → Euclidean d) (x : Euclidean d) : ℝ :=
  LinearMap.trace ℝ (Euclidean d) ((P x).toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap)

 

def StationaryWeight {d : ℕ} (U : Set (Euclidean d)) (μ : Measure (Euclidean d))
    (P : Euclidean d → PlaneEnd d) : Prop :=
  ∀ X : Euclidean d → Euclidean d,
    ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
      ∫ x, tangentialDivergence P X x ∂μ = 0

 

def liftedMeasure {d : ℕ} (μ : Measure (Euclidean d)) (P : Euclidean d → PlaneEnd d) :
    Measure (Euclidean d × PlaneEnd d) :=
  μ.map (fun x => (x, P x))

namespace IntegralVarifold

variable {m n : ℕ} {U : Set (Euclidean (m + n))}

def weight (V : IntegralVarifold m n U) : Measure (Euclidean (m + n)) :=
  rectifiableWeight m (m + n) V.carrier V.multiplicity

def measure (V : IntegralVarifold m n U) : Measure (Euclidean (m + n) × PlaneEnd (m + n)) :=
  liftedMeasure V.weight V.plane

def Stationary (V : IntegralVarifold m n U) : Prop :=
  StationaryWeight U V.weight V.plane

end IntegralVarifold

 

structure SmoothGraph (m n : ℕ) where
  domain : Set (Euclidean m)
  domain_open : IsOpen domain
  origin : Euclidean (m + n)
  horizontal : Euclidean m →ₗᵢ[ℝ] Euclidean (m + n)
  height : Euclidean m → Euclidean (m + n)
  height_smooth : ContDiffOn ℝ ⊤ height domain
  height_normal : ∀ y ∈ domain, height y ∈ (LinearMap.range horizontal.toLinearMap)ᗮ

namespace SmoothGraph

variable {m n : ℕ}

def parametrization (G : SmoothGraph m n) (y : Euclidean m) : Euclidean (m + n) :=
  G.origin + G.horizontal y + G.height y

def carrier (G : SmoothGraph m n) : Set (Euclidean (m + n)) :=
  G.parametrization '' G.domain

 
def parameter (G : SmoothGraph m n) (x : Euclidean (m + n)) : Euclidean m :=
  G.horizontal.toContinuousLinearMap.adjoint (x - G.origin)

 
def plane (G : SmoothGraph m n) (x : Euclidean (m + n)) : PlaneEnd (m + n) :=
  (LinearMap.range (fderiv ℝ G.parametrization (G.parameter x)).toLinearMap).starProjection

def weight (G : SmoothGraph m n) : Measure (Euclidean (m + n)) :=
  μH[(m : ℝ)].restrict G.carrier

def measure (G : SmoothGraph m n) : Measure (Euclidean (m + n) × PlaneEnd (m + n)) :=
  liftedMeasure G.weight G.plane

 

def MinimalIn (G : SmoothGraph m n) (W : Set (Euclidean (m + n))) : Prop :=
  StationaryWeight W G.weight G.plane

end SmoothGraph

namespace IntegralVarifold

variable {m n : ℕ} {U : Set (Euclidean (m + n))}

 

def RegularAt (V : IntegralVarifold m n U) (p : Euclidean (m + n)) : Prop :=
  ∃ W : Set (Euclidean (m + n)), IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧
    ∃ G : SmoothGraph m n, p ∈ G.carrier ∧ G.carrier ⊆ W ∧ G.MinimalIn W ∧
      ∃ q : ℕ, 1 ≤ q ∧ V.measure.restrict (Prod.fst ⁻¹' W) = (q : ℝ≥0∞) • G.measure

 

def singularSet (V : IntegralVarifold m n U) : Set (Euclidean (m + n)) :=
  (V.weight.support ∩ U) \ {p | V.RegularAt p}


 

theorem exists_finite_open_nhds (V : IntegralVarifold m n U) (hU : IsOpen U)
    {x : Euclidean (m + n)} (hx : x ∈ U) :
    ∃ O : Set (Euclidean (m + n)), IsOpen O ∧ x ∈ O ∧ V.weight O < ⊤ := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  have hsub : closedBall x (r / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith : r / 2 < r)).trans hball
  refine ⟨ball x (r / 2), isOpen_ball, mem_ball_self (by linarith), ?_⟩
  exact (measure_mono ball_subset_closedBall).trans_lt
    (V.locally_finite _ (isCompact_closedBall x (r / 2)) hsub)

 
theorem weight_apply (V : IntegralVarifold m n U) (A : Set (Euclidean (m + n)))
    (hA : MeasurableSet A) :
    V.weight A = ∫⁻ x in V.carrier ∩ A, (V.multiplicity x : ℝ≥0∞) ∂μH[(m : ℝ)] := by
  rw [weight, rectifiableWeight, withDensity_apply _ hA, Measure.restrict_restrict hA,
    inter_comm A V.carrier]

 
theorem map_fst_measure (V : IntegralVarifold m n U) :
    V.measure.map Prod.fst = V.weight := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA, measure, liftedMeasure, weight]
  erw [Measure.map_apply_of_aemeasurable
      (aemeasurable_id.prodMk V.plane_measurable) (hA.preimage measurable_fst)]
  rfl

 
theorem hausdorff_restrict_le (V : IntegralVarifold m n U) :
    μH[(m : ℝ)].restrict V.carrier ≤ V.weight := by
  have h : (1 : Euclidean (m + n) → ℝ≥0∞) ≤ᵐ[μH[(m : ℝ)].restrict V.carrier]
      (fun x => (V.multiplicity x : ℝ≥0∞)) := by
    filter_upwards [ae_restrict_mem₀ V.carrier_measurable] with x hx
    change (1 : ℝ≥0∞) ≤ (V.multiplicity x : ℝ≥0∞)
    exact_mod_cast Nat.succ_le_iff.mpr (V.multiplicity_pos x hx)
  simpa only [withDensity_one, weight, rectifiableWeight] using withDensity_mono h

 

theorem hausdorff_inter_carrier_zero (V : IntegralVarifold m n U)
    (A : Set (Euclidean (m + n))) (hA : V.weight A = 0) :
    μH[(m : ℝ)] (A ∩ V.carrier) = 0 := by
  have h := V.hausdorff_restrict_le A
  rw [Measure.restrict_apply₀' V.carrier_measurable, hA] at h
  exact le_antisymm h zero_le

 
theorem ae_norm_plane_le_one (V : IntegralVarifold m n U) :
    ∀ᵐ x ∂V.weight, ‖V.plane x‖ ≤ 1 := by
  apply (withDensity_absolutelyContinuous (μH[(m : ℝ)].restrict V.carrier)
    (fun x => (V.multiplicity x : ℝ≥0∞))).ae_le
  filter_upwards [V.plane_tangent] with x hx
  obtain ⟨T, _, hT⟩ := hx
  rw [hT]
  exact T.starProjection_norm_le

 

theorem integrable_tangentialDivergence (V : IntegralVarifold m n U)
    (X : Euclidean (m + n) → Euclidean (m + n)) (hX : ContDiff ℝ 1 X)
    (hc : HasCompactSupport X) (hU : tsupport X ⊆ U) :
    Integrable (tangentialDivergence V.plane X) V.weight := by
  let tr : PlaneEnd (m + n) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      (LinearMap.trace ℝ (Euclidean (m + n)) ∘ₗ ContinuousLinearMap.coeLM ℝ)
  change Integrable (fun x => tr (V.plane x ∘L fderiv ℝ X x)) V.weight
  have hd : Continuous (fderiv ℝ X) := hX.continuous_fderiv (by norm_num)
  have ht : Continuous (fun z : PlaneEnd (m + n) × PlaneEnd (m + n) =>
      tr (z.1 ∘L z.2)) := tr.continuous.comp (continuous_fst.clm_comp continuous_snd)
  have hf : AEMeasurable (fun x => tr (V.plane x ∘L fderiv ℝ X x)) V.weight :=
    ht.measurable.comp_aemeasurable (V.plane_measurable.prodMk hd.measurable.aemeasurable)
  let : IsFiniteMeasure (V.weight.restrict (tsupport X)) :=
    isFiniteMeasure_restrict.mpr (V.locally_finite (tsupport X) hc hU).ne
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn hd.continuousOn
  apply IntegrableOn.integrable_of_forall_notMem_eq_zero (s := tsupport X)
  · apply (integrable_const (μ := V.weight.restrict (tsupport X)) (‖tr‖ * B)).mono'
      hf.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_of_ae V.ae_norm_plane_le_one,
      ae_restrict_mem (isClosed_tsupport X).measurableSet] with x hP hx
    have hpd : ‖V.plane x ∘L fderiv ℝ X x‖ ≤ B := by
      calc
        _ ≤ ‖V.plane x‖ * ‖fderiv ℝ X x‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * ‖fderiv ℝ X x‖ := mul_le_mul_of_nonneg_right hP (norm_nonneg _)
        _ ≤ B := by simpa only [one_mul] using hB x hx
    exact (tr.le_opNorm _).trans (mul_le_mul_of_nonneg_left hpd (norm_nonneg _))
  · intro x hx
    simp [fderiv_of_notMem_tsupport ℝ hx]

end IntegralVarifold

namespace SmoothGraph
variable {m n : ℕ}

 

theorem parameter_parametrization (G : SmoothGraph m n) {y : Euclidean m}
    (hy : y ∈ G.domain) : G.parameter (G.parametrization y) = y := by
  have hnorm : G.horizontal.toContinuousLinearMap.adjoint (G.height y) = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact Submodule.inner_right_of_mem_orthogonal
      (K := LinearMap.range G.horizontal.toLinearMap) ⟨_, rfl⟩ (G.height_normal y hy)
  have hlin : G.horizontal.toContinuousLinearMap.adjoint (G.horizontal y) = y := by
    change (G.horizontal.toContinuousLinearMap.adjoint ∘L G.horizontal.toContinuousLinearMap) y = y
    rw [G.horizontal.adjoint_comp_self]
    rfl
  have hs : G.parametrization y - G.origin = G.horizontal y + G.height y := by
    simp only [parametrization]
    abel
  rw [parameter, hs, map_add, hnorm, hlin, add_zero]

theorem parametrization_smooth (G : SmoothGraph m n) :
    ContDiffOn ℝ ⊤ G.parametrization G.domain :=
  (contDiffOn_const.add G.horizontal.contDiff.contDiffOn).add G.height_smooth

theorem parameter_continuous (G : SmoothGraph m n) : Continuous G.parameter :=
  G.horizontal.toContinuousLinearMap.adjoint.continuous.comp (continuous_id.sub continuous_const)

 
theorem parametrization_isEmbedding (G : SmoothGraph m n) :
    Topology.IsEmbedding (fun y : G.domain => G.parametrization y) := by
  refine Topology.IsEmbedding.of_comp G.parametrization_smooth.continuousOn.domRestrict
    G.parameter_continuous ?_
  have h : G.parameter ∘ (fun y : G.domain => G.parametrization y) = Subtype.val := by
    funext y
    exact G.parameter_parametrization y.property
  rw [h]
  exact Topology.IsEmbedding.subtypeVal

 
theorem parametrization_rank (G : SmoothGraph m n) {y : Euclidean m} (hy : y ∈ G.domain) :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ G.parametrization y).toLinearMap) = m := by
  have hF : DifferentiableAt ℝ G.parametrization y :=
    (G.parametrization_smooth.differentiableOn (by simp) y hy).differentiableAt
      (G.domain_open.mem_nhds hy)
  have hp : HasFDerivAt G.parameter G.horizontal.toContinuousLinearMap.adjoint
      (G.parametrization y) := by
    change HasFDerivAt (fun x => G.horizontal.toContinuousLinearMap.adjoint (x - G.origin))
      G.horizontal.toContinuousLinearMap.adjoint (G.parametrization y)
    convert
      G.horizontal.toContinuousLinearMap.adjoint.hasFDerivAt.comp (G.parametrization y)
        ((hasFDerivAt_id (G.parametrization y)).sub_const G.origin) using 1 <;>
      simp only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id]
  have heq : id =ᶠ[𝓝 y] (G.parameter ∘ G.parametrization) := by
    filter_upwards [G.domain_open.mem_nhds hy] with z hz
    exact (G.parameter_parametrization hz).symm
  have hD : G.horizontal.toContinuousLinearMap.adjoint ∘L fderiv ℝ G.parametrization y =
      ContinuousLinearMap.id ℝ (Euclidean m) :=
    ((hp.comp y hF.hasFDerivAt).congr_of_eventuallyEq heq).unique (hasFDerivAt_id y)
  have hinj : Function.Injective (fderiv ℝ G.parametrization y) := by
    apply Function.LeftInverse.injective (g := G.horizontal.toContinuousLinearMap.adjoint)
    intro v
    change (G.horizontal.toContinuousLinearMap.adjoint ∘L fderiv ℝ G.parametrization y) v = v
    rw [hD]
    rfl
  simpa [Euclidean, finrank_euclideanSpace] using LinearMap.finrank_range_of_inj hinj

end SmoothGraph

 

 

theorem ball_bound_on_support_of_ae
    {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (U : Set X) (d : ℕ) (C : ℝ≥0∞)
    (hbound : ∀ᵐ x ∂μ, ∀ R : ℝ, 0 < R → closedBall x R ⊆ U →
      ENNReal.ofReal R ^ d ≤ C * μ (ball x R))
    {p : X} (hp : p ∈ μ.support) {R : ℝ} (hR : 0 < R)
    (hball : closedBall p R ⊆ U) :
    ENNReal.ofReal R ^ d ≤ C * μ (ball p R) := by
  have hsmall (r : ℝ) (hr : 0 < r) (hrR : r < R) :
      ENNReal.ofReal r ^ d ≤ C * μ (ball p R) := by
    have ht : 0 < μ (ball p (R - r)) :=
      (Measure.mem_support_iff_forall p).mp hp _ (ball_mem_nhds _ (sub_pos.mpr hrR))
    obtain ⟨x, hx, hxb⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae ht.ne'
      (ae_restrict_of_ae hbound)
    have hxr : closedBall x r ⊆ ball p R :=
      closedBall_subset_ball' (by have h := mem_ball.mp hx; linarith)
    exact (hxb r hr (hxr.trans (ball_subset_closedBall.trans hball))).trans
      (mul_le_mul_right (measure_mono (ball_subset_closedBall.trans hxr)) C)
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal r ^ d) (𝓝[<] R)
      (𝓝 (ENNReal.ofReal R ^ d)) :=
    ((ENNReal.continuous_pow d).comp ENNReal.continuous_ofReal).continuousAt.tendsto
      |>.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  have hpos : ∀ᶠ r : ℝ in 𝓝[<] R, 0 < r :=
    nhdsWithin_le_nhds (eventually_gt_nhds hR)
  filter_upwards [hpos, self_mem_nhdsWithin (s := Iio R)] with r hr hrR
  exact hsmall r hr hrR

 

section Covering

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X]

 

theorem hausdorffMeasure_le_open_of_ball_bound
    (μ : Measure X) (s O : Set X) (d : ℕ) (C : ℝ≥0∞)
    (hO : IsOpen O) (hsO : s ⊆ O)
    (hlower : ∀ x ∈ s, ∃ R > 0, ∀ r, 0 < r → r < R →
      ENNReal.ofReal r ^ d ≤ C * μ (ball x r)) :
    μH[(d : ℝ)] s ≤ (10 : ℝ≥0∞) ^ d * C * μ O := by
  classical
  rw [Measure.hausdorffMeasure, ← OuterMeasure.coe_mkMetric]
  change (OuterMeasure.mkMetric' (fun A : Set X => ediam A ^ (d : ℝ))) s ≤ _
  simp only [OuterMeasure.mkMetric', OuterMeasure.iSup_apply]
  refine iSup₂_le fun δ hδ => ?_
  obtain ⟨ε, -, hε0, hεδ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hδ
  have hε : 0 < ε := by simpa only [ENNReal.ofReal_pos] using hε0
  have hballs (x : s) : ∃ r : ℝ, 0 < r ∧ r ≤ ε / 10 ∧
      ball (x : X) r ⊆ O ∧ ENNReal.ofReal r ^ d ≤ C * μ (ball (x : X) r) := by
    obtain ⟨R, hR, hl⟩ := hlower x x.property
    obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.mp hO x (hsO x.property)
    obtain ⟨r, hr, hrlt⟩ := exists_between (lt_min hR (lt_min hρ (by positivity : 0 < ε / 10)))
    refine ⟨r, hr, (hrlt.trans_le (min_le_right _ _)).le.trans (min_le_right _ _), ?_,
      hl r hr (hrlt.trans_le (min_le_left _ _))⟩
    exact (ball_subset_ball (hrlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le).trans hρO
  choose r hrpos hrcap hrO hrlower using hballs
  obtain ⟨u, -, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      (univ : Set s) (fun x : s => (x : X)) r (ε / 10) (fun x _ => hrcap x) 5 (by norm_num)
  have huc : u.Countable := hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun x _ => ⟨(x : X), mem_ball_self (hrpos x)⟩)
  have : Countable u := huc.to_subtype
  have hcover' : s ⊆ ⋃ x : u, ball ((x : s) : X) (5 * r x) := by
    intro x hxs
    obtain ⟨y, hy, hxy⟩ := hcover ⟨x, hxs⟩ (mem_univ _)
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxy (mem_ball_self (hrpos ⟨x, hxs⟩))⟩
  have hdiam (x : u) : ediam (ball ((x : s) : X) (5 * r x)) ≤
      10 * ENNReal.ofReal (r x) := by
    calc
      _ ≤ 2 * ENNReal.ofReal (5 * r x) := by
        simpa only [Metric.eball_ofReal] using
          (Metric.ediam_eball_le (x := ((x : s) : X)) (r := ENNReal.ofReal (5 * r x)))
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]; norm_num; ring
  have hdiamδ (x : u) : ediam (ball ((x : s) : X) (5 * r x)) ≤ δ := by
    refine (hdiam x).trans (le_trans ?_ hεδ.le)
    calc
      10 * ENNReal.ofReal (r x) = ENNReal.ofReal (10 * r x) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10)]; norm_num
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by linarith [hrcap x])
  have hμ : (∑' x : u, μ (ball ((x : s) : X) (r x))) ≤ μ O := by
    rw [← measure_iUnion (hdisj.subtype _ _) (fun _ => measurableSet_ball)]
    exact measure_mono (iUnion_subset (fun x => hrO x))
  calc
    _ ≤ OuterMeasure.mkMetric'.pre (fun A : Set X => ediam A ^ (d : ℝ)) δ
        (⋃ x : u, ball ((x : s) : X) (5 * r x)) := measure_mono hcover'
    _ ≤ ∑' x : u, OuterMeasure.mkMetric'.pre (fun A : Set X => ediam A ^ (d : ℝ)) δ
        (ball ((x : s) : X) (5 * r x)) := measure_iUnion_le _
    _ ≤ ∑' x : u, ediam (ball ((x : s) : X) (5 * r x)) ^ (d : ℝ) :=
      ENNReal.tsum_le_tsum (fun x => OuterMeasure.mkMetric'.pre_le (hdiamδ x))
    _ ≤ ∑' x : u, (10 : ℝ≥0∞) ^ d * C * μ (ball ((x : s) : X) (r x)) := by
      apply ENNReal.tsum_le_tsum
      intro x
      rw [ENNReal.rpow_natCast]
      calc
        _ ≤ (10 * ENNReal.ofReal (r x)) ^ d := pow_le_pow_left' (hdiam x) d
        _ = (10 : ℝ≥0∞) ^ d * ENNReal.ofReal (r x) ^ d := mul_pow _ _ _
        _ ≤ (10 : ℝ≥0∞) ^ d * (C * μ (ball ((x : s) : X) (r x))) :=
          mul_le_mul_right (hrlower x) _
        _ = _ := (mul_assoc _ _ _).symm
    _ = (10 : ℝ≥0∞) ^ d * C * ∑' x : u, μ (ball ((x : s) : X) (r x)) :=
      ENNReal.tsum_mul_left
    _ ≤ (10 : ℝ≥0∞) ^ d * C * μ O := mul_le_mul_right hμ _

 

theorem hausdorffMeasure_le_mul_of_ball_bound
    (μ : Measure X) [μ.OuterRegular] (s : Set X) (d : ℕ) (C : ℝ≥0)
    (hlower : ∀ x ∈ s, ∃ R > 0, ∀ r, 0 < r → r < R →
      ENNReal.ofReal r ^ d ≤ (C : ℝ≥0∞) * μ (ball x r)) :
    μH[(d : ℝ)] s ≤ (10 : ℝ≥0∞) ^ d * C * μ s := by
  by_cases hC : C = 0
  · have h := hausdorffMeasure_le_open_of_ball_bound μ s univ d C
      isOpen_univ (subset_univ _) hlower
    simpa [hC] using h
  have hA0 : (10 : ℝ≥0∞) ^ d * C ≠ 0 := by
    simp [hC]
  have hAtop : (10 : ℝ≥0∞) ^ d * C ≠ ⊤ := by finiteness
  rw [s.measure_eq_iInf_isOpen μ]
  simp only [ENNReal.mul_iInf_of_ne hA0 hAtop]
  exact le_iInf fun O => le_iInf fun hsO => le_iInf fun hO =>
    hausdorffMeasure_le_open_of_ball_bound μ s O d C hO hsO hlower

 

theorem hausdorffMeasure_zero_of_ball_bound
    (μ : Measure X) [μ.OuterRegular] (s : Set X) (d : ℕ) (C : ℝ≥0)
    (hnull : μ s = 0)
    (hlower : ∀ x ∈ s, ∃ R > 0, ∀ r, 0 < r → r < R →
      ENNReal.ofReal r ^ d ≤ (C : ℝ≥0∞) * μ (ball x r)) :
    μH[(d : ℝ)] s = 0 := by
  apply le_antisymm _ (zero_le)
  simpa [hnull] using hausdorffMeasure_le_mul_of_ball_bound μ s d C hlower

 

theorem hausdorffMeasure_zero_of_locally_finite_ball_bound
    (μ : Measure X) (s : Set X) (d : ℕ) (C : ℝ≥0)
    (hfinite : ∀ x ∈ s, ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ μ O < ⊤)
    (hnull : μ s = 0)
    (hlower : ∀ x ∈ s, ∃ R > 0, ∀ r, 0 < r → r < R →
      ENNReal.ofReal r ^ d ≤ (C : ℝ≥0∞) * μ (ball x r)) :
    μH[(d : ℝ)] s = 0 := by
  classical
  choose O hO hxO hμO using fun x : s => hfinite x x.property
  have hlocal (i : s) : μH[(d : ℝ)] (s ∩ O i) = 0 := by
    let : IsFiniteMeasure (μ.restrict (O i)) := isFiniteMeasure_restrict.mpr (hμO i).ne
    apply hausdorffMeasure_zero_of_ball_bound (μ.restrict (O i)) (s ∩ O i) d C
    · apply le_antisymm _ zero_le
      exact (Measure.restrict_le_self (s ∩ O i)).trans
        (le_trans (measure_mono inter_subset_left) hnull.le)
    · intro x hx
      obtain ⟨R, hR, hlow⟩ := hlower x hx.1
      obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.mp (hO i) x hx.2
      refine ⟨min R ρ, lt_min hR hρ, fun r hr hrR => ?_⟩
      have hball : ball x r ⊆ O i :=
        (ball_subset_ball (hrR.trans_le (min_le_right _ _)).le).trans hρO
      rw [Measure.restrict_apply measurableSet_ball, inter_eq_left.mpr hball]
      exact hlow r hr (hrR.trans_le (min_le_left _ _))
  obtain ⟨t, htc, ht⟩ := isOpen_iUnion_countable O hO
  have hcover : s ⊆ ⋃ i ∈ t, s ∩ O i := by
    intro x hx
    have h : x ∈ ⋃ i ∈ t, O i := ht.symm ▸ mem_iUnion.mpr ⟨⟨x, hx⟩, hxO ⟨x, hx⟩⟩
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp h
    exact mem_iUnion₂.mpr ⟨i, hi, hx, hxi⟩
  exact measure_mono_null hcover (measure_biUnion_null_iff htc |>.mpr fun i _ => hlocal i)

end Covering

namespace IntegralVarifold

 

theorem hausdorff_zero_of_weight_zero_of_ball_bound
    {m n : ℕ} {U : Set (Euclidean (m + n))}
    (V : IntegralVarifold m n U) (hU : IsOpen U)
    (A : Set (Euclidean (m + n))) (hAU : A ⊆ U) (C : ℝ≥0)
    (hnull : V.weight A = 0)
    (hlower : ∀ x ∈ A, ∃ R > 0, ∀ r, 0 < r → r < R →
      ENNReal.ofReal r ^ m ≤ (C : ℝ≥0∞) * V.weight (ball x r)) :
    μH[(m : ℝ)] A = 0 :=
  hausdorffMeasure_zero_of_locally_finite_ball_bound V.weight A m C
    (fun _ hx => V.exists_finite_open_nhds hU (hAU hx)) hnull hlower

end IntegralVarifold
end StationaryVarifolds

end

end OAI
