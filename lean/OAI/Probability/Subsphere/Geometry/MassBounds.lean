import Mathlib
import OAI.Probability.Subsphere.Kernels.Precision
import OAI.Probability.Subsphere.Geometry.Integration

namespace OAI

noncomputable section

namespace SubsphereCurrent.Weighted
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

def weightedOnTest {d n : ℕ} (A : Affine.Test d n) (g : Sphere d → ℝ≥0∞)
    (s : Affine.Sphere A.space) : ℝ≥0∞ :=
  (ENNReal.ofReal A.radius)^((d : ℝ)/16) * g (onTest A s)

lemma measurable_weightedOnTest {d n : ℕ} (A : Affine.Test d n)
    {g : Sphere d → ℝ≥0∞} (hg : Measurable g) : Measurable (weightedOnTest A g) :=
  measurable_const.mul (hg.comp (borel_onTest A))

lemma weighted_control {d n k b : ℕ} (A : Affine.Test d n)
    {g : Sphere d → ℝ≥0∞} (hg : Measurable g) (hb : (d : ℝ)/16 ≤ b) :
    Slice.Controlled (weightedOnTest A g) k b (norm d k g) := by
  intro B
  have hB1 : B.radius ≤ 1 := by nlinarith [B.unit,sq_nonneg ‖B.center‖,B.positive]
  have hp : ENNReal.ofReal (B.radius^b) ≤ (ENNReal.ofReal B.radius)^((d : ℝ)/16) := by
    rw [ENNReal.ofReal_pow B.positive.le,← ENNReal.rpow_natCast]
    exact ENNReal.rpow_le_rpow_of_exponent_ge (ENNReal.ofReal_le_one.mpr hB1) hb
  change ENNReal.ofReal (B.radius^b) *
    (∫⁻ s, (ENNReal.ofReal A.radius)^((d : ℝ)/16)*g (onTest A (B.point s))
      ∂Affine.sphereLaw B.space) ≤ _
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)]
  calc
    _ ≤ (ENNReal.ofReal B.radius)^((d : ℝ)/16)*
        ((ENNReal.ofReal A.radius)^((d : ℝ)/16)*
          ∫⁻ s, g (onTest A (B.point s)) ∂Affine.sphereLaw B.space) := mul_le_mul' hp le_rfl
    _ = (ENNReal.ofReal (nestedTest A B).radius)^((d : ℝ)/16)*
        ∫⁻ s, g (onTest (nestedTest A B) s) ∂Affine.sphereLaw (nestedTest A B).space := by
      rw [nested_average A B hg,← mul_assoc,mul_comm ((ENNReal.ofReal B.radius)^((d : ℝ)/16)),
        ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity),← ENNReal.ofReal_mul A.radius_positive.le]
      rfl
    _ ≤ _ := le_iSup (fun D : Affine.Test d k => (ENNReal.ofReal D.radius)^((d : ℝ)/16)*
      ∫⁻ s, g (onTest D s) ∂Affine.sphereLaw D.space) (nestedTest A B)

lemma subspace_perpendicular {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (z : E) {k : ℕ} (hk : k+1 ≤ Module.finrank ℝ E) :
    ∃ K : Submodule ℝ E, Module.finrank ℝ K = k ∧ z ∈ Kᗮ := by
  let U := Submodule.span ℝ ({z} : Set E)
  have hU : Module.finrank ℝ U ≤ 1 := by
    simpa [U] using (finrank_span_le_card (R := ℝ) ({z} : Set E))
  have hd := U.finrank_add_finrank_orthogonal
  obtain ⟨K,hK,hkd⟩ := Quarter.subspace_dimension Uᗮ (k := k) (by omega)
  refine ⟨K,hkd,?_⟩
  apply (Submodule.mem_orthogonal _ _).mpr
  intro x hx
  exact Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span (by simp : z ∈ ({z} : Set E))) (hK hx)

lemma weighted_cap {d n k b : ℕ} (A : Affine.Test d n) [Nontrivial A.space]
    {g : Sphere d → ℝ≥0∞} (hg : Measurable g)
    (hkn : k+1 ≤ n) (hb0 : b+1 ≤ k) (h2b : 2*b ≤ k) (hb : (d : ℝ)/16 ≤ b)
    (z : A.space) {t : ℝ} (ht : 0 < t) :
    (∫⁻ s, Slice.capFunction (weightedOnTest A g) z t s ∂Affine.sphereLaw A.space) ≤
      (2 : ℝ≥0∞)^(n+1)*norm d k g*ENNReal.ofReal (t^(k-b)) := by
  obtain ⟨K,hK,hz⟩ := subspace_perpendicular z (A.dimension ▸ hkn)
  let : Nontrivial K := Module.nontrivial_of_finrank_pos (hK ▸ (by omega : 0 < k))
  simpa only [A.dimension] using Slice.controlled_cap_bound
    (measurable_weightedOnTest A hg) (weighted_control A hg hb) K hK hb0 h2b hz ht


lemma radial_sphere {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (g : Metric.sphere (0 : E) 1 → ℝ≥0∞) (s : Metric.sphere (0 : E) 1) :
    Polar.radial g s.val = g s := by
  simpa using Polar.radial_smul g s (r := 1) zero_lt_one

lemma weightedOnTest_le_one {d n : ℕ} (A : Affine.Test d n)
    {g : Sphere d → ℝ≥0∞} (hg : ∀ s, g s ≤ 1) (s : Affine.Sphere A.space) :
    weightedOnTest A g s ≤ 1 := by
  refine (mul_le_of_le_one_left zero_le ?_).trans (hg _)
  exact ENNReal.rpow_le_one (ENNReal.ofReal_le_one.mpr (radius_le_one A)) (by positivity)

lemma weighted_norm_le_one {d n : ℕ} (hn : 0 < n)
    {g : Sphere d → ℝ≥0∞} (hg : ∀ s, g s ≤ 1) : norm d n g ≤ 1 := by
  apply iSup_le
  intro A
  let : Nontrivial A.space := Module.nontrivial_of_finrank_pos (A.dimension ▸ hn)
  let : IsProbabilityMeasure (Affine.sphereLaw A.space) := SubsphereRegression.sphereLaw_probability
  refine (mul_le_of_le_one_left zero_le ?_).trans
    (by simpa using (lintegral_mono (μ := Affine.sphereLaw A.space) (fun s => hg (onTest A s))))
  exact ENNReal.rpow_le_one (ENNReal.ofReal_le_one.mpr (radius_le_one A)) (by positivity)

section Ambient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

def sphereDensity (g : Metric.sphere (0 : E) 1 → ℝ≥0∞) : Measure E :=
  (SubsphereRegression.ambientSphereLaw (E := E)).withDensity (Polar.radial g)

lemma sphereDensity_integral {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg : Measurable g)
    {f : E → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂sphereDensity g) = ∫⁻ s, g s*f s.val ∂Affine.sphereLaw E := by
  rw [sphereDensity,lintegral_withDensity_eq_lintegral_mul _ (Polar.measurable_radial hg) hf,
    SubsphereRegression.ambientSphereLaw,lintegral_map ((Polar.measurable_radial hg).mul hf) (by fun_prop)]
  apply lintegral_congr
  intro s
  change Polar.radial g s.val*f s.val = _
  rw [radial_sphere]

lemma sphereDensity_cap {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg : Measurable g)
    (z : E) (r : ℝ) :
    sphereDensity g (Metric.closedBall z r) =
      ∫⁻ s, Slice.capFunction g z r s ∂Affine.sphereLaw E := by
  rw [← one_mul (sphereDensity g _),← lintegral_indicator_const Metric.isClosed_closedBall.measurableSet 1,
    sphereDensity_integral hg ((measurable_const : Measurable (fun _ : E => (1 : ℝ≥0∞))).indicator
      Metric.isClosed_closedBall.measurableSet)]
  apply lintegral_congr
  intro s
  by_cases hs : dist s.val z ≤ r <;> simp [Slice.capFunction,Metric.mem_closedBall,hs]

omit [Nontrivial E] in
lemma sphereDensity_le {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg : ∀ s, g s ≤ 1) :
    sphereDensity g ≤ SubsphereRegression.ambientSphereLaw (E := E) := by
  rw [sphereDensity]
  conv_rhs => rw [← withDensity_one (μ := SubsphereRegression.ambientSphereLaw (E := E))]
  apply withDensity_mono
  filter_upwards [] with x
  unfold Polar.radial
  split_ifs <;> simp_all

lemma sphereDensity_finite {g : Metric.sphere (0 : E) 1 → ℝ≥0∞}
    (hg : ∀ s, g s ≤ 1) : IsFiniteMeasure (sphereDensity g) :=
  isFiniteMeasure_of_le _ (sphereDensity_le hg)

lemma sphereDensity_restrict_ball {g : Metric.sphere (0 : E) 1 → ℝ≥0∞}
    (hg : ∀ s, g s ≤ 1) : (sphereDensity g).restrict (Metric.closedBall 0 1) = sphereDensity g := by
  apply Measure.restrict_eq_self_of_ae_mem
  have hnorm : ∀ᵐ x ∂sphereDensity g, ‖x‖ = 1 :=
    MeasureTheory.ae_mono (sphereDensity_le hg) SubsphereRegression.ambientSphereLaw_ae_norm
  filter_upwards [hnorm] with x hx
  simp [Metric.mem_closedBall,dist_zero_right,hx]

end Ambient

lemma polynomialMass_weighted {d n k b : ℕ} (A : Affine.Test d n) [Nontrivial A.space]
    {g : Sphere d → ℝ≥0∞} (hg : Measurable g)
    (hkn : k+1 ≤ n) (hb0 : b+1 ≤ k) (h2b : 2*b ≤ k) (hb : (d : ℝ)/16 ≤ b) :
    SubsphereRegression.PolynomialMass (sphereDensity (weightedOnTest A g)) (k-b)
      ((2 : ℝ≥0∞)^(n+1)*norm d k g) := by
  intro z t ht
  rw [sphereDensity_cap (measurable_weightedOnTest A hg)]
  exact weighted_cap A hg hkn hb0 h2b hb z ht

variable {V : Type*} [Fintype V] [Nonempty V]

def completeRoute (v₀ : V) (w : V → ℝ≥0∞) (hw : ∑ v, w v ≤ 1) : PMF V := by
  classical
  refine ⟨fun v => w v + if v = v₀ then 1-∑ i, w i else 0,?_⟩
  have he : (∑ v, (w v + if v = v₀ then 1-∑ i, w i else 0)) = 1 := by
    simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    exact add_tsub_cancel_of_le hw
  have hh := hasSum_fintype (fun v => w v + if v=v₀ then 1-∑ i, w i else 0)
  rw [he] at hh
  exact hh

omit [Nonempty V] in
lemma completeRoute_ge (v₀ : V) (w : V → ℝ≥0∞) (hw : ∑ v, w v ≤ 1) (v : V) :
    w v ≤ completeRoute v₀ w hw v := by
  classical
  exact le_add_right le_rfl

omit [Nonempty V] in
lemma measurable_completeRoute {X : Type*} [MeasurableSpace X]
    (v₀ : V) (w : V → X → ℝ≥0∞) (hw : ∀ x, ∑ v, w v x ≤ 1)
    (hm : ∀ v, Measurable (w v)) (v : V) :
    Measurable (fun x => completeRoute v₀ (fun i => w i x) (hw x) v) := by
  classical
  change Measurable (fun x => w v x + if v = v₀ then 1-∑ i, w i x else 0)
  split_ifs
  · exact (hm v).add (measurable_const.sub (Finset.measurable_sum _ (fun i _ => hm i)))
  · simpa using hm v

lemma sample_mass_identity {X : Type*} [MeasurableSpace X]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (p : X → PMF V) (hp : ∀ v, Measurable (fun x => p x v))
    (μ : Measure X) [SFinite μ] (v : V) :
    (∫⁻ x, p x v ∂μ) = ∫⁻ r, μ {x | samplePMF (p x) r = v} ∂coinLaw := by
  classical
  have hf : Measurable (fun z : X × ℝ => samplePMF (p z.1) z.2) :=
    measurable_samplePMF (fun i => (hp i).comp measurable_fst) measurable_snd
  have hi : Measurable (fun z : X × ℝ => if samplePMF (p z.1) z.2 = v then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_eq_fun hf measurable_const) measurable_const measurable_const
  have he (x : X) : p x v = ∫⁻ r, (if samplePMF (p x) r = v then (1 : ℝ≥0∞) else 0) ∂coinLaw := by
    rw [lintegral_samplePMF (p x) (fun a => if a=v then (1 : ℝ≥0∞) else 0)]
    simp
  simp_rw [he]
  rw [lintegral_lintegral_swap hi.aemeasurable]
  apply lintegral_congr
  intro r
  have hr : Measurable (fun x : X => samplePMF (p x) r) :=
    measurable_samplePMF hp measurable_const
  change (∫⁻ x, {x | samplePMF (p x) r = v}.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ) = _
  rw [lintegral_indicator_const (measurableSet_eq_fun hr measurable_const),one_mul]

lemma measurable_sample_mass {X : Type*} [MeasurableSpace X]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (p : X → PMF V) (hp : ∀ v, Measurable (fun x => p x v))
    (μ : Measure X) [SFinite μ] (v : V) :
    Measurable (fun r : ℝ => μ {x | samplePMF (p x) r = v}) := by
  classical
  have hf : Measurable (fun z : ℝ × X => samplePMF (p z.2) z.1) :=
    measurable_samplePMF (fun i => (hp i).comp measurable_snd) measurable_fst
  have hi : Measurable (fun z : ℝ × X => if samplePMF (p z.2) z.1 = v then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_eq_fun hf measurable_const) measurable_const measurable_const
  have hmi : Measurable (fun r : ℝ => ∫⁻ x : X,
      (if samplePMF (p x) r = v then (1 : ℝ≥0∞) else 0) ∂μ) := hi.lintegral_prod_right
  convert hmi using 1
  ext r
  have hr : Measurable (fun x : X => samplePMF (p x) r) :=
    measurable_samplePMF hp measurable_const
  change _ = ∫⁻ x, {x | samplePMF (p x) r = v}.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ
  rw [lintegral_indicator_const (measurableSet_eq_fun hr measurable_const),one_mul]

lemma routing_mixture_bound {X : Type*} [MeasurableSpace X]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (μ : V → Measure X) [∀ v, SFinite (μ v)]
    (w : V → X → ℝ≥0∞) (hw : ∀ x, ∑ v, w v x ≤ 1) (hm : ∀ v, Measurable (w v))
    {B : ℝ≥0∞}
    (hb : ∀ φ : X → V, Measurable φ → ∑ v, μ v {x | φ x = v} ≤ B) :
    (∑ v, ∫⁻ x, w v x ∂μ v) ≤ B := by
  classical
  let v₀ : V := Classical.choice inferInstance
  let p (x : X) := completeRoute v₀ (fun v => w v x) (hw x)
  have hp (v : V) : Measurable (fun x => p x v) := measurable_completeRoute v₀ w hw hm v
  calc
    _ ≤ ∑ v, ∫⁻ x, p x v ∂μ v := Finset.sum_le_sum fun v _ => lintegral_mono fun x =>
      completeRoute_ge v₀ (fun i => w i x) (hw x) v
    _ = ∑ v, ∫⁻ r, μ v {x | samplePMF (p x) r = v} ∂coinLaw := by
      simp_rw [sample_mass_identity p hp]
    _ = ∫⁻ r, ∑ v, μ v {x | samplePMF (p x) r = v} ∂coinLaw :=
      (lintegral_finsetSum _ (fun v _ => measurable_sample_mass p hp (μ v) v)).symm
    _ ≤ ∫⁻ _ : ℝ, B ∂coinLaw := lintegral_mono fun r =>
      hb (fun x => samplePMF (p x) r) (measurable_samplePMF hp measurable_const)
    _ = B := by simp

end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable {V : Type*} [Fintype V] [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V]

lemma projection_sphere_integral {m : ℕ}
    {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg : Measurable g) (hg1 : ∀ s, g s ≤ 1)
    {f : ((Fin m → E) × (Fin m → ℝ)) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂SubsphereRegression.projectionLaw (sphereDensity g) m) =
      ∫⁻ s, g s * (∫⁻ X : Fin m → E, f (X,fun i => ⟪s.val,X i⟫)
        ∂Measure.pi (fun _ => stdGaussian E)) ∂Affine.sphereLaw E := by
  let : IsFiniteMeasure (sphereDensity g) := sphereDensity_finite hg1
  have hobs : Measurable (fun z : (Fin m → E) × E => (z.1,fun i => ⟪z.2,z.1 i⟫)) := by fun_prop
  have hi : Measurable (fun z : (Fin m → E) × E => f (z.1,fun i => ⟪z.2,z.1 i⟫)) := hf.comp hobs
  rw [SubsphereRegression.projectionLaw,lintegral_map hf hobs,
    lintegral_prod_symm _ hi.aemeasurable]
  exact sphereDensity_integral hg hi.lintegral_prod_left

lemma sphereDensity_zero_of_mass_zero
    {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg1 : ∀ s, g s ≤ 1)
    {a : ℕ} (hlocal : SubsphereRegression.PolynomialMass (sphereDensity g) a 0) :
    sphereDensity g = 0 := by
  have hz := hlocal 0 1 zero_lt_one
  simp only [zero_mul] at hz
  have hr := sphereDensity_restrict_ball hg1
  apply Measure.measure_univ_eq_zero.mp
  rw [← hr,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter]
  exact le_zero_iff.mp hz

omit [Nonempty V] in
lemma deterministic_sphere_routing {m a q : ℕ} {C : ℝ≥0∞}
    {g : V → Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg1 : ∀ v s, g v s ≤ 1)
    (hlocal : ∀ v, SubsphereRegression.PolynomialMass (sphereDensity (g v)) a C)
    (hCt : C ≠ ∞)
    (ha : a ≤ Module.finrank ℝ E) (hm : m ≤ Module.finrank ℝ E)
    (hq : 1 ≤ q) (hmargin : q+m ≤ a)
    (φ : ((Fin m → E) × (Fin m → ℝ)) → V) (hφ : Measurable φ) :
    (∑ v, SubsphereRegression.projectionLaw (sphereDensity (g v)) m {x | φ x=v}) ≤
      (32768 : ℝ≥0∞)^Module.finrank ℝ E*(Fintype.card V : ℝ≥0∞)^(1/((q : ℝ)+1))*C := by
  let (v : V) : IsFiniteMeasure (sphereDensity (g v)) := sphereDensity_finite (hg1 v)
  by_cases hC : C=0
  · subst C
    have hz (v : V) := sphereDensity_zero_of_mass_zero (hg1 v) (hlocal v)
    simp [hz,SubsphereRegression.projectionLaw]
  · have hb := SubsphereRegression.localized_routing_bound (fun v => sphereDensity (g v))
      hlocal hC hCt Module.finrank_pos ha hm hq hmargin φ hφ (0 : E) zero_lt_one
    simp only [sphereDensity_restrict_ball (hg1 _),one_pow,ENNReal.ofReal_one,mul_one] at hb
    exact hb

lemma sphere_routing_bound {m a q : ℕ} {C : ℝ≥0∞}
    {g : V → Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg : ∀ v, Measurable (g v))
    (hg1 : ∀ v s, g v s ≤ 1)
    (hlocal : ∀ v, SubsphereRegression.PolynomialMass (sphereDensity (g v)) a C)
    (hCt : C ≠ ∞)
    (ha : a ≤ Module.finrank ℝ E) (hm : m ≤ Module.finrank ℝ E)
    (hq : 1 ≤ q) (hmargin : q+m ≤ a)
    (κ : V → ((Fin m → E) × (Fin m → ℝ)) → ℝ≥0∞)
    (hκ : ∀ v, Measurable (κ v)) (hκ1 : ∀ obs, ∑ v, κ v obs ≤ 1) :
    (∑ v, ∫⁻ s, g v s * (∫⁻ X : Fin m → E, κ v (X,fun i => ⟪s.val,X i⟫)
      ∂Measure.pi (fun _ => stdGaussian E)) ∂Affine.sphereLaw E) ≤
      (32768 : ℝ≥0∞)^Module.finrank ℝ E*(Fintype.card V : ℝ≥0∞)^(1/((q : ℝ)+1))*C := by
  let (v : V) : IsFiniteMeasure (sphereDensity (g v)) := sphereDensity_finite (hg1 v)
  let (v : V) : IsFiniteMeasure (SubsphereRegression.projectionLaw (sphereDensity (g v)) m) := by
    unfold SubsphereRegression.projectionLaw
    infer_instance
  simp_rw [← projection_sphere_integral (hg _) (hg1 _) (hκ _)]
  exact routing_mixture_bound (fun v => SubsphereRegression.projectionLaw (sphereDensity (g v)) m)
    κ hκ1 hκ (fun φ hφ => deterministic_sphere_routing hg1 hlocal hCt ha hm hq hmargin φ hφ)

end SubsphereCurrent.Weighted

end

end OAI
