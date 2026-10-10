import OAI.Probability.ProjectionMoments.CapTests

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open MeasureTheory
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[fun_prop] lemma measurable_radialLabel {k : ℕ} :
    Measurable (fun z : (Fin k → E) × Label k => radialLabel z.1 z.2) := by
  have hH : Measurable (fun z : (Fin k → E) × Label k => polarRadial z.1) := (continuous_polarRadial (E := E) (k := k)).measurable.comp measurable_fst
  apply (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurable.comp
  apply Measurable.of_eval
  intro i
  change Measurable (fun z : (Fin k → E) × Label k => ∑ j, polarRadial z.1 i j * z.2.ofLp j)
  apply Finset.measurable_sum
  intro j hj
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hH)).mul (by fun_prop)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rowMap_mixRows [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (X : Fin k → E) (s : E) :
    rowMap (mixRows M X) s = WithLp.toLp 2 (M *ᵥ (rowMap X s).ofLp) := by
  ext i
  simp [rowMap, mixRows, Matrix.mulVec, dotProduct]

lemma polar_label_identity {k : ℕ} {X : Fin k → E} (hX : LinearIndependent ℝ X)
    (u : Fin k → E) (c s : E) (r : ℝ) :
    rowMap X (dilate c r s) = rowMap X c + r • radialLabel X (rowMap (polarRows u X) s) := by
  have he : radialLabel X (rowMap (polarRows u X) s) = rowMap X s := by
    rw [radialLabel, ← rowMap_mixRows]
    simp only [polarRows, ite_eq_left hX, polar_reconstruction hX]
  rw [he, dilate, map_add, map_smul]
  exact add_comm _ _

lemma normalizedDensity_unitBall (ν : Measure E) [IsFiniteMeasure ν] {k : ℕ}
    {u : Fin k → E} (hu : Orthonormal ℝ u) (hs : ν.support ⊆ Metric.closedBall 0 1)
    (X : Fin k → E) (hac : ν.map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k))) :
    (unitBallLaw k).withDensity (fun y => normalizedDensity ν k u (X,y)) =
      ν.map (rowMap (polarRows u X)) := by
  have he : (Metric.closedBall (0:Label k) 1).indicator
      (fun y => normalizedDensity ν k u (X,y)) = fun y => normalizedDensity ν k u (X,y) := by
    funext y
    by_cases hy : y ∈ Metric.closedBall (0:Label k) 1
    · simp [hy]
    · rw [Set.indicator_of_notMem hy]
      have hh : 1 < ‖y‖ := by simpa using hy
      exact (normalizedDensity_support ν hu hs X y hh).symm
  rw [unitBallLaw, withDensity_smul_measure, ← withDensity_indicator Metric.isClosed_closedBall.measurableSet, he,
    ← withDensity_smul_measure]
  exact normalizedDensity_is_density ν X hac

@[fun_prop] lemma measurable_capReferenceLabel {k : ℕ} (c : E) (r : ℝ) :
    Measurable (fun z : (Fin k → E) × Label k => capReferenceLabel c r z.1 z.2) := by
  unfold capReferenceLabel
  exact (show Measurable (fun z : (Fin k → E) × Label k => rowMap z.1 c) by
    simp only [rowMap_apply]; fun_prop).add (measurable_radialLabel.const_smul r)

@[fun_prop] lemma measurable_capKernelValue {k : ℕ} {K : (Fin k → E) × Label k → ℝ≥0∞}
    (hK : Measurable K) : Measurable (capKernelValue K) := by
  apply Measurable.lintegral_prod_right
  exact hK.comp (measurable_snd.prodMk (by simp only [rowMap_apply]; fun_prop))

omit [BorelSpace E] in
lemma capReference_le_one [BorelSpace E] {k : ℕ} {K : (Fin k → E) × Label k → ℝ≥0∞}
    (hK1 : ∀ z, K z ≤ 1) (c : E) (r : ℝ) : capReference K c r ≤ 1 := by
  calc
    _ ≤ ∫⁻ X, ∫⁻ z : Label k, (1:ℝ≥0∞) ∂unitBallLaw k ∂Measure.pi (fun _ : Fin k => stdGaussian E) :=
      lintegral_mono (fun X => lintegral_mono (fun z => hK1 _))
    _ = 1 := by simp

omit [BorelSpace E] in
lemma capKernelValue_le_one [BorelSpace E] {k : ℕ} {K : (Fin k → E) × Label k → ℝ≥0∞}
    (hK1 : ∀ z, K z ≤ 1) (s : E) : capKernelValue K s ≤ 1 := by
  calc
    _ ≤ ∫⁻ X : Fin k → E, (1:ℝ≥0∞) ∂Measure.pi (fun _ => stdGaussian E) :=
      lintegral_mono (fun X => hK1 _)
    _ = 1 := by simp

lemma cap_kernel_test_identity {k : ℕ} (hk : k ≤ Module.finrank ℝ E)
    {K : (Fin k → E) × Label k → ℝ≥0∞} (hK : Measurable K)
    (h : E → ℝ≥0∞) (hh : Measurable h) (c : E) {r : ℝ} (hr : 0 < r)
    {u : Fin k → E} (hu : Orthonormal ℝ u)
    [IsFiniteMeasure ((capMeasure c r).withDensity h)]
    (hac : ∀ X, (capTestMeasure h c r).map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k))) :
    (∫⁻ s, h s * capKernelValue K s ∂capMeasure c r) =
      ∫⁻ X, ∫⁻ z, normalizedDensity (capTestMeasure h c r) k u (X,z) *
        K (X,capReferenceLabel c r X z) ∂unitBallLaw k ∂Measure.pi (fun _ => stdGaussian E) := by
  let μ := (capMeasure c r).withDensity h
  let ν := capTestMeasure h c r
  have : IsFiniteMeasure ν := Measure.isFiniteMeasure_map _ _
  have hf (X : Fin k → E) : Measurable (fun s => K (X,rowMap X s)) := by fun_prop
  have he (X : Fin k → E) (hX : LinearIndependent ℝ X) :
      (∫⁻ s, K (X,rowMap X s) ∂μ) =
      ∫⁻ z, normalizedDensity ν k u (X,z)*K (X,capReferenceLabel c r X z) ∂unitBallLaw k := by
    have hid := lintegral_withDensity_eq_lintegral_mul (unitBallLaw k)
      (show Measurable (fun z => normalizedDensity ν k u (X,z)) by fun_prop)
      (show Measurable (fun z => K (X,capReferenceLabel c r X z)) by fun_prop)
    simp only [Pi.mul_apply] at hid
    rw [← hid,
      normalizedDensity_unitBall ν hu (capTestMeasure_support h c hr) X (hac X),
      lintegral_map (by fun_prop) (by fun_prop)]
    change _ = ∫⁻ s, K (X,capReferenceLabel c r X (rowMap (polarRows u X) s)) ∂μ.map (rescale c r)
    rw [lintegral_map (by fun_prop) (measurable_rescale c r)]
    apply lintegral_congr
    intro s
    congr 1
    rw [capReferenceLabel, ← polar_label_identity hX u c (rescale c r s) r,
      dilate_rescale c hr.ne']
  have hid := lintegral_withDensity_eq_lintegral_mul (capMeasure c r) hh (measurable_capKernelValue hK)
  simp only [Pi.mul_apply] at hid
  rw [← hid]
  change (∫⁻ s, ∫⁻ X, K (X,rowMap X s) ∂Measure.pi (fun _ => stdGaussian E) ∂μ) = _
  rw [lintegral_lintegral_swap (show AEMeasurable (fun z : E × (Fin k → E) => K (z.2,rowMap z.2 z.1)) _ by
    apply Measurable.aemeasurable; exact hK.comp (measurable_snd.prodMk (by simp only [rowMap_apply]; fun_prop)))]
  exact lintegral_congr_ae (by filter_upwards [gaussian_rows_ae_linearIndependent k hk] with X hX; exact he X hX)

end

lemma holder_bounded_kernel {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {g f : Ω → ℝ≥0∞} (hg : Measurable g) (hf : Measurable f) (hf1 : ∀ x, f x ≤ 1)
    {p : ℝ} (hp : 1 < p) {D : ℝ≥0∞} (hD : (∫⁻ x, g x^p ∂μ) ≤ D) :
    (∫⁻ x, g x*f x ∂μ) ≤ D^(1/p) * (∫⁻ x, f x ∂μ)^(1-1/p) := by
  have hpq := Real.HolderConjugate.conjExponent hp
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hg.aemeasurable hf.aemeasurable
  have he : 1 / Real.conjExponent p = 1-1/p := by
    simpa only [one_div] using hpq.one_sub_inv.symm
  have hpow : ∀ x, f x ^ Real.conjExponent p ≤ f x := by
    intro x
    simpa only [ENNReal.rpow_one] using ENNReal.rpow_le_rpow_of_exponent_ge (hf1 x) hpq.symm.lt.le
  simp only [Pi.mul_apply, he] at hh
  exact hh.trans (mul_le_mul' (ENNReal.rpow_le_rpow hD (by positivity))
    (ENNReal.rpow_le_rpow (lintegral_mono hpow) (by rw [← he]; exact one_div_nonneg.mpr hpq.symm.pos.le)))

lemma cap_exp_root (C d : ℝ) {p : ℝ} (hp : 0 < p) :
    (ENNReal.ofReal (Real.exp (C*d*p))) ^ (1/p) = ENNReal.ofReal (Real.exp (C*d)) := by
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
  congr 2
  field_simp

lemma cap_dual_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 32 ≤ d →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      ∀ (c : EuclideanSpace ℝ (Fin d)), ‖c‖ = 1 →
      ∀ r : ℝ, 0 < r → r ≤ 2 →
      ∀ D : CapDictionary c r α,
      ∀ K : (Fin k → EuclideanSpace ℝ (Fin d)) × Label k → ℝ≥0∞,
      Measurable K → (∀ z, K z ≤ 1) →
      ∀ h : EuclideanSpace ℝ (Fin d) → ℝ≥0∞, Measurable h →
      (∀ i, ∫⁻ x, h x ∂capMeasure (D.center i) (D.radius i) ≤ ENNReal.ofReal ((r/D.radius i)^α)) →
      (∫⁻ s, h s*capKernelValue K s ∂capMeasure c r) ≤
        ENNReal.ofReal (Real.exp (C*d)) * (capReference K c r)^(1-1/(k:ℝ)) := by
  obtain ⟨C,hC,hmoment⟩ := normalized_unitBall_moment 2048 (by norm_num)
  refine ⟨C,hC,?_⟩
  intro d hd k α c hc r hr hr2 D K hK hK1 h hh hdual
  let : NeZero d := ⟨by omega⟩
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hkd : k ≤ d := by dsimp [k]; omega
  have hkd2 : k+2 ≤ d := by dsimp [k]; omega
  have hdR : (32:ℝ) ≤ d := by exact_mod_cast hd
  have hα : 2*α = (Module.finrank ℝ (EuclideanSpace ℝ (Fin d))-1:ℕ) := by
    simp only [finrank_euclideanSpace_fin, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    dsimp [α]
    ring
  let u : Fin k → EuclideanSpace ℝ (Fin d) := (EuclideanSpace.basisFun (Fin d) ℝ) ∘ Fin.castLE hkd
  have hu : Orthonormal ℝ u := (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.comp _ (Fin.castLE_injective hkd)
  let ν := capTestMeasure h c r
  have hmass := capTestMeasure_mass hr D hdual
  let : IsFiniteMeasure ν := capTestMeasure_finite hr D hdual
  have hs := capTestMeasure_support h c hr
  have hball := capTest_allBall hc hr hr2 (by dsimp [α]; linarith : 0 ≤ α) hα D hdual
  simp only [finrank_euclideanSpace_fin] at hball
  have hac : ∀ X, ν.map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k)) :=
    fun X => capTest_frame_ac h c hr (by simpa using hkd2) _ (polarRows_orthonormal hu X)
  have hm := (hmoment d hd ν u hmass hs hball hu (Filter.Eventually.of_forall hac)).2.2.2
  have hp : (1:ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  let γ := Measure.pi (fun _ : Fin k => stdGaussian (EuclideanSpace ℝ (Fin d)))
  let F : (Fin k → EuclideanSpace ℝ (Fin d)) × Label k → ℝ≥0∞ :=
    fun z => K (z.1,capReferenceLabel c r z.1 z.2)
  have hF : Measurable F := hK.comp (measurable_fst.prodMk (measurable_capReferenceLabel c r))
  have hnorm : (∫⁻ z, normalizedDensity ν k u z ^ (k:ℝ) ∂γ.prod (unitBallLaw k)) ≤
      ENNReal.ofReal (Real.exp (C*d*k)) := by
    rw [lintegral_prod _ (by fun_prop)]
    simpa only [ENNReal.rpow_natCast] using hm
  have hb := holder_bounded_kernel (γ.prod (unitBallLaw k))
    (measurable_normalizedDensity ν k u) hF (fun z => hK1 _) hp hnorm
  rw [cap_exp_root C d (by positivity : (0:ℝ)<k), lintegral_prod _ (by fun_prop),
    lintegral_prod _ (by fun_prop)] at hb
  have hparent : (∫⁻ s, h s ∂capMeasure c r) ≤ 1 := by
    simpa only [D.parent_center,D.parent_radius,div_self hr.ne',Real.one_rpow,ENNReal.ofReal_one] using hdual D.parent
  let : IsFiniteMeasure ((capMeasure c r).withDensity h) :=
    isFiniteMeasure_withDensity (ne_of_lt (hparent.trans_lt (by simp)))
  rw [cap_kernel_test_identity (by simpa using hkd) hK h hh c hr hu hac]
  exact hb

end ProjectionMoments

end

end OAI
