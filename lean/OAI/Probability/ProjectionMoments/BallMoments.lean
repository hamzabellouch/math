import OAI.Probability.ProjectionMoments.Polar

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
attribute [fun_prop] measurable_polarRows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma rowMap_ac_iff {ν : Measure E} {k : ℕ} (A : Fin k → E) :
    ν.map (rowMap A) ≪ (volume : Measure (Label k)) ↔
      ν.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ)) := by
  constructor
  · intro h
    have hh := h.map (MeasurableEquiv.toLp 2 (Fin k → ℝ)).symm.measurable
    rw [(EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin k)).map_eq,
      Measure.map_map (by fun_prop) (by fun_prop)] at hh
    exact hh
  · intro h
    rw [rowMap_eq_toLp_coordinateMap, ← Measure.map_map (by fun_prop) (by fun_prop),
      ← (PiLp.volume_preserving_toLp (Fin k)).map_eq]
    exact h.map (by fun_prop)

lemma measurableSet_projection_ac (ν : Measure E) [IsFiniteMeasure ν] (k : ℕ) :
    MeasurableSet {A : Fin k → E | ν.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ))} := by
  have h := Kernel.measurableSet_absolutelyContinuous (projectionKernel ν k)
    (Kernel.const (Fin k → E) (volume : Measure (Fin k → ℝ)).toFinite)
  convert h using 1
  ext A
  exact ⟨fun h => h.trans (absolutelyContinuous_toFinite volume),
    fun h => h.trans (toFinite_absolutelyContinuous volume)⟩

lemma polar_ac_to_frame (ν : Measure E) [IsFiniteMeasure ν] {k : ℕ}
    (hk : k ≤ Module.finrank ℝ E) {u : Fin k → E} (hu : Orthonormal ℝ u)
    (h : ∀ᵐ X ∂Measure.pi (fun _ : Fin k => stdGaussian E),
      ν.map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k))) :
    ∀ᵐ A ∂frameLaw u, ν.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ)) := by
  rw [← polarRows_law hk hu]
  apply (ae_map_iff (measurable_polarRows u).aemeasurable (measurableSet_projection_ac ν k)).mpr
  filter_upwards [h] with X hX
  exact (rowMap_ac_iff _).mp hX

lemma unitBallVolume_ne_zero (k : ℕ) : unitBallVolume k ≠ 0 := by
  apply ne_of_gt
  exact (Metric.measure_ball_pos volume 0 one_pos).trans_le (measure_mono Metric.ball_subset_closedBall)
lemma unitBallVolume_ne_top (k : ℕ) : unitBallVolume k ≠ ∞ :=
  (isCompact_closedBall (0 : Label k) (1:ℝ)).measure_ne_top
instance unitBallLaw_probability (k : ℕ) : IsProbabilityMeasure (unitBallLaw k) := by
  constructor
  simp only [unitBallLaw, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (unitBallVolume_ne_zero k) (unitBallVolume_ne_top k)

lemma unitBallVolume_bound (k : ℕ) (hk : 1 ≤ k) :
    unitBallVolume k ≤ ENNReal.ofReal ((6/Real.sqrt k)^k) := by
  rw [unitBallVolume, Measure.addHaar_unitClosedBall_eq_addHaar_unitBall]
  exact unit_ball_volume_bound k hk

@[fun_prop] lemma measurable_normalizedDensity (ν : Measure E) [SFinite ν] (k : ℕ) (u : Fin k → E) :
    Measurable (normalizedDensity ν k u) := by
  exact measurable_const.mul ((measurable_lowerDensity ν k).comp
    (((measurable_polarRows u).comp measurable_fst).prodMk measurable_snd))

lemma normalizedDensity_support (ν : Measure E) [IsFiniteMeasure ν] {k : ℕ}
    {u : Fin k → E} (hu : Orthonormal ℝ u) (hs : ν.support ⊆ Metric.closedBall 0 1)
    (X : Fin k → E) (y : Label k) (hy : 1 < ‖y‖) : normalizedDensity ν k u (X,y) = 0 := by
  have h := lowerDensity_eq_zero_of_far ν k (polarRows u X) 0 1 y hs
    (by simpa only [map_zero, sub_zero, mul_one] using (norm_rowMap_le (polarRows_orthonormal hu X)).trans_lt hy)
  simp only [normalizedDensity, h, mul_zero]

lemma normalizedDensity_is_density (ν : Measure E) [IsFiniteMeasure ν] {k : ℕ}
    {u : Fin k → E} (X : Fin k → E)
    (h : ν.map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k))) :
    ((unitBallVolume k)⁻¹ • (volume : Measure (Label k))).withDensity
      (fun y => normalizedDensity ν k u (X,y)) = ν.map (rowMap (polarRows u X)) := by
  rw [withDensity_smul_measure]
  change (unitBallVolume k)⁻¹ • volume.withDensity
    (unitBallVolume k • (fun y => lowerDensity ν k (polarRows u X,y))) = _
  rw [withDensity_smul _ (by fun_prop), smul_smul,
    ENNReal.inv_mul_cancel (unitBallVolume_ne_zero k) (unitBallVolume_ne_top k), one_smul]
  exact lowerDensity_is_density ν k _ h

lemma normalizedMoment_le (ν : Measure E) [IsFiniteMeasure ν] {k : ℕ}
    (hk : k ≤ Module.finrank ℝ E) {u : Fin k → E} (hu : Orthonormal ℝ u) (n : ℕ) :
    (∫⁻ X, ∫⁻ y, normalizedDensity ν k u (X,y)^(n+1) ∂unitBallLaw k
      ∂Measure.pi (fun _ => stdGaussian E)) ≤
      unitBallVolume k ^ n * ∫⁻ A, labelMoment ν k n A ∂frameLaw u := by
  have hpoint (X : Fin k → E) :
      (∫⁻ y, normalizedDensity ν k u (X,y)^(n+1) ∂unitBallLaw k) ≤
        unitBallVolume k ^ n * labelMoment ν k n (polarRows u X) := by
    simp only [unitBallLaw, normalizedDensity, mul_pow, lintegral_smul_measure, smul_eq_mul]
    rw [lintegral_const_mul _ (by fun_prop), ← mul_assoc,
      pow_succ', ← mul_assoc, ENNReal.inv_mul_cancel (unitBallVolume_ne_zero k) (unitBallVolume_ne_top k), one_mul]
    apply mul_le_mul' le_rfl
    have he : labelMoment ν k n (polarRows u X) =
        ∫⁻ y : Label k, lowerDensity ν k (polarRows u X,y)^(n+1) :=
      (PiLp.volume_preserving_toLp (Fin k)).lintegral_comp
        (show Measurable (fun y : Label k => lowerDensity ν k (polarRows u X,y)^(n+1)) by fun_prop)
    rw [he]
    exact setLIntegral_le_lintegral _ _
  apply (lintegral_mono hpoint).trans
  rw [lintegral_const_mul _ (by fun_prop), lintegral_polarRows_eq_frame hk hu _ (by fun_prop)]

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sphereWeightedRestriction_le [Nontrivial E] {h : E → ℝ≥0∞}
    (h1 : ∀ s, h s ≤ 1) (H : Set E) :
    sphereWeightedRestriction h H ≤ NoiselessRegression.ambientSphereLaw := by
  apply Measure.restrict_le_self.trans
  calc
    _ ≤ NoiselessRegression.ambientSphereLaw.withDensity (1 : E → ℝ≥0∞) :=
      withDensity_mono (Filter.Eventually.of_forall h1)
    _ = _ := withDensity_one

lemma sphereWeightedRestriction_finite [Nontrivial E] {h : E → ℝ≥0∞}
    (h1 : ∀ s, h s ≤ 1) (H : Set E) : IsFiniteMeasure (sphereWeightedRestriction h H) :=
  ⟨(Measure.le_iff.mp (sphereWeightedRestriction_le h1 H) Set.univ MeasurableSet.univ).trans_lt (by simp)⟩

lemma sphereWeightedRestriction_support {h : E → ℝ≥0∞} {H : Set E}
    {z : E} {ρ : ℝ} (hH : H ⊆ Metric.closedBall z ρ) :
    (sphereWeightedRestriction h H).support ⊆ Metric.closedBall z ρ :=
  Measure.support_restrict_subset.trans (fun _ hx =>
    (closure_minimal hH Metric.isClosed_closedBall) hx.1)

theorem riesz_deterministic_offsets :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d : ℕ, 16 ≤ d →
      let k := d/8
      let α : ℝ := (d:ℝ)/2
      ∀ h : EuclideanSpace ℝ (Fin d) → ℝ≥0∞, Measurable h → (∀ s, h s ≤ 1) →
      ∀ z : EuclideanSpace ℝ (Fin d), ∀ ρ : ℝ, 0 < ρ →
      ∀ H : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet H → H ⊆ Metric.closedBall z ρ →
      rieszPotential α h < ∞ ∧
      Measurable (lowerDensity (sphereWeightedRestriction h H) k) ∧
      (∀ A : Fin k → EuclideanSpace ℝ (Fin d), LinearIndependent ℝ A →
        volume.withDensity (fun y => lowerDensity (sphereWeightedRestriction h H) k (A,y)) =
          (sphereWeightedRestriction h H).map (rowMap A)) ∧
      (∀ b : Label k, (∫⁻ A, (lowerDensity (sphereWeightedRestriction h H) k (A,rowMap A z+b))^k
          ∂Measure.pi (fun _ => stdGaussian (EuclideanSpace ℝ (Fin d))))^(1/(k:ℝ)) ≤
        ENNReal.ofReal (C^d) * rieszPotential α h * ENNReal.ofReal (ρ^(α-k))) ∧
      (∀ A y, ‖rowMap A‖*ρ < ‖y-rowMap A z‖ →
        lowerDensity (sphereWeightedRestriction h H) k (A,y) = 0) := by
  refine ⟨128,by norm_num,?_⟩
  intro d hd k α h hh h1 z ρ hρ H hH hHz
  let : NeZero d := ⟨by omega⟩
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hkd : k+2 ≤ d := by dsimp [k]; omega
  have hαd : α ≤ d := by dsimp [α]; linarith [Nat.cast_nonneg (α := ℝ) d]
  have hmargin : (k:ℝ)+k ≤ α := by
    have hn : 4*k ≤ d := by dsimp [k]; omega
    have hn' : 4*(k:ℝ) ≤ d := by exact_mod_cast hn
    dsimp [α]; linarith
  have hfinite : rieszPotential α h < ∞ := by
    apply rieszPotential_finite hα (m := d/2+1) _ _ h1
    · have hn : d ≤ 2*(d/2+1) := by omega
      have hn' : (d:ℝ) ≤ 2*((d/2+1:ℕ):ℝ) := by exact_mod_cast hn
      dsimp [α]; linarith
    · simp only [finrank_euclideanSpace_fin]; omega
  let μ := sphereWeightedRestriction h H
  let : IsFiniteMeasure μ := sphereWeightedRestriction_finite h1 H
  have hs : μ.support ⊆ Metric.closedBall z ρ := sphereWeightedRestriction_support hHz
  have hball : AllBallMass μ (rieszPotential α h).toReal α := by
    intro c r hr
    apply (Measure.restrict_le_self _).trans
    apply (rieszPotential_ball_control hα hh c hr).trans_eq
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfinite.ne]
  refine ⟨hfinite,measurable_lowerDensity μ k,?_,?_,?_⟩
  · intro A hA
    apply lowerDensity_is_density
    apply (rowMap_ac_iff _).mpr
    exact ((Measure.absolutelyContinuous_of_le (sphereWeightedRestriction_le h1 H)).map
      (show Measurable (coordinateMap A) by fun_prop)).trans (sphere_fullRank_ac (by simpa using hkd) hA)
  · intro b
    have hb := gaussian_fixed_offset hball ENNReal.toReal_nonneg z hρ hs k k (by omega)
      hmargin (by simpa using hαd) b
    simpa only [finrank_euclideanSpace_fin,ENNReal.ofReal_mul (by positivity : 0 ≤ (128:ℝ)^d),
      ENNReal.ofReal_mul (by positivity : 0 ≤ (128:ℝ)^d*(rieszPotential α h).toReal),
      ENNReal.ofReal_toReal hfinite.ne] using hb
  · intro A y hy
    exact lowerDensity_eq_zero_of_far μ k A z ρ y hs hy

end

theorem all_radii_sphere_moment :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d : ℕ, 16 ≤ d →
      let k := d/4
      let β : ℝ := (d:ℝ)-1-k
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
      Measurable f → (∀ s, f s ≤ 1) →
      ∀ K : ℝ, 0 ≤ K →
      AllBallMass (NoiselessRegression.ambientSphereLaw.withDensity f) K β →
      ∀ z : EuclideanSpace ℝ (Fin d), ∀ R : ℝ, 0 < R →
      ∀ u : Fin k → EuclideanSpace ℝ (Fin d), Orthonormal ℝ u →
      let μ := sphereWeightedRestriction f (Metric.closedBall z R)
      Measurable (coordinateDensity μ k) ∧
      (∀ A : Fin k → EuclideanSpace ℝ (Fin d), Orthonormal ℝ A →
        (volume : Measure (Fin k → ℝ)).withDensity (fun y => coordinateDensity μ k (A,y)) =
          μ.map (coordinateMap A)) ∧
      (∀ A : Fin k → EuclideanSpace ℝ (Fin d), Orthonormal ℝ A →
        ∀ y : Fin k → ℝ, R < ‖WithLp.toLp 2 (y-coordinateMap A z)‖ →
          coordinateDensity μ k (A,y) = 0) ∧
      (∫⁻ A, ∫⁻ y : Fin k → ℝ, coordinateDensity μ k (A,y)^k ∂volume ∂frameLaw u) ^ (1/(k:ℝ)) ≤
        ENNReal.ofReal (C^d*(C*Real.sqrt d)^((k:ℝ)*(1-1/(k:ℝ)))*
          K*R^(β-(k:ℝ)*(1-1/(k:ℝ)))) := by
  obtain ⟨C,hC,h⟩ := integrated_frame_moment
  refine ⟨C,hC,?_⟩
  intro d hd k β f hf hf1 K hK hball z R hR u hu μ
  let : NeZero d := ⟨by omega⟩
  let : IsFiniteMeasure μ := sphereWeightedRestriction_finite hf1 _
  have hk : 4 ≤ k := by dsimp [k]; omega
  have h3k : 3*k ≤ d := by dsimp [k]; omega
  have h3kR : 3*(k:ℝ) ≤ d := by exact_mod_cast h3k
  have hkR : (4:ℝ) ≤ k := by exact_mod_cast hk
  have hβ : 0 < β := by dsimp [β]; linarith
  have hβd : β ≤ d := by dsimp [β]; linarith
  have hm : 1 ≤ β-(k:ℝ)-((k:ℝ)-2) := by dsimp [β]; linarith
  have hs : μ.support ⊆ Metric.closedBall z R := sphereWeightedRestriction_support Subset.rfl
  have hball' : AllBallMass μ K β := fun c r hr => (Measure.restrict_le_self _).trans (hball c r hr)
  have hac (A : Fin k → EuclideanSpace ℝ (Fin d)) (hA : Orthonormal ℝ A) :
      μ.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ)) :=
    ((Measure.absolutelyContinuous_of_le (sphereWeightedRestriction_le hf1 _)).map
      (by fun_prop)).trans (sphere_frame_ac (by simp only [finrank_euclideanSpace_fin]; omega) hA)
  have hframe := h d k k β K R μ z u (by omega) (by omega) (by omega)
    hβ (by exact_mod_cast hβd) hm hK hR hs hball' hu
      (polar_ac_to_frame μ (by simpa only [finrank_euclideanSpace_fin] using (show k ≤ d by omega)) hu
        (Filter.Eventually.of_forall (fun X => (rowMap_ac_iff _).mpr (hac _ (polarRows_orthonormal hu X)))))
  refine ⟨hframe.1,?_,hframe.2.2.1,hframe.2.2.2⟩
  intro A hA
  exact coordinateDensity_is_density μ k A (hac A hA)

lemma normalized_cost (d k n : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) (hdk : d ≤ 32*k)
    (D : ℝ) (hD : 0 < D) :
    unitBallVolume k ^ n *
      ((2 : ℝ≥0∞)^k * ENNReal.ofReal (Real.sqrt (2*d))^(k*n) *
        (ENNReal.ofReal (D^d)^(n+1) * (128 : ℝ≥0∞)^(d*n))) ≤
      ENNReal.ofReal ((16384 * max D 1)^(d*(n+1))) := by
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hdR : (d:ℝ) ≤ 32*k := by exact_mod_cast hdk
  have hroot : Real.sqrt (2*d) ≤ 8*Real.sqrt k := by
    have h1 := Real.sq_sqrt (show (0:ℝ) ≤ 2*d by positivity)
    have h2 := Real.sq_sqrt hkR.le
    have h3 := Real.sqrt_nonneg (2*(d:ℝ))
    have h4 := Real.sqrt_pos.mpr hkR
    nlinarith
  have hc : 0 ≤ 6/Real.sqrt k := by positivity
  have hcs : 6/Real.sqrt k * Real.sqrt (2*d) ≤ 48 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (Real.sqrt_pos.mpr hkR)]
    nlinarith
  have hvol : unitBallVolume k ^ n * ENNReal.ofReal (Real.sqrt (2*d))^(k*n) ≤
      (48 : ℝ≥0∞)^(k*n) := by
    calc
      _ ≤ ENNReal.ofReal ((6/Real.sqrt k)^k)^n * ENNReal.ofReal (Real.sqrt (2*d))^(k*n) :=
        mul_le_mul' (pow_le_pow_left' (unitBallVolume_bound k hk) n) le_rfl
      _ = ENNReal.ofReal (6/Real.sqrt k * Real.sqrt (2*d))^(k*n) := by
        rw [ENNReal.ofReal_pow hc, ← pow_mul, ENNReal.ofReal_mul hc, mul_pow]
      _ ≤ (48 : ℝ≥0∞)^(k*n) := pow_le_pow_left' (by exact_mod_cast ENNReal.ofReal_le_ofReal hcs) _
  have h2 : (2 : ℝ≥0∞)^k ≤ (2 : ℝ≥0∞)^(d*(n+1)) :=
    pow_le_pow_right₀ (by norm_num) (by nlinarith)
  have h48 : (48 : ℝ≥0∞)^(k*n) ≤ (64 : ℝ≥0∞)^(d*(n+1)) :=
    (pow_le_pow_left' (by norm_num : (48:ℝ≥0∞) ≤ 64) _).trans
      (pow_le_pow_right₀ (by norm_num) (by nlinarith))
  have h128 : (128 : ℝ≥0∞)^(d*n) ≤ (128 : ℝ≥0∞)^(d*(n+1)) :=
    pow_le_pow_right₀ (by norm_num) (by nlinarith)
  have hDD : ENNReal.ofReal (D^d)^(n+1) ≤ ENNReal.ofReal (max D 1)^(d*(n+1)) := by
    rw [ENNReal.ofReal_pow hD.le, ← pow_mul]
    exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _
  calc
    _ = (2 : ℝ≥0∞)^k *
        (unitBallVolume k ^ n * ENNReal.ofReal (Real.sqrt (2*d))^(k*n)) *
        ENNReal.ofReal (D^d)^(n+1) * (128 : ℝ≥0∞)^(d*n) := by ring
    _ ≤ (2 : ℝ≥0∞)^(d*(n+1)) * (64 : ℝ≥0∞)^(d*(n+1)) *
        ENNReal.ofReal (max D 1)^(d*(n+1)) * (128 : ℝ≥0∞)^(d*(n+1)) :=
      mul_le_mul' (mul_le_mul' (mul_le_mul' h2 (hvol.trans h48)) hDD) h128
    _ = ENNReal.ofReal ((16384 * max D 1)^(d*(n+1))) := by
      rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by norm_num)]
      norm_num only [ENNReal.ofReal_ofNat]
      rw [← mul_pow, ← mul_pow, ← mul_pow]
      congr 1
      ring

theorem normalized_unitBall_moment (D : ℝ) (hD : 0 < D) :
    ∃ C_D : ℝ, 0 < C_D ∧ ∀ d : ℕ, 32 ≤ d →
      let k := d/16
      let lam : ℝ := ((d:ℝ)-1)/2
      ∀ (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
        (u : Fin k → EuclideanSpace ℝ (Fin d)),
        ν Set.univ ≤ 1 → ν.support ⊆ Metric.closedBall 0 1 →
        AllBallMass ν (D^d) lam → Orthonormal ℝ u →
        (∀ᵐ X ∂Measure.pi (fun _ : Fin k => stdGaussian (EuclideanSpace ℝ (Fin d))),
          ν.map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k))) →
        Measurable (normalizedDensity ν k u) ∧
        (∀ᵐ X ∂Measure.pi (fun _ : Fin k => stdGaussian (EuclideanSpace ℝ (Fin d))),
          ((unitBallVolume k)⁻¹ • (volume : Measure (Label k))).withDensity
            (fun y => normalizedDensity ν k u (X,y)) = ν.map (rowMap (polarRows u X))) ∧
        (∀ X y, 1 < ‖y‖ → normalizedDensity ν k u (X,y) = 0) ∧
        (∫⁻ X, ∫⁻ y, normalizedDensity ν k u (X,y)^k ∂unitBallLaw k
          ∂Measure.pi (fun _ => stdGaussian (EuclideanSpace ℝ (Fin d)))) ≤
          ENNReal.ofReal (Real.exp (C_D*d*k)) := by
  refine ⟨Real.log (16384*max D 1), Real.log_pos (by nlinarith [le_max_right D 1]), ?_⟩
  intro d hd k lam ν _ u hmass hs hν hu hac
  have hk2 : 2 ≤ k := by dsimp [k]; omega
  have hk : 1 ≤ k := by omega
  have hkd : k ≤ d := by dsimp [k]; omega
  have hdk : d ≤ 32*k := by dsimp [k]; omega
  have h16 : 16*k ≤ d := by dsimp [k]; omega
  have hnc : k-1+1 = k := by omega
  have hncR : ((k-1:ℕ):ℝ)+1 = k := by exact_mod_cast hnc
  have h16R : 16*(k:ℝ) ≤ d := by exact_mod_cast h16
  have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk2
  have hdR : (32:ℝ) ≤ d := by exact_mod_cast hd
  have hmargin : ((k-1:ℕ):ℝ)+k ≤ lam := by dsimp [lam]; linarith
  have hlamd : lam ≤ (d:ℝ) := by dsimp [lam]; linarith
  have hac' := polar_ac_to_frame ν (by simpa using hkd) hu hac
  refine ⟨measurable_normalizedDensity ν k u, ?_, ?_, ?_⟩
  · filter_upwards [hac] with X hX
    exact normalizedDensity_is_density ν X hX
  · exact normalizedDensity_support ν hu hs
  · have hframe := frame_moment_scaled hν (pow_pos hD d) (0 : EuclideanSpace ℝ (Fin d))
      (by norm_num : (0:ℝ) < 1) hs k (k-1) hmargin
      (by simpa using (show 1 ≤ d by omega)) (by simpa using hlamd) (by simpa using hkd) u hu hac'
    simp only [Real.one_rpow, mul_one, one_pow, ENNReal.ofReal_one, finrank_euclideanSpace_fin] at hframe
    have hnorm := (normalizedMoment_le ν (by simpa using hkd) hu (k-1)).trans
      (mul_le_mul' le_rfl hframe)
    have hcost := normalized_cost d k (k-1) hk hkd hdk D hD
    have hres := hnorm.trans hcost
    rw [hnc] at hres
    have he : (16384*max D 1)^(d*k) = Real.exp (Real.log (16384*max D 1)*d*k) := by
      rw [show Real.log (16384*max D 1)*(d:ℝ)*k = ((d*k:ℕ):ℝ)*Real.log (16384*max D 1) by push_cast; ring,
        Real.exp_nat_mul, Real.exp_log (by positivity)]
    simpa only [he] using hres

end ProjectionMoments

end

end OAI
