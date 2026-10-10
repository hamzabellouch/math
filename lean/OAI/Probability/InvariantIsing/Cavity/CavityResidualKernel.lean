import OAI.Probability.InvariantIsing.Cavity.CavityResidualFinite
import OAI.Probability.InvariantIsing.Cavity.CavityQuadraticReplica

namespace OAI

/-! The ordinary residual, sampled independently for each replica, becomes
independent of the tilted leaf after its centered Gaussian innovation map.
It is not an additional level of the Poisson tree. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

private lemma cavity_exp_mass_eq_scaled_tilt {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (F : X → ℝ)
    (hF : Measurable F) (hI : Integrable (fun x => Real.exp (F x)) μ) :
    μ.withDensity (fun x => ENNReal.ofReal (Real.exp (F x))) =
      ENNReal.ofReal (∫ x, Real.exp (F x) ∂μ) • μ.tilted F := by
  have hZ : 0 < ∫ x, Real.exp (F x) ∂μ := integral_exp_pos hI
  rw [Measure.tilted, ← withDensity_smul _ ((hF.exp.div_const _).ennreal_ofReal)]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.ofReal_div_of_pos hZ]
  symm
  calc
    _ = (ENNReal.ofReal (∫ x, Real.exp (F x) ∂μ) *
        (ENNReal.ofReal (∫ x, Real.exp (F x) ∂μ))⁻¹) *
        ENNReal.ofReal (Real.exp (F x)) := by rw [div_eq_mul_inv]; ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hZ).ne'
      ENNReal.ofReal_ne_top, one_mul]

private lemma cavity_weighted_product_transport {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure X) (μ : Measure Y) (κ : Measure Z) [SFinite ν] [SFinite μ] [SFinite κ]
    (w : X × Y → ℝ≥0∞) (a : X → ℝ≥0∞) (T : X × Y → Z)
    (hw : Measurable w) (ha : Measurable a) (hT : Measurable T)
    (hlaw : ∀ x, (μ.withDensity (fun y => w (x, y))).map (fun y => T (x, y)) = a x • κ) :
    ((ν.prod μ).withDensity w).map (fun p => (p.1, T p)) =
      (ν.withDensity a).prod κ := by
  have hmap : Measurable (fun p : X × Y => (p.1, T p)) := measurable_fst.prodMk hT
  apply Measure.ext_of_lintegral
  intro f hf
  have hfc : Measurable (fun p : X × Y => f (p.1, T p)) := hf.comp hmap
  rw [lintegral_map hf hmap, lintegral_withDensity_eq_lintegral_mul _ hw hfc]
  change (∫⁻ p, w p * f (p.1, T p) ∂ν.prod μ) = _
  rw [lintegral_prod _ (show AEMeasurable (fun p : X × Y => w p * f (p.1, T p)) _ from
      (hw.mul hfc).aemeasurable), lintegral_prod _ hf.aemeasurable]
  have hx (x : X) : (∫⁻ y, w (x, y) * f (x, T (x, y)) ∂μ) =
      a x * ∫⁻ z, f (x, z) ∂κ := by
    have hfx : Measurable (fun z => f (x, z)) :=
      hf.comp (measurable_const.prodMk measurable_id)
    have hTx : Measurable (fun y => T (x, y)) :=
      hT.comp (measurable_const.prodMk measurable_id)
    calc
      _ = ∫⁻ y, f (x, T (x, y)) ∂μ.withDensity (fun y => w (x, y)) :=
        (lintegral_withDensity_eq_lintegral_mul _
          (show Measurable (fun y => w (x, y)) from
            hw.comp (measurable_const.prodMk measurable_id))
          (show Measurable (fun y => f (x, T (x, y))) from hfx.comp hTx)).symm
      _ = ∫⁻ z, f (x, z) ∂(μ.withDensity (fun y => w (x, y))).map (fun y => T (x, y)) :=
        (lintegral_map hfx hTx).symm
      _ = _ := by rw [hlaw x, lintegral_smul_measure]; rfl
  simp_rw [hx]
  exact (lintegral_withDensity_eq_lintegral_mul _ ha hf.lintegral_prod_right').symm

private lemma cavity_normalize_prod_right {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [Nonempty X] [Nonempty Y]
    (ν : Measure X) (κ : Measure Y) [SFinite ν] [IsProbabilityMeasure κ]
    (hν : 0 < ν Set.univ ∧ ν Set.univ < ∞) :
    normalizeMass (ν.prod κ) = (normalizeMass ν).prod κ := by
  have hm : ν.prod κ Set.univ = ν Set.univ := by
    rw [← Set.univ_prod_univ, Measure.prod_prod,
      show κ Set.univ = 1 from measure_univ, mul_one]
  rw [normalizeMass, hm, ite_eq_left hν, normalizeMass, ite_eq_left hν,
    Measure.prod_smul_left]

/-- The full leaf/residual Gibbs law factors after centering the ordinary
residual. The first factor is the backward-quadratic leaf tilt, while the
second is a Gaussian with covariance `(I-HK)⁻¹H`. -/
theorem cavity_residual_joint_kernel {X : Type*} [MeasurableSpace X] [Nonempty X]
    {d : ℕ} (ν : Measure X) [IsProbabilityMeasure ν]
    (y : X → EuclideanSpace ℝ (Fin d)) (hy : Measurable y)
    (K H : Matrix (Fin d) (Fin d) ℝ) (hK : K.transpose = K) (hH : H.PosSemidef)
    (hdet : IsUnit (1 - H * K).det)
    (hQ : (cavityFactorPrecision K (CFC.sqrt H)).PosDef)
    (hI : Integrable (fun x => Real.exp
      (⟪y x, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K H) (y x)⟫ / 2)) ν) :
    (normalizeMass ((ν.prod (multivariateGaussian 0 H)).withDensity
      (fun p : X × EuclideanSpace ℝ (Fin d) => ENNReal.ofReal
        (Real.exp (⟪y p.1 + p.2, Matrix.toEuclideanCLM (𝕜 := ℝ) K (y p.1 + p.2)⟫ / 2))))).map
        (fun p => (p.1, y p.1 + p.2 -
          Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H * K)⁻¹ (y p.1))) =
      (ν.tilted (fun x =>
        ⟪y x, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K H) (y x)⟫ / 2)).prod
          (multivariateGaussian 0 (cavityResolvent K H)) := by
  let μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) H
  let κ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (cavityResolvent K H)
  let F : X → ℝ := fun x =>
    ⟪y x, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K H) (y x)⟫ / 2
  let c : ℝ := -Real.log (1 - H * K).det / 2
  let Q : X × EuclideanSpace ℝ (Fin d) → ℝ := fun p =>
    ⟪y p.1 + p.2, Matrix.toEuclideanCLM (𝕜 := ℝ) K (y p.1 + p.2)⟫ / 2
  let T : X × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun p =>
    y p.1 + p.2 - Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H * K)⁻¹ (y p.1)
  let a : X → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (c + F x))
  let η := ν.withDensity a
  let M := (ν.prod μ).withDensity (fun p => ENNReal.ofReal (Real.exp (Q p)))
  have hFm : Measurable F := by dsimp [F]; fun_prop
  have hQm : Measurable Q := by dsimp [Q]; fun_prop
  have hTm : Measurable T := by dsimp [T]; fun_prop
  have ham : Measurable a := ((measurable_const.add hFm).exp).ennreal_ofReal
  have hKh : K.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hK
  have hlaw (x : X) :
      (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (Q (x, z))))).map (fun z => T (x, z)) =
        a x • κ := by
    have hi := cavity_multivariate_gaussian_integrable K H hKh hQ (y x)
    have he := cavity_exp_mass_eq_scaled_tilt μ (fun z => Q (x, z))
      (hQm.comp (measurable_const.prodMk measurable_id)) hi
    have hTx : Measurable (fun z => T (x, z)) :=
      hTm.comp (measurable_const.prodMk measurable_id)
    rw [he, Measure.map_smul _ hTx.aemeasurable]
    have ht := cavity_residual_innovation_law K H hK hH hdet hQ (y x)
    have hz := cavity_residual_integral K H hKh hH hQ (y x)
    have hf : (fun z : EuclideanSpace ℝ (Fin d) => (1 / 2 : ℝ) *
        ⟪y x + z, Matrix.toEuclideanCLM (𝕜 := ℝ) K (y x + z)⟫) =
        (fun z => Q (x, z)) := by
      funext z
      dsimp [Q]
      ring
    rw [hf] at ht
    change (μ.tilted (fun z => Q (x, z))).map (fun z => T (x, z)) = κ at ht
    rw [ht]
    congr 1
    exact congrArg ENNReal.ofReal hz
  have htransport : M.map (fun p => (p.1, T p)) = η.prod κ :=
    cavity_weighted_product_transport ν μ κ _ a T hQm.exp.ennreal_ofReal ham hTm hlaw
  have hη : η = ENNReal.ofReal (Real.exp c) •
      ν.withDensity (fun x => ENNReal.ofReal (Real.exp (F x))) := by
    dsimp only [η]
    rw [← withDensity_smul _ hFm.exp.ennreal_ofReal]
    congr 1
    funext x
    simp only [a, Real.exp_add, Pi.smul_apply, smul_eq_mul,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hbase : 0 < (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (F x)))) Set.univ ∧
      (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (F x)))) Set.univ < ∞ := by
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ (fun _ => (Real.exp_pos _).le))]
    exact ⟨ENNReal.ofReal_pos.mpr (integral_exp_pos hI), ENNReal.ofReal_lt_top⟩
  have hηmass : 0 < η Set.univ ∧ η Set.univ < ∞ := by
    rw [hη, Measure.smul_apply, smul_eq_mul]
    exact ⟨ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.exp_pos c)).ne' hbase.1.ne',
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbase.2⟩
  have hm : M Set.univ = η Set.univ := by
    have he := congrArg (fun ρ : Measure (X × EuclideanSpace ℝ (Fin d)) => ρ Set.univ) htransport
    rw [Measure.map_apply (measurable_fst.prodMk hTm) MeasurableSet.univ,
      Set.preimage_univ] at he
    have hprod : (η.prod κ) Set.univ = η Set.univ := by
      rw [← Set.univ_prod_univ, Measure.prod_prod,
        show κ Set.univ = 1 from measure_univ, mul_one]
    rw [hprod] at he
    exact he
  change (normalizeMass M).map (fun p => (p.1, T p)) = (ν.tilted F).prod κ
  rw [normalizeMass_map M (measurable_fst.prodMk hTm) (hm ▸ hηmass), htransport,
    cavity_normalize_prod_right η κ hηmass, hη,
    normalizeMass_smul _ ⟨ENNReal.ofReal_pos.mpr (Real.exp_pos c), ENNReal.ofReal_lt_top⟩ hbase,
    normalizeMass_exp ν F hFm hI]

end InvariantIsing

end

end OAI
