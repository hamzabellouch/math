import Mathlib
import OAI.Geometry.CAT0Fillings.Geometry.Polarization
import OAI.Geometry.CAT0Fillings.Geometry.Determinant
import OAI.Geometry.CAT0Fillings.Bubble.Euclidean

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal MatrixOrder

namespace CAT0Fillings

lemma exists_hilbert_norm_equiv {k : ℕ} (p : Seminorm ℝ (Euc k))
    (hp : ∀ v, p v = 0 ↔ v = 0)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2) :
    ∃ e : Euc k ≃L[ℝ] Euc k, (∀ v, ‖e v‖ = p v) ∧
      |LinearMap.det e.toLinearEquiv.toLinearMap| =
        Real.sqrt (polarizationMatrix p (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det := by
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let Q := polarizationMatrix p b
  have hQ : Q.PosDef := polarizationMatrix_posDef b p hp hpara
  let L : Euc k →ₗ[ℝ] Euc k := Matrix.toEuclideanLin (CFC.sqrt Q)
  have hdet : LinearMap.det L = Real.sqrt Q.det := by
    rw [show L = Matrix.toLin b b (CFC.sqrt Q) from rfl,LinearMap.det_toLin]
    simpa only [RCLike.sqrt_real] using hQ.posSemidef.det_sqrt
  have hdet0 : LinearMap.det L ≠ 0 := by rw [hdet]; exact (Real.sqrt_pos.mpr hQ.det_pos).ne'
  let e := (L.equivOfDetNeZero hdet0).toContinuousLinearEquiv
  refine ⟨e,?_,?_⟩
  · intro v
    have hnorm : ‖e v‖^2 = p v^2 := by
      rw [←real_inner_self_eq_norm_sq]
      change inner ℝ (L v) (L v) = _
      simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial]
      change (CFC.sqrt Q).mulVec (WithLp.ofLp v) ⬝ᵥ
        (CFC.sqrt Q).mulVec (WithLp.ofLp v) = p v^2
      rw [←dot_mulVec_sqrt Q hQ.posSemidef]
      have hrepr : b.repr v = WithLp.ofLp v := by ext j; simp [b]
      rw [←hrepr]
      exact polarizationMatrix_quadratic b p hp hpara v
    nlinarith [norm_nonneg (e v),apply_nonneg p v]
  · change |LinearMap.det L| = _
    rw [hdet,abs_of_nonneg (Real.sqrt_nonneg _)]

lemma normalized_linear_image_push {E X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace X]
    (ν : Measure E) [ν.IsAddHaarMeasure] (e : E ≃L[ℝ] E)
    {s : Set E} (hs : MeasurableSet s) {f : E → X} (hf : Measurable f) :
    Measure.map (f ∘ e.symm) (ν.restrict (e '' s)) =
      ENNReal.ofReal |LinearMap.det e.toLinearEquiv.toLinearMap| •
        Measure.map f (ν.restrict s) := by
  have hs' : MeasurableSet (e '' s) := e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hs
  let J := ENNReal.ofReal |LinearMap.det e.toLinearEquiv.toLinearMap|
  have hmap : Measure.map e.symm ν = J • ν := by
    have hh := Measure.map_linearMap_addHaar_eq_smul_addHaar ν
      (LinearEquiv.isUnit_det' e.symm.toLinearEquiv).ne_zero
    convert hh using 1
    change J • ν = ENNReal.ofReal |(LinearMap.det e.toLinearEquiv.symm.toLinearMap)⁻¹| • ν
    rw [LinearEquiv.det_coe_symm,inv_inv]
  have heq : Measure.map e.symm (ν.restrict (e '' s)) = J • ν.restrict s := by
    rw [show e '' s = e.symm ⁻¹' s by
      ext x; exact e.toEquiv.image_eq_preimage_symm s ▸ Iff.rfl,
      ←Measure.restrict_map e.symm.continuous.measurable hs,hmap,Measure.restrict_smul]
  rw [←Measure.map_map hf e.symm.continuous.measurable,heq,
    Measure.map_smul _ hf.aemeasurable]

end CAT0Fillings
end

section
open Set Filter MeasureTheory Matrix
open scoped Topology

namespace CAT0Fillings.TangentDensity

lemma integral_comp_linear_equiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] E) (f : E → F) :
    (∫ x, f (e x) ∂μ) = |LinearMap.det e.toLinearEquiv.toLinearMap|⁻¹ • (∫ x, f x ∂μ) := by
  have hi := e.toHomeomorph.measurableEmbedding.integral_map (μ := μ) f
  change (∫ x, f x ∂Measure.map e μ) = (∫ x, f (e x) ∂μ) at hi
  rw [←hi]
  have he := Measure.map_linearMap_addHaar_eq_smul_addHaar μ
    (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  change Measure.map e μ = _ at he
  rw [he,integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _),abs_inv]

lemma quadratic_bubble_mass {n : ℕ} (hn : 2 < n) (d : Seminorm ℝ (Euc n))
    (hd : ∀ h, d h = 0 ↔ h = 0)
    (hpara : ∀ h h', d (h+h')^2+d (h-h')^2 = 2*d h^2+2*d h'^2)
    {a : ℝ} (ha : 0 < a) :
    a^n * Real.sqrt (polarizationMatrix d (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).det *
      (∫ h : Euc n, (1+a^2*(d h)^2)^(-(n:ℝ))) = sphereArea n/(2:ℝ)^n := by
  obtain ⟨e,he,hdet⟩ := exists_hilbert_norm_equiv d hd hpara
  have hJ : 0 < Real.sqrt (polarizationMatrix d (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).det :=
    Real.sqrt_pos.mpr (polarizationMatrix_posDef _ _ hd hpara).det_pos
  have hnorm (h : Euc n) : ‖a • e h‖^2 = a^2*(d h)^2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ha,he,mul_pow]
  have hi : (∫ h : Euc n, (1+a^2*(d h)^2)^(-(n:ℝ))) =
      |LinearMap.det e.toLinearEquiv.toLinearMap|⁻¹ *
      (a^n)⁻¹ * (sphereArea n/(2:ℝ)^n) := by
    simp_rw [←hnorm]
    rw [integral_comp_linear_equiv volume e (fun x => (1+‖a • x‖^2)^(-(n:ℝ))),
      Measure.integral_comp_smul_of_nonneg volume (fun x : Euc n => (1+‖x‖^2)^(-(n:ℝ))) a (hR := ha.le)]
    simp only [finrank_euclideanSpace,Fintype.card_fin,smul_eq_mul,
      RadialSobolev.integral_euclidean_bubble hn]
    ring
  rw [hi,hdet]
  field_simp
end CAT0Fillings.TangentDensity
end

section
open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal

namespace CAT0Fillings.TangentDensity

lemma integral_tangent_density {n : ℕ} (hn : 2 < n) (d : Seminorm ℝ (Euc n))
    (hd : ∀ h, d h = 0 ↔ h = 0)
    (hpara : ∀ h h', d (h+h')^2+d (h-h')^2 = 2*d h^2+2*d h'^2)
    {u β : ℝ} (hu : 0 < u) (θ : ℤ) :
    (∫ h : Euc n, u^(2*(n:ℝ)*β)*
      (|(θ:ℝ)| *Real.sqrt (polarizationMatrix d (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).det) /
      (1+(u^β)^2*(d h)^2*u^(2*β))^n) = |(θ:ℝ)| *(sphereArea n/(2:ℝ)^n) := by
  let J := Real.sqrt (polarizationMatrix d (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).det
  have ha : 0 < u^(2*β) := Real.rpow_pos_of_pos hu _
  have hm : (u^β)^2 = u^(2*β) := by
    rw [←Real.rpow_mul_natCast hu.le]; congr 1; ring
  have hpow : (u^(2*β))^n = u^(2*(n:ℝ)*β) := by
    rw [←Real.rpow_mul_natCast hu.le]; congr 1; ring
  have he (h : Euc n) : 1+(u^β)^2*(d h)^2*u^(2*β) = 1+(u^(2*β))^2*(d h)^2 := by
    rw [hm]; ring
  simp_rw [he]
  have hi : (∫ h : Euc n, u^(2*(n:ℝ)*β)*(|(θ:ℝ)| *J) /
      (1+(u^(2*β))^2*(d h)^2)^n) =
      u^(2*(n:ℝ)*β)*(|(θ:ℝ)| *J)*(∫ h : Euc n, (1+(u^(2*β))^2*(d h)^2)^(-(n:ℝ))) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with h
    simp only [Real.rpow_neg_natCast, _root_.zpow_neg,zpow_natCast,div_eq_mul_inv]
  change _ = |(θ:ℝ)| *(sphereArea n/(2:ℝ)^n)
  rw [hi]
  have hq := quadratic_bubble_mass hn d hd hpara ha
  rw [hpow] at hq
  change u^(2*(n:ℝ)*β)*J*(∫ h : Euc n, (1+(u^(2*β))^2*(d h)^2)^(-(n:ℝ))) = _ at hq
  calc
    _ = |(θ:ℝ)| *(u^(2*(n:ℝ)*β)*J*(∫ h : Euc n, (1+(u^(2*β))^2*(d h)^2)^(-(n:ℝ)))) := by ring
    _ = _ := by rw [hq]

lemma tangent_density_lower_bound {n : ℕ} (hn : 2 < n) (d : Seminorm ℝ (Euc n))
    (hd : ∀ h, d h = 0 ↔ h = 0)
    (hpara : ∀ h h', d (h+h')^2+d (h-h')^2 = 2*d h^2+2*d h'^2)
    {u β : ℝ} (hu : 0 < u) {θ : ℤ} (hθ : θ ≠ 0) :
    sphereArea n/(2:ℝ)^n ≤ (∫ h : Euc n, u^(2*(n:ℝ)*β)*
      (|(θ:ℝ)| *Real.sqrt (polarizationMatrix d (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).det) /
      (1+(u^β)^2*(d h)^2*u^(2*β))^n) := by
  rw [integral_tangent_density hn d hd hpara hu θ]
  have hθ1 : (1:ℝ) ≤ |(θ:ℝ)| := by exact_mod_cast (Int.one_le_abs hθ)
  apply le_mul_of_one_le_left
  · unfold sphereArea
    exact div_nonneg (mul_nonneg (by positivity) (by unfold omega; exact ENNReal.toReal_nonneg)) (by positivity)
  · exact hθ1
end CAT0Fillings.TangentDensity
end

end OAI
