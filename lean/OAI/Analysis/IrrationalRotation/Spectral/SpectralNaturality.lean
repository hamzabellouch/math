import OAI.Analysis.IrrationalRotation.Spectral.Spectral

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal CStarAlgebra

namespace Invariant233

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma regularizedNormSquare_spectrum_pos (a : A) (ε : ℝ) (hε : 0 < ε) :
    ∀ x ∈ spectrum ℝ (star a * a + ε • (1 : A)), 0 < x := by
  intro x hx
  rw [← Algebra.algebraMap_eq_smul_one, ← spectrum.add_singleton_eq] at hx
  obtain ⟨y, hy, t, ht, rfl⟩ := Set.mem_add.mp hx
  have ht' : t = ε := Set.mem_singleton_iff.mp ht
  subst t
  linarith [spectrum_star_mul_self_nonneg y hy]

lemma regularizedLog_map (φ : A →⋆ₐ[ℂ] B) (a : A) (ε : ℝ) (hε : 0 < ε) :
    φ (CFC.log (star a * a + ε • (1 : A))) =
      CFC.log (star (φ a) * φ a + ε • (1 : B)) := by
  have hp := regularizedNormSquare_spectrum_pos a ε hε
  have hc : ContinuousOn Real.log (spectrum ℝ (star a * a + ε • (1 : A))) := by
    apply Real.continuousOn_log.mono
    intro x hx
    exact ne_of_gt (hp x hx)
  have hs : IsSelfAdjoint (star a * a + ε • (1 : A)) := by
    simp [IsSelfAdjoint]
  have hφs : IsSelfAdjoint (φ (star a * a + ε • (1 : A))) := by
    change star (φ _) = φ _
    rw [← map_star, hs.star_eq]
  have hsmul : φ (ε • (1 : A)) = ε • (1 : B) := by
    calc
      φ (ε • (1 : A)) = ε • φ 1 := φ.toAlgHom.map_smul_of_tower ε 1
      _ = ε • (1 : B) := by rw [map_one]
  rw [CFC.log, φ.map_cfc Real.log _ hc (by fun_prop) hs hφs]
  simp only [map_add, map_mul, map_star, hsmul, CFC.log]

theorem fugledeKadisonDeterminant_map (φ : A →⋆ₐ[ℂ] B)
    (τA : TracialState A) (τB : TracialState B)
    (hτ : ∀ a, τB (φ a) = τA a) (a : A) :
    fugledeKadisonDeterminant τB (φ a) = fugledeKadisonDeterminant τA a := by
  unfold fugledeKadisonDeterminant
  apply iInf_congr
  intro ε
  rw [← regularizedLog_map φ a ε.val ε.property, hτ]

lemma regularizedLog_complex (z : ℂ) (ε : ℝ) :
    CFC.log (star z * z + ε • (1 : ℂ)) =
      (Real.log (‖z‖ ^ 2 + ε) : ℂ) := by
  have h : star z * z + ε • (1 : ℂ) =
      algebraMap ℝ ℂ (‖z‖ ^ 2 + ε) := by
    simp only [Complex.star_def, Complex.conj_mul', Complex.real_smul, mul_one,
      Complex.coe_algebraMap, Complex.ofReal_add, Complex.ofReal_pow]
  rw [h, CFC.log_algebraMap]
  rfl

theorem fugledeKadisonDeterminant_continuous_representation
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    (μ : Measure X) (π : C(X, ℂ) →⋆ₐ[ℂ] A) (τ : TracialState A)
    (hτ : ∀ g : C(X, ℂ), τ (π g) = ∫ x, g x ∂μ) (f : C(X, ℂ)) :
    fugledeKadisonDeterminant τ (π f) =
      ⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
        (Real.exp ((∫ x, Real.log (‖f x‖ ^ 2 + ε.val) ∂μ) / 2)) := by
  let : NormedAlgebra ℝ C(X, ℂ) := NormedAlgebra.restrictScalars ℝ ℂ C(X, ℂ)
  unfold fugledeKadisonDeterminant
  apply iInf_congr
  intro ε
  rw [← regularizedLog_map π f ε.val ε.property, hτ]
  have hpoint : ∀ x, (CFC.log (star f * f + ε.val • (1 : C(X, ℂ)))) x =
      (Real.log (‖f x‖ ^ 2 + ε.val) : ℂ) := by
    intro x
    have h := regularizedLog_map (ContinuousMap.evalStarAlgHom ℂ ℂ x) f ε.val ε.property
    simpa only [ContinuousMap.evalStarAlgHom_apply] using
      h.trans (regularizedLog_complex (f x) ε.val)
  simp_rw [hpoint]
  rw [integral_complex_ofReal]
  rfl

theorem TracialState.map_complex (τ : TracialState A) (z : ℂ) :
    τ (algebraMap ℂ A z) = z := by
  rw [Algebra.algebraMap_eq_smul_one]
  change τ.toContinuousLinearMap (z • 1) = z
  rw [map_smul, τ.map_one, smul_eq_mul, mul_one]

theorem fugledeKadisonDeterminant_scalar (τ : TracialState A) (z : ℂ) :
    fugledeKadisonDeterminant τ (algebraMap ℂ A z) = ENNReal.ofReal ‖z‖ := by
  unfold fugledeKadisonDeterminant
  have h : ∀ ε : {r : ℝ // 0 < r},
      (τ (CFC.log (star (algebraMap ℂ A z) * algebraMap ℂ A z + ε.val • (1 : A)))).re =
        Real.log (‖z‖ ^ 2 + ε.val) := by
    intro ε
    have hmap := regularizedLog_map (StarAlgHom.ofId ℂ A) z ε.val ε.property
    simp only [StarAlgHom.ofId_apply] at hmap
    rw [← hmap, regularizedLog_complex, TracialState.map_complex]
    rfl
  simp_rw [h]
  have hsqrt : ∀ ε : {r : ℝ // 0 < r},
      Real.exp (Real.log (‖z‖ ^ 2 + ε.val) / 2) = Real.sqrt (‖z‖ ^ 2 + ε.val) := by
    intro ε
    exact exp_half_log_eq_sqrt (by nlinarith [ε.property, sq_nonneg ‖z‖])
  simp_rw [hsqrt]
  exact iInf_sqrt_sq_add_pos _ (norm_nonneg _)

theorem isBrownMeasure_scalar (τ : TracialState A) (c : ℂ) :
    IsBrownMeasure τ (algebraMap ℂ A c) (Measure.dirac c) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · have hs : (Measure.dirac c).support ⊆ ({c} : Set ℂ) :=
      Measure.support_subset_of_isClosed isClosed_singleton (by simp)
    exact isCompact_singleton.of_isClosed_subset Measure.isClosed_support hs
  · intro z
    rw [← map_sub, fugledeKadisonDeterminant_scalar, logarithmicPotentialDeterminant_dirac]

end Invariant233

end

end OAI
