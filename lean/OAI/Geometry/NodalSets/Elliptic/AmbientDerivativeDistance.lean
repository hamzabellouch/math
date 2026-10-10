import Mathlib.Geometry.Manifold.Riemannian.Basic

namespace OAI

namespace Yau.Geometry
open Bundle Manifold Set MeasureTheory
open scoped ENNReal NNReal ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma map_edist_le_pathELength (f : M → F) (hf : ContMDiff I 𝓘(ℝ,F) 1 f)
    (C : ℝ≥0)
    (hC : ∀ x, ENorm.enorm (E := TangentSpace I x →L[ℝ] F) (mfderiv I 𝓘(ℝ,F) f x) ≤ C)
    (γ : ℝ → M) (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc (0:ℝ) 1)) :
    edist (f (γ 0)) (f (γ 1)) ≤ C * pathELength I γ 0 1 := by
  have hs : ContDiffOn ℝ 1 (f ∘ γ) (Icc (0:ℝ) 1) :=
    contMDiffOn_iff_contDiffOn.mp (hf.comp_contMDiffOn hγ)
  calc
    edist (f (γ 0)) (f (γ 1)) = ‖(f ∘ γ) 1 - (f ∘ γ) 0‖ₑ := by
      rw [edist_comm, edist_eq_enorm_sub]; rfl
    _ ≤ ∫⁻ t in Icc (0:ℝ) 1, ‖derivWithin (f ∘ γ) (Icc (0:ℝ) 1) t‖ₑ :=
      enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hs zero_le_one
    _ = ∫⁻ t in Icc (0:ℝ) 1, ‖mfderivWithin 𝓘(ℝ) 𝓘(ℝ,F) (f ∘ γ)
          (Icc (0:ℝ) 1) t 1‖ₑ := by
      simp_rw [mfderivWithin_eq_fderivWithin, ← fderivWithin_derivWithin]; rfl
    _ ≤ ∫⁻ t in Icc (0:ℝ) 1, C * ‖mfderivWithin 𝓘(ℝ) I γ (Icc (0:ℝ) 1) t 1‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      rw [mfderiv_comp_mfderivWithin t (hf.mdifferentiable one_ne_zero (γ t))
        (hγ.mdifferentiableOn one_ne_zero t ht)
        (by rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]; exact uniqueDiffOn_Icc zero_lt_one t ht)]
      apply (ContinuousLinearMap.le_opENorm (mfderiv I 𝓘(ℝ,F) f (γ t))
        (mfderivWithin 𝓘(ℝ) I γ (Icc (0:ℝ) 1) t 1)).trans
      gcongr
      exact hC (γ t)
    _ = C * pathELength I γ 0 1 := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
        pathELength_eq_lintegral_mfderivWithin_Icc]

lemma map_edist_le_riemannianEDist (f : M → F) (hf : ContMDiff I 𝓘(ℝ,F) 1 f)
    (C : ℝ≥0) (hpos : 0 < C)
    (hC : ∀ x, ENorm.enorm (E := TangentSpace I x →L[ℝ] F) (mfderiv I 𝓘(ℝ,F) f x) ≤ C)
    (x y : M) :
    edist (f x) (f y) ≤ C * riemannianEDist I x y := by
  rw [riemannianEDist, ENNReal.mul_iInf_of_ne (by exact_mod_cast hpos.ne') ENNReal.coe_ne_top]
  simp_rw [ENNReal.mul_iInf_of_ne (by exact_mod_cast hpos.ne') ENNReal.coe_ne_top]
  apply le_iInf
  intro γ
  apply le_iInf
  intro hγ
  rw [lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc]
  simpa using map_edist_le_pathELength f hf C hC
    (γ ∘ projIcc 0 1 zero_le_one) (hγ.comp_contMDiffOn contMDiffOn_projIcc)

end
end Yau.Geometry

end OAI
