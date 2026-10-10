import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularOperator
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Topology.ContinuousMap.Bounded.Star

namespace OAI

/-! The two circular coefficients of the regular-origin spectral equation. -/

open scoped BoundedContinuousFunction
namespace DefocusingNLS

abbrev RegularSpectralSpace := (ℝ →ᵇ ℂ) × (ℝ →ᵇ ℂ)

noncomputable def spectralRegularSourceValue (A B : ℝ →ᵇ ℂ) (cp cm : ℂ)
    (v : RegularSpectralSpace) : RegularSpectralSpace :=
  (A*v.1+B*v.2-cp • v.1,star B*v.1+star A*v.2-cm • v.2)

noncomputable def spectralRegularSourceBound (A B : ℝ →ᵇ ℂ) (cp cm : ℂ) : ℝ :=
  ‖A‖+‖B‖+‖cp‖+‖cm‖

theorem spectralRegularSourceBound_nonneg (A B : ℝ →ᵇ ℂ) (cp cm : ℂ) :
    0 ≤ spectralRegularSourceBound A B cp cm := by
  unfold spectralRegularSourceBound
  positivity

theorem spectralRegularSourceValue_norm (A B : ℝ →ᵇ ℂ) (cp cm : ℂ)
    (v : RegularSpectralSpace) :
    ‖spectralRegularSourceValue A B cp cm v‖ ≤ spectralRegularSourceBound A B cp cm*‖v‖ := by
  have hvp := norm_fst_le v
  have hvm := norm_snd_le v
  have hp : ‖A*v.1+B*v.2-cp • v.1‖ ≤
      (‖A‖+‖B‖+‖cp‖)*‖v‖ := by
    calc
      _ ≤ ‖A*v.1‖+‖B*v.2‖+‖cp • v.1‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ‖A‖*‖v.1‖+‖B‖*‖v.2‖+‖cp‖*‖v.1‖ := by
        gcongr
        · exact norm_mul_le _ _
        · exact norm_mul_le _ _
        · exact norm_smul_le _ _
      _ ≤ ‖A‖*‖v‖+‖B‖*‖v‖+‖cp‖*‖v‖ := by gcongr
      _ = _ := by ring
  have hm : ‖star B*v.1+star A*v.2-cm • v.2‖ ≤
      (‖A‖+‖B‖+‖cm‖)*‖v‖ := by
    calc
      _ ≤ ‖star B*v.1‖+‖star A*v.2‖+‖cm • v.2‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ‖star B‖*‖v.1‖+‖star A‖*‖v.2‖+‖cm‖*‖v.2‖ := by
        gcongr
        · exact norm_mul_le _ _
        · exact norm_mul_le _ _
        · exact norm_smul_le _ _
      _ = ‖B‖*‖v.1‖+‖A‖*‖v.2‖+‖cm‖*‖v.2‖ := by rw [norm_star,norm_star]
      _ ≤ ‖B‖*‖v‖+‖A‖*‖v‖+‖cm‖*‖v‖ := by gcongr
      _ = _ := by ring
  apply max_le
  · exact hp.trans (by unfold spectralRegularSourceBound; nlinarith [norm_nonneg cm,norm_nonneg v])
  · exact hm.trans (by unfold spectralRegularSourceBound; nlinarith [norm_nonneg cp,norm_nonneg v])

noncomputable def spectralRegularSourceCLM (A B : ℝ →ᵇ ℂ) (cp cm : ℂ) :
    RegularSpectralSpace →L[ℂ] RegularSpectralSpace :=
  LinearMap.mkContinuous
    { toFun := spectralRegularSourceValue A B cp cm
      map_add' := by
        intro u v
        apply Prod.ext <;> apply BoundedContinuousFunction.ext <;> intro r
        all_goals
          simp only [spectralRegularSourceValue,Prod.fst_add,Prod.snd_add,
            BoundedContinuousFunction.add_apply,BoundedContinuousFunction.sub_apply,
            BoundedContinuousFunction.mul_apply,BoundedContinuousFunction.smul_apply,smul_eq_mul]
          ring
      map_smul' := by
        intro c v
        apply Prod.ext <;> apply BoundedContinuousFunction.ext <;> intro r
        all_goals
          simp only [spectralRegularSourceValue,Prod.smul_fst,Prod.smul_snd,
            BoundedContinuousFunction.add_apply,BoundedContinuousFunction.sub_apply,
            BoundedContinuousFunction.mul_apply,BoundedContinuousFunction.smul_apply,
            RingHom.id_apply,smul_eq_mul]
          ring }
    (spectralRegularSourceBound A B cp cm) (spectralRegularSourceValue_norm A B cp cm)

theorem spectralRegularSourceCLM_norm (A B : ℝ →ᵇ ℂ) (cp cm : ℂ) :
    ‖spectralRegularSourceCLM A B cp cm‖ ≤ spectralRegularSourceBound A B cp cm :=
  LinearMap.mkContinuous_norm_le _ (spectralRegularSourceBound_nonneg A B cp cm) _

theorem spectralRegularSourceCLM_analyticAt (A B : ℝ →ᵇ ℂ) (cp cm z : ℂ) :
    AnalyticAt ℂ (fun lam => spectralRegularSourceCLM A B (cp+Complex.I*lam)
      (cm-Complex.I*lam)) z := by
  let J : RegularSpectralSpace →L[ℂ] RegularSpectralSpace :=
    ((-Complex.I) • ContinuousLinearMap.fst ℂ (ℝ →ᵇ ℂ) (ℝ →ᵇ ℂ)).prod
      (Complex.I • ContinuousLinearMap.snd ℂ (ℝ →ᵇ ℂ) (ℝ →ᵇ ℂ))
  have he (lam : ℂ) : spectralRegularSourceCLM A B (cp+Complex.I*lam) (cm-Complex.I*lam)=
      spectralRegularSourceCLM A B cp cm+lam • J := by
    apply ContinuousLinearMap.ext
    intro v
    apply Prod.ext <;> apply BoundedContinuousFunction.ext <;> intro r
    all_goals
      simp only [spectralRegularSourceCLM,spectralRegularSourceValue,J,
        add_apply,smul_apply,
        ContinuousLinearMap.prod_apply,ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd',LinearMap.mkContinuous_apply,
        LinearMap.coe_mk,AddHom.coe_mk,Prod.fst_add,Prod.snd_add,
        Prod.smul_fst,Prod.smul_snd,BoundedContinuousFunction.add_apply,
        BoundedContinuousFunction.sub_apply,BoundedContinuousFunction.mul_apply,
        BoundedContinuousFunction.smul_apply,smul_eq_mul]
      ring
  simp_rw [he]
  exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)

end DefocusingNLS

end OAI
