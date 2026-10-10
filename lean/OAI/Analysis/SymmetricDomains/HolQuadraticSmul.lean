import Mathlib
import OAI.Analysis.SymmetricDomains.HermPartUnit

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Hermitian
open Set Complex
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {k : ℕ}

def holQuadratic (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (z : E) : Fin k → ℂ :=
  fun i => holPart (symmetrize (B i)) z z

def hermQuadratic (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (z : E) : Fin k → ℝ :=
  fun i => (hermPart (symmetrize (B i)) z z).re

omit [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] in
lemma vector_decomposition (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (z : E) (i : Fin k) :
    B i z z = hermQuadratic B z i + (holQuadratic B z i).re := by
  rw [← symmetrize_diag (B i) z]
  exact quadratic_decomposition (symmetrize (B i)) z

lemma holQuadratic_analytic (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (z : E) :
    AnalyticAt ℂ (holQuadratic B) z := by
  exact analyticAt_pi_iff.mpr (fun i => holPart_analytic (symmetrize (B i)) z)

lemma holQuadratic_continuous (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    Continuous (holQuadratic B) :=
  continuous_iff_continuousAt.mpr fun z => (holQuadratic_analytic B z).continuousAt

def quadraticShear (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    E × (Fin k → ℂ) ≃ₜ E × (Fin k → ℂ) where
  toFun x := (x.1,x.2-I • holQuadratic B x.1)
  invFun x := (x.1,x.2+I • holQuadratic B x.1)
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := continuous_fst.prodMk
    (continuous_snd.sub ((holQuadratic_continuous B).comp continuous_fst |>.const_smul I))
  continuous_invFun := continuous_fst.prodMk
    (continuous_snd.add ((holQuadratic_continuous B).comp continuous_fst |>.const_smul I))

lemma quadraticShear_analytic (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (x : E × (Fin k → ℂ)) : AnalyticAt ℂ (quadraticShear B) x := by
  exact analyticAt_fst.prod (analyticAt_snd.sub
    ((holQuadratic_analytic B x.1).comp analyticAt_fst |>.const_smul (c := I)))

lemma quadraticShear_inverse_analytic (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (x : E × (Fin k → ℂ)) : AnalyticAt ℂ (quadraticShear B).symm x := by
  exact analyticAt_fst.prod (analyticAt_snd.add
    ((holQuadratic_analytic B x.1).comp analyticAt_fst |>.const_smul (c := I)))

lemma quadraticShear_residual (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (x : E × (Fin k → ℂ)) :
    (fun i => ((quadraticShear B x).2 i).im-hermQuadratic B (quadraticShear B x).1 i) =
      (fun i => (x.2 i).im-B i x.1 x.1) := by
  funext i
  change (x.2 i-I*holQuadratic B x.1 i).im-hermQuadratic B x.1 i = _
  simp only [sub_im,I_mul_im]
  rw [vector_decomposition B x.1 i]
  ring

theorem quadraticShear_preimage (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (C : Set (Fin k → ℝ)) :
    (quadraticShear B) ⁻¹' {x | (fun i => (x.2 i).im-hermQuadratic B x.1 i) ∈ C} =
      {x | (fun i => (x.2 i).im-B i x.1 x.1) ∈ C} := by
  ext x
  simp only [mem_preimage,mem_ofPred_eq,quadraticShear_residual]

omit [FiniteDimensional ℂ E] in
lemma hermQuadratic_unit (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (c : ℂ) (hc : ‖c‖ = 1)
    (z : E) : hermQuadratic B (c • z) = hermQuadratic B z := by
  funext i
  exact congrArg re (hermPart_unit (symmetrize (B i)) c hc z z)

omit [FiniteDimensional ℂ E] in
lemma hermQuadratic_real_smul (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (r : ℝ) (z : E) :
    hermQuadratic B (r • z) = r^2 • hermQuadratic B z := by
  funext i
  simp only [hermQuadratic,hermPart_real_left,hermPart_real_right,Pi.smul_apply,
    Complex.real_smul,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero,smul_eq_mul]
  ring

omit [FiniteDimensional ℂ E] in
lemma holQuadratic_smul (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (c : ℂ) (z : E) :
    holQuadratic B (c • z) = c^2 • holQuadratic B z := by
  funext i
  exact holPart_smul_both (symmetrize (B i)) c z z

end Release061.Hermitian

end

end OAI
