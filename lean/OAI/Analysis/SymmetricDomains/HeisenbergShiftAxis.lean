import Mathlib
import OAI.Analysis.SymmetricDomains.HolQuadraticSmul
import OAI.Analysis.SymmetricDomains.QuadraticDomainConnectedComponent

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
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Hermitian
open Set Complex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] {k : ℕ}

def heisenbergShift (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (a : E)
    (p : E × (Fin k → ℂ)) : E × (Fin k → ℂ) :=
  (p.1+a,fun i => p.2 i + 2*I*hermPart (symmetrize (B i)) p.1 a +
    I*(hermQuadratic B a i : ℂ))

omit [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] in

theorem heisenbergShift_residual
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (a : E) (p : E × (Fin k → ℂ)) :
    (fun i => ((heisenbergShift B a p).2 i).im -
      hermQuadratic B (heisenbergShift B a p).1 i) =
      (fun i => (p.2 i).im - hermQuadratic B p.1 i) := by
  funext i
  have hc := congrArg re (hermPart_conj (symmetrize (B i)) (symmetrize_symm (B i)) p.1 a)
  simp only [star_def,conj_re] at hc
  simp only [heisenbergShift,hermQuadratic,hermPart_add_left,hermPart_add_right,
    add_re,add_im,mul_re,mul_im,I_re,I_im,ofReal_re,ofReal_im]
  norm_num only [show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl]
  rw [hc]
  ring

omit [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] in
lemma heisenbergShift_mem
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (C : Set (Fin k → ℝ)) (a : E)
    (p : E × (Fin k → ℂ)) :
    heisenbergShift B a p ∈ quadraticDomain (hermQuadratic B) C ↔
      p ∈ quadraticDomain (hermQuadratic B) C := by
  change (fun i => ((heisenbergShift B a p).2 i).im -
    hermQuadratic B (heisenbergShift B a p).1 i) ∈ C ↔ _
  rw [heisenbergShift_residual]
  rfl

def hermLinearLeft (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (a : E) : E →ₗ[ℂ] ℂ where
  toFun z := hermPart B z a
  map_add' x y := hermPart_add_left B x y a
  map_smul' c x := hermPart_smul_left B c x a

lemma heisenbergShift_analytic
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (a : E) :
    AnalyticOnNhd ℂ (heisenbergShift B a) univ := by
  intro p _
  apply AnalyticAt.prod
  · exact analyticAt_fst.add analyticAt_const
  · apply analyticAt_pi_iff.mpr
    intro i
    have hh : AnalyticAt ℂ (fun q : E × (Fin k → ℂ) =>
        hermPart (symmetrize (B i)) q.1 a) p :=
      ((hermLinearLeft (symmetrize (B i)) a).toContinuousLinearMap.analyticAt p.1).comp
        analyticAt_fst
    exact ((((ContinuousLinearMap.proj i).analyticAt p.2).comp analyticAt_snd).add
      (analyticAt_const.mul hh)).add analyticAt_const

omit [FiniteDimensional ℂ E] in
lemma hermPart_neg_right (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y : E) :
    hermPart B x (-y) = -hermPart B x y := by
  rw [show -y = (-1 : ℂ) • y by simp,hermPart_smul_right]
  simp

omit [FiniteDimensional ℂ E] in
lemma heisenbergShift_left_inverse
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (a : E) :
    Function.LeftInverse (heisenbergShift B (-a)) (heisenbergShift B a) := by
  intro p
  apply Prod.ext
  · simp [heisenbergShift]
  · funext i
    have hQ : hermQuadratic B (-a) = hermQuadratic B a := by
      simpa using hermQuadratic_real_smul B (-1) a
    have hdiag : hermPart (symmetrize (B i)) a a = (hermQuadratic B a i : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using hermPart_diag_real (symmetrize (B i)) (symmetrize_symm (B i)) a
    simp only [heisenbergShift,hermPart_neg_right,hermPart_add_left,hQ]
    rw [hdiag]
    ring

def heisenbergHomeomorph
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (a : E) :
    (E × (Fin k → ℂ)) ≃ₜ (E × (Fin k → ℂ)) where
  toFun := heisenbergShift B a
  invFun := heisenbergShift B (-a)
  left_inv := heisenbergShift_left_inverse B a
  right_inv p := by simpa only [neg_neg] using heisenbergShift_left_inverse B (-a) p
  continuous_toFun := continuous_iff_continuousAt.mpr
    (fun p => (heisenbergShift_analytic B a p (mem_univ _)).continuousAt)
  continuous_invFun := continuous_iff_continuousAt.mpr
    (fun p => (heisenbergShift_analytic B (-a) p (mem_univ _)).continuousAt)

def heisenbergModelHomeomorph
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (C : Set (Fin k → ℝ)) (a : E) :
    quadraticDomain (hermQuadratic B) C ≃ₜ quadraticDomain (hermQuadratic B) C :=
  (heisenbergHomeomorph B a).subtype (fun p => (heisenbergShift_mem B C a p).symm)

omit [FiniteDimensional ℂ E] in

theorem heisenbergShift_axis
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : E × (Fin k → ℂ)) :
    heisenbergShift B (-p.1) p =
      (0,fun i => p.2 i - I*(hermQuadratic B p.1 i : ℂ)) := by
  apply Prod.ext
  · simp [heisenbergShift]
  · funext i
    have hQ : hermQuadratic B (-p.1) = hermQuadratic B p.1 := by
      simpa using hermQuadratic_real_smul B (-1) p.1
    have hdiag : hermPart (symmetrize (B i)) p.1 p.1 =
        (hermQuadratic B p.1 i : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using hermPart_diag_real (symmetrize (B i)) (symmetrize_symm (B i)) p.1
    simp only [heisenbergShift,hermPart_neg_right,hQ]
    rw [hdiag]
    ring

end Release061.Hermitian

end

end OAI
