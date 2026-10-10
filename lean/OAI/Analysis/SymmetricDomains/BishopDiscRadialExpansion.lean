import Mathlib
import OAI.Analysis.SymmetricDomains.BishopAnalyticDiscs
import OAI.Analysis.SymmetricDomains.BishopNormalZeroDeformation

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
namespace Release061

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem eventually_isUnit_partial {F : P × E → E} {c : ℝ}
    (hc : c ≠ 0) (hF : ContDiffAt ℝ 1 F 0)
    (hzero : ∀ᶠ e in 𝓝 (0 : E), F (0,e) = c • e) :
    ∀ᶠ p in 𝓝 (0 : P), IsUnit (fderiv ℝ (fun e => F (p,e)) 0) := by
  have hd0 : fderiv ℝ (fun e => F (0,e)) 0 = c • ContinuousLinearMap.id ℝ E := by
    exact (((c • ContinuousLinearMap.id ℝ E).hasFDerivAt (x := 0)).congr_of_eventuallyEq hzero).fderiv
  have hu0 : IsUnit (c • ContinuousLinearMap.id ℝ E) := by
    have h := (isUnit_iff_ne_zero.mpr hc).map (algebraMap ℝ (E →L[ℝ] E))
    simpa only [Algebra.algebraMap_eq_smul_one,ContinuousLinearMap.one_def] using h
  have hcont : ContinuousAt (fun p => fderiv ℝ (fun e => F (p,e)) 0) (0 : P) := by
    have hh : ContDiffAt ℝ 0 (fun p => fderiv ℝ (fun e => F (p,e)) 0) (0 : P) :=
      hF.fderiv contDiffAt_const (by norm_num)
    exact hh.continuousAt
  exact hcont.eventually (Units.isOpen.mem_nhds (by change IsUnit (fderiv ℝ (fun e => F (0,e)) 0); rw [hd0]; exact hu0))

end Release061

namespace Release061.Wiener

theorem bishopNormal_transverse {k : ℕ} {κ η : realAlgebra}
    {Y : BishopParams k → BoundarySpace k}
    (hY : ContDiffAt ℝ ∞ Y 0)
    (hzero : ∀ᶠ p in 𝓝 0, p.2.2.1 = 0 → p.2.2.2 = 0 → ∀ i, Y p i = p.2.1 i • η)
    (hη : 0 < 2*realMean (κ*η)) :
    ∀ᶠ α in 𝓝 (0 : ℝ), IsUnit
      (fderiv ℝ (fun e : Fin k → ℝ => bishopNormal κ Y (0,e,α,0)) 0) := by
  let F : ℝ × (Fin k → ℝ) → Fin k → ℝ := fun q => bishopNormal κ Y (0,q.2,q.1,0)
  have hF : ContDiffAt ℝ 1 F 0 := by
    have hN : ContDiffAt ℝ 1 (bishopNormal κ Y) 0 :=
      (bishopNormal_smooth κ hY).of_le (by simp)
    have hP : ContDiffAt ℝ 1 (fun q : ℝ × (Fin k → ℝ) =>
        ((0 : Fin k → ℝ),q.2,q.1,0) : _ → BishopParams k) 0 := by fun_prop
    exact hN.comp (f := fun q : ℝ × (Fin k → ℝ) =>
      ((0 : Fin k → ℝ),q.2,q.1,0)) 0 hP
  have hzq := bishopNormal_zero_deformation (κ := κ) hzero
  have ht : Tendsto (fun e : Fin k → ℝ => ((0 : Fin k → ℝ),e)) (𝓝 0) (𝓝 0) := by
    exact (by fun_prop : ContinuousAt (fun e : Fin k → ℝ => ((0 : Fin k → ℝ),e)) 0)
  have hz : ∀ᶠ e in 𝓝 (0 : Fin k → ℝ), F (0,e) = (2*realMean (κ*η)) • e := by
    exact ht.eventually hzq
  exact eventually_isUnit_partial hη.ne' hF hz

lemma bishopDisc_constant_branch {k : ℕ}
    {f : (Fin (k+1) → ℝ) → Fin k → ℝ} {lam η : realAlgebra}
    {X Y : BishopParams k → BoundarySpace k}
    (hEq : ∀ᶠ p in 𝓝 0, ∀ θ i, realEvaluation θ (Y p i) =
      f (Fin.cons (p.2.2.1*realEvaluation θ lam+p.2.2.2)
        (fun j => realEvaluation θ (X p j))) i+realEvaluation θ η*p.2.1 i)
    (hconst : ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ),
      X (q.1,0,0,q.2) = fun i => constantReal (q.1 i)) :
    ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ), ∀ i (z : ClosedDisc),
      bishopDisc Y (q.1,0,0,q.2) i z =
        (q.1 i : ℂ)+Complex.I*(f (Fin.cons q.2 q.1) i : ℂ) := by
  have ht : Tendsto (fun q : (Fin k → ℝ) × ℝ =>
      (q.1,0,0,q.2) : _ → BishopParams k) (𝓝 0) (𝓝 0) :=
    (by fun_prop : ContinuousAt (fun q : (Fin k → ℝ) × ℝ =>
      (q.1,0,0,q.2) : _ → BishopParams k) 0)
  filter_upwards [ht.eventually hEq,hconst] with q hq hc
  have he (i : Fin k) : Y (q.1,0,0,q.2) i = constantReal (f (Fin.cons q.2 q.1) i) := by
    apply realEvaluation_ext
    intro θ
    rw [hq θ i,hc,realEvaluation_constant]
    simp only [zero_mul,zero_add,Pi.zero_apply,mul_zero,add_zero,realEvaluation_constant]
  intro i z
  change constantDisc (q.1 i) z+realSchwarz (Y (q.1,0,0,q.2) i) z = _
  rw [constantDisc_apply,he]
  rw [schwarz_constant]
  rfl

lemma radial_mem_closedDisc {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    1-(t : ℂ) ∈ ClosedDisc := by
  simp only [ClosedDisc,Metric.mem_closedBall,dist_zero_right]
  rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ht1)]
  linarith

lemma bishopDisc_radial_expansion {k : ℕ} {κ : realAlgebra}
    (hκ : ∀ θ, dist (circleCos θ) (-1 : ℝ) ≤ 1/2 →
      (2-2*circleCos θ)*realEvaluation θ κ = 1)
    {Y : BishopParams k → BoundarySpace k} {p : BishopParams k}
    (hY : ∀ θ, (1/2 : ℝ) < dist (circleCos θ) (-1 : ℝ) →
      ∀ i, realEvaluation θ (Y p i) = 0)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (i : Fin k) :
    bishopDisc Y p i ⟨1-(t : ℂ),radial_mem_closedDisc ht ht1.le⟩ =
      (p.1 i : ℂ)+Complex.I*(t : ℂ)*(bishopNormal κ Y p i : ℂ) -
        (t : ℂ)^2/(1-(t : ℂ))*(discValue (κ*Y p i : Space) (1-(t : ℂ))-
          discValue (κ*Y p i : Space) 0) := by
  change constantDisc (p.1 i) _+schwarz (Y p i) _ = _
  rw [constantDisc_apply,← discValue_eq _ (radial_mem_closedDisc ht ht1.le),
    localized_radial_expansion hκ (fun θ hθ => hY θ hθ i) ht ht1]
  simp only [bishopNormal,add_sub_assoc]

end Release061.Wiener

end

end OAI
