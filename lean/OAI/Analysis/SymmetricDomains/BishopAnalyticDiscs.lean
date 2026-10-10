import Mathlib
import OAI.Analysis.SymmetricDomains.BishopBoundarySolution

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
namespace Release061

theorem smooth_fixed_point_family_unique
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : P × E → E} {F' : P × E →L[ℝ] E}
    (hF : ContDiffAt ℝ ∞ F 0) (hFd : HasFDerivAt F F' 0)
    (hF0 : F 0 = 0) (hFX : F'.comp (ContinuousLinearMap.inr ℝ P E) = 0) :
    ∃ ψ : P → E, ψ 0 = 0 ∧ ContDiffAt ℝ ∞ ψ 0 ∧
      (∀ᶠ p in 𝓝 0, ψ p = F (p,ψ p)) ∧
      HasFDerivAt ψ (F'.comp (ContinuousLinearMap.inl ℝ P E)) 0 ∧
      (∀ᶠ q in 𝓝 (0 : P × E), F q = q.2 ↔ ψ q.1 = q.2) := by
  let G : P × E → E := fun q => q.2-F q
  let G' : P × E →L[ℝ] E := ContinuousLinearMap.snd ℝ P E-F'
  have hGd : HasFDerivAt G G' 0 := hasFDerivAt_snd.sub hFd
  have hG : ContDiffAt ℝ ∞ G 0 := contDiffAt_snd.sub hF
  have hGX : (fderiv ℝ G 0).comp (ContinuousLinearMap.inr ℝ P E) =
      ContinuousLinearMap.id ℝ E := by
    rw [hGd.fderiv,ContinuousLinearMap.sub_comp,hFX,sub_zero]
    rfl
  have hGP : (fderiv ℝ G 0).comp (ContinuousLinearMap.inl ℝ P E) =
      -(F'.comp (ContinuousLinearMap.inl ℝ P E)) := by
    rw [hGd.fderiv,ContinuousLinearMap.sub_comp]
    change 0-_ = _
    exact zero_sub _
  have hi : ((fderiv ℝ G 0).comp (ContinuousLinearMap.inr ℝ P E)).IsInvertible := by
    rw [hGX]
    exact ⟨ContinuousLinearEquiv.refl ℝ E,rfl⟩
  let ψ := hG.implicitFunction (by simp) hi
  have hψ0 : ψ 0 = 0 := hG.implicitFunction_apply_self (by simp) hi
  refine ⟨ψ,hψ0,hG.contDiffAt_implicitFunction (by simp) hi,?_,?_,?_⟩
  · have hh := hG.eventually_apply_implicitFunction (by simp) hi
    filter_upwards [hh] with p hp
    change ψ p-F (p,ψ p) = (0 : E)-F 0 at hp
    rw [hF0,sub_self] at hp
    exact sub_eq_zero.mp hp
  · have hd := (hG.hasStrictFDerivAt_implicitFunction (by simp) hi).hasFDerivAt
    rw [hGX,hGP] at hd
    have hinv : (ContinuousLinearMap.id ℝ E).inverse = ContinuousLinearMap.id ℝ E :=
      ContinuousLinearMap.inverse_equiv (ContinuousLinearEquiv.refl ℝ E)
    simpa only [ψ,Prod.fst_zero,hinv,ContinuousLinearMap.neg_comp,ContinuousLinearMap.comp_neg,
      ContinuousLinearMap.id_comp,neg_neg] using hd
  · have hh := hG.eventually_apply_eq_iff_implicitFunction (by simp) hi
    filter_upwards [hh] with q hq
    change q.2-F q = (0 : E)-F 0 ↔ ψ q.1 = q.2 at hq
    rw [hF0,sub_self,sub_eq_zero,eq_comm] at hq
    exact hq

end Release061

namespace Release061.Wiener

lemma normalizedHilbert_constant (r : ℝ) : normalizedHilbert (constantReal r) = 0 := by
  have hh : hilbert (1 : Space) = 0 := by
    rw [← UniformSpace.Completion.coe_one]
    change hilbert ((AddMonoidAlgebra.single 0 1 : Poly) : Space) = 0
    rw [hilbert,multiplier_single]
    simp [hilbertSymbol]
  have hc : realHilbert (constantReal r) = 0 := by
    apply Subtype.ext
    change hilbert (algebraMap ℝ Space r) = 0
    rw [Algebra.algebraMap_eq_smul_one]
    have hs := (hilbert.restrictScalars ℝ).map_smul r (1 : Space)
    change hilbert (r • (1 : Space)) = r • hilbert 1 at hs
    rw [hs,hh,smul_zero]
  simp [normalizedHilbert,hc]

lemma realEvaluation_constant (θ : Circle) (r : ℝ) :
    realEvaluation θ (constantReal r) = r := by
  change realEvaluation θ (algebraMap ℝ realAlgebra r) = r
  exact (realEvaluation θ).commutes r

def realSchwarz : realAlgebra →L[ℝ] C(ClosedDisc,ℂ) :=
  (schwarz.restrictScalars ℝ).comp realAlgebra.toSubmodule.subtypeL

def constantDisc : ℝ →L[ℝ] C(ClosedDisc,ℂ) :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) 1

lemma constantDisc_apply (r : ℝ) (z : ClosedDisc) : constantDisc r z = (r : ℂ) := by
  simp [constantDisc]

lemma realSchwarz_boundary (f : realAlgebra) (θ : Circle)
    (hz : fourier 1 θ ∈ ClosedDisc) :
    realSchwarz f ⟨fourier 1 θ,hz⟩ =
      (realEvaluation θ (normalizedHilbert f) : ℂ)+Complex.I*(realEvaluation θ f : ℂ) := by
  change schwarz (f : Space) ⟨fourier 1 θ,hz⟩ = _
  rw [← discValue_eq _ hz,schwarz_boundary]
  apply Complex.ext
  · simp only [Complex.add_re,Complex.sub_re,Complex.ofReal_re,Complex.mul_re,
      Complex.I_re,Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
    rw [realAlgebra_boundary_im,one_mul,sub_zero,add_zero]
    change _ = realEvaluation θ (realHilbert f-constantReal (realEvaluation 0 (realHilbert f)))
    rw [map_sub,realEvaluation_constant]
    rfl
  · simp only [Complex.add_im,Complex.sub_im,Complex.ofReal_re,Complex.mul_im,
      Complex.I_re,Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,one_mul,zero_add]
    rw [real_boundary (hilbert_real (realAlgebra_mem_subspace f)) θ,
      real_boundary (hilbert_real (realAlgebra_mem_subspace f)) 0,sub_self,zero_add]
    rfl

lemma fourier_mem_closedDisc (θ : Circle) : fourier 1 θ ∈ ClosedDisc := by
  simpa only [ClosedDisc,Metric.mem_closedBall,dist_zero_right,fourier_one] using
    (_root_.Circle.norm_coe (AddCircle.toCircle θ)).le

lemma schwarz_constant (r : ℝ) :
    realSchwarz (constantReal r) = ContinuousMap.const ClosedDisc (Complex.I*(r : ℂ)) := by
  change schwarz (algebraMap ℝ Space r) = _
  rw [Algebra.algebraMap_eq_smul_one]
  have hs := (schwarz.restrictScalars ℝ).map_smul r (1 : Space)
  change schwarz (r • (1 : Space)) = r • schwarz 1 at hs
  rw [hs,← UniformSpace.Completion.coe_one]
  change r • schwarz ((AddMonoidAlgebra.single 0 1 : Poly) : Space) = _
  rw [schwarz_single]
  ext z
  simp [schwarzModeC,schwarzMode,mul_comm]

def bishopDisc {k : ℕ} (Y : BishopParams k → BoundarySpace k)
    (p : BishopParams k) (i : Fin k) : C(ClosedDisc,ℂ) :=
  constantDisc (p.1 i)+realSchwarz (Y p i)

lemma bishopDisc_smooth {k : ℕ} {Y : BishopParams k → BoundarySpace k}
    (hY : ContDiffAt ℝ ∞ Y 0) : ContDiffAt ℝ ∞ (bishopDisc Y) 0 := by
  apply contDiffAt_pi.mpr
  intro i
  apply ContDiffAt.add
  · fun_prop
  · exact realSchwarz.contDiff.contDiffAt.comp _ (contDiffAt_pi.mp hY i)

lemma bishopDisc_continuous_boundary {k : ℕ} (Y : BishopParams k → BoundarySpace k)
    (p : BishopParams k) : Continuous (fun z : ClosedDisc => fun i => bishopDisc Y p i z) := by
  apply continuous_pi
  intro i
  exact (bishopDisc Y p i).continuous

lemma bishopDisc_analytic {k : ℕ} (Y : BishopParams k → BoundarySpace k) (p : BishopParams k) :
    AnalyticOnNhd ℂ (fun z : ℂ => fun i => (p.1 i : ℂ)+discValue (Y p i) z) (Metric.ball 0 1) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_pi.mpr
  intro i
  exact (differentiableAt_const _).add (discValue_analytic (Y p i) z hz).differentiableAt

lemma bishopDisc_boundary {k : ℕ} {X Y : BishopParams k → BoundarySpace k}
    {p : BishopParams k} (hX : ∀ i, X p i = constantReal (p.1 i)+normalizedHilbert (Y p i))
    (θ : Circle) (i : Fin k) :
    bishopDisc Y p i ⟨fourier 1 θ,fourier_mem_closedDisc θ⟩ =
      (realEvaluation θ (X p i) : ℂ)+Complex.I*(realEvaluation θ (Y p i) : ℂ) := by
  change constantDisc (p.1 i) _+realSchwarz (Y p i) _ = _
  rw [constantDisc_apply,realSchwarz_boundary,hX i,map_add,realEvaluation_constant]
  rw [Complex.ofReal_add,add_assoc]

theorem bishop_analytic_discs {k : ℕ} {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    (hf : AnalyticAt ℝ f 0)
    (hf0 : ∀ᶠ X in 𝓝 (0 : Fin k → ℝ), f (Fin.cons 0 X) = 0)
    (lam η : realAlgebra) (hlam : realEvaluation 0 lam = 0) (hη : realEvaluation 0 η = 0) :
    ∃ A : BishopParams k → Fin k → C(ClosedDisc,ℂ),
      A 0 = 0 ∧ ContDiffAt ℝ ∞ A 0 ∧
      (∀ p, ∃ g : ℂ → Fin k → ℂ, AnalyticOnNhd ℂ g (Metric.ball 0 1) ∧
        ∀ z : ClosedDisc, ∀ i, g z i = A p i z) ∧
      (∀ᶠ p in 𝓝 0,
        (∀ θ i, (A p i ⟨fourier 1 θ,fourier_mem_closedDisc θ⟩).im =
          f (Fin.cons (p.2.2.1*realEvaluation θ lam+p.2.2.2)
            (fun j => (A p j ⟨fourier 1 θ,fourier_mem_closedDisc θ⟩).re)) i +
              realEvaluation θ η*p.2.1 i) ∧
        (∀ i, A p i ⟨1,by simp [ClosedDisc]⟩ =
          (p.1 i : ℂ)+Complex.I*(f (Fin.cons p.2.2.2 p.1) i : ℂ))) := by
  obtain ⟨X,Y,hX0,hY0,hX,hY,hEq⟩ := bishop_boundary_solution hf hf0 lam η
  refine ⟨bishopDisc Y,?_,bishopDisc_smooth hY,?_,?_⟩
  · ext i z
    simp [bishopDisc,hY0]
  · intro p
    refine ⟨fun z i => (p.1 i : ℂ)+discValue (Y p i) z,bishopDisc_analytic Y p,?_⟩
    intro z i
    dsimp only
    rw [discValue_eq _ z.property]
    change _ = constantDisc (p.1 i) z+schwarz (Y p i) z
    rw [constantDisc_apply]
  · filter_upwards [hEq] with p hp
    have heval (θ : Circle) (i : Fin k) := bishopDisc_boundary hp.1 θ i
    have hRe (θ : Circle) (i : Fin k) :
        (bishopDisc Y p i ⟨fourier 1 θ,fourier_mem_closedDisc θ⟩).re = realEvaluation θ (X p i) := by
      rw [heval]
      simp
    have hIm (θ : Circle) (i : Fin k) :
        (bishopDisc Y p i ⟨fourier 1 θ,fourier_mem_closedDisc θ⟩).im = realEvaluation θ (Y p i) := by
      rw [heval]
      simp
    refine ⟨?_,?_⟩
    · intro θ i
      simp only [hRe,hIm]
      exact hp.2 θ i
    · intro i
      have hE : (fun j => realEvaluation 0 (X p j)) = p.1 := by
        funext j
        rw [hp.1 j,map_add,normalizedHilbert_eval_zero,realEvaluation_constant]
        ring
      have hYeq := hp.2 0 i
      rw [hlam,hη,mul_zero,zero_add,zero_mul,add_zero,hE] at hYeq
      have hXi : realEvaluation 0 (X p i) = p.1 i := congrFun hE i
      have hh := heval 0 i
      simpa only [fourier_eval_zero,hXi,hYeq] using hh

end Release061.Wiener

end

end OAI
