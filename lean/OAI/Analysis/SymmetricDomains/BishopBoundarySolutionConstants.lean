import Mathlib
import OAI.Analysis.SymmetricDomains.BishopAnalyticDiscs

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
namespace Release061.Wiener

lemma bishop_constant_branch {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    {F : (Fin (k+1) → realAlgebra) → BoundarySpace k}
    {lam η : realAlgebra} {X : BishopParams k → BoundarySpace k}
    (hEval : ∀ x, ‖x‖ < ε → ∀ θ i,
      realEvaluation θ (F x i) = f (fun j => realEvaluation θ (x j)) i)
    (hUnique : ∀ᶠ q in 𝓝 (0 : BishopParams k × BoundarySpace k),
      bishopRHS lam η F q = q.2 ↔ X q.1 = q.2) :
    ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ),
      X (q.1,0,0,q.2) = fun i => constantReal (q.1 i) := by
  let Q : ((Fin k → ℝ) × ℝ) → BishopParams k × BoundarySpace k :=
    fun q => ((q.1,0,0,q.2),fun i => constantReal (q.1 i))
  have hQ : ContinuousAt Q 0 := by fun_prop
  have hQ0 : Q 0 = 0 := by ext <;> simp [Q]
  have hsmall : ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ), ‖bishopInput lam (Q q)‖ < ε := by
    have hc : ContinuousAt (fun q => bishopInput lam (Q q)) 0 := by fun_prop
    exact hc.eventually ((isOpen_lt continuous_norm continuous_const).mem_nhds
      (by simpa only [Set.mem_ofPred_eq,hQ0,map_zero,norm_zero] using hε))
  have hu : ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ),
      bishopRHS lam η F (Q q) = (Q q).2 ↔ X (Q q).1 = (Q q).2 :=
    (show Tendsto Q (𝓝 0) (𝓝 0) by simpa only [hQ0] using hQ.tendsto).eventually hUnique
  filter_upwards [hu,hsmall] with q hq hs
  apply hq.mp
  have hF (i : Fin k) : F (bishopInput lam (Q q)) i = constantReal (f (Fin.cons q.2 q.1) i) := by
    apply realEvaluation_ext
    intro θ
    rw [hEval _ hs,realEvaluation_constant]
    congr 2
    funext j
    dsimp only [Q]
    rw [bishopInput_apply]
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.cons_zero,zero_smul,zero_add,realEvaluation_constant]
    · simp only [Fin.cons_succ,realEvaluation_constant]
  funext i
  change constantReal (q.1 i)+normalizedHilbert (F (bishopInput lam (Q q)) i+0 • η) = constantReal (q.1 i)
  rw [hF,zero_smul,add_zero,normalizedHilbert_constant,add_zero]

theorem bishop_boundary_solution_with_constants {k : ℕ} {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    (hf : AnalyticAt ℝ f 0)
    (hf0 : ∀ᶠ X in 𝓝 (0 : Fin k → ℝ), f (Fin.cons 0 X) = 0)
    (lam η : realAlgebra) :
    ∃ X Y : BishopParams k → BoundarySpace k,
      X 0 = 0 ∧ Y 0 = 0 ∧ ContDiffAt ℝ ∞ X 0 ∧ ContDiffAt ℝ ∞ Y 0 ∧
      (∀ᶠ p in 𝓝 0,
        (∀ i, X p i = constantReal (p.1 i)+normalizedHilbert (Y p i)) ∧
        (∀ θ i, realEvaluation θ (Y p i) =
          f (Fin.cons (p.2.2.1*realEvaluation θ lam+p.2.2.2)
            (fun j => realEvaluation θ (X p j))) i + realEvaluation θ η*p.2.1 i)) ∧
      (∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ),
        X (q.1,0,0,q.2) = fun i => constantReal (q.1 i)) := by
  obtain ⟨ε,F,hε,hF,hF0,hEval⟩ := exists_boundary_lift hf hf0
  let R := bishopRHS lam η F
  have hR := bishopRHS_smooth lam η hF
  have hR0 := bishopRHS_zero_unknown lam η hF0
  have hR00 : R 0 = 0 := hR0.self_of_nhds
  have hd := (hR.differentiableAt (by simp)).hasFDerivAt
  have hRX : (fderiv ℝ R 0).comp
      (ContinuousLinearMap.inr ℝ (BishopParams k) (BoundarySpace k)) = 0 := by
    have hcomp := hd.comp 0 (ContinuousLinearMap.inr ℝ (BishopParams k) (BoundarySpace k)).hasFDerivAt
    exact hcomp.unique ((hasFDerivAt_const (0 : BoundarySpace k) (0 : BoundarySpace k)).congr_of_eventuallyEq hR0)
  obtain ⟨X,hX0,hX,hEq,_,hUnique⟩ := smooth_fixed_point_family_unique hR hd hR00 hRX
  let Y : BishopParams k → BoundarySpace k := fun p i =>
    F (bishopInput lam (p,X p)) i+p.2.1 i • η
  have hY : ContDiffAt ℝ ∞ Y 0 := by
    apply contDiffAt_pi.mpr
    intro i
    apply ContDiffAt.add
    · have hc : ContDiffAt ℝ ∞ (fun p => bishopInput lam (p,X p)) 0 := by fun_prop
      have hFin : ContDiffAt ℝ ∞ F (bishopInput lam (0,X 0)) := by
        simpa only [hX0,← Prod.zero_eq_mk,map_zero] using hF.contDiffAt
      have hh := hFin.comp 0 hc
      exact contDiffAt_pi.mp hh i
    · fun_prop
  have hY0 : Y 0 = 0 := by
    have hh := hF0.self_of_nhds
    have hz : Fin.cons (α := fun _ : Fin (k+1) => realAlgebra) 0 (0 : BoundarySpace k) = 0 := by ext j; exact Fin.cases rfl (fun _ => rfl) j
    rw [hz] at hh
    ext i
    simp [Y,hX0,← Prod.zero_eq_mk,hh]
  refine ⟨X,Y,hX0,hY0,hX,hY,?_,bishop_constant_branch hε hEval hUnique⟩
  have hsmall : ∀ᶠ p in 𝓝 0, ‖bishopInput lam (p,X p)‖ < ε := by
    have hc : ContinuousAt (fun p => bishopInput lam (p,X p)) 0 := by fun_prop
    exact hc.eventually ((isOpen_lt continuous_norm continuous_const).mem_nhds
      (by simpa [hX0,← Prod.zero_eq_mk] using hε))
  filter_upwards [hEq,hsmall] with p hp hs
  refine ⟨fun i => congrFun hp i,?_⟩
  intro θ i
  change realEvaluation θ (F (bishopInput lam (p,X p)) i+p.2.1 i • η) = _
  rw [map_add,map_smul,hEval _ hs θ i,bishopInput_apply]
  have hi : (fun j => realEvaluation θ (Fin.cons (α := fun _ => realAlgebra) (p.2.2.1 • lam+constantReal p.2.2.2) (X p) j)) =
      Fin.cons (p.2.2.1*realEvaluation θ lam+p.2.2.2) (fun j => realEvaluation θ (X p j)) := by
    ext j
    refine Fin.cases ?_ (fun _ => rfl) j
    simp only [Fin.cons_zero,map_add,map_smul,smul_eq_mul]
    change _ + realEvaluation θ (algebraMap ℝ realAlgebra p.2.2.2) = _
    rw [AlgHom.commutes]
    rfl
  rw [hi]
  simp only [smul_eq_mul,mul_comm]

end Release061.Wiener

end

end OAI
