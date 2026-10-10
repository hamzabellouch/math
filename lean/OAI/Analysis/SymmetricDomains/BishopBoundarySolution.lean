import Mathlib
import OAI.Analysis.SymmetricDomains.BoundaryInjective
import OAI.Analysis.SymmetricDomains.VectorLift

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
namespace Release061

theorem smooth_fixed_point_family
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : P × E → E} {F' : P × E →L[ℝ] E}
    (hF : ContDiffAt ℝ ∞ F 0) (hFd : HasFDerivAt F F' 0)
    (hF0 : F 0 = 0) (hFX : F'.comp (ContinuousLinearMap.inr ℝ P E) = 0) :
    ∃ ψ : P → E, ψ 0 = 0 ∧ ContDiffAt ℝ ∞ ψ 0 ∧
      (∀ᶠ p in 𝓝 0, ψ p = F (p,ψ p)) ∧
      HasFDerivAt ψ (F'.comp (ContinuousLinearMap.inl ℝ P E)) 0 := by
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
  refine ⟨ψ,hψ0,hG.contDiffAt_implicitFunction (by simp) hi,?_,?_⟩
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

end Release061

namespace Release061.Wiener

lemma realEvaluation_ext {f g : realAlgebra}
    (h : ∀ θ, realEvaluation θ f = realEvaluation θ g) : f = g := by
  apply Subtype.ext
  apply boundary_injective
  ext θ
  apply Complex.ext
  · exact h θ
  · rw [realAlgebra_boundary_im,realAlgebra_boundary_im]

lemma eval_zero_input {k : ℕ} (θ : Circle) (X : Fin k → realAlgebra) :
    (fun j => realEvaluation θ (Fin.cons (α := fun _ => realAlgebra) 0 X j)) =
      Fin.cons 0 (fun i => realEvaluation θ (X i)) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> simp

lemma cons_zero_norm {A : Type*} [NormedAddCommGroup A] {k : ℕ} (X : Fin k → A) :
    ‖Fin.cons (α := fun _ => A) 0 X‖ = ‖X‖ := by
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (by
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp
      · simpa using norm_le_pi_norm X i)
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (by
      intro i
      simpa using norm_le_pi_norm (Fin.cons (α := fun _ => A) 0 X) i.succ)

lemma exists_boundary_lift {k : ℕ} {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    (hf : AnalyticAt ℝ f 0)
    (hf0 : ∀ᶠ X in 𝓝 (0 : Fin k → ℝ), f (Fin.cons 0 X) = 0) :
    ∃ (ε : ℝ) (F : (Fin (k+1) → realAlgebra) → Fin k → realAlgebra),
      0 < ε ∧ AnalyticAt ℝ F 0 ∧
      (∀ᶠ X in 𝓝 (0 : Fin k → realAlgebra), F (Fin.cons 0 X) = 0) ∧
      (∀ x, ‖x‖ < ε → ∀ θ i,
        realEvaluation θ (F x i) = f (fun j => realEvaluation θ (x j)) i) := by
  obtain ⟨ε,F,hε,hF,hEval⟩ := AnalyticLift.exists_vector_lift (A := realAlgebra) hf
  obtain ⟨δ,hδ,hδf⟩ := Metric.mem_nhds_iff.mp hf0
  refine ⟨ε,F,hε,hF,?_,?_⟩
  · filter_upwards [Metric.ball_mem_nhds (0 : Fin k → realAlgebra) (lt_min hε hδ)] with X hX
    have hX' : ‖X‖ < min ε δ := by simpa [Metric.mem_ball,dist_zero_right] using hX
    funext i
    apply realEvaluation_ext
    intro θ
    change realEvaluation θ (F (Fin.cons 0 X) i) = realEvaluation θ 0
    rw [map_zero,hEval (realEvaluation θ) (realEvaluationCLM θ) (fun _ => rfl)
      (realEvaluation_bound θ) _ (by rw [cons_zero_norm]; exact hX'.trans_le (min_le_left _ _)),
      eval_zero_input]
    have he : ‖fun j => realEvaluation θ (X j)‖ ≤ ‖X‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun j =>
        (realEvaluation_bound θ (X j)).trans (norm_le_pi_norm X j))
    have hh := hδf (by
      simpa [Metric.mem_ball,dist_zero_right] using he.trans_lt (hX'.trans_le (min_le_right _ _)))
    exact congrFun hh i
  · intro x hx θ i
    exact hEval _ (realEvaluationCLM θ) (fun _ => rfl) (realEvaluation_bound θ) x hx i

abbrev BishopParams (k : ℕ) := (Fin k → ℝ) × (Fin k → ℝ) × ℝ × ℝ
abbrev BoundarySpace (k : ℕ) := Fin k → realAlgebra

def bishopInput {k : ℕ} (lam : realAlgebra) :
    (BishopParams k × BoundarySpace k) →L[ℝ] (Fin (k+1) → realAlgebra) :=
  ContinuousLinearMap.pi (fun j => Fin.cases
    ((ContinuousLinearMap.smulRight
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
        ((ContinuousLinearMap.snd ℝ (Fin k → ℝ) (ℝ × ℝ)).comp
          ((ContinuousLinearMap.snd ℝ (Fin k → ℝ) ((Fin k → ℝ) × ℝ × ℝ)).comp
            (ContinuousLinearMap.fst ℝ (BishopParams k) (BoundarySpace k))))) lam) +
      constantReal.comp
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        ((ContinuousLinearMap.snd ℝ (Fin k → ℝ) (ℝ × ℝ)).comp
          ((ContinuousLinearMap.snd ℝ (Fin k → ℝ) ((Fin k → ℝ) × ℝ × ℝ)).comp
            (ContinuousLinearMap.fst ℝ (BishopParams k) (BoundarySpace k))))))
    (fun i => (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ (BishopParams k) (BoundarySpace k))) j)

lemma bishopInput_apply {k : ℕ} (lam : realAlgebra) (p : BishopParams k) (X : BoundarySpace k) :
    bishopInput lam (p,X) = Fin.cons (p.2.2.1 • lam+constantReal p.2.2.2) X := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> rfl

def bishopRHS {k : ℕ} (lam η : realAlgebra)
    (F : (Fin (k+1) → realAlgebra) → BoundarySpace k)
    (q : BishopParams k × BoundarySpace k) : BoundarySpace k :=
  fun i => constantReal (q.1.1 i) + normalizedHilbert (F (bishopInput lam q) i + q.1.2.1 i • η)

lemma bishopRHS_smooth {k : ℕ} (lam η : realAlgebra)
    {F : (Fin (k+1) → realAlgebra) → BoundarySpace k} (hF : AnalyticAt ℝ F 0) :
    ContDiffAt ℝ ∞ (bishopRHS lam η F) 0 := by
  have hFC : ContDiffAt ℝ ∞ (F ∘ bishopInput lam) 0 := by
    have hh : ContDiffAt ℝ ∞ F (bishopInput lam (0 : BishopParams k × BoundarySpace k)) := by
      simpa only [map_zero] using hF.contDiffAt
    have hI : ContDiff ℝ ∞ (bishopInput (k := k) lam) := ContinuousLinearMap.contDiff _
    exact hh.comp 0 hI.contDiffAt
  apply contDiffAt_pi.mpr
  intro i
  have hFi := contDiffAt_pi.mp hFC i
  change ContDiffAt ℝ ∞ (fun q : BishopParams k × BoundarySpace k =>
    constantReal (q.1.1 i) + normalizedHilbert (F (bishopInput lam q) i + q.1.2.1 i • η)) 0
  apply ContDiffAt.add
  · fun_prop
  · apply normalizedHilbert.contDiff.contDiffAt.comp _
    exact hFi.add (by fun_prop)

lemma bishopRHS_zero_unknown {k : ℕ} (lam η : realAlgebra)
    {F : (Fin (k+1) → realAlgebra) → BoundarySpace k}
    (hF0 : ∀ᶠ X in 𝓝 (0 : BoundarySpace k), F (Fin.cons 0 X) = 0) :
    ∀ᶠ X in 𝓝 (0 : BoundarySpace k), bishopRHS lam η F (0,X) = 0 := by
  filter_upwards [hF0] with X hX
  funext i
  simp [bishopRHS,bishopInput_apply,hX]

theorem bishop_boundary_solution {k : ℕ} {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    (hf : AnalyticAt ℝ f 0)
    (hf0 : ∀ᶠ X in 𝓝 (0 : Fin k → ℝ), f (Fin.cons 0 X) = 0)
    (lam η : realAlgebra) :
    ∃ X Y : BishopParams k → BoundarySpace k,
      X 0 = 0 ∧ Y 0 = 0 ∧ ContDiffAt ℝ ∞ X 0 ∧ ContDiffAt ℝ ∞ Y 0 ∧
      (∀ᶠ p in 𝓝 0,
        (∀ i, X p i = constantReal (p.1 i)+normalizedHilbert (Y p i)) ∧
        (∀ θ i, realEvaluation θ (Y p i) =
          f (Fin.cons (p.2.2.1*realEvaluation θ lam+p.2.2.2)
            (fun j => realEvaluation θ (X p j))) i + realEvaluation θ η*p.2.1 i)) := by
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
  obtain ⟨X,hX0,hX,hEq,_⟩ := smooth_fixed_point_family hR hd hR00 hRX
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
  refine ⟨X,Y,hX0,hY0,hX,hY,?_⟩
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
