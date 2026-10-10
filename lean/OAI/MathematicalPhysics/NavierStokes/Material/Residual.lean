import OAI.MathematicalPhysics.NavierStokes.Material.Model

namespace OAI

namespace Alternating
open scoped Topology BigOperators
open Filter

noncomputable section

theorem spatialD_time_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → Space → E} (hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u)) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun tx : ℝ × Space => spatialD i (u tx.1) tx.2) := by
  have h : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × Space) × Space => u p.1.1 p.2) :=
    hu.comp ((contDiff_fst.fst).prodMk contDiff_snd)
  exact h.fderiv_apply contDiff_snd contDiff_const (by simp)

theorem spatialD_iterate_time_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → Space → E} (hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u)) (i : Fin 3) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun tx : ℝ × Space => (spatialD i)^[n] (u tx.1) tx.2) := by
  induction n with
  | zero => exact hu
  | succ n ih =>
    simpa only [Function.iterate_succ_apply'] using spatialD_time_smooth (u := fun t => (spatialD i)^[n] (u t)) ih i

theorem spatialPartial_time_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → Space → E} (hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u)) (α : MultiIndex) :
    ContDiff ℝ (⊤ : ℕ∞) (fun tx : ℝ × Space => spatialPartial α (u tx.1) tx.2) :=
  spatialD_iterate_time_smooth
    (u := fun t => (spatialD 1)^[α 1] ((spatialD 0)^[α 0] (u t)))
    (spatialD_iterate_time_smooth (u := fun t => (spatialD 0)^[α 0] (u t))
      (spatialD_iterate_time_smooth hu 0 (α 0)) 1 (α 1)) 2 (α 2)

def ordinaryTimeD (u : Field) : Field := fun t x => deriv (fun s => u s x) t

theorem ordinaryTimeD_smooth {u : Field}
    (hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u)) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (ordinaryTimeD u)) := by
  have h : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × Space) × ℝ => u p.2 p.1.2) :=
    hu.comp (contDiff_snd.prodMk (contDiff_fst.snd))
  exact h.fderiv_apply contDiff_fst contDiff_const (by simp)

theorem timeDerivative_eq_ordinary {u : Field}
    (hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u)) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    timeDerivative u t x = ordinaryTimeD u t x := by
  have hd : Differentiable ℝ (fun s => u s x) :=
    (hu.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
  exact (hd t).derivWithin (uniqueDiffOn_Ici 0 t ht)

theorem timeDerivative_smoothUpToZero {u : Field}
    (hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u)) : SmoothUpToZero (timeDerivative u) := by
  apply (ordinaryTimeD_smooth hu).contDiffOn.congr
  intro p hp
  exact timeDerivative_eq_ordinary hu hp.1 p.2

theorem laplacian_time_smooth {u : Field}
    (hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun tx : ℝ × Space => laplacian (u tx.1) tx.2) := by
  apply ContDiff.sum
  intro i _hi
  exact spatialD_time_smooth (u := fun t => spatialD i (u t)) (spatialD_time_smooth hu i) i

theorem convection_time_smooth {u : Field}
    (hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun tx : ℝ × Space => convection (u tx.1) tx.2) := by
  apply ContDiff.sum
  intro i _hi
  exact ((EuclideanSpace.proj i).contDiff.comp hu).smul (spatialD_time_smooth hu i)

theorem residual_smoothUpToZero (ν : ℝ) {u : Field}
    (hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u)) : SmoothUpToZero (residual ν u) :=
  ((timeDerivative_smoothUpToZero hu).add (convection_time_smooth hu).contDiffOn).sub
    ((laplacian_time_smooth hu).contDiffOn.const_smul ν)

theorem classicalRegularity_of_smooth {u : Field}
    (hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u)) :
    ClassicalRegularity u (fun _ _ => 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t _ht
    exact ⟨(hu.comp (contDiff_const.prodMk contDiff_id)).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)), contDiff_const⟩
  · intro x
    exact ((hu.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)).differentiableOn
  · intro T _hT
    refine ⟨?_, ?_, ?_⟩
    · apply (timeDerivative_smoothUpToZero hu).continuousOn.mono
      intro tx htx
      exact ⟨htx.1.1, Set.mem_univ _⟩
    · intro α _hα
      exact (spatialPartial_time_smooth hu α).continuous.continuousOn
    · intro α _hα
      exact (spatialPartial_time_smooth
        (u := fun (_ : ℝ) (_ : Space) => (0 : ℝ)) contDiff_const α).continuous.continuousOn

@[simp] theorem gradient_zero (x : Space) : gradient (fun _ => (0 : ℝ)) x = 0 := by
  ext i
  simp [gradient, spatialD]

theorem nsSolution_residual (ν : ℝ) {u : Field}
    (hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u))
    (h0 : ∀ x : Space, u 0 x = 0) (hd : ∀ t : ℝ, 0 ≤ t → ∀ x : Space, divergence (u t) x = 0) :
    NSSolution ν (residual ν u) u (fun _ _ => 0) := by
  refine ⟨classicalRegularity_of_smooth hu, h0, ?_⟩
  intro t ht x
  refine ⟨hd t ht x, ?_⟩
  simp only [gradient_zero, neg_zero, zero_add, residual]
  abel

theorem supportedIn_spatialD {K : Set Space} (hK : IsClosed K) {u : Field}
    (hu : SupportedIn K u) (i : Fin 3) : SupportedIn K (fun t => spatialD i (u t)) := by
  intro t ht x hx
  have hs : tsupport (u t) ⊆ K := by
    apply closure_minimal _ hK
    intro y hy
    by_contra h
    exact hy (hu t ht y h)
  have hds : tsupport (spatialD i (u t)) ⊆ K :=
    (tsupport_fderiv_apply_subset ℝ (basisVector i)).trans hs
  exact (notMem_tsupport_iff_eventuallyEq.mp (fun hx' => hx (hds hx'))).self_of_nhds

theorem supportedIn_timeDerivative {K : Set Space} {u : Field}
    (hu : SupportedIn K u) : SupportedIn K (timeDerivative u) := by
  intro t ht x hx
  have he : Set.EqOn (fun s => u s x) (fun _ => (0 : Space)) (Set.Ici 0) :=
    fun s hs => hu s hs x hx
  unfold timeDerivative timeD
  rw [derivWithin_congr he (he ht)]
  simp

theorem residual_supported (ν : ℝ) {K : Set Space} (hK : IsClosed K) {u : Field}
    (hu : SupportedIn K u) : SupportedIn K (residual ν u) := by
  intro t ht x hx
  have htime := supportedIn_timeDerivative hu t ht x hx
  have hspace (i : Fin 3) := supportedIn_spatialD hK hu i t ht x hx
  have hlap (i : Fin 3) := supportedIn_spatialD hK (supportedIn_spatialD hK hu i) i t ht x hx
  simp [residual, htime, convection, hspace, laplacian, hlap]

end
end Alternating

end OAI
