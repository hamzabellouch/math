import OAI.Dynamics.ConditionalShuffle.TVTransport

namespace OAI

noncomputable section
namespace Revealed.Split
open scoped Classical

def slotEquiv {α β : Type} (r₀ r₁ : α ≃ β) (a₀ : Equiv.Perm α) : Equiv.Perm α ≃ Equiv.Perm β :=
  r₁.permCongr.trans (Equiv.mulRight (r₀.symm.trans (a₀.trans r₁)))

lemma slotEquiv_apply {α β : Type} (r₀ r₁ : α ≃ β) (a₀ g : Equiv.Perm α) :
    slotEquiv r₀ r₁ a₀ g = r₀.symm.trans ((a₀.trans g).trans r₁) := by
  apply Equiv.ext
  intro x
  change r₁ (g (r₁.symm (r₁ (a₀ (r₀.symm x))))) = r₁ (g (a₀ (r₀.symm x)))
  rw [Equiv.symm_apply_apply]

end Revealed.Split

namespace Revealed.Disintegration
open scoped Classical
open Thorp
lemma average_quotient {E G : Type} [Fintype E] [Fintype G] [Nonempty G]
    (μ : E × G → ℝ) (u : G → ℝ) :
    (∑ e, marginal μ e * tv (fun g => μ (e,g) / marginal μ e) u) =
      ∑ e, marginal μ e * tv (conditional μ e) u := by
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : marginal μ e = 0
  · simp only [h, zero_mul]
  · have hc : conditional μ e = fun g => μ (e,g) / marginal μ e := by
      funext g
      rw [conditional, ite_eq_right h]
    rw [hc]
end Revealed.Disintegration

namespace Revealed
open scoped Classical
open Thorp Thorp.Conditional Split Instrument Disintegration Physical

def splitLayout (d : ℕ) (g₀ : State (d+1)) : Sum (Position d) (Position d) ≃ Position (d+1) :=
  (splitLabels d).trans g₀

lemma splitLayout_post (d : ℕ) (g₀ g : State (d+1)) :
    (splitLayout d g₀).trans g = splitLayout d (g*g₀) := rfl

lemma outsidePaths_split (d t : ℕ) (g₀ : State (d+1)) (ω : History (d+1) t) :
    outsidePaths d t g₀ ω = splitPath (splitLayout d g₀) t ω := by
  induction t with
  | zero => rfl
  | succ t ih =>
      funext s x
      refine Fin.lastCases ?_ (fun j => ?_) s
      · simp only [outsidePaths, layoutPath, splitPath, exposedPath, Fin.snoc_last]
        rfl
      · simp only [outsidePaths, layoutPath, splitPath, exposedPath, Fin.snoc_castSucc]
        exact congrFun (congrFun (ih (Fin.init ω)) j) x

def canonicalTransport (d t : ℕ) (g₀ : State (d+1))
    (p : Fin t → Outside (Position d) (Position d) (Position (d+1))) :
    State d ≃ Equiv.Perm (Fin (2^d)) :=
  slotEquiv (ranks d (splitLayout d g₀))
    (ranks d (sectionFrame (base (instrument (d+1)) (Split.outside (splitLayout d g₀)) t p)))
    (assignment (splitLayout d g₀))

lemma canonical_realization (d t : ℕ) (g₀ : State (d+1)) (ω : History (d+1) t) :
    canonicalTransport d t g₀ (observed (instrument (d+1)) (Split.outside (splitLayout d g₀)) t ω)
      (groupRun (instrument (d+1)) (Split.outside (splitLayout d g₀)) t ω) =
        slotPermutation d t g₀ ω := by
  rw [canonicalTransport, slotEquiv_apply, physical_base]
  have hg : (assignment (splitLayout d g₀)).trans
      (groupRun (instrument (d+1)) (Split.outside (splitLayout d g₀)) t ω) =
      assignment ((splitLayout d g₀).trans (run (d+1) t ω)) :=
    physical_group (d+1) (splitLayout d g₀) t ω
  rw [hg, ← ranks_assignment, splitLayout_post]
  change (ranks d ((splitLabels d).trans g₀)).symm.trans
    (ranks d ((splitLabels d).trans (run (d+1) t ω*g₀))) = _
  rw [ranks_freeRank, ranks_freeRank]
  rfl

lemma expectedTV_completed (d t : ℕ) (g₀ : State (d+1)) : expectedTV d t g₀ =
    ∑ e, marginal (fairMass (fun ω : History (d+1) t =>
      (outsidePaths d t g₀ ω,slotPermutation d t g₀ ω))) e *
      tv (conditional (fairMass (fun ω : History (d+1) t =>
        (outsidePaths d t g₀ ω,slotPermutation d t g₀ ω))) e)
      (fun _ => (Fintype.card (Equiv.Perm (Fin (2^d))) : ℝ)⁻¹) := by
  rw [← average_quotient]
  simp only [marginal_fairMass, Fintype.card_perm, Fintype.card_fin]
  simp only [expectedTV, environmentMass, one_div]
  apply Finset.sum_congr rfl
  intro e _
  congr 2

theorem expectedTV_le_instrument (d t : ℕ) (g₀ : State (d+1)) : expectedTV d t g₀ ≤
    Instrument.distance (instrument (d+1)) (Split.outside (splitLayout d g₀)) t := by
  let : Fintype (Outside (Position d) (Position d) (Position (d+1))) := inferInstance
  rw [expectedTV_completed, distance_disintegration]
  have h := average_tv_transport
    (observed (instrument (d+1)) (Split.outside (splitLayout d g₀)) t)
    (groupRun (instrument (d+1)) (Split.outside (splitLayout d g₀)) t)
    (fullPath (Split.outside (splitLayout d g₀))) (canonicalTransport d t g₀)
  simp_rw [canonical_realization, physical_path, ← outsidePaths_split] at h
  exact h

lemma expectedTV_nonneg (d t : ℕ) (g₀ : State (d+1)) : 0 ≤ expectedTV d t g₀ := by
  unfold expectedTV
  exact Finset.sum_nonneg (fun e _ => mul_nonneg (fairMass_nonneg _ e) (Thorp.Fourier.tv_nonneg _ _))

end Revealed

end

end OAI
