import OAI.Dynamics.ConditionalShuffle.OverlayMain

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter Topology
namespace Revealed.Overlay
open Thorp Thorp.Conditional

def prefixMean (D p t : ℕ) (w : History D p) (f : History D p → History D t → ℝ) : ℝ :=
  mean (fun ω : History D (p+t) =>
      if (splitHistory D p t ω).1 = w then
        f (splitHistory D p t ω).1 (splitHistory D p t ω).2 else 0) /
    fairMass (fun ω : History D (p+t) => (splitHistory D p t ω).1) w

lemma prefixMean_eq (D p t : ℕ) (w : History D p) (f : History D p → History D t → ℝ) :
    prefixMean D p t w f = mean (f w) := by
  unfold prefixMean
  rw [← mean_equiv (splitHistory D p t).symm,
      fairMass_eq_mean, ← mean_equiv (splitHistory D p t).symm]
  simp only [Function.comp_def, Equiv.apply_symm_apply]
  rw [mean_prod, mean_prod]
  simp only [mean_indicator]
  have hconst (a : History D p) :
      mean (fun _ : History D t => if a = w then (1 : ℝ) else 0) =
        if a = w then (1 : ℝ) else 0 := mean_const _
  simp only [hconst]
  simp only [mean, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hc : (Fintype.card (History D p) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (History D p) ≠ 0)
  field_simp

def preCallLayout (d p : ℕ) (g₀ : State (d+3)) (w : History (d+3) p) (phase : ℕ) :
    Sum (OutsideLabels d) (Position d) ≃ Position (d+3) :=
  ((standardLayout d).trans (run (d+3) p w * g₀)).trans (rotate (d+3)^phase)

def preCallRisk (d p : ℕ) (g₀ : State (d+3)) (w : History (d+3) p) (phase : ℕ) : ℝ :=
  prefixMean (d+3) p (65536*21*(d+3)) w (fun a c =>
    tv (conditionalLaw (d+2) (preCallLayout d p g₀ a phase) (isActive (d+3))
        (65536*21*(d+3)) c)
      (fun _ => (Fintype.card (Equiv.Perm (Position d)) : ℝ)⁻¹))

lemma preCallRisk_eq (d p : ℕ) (g₀ : State (d+3)) (w : History (d+3) p) (phase : ℕ) :
    preCallRisk d p g₀ w phase = expectedTV (d+2) (preCallLayout d p g₀ w phase)
      (isActive (d+3)) (65536*21*(d+3)) := by
  exact prefixMean_eq _ _ _ _ _

lemma preCallRisk_le (d p : ℕ) (g₀ : State (d+3)) (w : History (d+3) p) (phase : ℕ) :
    preCallRisk d p g₀ w phase ≤ worstCallTV d := by
  rw [preCallRisk_eq]
  exact Finset.le_sup' (fun g : State (d+3) => expectedTV (d+2) ((standardLayout d).trans g)
    (isActive (d+3)) (65536*21*(d+3)))
    (Finset.mem_univ ((run (d+3) p w * g₀).trans (rotate (d+3)^phase)))

theorem overlay_call_uniform_prehistory :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in atTop,
      ∀ (p : ℕ) (g₀ : State (d+3)) (w : History (d+3) p) (phase : ℕ),
        preCallRisk d p g₀ w phase < ε := by
  intro ε hε
  filter_upwards [(tendsto_order.mp overlay_call).2 ε hε] with d hd
  intro p g₀ w phase
  exact (preCallRisk_le d p g₀ w phase).trans_lt hd

end Revealed.Overlay

end

end OAI
