import OAI.MeasureTheory.Falconer.Estimates.ScaleUniformNonstationary

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem rotated_cosine_integral (f : ℝ → ℂ) (Λ φ : ℝ) :
    (∫ x : ℝ, cosineOscillator Λ (x-φ)*f x) =
      ∫ x : ℝ, cosineOscillator Λ x * f (x+φ) := by
  have h := integral_add_right_eq_self (μ := volume) (fun x : ℝ => cosineOscillator Λ (x-φ)*f x) φ
  simpa only [add_sub_cancel_right] using h.symm

theorem angular_nonstationary_rotated_scale {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ η, 0 < η → η ≤ 1 → ∀ φ : ℝ, |φ| ≤ Real.pi →
    ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f → tsupport f ⊆ Icc a b →
    (∀ x ∈ tsupport f, η ≤ |Real.sin (x-φ)|) →
    ∀ {C D Λ : ℝ}, 0 ≤ C → η⁻¹ ≤ D → 0 < Λ →
    (∀ k ≤ n, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖∫ x : ℝ, cosineOscillator Λ (x-φ)*f x‖ ≤ A*C*(D/(Λ*η))^n := by
  obtain ⟨A,hA,hbound⟩ := angular_nonstationary_scale_uniform
    (a := a-Real.pi) (b := b+Real.pi) (by have := Real.pi_pos; linarith) n
  refine ⟨A,hA,?_⟩
  intro η hη hη1 φ hφ f hf hs haway C D Λ hC hD hΛ hb
  let g : ℝ → ℂ := fun x => f (x+φ)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have hgs : tsupport g ⊆ (fun x : ℝ => x+φ) ⁻¹' tsupport f :=
    tsupport_comp_subset_preimage f (continuous_id.add continuous_const)
  have hs' : tsupport g ⊆ Icc (a-Real.pi) (b+Real.pi) := by
    intro x hx
    have ht := hs (hgs hx)
    have hp := abs_le.mp hφ
    constructor <;> dsimp at ht <;> linarith [ht.1,ht.2,hp.1,hp.2]
  have ha' : ∀ x ∈ tsupport g, η ≤ |Real.sin x| := by
    intro x hx
    simpa only [add_sub_cancel_right] using haway (x+φ) (hgs hx)
  rw [rotated_cosine_integral]
  exact hbound η hη hη1 hg hs' ha' hC hD hΛ (fun k hk x _ => by
    dsimp [g]
    rw [iteratedDeriv_comp_add_const]
    exact hb k hk (x+φ))

end PlanarFalconer

end OAI
