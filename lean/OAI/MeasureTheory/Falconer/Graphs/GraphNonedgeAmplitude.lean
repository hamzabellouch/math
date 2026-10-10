import OAI.MeasureTheory.Falconer.Graphs.GraphAmplitudeScale
import OAI.MeasureTheory.Falconer.Graphs.GraphAmplitudeSupport

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem GraphDerivativeBound.rescale {n : ℕ} {f : (Plane × ℝ) → ℂ} {C D q E : ℝ}
    (hf : GraphDerivativeBound n f C D) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hq : 1 ≤ q) (hE : 0 ≤ E) (hle : D ≤ q*E) :
    GraphDerivativeBound n f (C*q^n) E := by
  refine ⟨hf.smooth,?_⟩
  intro j hj η z hhi hz hlo
  calc
    _ ≤ C*D^j := hf.bound j hj η z hhi hz hlo
    _ ≤ C*(q*E)^j := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD hle _) hC
    _ = (C*q^j)*E^j := by rw [mul_pow]; ring
    _ ≤ (C*q^n)*E^j := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq hj) hC) (pow_nonneg hE _)

theorem uniform_actual_graph_amplitude_E {sig : ℝ} (hsig : 0 < sig) (K n : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) {c₀ : ℝ} (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 4 → Type} [∀ a, DecidableEq (ι a)],
    ∀ (S : ∀ a, Finset (ι a)) (d : ∀ a, ι a → PolicyDescriptor) (k : ∀ a, ι a → ℕ),
    (∀ a, (S a).card ≤ (N+1)^3+1) → (∀ a, (∑ t ∈ S a, k a t) ≤ K) →
    ∀ L : ℕ, (∀ a t, t ∈ S a → descriptorLength (d a t) ≤ L) →
    ∀ Q : Fin 4 → DyadicSquare, (∀ a, 0 < (Q a).side) →
    ∀ (ρ : Fin 4 → Measure Plane) (mass : Fin 4 → ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (h : Fin 4 → Plane → ℂ) (x : Fin 4 → Plane),
    (∀ a, ‖h a (x a)‖ ≤ 1) → ∀ t u : ℝ, 0 ≤ u →
    t ≤ u+2*sig*(N:ℝ) → (L:ℝ) ≤ u+2*sig*(N:ℝ) →
    ∀ (distance plus : Bool) (axis : ℝ) (j₁ j₂ : ℕ),
    let b := fun a => inheritedCircleSymbol (S a) (d a) (k a) (Q a) (ρ a) (mass a)
      N lam sig J i (h a)
    GraphDerivativeBound n (graphAmplitudePullback b x distance plus axis (graphAngularScale N sig t c₀) j₁ j₂ Ψ)
      A (graphNonedgeDerivativeScale N sig u) := by
  obtain ⟨A,hA,N₀,hb⟩ := uniform_actual_graph_amplitude hsig K n hΨ
  let q := 2+4*max 1 c₀⁻¹
  have hq : 1 ≤ q := by dsimp [q]; linarith [le_max_left (1:ℝ) c₀⁻¹]
  refine ⟨A*q^n,mul_nonneg hA (pow_nonneg (zero_le_one.trans hq) _),N₀,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ ρ mass lam J i h x hx t u hu ht hLu distance plus axis j₁ j₂
  have he := hb N hN S d k hcard hK L hL Q hQ ρ mass lam J i h x hx
    (graphAngularScale N sig t c₀) (graphAngularScale_pos N sig t hc)
    ((min_le_left _ _).trans hcap) distance plus axis j₁ j₂
  exact he.rescale hA (by have := sourceSymbolScale_pos N sig L; positivity) hq
    (zero_le_one.trans (graphNonedgeDerivativeScale_one_le N hsig.le hu))
    (graph_total_amplitude_scale N L hsig.le hu hc ht hLu)

end PlanarFalconer

end OAI
