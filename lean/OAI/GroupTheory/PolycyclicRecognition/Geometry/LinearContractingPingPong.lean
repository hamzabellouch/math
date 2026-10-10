import OAI.GroupTheory.PolycyclicRecognition.Geometry.DominantEigenlineContraction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.EventualPingPong

namespace OAI

/-! # Free powers from a concrete contracting linear configuration

Both directions of each of two generators have a dominant eigenline.
Uniform source-cone bounds and disjoint target domains then give actual free
powers. Every hypothesis is an explicit linear or set-theoretic condition.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Pointwise Function

variable {G V : Type} [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MulAction G V]

def signedPingPongGenerator (a : Bool → G) (i s : Bool) : G :=
  if s then (a i)⁻¹ else a i

theorem free_powers_of_dominant_eigenlines
    (ρ : G →* (V →L[ℝ] V)) (hact : ∀ g x, ρ g x = g • x)
    (a : Bool → G) (D : Bool → Set V)
    (φ : Bool → Bool → V →L[ℝ] ℝ) (v : Bool → Bool → V)
    (μ b M ε : Bool → Bool → ℝ)
    (hne : ∀ i, (D i).Nonempty) (hdis : Pairwise (Disjoint on D))
    (hv : ∀ i s, ρ (signedPingPongGenerator a i s) (v i s) = μ i s • v i s)
    (hφv : ∀ i s, φ i s (v i s) = 1)
    (hφ : ∀ i s x, φ i s (ρ (signedPingPongGenerator a i s) x) = μ i s * φ i s x)
    (hb : ∀ i s, 0 ≤ b i s) (hgap : ∀ i s, b i s < |μ i s|)
    (hker : ∀ i s x, φ i s x = 0 →
      ‖ρ (signedPingPongGenerator a i s) x‖ ≤ b i s * ‖x‖)
    (hε : ∀ i s, 0 < ε i s)
    (hsource : ∀ i s j, i ≠ j → ∀ x ∈ D j,
      φ i s x ≠ 0 ∧ ‖eigenlineRemainder (φ i s) (v i s) x‖ ≤ M i s * |φ i s x|)
    (htarget : ∀ i s x, φ i s x ≠ 0 →
      ‖eigenlineRemainder (φ i s) (v i s) x‖ ≤ ε i s * |φ i s x| → x ∈ D i) :
    ∃ N : ℕ, 0 < N ∧ Function.Injective (FreeGroup.lift (fun i => (a i) ^ N)) := by
  apply eventual_ping_pong_free_power a D hne hdis
  intro i
  have hc (s : Bool) : ∃ N : ℕ, ∀ n ≥ N, ∀ j, i ≠ j →
      (signedPingPongGenerator a i s) ^ n • D j ⊆ D i := by
    obtain ⟨N, hN⟩ := dominant_eigenline_contracts_cones
      (ρ (signedPingPongGenerator a i s)) (φ i s) (v i s) (μ i s) (b i s)
      (hv i s) (hφv i s) (hφ i s) (hb i s) (hgap i s) (hker i s)
      (M i s) (ε i s) (hε i s)
    refine ⟨N, fun n hn j hij y hy => ?_⟩
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨hx0, hxbound⟩ := hsource i s j hij x hx
    have hpow : (ρ (signedPingPongGenerator a i s) ^ n) x =
        (signedPingPongGenerator a i s) ^ n • x := by
      rw [← map_pow, hact]
    change (signedPingPongGenerator a i s) ^ n • x ∈ D i
    rw [← hpow]
    apply htarget i s
    · rw [eigenline_functional_power _ _ _ (hφ i s)]
      exact mul_ne_zero (pow_ne_zero n (abs_ne_zero.mp
        (ne_of_gt (lt_of_le_of_lt (hb i s) (hgap i s))))) hx0
    · exact hN n hn x hxbound
  obtain ⟨Np, hp⟩ := hc false
  obtain ⟨Nm, hm⟩ := hc true
  refine ⟨max Np Nm, fun j hij n hn => ⟨?_, ?_⟩⟩
  · exact hp n ((le_max_left _ _).trans hn) j hij
  · exact hm n ((le_max_right _ _).trans hn) j hij

end PolycyclicRecognition

end

end OAI
