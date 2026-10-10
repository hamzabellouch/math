import OAI.GroupTheory.PolycyclicRecognition.Algebra.SmallEigenlineCones
import OAI.GroupTheory.PolycyclicRecognition.Algebra.EigenlinePingPong

namespace OAI

/-! # A free pair from transverse dominant eigenlines

Small disjoint cones and their source bounds are constructed from the finite
family of eigenvectors and functionals. No ping-pong-domain existence
hypothesis is used.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G V : Type} [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MulAction G V]

theorem free_powers_of_transverse_dominant_eigenlines
    (ρ : G →* (V →L[ℝ] V)) (hact : ∀ g x, ρ g x = g • x)
    (a : Bool → G) (φ : Bool → Bool → V →L[ℝ] ℝ) (v : Bool → Bool → V)
    (μ b : Bool → Bool → ℝ)
    (hv : ∀ i s, ρ (signedPingPongGenerator a i s) (v i s) = μ i s • v i s)
    (hφv : ∀ i s, φ i s (v i s) = 1)
    (hφ : ∀ i s x, φ i s (ρ (signedPingPongGenerator a i s) x) = μ i s * φ i s x)
    (hb : ∀ i s, 0 ≤ b i s) (hgap : ∀ i s, b i s < |μ i s|)
    (hker : ∀ i s x, φ i s x = 0 →
      ‖ρ (signedPingPongGenerator a i s) x‖ ≤ b i s * ‖x‖)
    (htrans : ∀ i s j t, i ≠ j → φ i s (v j t) ≠ 0)
    (hlines : ∀ i s j t, i ≠ j →
      v j t ∉ Submodule.span ℝ ({v i s} : Set V)) :
    ∃ N : ℕ, 0 < N ∧ Function.Injective (FreeGroup.lift (fun i => (a i) ^ N)) := by
  classical
  let I := (Bool × Bool) × (Bool × Bool)
  have hs (p : I) : ∃ δ : ℝ, 0 < δ ∧ ∀ ε, 0 ≤ ε → ε ≤ δ →
      p.1.1 ≠ p.2.1 →
        ‖φ p.1.1 p.1.2‖ * ε < |φ p.1.1 p.1.2 (v p.2.1 p.2.2)| ∧
        Disjoint (eigenlineCone (φ p.1.1 p.1.2) (v p.1.1 p.1.2) ε)
          (eigenlineCone (φ p.2.1 p.2.2) (v p.2.1 p.2.2) ε) := by
    by_cases hij : p.1.1 = p.2.1
    · exact ⟨1, zero_lt_one, fun _ _ _ h => (h hij).elim⟩
    obtain ⟨δ₁, hδ₁, h₁⟩ := small_eigenline_cones_disjoint
      (φ p.1.1 p.1.2) (φ p.2.1 p.2.2) (v p.1.1 p.1.2) (v p.2.1 p.2.2)
      (hlines _ _ _ _ hij)
    obtain ⟨δ₂, hδ₂, h₂⟩ := exists_positive_interval_lt
      (fun ε : ℝ => ‖φ p.1.1 p.1.2‖ * ε) (by fun_prop)
      |φ p.1.1 p.1.2 (v p.2.1 p.2.2)| (by
        simpa only [mul_zero] using abs_pos.mpr (htrans _ _ _ _ hij))
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun ε hε hεδ _ => ?_⟩
    exact ⟨h₂ ε hε (hεδ.trans (min_le_right _ _)),
      h₁ ε hε (hεδ.trans (min_le_left _ _))⟩
  choose δ hδ hd using hs
  let ε := Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset I).Nonempty) δ
  have hε : 0 < ε := (Finset.lt_inf'_iff _).mpr (fun p _ => hδ p)
  have hεδ (p : I) : ε ≤ δ p := Finset.inf'_le δ (Finset.mem_univ p)
  apply free_powers_of_transverse_eigenline_cones ρ hact a φ v μ b ε hε hv hφv hφ hb hgap hker
  · intro i s j t hij
    exact (hd ((i, s), (j, t)) ε (le_of_lt hε) (hεδ _) hij).1
  · intro i j hij s t
    exact (hd ((i, s), (j, t)) ε (le_of_lt hε) (hεδ _) hij).2

end PolycyclicRecognition

end

end OAI
