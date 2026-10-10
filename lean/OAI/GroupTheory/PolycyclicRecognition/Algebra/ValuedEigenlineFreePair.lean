import OAI.GroupTheory.PolycyclicRecognition.Algebra.ValuedEigenlineCones
import OAI.GroupTheory.PolycyclicRecognition.Algebra.EventualPingPong

namespace OAI

/-! # Free powers after a change of normed coefficient field

Concrete spectral gaps and transverse eigenlines imply free powers over the
coefficient field. This is the dynamical part needed for Tits's field change.
-/

noncomputable section
namespace PolycyclicRecognition.ValuedLinearDynamics
open scoped Pointwise Function

variable {K G V : Type} [NontriviallyNormedField K] [Group G]
    [NormedAddCommGroup V] [NormedSpace K V] [MulAction G V]

theorem free_powers_of_dominant_eigenlines
    (ρ : G →* (V →L[K] V)) (hact : ∀ g x, ρ g x = g • x)
    (a : Bool → G) (D : Bool → Set V)
    (φ : Bool → Bool → V →L[K] K) (v : Bool → Bool → V)
    (μ : Bool → Bool → K) (b M ε : Bool → Bool → ℝ)
    (hne : ∀ i, (D i).Nonempty) (hdis : Pairwise (Disjoint on D))
    (hv : ∀ i s, ρ (signedPingPongGenerator a i s) (v i s) = μ i s • v i s)
    (hφv : ∀ i s, φ i s (v i s) = 1)
    (hφ : ∀ i s x, φ i s (ρ (signedPingPongGenerator a i s) x) = μ i s * φ i s x)
    (hb : ∀ i s, 0 ≤ b i s) (hgap : ∀ i s, b i s < ‖μ i s‖)
    (hker : ∀ i s x, φ i s x = 0 →
      ‖ρ (signedPingPongGenerator a i s) x‖ ≤ b i s * ‖x‖)
    (hε : ∀ i s, 0 < ε i s)
    (hsource : ∀ i s j, i ≠ j → ∀ x ∈ D j,
      φ i s x ≠ 0 ∧ ‖remainder (φ i s) (v i s) x‖ ≤ M i s * ‖φ i s x‖)
    (htarget : ∀ i s x, φ i s x ≠ 0 →
      ‖remainder (φ i s) (v i s) x‖ ≤ ε i s * ‖φ i s x‖ → x ∈ D i) :
    ∃ N : ℕ, 0 < N ∧ Function.Injective (FreeGroup.lift (fun i => (a i) ^ N)) := by
  apply eventual_ping_pong_free_power a D hne hdis
  intro i
  have hc (s : Bool) : ∃ N : ℕ, ∀ n ≥ N, ∀ j, i ≠ j →
      (signedPingPongGenerator a i s) ^ n • D j ⊆ D i := by
    obtain ⟨N, hN⟩ := contracts_cones
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
    · rw [functional_power _ _ _ (hφ i s)]
      exact mul_ne_zero (pow_ne_zero n (norm_ne_zero_iff.mp
        (ne_of_gt (lt_of_le_of_lt (hb i s) (hgap i s))))) hx0
    · exact hN n hn x hxbound
  obtain ⟨Np, hp⟩ := hc false
  obtain ⟨Nm, hm⟩ := hc true
  refine ⟨max Np Nm, fun j hij n hn => ⟨?_, ?_⟩⟩
  · exact hp n ((le_max_left _ _).trans hn) j hij
  · exact hm n ((le_max_right _ _).trans hn) j hij


theorem free_powers_of_transverse_eigenline_cones
    (ρ : G →* (V →L[K] V)) (hact : ∀ g x, ρ g x = g • x)
    (a : Bool → G) (φ : Bool → Bool → V →L[K] K) (v : Bool → Bool → V)
    (μ : Bool → Bool → K) (b : Bool → Bool → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hv : ∀ i s, ρ (signedPingPongGenerator a i s) (v i s) = μ i s • v i s)
    (hφv : ∀ i s, φ i s (v i s) = 1)
    (hφ : ∀ i s x, φ i s (ρ (signedPingPongGenerator a i s) x) = μ i s * φ i s x)
    (hb : ∀ i s, 0 ≤ b i s) (hgap : ∀ i s, b i s < ‖μ i s‖)
    (hker : ∀ i s x, φ i s x = 0 →
      ‖ρ (signedPingPongGenerator a i s) x‖ ≤ b i s * ‖x‖)
    (htrans : ∀ i s j t, i ≠ j → ‖φ i s‖ * ε < ‖φ i s (v j t)‖)
    (hsep : ∀ i j, i ≠ j → ∀ s t,
      Disjoint (cone (φ i s) (v i s) ε) (cone (φ j t) (v j t) ε)) :
    ∃ N : ℕ, 0 < N ∧ Function.Injective (FreeGroup.lift (fun i => (a i) ^ N)) := by
  let D (i : Bool) := cone (φ i false) (v i false) ε ∪
    cone (φ i true) (v i true) ε
  let Q (i s : Bool) (p : Bool × Bool) : ℝ :=
    (‖v p.1 p.2‖ + ε) / (‖φ i s (v p.1 p.2)‖ - ‖φ i s‖ * ε) + ‖v i s‖
  let M (i s : Bool) := sSup (Set.range (Q i s))
  have hM (i s j t : Bool) : Q i s (j, t) ≤ M i s :=
    le_csSup (Set.finite_range (Q i s)).bddAbove (Set.mem_range_self (j, t))
  apply free_powers_of_dominant_eigenlines ρ hact a D φ v μ b M (fun _ _ => ε)
  · intro i
    have hv0 : v i false ≠ 0 := by
      intro hz
      have h := hφv i false
      rw [hz, map_zero] at h
      exact zero_ne_one h
    refine ⟨v i false, Or.inl ⟨hv0, ?_⟩⟩
    simp only [remainder, hφv, one_smul, sub_self, norm_zero, norm_one, mul_one]
    exact le_of_lt hε
  · intro i j hij
    exact Disjoint.union_left
      (Disjoint.union_right (hsep i j hij false false) (hsep i j hij false true))
      (Disjoint.union_right (hsep i j hij true false) (hsep i j hij true true))
  · exact hv
  · exact hφv
  · exact hφ
  · exact hb
  · exact hgap
  · exact hker
  · exact fun _ _ => hε
  · intro i s j hij x hx
    have ht : ∃ t, x ∈ cone (φ j t) (v j t) ε := by
      rcases hx with hx | hx
      · exact ⟨false, hx⟩
      · exact ⟨true, hx⟩
    obtain ⟨t, hxt⟩ := ht
    refine ⟨cone_transverse_nonzero (φ j t) (φ i s) (v j t) ε
      (htrans i s j t hij) hxt, ?_⟩
    have hn := cone_transverse_bound (φ j t) (φ i s) (v j t) x ε
      (le_of_lt hε) (htrans i s j t hij) hxt.2
    calc
      ‖remainder (φ i s) (v i s) x‖ ≤ ‖x‖ + ‖φ i s x‖ * ‖v i s‖ := by
        simpa only [remainder, norm_smul] using
          norm_sub_le x (φ i s x • v i s)
      _ ≤ Q i s (j, t) * ‖φ i s x‖ := by
        dsimp only [Q]
        nlinarith only [hn]
      _ ≤ M i s * ‖φ i s x‖ :=
        mul_le_mul_of_nonneg_right (hM i s j t) (norm_nonneg _)
  · intro i s x hx0 hx
    have hxn : x ≠ 0 := by
      intro hz
      exact hx0 (by rw [hz, map_zero])
    cases s
    · exact Or.inl ⟨hxn, hx⟩
    · exact Or.inr ⟨hxn, hx⟩


variable [CompleteSpace K] [FiniteDimensional K V]

theorem free_powers_of_transverse_dominant_eigenlines
    (ρ : G →* (V →L[K] V)) (hact : ∀ g x, ρ g x = g • x)
    (a : Bool → G) (φ : Bool → Bool → V →L[K] K) (v : Bool → Bool → V)
    (μ : Bool → Bool → K) (b : Bool → Bool → ℝ)
    (hv : ∀ i s, ρ (signedPingPongGenerator a i s) (v i s) = μ i s • v i s)
    (hφv : ∀ i s, φ i s (v i s) = 1)
    (hφ : ∀ i s x, φ i s (ρ (signedPingPongGenerator a i s) x) = μ i s * φ i s x)
    (hb : ∀ i s, 0 ≤ b i s) (hgap : ∀ i s, b i s < ‖μ i s‖)
    (hker : ∀ i s x, φ i s x = 0 →
      ‖ρ (signedPingPongGenerator a i s) x‖ ≤ b i s * ‖x‖)
    (htrans : ∀ i s j t, i ≠ j → φ i s (v j t) ≠ 0)
    (hlines : ∀ i s j t, i ≠ j →
      v j t ∉ Submodule.span K ({v i s} : Set V)) :
    ∃ N : ℕ, 0 < N ∧ Function.Injective (FreeGroup.lift (fun i => (a i) ^ N)) := by
  classical
  let I := (Bool × Bool) × (Bool × Bool)
  have hs (p : I) : ∃ δ : ℝ, 0 < δ ∧ ∀ ε, 0 ≤ ε → ε ≤ δ →
      p.1.1 ≠ p.2.1 →
        ‖φ p.1.1 p.1.2‖ * ε < ‖φ p.1.1 p.1.2 (v p.2.1 p.2.2)‖ ∧
        Disjoint (cone (φ p.1.1 p.1.2) (v p.1.1 p.1.2) ε)
          (cone (φ p.2.1 p.2.2) (v p.2.1 p.2.2) ε) := by
    by_cases hij : p.1.1 = p.2.1
    · exact ⟨1, zero_lt_one, fun _ _ _ h => (h hij).elim⟩
    obtain ⟨δ₁, hδ₁, h₁⟩ := small_cones_disjoint
      (φ p.1.1 p.1.2) (φ p.2.1 p.2.2) (v p.1.1 p.1.2) (v p.2.1 p.2.2)
      (hlines _ _ _ _ hij)
    obtain ⟨δ₂, hδ₂, h₂⟩ := exists_positive_interval_lt
      (fun ε : ℝ => ‖φ p.1.1 p.1.2‖ * ε) (by fun_prop)
      ‖φ p.1.1 p.1.2 (v p.2.1 p.2.2)‖ (by
        simpa only [mul_zero] using norm_pos_iff.mpr (htrans _ _ _ _ hij))
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

end PolycyclicRecognition.ValuedLinearDynamics

end

end OAI
