import OAI.GroupTheory.PolycyclicRecognition.Algebra.ValuedEigenlineCones
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialGrowthSemigroupPingPong
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ValuedPowerDominant

namespace OAI

/-! # One-sided spectral gaps contradict polynomial growth

Two transverse attracting eigenlines give disjoint forward invariant cones
for suitable positive powers. Counting positive words needs no inverse gap.
-/

noncomputable section
namespace PolycyclicRecognition.ValuedLinearDynamics

variable {K G V : Type} [NontriviallyNormedField K] [Group G]
    [NormedAddCommGroup V] [NormedSpace K V] [MulAction G V]

theorem forward_cones_of_dominant_eigenlines
    (ρ : G →* (V →L[K] V)) (hact : ∀ g x, ρ g x = g • x)
    (a : Bool → G) (φ : Bool → V →L[K] K) (v : Bool → V)
    (μ : Bool → K) (b : Bool → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hv : ∀ i, ρ (a i) (v i) = μ i • v i)
    (hφv : ∀ i, φ i (v i) = 1)
    (hφ : ∀ i x, φ i (ρ (a i) x) = μ i * φ i x)
    (hb : ∀ i, 0 ≤ b i) (hgap : ∀ i, b i < ‖μ i‖)
    (hker : ∀ i x, φ i x = 0 → ‖ρ (a i) x‖ ≤ b i * ‖x‖)
    (htrans : ∀ i j, ‖φ i‖ * ε < ‖φ i (v j)‖) :
    ∃ N : ℕ, 0 < N ∧ ∀ i j x, x ∈ cone (φ j) (v j) ε →
      (a i) ^ N • x ∈ cone (φ i) (v i) ε := by
  let Q (i j : Bool) : ℝ :=
    (‖v j‖ + ε) / (‖φ i (v j)‖ - ‖φ i‖ * ε) + ‖v i‖
  let M (i : Bool) := max (Q i false) (Q i true)
  have hM (i j : Bool) : Q i j ≤ M i := by
    cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hsrc (i j : Bool) (x : V) (hx : x ∈ cone (φ j) (v j) ε) :
      φ i x ≠ 0 ∧ ‖remainder (φ i) (v i) x‖ ≤ M i * ‖φ i x‖ := by
    refine ⟨cone_transverse_nonzero (φ j) (φ i) (v j) ε (htrans i j) hx, ?_⟩
    have hn := cone_transverse_bound (φ j) (φ i) (v j) x ε hε.le (htrans i j) hx.2
    calc
      ‖remainder (φ i) (v i) x‖ ≤ ‖x‖ + ‖φ i x‖ * ‖v i‖ := by
        simpa only [remainder, norm_smul] using norm_sub_le x (φ i x • v i)
      _ ≤ Q i j * ‖φ i x‖ := by dsimp only [Q]; nlinarith only [hn]
      _ ≤ M i * ‖φ i x‖ := mul_le_mul_of_nonneg_right (hM i j) (norm_nonneg _)
  have hc (i : Bool) := contracts_cones (ρ (a i)) (φ i) (v i) (μ i) (b i)
    (hv i) (hφv i) (hφ i) (hb i) (hgap i) (hker i) (M i) ε hε
  choose N hN using hc
  let n := max 1 (max (N false) (N true))
  refine ⟨n, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro i j x hx
  have hi : N i ≤ n := by
    apply le_trans _ (le_max_right _ _)
    cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  obtain ⟨hx0, hxM⟩ := hsrc i j x hx
  have he : (ρ (a i) ^ n) x = (a i) ^ n • x := by rw [← map_pow, hact]
  rw [← he]
  refine ⟨?_, hN i n hi x hxM⟩
  intro hz
  have hne : φ i ((ρ (a i) ^ n) x) ≠ 0 := by
    rw [functional_power _ _ _ (hφ i)]
    exact mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mp
      (ne_of_gt ((hb i).trans_lt (hgap i))))) hx0
  exact hne (by rw [hz, map_zero])

variable [CompleteSpace K] [FiniteDimensional K V] [DecidableEq G]

theorem polynomial_growth_excludes_transverse_dominant_eigenlines
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (ρ : G →* (V →L[K] V)) (hact : ∀ g x, ρ g x = g • x)
    (a : Bool → G) (φ : Bool → V →L[K] K) (v : Bool → V)
    (μ : Bool → K) (b : Bool → ℝ)
    (hv : ∀ i, ρ (a i) (v i) = μ i • v i)
    (hφv : ∀ i, φ i (v i) = 1)
    (hφ : ∀ i x, φ i (ρ (a i) x) = μ i * φ i x)
    (hb : ∀ i, 0 ≤ b i) (hgap : ∀ i, b i < ‖μ i‖)
    (hker : ∀ i x, φ i x = 0 → ‖ρ (a i) x‖ ≤ b i * ‖x‖)
    (htrans : ∀ i j, φ i (v j) ≠ 0)
    (hline : v true ∉ Submodule.span K ({v false} : Set V)) : False := by
  classical
  obtain ⟨δ₀, hδ₀, hsep⟩ := small_cones_disjoint (φ false) (φ true)
    (v false) (v true) hline
  have ht (p : Bool × Bool) : ∃ δ : ℝ, 0 < δ ∧ ∀ ε, 0 ≤ ε → ε ≤ δ →
      ‖φ p.1‖ * ε < ‖φ p.1 (v p.2)‖ :=
    exists_positive_interval_lt (fun ε : ℝ => ‖φ p.1‖ * ε) (by fun_prop)
      ‖φ p.1 (v p.2)‖ (by simpa only [mul_zero] using norm_pos_iff.mpr (htrans p.1 p.2))
  choose δ hδ hδt using ht
  let δ₁ := Finset.univ.inf' (Finset.univ_nonempty :
    (Finset.univ : Finset (Bool × Bool)).Nonempty) δ
  have hδ₁ : 0 < δ₁ := (Finset.lt_inf'_iff _).mpr (fun p _ => hδ p)
  let ε := min δ₀ δ₁
  have hε : 0 < ε := lt_min hδ₀ hδ₁
  have htr (i j : Bool) : ‖φ i‖ * ε < ‖φ i (v j)‖ :=
    hδt (i, j) ε hε.le ((min_le_right _ _).trans (Finset.inf'_le δ (Finset.mem_univ _)))
  obtain ⟨N, _, hN⟩ := forward_cones_of_dominant_eigenlines ρ hact a φ v μ b ε hε
    hv hφv hφ hb hgap hker htr
  apply polynomial_growth_excludes_one_sided_ping_pong S hS hgen hvol
    (fun i => (a i) ^ N) (fun i => cone (φ i) (v i) ε)
    (hsep ε hε.le (min_le_left _ _))
  · refine ⟨v false, ?_, ?_⟩
    · intro hz
      have hh := hφv false
      rw [hz, map_zero] at hh
      exact zero_ne_one hh
    · simp only [remainder, hφv, one_smul, sub_self, norm_zero, norm_one, mul_one]
      exact hε.le
  · intro i x hx
    obtain hx | hx := hx
    · exact hN i false x hx
    · exact hN i true x hx

theorem polynomial_growth_excludes_asymptotically_dominant_eigenlines
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (ρ : G →* (V →L[K] V)) (hact : ∀ g x, ρ g x = g • x)
    (a : Bool → G) (φ : Bool → V →L[K] K) (v : Bool → V)
    (μ : Bool → K) (b C : Bool → ℝ)
    (hv : ∀ i, ρ (a i) (v i) = μ i • v i)
    (hφv : ∀ i, φ i (v i) = 1)
    (hφ : ∀ i x, φ i (ρ (a i) x) = μ i * φ i x)
    (hb : ∀ i, 0 ≤ b i) (hgap : ∀ i, b i < ‖μ i‖) (hC : ∀ i, 0 ≤ C i)
    (hker : ∀ i n x, φ i x = 0 → ‖(ρ (a i) ^ n) x‖ ≤ C i * b i ^ n * ‖x‖)
    (htrans : ∀ i j, φ i (v j) ≠ 0)
    (hline : v true ∉ Submodule.span K ({v false} : Set V)) : False := by
  have he (i : Bool) : ∃ n : ℕ, C i * b i ^ n < ‖μ i ^ n‖ := by
    have hh := scaled_spectral_gap_eventually ‖μ i‖ (b i) (C i) (hb i)
      (by simpa only [abs_of_nonneg (norm_nonneg _)] using hgap i)
    simpa only [abs_pow, abs_of_nonneg (norm_nonneg _), norm_pow] using hh.exists
  choose N hN using he
  apply polynomial_growth_excludes_transverse_dominant_eigenlines S hS hgen hvol ρ hact
    (fun i => a i ^ N i) φ v (fun i => μ i ^ N i) (fun i => C i * b i ^ N i)
  · intro i
    rw [map_pow]
    exact eigenline_vector_power _ _ _ (hv i) (N i)
  · exact hφv
  · intro i x
    rw [map_pow]
    exact functional_power _ _ _ (hφ i) (N i) x
  · exact fun i => mul_nonneg (hC i) (pow_nonneg (hb i) _)
  · exact hN
  · intro i x hx
    rw [map_pow]
    exact hker i (N i) x hx
  · exact htrans
  · exact hline

end PolycyclicRecognition.ValuedLinearDynamics

end

end OAI
