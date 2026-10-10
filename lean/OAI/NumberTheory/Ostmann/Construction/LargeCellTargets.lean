import OAI.NumberTheory.Ostmann.Construction.RoundedCellTargets

namespace OAI

/-! # Constructing the number of cell labels for a large target

The number of labels is the floor of the target divided by the midpoint
of the extreme cell indices. All constants depend only on the density.
-/

namespace Ostmann

/-- A dense set of positive cell indices realizes all sufficiently large
real targets, with a number of labels comparable to target divided by scale. -/
theorem dense_cell_large_target (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Finset ℕ) (a b : ℕ),
      a < b → a ∈ I → b ∈ I → (∀ x ∈ I, a ≤ x ∧ x ≤ b) →
      δ * b + 2 ≤ I.card → ∀ T : ℝ, C * b ≤ T →
      ∃ (n : ℕ) (w : List ℕ), w.length = n ∧ (∀ x ∈ w, x ∈ I) ∧
        |(w.sum : ℝ) - T| < δ⁻¹ ∧ (n : ℝ) * b ≤ 2 * T ∧ T < (n + 1 : ℕ) * b := by
  classical
  obtain ⟨r, hr, happrox⟩ := dense_cell_approximate_sum δ hδ
  let K : ℕ := 2 * r + 1 + ⌈((2 : ℝ) * r + 2 + 2 / δ) / δ⌉₊
  refine ⟨(K : ℝ) + 1, by positivity, ?_⟩
  intro I a b hab ha hb hbounds hdensity T hT
  have hbpos : 0 < b := lt_of_le_of_lt (Nat.zero_le _) hab
  have hbr : (0 : ℝ) < b := by exact_mod_cast hbpos
  let s := b - a
  have hs : 0 < s := Nat.sub_pos_of_lt hab
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  have hsb : (s : ℝ) ≤ b := by exact_mod_cast Nat.sub_le b a
  have hidentity : (s : ℝ) = (b : ℝ) - a := by
    dsimp [s]
    rw [Nat.cast_sub hab.le]
  let A := cellDifferences I a
  have hend : s ∈ A := Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have hbound : ∀ x ∈ A, x ≤ s := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Nat.sub_le_sub_right (hbounds y hy).2 a
  have hcard : A.card = I.card := cellDifferences_card I a (fun x hx => (hbounds x hx).1)
  have hcap : A.card ≤ s + 1 := by
    calc
      A.card ≤ (Finset.range (s + 1)).card := Finset.card_le_card (fun x hx =>
        Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound x hx)))
      _ = _ := Finset.card_range _
  have hspan : δ * b ≤ s := by
    have hh : (I.card : ℝ) ≤ (s : ℝ) + 1 := by exact_mod_cast hcard ▸ hcap
    linarith
  have hd : δ * s + 1 ≤ A.card := by
    rw [hcard]
    nlinarith
  have hdI : δ * (b - a : ℕ) + 1 ≤ I.card := by rwa [hcard] at hd
  let g : ℕ := A.gcd id
  have hspacing : δ * (g : ℝ) ≤ 1 := dense_difference_gcd_bound A s hs hend hbound δ hd
  have hgupper : (g : ℝ) ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by nlinarith)
  let μ : ℝ := ((a : ℝ) + b) / 2
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hμb : μ ≤ b := by
    dsimp [μ]
    have : (a : ℝ) ≤ b := by exact_mod_cast hab.le
    linarith
  have hbμ : (b : ℝ) ≤ 2 * μ := by
    dsimp [μ]
    have := Nat.cast_nonneg (α := ℝ) a
    linarith
  have hT0 : 0 ≤ T := by nlinarith
  let n := ⌊T / μ⌋₊
  have hnlow : (n : ℝ) * μ ≤ T := (le_div_iff₀ hμ).mp (Nat.floor_le (div_nonneg hT0 hμ.le))
  have hnup : T < ((n : ℝ) + 1) * μ := (div_lt_iff₀ hμ).mp (Nat.lt_floor_add_one (T / μ))
  have hKn : K ≤ n := Nat.le_floor ((le_div_iff₀ hμ).mpr (by nlinarith))
  have hrn : r ≤ n := by
    have : r ≤ K := by dsimp [K]; omega
    omega
  have hknδ : (2 : ℝ) * r + 2 + 2 / δ ≤ (n : ℝ) * δ := by
    have hc := Nat.le_ceil (((2 : ℝ) * r + 2 + 2 / δ) / δ)
    have hcn : ⌈((2 : ℝ) * r + 2 + 2 / δ) / δ⌉₊ ≤ n := by
      dsimp [K] at hKn
      omega
    have hcnr : (⌈((2 : ℝ) * r + 2 + 2 / δ) / δ⌉₊ : ℝ) ≤ n := by exact_mod_cast hcn
    exact (div_le_iff₀ hδ).mp (hc.trans hcnr)
  have hgb : (g : ℝ) ≤ (1 / δ) * b :=
    hgupper.trans (le_mul_of_one_le_right (by positivity) (by exact_mod_cast hbpos))
  have hwide : 2 * r * s + 2 * b + 2 * g ≤ (n : ℝ) * s := by
    calc
      _ ≤ 2 * r * b + 2 * b + 2 * ((1 / δ) * b) := by gcongr
      _ = (2 * r + 2 + 2 / δ) * b := by ring
      _ ≤ ((n : ℝ) * δ) * b := mul_le_mul_of_nonneg_right hknδ hbr.le
      _ = (n : ℝ) * (δ * b) := by ring
      _ ≤ (n : ℝ) * s := mul_le_mul_of_nonneg_left hspan (Nat.cast_nonneg _)
  have hlo : (n * a + r * (b - a) + (cellDifferences I a).gcd id : ℕ) ≤ T := by
    push_cast
    change (n : ℝ) * a + r * s + g ≤ T
    dsimp [μ] at hnlow
    nlinarith
  have hhi : T ≤ (n * a + (n - r) * (b - a) : ℕ) := by
    push_cast
    rw [Nat.cast_sub hrn]
    change T ≤ (n : ℝ) * a + ((n : ℝ) - r) * s
    dsimp [μ] at hnup
    nlinarith
  obtain ⟨w, hwlen, hwmem, hwerr⟩ := happrox I a b hab ha hb hbounds hdI n hrn T hlo hhi
  refine ⟨n, w, hwlen, hwmem, hwerr, ?_, ?_⟩
  · nlinarith
  · push_cast
    exact hnup.trans_le (mul_le_mul_of_nonneg_left hμb (by positivity))

end Ostmann

end OAI
