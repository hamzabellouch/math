import OAI.MeasureTheory.Falconer.Angular.ActualAngularRegularization

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

noncomputable def sourceAngularWidth (N : ℕ) (sig : ℝ) (J i n : ℕ) : ℝ :=
  (2-(i:ℝ)/(J:ℝ))/(2:ℝ)^n*((2:ℝ)^N)^(1000*sig)

noncomputable def sourceAngularRadius (N : ℕ) (sig : ℝ) (l : ℕ) : ℝ :=
  min 1 (1/(2:ℝ)^l*((2:ℝ)^N)^(50*sig))

theorem sourceAngularRadius_pos (N : ℕ) (sig : ℝ) (l : ℕ) :
    0 < sourceAngularRadius N sig l := by unfold sourceAngularRadius; positivity

theorem sourceAngularWidth_zero (N : ℕ) (sig : ℝ) (J n : ℕ) :
    sourceAngularWidth N sig J 0 n = 2/(2:ℝ)^n*((2:ℝ)^N)^(1000*sig) := by
  simp [sourceAngularWidth]

theorem sourceAngularWidth_gap (N : ℕ) (sig : ℝ) {J : ℕ} (hJ : 0 < J) (i n : ℕ) :
    sourceAngularWidth N sig J i n-sourceAngularWidth N sig J (i+1) n =
      ((2:ℝ)^N)^(1000*sig)/((J:ℝ)*(2:ℝ)^n) := by
  have hj : (J:ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  simp only [sourceAngularWidth,Nat.cast_add,Nat.cast_one]
  field_simp
  ring

theorem sourceAngularWidth_nonneg (N : ℕ) (sig : ℝ) {J i : ℕ}
    (hJ : 0 < J) (hi : i ≤ J) (n : ℕ) : 0 ≤ sourceAngularWidth N sig J i n := by
  have hj : 0 < (J:ℝ) := by exact_mod_cast hJ
  have hiR : (i:ℝ) ≤ J := by exact_mod_cast hi
  have hh : (i:ℝ)/(J:ℝ) ≤ 1 := (div_le_one hj).mpr hiR
  have hn : 0 ≤ 2-(i:ℝ)/(J:ℝ) := by linarith
  unfold sourceAngularWidth
  positivity

theorem uniform_angular_width_gap {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) (C : ℝ) (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ g n : ℕ, g ≤ n → ∀ i : ℕ,
      sourceAngularWidth N sig J (i+1) n+
        (C/(2:ℝ)^g)*sourceAngularRadius N sig (n-g) ≤
      sourceAngularWidth N sig J i n := by
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed (by positivity : 0 < 950*sig) (C*(J:ℝ))
  refine ⟨N₀,?_⟩
  intro N hN g n hgn i
  have hj : 0 < (J:ℝ) := by exact_mod_cast hJ
  have hRp : 0 < (2:ℝ)^N := by positivity
  have hconst := mul_le_mul_of_nonneg_right (hN₀ N hN)
    (by positivity : 0 ≤ ((2:ℝ)^N)^(50*sig))
  have he : ((2:ℝ)^N)^(950*sig)*((2:ℝ)^N)^(50*sig) =
      ((2:ℝ)^N)^(1000*sig) := by rw [← Real.rpow_add hRp]; congr 1; ring
  rw [he] at hconst
  have hp : (2:ℝ)^g*(2:ℝ)^(n-g) = (2:ℝ)^n := by rw [← pow_add,Nat.add_sub_of_le hgn]
  have hb : (C/(2:ℝ)^g)*sourceAngularRadius N sig (n-g) ≤
      ((2:ℝ)^N)^(1000*sig)/((J:ℝ)*(2:ℝ)^n) := by
    calc
      _ ≤ (C/(2:ℝ)^g)*(1/(2:ℝ)^(n-g)*((2:ℝ)^N)^(50*sig)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = (C*(J:ℝ)*((2:ℝ)^N)^(50*sig))/((J:ℝ)*(2:ℝ)^n) := by
        rw [← hp]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hconst (by positivity)
  rw [← sourceAngularWidth_gap N sig hJ i n] at hb
  linarith

theorem uniform_parallel_width_transfer {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare) (ρ : Measure Plane),
      ∀ g p : ℕ, g ≤ p → ∀ (P : CellPath) (i : ℕ) (ω ω' : Plane),
      dist ω ω' ≤ C₀*sourceAngularRadius N sig (p-g) →
      parallelTestCount Q ρ g p P (sourceAngularWidth N sig J (i+1) p) ω' ≤
      parallelTestCount Q ρ g p P (sourceAngularWidth N sig J i p) ω := by
  obtain ⟨N₀,hN₀⟩ := uniform_angular_width_gap hsig hJ (10*C₀) (by positivity)
  refine ⟨N₀,?_⟩
  intro N hN Q ρ g p hgp P i ω ω' hdist
  apply parallelTestCount_transfer Q ρ g p P hdist
  convert hN₀ N hN g p hgp i using 1
  ring

theorem uniform_projection_width_transfer {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare), Q.side = 1 → ∀ (ρ : Measure Plane),
      ∀ p u : ℕ, p ≤ u → ∀ P : CellPath, P.length = p → ∀ (i : ℕ) (ω ω' : Plane),
      dist ω ω' ≤ C₀*sourceAngularRadius N sig (u-p) →
      projectionTestCount Q ρ p u P (sourceAngularWidth N sig J (i+1) u) ω' ≤
      projectionTestCount Q ρ p u P (sourceAngularWidth N sig J i u) ω := by
  obtain ⟨N₀,hN₀⟩ := uniform_angular_width_gap hsig hJ (2*C₀) (by positivity)
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ p u hpu P hP i ω ω' hdist
  apply projectionTestCount_transfer Q (by rw [hQ]; norm_num) ρ p u hP hdist
  rw [hQ]
  convert hN₀ N hN p u hpu i using 1
  ring

end PlanarFalconer

end OAI
