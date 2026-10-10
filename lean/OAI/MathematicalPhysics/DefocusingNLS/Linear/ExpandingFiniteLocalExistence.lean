import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingWeightedLocal

namespace OAI

/-! # Local nonlinear existence on an arbitrary fixed similarity slab

Only a Lipschitz bound on a fixed state ball is used.  Small initial data
and small forcing keep the exponentially weighted fixed point in that ball.
-/

open Set Metric

namespace DefocusingNLS

attribute [local irreducible] expandingFreeStep

theorem exists_expandingMild_local_finiteSlab (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2)) (u₀ : FourierL2)
    (K ρ R ε : ℝ) (hK : 0 ≤ K) (hρ : 0 ≤ ρ) (hε : 0 ≤ ε)
    (hF : ∀ t x y, ‖x‖ ≤ R → ‖y‖ ≤ R → ‖F (t, x) - F (t, y)‖ ≤ K * ‖x - y‖)
    (hzero : ∀ t, ‖F (t, 0)‖ ≤ ε)
    (hball : Real.exp ((K + 1) * T) * ρ ≤ R)
    (hdata : (K + 1) * ‖u₀‖ + ε ≤ ρ) :
    ∃ u : C(Icc (0 : ℝ) T, FourierL2),
      u = expandingPicard a b k L T ha hk hL hT F u₀ u ∧
      ‖u‖ ≤ Real.exp ((K + 1) * T) * ((K + 1) * ‖u₀‖ + ε) ∧
      ‖u‖ ≤ R := by
  let η := K + 1
  have hη : 0 < η := by dsimp [η]; linarith
  have hKη : K / η < 1 := (div_lt_one hη).2 (by dsimp [η]; linarith)
  let P := expandingBieleckiPicard a b k L T η ha hk hL hT F u₀
  have hstate (z : C(Icc (0 : ℝ) T, FourierL2)) (hz : z ∈ closedBall 0 ρ)
      (t : Icc (0 : ℝ) T) : ‖expandingTimeWeight T η z t‖ ≤ R := by
    have hzn : ‖z‖ ≤ ρ := by simpa only [mem_closedBall, dist_zero_right] using hz
    have hzt : ‖z t‖ ≤ ρ := (ContinuousMap.norm_coe_le_norm z t).trans hzn
    change ‖Real.exp (η * t) • z t‖ ≤ R
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left t.2.2 hη.le)) hzt
      (norm_nonneg _) (Real.exp_pos _).le).trans hball
  have hpair (z w : C(Icc (0 : ℝ) T, FourierL2))
      (hz : z ∈ closedBall 0 ρ) (hw : w ∈ closedBall 0 ρ) :
      dist (P z) (P w) ≤ K / η * dist z w :=
    expandingBieleckiPicard_pair_dist_le a b k L T η ha hk hL hT hη F u₀ K hK z w
      (fun t => hF t _ _ (hstate z hz t) (hstate w hw t))
  have h0 : (0 : C(Icc (0 : ℝ) T, FourierL2)) ∈ closedBall 0 ρ := by simpa using hρ
  have hP0 : ‖P 0‖ ≤ ‖u₀‖ + ε / η :=
    expandingBieleckiPicard_zero_bound a b k L T η ha hk hL hT hη F u₀ ε hε hzero
  have hdata' : ‖u₀‖ + ε / η ≤ ρ / η := by
    apply (le_div_iff₀ hη).mpr
    rw [add_mul, div_mul_cancel₀ _ hη.ne']
    nlinarith [hdata]
  have hidentity : K / η * ρ + ρ / η = ρ := by
    calc
      _ = (K + 1) * ρ / η := by ring
      _ = ρ := mul_div_cancel_left₀ ρ hη.ne'
  have hmap : MapsTo P (closedBall 0 ρ) (closedBall 0 ρ) := by
    intro z hz
    change dist (P z) 0 ≤ ρ
    calc
      dist (P z) 0 ≤ dist (P z) (P 0) + dist (P 0) 0 := dist_triangle _ _ _
      _ ≤ K / η * dist z 0 + (‖u₀‖ + ε / η) := add_le_add (hpair z 0 hz h0) hP0
      _ ≤ K / η * ρ + ρ / η := add_le_add
        (mul_le_mul_of_nonneg_left hz (div_nonneg hK hη.le)) hdata'
      _ = ρ := hidentity
  have hcontract : ContractingWith ⟨K / η, div_nonneg hK hη.le⟩
      (hmap.restrict P (closedBall 0 ρ) (closedBall 0 ρ)) := by
    refine ⟨hKη, LipschitzWith.of_dist_le_mul ?_⟩
    intro z w
    exact hpair z.1 w.1 z.2 w.2
  obtain ⟨z, hz, hfix, _⟩ := hcontract.exists_fixedPoint'
    isClosed_closedBall.isComplete hmap h0 (edist_ne_top _ _)
  have hzbound : ‖z‖ ≤ η * ‖u₀‖ + ε := by
    have hi : ‖z‖ ≤ K / η * ‖z‖ + (‖u₀‖ + ε / η) := by
      calc
        ‖z‖ = dist (P z) 0 := by rw [hfix, dist_zero_right]
        _ ≤ dist (P z) (P 0) + dist (P 0) 0 := dist_triangle _ _ _
        _ ≤ K / η * dist z 0 + (‖u₀‖ + ε / η) := add_le_add (hpair z 0 hz h0) hP0
        _ = _ := by rw [dist_zero_right]
    have hm := mul_le_mul_of_nonneg_right hi hη.le
    have he : (K / η * ‖z‖ + (‖u₀‖ + ε / η)) * η = K * ‖z‖ + η * ‖u₀‖ + ε := by
      calc
        _ = (K / η * η) * ‖z‖ + η * ‖u₀‖ + ε / η * η := by ring
        _ = _ := by rw [div_mul_cancel₀ _ hη.ne', div_mul_cancel₀ _ hη.ne']
    rw [he] at hm
    dsimp [η] at hm ⊢
    nlinarith
  let u := expandingTimeWeight T η z
  have hu : u = expandingPicard a b k L T ha hk hL hT F u₀ u := by
    have he := congrArg (expandingTimeWeight T η) hfix
    simpa only [P, expandingBieleckiPicard, expandingTimeWeight_cancel, u] using he.symm
  have hu_bound : ‖u‖ ≤ Real.exp (η * T) * (η * ‖u₀‖ + ε) := by
    have he := expandingTimeWeight_dist_le T η hη.le z 0
    simp only [expandingTimeWeight_zero, dist_zero_right] at he
    exact he.trans (mul_le_mul_of_nonneg_left hzbound (Real.exp_pos _).le)
  refine ⟨u, hu, hu_bound, ?_⟩
  exact hu_bound.trans ((mul_le_mul_of_nonneg_left hdata (Real.exp_pos _).le).trans hball)

end DefocusingNLS

end OAI
