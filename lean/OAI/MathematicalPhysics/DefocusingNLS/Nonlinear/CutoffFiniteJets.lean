import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousAnnulusBounds
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.OddPowerNonlinearity

namespace OAI

/-! # Finite derivative bounds used by the cutoff residual

The nonlinear estimate concerns the actual scalar odd-power polynomial.  The
annular estimate only uses derivatives where the compact coefficient lives.
-/

open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem exists_oddPower_finiteJet_bound (m N : ℕ) (B : ℝ) (_hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : E → ℂ), ContDiff ℝ ∞ f → ∀ x : E,
      (∀ i ≤ N, ‖iteratedFDeriv ℝ i f x‖ ≤ B) →
      ∀ n ≤ N, ‖iteratedFDeriv ℝ n (fun y => oddPowerNonlinearity m (f y)) x‖ ≤ C := by
  let M : ℂ → ℝ := fun z => ∑ i ∈ Finset.range (N + 1),
    ‖iteratedFDeriv ℝ i (oddPowerNonlinearity m) z‖
  have hM : Continuous M := by
    apply continuous_finsetSum
    intro i _
    exact ((contDiff_oddPowerNonlinearity m).continuous_iteratedFDeriv (by simp)).norm
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall (0 : ℂ) B).exists_bound_of_continuousOn
    hM.continuousOn
  let A := max C₀ 0
  let D := max B 1
  let C := ∑ n ∈ Finset.range (N + 1), (n.factorial : ℝ) * A * D ^ n
  have hA : 0 ≤ A := le_max_right _ _
  have hD : 1 ≤ D := le_max_right _ _
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro f hf x hx n hn
  have hxB : ‖f x‖ ≤ B := by simpa only [norm_iteratedFDeriv_zero] using hx 0 (Nat.zero_le _)
  have hxball : f x ∈ Metric.closedBall (0 : ℂ) B := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hxB
  have houter (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i (oddPowerNonlinearity m) (f x)‖ ≤ A := by
    have hiM : ‖iteratedFDeriv ℝ i (oddPowerNonlinearity m) (f x)‖ ≤ M (f x) :=
      Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j (oddPowerNonlinearity m) (f x)‖)
        (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le (hi.trans hn)))
    exact hiM.trans ((le_abs_self _).trans ((hC₀ (f x) hxball).trans (le_max_left _ _)))
  have hinner (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i := by
    exact (hx i (hin.trans hn)).trans ((le_max_left B 1).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hD hi))
  have hodd : ContDiff ℝ ∞ (oddPowerNonlinearity m) :=
    (contDiff_oddPowerNonlinearity m).of_le (by simp)
  have hcomp := norm_iteratedFDeriv_comp_le hodd
    hf (by simp : (n : ℕ∞ω) ≤ ∞) x houter hinner
  have hsum : (n.factorial : ℝ) * A * D ^ n ≤ C :=
    Finset.single_le_sum (f := fun j => (j.factorial : ℝ) * A * D ^ j) (fun j _ => by positivity)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  exact hcomp.trans hsum

noncomputable def annularCoefficientProduct (κ : 𝓢(E, ℂ))
    (hκ : HasCompactSupport (κ : E → ℂ)) (f : E → ℂ) (hf : ContDiff ℝ ∞ f) :
    𝓢(E, ℂ) := (hκ.mul_right (f' := f)).toSchwartzMap (κ.smooth'.mul hf)

@[simp] theorem annularCoefficientProduct_apply (κ : 𝓢(E, ℂ))
    (hκ : HasCompactSupport (κ : E → ℂ)) (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (x : E) :
    annularCoefficientProduct κ hκ f hf x = κ x * f x := rfl

theorem annularCoefficientProduct_jet_bound (κ : 𝓢(E, ℂ))
    (hκ : HasCompactSupport (κ : E → ℂ))
    (hκann : ∀ x ∈ tsupport (κ : E → ℂ), (1 / 2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 2)
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hjet : ∀ x ∈ tsupport (κ : E → ℂ), ∀ i ≤ N,
      ‖iteratedFDeriv ℝ i f x‖ ≤ B) (n : ℕ) (hn : n ≤ N) (x : E) :
    (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n (annularCoefficientProduct κ hκ f hf) x‖ ≤
      3 ^ N * homogeneousAnnulusCutoffConstant κ N * B := by
  by_cases hx : x ∈ tsupport (κ : E → ℂ)
  · have hp : ‖iteratedFDeriv ℝ n (annularCoefficientProduct κ hκ f hf) x‖ ≤
        (∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i κ) * B := by
      refine (norm_iteratedFDeriv_mul_le κ.smooth' hf x (by simp)).trans ?_
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ κ i x)
          (Nat.cast_nonneg _))
        (hjet x hx (n - i) ((Nat.sub_le _ _).trans hn)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _))
    have hs : (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i κ) ≤
        homogeneousAnnulusCutoffConstant κ N := by
      exact Finset.single_le_sum (f := fun j : ℕ => ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i κ)
        (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
    have hw : (1 + ‖x‖) ^ N ≤ (3 : ℝ) ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith [(hκann x hx).2]) _
    calc
      _ ≤ 3 ^ N * (homogeneousAnnulusCutoffConstant κ N * B) :=
        mul_le_mul hw (hp.trans (mul_le_mul_of_nonneg_right hs hB))
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have hz : iteratedFDeriv ℝ n (annularCoefficientProduct κ hκ f hf) x = 0 := by
      by_contra hne
      have hm : x ∈ tsupport (fun y => κ y * f y) := support_iteratedFDeriv_subset n hne
      exact hx (tsupport_mul_subset_left hm)
    rw [hz, norm_zero, mul_zero]
    exact mul_nonneg (mul_nonneg (by positivity)
      (homogeneousAnnulusCutoffConstant_nonneg κ N)) hB

theorem norm_iteratedFDeriv_directional_le (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (v : E) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ f y v) x‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.mp hf).2
  simpa only [norm_iteratedFDeriv_fderiv] using
    norm_iteratedFDeriv_clm_apply_const hdf.contDiffAt (by simp : (n : ℕ∞ω) ≤ ∞)

end DefocusingNLS

end OAI
