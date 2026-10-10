import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Differential

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

namespace ShearFlows
def pulsedSum {ι : Type*} [Fintype ι]
    (b : ι → ℝ → ℝ) (W : ι → Space → Space) : Velocity :=
  fun tx => ∑ j, b j tx.1 • W j tx.2

theorem divergence_const_smul {W : Space → Space} {x : Space}
    (hW : DifferentiableAt ℝ W x) (a : ℝ) :
    divergence (fun y => a • W y) x = a * divergence W x := by
  unfold divergence derivative
  rw [fderiv_fun_const_smul hW]
  simp only [smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem advection_const_smul {W : Space → Space} {x : Space}
    (hW : DifferentiableAt ℝ W x) (a : ℝ) :
    advection (fun y => a • W y) x = (a * a) • advection W x := by
  unfold advection
  rw [fderiv_fun_const_smul hW]
  simp only [smul_apply, map_smul, smul_smul]

theorem pulsedSum_smooth {ι : Type*} [Fintype ι]
    (b : ι → ℝ → ℝ) (W : ι → Space → Space)
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (hW : ∀ j, ContDiff ℝ ∞ (W j)) :
    ContDiff ℝ ∞ (pulsedSum b W) := by
  apply ContDiff.sum
  intro j _
  exact ((hb j).comp contDiff_fst).smul ((hW j).comp contDiff_snd)

theorem pulsedSum_divergence_advection {ι : Type*} [Fintype ι]
    (b : ι → ℝ → ℝ) (W : ι → Space → Space)
    (hactive : ∀ t i j, b i t ≠ 0 → b j t ≠ 0 → i = j)
    (hW : ∀ j, Differentiable ℝ (W j))
    (hdiv : ∀ j x, divergence (W j) x = 0)
    (hadv : ∀ j x, advection (W j) x = 0) :
    Solenoidal (pulsedSum b W) ∧ ZeroAdvection (pulsedSum b W) := by
  classical
  have hboth (t : ℝ) (x : Space) :
      divergence (fun y => pulsedSum b W (t, y)) x = 0 ∧
      advection (fun y => pulsedSum b W (t, y)) x = 0 := by
    by_cases h : ∃ k, b k t ≠ 0
    · obtain ⟨k, hk⟩ := h
      have heq : (fun y => pulsedSum b W (t, y)) = (fun y => b k t • W k y) := by
        funext y
        apply Finset.sum_eq_single k
        · intro j _ hj
          have hj0 : b j t = 0 := by
            by_contra hn
            exact hj (hactive t j k hn hk)
          simp [hj0]
        · simp
      rw [heq, divergence_const_smul (hW k x), advection_const_smul (hW k x), hdiv, hadv]
      simp
    · have hz : ∀ k, b k t = 0 := by simpa using h
      have heq : (fun y => pulsedSum b W (t, y)) = (fun _ => 0) := by
        funext y
        simp [pulsedSum, hz]
      rw [heq]
      simp [divergence, derivative, advection]
  exact ⟨fun t x => (hboth t x).1, fun t x => (hboth t x).2⟩

theorem pulsedSum_mean_zero {ι : Type*} [Fintype ι]
    (b : ι → ℝ → ℝ) (W : ι → Space → Space) (L : ℝ)
    (hW : ∀ j, Continuous (W j))
    (hmean : ∀ j, (∫ x in fundamentalCube L, W j x) = 0) :
    HasZeroMean L (pulsedSum b W) := by
  intro t
  change (∫ x in fundamentalCube L, ∑ j, b j t • W j x) = 0
  rw [integral_finsetSum]
  · simp [integral_smul, hmean]
  · intro j _
    exact ((hW j).const_smul (b j t)).integrableOn_Icc

end ShearFlows

end

end OAI
