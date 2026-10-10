import OAI.Probability.InvariantIsing.Cavity.CavityCanonicalContinuity
import OAI.Probability.InvariantIsing.Cavity.CavityCanonicalBlockLimit

namespace OAI

/-! Recalculating the covariance from a nearby path is uniform in every
finite overlap block. Thus it is harmless before taking cascade limits. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_recalculated_label_test_uniform {m r : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (q : ℕ → OverlapPath)
    (hL : Tendsto (fun n => ∫ s, |q n s - p s| ∂pathMeasure) atTop (𝓝 0))
    (F : SpectralBlock m r →ᵇ ℝ) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x : Fin r → Fin r → ℝ,
      |F (cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hρsum (q n))
          (cavityCanonicalLabel ρ eig hρ hρsum (q n)) x) -
        F (cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hρsum p)
          (cavityCanonicalLabel ρ eig hρ hρsum p) x)| < ε := by
  intro ε hε
  have hu := (isCompact_univ : IsCompact (univ : Set (SpectralBlock m r))).uniformContinuousOn_of_continuous
    F.continuous.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  have he : ∀ᶠ n in atTop, ∀ a : Fin m, ∀ t : ℝ,
      |cavityCanonicalCoordinate ρ eig hρ hρsum (q n) a t -
        cavityCanonicalCoordinate ρ eig hρ hρsum p a t| < δ :=
    eventually_all.mpr (fun a => cavityCanonicalCoordinate_uniform_of_L1 ρ eig hρ hρsum p q hL a δ hδ)
  filter_upwards [he] with n hn
  intro x
  apply hmod _ (mem_univ _) _ (mem_univ _)
  apply (dist_pi_lt_iff hδ).mpr
  intro i
  apply (dist_pi_lt_iff hδ).mpr
  intro j
  apply (dist_pi_lt_iff hδ).mpr
  intro a
  by_cases hij : i = j
  · simp only [cavitySynchronizedBlock, ite_eq_left hij]
    change |spectralGroupDiagonal ρ eig hρ hρsum (q n) a -
      spectralGroupDiagonal ρ eig hρ hρsum p a| < δ
    simpa only [cavityCanonicalCoordinate, spectralGroupDiagonal,
      Set.projIcc_of_mem zero_le_one (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)] using hn a 1
  · simp only [cavitySynchronizedBlock, ite_eq_right hij]
    change |cavityCanonicalCoordinate ρ eig hρ hρsum (q n) a (x i j) -
      cavityCanonicalCoordinate ρ eig hρ hρsum p a (x i j)| < δ
    exact hn a (x i j)

theorem cavity_recalculated_label_integral_error {m r : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (q : ℕ → OverlapPath)
    (hL : Tendsto (fun n => ∫ s, |q n s - p s| ∂pathMeasure) atTop (𝓝 0))
    (P : ℕ → ProbabilityMeasure JointArray) (F : SpectralBlock m r →ᵇ ℝ) :
    Tendsto (fun n => ∫ x,
      F (cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hρsum (q n))
        (cavityCanonicalLabel ρ eig hρ hρsum (q n)) (arrayBlock spinArray r x)) -
      F (cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hρsum p)
        (cavityCanonicalLabel ρ eig hρ hρsum p) (arrayBlock spinArray r x))
      ∂(P n : Measure JointArray)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [cavity_recalculated_label_test_uniform ρ eig hρ hρsum p q hL F
    (ε / 2) (half_pos hε)] with n hn
  rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
  have hb := norm_integral_le_of_norm_le_const (μ := (P n : Measure JointArray))
    (f := fun x =>
      F (cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hρsum (q n))
        (cavityCanonicalLabel ρ eig hρ hρsum (q n)) (arrayBlock spinArray r x)) -
      F (cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hρsum p)
        (cavityCanonicalLabel ρ eig hρ hρsum p) (arrayBlock spinArray r x)))
    (C := ε / 2) (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using (hn _).le)
  simp only [probReal_univ, mul_one] at hb
  exact hb.trans_lt (half_lt_self hε)

end InvariantIsing

end

end OAI
