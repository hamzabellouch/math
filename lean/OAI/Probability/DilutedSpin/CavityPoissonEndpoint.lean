import OAI.Probability.DilutedSpin.CavityEndpointCount
import OAI.Probability.DilutedSpin.PoissonRootSelection

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory KernelTower
open scoped BigOperators NNReal
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

lemma upperSelectedCountMean_bound (M : Model p) (hM : Admissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (s : Fin N)
    (f : FinitePath Ω n → ℝ) (l : ℕ) :
    |∫ c,activeCountMean M Q T U V x m j f
        (selectedCount l (rootMap (fun a => decide (a=s)) l c))
        ∂rootLaw l (fun _ => finiteUniform (Fin N))|≤
      ‖f‖+(∫ a,‖a.1‖ ∂M.disorder.toMeasure)*l := by
  apply abs_integral_le_bound_ae
  apply ae_of_all
  intro c
  apply (activeCountMean_bound M hM Q T U V x m hm j f _ (fun y => norm_le_pi_norm f y)).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (integral_nonneg (fun a => norm_nonneg a.1))
  rw [selectedCount_eq_successCountAt]
  exact_mod_cast successCountAt_le s (rootArray l c)

lemma upperPoisson_cavity_separable (M : Model p) (hM : Admissible M) (Q : FiniteLaw R)
    (T : Fin N → KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : Fin N → FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p)
    (f : Fin N → FinitePath Ω n → ℝ) (r : ℝ≥0) :
    (∫ l,upperCountMean M (KernelTower.pi n T) Q U (fun y s => V s (FinitePath.proj n y s)) x m j
      (fun y => ∑ s,f s (FinitePath.proj n y s)) 0 l ∂poissonMeasure r)=
      ∑ s : Fin N,∫ k,activeCountMean M Q (T s) U (V s) x m j (f s) k
        ∂poissonMeasure (r/N) := by
  simp_rw [upperCountMean_separable M hM Q T U V x m hm j f]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro s _
    exact integral_poisson_rootSelection r N s _ (integral_nonneg (fun a : InteractionSample p => norm_nonneg a.1))
      (fun l => activeCountMean_bound M hM Q (T s) U (V s) x m hm j (f s) l
        (fun y => norm_le_pi_norm (f s) y))
  · intro s _
    apply ((integrable_const ‖f s‖).add ((poisson_integrable_count r).const_mul
      (∫ a,‖a.1‖ ∂M.disorder.toMeasure))).mono' (measurable_of_countable _).aestronglyMeasurable
    exact ae_of_all _ (fun l => upperSelectedCountMean_bound M hM Q (T s) U (V s) x m hm j s (f s) l)

end DilutedSpinGlass.PrescribedTree

end

end OAI
