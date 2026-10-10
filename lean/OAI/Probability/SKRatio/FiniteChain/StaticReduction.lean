import Mathlib
import OAI.Probability.SKRatio.Dynamics.Assembly
import OAI.Probability.SKRatio.Entropy.BadAvoidance

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter
namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

theorem ratio_cutoff_of_static_inputs (β ε η : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hη : 0 < η)
    (G : ∀ n : ℕ, Set (Disorder n))
    (bad : ∀ n, Disorder n → Set (Spin n)) {κ A χ γ K : ℝ}
    (hκ : 0 < κ) (hA : 0 ≤ A) (hχ : 0 < χ) (hγ : 0 < γ) (hK : 0 < K)
    (hG : Tendsto (fun n => disorderLaw β n (G n)ᶜ) atTop (𝓝 0))
    (hnorm : ∀ n, ∀ g ∈ G n, euclideanOpNorm (coupling g) ≤ K)
    (hgap : ∀ n, ∀ g ∈ G n, ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (hmlsi : ∀ n, ∀ g ∈ G n, ∀ F : Observables n,
      (∀ y, 0 < F y) → FiniteLaw.mean (mass g 0) F = 1 →
      χ*FiniteLaw.entropy (mass g 0) F ≤
        -stationaryInner g (generator (coupling g) F) (fun y => Real.log (F y)))
    (hsmall : ∀ n, ∀ g ∈ G n, FiniteLaw.mean (mass g 0)
      (fun y => if y ∈ bad n g then 1 else 0) ≤ Real.exp (-κ*n))
    (hgradient : ∀ n, ∀ g ∈ G n, ∀ f : Observables n, ∀ y,
      (∑ i, 2*halfDiff i f y*halfDiff i (generator (coupling g) f) y) -
        generator (coupling g) (unweightedGradient f) y ≤
          (-κ + if y ∈ bad n g then A else 0)*unweightedGradient f y) :
    Tendsto
      (fun n : ℕ => disorderLaw β n
        {g : Disorder n | 1+η <
          (mixingTime g ε : ℝ)/(mixingTime g (1-ε) : ℝ)})
      atTop (𝓝 0) ∧
    (∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0 < mixingTime g (1-ε)) := by
  have hdrift (n : ℕ) (g : Disorder n) (hg : g ∈ G n) (f : Observables n)
      (r : ℝ) (_hr : 0 ≤ r) (y : Spin n) :
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          (-κ + if y ∈ bad n g then A else 0)*
            unweightedGradient (semigroup (coupling g) r f) y := by
    rw [(unweightedGradient_hasDerivAt (coupling g) f y r).deriv]
    exact hgradient n g hg (semigroup (coupling g) r f) y
  obtain ⟨d,c,hd,hc,havoid⟩ := uniform_bad_avoidance G bad hκ hA hχ hK.le hnorm hmlsi hsmall hdrift
  have hav := superpolynomial_bad_avoidance G bad hc havoid
  have hgp : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f := Eventually.of_forall hgap
  have hgd (D : ℝ) (_hD : 0 < D) : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      ∀ f : Observables n, ∀ r ∈ Set.Icc (0:ℝ) (D*Real.log n), ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          (-κ + if y ∈ bad n g then A else 0)*
            unweightedGradient (semigroup (coupling g) r f) y :=
    Eventually.of_forall (fun n g hg f r hr => hdrift n g hg f r hr.1)
  have hrow : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ i, ∑ j, coupling g i j ^ 2 ≤ K^2 := by
    apply Eventually.of_forall
    intro n g hg i
    exact row_squares_le_opNorm (coupling g) (coupling_symm g) hK.le (hnorm n g hg) i
  have hfields := uniform_field_tails_of_small_set G bad hκ hA hd.le hγ (sq_nonneg K) hrow hgp hgd hav
  have hlag := uniform_positive_lag_of_small_set_gradient G bad hκ hA hd.le hγ hgp hgd hav hfields
  have hlo := uniform_median_lower_of_small_set G bad hκ hA hd.le hγ hgp hgd hav
  have hup := uniform_median_upper_of_mlsi G hχ hnorm hmlsi
  apply ratio_cutoff_of_positive_lag β ε η hε hε1 hη G (c := 1/4) (C := 2/χ)
    (by norm_num) hK hnorm hG _ hlag
  filter_upwards [hlo,hup] with n hnlo hnup
  intro g hg
  exact ⟨by simpa only [one_div_mul_eq_div] using hnlo g hg,hnup g hg⟩

end SKRatio.Calculus

end
end

end OAI
