import Mathlib
import OAI.Probability.CriticalPercolation.Harmonic.HarmonicFunctionSpace
import OAI.Probability.CriticalPercolation.Harmonic.CayleyPoincare
import OAI.Probability.CriticalPercolation.Growth.WordBallPacking
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteCoverSums
import OAI.Probability.CriticalPercolation.Harmonic.CayleyCaccioppoli

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A : Type*} [Group A] (W : WordGeometry A)

lemma squareMass_around (a : A) (r : ℕ) (u : A → ℝ) :
    squareMass (W.around a r) u = squareMass (W.ball r) (fun x => u (a*x)) := by
  unfold squareMass around
  rw [Finset.sum_image]
  intro x _ y _ h
  exact mul_left_cancel h

lemma energy_around (a : A) (r : ℕ) (u : A → ℝ) :
    energy W.generators (W.around a r) u =
      energy W.generators (W.ball r) (fun x => u (a*x)) := by
  unfold energy around
  rw [Finset.sum_image]
  · simp only [mul_assoc]
  · intro x _ y _ h
    exact mul_left_cancel h

lemma sum_around (a : A) (r : ℕ) (u : A → ℝ) :
    (∑ x∈W.around a r, u x) = ∑ y∈W.ball r, u (a*y) := by
  unfold around
  rw [Finset.sum_image]
  intro x _ y _ h
  exact mul_left_cancel h

lemma translated_poincare (a : A) (r K : ℕ) (u : A → ℝ)
    (hvol : (W.ball (7*r)).card≤K*(W.ball r).card)
    (hu : (∑ x∈W.around a (2*r), u x)=0) :
    squareMass (W.around a (2*r)) u ≤
      8*(r:ℝ)^2*(K:ℝ)*energy W.generators (W.around a (6*r)) u := by
  rw [W.sum_around] at hu
  have hp := word_ball_poincare W.generators W.one_mem W.inv_eq
    (fun x => u (a*x)) (2*r) hu
  change ((W.ball (2*r)).card:ℝ)*squareMass (W.ball (2*r)) (fun x => u (a*x)) ≤ _ at hp
  rw [←W.squareMass_around] at hp
  have he : energy W.generators (W.generators^(3*(2*r))) (fun x => u (a*x)) =
      energy W.generators (W.around a (6*r)) u := by
    rw [W.energy_around]
    congr 1
    change W.generators^(3*(2*r))=W.generators^(6*r)
    congr 1; omega
  rw [he] at hp
  have hv : (W.generators^(2*(2*r))).card≤K*(W.ball (2*r)).card := by
    calc
      _ ≤ (W.ball (7*r)).card := Finset.card_le_card (W.ball_mono (by omega))
      _ ≤ _ := hvol.trans (Nat.mul_le_mul_left _ (Finset.card_le_card (W.ball_mono (by omega))))
  have hv' : ((W.generators^(2*(2*r))).card:ℝ)≤(K:ℝ)*((W.ball (2*r)).card:ℝ) := by exact_mod_cast hv
  have hbpos : (0:ℝ)<(W.ball (2*r)).card := by exact_mod_cast W.ball_card_pos (2*r)
  have hepos := energy_nonneg W.generators (W.around a (6*r)) u
  have hm := mul_le_mul_of_nonneg_right hv' (mul_nonneg (sq_nonneg (r:ℝ)) hepos)
  push_cast at hp
  nlinarith

lemma cover_mass_energy (R r K : ℕ) (J : Finset A)
    (hJR : J⊆W.ball R)
    (hJ : (J:Set A).PairwiseDisjoint (fun a => W.around a r))
    (hcover : ∀ x∈W.ball R, ∃ a∈J, x∈W.around a (2*r))
    (hvol : (W.ball (7*r)).card≤K*(W.ball r).card)
    (u : A → ℝ) (hu : ∀ a∈J, (∑ x∈W.around a (2*r), u x)=0) :
    squareMass (W.ball R) u ≤
      8*(r:ℝ)^2*(K:ℝ)^2*energy W.generators (W.ball (R+6*r)) u := by
  have hcover' := sum_le_sum_of_finite_cover J (fun a => W.around a (2*r))
    (W.ball R) hcover (fun x => (u x)^2) (fun x => sq_nonneg _)
  have hpsum := Finset.sum_le_sum (fun a (ha : a∈J) => W.translated_poincare a r K u hvol (hu a ha))
  have hsub : ∀ a∈J, W.around a (6*r)⊆W.ball (R+6*r) :=
    fun a ha => W.around_subset_ball (hJR ha)
  have hover : ∀ x∈W.ball (R+6*r), (J.filter (fun a => x∈W.around a (6*r))).card≤K := by
    intro x _
    apply W.packing_overlap J r (6*r) K hJ
    simpa only [show 6*r+r=7*r by omega] using hvol
  have he := sum_le_sum_of_finite_overlap J (fun a => W.around a (6*r))
    (W.ball (R+6*r)) hsub K hover
    (fun x => ∑ s∈W.generators, (u (x*s)-u x)^2)
    (fun x => Finset.sum_nonneg (fun s _ => sq_nonneg _))
  change (∑ a∈J, energy W.generators (W.around a (6*r)) u)≤
    (K:ℝ)*energy W.generators (W.ball (R+6*r)) u at he
  simp only [←Finset.mul_sum] at hpsum
  change squareMass (W.ball R) u≤∑ a∈J, squareMass (W.around a (2*r)) u at hcover'
  have hm := mul_le_mul_of_nonneg_left he (by positivity : 0≤8*(r:ℝ)^2*(K:ℝ))
  calc
    _ ≤ _ := hcover'.trans hpsum
    _ ≤ _ := by nlinarith

theorem harmonic_cover_kernel_bound (R r K : ℕ) (hR : 1≤R) (hrR : 6*r≤R)
    (J : Finset A) (hJR : J⊆W.ball R)
    (hJ : (J:Set A).PairwiseDisjoint (fun a => W.around a r))
    (hcover : ∀ x∈W.ball R, ∃ a∈J, x∈W.around a (2*r))
    (hvol : (W.ball (7*r)).card≤K*(W.ball r).card)
    (u : A → ℝ) (hharm : W.IsHarmonic u)
    (hu : ∀ a∈J, (∑ x∈W.around a (2*r), u x)=0) :
    (R:ℝ)^2*squareMass (W.ball R) u ≤
      8*(K:ℝ)^2*(W.generators.card:ℝ)*(r:ℝ)^2*squareMass (W.ball (5*R)) u := by
  have hp := W.cover_mass_energy R r K J hJR hJ hcover hvol u hu
  have hem := energy_mono W.generators (W.ball_mono (show R+6*r≤2*R by omega)) u
  have hm := mul_le_mul_of_nonneg_left hem (by positivity : 0≤8*(r:ℝ)^2*(K:ℝ)^2)
  have hp' : squareMass (W.ball R) u≤8*(r:ℝ)^2*(K:ℝ)^2*energy W.generators (W.ball (2*R)) u := hp.trans hm
  have hc := W.caccioppoli u hharm (2*R)
  have hqm := squareMass_mono (W.ball_mono (show 2*(2*R)+1≤5*R by omega)) u
  have hq := mul_le_mul_of_nonneg_left hqm (by positivity : 0≤4*(W.generators.card:ℝ))
  have hc' : (R:ℝ)^2*energy W.generators (W.ball (2*R)) u≤
      (W.generators.card:ℝ)*squareMass (W.ball (5*R)) u := by
    push_cast at hc
    nlinarith
  have hm' := mul_le_mul_of_nonneg_left hp' (sq_nonneg (R:ℝ))
  have hm'' := mul_le_mul_of_nonneg_left hc' (by positivity : 0≤8*(r:ℝ)^2*(K:ℝ)^2)
  nlinarith

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
