import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeIteration
import OAI.NumberTheory.Ostmann.Characters.TemplateNormAsymptoticPrecision

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.TemplateAmplitudeIteration
open Filter

theorem amplitude_budget_of_factor (k : ℕ) (B0 B1 m : ℝ) (η d D F : ℕ → ℝ)
    (hd : ∀j,0≤d j) (hη : ∀j,0≤η j) (hD : ∀j,0≤D j)
    (hbudget : (∑j∈Finset.range k,(d j+Real.log 2))≤(B1-B0)*m)
    (hinitial : Real.exp (-B0*m)≤η 0)
    (hfactor : ∀j<k,F j≤Real.exp (d j))
    (htransfer : ∀j<k,(η j)^2≤F j*(D j+η (j+1)))
    (hdiag : ∀j<k,D j≤(1/2:ℝ)*Real.exp (-d j)*Real.exp (-2*B1*(2:ℝ)^j*m)) :
    ∀j≤k,Real.exp (-B1*(2:ℝ)^j*m)≤η j := by
  apply amplitude_budget k B0 B1 m η d D hd hbudget hinitial _ hdiag
  intro j hj
  exact (htransfer j hj).trans (mul_le_mul_of_nonneg_right (hfactor j hj)
    (add_nonneg (hD j) (hη (j+1))))

theorem total_loss_eventually (k : ℕ) {B0 B1 z : ℝ} (hB : B0+1<B1) (hz : 0<z) :
    ∀ᶠ L : ℝ in atTop,∀d : ℕ → ℝ,
      (∑j∈Finset.range k,d j)≤(⌊z*L⌋₊ : ℝ) →
      (∑j∈Finset.range k,(d j+Real.log 2))≤(B1-B0)*(⌊z*L⌋₊ : ℝ) := by
  have hg : 0<B1-B0-1 := by linarith
  have ht := (TemplateNormAsymptotic.word_tendsto hz).const_mul_atTop hg
  filter_upwards [ht.eventually_ge_atTop ((k:ℝ)*Real.log 2)] with L hL
  intro d hd
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  nlinarith

theorem amplitude_budget_eventually (k : ℕ) {B0 B1 z : ℝ}
    (hB : B0+1<B1) (hz : 0<z) :
    ∀ᶠ L : ℝ in atTop,∀η d D F : ℕ → ℝ,
      (∀j,0≤d j) → (∀j,0≤η j) → (∀j,0≤D j) →
      (∑j∈Finset.range k,d j)≤(⌊z*L⌋₊ : ℝ) →
      Real.exp (-B0*(⌊z*L⌋₊ : ℝ))≤η 0 →
      (∀j<k,F j≤Real.exp (d j)) →
      (∀j<k,(η j)^2≤F j*(D j+η (j+1))) →
      (∀j<k,D j≤(1/2:ℝ)*Real.exp (-d j)*
        Real.exp (-2*B1*(2:ℝ)^j*(⌊z*L⌋₊ : ℝ))) →
      ∀j≤k,Real.exp (-B1*(2:ℝ)^j*(⌊z*L⌋₊ : ℝ))≤η j := by
  filter_upwards [total_loss_eventually k hB hz] with L hL
  intro η d D F hd hη hD hsum hinitial hfactor htransfer hdiag
  exact amplitude_budget_of_factor k B0 B1 (⌊z*L⌋₊ : ℝ) η d D F hd hη hD
    (hL d hsum) hinitial hfactor htransfer hdiag

end Ostmann.Characters.TemplateAmplitudeIteration

end

end OAI
