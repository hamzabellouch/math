import OAI.NumberTheory.Ostmann.Supply.CenteredProjection
import OAI.NumberTheory.Ostmann.Supply.SpectralApproximation

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]
local notation "H" => EuclideanSpace ℂ (ZMod p)

def oneVector : H := WithLp.toLp 2 (fun _ => 1)

omit [NeZero p] in
@[simp] theorem oneVector_apply (x : ZMod p) : oneVector x = 1 := rfl

def uniformCoefficient (S : Finset (ZMod p)) : ℝ :=
  Real.sqrt (density S*(1-density S))/(S.card:ℝ)

theorem uniformVector_decomposition (S : Finset (ZMod p))
    (hpos : 0 < density S) (hlt : density S < 1) :
    uniformVector S = (p : ℂ)⁻¹ • oneVector +
      (uniformCoefficient S : ℂ) • normalizedVector S := by
  have hp : (p:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hs : (S.card:ℝ) ≠ 0 := by
    intro hh
    simp [density, hh] at hpos
  have hv : 0 < density S*(1-density S) := mul_pos hpos (sub_pos.mpr hlt)
  have hr : Real.sqrt (density S*(1-density S)) ≠ 0 := (Real.sqrt_pos.mpr hv).ne'
  have hid (a : ℝ) : a/(S.card:ℝ) = (p:ℝ)⁻¹ +
      uniformCoefficient S * ((a-density S)/Real.sqrt (density S*(1-density S))) := by
    unfold uniformCoefficient
    have hcancel : Real.sqrt (density S*(1-density S))/(S.card:ℝ) *
        ((a-density S)/Real.sqrt (density S*(1-density S))) = (a-density S)/(S.card:ℝ) := by
      field_simp
    rw [hcancel]
    simp only [density, ZMod.card]
    field_simp
    ring
  ext x
  simp only [PiLp.add_apply, PiLp.smul_apply, oneVector_apply, normalizedVector_apply,
    uniformVector_apply, smul_eq_mul, mul_one,
    normalizedIndicator, centeredIndicator]
  have hh := congrArg (fun r : ℝ => (r:ℂ)) (hid (if x ∈ S then 1 else 0))
  push_cast at hh
  split_ifs at hh ⊢ with hx <;> simpa using hh

theorem uniformVector_compl_decomposition (S : Finset (ZMod p))
    (hpos : 0 < density S) (hlt : density S < 1) :
    uniformVector Sᶜ = (p : ℂ)⁻¹ • oneVector -
      (uniformCoefficient Sᶜ : ℂ) • normalizedVector S := by
  have hd : density Sᶜ = 1-density S := by
    have hc := Finset.card_add_card_compl S
    rw [ZMod.card p] at hc
    have hp : (p:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
    simp only [density,ZMod.card]
    have hcr : (S.card:ℝ)+(Sᶜ.card:ℝ) = p := by exact_mod_cast hc
    field_simp
    linarith
  have hn : normalizedVector Sᶜ = -normalizedVector S := by
    ext x
    simp only [normalizedVector_apply, PiLp.neg_apply, normalizedIndicator,
      centeredIndicator, hd]
    push_cast
    have hh : (1-density S)*(1-(1-density S)) = density S*(1-density S) := by ring
    rw [hh]
    by_cases hx : x∈S <;> simp [hx] <;> ring
  rw [uniformVector_decomposition Sᶜ (by rw [hd]; linarith) (by rw [hd]; linarith), hn,
    smul_neg, sub_eq_add_neg]

end Ostmann.Supply

end

end OAI
