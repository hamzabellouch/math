import OAI.NumberTheory.Ostmann.ZeroDensity.ActualDetector
import OAI.NumberTheory.Ostmann.ZeroDensity.ActualZeros
import OAI.NumberTheory.Ostmann.ZeroDensity.DyadicDetector
import OAI.NumberTheory.Ostmann.ZeroDensity.VaryingSampling

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.ZeroDensity

theorem exists_selected_zero_density_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q H : ℕ) (exception : Option (PrimitiveFamily Q))
      (σ : ℝ) (r : Finset (ZeroOccurrence Q (H : ℝ))),
      0 < Q → 0 < H → 1/2 ≤ σ → σ ≤ 1 →
      r ⊆ retainedZeros Q exception σ H →
      (∀ z ∈ r, ∀ w ∈ r, z ≠ w → z.1 = w.1 → 1 ≤ |z.point.im-w.point.im|) →
      (r.card : ℝ) ≤
        4*C*(detectorBlockCount (detectorLength Q H (Q^2*H)) : ℝ) *
          ∑ j ∈ Finset.range (detectorBlockCount (detectorLength Q H (Q^2*H))),
            (((2^j*(Q^2*H) : ℕ) : ℝ)+(Q : ℝ)^2*H) * (1+Real.log Q) *
              (1+Real.log (2*(2^j*(Q^2*H) : ℕ) : ℝ))^7 *
                (2^j*(Q^2*H) : ℕ) * ((2^j*(Q^2*H) : ℕ) : ℝ)^(-2*σ) := by
  classical
  obtain ⟨C,hC,hsample⟩ := exists_mollifier_varying_sampling_constant
  refine ⟨C,hC,?_⟩
  intro Q H exception σ r hQ hH hσ hσ1 hrs hsep
  let X : ℕ := Q^2*H
  let N : ℕ := detectorLength Q H X
  let J : ℕ := detectorBlockCount N
  have hX : 1 ≤ X := by
    have hxpos : 0 < X := by dsimp [X]; positivity
    omega
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  let χ : r → Ostmann.HybridSieve.PrimitiveFamily Q := fun z => z.val.1.1
  let β : r → ℝ := fun z => z.val.point.re
  let γ : r → ℝ := fun z => z.val.point.im
  have hβ (z : r) : β z ∈ Set.Icc σ 1 :=
    ⟨(Finset.mem_filter.mp (hrs z.property)).2.2, z.val.isNontrivialZero.2.2.le⟩
  have hγ (z : r) : |γ z| ≤ (H : ℝ) := z.val.2.1.property.2
  have hspacing (z w : r) (hne : z ≠ w) (hc : χ z = χ w) : 1 ≤ |γ z-γ w| := by
    exact hsep z.val z.property w.val w.property
      (fun heq => hne (Subtype.ext heq)) (Subtype.ext hc)
  have hblock (j : ℕ) :
      (∑ z : r, ‖detectorBlock (χ z).2.val X N j z.val.point‖^2) ≤
        C * (((2^j*X : ℕ) : ℝ)+(Q : ℝ)^2*H) * (1+Real.log Q) *
          (1+Real.log (2*(2^j*X : ℕ) : ℝ))^7 *
            (2^j*X : ℕ) * ((2^j*X : ℕ) : ℝ)^(-2*σ) := by
    have hU : 0 < 2^j*X := by positivity
    have hb := hsample (2^j*X) Q X N σ H χ β γ hU hQ hHR
      (by linarith) hσ1 hβ hγ hspacing
    have heq (z : r) :
        finiteCharacterPolynomial (χ z).2.val (mollifierCoefficient X N)
          (Finset.Ioc (2^j*X) (2*(2^j*X))) ((β z : ℂ)+(γ z : ℂ)*Complex.I) =
        detectorBlock (χ z).2.val X N j z.val.point := by
      have hp : 2*(2^j*X) = 2^(j+1)*X := by ring
      simp only [finiteCharacterPolynomial, detectorBlock, hp, β, γ, Complex.re_add_im]
    simpa only [heq] using hb
  have hdetect := detected_family_card_le (Finset.univ : Finset r) J
    (fun z j => detectorBlock (χ z).2.val X N j z.val.point) (by
      intro z hz
      rw [← detector_eq_sum_blocks (χ z).2.val X N J (detectorBlockCount_covers N)]
      apply actual_zero_detector (χ z).2.val z.val.1.property
        (by have ht := z.val.1.1.1.isLt; omega) hH hX z.val.isNontrivialZero.1
      · exact hσ.trans (hβ z).1
      · exact (hβ z).2
      · exact hγ z)
  have hsum := Finset.sum_le_sum (fun j (_hj : j ∈ Finset.range J) => hblock j)
  have hJ : (0 : ℝ) ≤ 4*J := by positivity
  calc
    (r.card : ℝ) ≤ 4*J*∑ j ∈ Finset.range J,
        ∑ z : r, ‖detectorBlock (χ z).2.val X N j z.val.point‖^2 := by
      simpa using hdetect
    _ ≤ 4*J*∑ j ∈ Finset.range J,
        C * (((2^j*X : ℕ) : ℝ)+(Q : ℝ)^2*H) * (1+Real.log Q) *
          (1+Real.log (2*(2^j*X : ℕ) : ℝ))^7 *
            (2^j*X : ℕ) * ((2^j*X : ℕ) : ℝ)^(-2*σ) :=
      mul_le_mul_of_nonneg_left hsum hJ
    _ = _ := by
      dsimp [X, N, J]
      simp only [mul_assoc, ← Finset.mul_sum]
      ring

end Ostmann.ZeroDensity

end

end OAI
