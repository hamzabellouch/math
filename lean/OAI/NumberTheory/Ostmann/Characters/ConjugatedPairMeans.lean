import OAI.NumberTheory.Ostmann.Characters.MixedQuartetBounds
import OAI.NumberTheory.Ostmann.Tree.SamePairMeanBounds

namespace OAI

/-! # The same-pair bounds uniformly in the manuscript's conjugation choices -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable local instance conjugatedPairMeansFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

theorem norm_pairConjugate {p : ℕ} (g : ZMod p → ℂ) (c : Bool) (x : ZMod p) :
    ‖pairConjugate g c x‖ = ‖g x‖ := by cases c <;> simp [pairConjugate]

theorem pairConjugate_zero {p : ℕ} (g : ZMod p → ℂ) (hg : g 0 = 0) (c : Bool) :
    pairConjugate g c 0 = 0 := by cases c <;> simp [pairConjugate, hg]

theorem MixedFourierBound.pairConjugate {p : ℕ} [Fact p.Prime]
    {g : ZMod p → ℂ} {ε : ℝ} (hg : MixedFourierBound g ε) (c : Bool) :
    MixedFourierBound (pairConjugate g c) ε := by
  cases c
  · exact hg
  · exact hg.conj

theorem MixedFourierBound.characterTwist {p : ℕ} [Fact p.Prime]
    {g : ZMod p → ℂ} {ε : ℝ} (hg : MixedFourierBound g ε)
    (χ : MulChar (ZMod p) ℂ) (a : ZMod p) :
    ‖additiveFourier (characterTwist g χ) a‖ ≤ ε := by
  have he : Ostmann.characterTwist g χ = fun x => g x * χ⁻¹ x := by
    funext x
    exact congrArg (fun z => g x * z) (MulChar.star_apply' χ x)
  rw [he]
  exact hg χ⁻¹ a

theorem conjugated_samePairMajorant_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0) (ε : ℝ) (hε : 0 ≤ ε)
    (hflat : MixedFourierBound g ε)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (cL cR : Bool) (ρ : MulChar (ZMod p) ℂ) :
    (∑ y : (ZMod p)ˣ, samePairMajorant
      (fieldPairCoefficientMoment (pairConjugate g cL))
      (fieldPairMoment (pairConjugate g cR)) ρ y) / (Fintype.card (ZMod p)ˣ : ℝ) ≤
      2 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 5 * ε ^ 2 := by
  have he (c : Bool) : (∑ x : ZMod p, ‖pairConjugate g c x‖ ^ 2) ≤ (p : ℝ) := by
    simpa only [norm_pairConjugate] using henergy
  have h := samePairMajorant_mean_le
    (fieldPairCoefficientMoment (pairConjugate g cL))
    (fieldPairMoment (pairConjugate g cR)) (fun _ _ => sq_nonneg _)
    (fieldPairMoment_nonneg _) (((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 3 * ε ^ 2)
    (((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2) (by positivity)
    (fun χ => fieldPairCoefficientMoment_mean_le _ (pairConjugate_zero g hg cL) χ ε hε
      ((hflat.pairConjugate cL).characterTwist χ) (he cL))
    (fieldPairMoment_mean_le _ (pairConjugate_zero g hg cR) (he cR)) ρ
  convert h using 1
  ring

theorem conjugated_samePairMajorant_total_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) (cL cR : Bool) :
    (∑ ρ : MulChar (ZMod p) ℂ, (∑ y : (ZMod p)ˣ, samePairMajorant
      (fieldPairCoefficientMoment (pairConjugate g cL))
      (fieldPairMoment (pairConjugate g cR)) ρ y) / (Fintype.card (ZMod p)ˣ : ℝ)) ≤
      ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4 := by
  have he (c : Bool) : (∑ x : ZMod p, ‖pairConjugate g c x‖ ^ 2) ≤ (p : ℝ) := by
    simpa only [norm_pairConjugate] using henergy
  have h := samePairMajorant_total_mean_le
    (fieldPairCoefficientMoment (pairConjugate g cL))
    (fieldPairMoment (pairConjugate g cR)) (fun _ _ => sq_nonneg _)
    (fieldPairMoment_nonneg _) (((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2)
    (((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2) (sq_nonneg _)
    (fieldPairCoefficientMoment_total_mean_le _ (pairConjugate_zero g hg cL) (he cL))
    (fieldPairMoment_mean_le _ (pairConjugate_zero g hg cR) (he cR))
  convert h using 1
  ring

end Ostmann

end OAI
