import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedMassSeries
import OAI.NumberTheory.CubicMoment.Estimates.NormSeries

namespace OAI

/-! Absolute convergence and factorization of the literal coefficient mass.
The unramified factors retain the primary and squarefree restrictions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

abbrev CubicThetaSquarefreePrimary := {c : Eisenstein // primary c ∧ Squarefree c}

def cubicThetaPrimaryMass (t : ℝ) : ℝ :=
  ∑' d : PrimaryArgument, (norm d.val)^(-t)

def cubicThetaSquarefreeMass (t : ℝ) : ℝ :=
  ∑' c : CubicThetaSquarefreePrimary, (norm c.val)^(-t)

def cubicThetaMassPairEquiv : CubicThetaPrimaryPair ≃
    CubicThetaSquarefreePrimary × PrimaryArgument where
  toFun cd := (⟨cd.val.1,cd.property.1,cd.property.2.2⟩,⟨cd.val.2,cd.property.2.1⟩)
  invFun cd := ⟨(cd.1.val,cd.2.val),cd.1.property.1,cd.2.property,cd.1.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma cubicThetaPrimaryMass_summable {t : ℝ} (ht : 1 < t) :
    Summable (fun d : PrimaryArgument => (norm d.val)^(-t)) :=
  (summable_eisenstein_norm_rpow ht).subtype _

lemma cubicThetaSquarefreeMass_summable {t : ℝ} (ht : 1 < t) :
    Summable (fun c : CubicThetaSquarefreePrimary => (norm c.val)^(-t)) :=
  (summable_eisenstein_norm_rpow ht).subtype _

def cubicThetaPairMassTerm (σ : ℝ) (cd : CubicThetaPrimaryPair) : ℝ :=
  (norm cd.val.1)^(-(1+σ)) * (norm cd.val.2)^(-(2+3*σ))

lemma cubicThetaPairMassTerm_nonneg (σ : ℝ) (cd : CubicThetaPrimaryPair) :
    0 ≤ cubicThetaPairMassTerm σ cd := by
  exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
    (Real.rpow_nonneg (norm_nonneg _) _)

lemma cubicThetaPairMassTerm_summable {σ : ℝ} (hσ : 0 < σ) :
    Summable (cubicThetaPairMassTerm σ) := by
  have hc := cubicThetaSquarefreeMass_summable (show 1 < 1+σ by linarith)
  have hd := cubicThetaPrimaryMass_summable (show 1 < 2+3*σ by linarith)
  have hp := summable_mul_of_summable_norm hc.norm hd.norm
  have he := hp.comp_injective cubicThetaMassPairEquiv.injective
  exact he.congr (fun _ => rfl)

lemma cubicThetaPairMassTerm_sum {σ : ℝ} (hσ : 0 < σ) :
    (∑' cd, cubicThetaPairMassTerm σ cd) =
      cubicThetaSquarefreeMass (1+σ) * cubicThetaPrimaryMass (2+3*σ) := by
  have hc := cubicThetaSquarefreeMass_summable (show 1 < 1+σ by linarith)
  have hd := cubicThetaPrimaryMass_summable (show 1 < 2+3*σ by linarith)
  rw [←cubicThetaMassPairEquiv.symm.tsum_eq (cubicThetaPairMassTerm σ)]
  change (∑' cd : CubicThetaSquarefreePrimary × PrimaryArgument,
    (norm cd.1.val)^(-(1+σ)) * (norm cd.2.val)^(-(2+3*σ))) = _
  exact (tsum_mul_tsum_of_summable_norm hc.norm hd.norm).symm

lemma cubicThetaRamifiedMass_summable {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun p : Eisensteinˣ × ℕ => cubicThetaRamifiedMass σ p.1 p.2) := by
  have : Finite Eisensteinˣ := Nat.finite_of_card_ne_zero (by rw [eisenstein_units_card]; norm_num)
  have h : Summable (fun p : ℕ × Eisensteinˣ => cubicThetaRamifiedMass σ p.2 p.1) := by
    apply (summable_prod_of_nonneg (fun p => cubicThetaRamifiedMass_nonneg σ _ _)).2
    exact ⟨fun _ => Summable.of_finite,cubicThetaRamifiedMass_sum_summable hσ⟩
  exact h.prod_symm

lemma cubicThetaRamifiedMass_total {σ : ℝ} (hσ : 0 < σ) :
    (∑' p : Eisensteinˣ × ℕ, cubicThetaRamifiedMass σ p.1 p.2) =
      6*3^(8:ℝ)*((1-cubicThetaRamifiedRatio σ)⁻¹-1) +
      2*3^(8-σ)*(1-cubicThetaRamifiedRatio σ)⁻¹ := by
  have h := cubicThetaRamifiedMass_summable hσ
  have hc : Summable (Function.uncurry
      (fun u : Eisensteinˣ => fun k : ℕ => cubicThetaRamifiedMass σ u k)) := h
  calc
    _ = ∑' u : Eisensteinˣ, ∑' k : ℕ, cubicThetaRamifiedMass σ u k := h.tsum_prod
    _ = ∑' k : ℕ, ∑' u : Eisensteinˣ, cubicThetaRamifiedMass σ u k := hc.tsum_comm.symm
    _ = _ := cubicThetaRamifiedMass_sum hσ

lemma cubicThetaCoefficientMassTerm_common (σ : ℝ) (x : CubicThetaCommonIndex) :
    cubicThetaCoefficientMassTerm σ (cubicThetaCommonNumerator x) =
      cubicThetaRamifiedMass σ x.1 x.2.1 * cubicThetaPairMassTerm σ x.2.2 := by
  rw [(cubicThetaCommonCoordinates x).mass_term σ]
  simp only [cubicThetaCommonCoordinates,cubicThetaRamifiedMass,cubicThetaPairMassTerm]
  split_ifs <;> simp_all [mul_assoc]

lemma cubicThetaCoefficientMass_common_summable {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun x : CubicThetaCommonIndex =>
      cubicThetaCoefficientMassTerm σ (cubicThetaCommonNumerator x)) := by
  have hr := cubicThetaRamifiedMass_summable hσ
  have hp := cubicThetaPairMassTerm_summable hσ
  have h := summable_mul_of_summable_norm hr.norm hp.norm
  have he := h.comp_injective (Equiv.prodAssoc Eisensteinˣ ℕ CubicThetaPrimaryPair).symm.injective
  simp only [Function.comp_def,Equiv.prodAssoc_symm_apply] at he
  simpa only [cubicThetaCoefficientMassTerm_common] using he

lemma cubicThetaCoefficientMassTerm_summable {σ : ℝ} (hσ : 0 < σ) :
    Summable (cubicThetaCoefficientMassTerm σ) := by
  apply (cubicThetaCommonNumerator_injective.summable_iff (f := cubicThetaCoefficientMassTerm σ) ?_).mp
    (cubicThetaCoefficientMass_common_summable hσ)
  intro n hn
  have hnone : ¬Nonempty (CubicThetaCoordinates n) := fun h =>
    hn ((cubicThetaCommonNumerator_range n).mpr h)
  simp [cubicThetaCoefficientMassTerm,cubicThetaArithmeticCoefficient,hnone]


theorem cubicThetaCoefficientMass_factorization {σ : ℝ} (hσ : 0 < σ) :
    cubicThetaCoefficientMass σ =
      (6*3^(8:ℝ)*((1-cubicThetaRamifiedRatio σ)⁻¹-1) +
       2*3^(8-σ)*(1-cubicThetaRamifiedRatio σ)⁻¹) *
      cubicThetaSquarefreeMass (1+σ) * cubicThetaPrimaryMass (2+3*σ) := by
  rw [cubicThetaCoefficientMass_reindex]
  simp_rw [cubicThetaCoefficientMassTerm_common]
  rw [←(Equiv.prodAssoc Eisensteinˣ ℕ CubicThetaPrimaryPair).tsum_eq
    (fun x : CubicThetaCommonIndex =>
      cubicThetaRamifiedMass σ x.1 x.2.1 * cubicThetaPairMassTerm σ x.2.2)]
  change (∑' x : (Eisensteinˣ × ℕ) × CubicThetaPrimaryPair,
    cubicThetaRamifiedMass σ x.1.1 x.1.2 * cubicThetaPairMassTerm σ x.2) = _
  rw [←tsum_mul_tsum_of_summable_norm (cubicThetaRamifiedMass_summable hσ).norm
    (cubicThetaPairMassTerm_summable hσ).norm,
    cubicThetaRamifiedMass_total hσ,cubicThetaPairMassTerm_sum hσ]
  exact (mul_assoc _ _ _).symm

end CubicFirstMoment

end

end OAI
