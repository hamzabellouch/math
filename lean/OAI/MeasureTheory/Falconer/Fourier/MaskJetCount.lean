import OAI.MeasureTheory.Falconer.Fourier.InverseMaskJets

namespace OAI

/-! # Polynomial term count in the individual-mask inverse expansion -/

namespace Falconer.MaskJetExpansion
open scoped ContDiff
variable {ι : Type} {d : ℕ} {E H : Type*}
  [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [Fintype ι] in
@[simp] theorem card_mulFixed (S : MaskJetExpansion ι d E) (c : E → ℂ)
    (hc : ContDiff ℝ ∞ c) :
    Fintype.card (S.mulFixed c hc).index = Fintype.card S.index := rfl

omit [Fintype ι] in
@[simp] theorem card_pullback (S : MaskJetExpansion ι d E) (g : H → E)
    (hg : ContDiff ℝ ∞ g) :
    Fintype.card (S.pullback g hg).index = Fintype.card S.index := rfl

omit [Fintype ι] in
theorem card_sum {J : Type} [Fintype J] (S : J → MaskJetExpansion ι d E) :
    Fintype.card (sum S).index = ∑ j, Fintype.card (S j).index :=
  Fintype.card_sigma

theorem card_derivative [DecidableEq ι] (S : MaskJetExpansion ι d E) (v : E) :
    Fintype.card (S.derivative v).index =
      Fintype.card S.index * (1+Fintype.card ι*d) := by
  change Fintype.card (S.index × (Unit ⊕ (ι × Fin d))) = _
  rw [Fintype.card_prod,Fintype.card_sum,Fintype.card_unique (α := Unit),Fintype.card_prod,
    Fintype.card_fin]

theorem card_laplacian [DecidableEq ι] {n : ℕ}
    (S : MaskJetExpansion ι d E) (v : Fin n → E) :
    Fintype.card (S.laplacian v).index =
      Fintype.card S.index * n * (1+Fintype.card ι*d)^2 := by
  rw [laplacian,card_sum]
  simp_rw [card_derivative]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

theorem card_iteratedLaplacian [DecidableEq ι] {n : ℕ}
    (S : MaskJetExpansion ι d E) (v : Fin n → E) (j : ℕ) :
    Fintype.card (S.iteratedLaplacian v j).index =
      Fintype.card S.index * n^j * (1+Fintype.card ι*d)^(2*j) := by
  induction j with
  | zero =>
    change Fintype.card S.index = _
    simp only [Nat.mul_zero,pow_zero,Nat.mul_one]
  | succ j ih =>
    change Fintype.card (((fun T : MaskJetExpansion ι d E => T.laplacian v)^[j+1]) S).index = _
    rw [Function.iterate_succ_apply',card_laplacian]
    change Fintype.card (S.iteratedLaplacian v j).index * _ * _ = _
    rw [ih,show 2*(j+1)=2*j+2 by omega,pow_add,pow_succ]
    ring

theorem card_stationaryJet [DecidableEq ι] (m j : ℕ)
    (S : MaskJetExpansion ι d (Space (m+3))) :
    Fintype.card (S.stationaryJet m j).index =
      Fintype.card S.index * (m+2)^j * (1+Fintype.card ι*d)^(2*j) := by
  change Fintype.card
    ((((S.pullback (safeStationaryChart m) (safeStationaryChart_contDiff m)).mulFixed
      (SmoothSeparation.stationaryJointDensity m)
      (SmoothSeparation.stationaryJointDensity_contDiff m)).iteratedLaplacian
        (verticalDirections (m+2)) j)).index = _
  rw [card_iteratedLaplacian]
  rfl

def inverseMultiplicity (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | j+1 => ∑ h : Fin (j+1), inverseMultiplicity n (j-h) * n^((h:ℕ)+1)
termination_by j => j
decreasing_by omega

theorem card_inverse [DecidableEq ι] (m j : ℕ)
    (S : MaskJetExpansion ι d (Space (m+3))) :
    Fintype.card (S.inverse m j).index =
      Fintype.card S.index * inverseMultiplicity (m+2) j *
        (1+Fintype.card ι*d)^(2*j) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => simp [MaskJetExpansion.inverse,inverseMultiplicity]
    | succ j =>
      rw [MaskJetExpansion.inverse,card_mulFixed,card_sum,inverseMultiplicity]
      simp_rw [card_stationaryJet]
      have hterm (h : Fin (j+1)) :
          Fintype.card (S.inverse m (j-h)).index * (m+2)^((h:ℕ)+1) *
            (1+Fintype.card ι*d)^(2*((h:ℕ)+1)) =
          Fintype.card S.index * (1+Fintype.card ι*d)^(2*(j+1)) *
            (inverseMultiplicity (m+2) (j-h) * (m+2)^((h:ℕ)+1)) := by
        rw [ih (j-h) (by have hh := h.isLt; omega)]
        have hp : 2*(j-h)+2*((h:ℕ)+1) = 2*(j+1) := by have hh := h.isLt; omega
        rw [← hp,pow_add]
        ring
      simp_rw [hterm]
      rw [← Finset.mul_sum]
      ring

theorem card_inverse_product [DecidableEq ι] (m j : ℕ) :
    Fintype.card ((product : MaskJetExpansion ι (m+3) (Space (m+3))).inverse m j).index =
      inverseMultiplicity (m+2) j * (1+Fintype.card ι*(m+3))^(2*j) := by
  rw [card_inverse]
  change 1 * _ * _ = _
  rw [one_mul]

end Falconer.MaskJetExpansion

end OAI
