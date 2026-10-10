import Mathlib
import OAI.Probability.SKBarriers.Parisi.QuantileLipschitz

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

def quantileFirstMoment (k : ℕ) (Q : Fin (k+1) → ℝ) : ℝ :=
  ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*Q j

def quantileSecondMoment (k : ℕ) (Q : Fin (k+1) → ℝ) : ℝ :=
  ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q j)^2

theorem quantileFirstMoment_nonneg (k : ℕ) (Q : Fin (k+1) → ℝ) (hQ : ∀ j, 0 ≤ Q j) :
    0 ≤ quantileFirstMoment k Q :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (hQ j))

theorem quantileSecondMoment_nonneg (k : ℕ) (Q : Fin (k+1) → ℝ) :
    0 ≤ quantileSecondMoment k Q :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (by positivity) (sq_nonneg _))

theorem quantileFirstMoment_sq_le (k : ℕ) (Q : Fin (k+1) → ℝ) :
    (quantileFirstMoment k Q)^2 ≤ quantileSecondMoment k Q := by
  let a := quantileFirstMoment k Q
  have H : 0 ≤ ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q j-a)^2 :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (by positivity) (sq_nonneg _))
  have he (j : Fin (k+1)) : ((k+1:ℕ):ℝ)⁻¹*(Q j-a)^2 =
      ((k+1:ℕ):ℝ)⁻¹*(Q j)^2-(2*a)*(((k+1:ℕ):ℝ)⁻¹*Q j)+a^2*((k+1:ℕ):ℝ)⁻¹ := by ring
  simp_rw [he] at H
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib] at H
  have h1 : (∑ j : Fin (k+1), (2*a)*(((k+1:ℕ):ℝ)⁻¹*Q j)) = (2*a)*a := by
    rw [← Finset.mul_sum]
    rfl
  have h2 : (∑ _j : Fin (k+1), a^2*((k+1:ℕ):ℝ)⁻¹) = a^2 := by
    rw [← Finset.mul_sum,uniformAtom_sum,mul_one]
  rw [h1,h2] at H
  change 0 ≤ quantileSecondMoment k Q-(2*a)*a+a^2 at H
  dsimp only [a] at H
  nlinarith

theorem scalarHierarchy_zero_variance (n : ℕ) (m : Fin n → ℝ) (f : ℝ → ℝ) :
    scalarHierarchy n m (fun _ => 0) f = f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [scalarHierarchy,scalarStep_zero]
    exact ih _ f

theorem extendedQuantileParisi_zero (k : ℕ) (β : ℝ) :
    extendedQuantileParisi k β (fun _ => 0) = Real.log 2+β^2/4 := by
  have hg : cumulativeGapMap k (fun _ => 0) = 0 := map_zero _
  have he : (fun b => β*Real.sqrt (cumulativeGapMap k (fun _ => 0) b)) = fun _ => 0 := by
    rw [hg]
    simp
  rw [extendedQuantileParisi,he,scalarHierarchy_zero_variance]
  simp [scalarSpinTerminal]

theorem quantileSecondMoment_of_gap {k : ℕ} {β δ : ℝ} (hβ : 0 < β) (hδ : 0 ≤ δ)
    (Q : Fin (k+1) → ℝ) (hm : Monotone Q) (hQ : ∀ j, Q j ∈ Set.Icc 0 1)
    (hgap : extendedQuantileParisi k β Q ≤ Real.log 2+β^2/4-δ) :
    (2*δ/β^2)^2 ≤ quantileSecondMoment k Q := by
  have H := extendedQuantileParisi_lipschitz β (fun _ => 0) Q
    (fun _ => ⟨le_rfl,zero_le_one⟩) hQ monotone_const hm
  rw [extendedQuantileParisi_zero] at H
  simp only [sub_zero,abs_of_nonneg (hQ _).1] at H
  have H' := neg_le_abs (extendedQuantileParisi k β Q-(Real.log 2+β^2/4))
  have hmean : 2*δ/β^2 ≤ quantileFirstMoment k Q := by
    apply (div_le_iff₀ (sq_pos_of_pos hβ)).mpr
    change _ ≤ (β^2/2)*quantileFirstMoment k Q at H
    nlinarith
  apply le_trans _ (quantileFirstMoment_sq_le k Q)
  apply sq_le_sq.mpr
  rw [abs_of_nonneg (by positivity : 0 ≤ 2*δ/β^2),
    abs_of_nonneg (quantileFirstMoment_nonneg k Q (fun j => (hQ j).1))]
  exact hmean

theorem extendedQuantileParisi_temperature_rescale {k : ℕ} {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (Q : Fin (k+1) → ℝ) :
    extendedQuantileParisi k γ ((β/γ)^2 • Q) = extendedQuantileParisi k β Q+
      (γ^2-β^2)/4*(1-(β^2/γ^2)*quantileSecondMoment k Q) := by
  have he (j : Fin (k+1)) : γ*Real.sqrt (cumulativeGapMap k ((β/γ)^2 • Q) j) =
      β*Real.sqrt (cumulativeGapMap k Q j) := by
    simp only [map_smul,Pi.smul_apply,smul_eq_mul]
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (div_nonneg hβ.le hγ.le)]
    field_simp
  have hs : (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(((β/γ)^2 • Q) j)^2) =
      (β/γ)^4*quantileSecondMoment k Q := by
    unfold quantileSecondMoment
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  simp only [extendedQuantileParisi,he]
  rw [hs]
  rw [show (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q j)^2) = quantileSecondMoment k Q from rfl]
  simp only [Pi.smul_apply,smul_eq_mul]
  field_simp [hγ.ne']
  ring

theorem rescaledQuantiles_admissible {k : ℕ} {β γ : ℝ} (hβ : 0 < β) (hβγ : β ≤ γ)
    (Q : Fin (k+1) → ℝ) (hm : Monotone Q) (hQ : ∀ j, Q j ∈ Set.Icc 0 1) :
    Monotone ((β/γ)^2 • Q) ∧ ∀ j, ((β/γ)^2 • Q) j ∈ Set.Icc 0 1 := by
  have hγ : 0 < γ := hβ.trans_le hβγ
  have ha : (β/γ)^2 ≤ 1 := by
    apply (sq_le_one_iff_abs_le_one _).mpr
    rw [abs_of_nonneg (div_nonneg hβ.le hγ.le)]
    exact (div_le_one hγ).mpr hβγ
  constructor
  · intro i j hij
    exact mul_le_mul_of_nonneg_left (hm hij) (sq_nonneg _)
  · intro j
    change (β/γ)^2*Q j ∈ Set.Icc 0 1
    constructor
    · exact mul_nonneg (sq_nonneg _) (hQ j).1
    · exact (mul_le_of_le_one_right (sq_nonneg _) (hQ j).2).trans ha
end SK.Analytic

end
end

end

end OAI
