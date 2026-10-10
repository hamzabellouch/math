import Mathlib
import OAI.Analysis.AffineBernstein.HessianVariation
import OAI.Analysis.AffineBernstein.FlatWeightedEuler

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι κ : Type*}

lemma flatBlockHessian_neg (φ : E → ℝ) (v : ι → E) (x : E) :
    flatBlockHessian (fun y => -φ y) v x = -flatBlockHessian φ v x := by
  ext i j
  have he : dirDeriv (v j) (fun y => -φ y) = fun y => -dirDeriv (v j) φ y := by
    funext y
    simp [dirDeriv]
  change fderiv ℝ (dirDeriv (v j) (fun y => -φ y)) x (v i) =
    -fderiv ℝ (dirDeriv (v j) φ) x (v i)
  rw [he,fderiv_fun_neg]
  rfl

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def flatBaseEulerWeight (B : E → Matrix ι ι ℝ) (R : E → Matrix κ κ ℝ) (δ : ℝ)
    (x : E) : ℝ := -δ * Real.rpow (B x).det (δ-1) * Real.rpow (R x).det (1-δ)

def flatAngularEulerWeight (B : E → Matrix ι ι ℝ) (R : E → Matrix κ κ ℝ) (δ : ℝ)
    (x : E) : ℝ := (1-δ) * Real.rpow (B x).det δ * Real.rpow (R x).det (-δ)

lemma contDiffAt_flatEulerWeights {B : E → Matrix ι ι ℝ} {R : E → Matrix κ κ ℝ}
    {x : E} (hB : ContDiffAt ℝ ∞ (fun y i j => B y i j) x)
    (hR : ContDiffAt ℝ ∞ (fun y i j => R y i j) x)
    (hBd : (B x).det ≠ 0) (hRd : (R x).det ≠ 0) (δ : ℝ) :
    ContDiffAt ℝ ∞ (flatBaseEulerWeight B R δ) x ∧
      ContDiffAt ℝ ∞ (flatAngularEulerWeight B R δ) x := by
  have hb : ContDiffAt ℝ ∞ (fun y => (B y).det) x :=
    (continuousDetRows (ι := ι)).contDiff.contDiffAt.comp x hB
  have hr : ContDiffAt ℝ ∞ (fun y => (R y).det) x :=
    (continuousDetRows (ι := κ)).contDiff.contDiffAt.comp x hR
  exact ⟨(contDiffAt_const.mul (hb.rpow_const_of_ne hBd)).mul (hr.rpow_const_of_ne hRd),
    (contDiffAt_const.mul (hb.rpow_const_of_ne hBd)).mul (hr.rpow_const_of_ne hRd)⟩

lemma tubeAreaFirstVariation_eq_flatContraction (φ : E → ℝ) (v : ι → E) (w : κ → E)
    (η : E → ℝ) (x : E) (δ : ℝ)
    (hB : (flatBlockHessian (fun y => -φ y) v x).IsSymm)
    (hR : (flatBlockHessian φ w x).IsSymm) :
    let B := fun y => flatBlockHessian (fun z => -φ z) v y
    let R := fun y => flatBlockHessian φ w y
    tubeAreaFirstVariation (B x) (-flatBlockHessian η v x) (R x) (flatBlockHessian η w x) δ =
      flatTestContraction (fun i j y => flatBaseEulerWeight B R δ y * (B y).adjugate i j) v η x +
      flatTestContraction (fun i j y => flatAngularEulerWeight B R δ y * (R y).adjugate i j) w η x := by
  dsimp only
  unfold tubeAreaFirstVariation flatTestContraction flatBaseEulerWeight flatAngularEulerWeight
  simp only [Matrix.neg_apply,flatBlockHessian,Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hB.adjugate.apply i j]
    ring
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hR.adjugate.apply i j]
    ring

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/- Two true integrations by parts and Piola cancellation convert flat tube
stationarity to the pointwise Euler equation. -/
theorem flatTubeEuler_of_stationary {W : Set E} (hW : IsOpen W)
    (φ : E → ℝ) (v : ι → E) (w : κ → E) (δ : ℝ)
    (hφ : ContDiffOn ℝ ∞ φ W)
    (hB : ∀ x ∈ W, (flatBlockHessian (fun y => -φ y) v x).PosDef)
    (hR : ∀ x ∈ W, (flatBlockHessian φ w x).PosDef)
    (hstat : ∀ η : E → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ W →
      (∫ x, tubeAreaFirstVariation (flatBlockHessian (fun y => -φ y) v x)
        (-flatBlockHessian η v x) (flatBlockHessian φ w x) (flatBlockHessian η w x) δ ∂μ) = 0)
    {x : E} (hx : x ∈ W) :
    let B := fun y => flatBlockHessian (fun z => -φ z) v y
    let R := fun y => flatBlockHessian φ w y
    (∑ j, ∑ i, (B x).adjugate i j * dirDeriv (v j) (dirDeriv (v i) (flatBaseEulerWeight B R δ)) x) +
      (∑ j, ∑ i, (R x).adjugate i j * dirDeriv (w j) (dirDeriv (w i) (flatAngularEulerWeight B R δ)) x) = 0 := by
  let B := fun y => flatBlockHessian (fun z => -φ z) v y
  let R := fun y => flatBlockHessian φ w y
  have hh (y : E) (hy : y ∈ W) := contDiffAt_flatEulerWeights
    (contDiffAt_flatBlockHessian (hφ.contDiffAt (hW.mem_nhds hy)).neg v)
    (contDiffAt_flatBlockHessian (hφ.contDiffAt (hW.mem_nhds hy)) w)
    (ne_of_gt (hB y hy).det_pos) (ne_of_gt (hR y hy).det_pos) δ
  apply flatWeightedBlockEuler (μ := μ) hW (fun y => -φ y) φ
    (flatBaseEulerWeight B R δ) (flatAngularEulerWeight B R δ) v w hφ.neg hφ
    (fun y hy => (hh y hy).1.contDiffWithinAt) (fun y hy => (hh y hy).2.contDiffWithinAt) ?_ hx
  intro η hη hc hs
  rw [← hstat η hη hc hs]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y ∈ tsupport η
  · exact (tubeAreaFirstVariation_eq_flatContraction φ v w η y δ
      (Matrix.isHermitian_iff_isSymm.mp (hB y (hs hy)).isHermitian)
      (Matrix.isHermitian_iff_isSymm.mp (hR y (hs hy)).isHermitian)).symm
  · have hv := flatTestContraction_eq_zero_of_notMem_tsupport
      (fun i j z => flatBaseEulerWeight B R δ z * (B z).adjugate i j) v hy
    have hw := flatTestContraction_eq_zero_of_notMem_tsupport
      (fun i j z => flatAngularEulerWeight B R δ z * (R z).adjugate i j) w hy
    rw [hv,hw,zero_add]
    have hz (l m : E) : dirDeriv l (dirDeriv m η) y = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun ht => hy ((tsupport_fderiv_apply_subset ℝ m) ((tsupport_fderiv_apply_subset ℝ l) ht))
    simp [tubeAreaFirstVariation,flatBlockHessian,hz]

end AffineBernstein
end

end OAI
