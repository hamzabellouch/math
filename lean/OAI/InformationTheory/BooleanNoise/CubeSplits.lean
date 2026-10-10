import OAI.InformationTheory.BooleanNoise.FiniteNoise
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

namespace OAI

open scoped BigOperators

noncomputable section

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

def cubeSplitEquiv (n : ℕ) : Bool × Cube n ≃ Cube (n + 1) where
  toFun z := Fin.cases z.1 z.2
  invFun x := (x 0, fun i => x i.succ)
  left_inv z := by cases z; rfl
  right_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem sum_cube_split (g : Cube (n + 1) → ℝ) :
    (∑ x, g x) = (∑ x, restrict g true x) + ∑ x, restrict g false x := by
  rw [← (cubeSplitEquiv n).sum_comp g, Fintype.sum_prod_type, Fintype.sum_bool]
  rfl

theorem cubeAverage_split (g : Cube (n + 1) → ℝ) :
    cubeAverage g = (cubeAverage (restrict g true) + cubeAverage (restrict g false)) / 2 := by
  unfold cubeAverage
  rw [sum_cube_split, pow_succ]
  have hN : (2 : ℝ) ^ n ≠ 0 := ne_of_gt (cube_denominator_pos n)
  field_simp

theorem cubeAverage_div (g : Cube n → ℝ) (c : ℝ) :
    cubeAverage (fun x => g x / c) = cubeAverage g / c := by
  simp only [cubeAverage, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  ring

theorem cubeAverage_half_sum (g h : Cube n → ℝ) :
    cubeAverage (fun x => (g x + h x) / 2) = (cubeAverage g + cubeAverage h) / 2 := by
  rw [cubeAverage_div, cubeAverage_add]

theorem cubeAverage_split_pair (g : Cube (n + 1) → ℝ) :
    cubeAverage g = cubeAverage (fun x => (restrict g true x + restrict g false x) / 2) := by
  rw [cubeAverage_half_sum, cubeAverage_split]

@[simp] theorem pairMean_add_halfDifference (g : Cube (n + 1) → ℝ) (x : Cube n) :
    pairMean g x + pairHalfDifference g x = restrict g true x := by
  unfold pairMean pairHalfDifference
  ring

@[simp] theorem pairMean_sub_halfDifference (g : Cube (n + 1) → ℝ) (x : Cube n) :
    pairMean g x - pairHalfDifference g x = restrict g false x := by
  unfold pairMean pairHalfDifference
  ring

@[simp] theorem cubeAverage_pairMean (g : Cube (n + 1) → ℝ) :
    cubeAverage (pairMean g) = cubeAverage g := by
  exact (cubeAverage_split_pair g).symm

theorem cubeAverage_pairHalfDifference (g : Cube (n + 1) → ℝ) :
    cubeAverage (pairHalfDifference g) =
      (cubeAverage (restrict g true) - cubeAverage (restrict g false)) / 2 := by
  unfold pairHalfDifference
  rw [cubeAverage_div, cubeAverage_sub]

theorem cubeAverage_pairMean_add_halfDifference (g : Cube (n + 1) → ℝ) :
    cubeAverage (pairMean g) + cubeAverage (pairHalfDifference g) =
      cubeAverage (restrict g true) := by
  rw [cubeAverage_pairMean, cubeAverage_split, cubeAverage_pairHalfDifference]
  ring

theorem cubeAverage_pairMean_sub_halfDifference (g : Cube (n + 1) → ℝ) :
    cubeAverage (pairMean g) - cubeAverage (pairHalfDifference g) =
      cubeAverage (restrict g false) := by
  rw [cubeAverage_pairMean, cubeAverage_split, cubeAverage_pairHalfDifference]
  ring

theorem entropyAverage_split (g : Cube (n + 1) → ℝ) :
    entropyAverage g = (entropyAverage (restrict g true) + entropyAverage (restrict g false)) / 2 := by
  exact cubeAverage_split (fun x => entropy (g x))

theorem cubeAverage_pairEntropyGap (g : Cube (n + 1) → ℝ) :
    cubeAverage (fun x => pairEntropyGap (pairMean g x) (pairHalfDifference g x)) =
      entropyAverage (pairMean g) - entropyAverage g := by
  simp only [pairEntropyGap, pairMean_add_halfDifference, pairMean_sub_halfDifference]
  rw [cubeAverage_sub, cubeAverage_div, cubeAverage_add]
  change entropyAverage (pairMean g) -
    (entropyAverage (restrict g true) + entropyAverage (restrict g false)) / 2 = _
  rw [← entropyAverage_split]

theorem informationDeficit_split (g : Cube (n + 1) → ℝ) :
    (informationDeficit (restrict g true) + informationDeficit (restrict g false)) / 2 =
      informationDeficit g - pairEntropyGap (cubeAverage (pairMean g))
        (cubeAverage (pairHalfDifference g)) := by
  rw [pairEntropyGap, cubeAverage_pairMean_add_halfDifference,
    cubeAverage_pairMean_sub_halfDifference, cubeAverage_pairMean]
  simp only [informationDeficit]
  rw [entropyAverage_split]
  ring

theorem informationDeficit_eq_pairMean_add (g : Cube (n + 1) → ℝ) :
    informationDeficit g = informationDeficit (pairMean g) +
      cubeAverage (fun x => pairEntropyGap (pairMean g x) (pairHalfDifference g x)) := by
  rw [cubeAverage_pairEntropyGap]
  simp only [informationDeficit, cubeAverage_pairMean]
  ring

theorem meanVariance_split (g : Cube (n + 1) → ℝ) :
    (meanVariance (restrict g true) + meanVariance (restrict g false)) / 2 =
      meanVariance g - (cubeAverage (pairHalfDifference g)) ^ 2 := by
  simp only [meanVariance]
  rw [cubeAverage_split, cubeAverage_pairHalfDifference]
  ring

theorem flip_zero_cases (b : Bool) (x : Cube n) :
    flip (0 : Fin (n + 1)) (Fin.cases b x) = Fin.cases (!b) x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [flip, LeanBlast.GotsmanLinial.flip]
  · simp [flip, LeanBlast.GotsmanLinial.flip]

theorem flip_succ_cases (i : Fin n) (b : Bool) (x : Cube n) :
    flip i.succ (Fin.cases b x) = Fin.cases b (flip i x) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · have h0 : (0 : Fin (n + 1)) ≠ i.succ := Ne.symm (Fin.succ_ne_zero i)
    simp [flip, LeanBlast.GotsmanLinial.flip, h0]
  · by_cases hki : k = i
    · subst k
      simp [flip, LeanBlast.GotsmanLinial.flip]
    · simp [flip, LeanBlast.GotsmanLinial.flip, hki]

theorem restrict_cubeDerivative_succ (g : Cube (n + 1) → ℝ) (i : Fin n) (b : Bool) :
    restrict (cubeDerivative i.succ g) b = cubeDerivative i (restrict g b) := by
  funext x
  simp only [restrict, cubeDerivative, flip_succ_cases]

theorem cubeAverage_first_coordinate_energy (g : Cube (n + 1) → ℝ) :
    cubeAverage (fun x => Real.artanh (g x) * cubeDerivative 0 g x) =
      cubeAverage (fun x => pairDissipation (pairMean g x) (pairHalfDifference g x)) := by
  rw [cubeAverage_split_pair]
  congr 1
  funext x
  simp only [restrict, cubeDerivative, flip_zero_cases, Bool.not_true, Bool.not_false]
  rw [pairDissipation, pairMean_add_halfDifference, pairMean_sub_halfDifference]
  dsimp only [pairHalfDifference, restrict]
  ring

theorem cubeAverage_succ_coordinate_energy (g : Cube (n + 1) → ℝ) (i : Fin n) :
    cubeAverage (fun x => Real.artanh (g x) * cubeDerivative i.succ g x) =
      (cubeAverage (fun x => Real.artanh (restrict g true x) * cubeDerivative i (restrict g true) x) +
        cubeAverage (fun x => Real.artanh (restrict g false x) * cubeDerivative i (restrict g false) x)) / 2 := by
  have hr (b : Bool) :
      restrict (fun x => Real.artanh (g x) * cubeDerivative i.succ g x) b =
        (fun x => Real.artanh (restrict g b x) * cubeDerivative i (restrict g b) x) := by
    funext x
    simp only [restrict, cubeDerivative, flip_succ_cases]
  rw [cubeAverage_split, hr true, hr false]

theorem dissipation_split (g : Cube (n + 1) → ℝ) :
    dissipation g = (dissipation (restrict g true) + dissipation (restrict g false)) / 2 +
      cubeAverage (fun x => pairDissipation (pairMean g x) (pairHalfDifference g x)) := by
  simp only [dissipation]
  rw [Fin.sum_univ_succ, cubeAverage_first_coordinate_energy]
  simp_rw [cubeAverage_succ_coordinate_energy]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  ring

theorem IsInterior.restrict {g : Cube (n + 1) → ℝ} (hg : IsInterior g) (b : Bool) :
    IsInterior (LeanBlast.CourtadeKumar.restrict g b) := by
  intro x
  exact hg (Fin.cases b x)

theorem IsInterior.pairMean {g : Cube (n + 1) → ℝ} (hg : IsInterior g) :
    IsInterior (LeanBlast.CourtadeKumar.pairMean g) := by
  intro x
  have h1 := hg.restrict true x
  have h0 := hg.restrict false x
  dsimp only [LeanBlast.CourtadeKumar.pairMean]
  constructor <;> linarith

theorem IsInterior.pairDomain {g : Cube (n + 1) → ℝ} (hg : IsInterior g) :
    ∀ x, |LeanBlast.CourtadeKumar.pairMean g x| + |pairHalfDifference g x| < 1 := by
  intro x
  have h1 := hg.restrict true x
  have h0 := hg.restrict false x
  have hsum := pairMean_add_halfDifference g x
  have hsub := pairMean_sub_halfDifference g x
  rcases le_total 0 (LeanBlast.CourtadeKumar.pairMean g x) with ha | ha <;>
    rcases le_total 0 (pairHalfDifference g x) with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb]
    linarith
  · rw [abs_of_nonneg ha, abs_of_nonpos hb]
    linarith
  · rw [abs_of_nonpos ha, abs_of_nonneg hb]
    linarith
  · rw [abs_of_nonpos ha, abs_of_nonpos hb]
    linarith

def cubeVariance (g : Cube n → ℝ) : ℝ :=
  cubeAverage (fun x => (g x - cubeAverage g) ^ 2)

theorem cubeVariance_nonneg (g : Cube n → ℝ) : 0 ≤ cubeVariance g :=
  cubeAverage_nonneg fun _ => sq_nonneg _

theorem cubeVariance_eq (g : Cube n → ℝ) :
    cubeVariance g = cubeAverage (fun x => (g x) ^ 2) - (cubeAverage g) ^ 2 := by
  unfold cubeVariance
  have heq : (fun x => (g x - cubeAverage g) ^ 2) =
      (fun x => (g x) ^ 2 - (2 * cubeAverage g) * g x + (cubeAverage g) ^ 2) := by
    funext x
    ring
  rw [heq, cubeAverage_add, cubeAverage_sub, cubeAverage_smul, cubeAverage_const]
  ring

theorem average_one_sub_sq_eq_meanVariance_sub_variance (g : Cube n → ℝ) :
    cubeAverage (fun x => 1 - (g x) ^ 2) = meanVariance g - cubeVariance g := by
  rw [cubeAverage_sub, cubeAverage_const, cubeVariance_eq]
  unfold meanVariance
  ring

theorem cubeAverage_dim_zero (g : Cube 0 → ℝ) :
    cubeAverage g = g (fun i => Fin.elim0 i) := by
  have heq : g = fun _ => g (fun i => Fin.elim0 i) := by
    funext x
    congr 1
    exact Subsingleton.elim _ _
  rw [heq, cubeAverage_const]

@[simp] theorem informationDeficit_dim_zero (g : Cube 0 → ℝ) : informationDeficit g = 0 := by
  simp only [informationDeficit, entropyAverage, cubeAverage_dim_zero]
  ring

@[simp] theorem dissipation_dim_zero (g : Cube 0 → ℝ) : dissipation g = 0 := by
  simp [dissipation]

end LeanBlast.CourtadeKumar

end

end OAI
