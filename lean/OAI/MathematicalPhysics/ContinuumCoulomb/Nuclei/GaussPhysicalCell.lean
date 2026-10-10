import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.GaussTensorError

namespace OAI

/-! The tensor Gauss rule on a physical three-dimensional cell. Normalized
error estimates acquire the correct cell-volume factor. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def gaussCellAffine (a b t : ℝ) : ℝ := (a+b)/2+(b-a)/2*t

def gaussCellPullback (a b : ℝ) (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  f (gaussCellAffine a b x) (gaussCellAffine a b y) (gaussCellAffine a b z)

def gaussPhysicalCell (a b : ℝ) (f : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ((b-a)/2)^3*gaussTwoPoint (fun x => gaussTwoPoint (fun y =>
    gaussTwoPoint (gaussCellPullback a b f x y)))

def physicalCellIntegral (a b : ℝ) (f : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in a..b, ∫ y : ℝ in a..b, ∫ z : ℝ in a..b, f x y z

theorem integral_gaussCellAffine (a b : ℝ) (f : ℝ → ℝ) :
    ((b-a)/2)*(∫ t : ℝ in (-1)..1, f (gaussCellAffine a b t)) =
      ∫ x : ℝ in a..b, f x := by
  have h := intervalIntegral.smul_integral_comp_add_mul
    (f := f) (a := (-1:ℝ)) (b := 1) ((b-a)/2) ((a+b)/2)
  have hl : (a+b)/2+(b-a)/2*(-1) = a := by ring
  have hr : (a+b)/2+(b-a)/2*1 = b := by ring
  simpa only [smul_eq_mul,hl,hr,gaussCellAffine] using h

theorem physicalCellIntegral_eq_normalized (a b : ℝ) (f : ℝ → ℝ → ℝ → ℝ) :
    physicalCellIntegral a b f = ((b-a)/2)^3*
      (∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1,
        gaussCellPullback a b f x y z) := by
  let d : ℝ := (b-a)/2
  have hz (x y : ℝ) : d*(∫ z : ℝ in (-1)..1, f x y (gaussCellAffine a b z)) =
      ∫ z : ℝ in a..b, f x y z := integral_gaussCellAffine a b (f x y)
  have hy (x : ℝ) : d^2*(∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1,
      f x (gaussCellAffine a b y) (gaussCellAffine a b z)) =
      ∫ y : ℝ in a..b, ∫ z : ℝ in a..b, f x y z := by
    calc
      _ = d*(∫ y : ℝ in (-1)..1, d*(∫ z : ℝ in (-1)..1,
          f x (gaussCellAffine a b y) (gaussCellAffine a b z))) := by
        rw [intervalIntegral.integral_const_mul]
        ring
      _ = d*(∫ y : ℝ in (-1)..1, ∫ z : ℝ in a..b, f x (gaussCellAffine a b y) z) := by
        simp_rw [hz]
      _ = _ := integral_gaussCellAffine a b (fun y => ∫ z : ℝ in a..b, f x y z)
  symm
  change d^3*(∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1,
    f (gaussCellAffine a b x) (gaussCellAffine a b y) (gaussCellAffine a b z)) = _
  calc
    _ = d*(∫ x : ℝ in (-1)..1, d^2*(∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1,
        f (gaussCellAffine a b x) (gaussCellAffine a b y) (gaussCellAffine a b z))) := by
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = d*(∫ x : ℝ in (-1)..1, ∫ y : ℝ in a..b, ∫ z : ℝ in a..b,
        f (gaussCellAffine a b x) y z) := by simp_rw [hy]
    _ = _ := integral_gaussCellAffine a b (fun x => ∫ y : ℝ in a..b, ∫ z : ℝ in a..b, f x y z)

theorem gaussPhysicalCell_error_of_normalized {a b E : ℝ} (hab : a ≤ b)
    (f : ℝ → ℝ → ℝ → ℝ)
    (herr : |gaussTwoPoint (fun x => gaussTwoPoint (fun y =>
      gaussTwoPoint (gaussCellPullback a b f x y)))-
      (∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1,
        gaussCellPullback a b f x y z)| ≤ E) :
    |gaussPhysicalCell a b f-physicalCellIntegral a b f| ≤ ((b-a)/2)^3*E := by
  rw [physicalCellIntegral_eq_normalized,gaussPhysicalCell,← mul_sub,abs_mul,
    abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ (b-a)/2) _)]
  exact mul_le_mul_of_nonneg_left herr (pow_nonneg (by linarith) _)

theorem gaussPhysicalCell_seventh_power_error {a b C : ℝ} (hab : a ≤ b)
    (f : ℝ → ℝ → ℝ → ℝ)
    (herr : |gaussTwoPoint (fun x => gaussTwoPoint (fun y =>
      gaussTwoPoint (gaussCellPullback a b f x y)))-
      (∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1,
        gaussCellPullback a b f x y z)| ≤ 128*C*((b-a)/2)^4) :
    |gaussPhysicalCell a b f-physicalCellIntegral a b f| ≤ C*(b-a)^7 := by
  apply (gaussPhysicalCell_error_of_normalized hab f herr).trans_eq
  ring

theorem gaussPhysicalCells_error {N : ℕ} (h : ℝ) (a C : Fin N → ℝ)
    (f : Fin N → ℝ → ℝ → ℝ → ℝ)
    (herr : ∀ i, |gaussPhysicalCell (a i) (a i+h) (f i)-
      physicalCellIntegral (a i) (a i+h) (f i)| ≤ C i*h^7) :
    |(∑ i, gaussPhysicalCell (a i) (a i+h) (f i))-
      (∑ i, physicalCellIntegral (a i) (a i+h) (f i))| ≤ h^4*∑ i, C i*h^3 := by
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun i _ => herr i)).trans_eq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end ContinuumCoulomb

end

end OAI
