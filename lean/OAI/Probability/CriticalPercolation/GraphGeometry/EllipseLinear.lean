import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.DiskWinding

namespace OAI

section
section
noncomputable section
open LinearMap

namespace CriticalPercolation.EllipseLinear

def det (a b c d : ℝ) : ℝ := a*d-b*c

def time (a b c d x y : ℝ) : ℝ := ((d-b)*x+(a-c)*y)/det a b c d

def height (a b c d x y : ℝ) : ℝ := ((d+b)*x-(c+a)*y)/det a b c d

lemma center_left (a b c d : ℝ) (h : det a b c d≠0) :
    time a b c d a b=1 ∧ height a b c d a b=1 := by
  constructor <;> dsimp only [time,height] <;> field_simp [h] <;> unfold det <;> ring

lemma center_right (a b c d : ℝ) (h : det a b c d≠0) :
    time a b c d c d=1 ∧ height a b c d c d= -1 := by
  constructor <;> dsimp only [time,height] <;> field_simp [h] <;> unfold det <;> ring

lemma det_lower_of_separation (θ ψ : ℝ)
    (hsep : Real.pi/4≤|DiskWinding.increment ((2*θ : ℝ) : Real.Angle)
      ((2*ψ : ℝ) : Real.Angle)|) :
    (1 : ℝ)/4≤|det (Real.cos θ) (Real.sin θ) (Real.cos ψ) (Real.sin ψ)| := by
  let t : Real.Angle := ((2*ψ : ℝ) : Real.Angle)-((2*θ : ℝ) : Real.Angle)
  have ht : t=((2*(ψ-θ) : ℝ) : Real.Angle) := by
    dsimp [t]
    rw [←Real.Angle.coe_sub]
    congr 1
    ring
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (by positivity : 0≤Real.pi/4) (Real.Angle.abs_toReal_le_pi t) hsep
  rw [Real.cos_abs,Real.Angle.cos_toReal,ht,Real.Angle.cos_coe,
    Real.cos_two_mul,Real.cos_pi_div_four] at hcos
  have hsqrt : Real.sqrt 2≤(7 : ℝ)/4 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ)≤2),Real.sqrt_nonneg 2]
  have hsq := Real.sin_sq_add_cos_sq (ψ-θ)
  have hsin : (1 : ℝ)/4≤|Real.sin (ψ-θ)| := by
    nlinarith [sq_abs (Real.sin (ψ-θ)),abs_nonneg (Real.sin (ψ-θ))]
  have heq : det (Real.cos θ) (Real.sin θ) (Real.cos ψ) (Real.sin ψ)=
      Real.sin (ψ-θ) := by rw [Real.sin_sub]; unfold det; ring
  rwa [heq]

lemma row_bound {a b c d : ℝ} (ha : |a|≤1) (hb : |b|≤1)
    (hc : |c|≤1) (hd : |d|≤1) (hdet : (1 : ℝ)/4≤|det a b c d|)
    (x y q : ℝ) (hq : 0≤q) (hx : |x|≤q) (hy : |y|≤q) :
    |time a b c d x y|≤16*q ∧ |height a b c d x y|≤16*q := by
  have hpos : 0 < |det a b c d| := by linarith
  have hdb : |d-b|≤2 := (abs_sub d b).trans (by linarith)
  have hac : |a-c|≤2 := (abs_sub a c).trans (by linarith)
  have hdb' : |d+b|≤2 := (abs_add_le d b).trans (by linarith)
  have hca : |c+a|≤2 := (abs_add_le c a).trans (by linarith)
  have hprod : ∀ z w : ℝ, |z|≤2 → |w|≤q → |z*w|≤2*q := by
    intro z w hz hw
    rw [abs_mul]
    exact mul_le_mul hz hw (abs_nonneg _) (by norm_num)
  constructor
  · unfold time
    rw [abs_div]
    apply (div_le_iff₀ hpos).mpr
    calc
      |(d-b)*x+(a-c)*y|≤|(d-b)*x|+|(a-c)*y| := abs_add_le _ _
      _ ≤4*q := by linarith [hprod (d-b) x hdb hx,hprod (a-c) y hac hy]
      _ ≤16*q*|det a b c d| := by nlinarith
  · unfold height
    rw [abs_div]
    apply (div_le_iff₀ hpos).mpr
    calc
      |(d+b)*x-(c+a)*y|≤|(d+b)*x|+|(c+a)*y| := abs_sub _ _
      _ ≤4*q := by linarith [hprod (d+b) x hdb' hx,hprod (c+a) y hca hy]
      _ ≤16*q*|det a b c d| := by nlinarith

lemma time_sub (a b c d x y x' y' : ℝ) :
    time a b c d x y-time a b c d x' y'=time a b c d (x-x') (y-y') := by
  unfold time; ring
lemma height_sub (a b c d x y x' y' : ℝ) :
    height a b c d x y-height a b c d x' y'=height a b c d (x-x') (y-y') := by
  unfold height; ring

def equiv (a b c d : ℝ) (h : det a b c d≠0) : (ℝ×ℝ) ≃ₗ[ℝ] (ℝ×ℝ) where
  toFun p := (time a b c d p.1 p.2,height a b c d p.1 p.2)
  invFun p := ((a*(p.1+p.2)+c*(p.1-p.2))/2,(b*(p.1+p.2)+d*(p.1-p.2))/2)
  left_inv p := by
    apply Prod.ext <;> dsimp only [time,height] <;> field_simp [h] <;> unfold det <;> ring
  right_inv p := by
    apply Prod.ext <;> dsimp only [time,height] <;> field_simp [h] <;> unfold det <;> ring
  map_add' p q := by apply Prod.ext <;> dsimp [time,height] <;> ring
  map_smul' r p := by apply Prod.ext <;> dsimp [time,height] <;> ring

lemma source_budgets {eps : ℝ} (heps : 0<eps) (heps' : eps<1/10) :
    16*(4*(eps/1000))<eps/8 ∧
    16*((1+eps/1000)^2)<30 := by constructor <;> nlinarith

end CriticalPercolation.EllipseLinear
end
end
end

end OAI
