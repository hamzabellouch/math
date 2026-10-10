import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.Basic

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def weightedPartition {n : ℕ} (ν : Config n → ℝ) (b : ℝ) (G : Disorder n) : ℝ :=
  ∑ x : Config n, ν x * Real.exp (b * hamiltonian G x)

theorem weightedPartition_integrable {n : ℕ} (ν : Config n → ℝ) (b : ℝ) :
    Integrable (weightedPartition ν b) (disorderLaw n) :=
  integrable_finsetSum _ (fun x _ =>
    (gaussian_exp_integrable (hamiltonian_gaussian x) b).const_mul _)

theorem weightedPartition_mean {n : ℕ} (hn : 0 < n) (ν : Config n → ℝ)
    (hν : ∑ x, ν x = 1) (b : ℝ) :
    (∫ G, weightedPartition ν b G ∂disorderLaw n) =
      Real.exp (b^2*((n:ℝ)-1)/4) := by
  unfold weightedPartition
  rw [integral_finsetSum _ (fun x _ =>
    (gaussian_exp_integrable (hamiltonian_gaussian x) b).const_mul _)]
  simp_rw [integral_const_mul,hamiltonian_exp_integral hn]
  rw [← Finset.sum_mul,hν,one_mul]

theorem weightedPartition_sq {n : ℕ} (ν : Config n → ℝ) (b : ℝ) (G : Disorder n) :
    (weightedPartition ν b G)^2 = ∑ x : Config n, ∑ y : Config n,
      (ν x*ν y)*Real.exp (b*(hamiltonian G x+hamiltonian G y)) := by
  unfold weightedPartition
  rw [pow_two,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [mul_add,Real.exp_add]
  ring

theorem weightedPartition_sq_integrable {n : ℕ} (ν : Config n → ℝ) (b : ℝ) :
    Integrable (fun G => (weightedPartition ν b G)^2) (disorderLaw n) := by
  simp_rw [weightedPartition_sq]
  exact integrable_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ =>
    (gaussian_exp_integrable (hamiltonian_add_gaussian x y) b).const_mul _))

theorem weightedPartition_secondMoment {n : ℕ} (hn : 0 < n) (ν : Config n → ℝ)
    (hν : ∑ x, ν x = 1) (b : ℝ) :
    (∫ G, (weightedPartition ν b G)^2 ∂disorderLaw n) /
      (∫ G, weightedPartition ν b G ∂disorderLaw n)^2 =
      ∑ x : Config n, ∑ y : Config n,
        ν x*ν y*Real.exp (b^2*((n:ℝ)*overlap x y^2-1)/2) := by
  rw [weightedPartition_mean hn ν hν]
  simp_rw [weightedPartition_sq]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ =>
    (gaussian_exp_integrable (hamiltonian_add_gaussian x y) b).const_mul _))]
  simp_rw [integral_finsetSum _ (fun y _ =>
    (gaussian_exp_integrable (hamiltonian_add_gaussian _ y) b).const_mul _),
    integral_const_mul,hamiltonian_add_exp_integral hn]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  rw [Real.exp_add]
  have he : Real.exp (b^2*((n:ℝ)-1)/2) =
      (Real.exp (b^2*((n:ℝ)-1)/4))^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [he]
  have hp := (Real.exp_pos (b^2*((n:ℝ)-1)/4)).ne'
  field_simp

theorem abs_overlap_le_one {n : ℕ} (x y : Config n) : |overlap x y| ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp [overlap]
  have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  unfold overlap
  rw [abs_div,abs_of_pos hnpos]
  apply (div_le_one hnpos).mpr
  calc
    _ ≤ ∑ i : Fin n, |spin (x i)*spin (y i)| := Finset.abs_sum_le_sum_abs _ _
    _ = (n:ℝ) := by
      have hs (i : Fin n) : |spin (x i)*spin (y i)| = 1 := by
        cases hx : x i <;> cases hy : y i <;> norm_num [spin]
      simp only [hs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

def weightedOverlapMass {n : ℕ} (ν : Config n → ℝ) (q : ℝ) : ℝ :=
  ∑ x : Config n, ∑ y : Config n, if q ≤ |overlap x y| then ν x*ν y else 0

theorem weightedPartition_secondMoment_le {n : ℕ} (hn : 0 < n)
    (ν : Config n → ℝ) (hνpos : ∀ x, 0 ≤ ν x) (hν : ∑ x, ν x = 1)
    (b q : ℝ) (hq : 0 ≤ q) :
    (∫ G, (weightedPartition ν b G)^2 ∂disorderLaw n) /
      (∫ G, weightedPartition ν b G ∂disorderLaw n)^2 ≤
      Real.exp (b^2*(n:ℝ)*q^2/2)+
        weightedOverlapMass ν q*Real.exp (b^2*(n:ℝ)/2) := by
  rw [weightedPartition_secondMoment hn ν hν]
  have H (x y : Config n) : ν x*ν y*Real.exp (b^2*((n:ℝ)*overlap x y^2-1)/2) ≤
      ν x*ν y*Real.exp (b^2*(n:ℝ)*q^2/2)+
      (if q ≤ |overlap x y| then ν x*ν y else 0)*Real.exp (b^2*(n:ℝ)/2) := by
    have hw : 0 ≤ ν x*ν y := mul_nonneg (hνpos x) (hνpos y)
    by_cases h : q ≤ |overlap x y|
    · rw [ite_eq_left h]
      have ho : overlap x y^2 ≤ 1 := by
        have hh := abs_overlap_le_one x y
        nlinarith [sq_abs (overlap x y)]
      have he : Real.exp (b^2*((n:ℝ)*overlap x y^2-1)/2) ≤
          Real.exp (b^2*(n:ℝ)/2) := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left ho (show 0 ≤ b^2*(n:ℝ) by positivity)
        nlinarith [sq_nonneg b]
      exact (mul_le_mul_of_nonneg_left he hw).trans (le_add_of_nonneg_left (by positivity))
    · rw [ite_eq_right h,zero_mul,add_zero]
      apply mul_le_mul_of_nonneg_left _ hw
      apply Real.exp_le_exp.mpr
      have ho : overlap x y^2 ≤ q^2 := by
        have hh := (not_le.mp h).le
        nlinarith [sq_abs (overlap x y),abs_nonneg (overlap x y)]
      have hh := mul_le_mul_of_nonneg_left ho (show 0 ≤ b^2*(n:ℝ) by positivity)
      nlinarith [sq_nonneg b]
  calc
    _ ≤ ∑ x : Config n, ∑ y : Config n,
        (ν x*ν y*Real.exp (b^2*(n:ℝ)*q^2/2)+
        (if q ≤ |overlap x y| then ν x*ν y else 0)*Real.exp (b^2*(n:ℝ)/2)) :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => H x y))
    _ = _ := by
      simp_rw [Finset.sum_add_distrib,← Finset.sum_mul]
      simp only [← Finset.mul_sum,hν,mul_one,one_mul,weightedOverlapMass]
end SK.Analytic

end
end

end

end OAI
