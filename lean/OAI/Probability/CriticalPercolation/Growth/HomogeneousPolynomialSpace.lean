import Mathlib
import OAI.Probability.CriticalPercolation.Growth.HomogeneousGeometry

namespace OAI

section
noncomputable section
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
variable {A : Type*} (W : Geometry A)

def harmonicSpace : Submodule ℝ (A → ℝ) where
  carrier := {u | W.IsHarmonic u}
  zero_mem' := by intro x; simp
  add_mem' := by
    intro u v hu hv x
    change (∑ s∈W.neighbors x, ((u x+v x)-(u s+v s)))=0
    simp_rw [show ∀ s:A, (u x+v x)-(u s+v s)=(u x-u s)+(v x-v s) by intro s; ring]
    rw [Finset.sum_add_distrib,hu x,hv x,add_zero]
  smul_mem' := by
    intro c u hu x
    change (∑ s∈W.neighbors x, (c*u x-c*u s))=0
    simp_rw [←mul_sub]
    rw [←Finset.mul_sum,hu x,mul_zero]

def HasPolynomialGrowth (k : ℕ) (u : A → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ x∈W.ball n, |u x| ≤ C*((n:ℝ)+1)^k

def polynomialGrowthSpace (k : ℕ) : Submodule ℝ (A → ℝ) where
  carrier := {u | W.HasPolynomialGrowth k u}
  zero_mem' := ⟨0,le_rfl,by simp⟩
  add_mem' := by
    rintro u v ⟨C,hC,hu⟩ ⟨D,hD,hv⟩
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    intro n x hx
    change |u x+v x| ≤ _
    calc
      _ ≤ |u x|+|v x| := abs_add_le _ _
      _ ≤ C*((n:ℝ)+1)^k+D*((n:ℝ)+1)^k := add_le_add (hu n x hx) (hv n x hx)
      _ = _ := by ring
  smul_mem' := by
    rintro c u ⟨C,hC,hu⟩
    refine ⟨|c| * C,mul_nonneg (abs_nonneg _) hC,?_⟩
    intro n x hx
    change |c*u x| ≤ _
    rw [abs_mul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (hu n x hx) (abs_nonneg _)

def polynomialHarmonicSpace (k : ℕ) : Submodule ℝ (A → ℝ) :=
  W.harmonicSpace ⊓ W.polynomialGrowthSpace k

lemma mem_polynomialHarmonicSpace (k : ℕ) (u : A → ℝ) :
    u∈W.polynomialHarmonicSpace k ↔ W.IsHarmonic u ∧ W.HasPolynomialGrowth k u := Iff.rfl

lemma polynomial_growth_iff_length (k : ℕ) (u : A → ℝ) :
    W.HasPolynomialGrowth k u ↔ ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, |u x| ≤ C*((W.length x:ℝ)+1)^k := by
  constructor
  · rintro ⟨C,hC,hu⟩
    exact ⟨C,hC,fun x => hu _ _ (W.mem_ball_length x)⟩
  · rintro ⟨C,hC,hu⟩
    refine ⟨C,hC,?_⟩
    intro n x hx
    apply (hu x).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast Nat.add_le_add_right (W.length_le_iff.mpr hx) 1

lemma finite_family_growth_bound {ι : Type*} [Fintype ι] (k : ℕ) (v : ι → A → ℝ)
    (hv : ∀ i, W.HasPolynomialGrowth k (v i)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n, 1 ≤ n → ∀ i, ∀ x∈W.ball n,
      |v i x| ≤ M*(n:ℝ)^k := by
  choose C hC hCv using hv
  let M := (∑ i, C i)*2^k
  have hm0 : 0 ≤ M := mul_nonneg (Finset.sum_nonneg (fun i _ => hC i)) (by positivity)
  refine ⟨M,hm0,?_⟩
  intro n hn i x hx
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hCi : C i ≤ ∑ j, C j := Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  calc
    _ ≤ C i*((n:ℝ)+1)^k := hCv i n x hx
    _ ≤ (∑ j, C j)*((n:ℝ)+1)^k := mul_le_mul_of_nonneg_right hCi (by positivity)
    _ ≤ (∑ j, C j)*(2*(n:ℝ))^k := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) k) (Finset.sum_nonneg (fun j _ => hC j))
    _ = M*(n:ℝ)^k := by dsimp [M]; rw [mul_pow]; ring

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
