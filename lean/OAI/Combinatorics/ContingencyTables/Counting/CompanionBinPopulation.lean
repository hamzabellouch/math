import OAI.Combinatorics.ContingencyTables.Machines.FairBits
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

namespace OAI

/-! # Exact integer bin populations for the companion weight evaluator -/

namespace ContingencyTables.CompanionBinPopulation

open scoped BigOperators Classical

variable {C : Type*} [Fintype C]

def coordinatePopulation (B N v : ℕ) : ℚ := B*(FairBits.fiber B N v).card/(N:ℚ)

def population (B : ℕ) (N : C → ℕ) (v : C → ℕ) : ℚ :=
  ∏ c,coordinatePopulation B (N c) (v c)

abbrev Assignments (B : ℕ) (N : C → ℕ) (v : C → ℕ) :=
  (c : C) → {z : ℕ // z ∈ FairBits.fiber B (N c) (v c)}

lemma assignment_card (B : ℕ) (N : C → ℕ) (v : C → ℕ) :
    Fintype.card (Assignments B N v)=∏ c,(FairBits.fiber B (N c) (v c)).card := by
  simp only [Assignments,Fintype.card_pi,Fintype.card_coe]

/-- The product formula is exactly B^e times the integer bin population
divided by the total number of free assignments. -/
lemma population_eq_card (B : ℕ) (N : C → ℕ) (v : C → ℕ) :
    population B N v=(B:ℚ)^Fintype.card C*(Fintype.card (Assignments B N v):ℚ)/
      (∏ c,(N c:ℚ)) := by
  rw [assignment_card]
  simp only [population,coordinatePopulation,Finset.prod_div_distrib,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Nat.cast_prod]

lemma coordinate_error (B N d v : ℕ) (hB : 0 < B) (hd : 1 ≤ d)
    (hN : 100*d*B ≤ N) (hv : v < B) :
    |coordinatePopulation B N v-1| ≤ 1/(100*(d:ℚ)) := by
  have hdQ : (0:ℚ) < d := by exact_mod_cast (show 0 < d by omega)
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hNQ : (0:ℚ) < N := by exact_mod_cast hNpos
  have hBQ : (0:ℚ) < B := by exact_mod_cast hB
  have hsize : (100:ℚ)*d*B ≤ N := by exact_mod_cast hN
  have heq : coordinatePopulation B N v-1=
      ((B:ℚ)/N)*(((FairBits.fiber B N v).card:ℚ)-(N:ℚ)/B) := by
    unfold coordinatePopulation
    field_simp [hNQ.ne',hBQ.ne']
  rw [heq,abs_mul,abs_of_nonneg (div_nonneg hBQ.le hNQ.le)]
  calc
    _ ≤ ((B:ℚ)/N)*1 := mul_le_mul_of_nonneg_left
      (FairBits.fiber_card_error hB hNpos hv).le (by positivity)
    _ = (B:ℚ)/N := mul_one _
    _ ≤ _ := by
      rw [div_le_div_iff₀ hNQ (by positivity : (0:ℚ) < 100*d)]
      nlinarith

private lemma reverse_bernoulli (u : ℚ) (hu : 0 ≤ u) (n : ℕ) :
    (1+u)^n*(1-(n:ℚ)*u) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have haux : (1+u)*(1-((n:ℚ)+1)*u) ≤ 1-(n:ℚ)*u := by
      nlinarith [mul_nonneg (show (0:ℚ) ≤ n+1 by positivity) (sq_nonneg u)]
    calc
      _ = (1+u)^n*((1+u)*(1-((n:ℚ)+1)*u)) := by
        rw [pow_succ,Nat.cast_add,Nat.cast_one]
        ring
      _ ≤ (1+u)^n*(1-(n:ℚ)*u) :=
        mul_le_mul_of_nonneg_left haux (by positivity)
      _ ≤ 1 := ih

/-- The source's alpha_v lies between one half and two, including the
empty-coordinate product. No large interval is enumerated to establish
the bound; its exact cardinality is the proved ceiling difference. -/
theorem population_bounds (B d : ℕ) (N : C → ℕ) (v : C → ℕ)
    (hB : 0 < B) (hd : 1 ≤ d) (hcard : Fintype.card C ≤ d)
    (hN : ∀ c,100*d*B ≤ N c) (hv : ∀ c,v c < B) :
    1/2 ≤ population B N v ∧ population B N v ≤ 2 := by
  let u : ℚ := 1/(100*(d:ℚ))
  have hdQ : (1:ℚ) ≤ d := by exact_mod_cast hd
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hu1 : u ≤ 1/100 := by
    dsimp only [u]
    rw [div_le_div_iff₀ (by positivity : (0:ℚ)<100*d) (by norm_num : (0:ℚ)<100)]
    linarith
  have hcountQ : (Fintype.card C:ℚ) ≤ d := by exact_mod_cast hcard
  have hsum : (Fintype.card C:ℚ)*u ≤ 1/100 := by
    dsimp only [u]
    rw [← mul_div_assoc,div_le_div_iff₀ (by positivity : (0:ℚ)<100*d) (by norm_num : (0:ℚ)<100)]
    linarith
  have hfactor (c : C) : 1-u ≤ coordinatePopulation B (N c) (v c) ∧
      coordinatePopulation B (N c) (v c) ≤ 1+u := by
    have hh := abs_le.mp (coordinate_error B (N c) d (v c) hB hd (hN c) (hv c))
    constructor <;> linarith
  have hpos (c : C) : 0 ≤ coordinatePopulation B (N c) (v c) := by
    unfold coordinatePopulation
    positivity
  have hlo : (1-u)^Fintype.card C ≤ population B N v := by
    unfold population
    calc
      _ = ∏ _c : C,(1-u) := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => by linarith) (fun c _ => (hfactor c).1)
  have hup : population B N v ≤ (1+u)^Fintype.card C := by
    unfold population
    calc
      _ ≤ ∏ _c : C,(1+u) := Finset.prod_le_prod₀ (fun c _ => hpos c) (fun c _ => (hfactor c).2)
      _ = _ := by simp
  have hbern := one_add_mul_le_pow (show (-2:ℚ) ≤ -u by linarith) (Fintype.card C)
  have hreverse := reverse_bernoulli u hu (Fintype.card C)
  have hpower : 0 ≤ (1+u)^Fintype.card C := by positivity
  constructor
  · have hh : 1-(Fintype.card C:ℚ)*u ≤ (1-u)^Fintype.card C := by
      simpa only [mul_neg,sub_eq_add_neg] using hbern
    linarith
  · nlinarith

theorem coordinate_nonempty (B N d v : ℕ) (hB : 0 < B) (hd : 1 ≤ d)
    (hN : 100*d*B ≤ N) (hv : v < B) : (FairBits.fiber B N v).Nonempty := by
  have hh := (abs_le.mp (coordinate_error B N d v hB hd hN hv)).1
  have hdQ : (1:ℚ) ≤ d := by exact_mod_cast hd
  have hu : 1/(100*(d:ℚ)) < 1 := by
    rw [div_lt_one (by positivity : (0:ℚ) < 100*d)]
    linarith
  have hp : 0 < coordinatePopulation B N v := by linarith
  apply Finset.card_pos.mp
  by_contra hzero
  have hz : (FairBits.fiber B N v).card=0 := by omega
  simp only [coordinatePopulation,hz,Nat.cast_zero,mul_zero,zero_div] at hp
  exact lt_irrefl _ hp

end ContingencyTables.CompanionBinPopulation

end OAI
