import OAI.NumberTheory.TotientAsymptotic.IntervalSieveDenominator
import OAI.NumberTheory.TotientAsymptotic.SieveEulerProduct
import OAI.NumberTheory.TotientAsymptotic.MertensProduct

namespace OAI

/-! An interval Euler-product lower bound from the already proved Mertens bound. -/
noncomputable section
open scoped BigOperators
open BoundingSieve SelbergSieve
namespace TotientAsymptotic

lemma intervalSieveWeight_euler {p : ℕ} (hp : p.Prime) :
    1+intervalSieveWeight p = (p:ℝ)/(p-1) := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hd : (p:ℝ)-1 ≠ 0 := by linarith
  unfold intervalSieveWeight
  field_simp
  ring

lemma primeEulerProduct_interval {S z : ℕ} (hS : 2 ≤ S) (hSz : S ≤ z) :
    primeEulerProduct z = primeEulerProduct S*
      ∏ p ∈ intervalSievePrimes S z,(1+intervalSieveWeight p) := by
  classical
  have he : (Finset.Icc 2 z).filter Nat.Prime =
      ((Finset.Icc 2 S).filter Nat.Prime) ∪ intervalSievePrimes S z := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_union,mem_intervalSievePrimes]
    constructor
    · rintro ⟨⟨hp2,hpz⟩,hpp⟩
      by_cases hpS : p ≤ S
      · exact Or.inl ⟨⟨hp2,hpS⟩,hpp⟩
      · exact Or.inr ⟨hpz,hpp,by omega,by omega⟩
    · rintro (⟨⟨hp2,hpS⟩,hpp⟩ | ⟨hpz,hpp,_,_⟩)
      · exact ⟨⟨hp2,hpS.trans hSz⟩,hpp⟩
      · exact ⟨⟨hpp.two_le,hpz⟩,hpp⟩
  have hd : Disjoint ((Finset.Icc 2 S).filter Nat.Prime) (intervalSievePrimes S z) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hh := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    have hj := (mem_intervalSievePrimes.mp hq).2.2.2
    omega
  unfold primeEulerProduct
  rw [he,Finset.prod_union hd]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  exact (intervalSieveWeight_euler (mem_intervalSievePrimes.mp hp).2.1).symm

theorem intervalSieveEuler_lower : ∃ C : ℝ,0 < C ∧
    ∀ S z : ℕ,2 ≤ S → S ≤ z →
      Real.log z/(C*Real.log S) ≤ ∏ p ∈ intervalSievePrimes S z,(1+intervalSieveWeight p) := by
  obtain ⟨C,hC,hbound⟩ := mertensProductInput
  refine ⟨C,hC,?_⟩
  intro S z hS hSz
  have hlogS : 0 < Real.log S := Real.log_pos (by exact_mod_cast (show 1 < S by omega))
  have hprod : 0 ≤ ∏ p ∈ intervalSievePrimes S z,(1+intervalSieveWeight p) := by
    apply Finset.prod_nonneg
    intro p hp
    have hh := intervalSieveWeight_nonneg (mem_intervalSievePrimes.mp hp).2.1
    linarith
  apply (div_le_iff₀ (mul_pos hC hlogS)).mpr
  have he := primeEulerProduct_log_lower z
  rw [primeEulerProduct_interval hS hSz] at he
  have hb := mul_le_mul_of_nonneg_right (hbound S hS) hprod
  nlinarith

theorem intervalSifted_bound : ∃ C : ℝ,0 < C ∧
    ∀ S X z : ℕ,2 ≤ S → S ≤ z → ∀ y : ℝ,1 < y →
      4*Real.log 4*(2+Real.log z) ≤ Real.log y →
      ((intervalSifted S X z).card:ℝ) ≤ C*X*Real.log S/Real.log z+2*y^3 := by
  obtain ⟨C,hC,hCbound⟩ := intervalSieveEuler_lower
  refine ⟨2*C,by positivity,?_⟩
  intro S X z hS hSz y hy hscale
  have hz : 2 ≤ z := hS.trans hSz
  have hlogS : 0 < Real.log S := Real.log_pos (by exact_mod_cast (show 1 < S by omega))
  have hlogz : 0 < Real.log z := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  let E := ∏ p ∈ intervalSievePrimes S z,(1+intervalSieveWeight p)
  have hE : Real.log z/(C*Real.log S) ≤ E := hCbound S z hS hSz
  have hB : E/2 ≤ selbergBoundingSum (intervalPrimeSieve S X z y hy.le) :=
    intervalSieveBoundingSum_lower S X z y hy hz hscale
  have hEl : 0 < E := lt_of_lt_of_le (div_pos hlogz (mul_pos hC hlogS)) hE
  have hd : (X:ℝ)/selbergBoundingSum (intervalPrimeSieve S X z y hy.le) ≤
      2*C*X*Real.log S/Real.log z := by
    calc
      _ ≤ (X:ℝ)/(E/2) := div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hB
      _ ≤ (X:ℝ)/((Real.log z/(C*Real.log S))/2) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) (by linarith)
      _ = _ := by field_simp
  exact (intervalSifted_selberg S X z y hy.le).trans (add_le_add hd le_rfl)

end TotientAsymptotic

end

end OAI
