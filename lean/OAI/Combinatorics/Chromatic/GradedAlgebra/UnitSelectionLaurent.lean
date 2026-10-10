import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.EnergyLaurentSeries
import OAI.Combinatorics.Chromatic.QuantumTorus.WeakUnitRecursion

namespace OAI

section
section
namespace ElementaryPositivity.UnitSelections
open EnergyLaurent
open scoped LaurentSeries
noncomputable section

def weakEnergy (n : ℕ) (k : ℤ) (f : Weak n) : ℤ := (n:ℤ)*k-2*weight f.val

lemma weakAdmissible (n : ℕ) (k : ℤ) : Admissible (weakEnergy n k) := by
  constructor
  · refine ⟨n*k,?_⟩
    intro f
    have hh : 0≤weight f.val:=Finset.sum_nonneg (fun i _=>Int.natCast_nonneg _)
    unfold weakEnergy
    linarith
  · intro E
    let U:=((n:ℤ)*k-E).toNat
    let F : {f : Weak n // weakEnergy n k f=E} → (Fin n → Fin (U+1)) := fun f i=>
      ⟨f.val.val i,by
        have hi : (f.val.val i:ℤ)≤weight f.val.val :=
          Finset.single_le_sum (fun j _=>Int.natCast_nonneg (f.val.val j)) (Finset.mem_univ i)
        have hn : 0≤weight f.val.val :=
          Finset.sum_nonneg (fun j _=>Int.natCast_nonneg (f.val.val j))
        have he:=f.property
        unfold weakEnergy at he
        dsimp only [U]
        omega⟩
    apply Finite.of_injective F
    intro f g h
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun h i)

def weakSeries (n : ℕ) (k : ℤ) : LaurentSeries ℚ := series (weakEnergy n k) (weakAdmissible n k)

lemma weakSeries_zero (k : ℤ) : weakSeries 0 k=1 := by
  let f : Weak 0:=⟨fun i=>Fin.elim0 i,by intro i; exact Fin.elim0 i⟩
  let : Unique (Weak 0):=⟨⟨f⟩,fun g=>Subsingleton.elim _ _⟩
  change (family (weakEnergy 0 k) (weakAdmissible 0 k)).hsum=1
  rw [HahnSeries.SummableFamily.hsum_unique]
  change HahnSeries.single (-(weakEnergy 0 k f)) (1:ℚ)=1
  simp only [weakEnergy,weight,Finset.univ_eq_empty,Finset.sum_empty,Int.natCast_zero,
    zero_mul,mul_zero,sub_self,neg_zero,HahnSeries.single_zero_one]

lemma weakSeries_recursion (n : ℕ) (k : ℤ) :
    weakSeries (n+1) k=weakSeries n k*HahnSeries.single (-k) (1:ℚ)+
      weakSeries (n+1) k*HahnSeries.single (2*(n+1:ℤ)) (1:ℚ) := by
  let he:=admissible_shift (weakAdmissible n k) k
  let hf:=admissible_shift (weakAdmissible (n+1) k) (-2*(n+1:ℤ))
  have hh:=series_equiv (admissible_sum he hf) (weakAdmissible (n+1) k)
    (weakSplit n).symm (fun p=>by
      simpa only [weakEnergy,sub_eq_add_neg,neg_mul] using weakSplit_inv_energy n k p)
  rw [series_sum he hf,series_shift (weakAdmissible n k),series_shift (weakAdmissible (n+1) k)] at hh
  simpa only [weakSeries,neg_mul,neg_neg] using hh.symm

lemma weakSeries_recursion_q (n : ℕ) (k : ℤ) :
    weakSeries (n+1) k*(1-(HahnSeries.single 2 (1:ℚ))^(n+1))=
      HahnSeries.single (-k) (1:ℚ)*weakSeries n k := by
  have hh:=weakSeries_recursion n k
  rw [HahnSeries.single_pow,one_pow]
  have hn : (n+1) • (2:ℤ)=2*(n+1:ℤ) := by simp only [nsmul_eq_mul,Nat.cast_add,Nat.cast_one]; ring
  rw [hn]
  linear_combination hh
end
end ElementaryPositivity.UnitSelections
end
end

end OAI
