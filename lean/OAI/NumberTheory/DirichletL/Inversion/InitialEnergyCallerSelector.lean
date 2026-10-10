import OAI.NumberTheory.DirichletL.Inversion.InitialRayAttachment
import OAI.NumberTheory.DirichletL.Descent.Marks

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open SevenEighths.InverseInitialOverlap SevenEighths.InverseInitialRayAttachment
open SevenEighths.InverseMoment
namespace SevenEighths.InverseInitialEnergyCallerSelector
local notation "Eis" => ActualEisensteinCubic.O

theorem mask_nonzero_coprime (F : Finset (Ideal Eis)) (j : Ideal Eis) (hj : Admissible j)
    (A : Finset (primePool F))
    (hm : rowCoprimeMask (fun i : primePool F=>i.val) A (primaryGenerator j)≠0) :
    IsCoprime (∏ i∈A,i.val) j := by
  have hspan := (primaryGenerator_spec j (primaryGenerator_admissible j hj)).1
  apply IsCoprime.prod_left
  intro i hi
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra htop
  have he := Ideal.IsMaximal.eq_of_le (inferInstance : i.val.IsMaximal) htop
    (show (i.val : Ideal Eis) ≤ (i.val : Ideal Eis) ⊔ j from le_sup_left)
  have hmem : primaryGenerator j∈i.val := by
    rw [he]
    apply (show j ≤ (i.val : Ideal Eis) ⊔ j from le_sup_right)
    have hjmem : primaryGenerator j ∈ Ideal.span {primaryGenerator j} :=
      Ideal.subset_span (Set.mem_singleton _)
    rw [hspan] at hjmem
    exact hjmem
  apply hm
  unfold rowCoprimeMask
  exact ite_eq_left ⟨i,hi,hmem⟩

theorem reconstructedSelector_profile
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j∣P)
    (a : Ideal Eis→ℂ) (W : Ideal Eis→ℂ)
    (A : Finset (primePool (columns S P j)))
    (hA : Squarefree (∏ i∈A,i.val))
    (hcover : residual P j∣(∏ i∈A,i.val) → W (∏ i∈A,i.val)≠0 →
      IsCoprime (∏ i∈A,i.val) j → reconstruct P j (∏ i∈A,i.val)∈S) :
    reconstructedSelector S P j a A *
      rowCoprimeMask (fun i : primePool (columns S P j)=>i.val) A (primaryGenerator j) *
      W (∏ i∈A,i.val) =
    a (reconstruct P j (∏ i∈A,i.val)) * (if residual P j∣(∏ i∈A,i.val) then 1 else 0) *
      rowCoprimeMask (fun i : primePool (columns S P j)=>i.val) A (primaryGenerator j) *
      W (∏ i∈A,i.val) := by
  by_cases hm : rowCoprimeMask (fun i : primePool (columns S P j)=>i.val) A (primaryGenerator j)=0
  · simp only [hm,mul_zero,zero_mul]
  by_cases hW : W (∏ i∈A,i.val)=0
  · simp only [hW,mul_zero]
  have hcop := mask_nonzero_coprime (columns S P j) j (admissible_of_dvd hP hj) A hm
  by_cases hd : residual P j∣(∏ i∈A,i.val)
  · have hmem := (mem_columns hP.2.1 hj).mpr ⟨hA,hcop,hd,hcover hd hW hcop⟩
    simp only [reconstructedSelector,hmem,ite_true,hd,mul_one]
  · have hn : (∏ i∈A,i.val)∉columns S P j := by
      intro h
      exact hd ((mem_columns hP.2.1 hj).mp h).2.2.1
    simp only [reconstructedSelector,hn,ite_false,hd,mul_zero,zero_mul]

theorem singleton_primeMark {ι : Type*} [DecidableEq ι] (B A : Finset ι) :
    primeMark B (fun i=>{i}) (fun _ _=>(1:ℂ)) A = if B⊆A then 1 else 0 := by
  classical
  simp only [primeMark,primeSlot,Finset.sum_singleton]
  by_cases h : B⊆A
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro i hi
    exact ite_eq_left (h hi)
  · rw [ite_eq_right h]
    obtain ⟨i,hi,hn⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero hi (ite_eq_right hn)

theorem forcing_primeMark {ι : Type*} [DecidableEq ι]
    (Q : ι→Ideal Eis) [∀ i,(Q i).IsMaximal] (hinj : Function.Injective Q)
    (B A : Finset ι) :
    primeMark B (fun i=>{i}) (fun _ _=>(1:ℂ)) A =
      if (∏ i∈B,Q i)∣(∏ i∈A,Q i) then 1 else 0 := by
  classical
  have hd : (∏ i∈B,Q i)∣(∏ i∈A,Q i) ↔ B⊆A := by
    constructor
    · intro h i hi
      exact (FirstCauchyArithmetic.family_prime_dvd_product_iff Q hinj A i).mp
        ((Finset.dvd_prod_of_mem Q hi).trans h)
    · intro h
      exact Finset.prod_dvd_prod_of_subset B A Q h
  rw [singleton_primeMark,hd]
  split_ifs <;> rfl

theorem reconstructedSelector_forced_mark
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j∣P)
    (a : Ideal Eis→ℂ) (W : Ideal Eis→ℂ)
    (B A : Finset (primePool (columns S P j)))
    (hB : (∏ i∈B,i.val)=residual P j)
    (hA : Squarefree (∏ i∈A,i.val))
    (hcover : residual P j∣(∏ i∈A,i.val) → W (∏ i∈A,i.val)≠0 →
      IsCoprime (∏ i∈A,i.val) j → reconstruct P j (∏ i∈A,i.val)∈S) :
    reconstructedSelector S P j a A *
      rowCoprimeMask (fun i : primePool (columns S P j)=>i.val) A (primaryGenerator j) *
      W (∏ i∈A,i.val) =
    a (reconstruct P j (∏ i∈A,i.val)) * primeMark B (fun i=>{i}) (fun _ _=>(1:ℂ)) A *
      rowCoprimeMask (fun i : primePool (columns S P j)=>i.val) A (primaryGenerator j) *
      W (∏ i∈A,i.val) := by
  rw [forcing_primeMark (fun i : primePool (columns S P j)=>i.val) Subtype.val_injective B A,hB]
  exact reconstructedSelector_profile S hP hj a W A hA hcover

end SevenEighths.InverseInitialEnergyCallerSelector

end

end OAI
