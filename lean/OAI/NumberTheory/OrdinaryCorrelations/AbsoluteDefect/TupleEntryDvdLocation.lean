import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MixedWeight

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryTwoScaleCofactor
open Finset OrdinaryDirichletMeanSquare OrdinaryPrimeDirichletMoments
open OrdinaryDirichletFiberMoments SourcePrimeFactor OrdinaryRestrictedCofactor

lemma tuple_entry_dvd_location {A : Finset ℕ} {k : ℕ}
    (z : (Fin k → A) × ℕ) (i : Fin k) : (z.1 i : ℕ) ∣ productLocation z := by
  exact dvd_mul_of_dvd_left (dvd_prod_of_mem _ (mem_univ i)) _

theorem multiplication_fiber_card (A : Finset ℕ) (hA : ∀p∈A,Nat.Prime p)
    (k M n : ℕ) :
    ((powersAndCofactors A k M).filter (fun z => productLocation z = n)).card ≤
      (primeCount A n)^k := by
  classical
  let F := (powersAndCofactors A k M).filter (fun z => productLocation z = n)
  let D := A.filter (fun p => p ∣ n)
  let g : F → (Fin k → D) := fun z i =>
    ⟨(z.val.1 i : ℕ), mem_filter.mpr ⟨(z.val.1 i).property,
      (mem_filter.mp z.property).2 ▸ tuple_entry_dvd_location z.val i⟩⟩
  have hg : Function.Injective g := by
    intro z w heq
    have ht : z.val.1 = w.val.1 := by
      funext i
      apply Subtype.ext
      exact congrArg (fun p : D => (p : ℕ)) (congrFun heq i)
    have hm : z.val.2 = w.val.2 := by
      apply Nat.eq_of_mul_eq_mul_left (tupleProduct_pos hA z.val.1)
      have hz := (mem_filter.mp z.property).2
      have hw := (mem_filter.mp w.property).2
      dsimp [productLocation] at hz hw
      rw [← ht] at hw
      exact hz.trans hw.symm
    exact Subtype.ext (Prod.ext ht hm)
  have hc := Fintype.card_le_of_injective g hg
  simpa [F, D, primeCount, Fintype.card_fun] using hc

lemma primeCount_tuple_mul (A : Finset ℕ) (hA : ∀p∈A,Nat.Prime p)
    {k : ℕ} (v : Fin k → A) (m : ℕ) :
    primeCount A (tupleProduct v * m) ≤ primeCount A m + k := by
  classical
  have hsub : A.filter (fun p => p ∣ tupleProduct v * m) ⊆
      A.filter (fun p => p ∣ m) ∪ univ.image (fun i => (v i : ℕ)) := by
    intro p hp
    obtain ⟨hpA,hpd⟩ := mem_filter.mp hp
    rcases (hA p hpA).dvd_mul.mp hpd with ht | hm
    · apply Finset.mem_union_right
      obtain ⟨i, _, hi⟩ := (hA p hpA).prime.dvd_finsetProd_iff (fun i : Fin k => (v i : ℕ)) |>.mp ht
      apply mem_image.mpr
      refine ⟨i, mem_univ _, ?_⟩
      exact ((hA _ (v i).property).eq_one_or_self_of_dvd _ hi).resolve_left
        (hA p hpA).ne_one |>.symm
    · apply Finset.mem_union_left
      exact mem_filter.mpr ⟨hpA,hm⟩
  calc
    _ ≤ (A.filter (fun p => p ∣ m) ∪ univ.image (fun i => (v i : ℕ))).card :=
      Finset.card_le_card hsub
    _ ≤ (A.filter (fun p => p ∣ m)).card + (Finset.univ.image (fun i => (v i : ℕ))).card :=
      Finset.card_union_le _ _
    _ ≤ _ := by
      exact Nat.add_le_add_left (by simpa using (Finset.card_image_le (s := (univ : Finset (Fin k)))
        (f := fun i => (v i : ℕ)))) _

theorem mixedEnergy_count_bound (f : ℕ → ℂ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (A P : Finset ℕ) (hA : ∀p∈A,Nat.Prime p)
    (k M : ℕ) :
    mixedEnergy f χ A P k M ≤
      ∑ z ∈ powersAndCofactors A k M,
        ((primeCount A z.2 + k : ℕ) : ℝ)^k * ‖mixedWeight f χ A P z‖^2 := by
  apply (collect_energy (powersAndCofactors A k M) productLocation
    (mixedWeight f χ A P)).trans
  apply sum_le_sum
  intro z hz
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hc := (multiplication_fiber_card A hA k M (productLocation z)).trans
    (Nat.pow_le_pow_left (primeCount_tuple_mul A hA z.1 z.2) k)
  exact_mod_cast hc

end OrdinaryTwoScaleCofactor

end

end OAI
