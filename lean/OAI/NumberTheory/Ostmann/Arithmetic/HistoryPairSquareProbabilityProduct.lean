import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSquareProbabilityB

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryPairSquareProbability
open Construction HistoryPairPattern HistoryPairRows HistoryPairRepresentatives
variable {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

lemma probability_nonneg {α : Type*} [Fintype α] (P : α→Prop) :
    0 ≤ probability P := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem product_relative_loss {ι : Type*} (s : Finset ι) (a b e : ι→ℝ)
    (hb : ∀i∈s,0 ≤ b i) (he : ∀i∈s,0 ≤ e i)
    (hloss : ∀i∈s,0 ≤ a i-b i ∧ a i-b i ≤ e i*a i) :
    0 ≤ (∏i∈s,a i)-(∏i∈s,b i) ∧
    (∏i∈s,a i)-(∏i∈s,b i) ≤ (∑i∈s,e i)*(∏i∈s,a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hbs : ∀j∈s,0 ≤ b j := fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have hes : ∀j∈s,0 ≤ e j := fun j hj => he j (Finset.mem_insert_of_mem hj)
    have hls : ∀j∈s,0 ≤ a j-b j ∧ a j-b j ≤ e j*a j :=
      fun j hj => hloss j (Finset.mem_insert_of_mem hj)
    have hbi := hb i (Finset.mem_insert_self _ _)
    have hei := he i (Finset.mem_insert_self _ _)
    have hli := hloss i (Finset.mem_insert_self _ _)
    have hai : 0 ≤ a i := by linarith
    have has : ∀j∈s,0 ≤ a j := fun j hj => le_trans (hbs j hj) (sub_nonneg.mp (hls j hj).1)
    have hpa : 0 ≤ ∏j∈s,a j := Finset.prod_nonneg has
    have hpb : 0 ≤ ∏j∈s,b j := Finset.prod_nonneg hbs
    have hh := ih hbs hes hls
    simp only [Finset.prod_insert hi,Finset.sum_insert hi]
    constructor
    · exact sub_nonneg.mpr (mul_le_mul (sub_nonneg.mp hli.1) (sub_nonneg.mp hh.1) hpb hai)
    · calc
        a i*(∏j∈s,a j)-b i*(∏j∈s,b j) =
          a i*((∏j∈s,a j)-(∏j∈s,b j))+(a i-b i)*(∏j∈s,b j) := by ring
        _ ≤ a i*((∑j∈s,e j)*(∏j∈s,a j))+(e i*a i)*(∏j∈s,a j) :=
          add_le_add (mul_le_mul_of_nonneg_left hh.2 hai)
            (mul_le_mul hli.2 (sub_nonneg.mp hh.1) hpb (mul_nonneg hei hai))
        _ = (e i+∑j∈s,e j)*(a i*∏j∈s,a j) := by ring

theorem occurrence_reciprocal_eq_fibers (h k : History l) :
    (∑i : Occurrences h k,(1:ℝ)/(slot h k i).value)=
      ∑r : Representative h k,(Fintype.card (Fiber h k r):ℝ)/prime h k r := by
  rw [← Fintype.sum_fiberwise (label h k) (fun i => (1:ℝ)/(slot h k i).value)]
  apply Finset.sum_congr rfl
  intro r _
  have hv : ∀i : Fiber h k r,(slot h k i.val).value=prime h k r := by
    intro i
    rw [← prime_label h k i.val,i.property]
  change (∑i : Fiber h k r,(1:ℝ)/(slot h k i.val).value)=_
  simp only [hv,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one_div]

def actualUnitSquareProbability (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (r : Representative h k) : ℝ :=
  letI : Fact (prime h k r).Prime := ⟨representative_prime h k hs ks r⟩
  unitGoodProbability (prime h k r) Finset.univ (actualLeft h k hs ks r) (actualRight h k hs ks r)

def actualMixedSquareProbability (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (r : Representative h k) : ℝ :=
  letI : Fact (prime h k r).Prime := ⟨representative_prime h k hs ks r⟩
  mixedGoodProbability (prime h k r) Finset.univ (actualLeft h k hs ks r) (actualRight h k hs ks r)

theorem actual_unit_square_product_loss (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (hroot : RootGiantsAgree h k)
    (hx : ∀r : Representative h k,HistoryPairPolynomialKernel.NoAccidentalFlags h k hs ks r
      (fun j => (pairSample h k j:ZMod (prime h k r)))) :
    0 ≤ (∏r : Representative h k,HistoryPairPolynomialKernel.unitKernel h k hs ks r)-
      (∏r : Representative h k,actualUnitSquareProbability h k hs ks r) ∧
    (∏r : Representative h k,HistoryPairPolynomialKernel.unitKernel h k hs ks r)-
      (∏r : Representative h k,actualUnitSquareProbability h k hs ks r) ≤
      (∑i : Occurrences h k,(1:ℝ)/(slot h k i).value)*
        (∏r : Representative h k,HistoryPairPolynomialKernel.unitKernel h k hs ks r) := by
  rw [occurrence_reciprocal_eq_fibers]
  apply product_relative_loss
  · intro r _
    let : Fact (prime h k r).Prime := ⟨representative_prime h k hs ks r⟩
    exact probability_nonneg _
  · intro r _
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro r _
    let : Fact (prime h k r).Prime := ⟨representative_prime h k hs ks r⟩
    exact actual_unit_square_loss h k hs ks hroot r (hx r)

theorem actual_mixed_square_product_loss (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (hroot : RootGiantsAgree h k)
    (hx : ∀r : Representative h k,HistoryPairPolynomialKernel.NoAccidentalFlags h k hs ks r
      (fun j => (pairSample h k j:ZMod (prime h k r)))) :
    0 ≤ (∏r : Representative h k,HistoryPairPolynomialKernel.mixedKernel h k hs ks r)-
      (∏r : Representative h k,actualMixedSquareProbability h k hs ks r) ∧
    (∏r : Representative h k,HistoryPairPolynomialKernel.mixedKernel h k hs ks r)-
      (∏r : Representative h k,actualMixedSquareProbability h k hs ks r) ≤
      (∑i : Occurrences h k,(1:ℝ)/(slot h k i).value)*
        (∏r : Representative h k,HistoryPairPolynomialKernel.mixedKernel h k hs ks r) := by
  rw [occurrence_reciprocal_eq_fibers]
  apply product_relative_loss
  · intro r _
    let : Fact (prime h k r).Prime := ⟨representative_prime h k hs ks r⟩
    exact probability_nonneg _
  · intro r _
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro r _
    let : Fact (prime h k r).Prime := ⟨representative_prime h k hs ks r⟩
    exact actual_mixed_square_loss h k hs ks hroot r (hx r)

end Ostmann.Arithmetic.HistoryPairSquareProbability

end

end OAI
