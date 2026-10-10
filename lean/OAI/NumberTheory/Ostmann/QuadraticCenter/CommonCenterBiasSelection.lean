import OAI.NumberTheory.Ostmann.QuadraticCenter.CommonCenterBiasCard
import OAI.NumberTheory.Ostmann.QuadraticCenter.CommonCenterBiasMeans

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

lemma card_pos_of_nonzero_finite_mean {ι : Type*} (U : Finset ι) (f : ι → ℝ)
    {c : ℝ} (hc : 0 < c) (hm : c≤|(∑x∈U,f x)/U.card|) : 0 < U.card := by
  by_contra hU
  have he : U=∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hU)
  simp only [he,Finset.sum_empty,Finset.card_empty,Nat.cast_zero,zero_div,abs_zero] at hm
  linarith

theorem actual_commonCenter_large_bias_subsets (d : Decomposition) (X : ℕ)
    (P : Finset ℕ) (hP : 0 < P.card) (ε t : ℕ → ℤ) (m : ℕ) (h : ℤ)
    (hm : 0 < m) (hprime : ∀p∈P,p.Prime ∧ m < p)
    (hcenter : ∀p∈P,(p:ℤ)∣h-(m:ℤ)*t p) {δ : ℝ} (hδ : 0 < δ)
    (hbias : ∀p∈P,(ε p=1 ∨ ε p=-1) ∧
      δ/4≤(∑x∈positiveIntegerWindow d.A X,((ε p*jacobiSym (x-t p) p:ℤ):ℝ))/
        (positiveIntegerWindow d.A X).card ∧
      (∑x∈negativeIntegerWindow d.B X,((ε p*jacobiSym (x-t p) p:ℤ):ℝ))/
        (negativeIntegerWindow d.B X).card≤-δ/4) :
    ∃ A₀ D₀ : Finset ℤ,
      A₀⊆positiveIntegerWindow d.A X ∧ D₀⊆negativeIntegerWindow d.B X ∧
      (δ/8)*(positiveIntegerWindow d.A X).card≤(A₀.card:ℝ) ∧
      (δ/8)*(negativeIntegerWindow d.B X).card≤(D₀.card:ℝ) ∧
      0 < A₀.card ∧ 0 < D₀.card ∧
      ∀x∈A₀∪D₀,
        δ/8≤|affineKernelAverage P (commonCenterOrientation ε m) m h x| ∧
        (m:ℤ)*x-h≠0 := by
  classical
  let F : ℤ → ℝ := affineKernelAverage P (commonCenterOrientation ε m) m h
  let A := positiveIntegerWindow d.A X
  let D := negativeIntegerWindow d.B X
  obtain ⟨_,hF,hA,hD⟩ := actual_commonCenter_bias_transport d X P hP ε t m h hm
    hprime hcenter δ hbias
  have hAm : δ/4≤|(∑x∈A,F x)/A.card| := hA.trans (le_abs_self _)
  have hDm : δ/4≤|(∑x∈D,F x)/D.card| := by
    have hn : δ/4≤-((∑x∈D,F x)/D.card) := by change _≤-δ/4 at hD; linarith
    exact hn.trans (neg_le_abs _)
  have hc : 0 < δ/4 := by positivity
  have hAc := card_pos_of_nonzero_finite_mean A F hc hAm
  have hDc := card_pos_of_nonzero_finite_mean D F hc hDm
  let A₀ := A.filter (fun x => δ/8≤|F x|)
  let D₀ := D.filter (fun x => δ/8≤|F x|)
  have he : δ/4/2=δ/8 := by ring
  have hAb : (δ/8)*(A.card:ℝ)≤(A₀.card:ℝ) := by
    simpa only [he] using card_large_abs_of_mean A F hAc hc.le (fun x _ => hF x) hAm
  have hDb : (δ/8)*(D.card:ℝ)≤(D₀.card:ℝ) := by
    simpa only [he] using card_large_abs_of_mean D F hDc hc.le (fun x _ => hF x) hDm
  have hA₀ : 0 < A₀.card := by
    have hpos : (0:ℝ)<A₀.card := lt_of_lt_of_le (mul_pos (by positivity)
      (by exact_mod_cast hAc)) hAb
    exact_mod_cast hpos
  have hD₀ : 0 < D₀.card := by
    have hpos : (0:ℝ)<D₀.card := lt_of_lt_of_le (mul_pos (by positivity)
      (by exact_mod_cast hDc)) hDb
    exact_mod_cast hpos
  refine ⟨A₀,D₀,Finset.filter_subset _ _,Finset.filter_subset _ _,hAb,hDb,hA₀,hD₀,?_⟩
  intro x hx
  have hxF : δ/8≤|F x| := by
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp hx).2
    · exact (Finset.mem_filter.mp hx).2
  exact ⟨hxF,affineKernelAverage_numerator_ne_zero P (fun p hp => (hprime p hp).1)
    _ m h x (by positivity : 0 < δ/8) hxF⟩

end Ostmann.QuadraticCenter

end

end OAI
