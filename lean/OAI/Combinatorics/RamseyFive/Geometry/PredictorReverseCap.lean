import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.UniformCutoff
import OAI.Combinatorics.RamseyFive.Geometry.DimensionTwoPublic
import OAI.Combinatorics.RamseyFive.Probability.CapNumerics
import OAI.Combinatorics.RamseyFive.Entropy.CapDecoder

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def lowIncidence (C : Finset (ℙ K (Dual K V))) : Finset (ℙ K V) :=
  Finset.univ.filter fun x=>((C.filter (Incident x)).card:ℝ) ≤ (C.card:ℝ)/(2*Nat.card K)

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma incidences_eq_sum_card (S : Finset (ℙ K V)) (C : Finset (ℙ K (Dual K V))) :
    (incidences S C:ℝ)=∑x∈S,((C.filter (Incident x)).card:ℝ) := by
  rw [incidences_eq_sum,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [incidenceEntry,Finset.sum_boole]

theorem lowIncidence_mass {d : ℕ} (hdim : finrank K V=d+1) (hd : 1 ≤ d)
    (hq : 3 ≤ Nat.card K) (C : Finset (ℙ K (Dual K V))) :
    ((lowIncidence C).card:ℝ)*C.card ≤ 16*(Nat.card K:ℝ)^(d+1) := by
  apply sparse_half_rectangle_size hdim hd hq
  rw [incidences_eq_sum_card]
  calc
    _ ≤ ∑x∈lowIncidence C,(C.card:ℝ)/(2*Nat.card K) :=
      Finset.sum_le_sum fun x hx=>(Finset.mem_filter.mp hx).2
    _ = _ := by simp;ring

theorem expected_projective_cap {d : ℕ} (hdim : finrank K V=d+1) (hd : 1 ≤ d)
    (hq : 3 ≤ Nat.card K) (C : Finset (ℙ K (Dual K V))) (hC : C.Nonempty)
    (U : Finset (ℙ K V)) (n : ℕ) :
    (∑row,iid (uniformOn C hC) (Fin n) row*
      ((cap Incident U (Nat.card K) row).card:ℝ)) ≤
      16*(Nat.card K:ℝ)^(d+1)/C.card +
        U.card*Real.exp (-(n:ℝ)/(20*Nat.card K)) := by
  have hqpos : (0:ℝ) < Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hc : (0:ℝ) < C.card := by exact_mod_cast Finset.card_pos.mpr hC
  have hh := expected_cap_card Incident U (lowIncidence C) C hC n (Nat.card K) hqpos
    (by
      intro x hx hlow
      have hdg : (C.card:ℝ)/(2*Nat.card K) < (C.filter (Incident x)).card := by
        simpa only [lowIncidence,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using hlow
      apply (le_div_iff₀ hc).mpr
      calc
        _ = (C.card:ℝ)/(2*Nat.card K) := by ring
        _ ≤ _ := hdg.le)
  have hb := (le_div_iff₀ hc).mpr (lowIncidence_mass hdim hd hq C)
  linarith

noncomputable def lowPencil (C : Finset (ℙ K V)) : Finset (ℙ K (Dual K V)) :=
  Finset.univ.filter fun y=>((C.filter fun x=>Incident x y).card:ℝ) ≤ (C.card:ℝ)/(2*Nat.card K)

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma incidences_eq_sum_card_right (C : Finset (ℙ K V)) (T : Finset (ℙ K (Dual K V))) :
    (incidences C T:ℝ)=∑y∈T,((C.filter fun x=>Incident x y).card:ℝ) := by
  rw [incidences_eq_sum]
  apply Finset.sum_congr rfl
  intro y hy
  simp only [incidenceEntry,Finset.sum_boole]

theorem lowPencil_mass {d : ℕ} (hdim : finrank K V=d+1) (hd : 1 ≤ d)
    (hq : 3 ≤ Nat.card K) (C : Finset (ℙ K V)) :
    ((lowPencil C).card:ℝ)*C.card ≤ 16*(Nat.card K:ℝ)^(d+1) := by
  have hh : (C.card:ℝ)*(lowPencil C).card ≤ 16*(Nat.card K:ℝ)^(d+1) := by
    apply sparse_half_rectangle_size hdim hd hq
    rw [incidences_eq_sum_card_right]
    calc
      _ ≤ ∑y∈lowPencil C,(C.card:ℝ)/(2*Nat.card K) :=
        Finset.sum_le_sum fun y hy=>(Finset.mem_filter.mp hy).2
      _ = _ := by simp; ring
  simpa only [mul_comm] using hh

theorem expected_dual_cap {d : ℕ} (hdim : finrank K V=d+1) (hd : 1 ≤ d)
    (hq : 3 ≤ Nat.card K) (C : Finset (ℙ K V)) (hC : C.Nonempty)
    (U : Finset (ℙ K (Dual K V))) (n : ℕ) :
    (∑row,iid (uniformOn C hC) (Fin n) row*
      ((cap (fun y x=>Incident x y) U (Nat.card K) row).card:ℝ)) ≤
      16*(Nat.card K:ℝ)^(d+1)/C.card +
        U.card*Real.exp (-(n:ℝ)/(20*Nat.card K)) := by
  have hqpos : (0:ℝ) < Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hc : (0:ℝ) < C.card := by exact_mod_cast Finset.card_pos.mpr hC
  have hh := expected_cap_card (fun y x=>Incident x y) U (lowPencil C) C hC n (Nat.card K) hqpos
    (by
      intro y hy hlow
      have hdeg : (C.card:ℝ)/(2*Nat.card K) < (C.filter fun x=>Incident x y).card := by
        simpa only [lowPencil,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using hlow
      apply (le_div_iff₀ hc).mpr
      calc
        _ = (C.card:ℝ)/(2*Nat.card K) := by ring
        _ ≤ _ := hdeg.le)
  have hb := (le_div_iff₀ hc).mpr (lowPencil_mass hdim hd hq C)
  linarith

end
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem geometric_validation_mass {d : ℕ} (hdim : finrank K V=d+1) (hd : 1 ≤ d)
    (hq : 3 ≤ Nat.card K) (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (X C : Finset (ℙ K (Dual K V))) (hC : C.Nonempty) (hCX : C⊆X)
    (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hcapture : c*X.card ≤ C.card)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences S X ≤ c*S.card*X.card)
    (n : ℕ) (hn : 0 < n)
    (hlen : 20*(Nat.card K:ℝ)*Real.log ((U.card:ℝ)/S.card) ≤ n) :
    (9:ℝ)/10 ≤ eventMass (iid (uniformOn C hC) (Fin n))
      (validationRows Incident S U C n (Nat.card K)
        ((320/c+320)*(Nat.card K:ℝ)^(d+1)/X.card)) := by
  have hqpos : (0:ℝ) < Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hCpos : (0:ℝ) < C.card := by exact_mod_cast Finset.card_pos.mpr hC
  have hXpos : (0:ℝ) < X.card := by exact_mod_cast Finset.card_pos.mpr (hC.mono hCX)
  have hSpos : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hUpos : (0:ℝ) < U.card := by exact_mod_cast Finset.card_pos.mpr (hS.mono hSU)
  have hprod := sparse_half_rectangle_size hdim hd hq S X
    (density_half (incidences S X) S.card X.card c (Nat.card K)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hqpos hc1 hsparse)
  have hm := (expected_projective_cap hdim hd hq C hC U n).trans
    (captured_cap_budget ((Nat.card K:ℝ)^(d+1)) X.card c C.card S.card U.card (Nat.card K) n
      (by positivity) hXpos hc hCpos hSpos hUpos hqpos hcapture hprod hlen)
  apply validationRows_mass Incident S U hS hSU C hC n hn (Nat.card K) _ hqpos (by positivity) hm
  have hsum : (∑a∈S,((C.filter (Incident a)).card:ℝ)) ≤ (incidences S X:ℝ) := by
    rw [incidences_eq_sum_card]
    apply Finset.sum_le_sum
    intro a ha
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hCX)
  apply rejection_from_capture _ _ c _ _ _ hCpos (Nat.cast_nonneg _) hcapture
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans hsparse

theorem geometric_dual_validation_mass {d : ℕ} (hdim : finrank K V=d+1) (hd : 1 ≤ d)
    (hq : 3 ≤ Nat.card K) (S U : Finset (ℙ K (Dual K V))) (hS : S.Nonempty) (hSU : S⊆U)
    (X C : Finset (ℙ K V)) (hC : C.Nonempty) (hCX : C⊆X)
    (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hcapture : c*X.card ≤ C.card)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences X S ≤ c*S.card*X.card)
    (n : ℕ) (hn : 0 < n)
    (hlen : 20*(Nat.card K:ℝ)*Real.log ((U.card:ℝ)/S.card) ≤ n) :
    (9:ℝ)/10 ≤ eventMass (iid (uniformOn C hC) (Fin n))
      (validationRows (fun y x=>Incident x y) S U C n (Nat.card K)
        ((320/c+320)*(Nat.card K:ℝ)^(d+1)/X.card)) := by
  have hqpos : (0:ℝ) < Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hCpos : (0:ℝ) < C.card := by exact_mod_cast Finset.card_pos.mpr hC
  have hXpos : (0:ℝ) < X.card := by exact_mod_cast Finset.card_pos.mpr (hC.mono hCX)
  have hSpos : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hUpos : (0:ℝ) < U.card := by exact_mod_cast Finset.card_pos.mpr (hS.mono hSU)
  have hdensity : (incidences X S:ℝ) ≤ X.card*S.card/(2*(Nat.card K)) := by
    have hh := density_half (incidences X S) S.card X.card c (Nat.card K)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hqpos hc1 hsparse
    simpa only [mul_comm] using hh
  have hprod : (S.card:ℝ)*X.card ≤ 16*(Nat.card K:ℝ)^(d+1) := by
    simpa only [mul_comm] using sparse_half_rectangle_size hdim hd hq X S hdensity
  have hm := (expected_dual_cap hdim hd hq C hC U n).trans
    (captured_cap_budget ((Nat.card K:ℝ)^(d+1)) X.card c C.card S.card U.card (Nat.card K) n
      (by positivity) hXpos hc hCpos hSpos hUpos hqpos hcapture hprod hlen)
  apply validationRows_mass (fun y x=>Incident x y) S U hS hSU C hC n hn (Nat.card K) _ hqpos (by positivity) hm
  have hsum : (∑y∈S,((C.filter fun x=>Incident x y).card:ℝ)) ≤ (incidences X S:ℝ) := by
    rw [incidences_eq_sum_card_right]
    apply Finset.sum_le_sum
    intro y hy
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hCX)
  apply rejection_from_capture _ _ c _ _ _ hCpos (Nat.cast_nonneg _) hcapture
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans hsparse

end SharpRamseyFive.ProjectiveIncidence
namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

omit [Fintype A] in
theorem validated_public_test (R : A→B→Prop) (S U : Finset A)
    (C X W : Finset B) (hC : C.Nonempty) (hW : W.Nonempty) (hCW : C⊆W)
    (hCX : C⊆X) (q c M : ℝ) (hq : 1 ≤ q) (hc : 0 < c)
    (hsize : c*X.card ≤ C.card) (n : ℕ) (hn : 0 < n)
    (hE : (9:ℝ)/10 ≤ eventMass (iid (uniformOn C hC) (Fin n))
      (validationRows R S U C n q M)) :
    let N := uniformCutoff q C W n
    let E := validationRows R S U C n q M
    let p := map (iid (iid (uniformOn W hW) (Fin n)) (Fin N)) (firstAccepted E (n := N))
    p none ≤ Real.exp (-q) ∧
    Real.log N ≤ Real.log (2*q)-Real.log ((9:ℝ)/10)+(n:ℝ)*Real.log ((W.card:ℝ)/C.card) ∧
    (∀t : Fin N→Fin n→B,∀row, firstAccepted E t=some row →
      ∃i : Fin N,cap R U q (t i)⊆U ∧ ((cap R U q (t i)).card:ℝ)≤M ∧
        (9:ℝ)/10*S.card ≤ (S∩cap R U q (t i)).card) ∧
    (∀H : Finset B,eventMass p
      ((Finset.univ.filter fun row => (1/(5*q))*n≤hits H row).image some) ≤
      (50*q/(9*c))*(((H∩X).card:ℝ)/X.card)) := by
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hsource : ∀row∈validationRows R S U C n q M,∀i,row i∈C := by
    intro row hr
    exact (Finset.mem_filter.mp hr).2.1
  refine ⟨uniform_cutoff_failure q C W hC hW hCW n _ hsource hE,
    uniformCutoff_log q hq C W hC hW hCW n,?_,?_⟩
  · intro t row hr
    exact validation_decode R S U C n _ q M t row hr
  · intro H
    exact fresh_test_domination C X W H hC hW hCW hCX q c hqpos hc hsize n _ hn
      (uniformCutoff_pos q hqpos C W hC hW n) _ hsource hE

end SharpRamseyFive.ReverseCap

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem geometric_public_fresh_test {d : ℕ} (hdim : finrank K V=d+1) (hd : 1 ≤ d)
    (hq : 3 ≤ Nat.card K) (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (X C W : Finset (ℙ K (Dual K V))) (hC : C.Nonempty) (hW : W.Nonempty)
    (hCX : C⊆X) (hCW : C⊆W) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hcapture : c*X.card ≤ C.card)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences S X ≤ c*S.card*X.card)
    (n : ℕ) (hn : 0 < n)
    (hlen : 20*(Nat.card K:ℝ)*Real.log ((U.card:ℝ)/S.card) ≤ n) :
    let q : ℝ := Nat.card K
    let M := (320/c+320)*q^(d+1)/X.card
    let N := uniformCutoff q C W n
    let E := validationRows Incident S U C n q M
    let p := map (iid (iid (uniformOn W hW) (Fin n)) (Fin N)) (firstAccepted E (n := N))
    p none ≤ Real.exp (-q) ∧
    Real.log N ≤ Real.log (2*q)-Real.log ((9:ℝ)/10)+(n:ℝ)*Real.log ((W.card:ℝ)/C.card) ∧
    (∀t : Fin N→Fin n→ℙ K (Dual K V),∀row, firstAccepted E t=some row →
      ∃i : Fin N,cap Incident U q (t i)⊆U ∧ ((cap Incident U q (t i)).card:ℝ)≤M ∧
        (9:ℝ)/10*S.card ≤ (S∩cap Incident U q (t i)).card) ∧
    (∀H : Finset (ℙ K (Dual K V)),eventMass p
      ((Finset.univ.filter fun row => (1/(5*q))*n≤hits H row).image some) ≤
      (50*q/(9*c))*(((H∩X).card:ℝ)/X.card)) := by
  exact validated_public_test Incident S U C X W hC hW hCW hCX (Nat.card K) c _
    (by exact_mod_cast hq.trans' (by omega : 1 ≤ 3)) hc hcapture n hn
    (geometric_validation_mass hdim hd hq S U hS hSU X C hC hCX c hc hc1 hcapture hsparse n hn hlen)

theorem geometric_public_dual_fresh_test {d : ℕ} (hdim : finrank K V=d+1) (hd : 1 ≤ d)
    (hq : 3 ≤ Nat.card K) (S U : Finset (ℙ K (Dual K V))) (hS : S.Nonempty) (hSU : S⊆U)
    (X C W : Finset (ℙ K V)) (hC : C.Nonempty) (hW : W.Nonempty)
    (hCX : C⊆X) (hCW : C⊆W) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hcapture : c*X.card ≤ C.card)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences X S ≤ c*S.card*X.card)
    (n : ℕ) (hn : 0 < n)
    (hlen : 20*(Nat.card K:ℝ)*Real.log ((U.card:ℝ)/S.card) ≤ n) :
    let q : ℝ := Nat.card K
    let M := (320/c+320)*q^(d+1)/X.card
    let N := uniformCutoff q C W n
    let E := validationRows (fun y x=>Incident x y) S U C n q M
    let p := map (iid (iid (uniformOn W hW) (Fin n)) (Fin N)) (firstAccepted E (n := N))
    p none ≤ Real.exp (-q) ∧
    Real.log N ≤ Real.log (2*q)-Real.log ((9:ℝ)/10)+(n:ℝ)*Real.log ((W.card:ℝ)/C.card) ∧
    (∀t : Fin N→Fin n→ℙ K V,∀row, firstAccepted E t=some row →
      ∃i : Fin N,cap (fun y x=>Incident x y) U q (t i)⊆U ∧ ((cap (fun y x=>Incident x y) U q (t i)).card:ℝ)≤M ∧
        (9:ℝ)/10*S.card ≤ (S∩cap (fun y x=>Incident x y) U q (t i)).card) ∧
    (∀H : Finset (ℙ K V),eventMass p
      ((Finset.univ.filter fun row => (1/(5*q))*n≤hits H row).image some) ≤
      (50*q/(9*c))*(((H∩X).card:ℝ)/X.card)) := by
  exact validated_public_test (fun y x=>Incident x y) S U C X W hC hW hCW hCX (Nat.card K) c _
    (by exact_mod_cast hq.trans' (by omega : 1 ≤ 3)) hc hcapture n hn
    (geometric_dual_validation_mass hdim hd hq S U hS hSU X C hC hCX c hc hc1 hcapture hsparse n hn hlen)

end SharpRamseyFive.ProjectiveIncidence

end OAI
