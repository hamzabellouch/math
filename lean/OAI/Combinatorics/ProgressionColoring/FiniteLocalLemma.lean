import OAI.Combinatorics.ProgressionColoring.FiniteLocalLemmaMeasure
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

universe uOmega uI

namespace QuantitativeVanDerWaerden.FiniteLocalLemma

open scoped BigOperators

variable {Ω : Type uOmega} {I : Type uI} [Fintype Ω] [DecidableEq Ω] [DecidableEq I]

/-- Outcomes avoiding every bad event indexed by `T`. -/
noncomputable def avoid (bad : I → Finset Ω) (T : Finset I) : Finset Ω := by
  classical
  exact Finset.univ.filter fun ω => ∀ i ∈ T, ω ∉ bad i

@[simp] theorem mem_avoid {Ω : Type uOmega} {I : Type uI} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq I]
    (bad : I → Finset Ω) (T : Finset I) (ω : Ω) :
    ω ∈ avoid bad T ↔ ∀ i ∈ T, ω ∉ bad i := by
  classical
  simp [avoid]

@[simp] theorem avoid_empty (bad : I → Finset Ω) :
    avoid bad ∅ = Finset.univ := by
  classical
  ext ω
  simp

theorem avoid_insert (bad : I → Finset Ω) (i : I) (T : Finset I) :
    avoid bad (insert i T) = avoid bad T \ bad i := by
  classical
  ext ω
  simp [and_comm]

theorem avoid_antitone (bad : I → Finset Ω) {S T : Finset I} (hST : S ⊆ T) :
    avoid bad T ⊆ avoid bad S := by
  intro ω hω
  rw [mem_avoid] at hω ⊢
  exact fun i hi => hω i (hST hi)

theorem avoid_mass_split (P : Probability Ω) (bad : I → Finset Ω)
    (i : I) (T : Finset I) :
    P.mass (avoid bad (insert i T)) + P.mass (bad i ∩ avoid bad T) =
      P.mass (avoid bad T) := by
  simpa [avoid_insert, Finset.inter_comm] using P.split (avoid bad T) (bad i)

/-- Products of factors in `[0,1]` decrease when more factors are included. -/
theorem prod_antitone_of_unitInterval {S T : Finset I} {f : I → ℝ}
    (hST : S ⊆ T) (h0 : ∀ i ∈ T, 0 ≤ f i) (h1 : ∀ i ∈ T, f i ≤ 1) :
    (∏ i ∈ T, f i) ≤ ∏ i ∈ S, f i := by
  rw [← Finset.prod_sdiff hST]
  exact mul_le_of_le_one_left
    (Finset.prod_nonneg fun i hi => h0 i (hST hi))
    (Finset.prod_le_one₀
      (fun i hi => h0 i (Finset.mem_sdiff.mp hi).1)
      (fun i hi => h1 i (Finset.mem_sdiff.mp hi).1))

/-- Iterating bounds on intersections with one bad event yields the lower
bound for avoiding a finite collection of further events. -/
theorem avoid_union_lower (P : Probability Ω) (bad : I → Finset Ω)
    (z : I → ℝ) (target S U : Finset I)
    (hz : ∀ i, 0 ≤ 1 - z i)
    (hST : S ⊆ target) (hUT : U ⊆ target) (hSU : Disjoint S U)
    (hcond : ∀ R, R ⊂ target → ∀ i, i ∉ R →
      P.mass (bad i ∩ avoid bad R) ≤ z i * P.mass (avoid bad R)) :
    P.mass (avoid bad S) * (∏ i ∈ U, (1 - z i)) ≤
      P.mass (avoid bad (S ∪ U)) := by
  revert hUT hSU
  induction U using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert i U hiU ih =>
      intro hUT hSU
      have hiT : i ∈ target := hUT (Finset.mem_insert_self i U)
      have hUT' : U ⊆ target := fun j hj => hUT (Finset.mem_insert_of_mem hj)
      have hiS : i ∉ S := by
        intro hiS
        exact Finset.disjoint_left.mp hSU hiS (Finset.mem_insert_self i U)
      have hSU' : Disjoint S U := Finset.disjoint_left.mpr fun j hjS hjU =>
        Finset.disjoint_left.mp hSU hjS (Finset.mem_insert_of_mem hjU)
      have hiR : i ∉ S ∪ U := by simp [hiS, hiU]
      have hRT : S ∪ U ⊆ target := Finset.union_subset hST hUT'
      have hRproper : S ∪ U ⊂ target := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hRT, ?_⟩
        intro heq
        exact hiR (heq.symm ▸ hiT)
      have hbound := hcond (S ∪ U) hRproper i hiR
      have hsplit := avoid_mass_split P bad i (S ∪ U)
      have hstep : (1 - z i) * P.mass (avoid bad (S ∪ U)) ≤
          P.mass (avoid bad (S ∪ insert i U)) := by
        rw [Finset.union_insert]
        nlinarith
      rw [Finset.prod_insert hiU]
      calc
        P.mass (avoid bad S) * ((1 - z i) * ∏ j ∈ U, (1 - z j)) =
            (1 - z i) * (P.mass (avoid bad S) * ∏ j ∈ U, (1 - z j)) := by ring
        _ ≤ (1 - z i) * P.mass (avoid bad (S ∪ U)) :=
          mul_le_mul_of_nonneg_left (ih hUT' hSU') (hz i)
        _ ≤ P.mass (avoid bad (S ∪ insert i U)) := hstep

/-- The simultaneous induction behind the asymmetric local lemma. -/
theorem positive_and_conditional_bound (P : Probability Ω) (bad : I → Finset Ω)
    (neighbors : I → Finset I) (z : I → ℝ)
    (hzpos : ∀ i, 0 < z i) (hzlt : ∀ i, z i < 1)
    (hindependent : ∀ i T, i ∉ T → Disjoint T (neighbors i) →
      P.mass (bad i ∩ avoid bad T) = P.mass (bad i) * P.mass (avoid bad T))
    (hcriterion : ∀ i, P.mass (bad i) ≤ z i * ∏ j ∈ neighbors i, (1 - z j))
    (T : Finset I) :
    0 < P.mass (avoid bad T) ∧
      ∀ i, i ∉ T → P.mass (bad i ∩ avoid bad T) ≤ z i * P.mass (avoid bad T) := by
  refine Finset.strongInductionOn T ?_
  intro T ih
  have hpositive : 0 < P.mass (avoid bad T) := by
    by_cases hT : T = ∅
    · subst T
      simpa only [avoid_empty, P.univ] using (show (0 : ℝ) < 1 by norm_num)
    · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hT
      have hrec := ih (T.erase j) (Finset.erase_ssubset hj)
      have hjnot : j ∉ T.erase j := Finset.notMem_erase j T
      have hbound := hrec.2 j hjnot
      have hsplit := avoid_mass_split P bad j (T.erase j)
      rw [Finset.insert_erase hj] at hsplit
      have hstrict : 0 < (1 - z j) * P.mass (avoid bad (T.erase j)) :=
        mul_pos (sub_pos.mpr (hzlt j)) hrec.1
      nlinarith
  refine ⟨hpositive, ?_⟩
  intro i hiT
  let S := T \ neighbors i
  let U := T ∩ neighbors i
  have hST : S ⊆ T := Finset.sdiff_subset
  have hUT : U ⊆ T := Finset.inter_subset_left
  have hUN : U ⊆ neighbors i := Finset.inter_subset_right
  have hSN : Disjoint S (neighbors i) := by
    exact Finset.disjoint_left.mpr fun j hjS hjN => (Finset.mem_sdiff.mp hjS).2 hjN
  have hSU : Disjoint S U := Finset.disjoint_left.mpr fun j hjS hjU =>
    Finset.disjoint_left.mp hSN hjS (hUN hjU)
  have hSUeq : S ∪ U = T := by
    ext j
    by_cases hj : j ∈ neighbors i <;> simp [S, U, hj]
  have hiS : i ∉ S := fun h => hiT (hST h)
  have hlow : P.mass (avoid bad S) * (∏ j ∈ U, (1 - z j)) ≤
      P.mass (avoid bad T) := by
    rw [← hSUeq]
    exact avoid_union_lower P bad z T S U (fun j => le_of_lt (sub_pos.mpr (hzlt j)))
      hST hUT hSU (fun R hR => (ih R hR).2)
  have hprod : (∏ j ∈ neighbors i, (1 - z j)) ≤ ∏ j ∈ U, (1 - z j) :=
    prod_antitone_of_unitInterval hUN
      (fun j _ => le_of_lt (sub_pos.mpr (hzlt j)))
      (fun j _ => sub_le_self 1 (le_of_lt (hzpos j)))
  have hbad : P.mass (bad i) ≤ z i * ∏ j ∈ U, (1 - z j) :=
    (hcriterion i).trans (mul_le_mul_of_nonneg_left hprod (le_of_lt (hzpos i)))
  calc
    P.mass (bad i ∩ avoid bad T) ≤ P.mass (bad i ∩ avoid bad S) :=
      P.mono (Finset.inter_subset_inter_left (avoid_antitone bad hST))
    _ = P.mass (bad i) * P.mass (avoid bad S) := hindependent i S hiS hSN
    _ ≤ (z i * ∏ j ∈ U, (1 - z j)) * P.mass (avoid bad S) :=
      mul_le_mul_of_nonneg_right hbad (P.nonneg _)
    _ = z i * (P.mass (avoid bad S) * ∏ j ∈ U, (1 - z j)) := by ring
    _ ≤ z i * P.mass (avoid bad T) :=
      mul_le_mul_of_nonneg_left hlow (le_of_lt (hzpos i))

/-- Finite asymmetric local lemma, stated for a finite additive probability. -/
theorem finite_asymmetric_local_lemma [Fintype I]
    (P : Probability Ω) (bad : I → Finset Ω) (neighbors : I → Finset I)
    (z : I → ℝ) (hzpos : ∀ i, 0 < z i) (hzlt : ∀ i, z i < 1)
    (hindependent : ∀ i T, i ∉ T → Disjoint T (neighbors i) →
      P.mass (bad i ∩ avoid bad T) = P.mass (bad i) * P.mass (avoid bad T))
    (hcriterion : ∀ i, P.mass (bad i) ≤ z i * ∏ j ∈ neighbors i, (1 - z j)) :
    0 < P.mass (avoid bad Finset.univ) :=
  (positive_and_conditional_bound P bad neighbors z hzpos hzlt hindependent
    hcriterion Finset.univ).1

theorem exists_avoiding [Fintype I]
    (P : Probability Ω) (bad : I → Finset Ω) (neighbors : I → Finset I)
    (z : I → ℝ) (hzpos : ∀ i, 0 < z i) (hzlt : ∀ i, z i < 1)
    (hindependent : ∀ i T, i ∉ T → Disjoint T (neighbors i) →
      P.mass (bad i ∩ avoid bad T) = P.mass (bad i) * P.mass (avoid bad T))
    (hcriterion : ∀ i, P.mass (bad i) ≤ z i * ∏ j ∈ neighbors i, (1 - z j)) :
    ∃ ω, ∀ i, ω ∉ bad i := by
  have hpos := finite_asymmetric_local_lemma P bad neighbors z hzpos hzlt
    hindependent hcriterion
  have hne : (avoid bad Finset.univ).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    rw [h, P.mass_empty] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos
  obtain ⟨ω, hω⟩ := hne
  exact ⟨ω, fun i => (mem_avoid bad Finset.univ ω).mp hω i (Finset.mem_univ i)⟩

theorem finite_asymmetric_local_lemma_weights [Fintype I]
    (weight : Ω → ℝ) (weight_nonneg : ∀ ω, 0 ≤ weight ω)
    (weight_sum : ∑ ω, weight ω = 1)
    (bad : I → Finset Ω) (neighbors : I → Finset I)
    (z : I → ℝ) (hzpos : ∀ i, 0 < z i) (hzlt : ∀ i, z i < 1)
    (hindependent : ∀ i T, i ∉ T → Disjoint T (neighbors i) →
      (∑ ω ∈ bad i ∩ avoid bad T, weight ω) =
        (∑ ω ∈ bad i, weight ω) * (∑ ω ∈ avoid bad T, weight ω))
    (hcriterion : ∀ i, (∑ ω ∈ bad i, weight ω) ≤
      z i * ∏ j ∈ neighbors i, (1 - z j)) :
    0 < ∑ ω ∈ avoid bad Finset.univ, weight ω :=
  finite_asymmetric_local_lemma (Probability.ofWeights weight weight_nonneg weight_sum)
    bad neighbors z hzpos hzlt hindependent hcriterion

end QuantitativeVanDerWaerden.FiniteLocalLemma

end OAI
