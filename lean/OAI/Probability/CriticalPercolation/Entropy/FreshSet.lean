import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.Uniform01
import OAI.Probability.CriticalPercolation.Entropy.EndpointKernel

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical
open Set MeasureTheory Real
open scoped Interval

namespace CriticalPercolation.Priority
variable {I : Type*} [Fintype I]

def freshSet (i : I) (S : Finset {j : I // j ≠ i}) : Set (I → ℝ) :=
  {u | ∀ j ∈ S, u i < u j.val}

omit [Fintype I] in
lemma measurableSet_freshSet (i : I) (S : Finset {j : I // j ≠ i}) :
    MeasurableSet (freshSet i S) := by
  have he : freshSet i S = ⋂ j ∈ (S : Set {j : I // j ≠ i}),
        {u : I → ℝ | u i < u j.val} := by
    ext u
    simp [freshSet]
  rw [he]
  exact MeasurableSet.biInter S.finite_toSet.countable fun j _ =>
    measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j.val)

lemma integrable_eval_continuous (f : ℝ → ℝ) (hf : Continuous f) (i : I) :
    Integrable (fun u : I → ℝ => f (u i)) law := by
  apply integrable_comp_eval
  exact hf.integrableOn_Icc

lemma integral_freshSet (f : ℝ → ℝ) (hf : Continuous f) (i : I)
    (S : Finset {j : I // j ≠ i}) :
    (∫ u in freshSet i S, f (u i) ∂law) =
      ∫ t, f t * (1-t)^S.card ∂uniform01 := by
  let F : (I → ℝ) → ℝ := (freshSet i S).indicator (fun u => f (u i))
  have hF : Integrable F law :=
    (integrable_eval_continuous f hf i).indicator (measurableSet_freshSet i S)
  rw [← integral_indicator (measurableSet_freshSet i S)]
  change (∫ u, F u ∂law) = _
  rw [← (split_preserving i).symm.integral_comp' F]
  have hi : Integrable (F ∘ (split i).symm)
      (uniform01.prod (law (I := {j : I // j ≠ i}))) :=
    (split_preserving i).symm.integrable_comp_of_integrable hF
  rw [integral_prod (fun x => F ((split i).symm x)) (by simpa [Function.comp_def] using hi)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have he (u : {j : I // j ≠ i} → ℝ) : F ((split i).symm (t,u)) =
      f t * (if ∀ j ∈ S, t < u j then (1:ℝ) else 0) := by
    dsimp [F]
    simp only [Set.indicator_apply, freshSet, Set.mem_ofPred_eq, split_symm_apply,
      ↓reduceDIte]
    split_ifs <;> simp_all
  simp_rw [he]
  rw [integral_const_mul]
  congr 1
  convert integral_survival S ht using 1
  apply integral_congr_ae
  filter_upwards [] with u
  split_ifs <;> rfl

lemma uniform01_integral_eq_interval (f : ℝ → ℝ) :
    (∫ t, f t ∂uniform01) = ∫ t in (0:ℝ)..1, f t := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  rw [uniform01, integral_Icc_eq_integral_Ioc]

open FiniteEntropy in

lemma weighted_fresh_identity (i : I) (S : Finset {j : I // j ≠ i}) (hS : S.card ≤ 3) :
    (∫ u in freshSet i S, endpointKernel (u i) ∂law) = 1 := by
  rw [integral_freshSet _ continuous_endpointKernel, uniform01_integral_eq_interval]
  exact integral_endpointKernel_power hS

open FiniteEntropy in

lemma square_weight_integral (i : I) :
    (∫ u : I → ℝ, (endpointKernel (u i))^2 ∂law) = 16 := by
  rw [show law (I := I) = Measure.pi (fun _ : I => uniform01) from rfl,
    integral_comp_eval (μ := fun _ : I => uniform01) (i := i)
      (f := fun t => (endpointKernel t)^2) (continuous_endpointKernel.pow 2).aestronglyMeasurable,
    uniform01_integral_eq_interval]
  exact integral_endpointKernel_sq

end CriticalPercolation.Priority

namespace CriticalPercolation.Priority
variable {I : Type*} [Fintype I]

noncomputable def enumeration : List I := Finset.univ.toList

abbrev Order (I : Type*) [Fintype I] := {l : List I // l.Perm (enumeration (I := I))}

noncomputable instance : Fintype (Order I) :=
  Fintype.subtype ((enumeration (I := I)).permutations.toFinset) (by
    intro l
    simp [List.mem_permutations])

lemma order_nodup (o : Order I) : o.val.Nodup := by
  exact o.property.nodup_iff.mpr (Finset.nodup_toList _)

lemma mem_order (o : Order I) (i : I) : i ∈ o.val := by
  rw [o.property.mem_iff]
  simp [enumeration]

def cell (o : Order I) : Set (I → ℝ) :=
  {u | o.val.Pairwise fun i j => u i < u j}

omit [Fintype I] in
lemma measurableSet_pairwise (l : List I) :
    MeasurableSet {u : I → ℝ | l.Pairwise fun i j => u i < u j} := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hc : {u : I → ℝ | (i::l).Pairwise fun a b => u a < u b} =
        {u : I → ℝ | ∀ j ∈ l, u i < u j} ∩
          {u : I → ℝ | l.Pairwise fun a b => u a < u b} := by
      ext u; exact List.pairwise_cons
    rw [hc]
    apply MeasurableSet.inter _ ih
    have he : {u : I → ℝ | ∀ j ∈ l, u i < u j} =
        ⋂ j ∈ (l.toFinset : Set I), {u : I → ℝ | u i < u j} := by
      ext u
      simp
    rw [he]
    exact MeasurableSet.biInter l.toFinset.finite_toSet.countable fun (j : I) _ =>
      measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)

lemma measurableSet_cell (o : Order I) : MeasurableSet (cell o) :=
  measurableSet_pairwise o.val

lemma exists_cell (u : I → ℝ) (hu : Function.Injective u) : ∃ o : Order I, u ∈ cell o := by
  let r : I → I → Prop := fun i j => u i ≤ u j
  let : Std.Total r := ⟨fun i j => le_total (u i) (u j)⟩
  let : IsTrans I r := ⟨fun _ _ _ => le_trans⟩
  let l := (enumeration (I := I)).insertionSort r
  have hperm : l.Perm enumeration := List.perm_insertionSort r _
  refine ⟨⟨l,hperm⟩, ?_⟩
  have hp : l.Pairwise r := List.pairwise_insertionSort r _
  have hn : l.Pairwise (fun a b => a ≠ b) :=
    hperm.nodup_iff.mpr (Finset.nodup_toList _)
  have hh : l.Pairwise (fun a b => r a b ∧ a ≠ b) := hp.and hn
  exact hh.imp fun {i j} hij => lt_of_le_of_ne hij.1 (fun he => hij.2 (hu he))

lemma cell_disjoint {o o' : Order I} (h : o ≠ o') : Disjoint (cell o) (cell o') := by
  apply Set.disjoint_left.mpr
  intro u hu hu'
  apply h
  apply Subtype.ext
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => False.elim (lt_asymm hab hba))
    hu hu' (o.property.trans o'.property.symm)

lemma order_split (o : Order I) (i : I) :
    ∃ pre post : List I, o.val = pre++i::post ∧ i ∉ pre ∧ i ∉ post := by
  obtain ⟨pre,post,he⟩ := List.mem_iff_append.mp (mem_order o i)
  refine ⟨pre,post,he,?_,?_⟩
  all_goals
    have hn := order_nodup o
    rw [he, List.nodup_append, List.nodup_cons] at hn
  · exact fun hi => hn.2.2 i hi i (by simp) rfl
  · exact hn.2.1.1

lemma before_iff (u : I → ℝ) (o : Order I) (hu : u ∈ cell o) {pre post : List I}
    {i j : I} (he : o.val = pre++i::post) (hji : j ≠ i) :
    j ∈ pre ↔ u j < u i := by
  rw [cell, Set.mem_ofPred_eq, he, List.pairwise_append, List.pairwise_cons] at hu
  constructor
  · intro hj
    exact hu.2.2 j hj i (by simp)
  · intro hj
    have hm := mem_order o j
    rw [he, List.mem_append, List.mem_cons] at hm
    rcases hm with hp | h | ht
    · exact hp
    · exact False.elim (hji h)
    · exact False.elim (lt_asymm hj (hu.2.1.1 j ht))

end CriticalPercolation.Priority

end
end

end OAI
