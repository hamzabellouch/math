import Mathlib
import OAI.Combinatorics.TriangleRemoval.Queries.TreeBind

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave
open scoped BigOperators

theorem trueProbability_map {A : Type*} [Fintype A] (p : PMF A) (b : A → Bool) :
    trueProbability (p.map b) = ∑ x, (p x).toReal * (if b x then 1 else 0) := by
  change trueProbability (p.bind (fun x => PMF.pure (b x))) = _
  simp only [trueProbability_bind, trueProbability_pure]

theorem boolean_coupling_bound {A : Type*} [Fintype A] (p : PMF A)
    (b₁ b₂ bad : A → Bool)
    (hagrees : ∀ x ∈ p.support, bad x = false → b₁ x = b₂ x) :
    |trueProbability (p.map b₁) - trueProbability (p.map b₂)| ≤
      trueProbability (p.map bad) := by
  rw [trueProbability_map, trueProbability_map, trueProbability_map,
    ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : p x = 0
  · simp only [hx, ENNReal.toReal_zero, zero_mul, sub_self, abs_zero, le_refl]
  · have hs : x ∈ p.support := hx
    have ha := hagrees x hs
    rw [← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    cases h₁ : b₁ x <;> cases h₂ : b₂ x <;> cases hb : bad x <;>
      simp_all

namespace ExposureTree
variable {K V : Type*} [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]

theorem independent_exposure_error (ν : K → PMF V) (P : ExposureTree K V Bool) :
    |trueProbability ((productPMF ν).map (fun ω => evaluate ω P)) -
      trueProbability (fresh ν P)| ≤
        trueProbability ((freshRecorded ν P ∅).map Prod.snd) := by
  have hh := boolean_coupling_bound (jointLaw ν P) Prod.fst (fun x => x.2.1)
    (fun x => x.2.2) (fun x hx hb => jointLaw_agrees ν P x hx hb)
  have hfst : (jointLaw ν P).map Prod.fst =
      (productPMF ν).map (fun ω => evaluate ω P) := jointLaw_fixed ν P
  have hsnd : (jointLaw ν P).map (fun x => x.2.1) = fresh ν P := by
    change (jointLaw ν P).map (Prod.fst ∘ Prod.snd) = _
    rw [← PMF.map_comp, jointLaw_fresh, freshRecorded_outcome]
  have hbad : (jointLaw ν P).map (fun x => x.2.2) =
      (freshRecorded ν P ∅).map Prod.snd := by
    change (jointLaw ν P).map (Prod.snd ∘ Prod.snd) = _
    rw [← PMF.map_comp, jointLaw_fresh]
  simpa only [hfst, hsnd, hbad] using hh

end ExposureTree

theorem pmf_map_congr_support {A B : Type*} (p : PMF A) (f g : A → B)
    (h : ∀ x ∈ p.support, f x = g x) : p.map f = p.map g := by
  unfold PMF.map
  apply pmf_bind_congr_on_support
  intro x hx
  rw [Function.comp_apply, Function.comp_apply, h x hx]

theorem productPMF_coord {K V : Type*} [Fintype K] [DecidableEq K]
    [Fintype V] [DecidableEq V] (ν : K → PMF V) (k : K) :
    (productPMF ν).map (fun ω => ω k) = ν k := by
  rw [productPMF_split ν k, PMF.map_bind]
  have hconst : ∀ v, (productPMF (Function.update ν k (PMF.pure v))).map (fun ω => ω k) =
      PMF.pure v := by
    intro v
    conv_rhs => rw [← PMF.map_const (p := productPMF (Function.update ν k (PMF.pure v)))]
    apply pmf_map_congr_support
    intro ω hω
    have hh := (productPMF_support _ _).mp hω k
    simpa only [Function.update_self, PMF.mem_support_pure_iff, Function.const_apply] using hh
  simp only [hconst, PMF.bind_pure]

theorem productPMF_pair {K V : Type*} [Fintype K] [DecidableEq K]
    [Fintype V] [DecidableEq V] (ν : K → PMF V) (a b : K) (hab : a ≠ b) :
    (productPMF ν).map (fun ω => (ω a, ω b)) =
      (ν a).bind (fun v => (ν b).map (fun w => (v, w))) := by
  rw [productPMF_split ν a, PMF.map_bind]
  congr 1
  funext v
  have hm : (productPMF (Function.update ν a (PMF.pure v))).map (fun ω => (ω a, ω b)) =
      (productPMF (Function.update ν a (PMF.pure v))).map (fun ω => (v, ω b)) := by
    apply pmf_map_congr_support
    intro ω hω
    have hh := (productPMF_support _ _).mp hω a
    have ha : ω a = v := by simpa only [Function.update_self, PMF.mem_support_pure_iff] using hh
    rw [ha]
  rw [hm]
  change (productPMF (Function.update ν a (PMF.pure v))).map
    ((fun w => (v, w)) ∘ (fun ω => ω b)) = _
  rw [← PMF.map_comp, productPMF_coord, Function.update_of_ne (Ne.symm hab)]

theorem boolean_union_bound {A I : Type*} [Fintype A] [Fintype I]
    (p : PMF A) (bad : A → Bool) (events : I → A → Bool)
    (hcover : ∀ x ∈ p.support, bad x = true → ∃ i, events i x = true) :
    trueProbability (p.map bad) ≤ ∑ i, trueProbability (p.map (events i)) := by
  classical
  simp only [trueProbability_map]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  rw [← Finset.mul_sum]
  by_cases hx : p x = 0
  · simp [hx]
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  by_cases hb : bad x = true
  · obtain ⟨i, hi⟩ := hcover x hx hb
    simp only [hb, ↓reduceIte]
    have him : (if events i x then (1 : ℝ) else 0) = 1 := by simp [hi]
    calc
      (1 : ℝ) = (if events i x then 1 else 0) := him.symm
      _ ≤ ∑ j, (if events j x then (1 : ℝ) else 0) :=
        Finset.single_le_sum (f := fun j => if events j x then (1 : ℝ) else 0)
          (fun j _ => by split <;> positivity) (Finset.mem_univ i)
  · simp only [hb, Bool.false_eq_true, ↓reduceIte]
    exact Finset.sum_nonneg (fun i _ => by split <;> positivity)

theorem grid_table_pair_tie {K : Type*} [Fintype K] [DecidableEq K]
    (N : ℕ) [NeZero N] (a b : K) (hab : a ≠ b) :
    trueProbability ((productPMF (gridPriorities (τ := K) N)).map
      (fun ω => decide (ω a = ω b))) = 1 / (N : ℝ) := by
  have hpair := productPMF_pair (gridPriorities (τ := K) N) a b hab
  have hh := congrArg (fun q : PMF (Fin N × Fin N) =>
    q.map (fun z => decide (z.1 = z.2))) hpair
  simp only [PMF.map_comp, PMF.map_bind] at hh
  change (productPMF (gridPriorities (τ := K) N)).map (fun ω => decide (ω a = ω b)) =
    (gridPriorities N a).bind (fun v => (gridPriorities N b).map (fun w => decide (v = w))) at hh
  rw [hh, trueProbability_bind]
  simp only [trueProbability_map, gridPriorities, PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Fintype.card_fin, Bool.decide_iff]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  field_simp

theorem grid_table_ties_bound {K : Type*} [Fintype K] [DecidableEq K]
    (N : ℕ) [NeZero N] :
    trueProbability ((productPMF (gridPriorities (τ := K) N)).map
      (fun ω => decide (¬Function.Injective ω))) ≤
        (Fintype.card K : ℝ) ^ 2 / N := by
  classical
  let p := productPMF (gridPriorities (τ := K) N)
  let events : K × K → (K → Fin N) → Bool :=
    fun ab ω => decide (ab.1 ≠ ab.2 ∧ ω ab.1 = ω ab.2)
  have hc : ∀ ω ∈ p.support, decide (¬Function.Injective ω) = true →
      ∃ ab, events ab ω = true := by
    intro ω _ hω
    simp only [Bool.decide_iff, Function.Injective, not_forall] at hω
    obtain ⟨a, b, h⟩ := hω
    push Not at h
    exact ⟨(a, b), by simpa [events] using And.intro h.2 h.1⟩
  have hle := boolean_union_bound p (fun ω => decide (¬Function.Injective ω)) events hc
  calc
    _ ≤ ∑ ab, trueProbability (p.map (events ab)) := hle
    _ ≤ ∑ _ab : K × K, (1 / (N : ℝ)) := by
      apply Finset.sum_le_sum
      intro ab _
      by_cases hab : ab.1 = ab.2
      · have he : events ab = Function.const (K → Fin N) false := by
          funext ω
          simp [events, hab]
        rw [he, PMF.map_const, trueProbability_pure]
        simp only [Bool.false_eq_true, ↓reduceIte]
        positivity
      · have he : events ab = fun ω => decide (ω ab.1 = ω ab.2) := by
          funext ω
          simp [events, hab]
        rw [he]
        exact le_of_eq (grid_table_pair_tie N ab.1 ab.2 hab)
    _ = _ := by simp [Fintype.card_prod, pow_two, Nat.cast_mul, div_eq_mul_inv]

end SharpTerminalLeave

open scoped BigOperators ENNReal Classical

end

end OAI
