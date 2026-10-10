import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.DivergentArms
import OAI.Combinatorics.TriangleRemoval.Queries.CallPath

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

lemma pmf_boolean_finite_cover {A J : Type*} (P : PMF A) (s : Finset J)
    (f : A → Bool) (g : J → A → Bool)
    (hcover : ∀ a ∈ P.support, f a = true → ∃ j ∈ s, g j a = true) :
    ((P.map f) true).toReal ≤ ∑ j ∈ s, ((P.map (g j)) true).toReal := by
  classical
  have hc (q : J → A → ℝ≥0∞) :
      (∑' a, ∑ j ∈ s, q j a) = ∑ j ∈ s, ∑' a, q j a := by
    clear hcover
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih => simp only [Finset.sum_insert hj,ENNReal.tsum_add,ih]
  have hp : (P.map f) true ≤ ∑ j ∈ s, (P.map (g j)) true := by
    simp only [PMF.map_apply]
    rw [← hc]
    apply ENNReal.tsum_le_tsum
    intro a
    by_cases h0 : P a = 0
    · simp only [h0,ite_self,Finset.sum_const_zero,le_refl]
    by_cases hf : f a = true
    · obtain ⟨j,hj,hg⟩ := hcover a ((PMF.mem_support_iff _ _).mpr h0) hf
      simp only [hf,↓reduceIte]
      have hterm : (if true = g j a then P a else 0) ≤
          ∑ j ∈ s, if true = g j a then P a else 0 :=
        Finset.single_le_sum (f := fun j => (if true = g j a then P a else 0))
          (fun _ _ => by positivity) hj
      convert hterm using 1 <;> simp [hg]
    · simp only [Ne.symm hf,↓reduceIte,zero_le]
  have hf : ∀ j ∈ s, (P.map (g j)) true ≠ ⊤ := fun j _ => PMF.apply_ne_top _ _
  have hh := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr hf) hp
  rwa [ENNReal.toReal_sum hf] at hh

def splitQueryPaths {A : Type*} [DecidableEq A] : List A → List A → List A × List A × List A
  | [], q => ([],[],q)
  | p, [] => ([],p,[])
  | a :: p, b :: q => if a = b then
      let s := splitQueryPaths p q
      (a :: s.1,s.2.1,s.2.2)
    else ([],a :: p,b :: q)

theorem splitQueryPaths_spec {A : Type*} [DecidableEq A] (p q : List A) :
    p = (splitQueryPaths p q).1 ++ (splitQueryPaths p q).2.1 ∧
    q = (splitQueryPaths p q).1 ++ (splitQueryPaths p q).2.2 ∧
    DivergentArms (splitQueryPaths p q).2.1 (splitQueryPaths p q).2.2 := by
  induction p generalizing q with
  | nil => simp [splitQueryPaths,DivergentArms]
  | cons a p ih =>
    cases q with
    | nil => simp [splitQueryPaths,DivergentArms]
    | cons b q =>
      by_cases hab : a = b
      · subst b
        obtain ⟨hp,hq,hd⟩ := ih q
        simpa only [splitQueryPaths,↓reduceIte,List.cons_append,List.cons.injEq,true_and] using
          And.intro hp (And.intro hq hd)
      · simp [splitQueryPaths,hab,DivergentArms]

noncomputable def pairFactorialWeight {A : Type*} [DecidableEq A] (x : ℝ) (p q : List A) : ℝ :=
  let s := splitQueryPaths p q
  x ^ (s.1.length+s.2.1.length+s.2.2.length) /
    ((s.1.length.factorial : ℝ)*(s.2.1.length.factorial : ℝ)*(s.2.2.length.factorial : ℝ))

lemma pairFactorialWeight_nonneg {A : Type*} [DecidableEq A] {x : ℝ}
    (hx : 0 ≤ x) (p q : List A) : 0 ≤ pairFactorialWeight x p q := by
  unfold pairFactorialWeight
  positivity

section PairWeight
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem actualPairVisitProbability_weight (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t) (hq : GridRowQuality H N b)
    (C : ℝ) (hC : 1 ≤ C) (hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (d k : ℕ) (hkd : k ≤ d) (hkN : k ≤ N) (focus : Finset ι) (parent : Option τ)
    (p q : List (ι × τ))
    (hp : p ∈ legalPaths H d focus parent) (hqp : q ∈ legalPaths H d focus parent) :
    actualPairVisitProbability H N d k focus parent p q ≤
      C^3 * pairFactorialWeight (prefixWeight (fun t => (2/(N : ℝ))*b t) k) p q := by
  obtain ⟨hpl,hplen⟩ := (mem_legalPaths H d focus parent p).mp hp
  obtain ⟨hql,hqlen⟩ := (mem_legalPaths H d focus parent q).mp hqp
  obtain ⟨he₁,he₂,hd⟩ := splitQueryPaths_spec p q
  unfold pairFactorialWeight
  have ht := actualPairVisitProbability_pattern_factorial H N b hb hq C hC hlower
    (splitQueryPaths p q).1 (splitQueryPaths p q).2.1 (splitQueryPaths p q).2.2 hd
    d k hkd hkN focus parent (he₁ ▸ hpl) (he₂ ▸ hql) (he₁ ▸ hplen) (he₂ ▸ hqlen)
  rwa [← he₁,← he₂] at ht

end PairWeight
end SharpTerminalLeave

end

end OAI
