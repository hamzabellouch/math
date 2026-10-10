import OAI.Computability.PerfectCompleteness.Construction.LocalReconstruction
import OAI.Computability.PerfectCompleteness.Foundations.RecursiveSpaceEquivLemmas
import OAI.Computability.PerfectCompleteness.Sampling.CutSamplerKeyLocalityLemmas
import OAI.Computability.PerfectCompleteness.Sampling.RecordSeedSamplingLemmas
import OAI.Computability.UniqueGames.Foundations.Conditioning
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas

namespace OAI


namespace PerfectCompleteness.CutSamplerReplayTransport

open PointwiseSpaces RecursiveSpaces DescendantSpaces RecursiveSampler
open CutSamplerKeyLocality
open scoped BigOperators Classical

noncomputable section

universe u v w

variable {branch : Nat → Nat} {n m : Nat}
  (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)

theorem squareEquiv_symm_apply
    {A : Slots branch n → Type u} {B : Slots branch n → Type v}
    (e : ∀ s, A s ≃ B s) (f : squareSpace (space 𝕜 branch n A))
    (y : Assignment B) :
    ((RecursiveSpaceEquiv.squareEquiv (𝕜 := 𝕜) e).symm f).val y =
      f.val (project (fun s => (e s).symm) y) := rfl

theorem squareEquiv_symm_eval_of_agree
    {A : Slots branch n → Type u} {B : Slots branch n → Type v}
    (e : ∀ s, A s ≃ B s) (f : squareSpace (space 𝕜 branch n A))
    (x : Assignment A) (y : Assignment B)
    (hagree : ∀ s, e s (x s) = y s) :
    ((RecursiveSpaceEquiv.squareEquiv (𝕜 := 𝕜) e).symm f).val y = f.val x := by
  rw [squareEquiv_symm_apply]
  apply congrArg f.val
  funext s
  exact (congrArg (e s).symm (hagree s)).symm.trans ((e s).symm_apply_apply (x s))

def transport (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
    (A : Slots branch n → Type u) → (B : Slots branch n → Type v) →
    (clean : Fin (branch m) → Prop) →
    (∀ s, keptLeaf p clean s → A s ≃ B s) →
    CutSamplerReplay.Tape 𝕜 repeats p A clean →
      CutSamplerReplay.Tape 𝕜 repeats p B clean
  | _, _, .refl _, _, _, _, e, tape =>
      fun i => (RecursiveSpaceEquiv.squareEquiv (𝕜 := 𝕜)
        (fun s => e (i.val, s) i.property)).symm (tape i)
  | _, _, .step i p, A, B, clean, e, tape =>
      (fun j => (RecursiveSpaceEquiv.squareEquiv (𝕜 := 𝕜)
        (fun s => e (j.val, s) (Or.inl j.property))).symm (tape.1 j),
        fun call => transport 𝕜 repeats p (childFamily A i) (childFamily B i) clean
          (fun s hs => e (i, s) (Or.inr hs)) (tape.2 call))

theorem evaluate_transport (p : Path branch n (m + 1)) :
    ∀ (A : Slots branch n → Type u) (B : Slots branch n → Type v)
      (clean : Fin (branch m) → Prop)
      (e : ∀ s, keptLeaf p clean s → A s ≃ B s)
      (tape : CutSamplerReplay.Tape 𝕜 repeats p A clean)
      (x : Assignment A) (y : Assignment B),
      (∀ s hs, e s hs (x s) = y s) →
      CutSamplerReplay.evaluate 𝕜 repeats p B clean
          (transport 𝕜 repeats p A B clean e tape) y =
        CutSamplerReplay.evaluate 𝕜 repeats p A clean tape x := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro A B clean e tape x y hagree
          simp only [CutSamplerReplay.evaluate_refl]
          apply Finset.sum_congr rfl
          intro i _
          exact squareEquiv_symm_eval_of_agree 𝕜
            (fun s => e (i.val, s) i.property) (tape i)
            (childRestriction A i.val x) (childRestriction B i.val y)
            (fun s => hagree (i.val, s) i.property)
      | step i p =>
          intro A B clean e tape x y hagree
          simp only [CutSamplerReplay.evaluate_step]
          apply congrArg₂ (fun a b : 𝕜 => a + b)
          · apply Finset.sum_congr rfl
            intro j _
            exact squareEquiv_symm_eval_of_agree 𝕜
              (fun s => e (j.val, s) (Or.inl j.property)) (tape.1 j)
              (childRestriction A j.val x) (childRestriction B j.val y)
              (fun s => hagree (j.val, s) (Or.inl j.property))
          · apply Finset.sum_congr rfl
            intro h _
            apply congrArg₂ (fun a b : 𝕜 => a * b)
            · exact ih p (childFamily A i) (childFamily B i) clean
                (fun s hs => e (i, s) (Or.inr hs)) (tape.2 (h, false))
                (childRestriction A i x) (childRestriction B i y)
                (fun s hs => hagree (i, s) (Or.inr hs))
            · exact ih p (childFamily A i) (childFamily B i) clean
                (fun s hs => e (i, s) (Or.inr hs)) (tape.2 (h, true))
                (childRestriction A i x) (childRestriction B i y)
                (fun s hs => hagree (i, s) (Or.inr hs))

end
end PerfectCompleteness.CutSamplerReplayTransport


section

namespace PerfectCompleteness.LocalReconstruction.Recipe

open scoped BigOperators

variable {𝕜 Atom Atom' X J : Type*} [Field 𝕜]

def map (f : Atom → Atom') : Recipe 𝕜 Atom → Recipe 𝕜 Atom'
  | .constant c => .constant c
  | .atom a => .atom (f a)
  | .add r s => .add (map f r) (map f s)
  | .mul r s => .mul (map f r) (map f s)

theorem evaluate_map (f : Atom → Atom') (atoms : Atom' → X → 𝕜)
    (r : Recipe 𝕜 Atom) :
    (r.map f).evaluate atoms = r.evaluate (fun a => atoms (f a)) := by
  induction r with
  | constant c => rfl
  | atom a => rfl
  | add r s hr hs => simp only [map, evaluate, hr, hs]
  | mul r s hr hs => simp only [map, evaluate, hr, hs]

def sumList (f : J → Recipe 𝕜 Atom) : List J → Recipe 𝕜 Atom
  | [] => .constant 0
  | j :: js => .add (f j) (sumList f js)

theorem evaluate_sumList (f : J → Recipe 𝕜 Atom) (js : List J)
    (atoms : Atom → X → 𝕜) :
    (sumList f js).evaluate atoms = (js.map fun j => (f j).evaluate atoms).sum := by
  induction js with
  | nil => rfl
  | cons j js ih => simp only [sumList, evaluate, List.map_cons, List.sum_cons, ih]

noncomputable def sumIndexed [Fintype J] (f : J → Recipe 𝕜 Atom) : Recipe 𝕜 Atom :=
  sumList f Finset.univ.toList

theorem evaluate_sumIndexed [Fintype J] (f : J → Recipe 𝕜 Atom)
    (atoms : Atom → X → 𝕜) :
    (sumIndexed f).evaluate atoms = ∑ j, (f j).evaluate atoms := by
  rw [sumIndexed, evaluate_sumList, Finset.sum_map_toList]

end PerfectCompleteness.LocalReconstruction.Recipe

namespace PerfectCompleteness.StoppedSamplerRecipe

open scoped BigOperators
open PointwiseSpaces RecursiveSpaces DescendantSpaces RecursiveSampler
open LocalReconstruction

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}

def ordinaryTag (repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (j : OffPath i) : DrawIndex repeats (.step i p) := Sum.inl j

def factorTag (repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (h : Fin (repeats (n + 1))) (b : Bool) (j : DrawIndex repeats p) :
    DrawIndex repeats (.step i p) := Sum.inr ((h, b), j)

def recipe (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) → Recipe 𝕜 (DrawIndex repeats p)
  | _, _, .refl _ => .atom ()
  | n + 1, _, .step i p =>
      .add
        (Recipe.sumIndexed (fun j : OffPath i => .atom (ordinaryTag repeats i p j)))
        (Recipe.sumIndexed (fun h : Fin (repeats (n + 1)) =>
          .mul
            ((recipe 𝕜 repeats p).map (factorTag repeats i p h false))
            ((recipe 𝕜 repeats p).map (factorTag repeats i p h true))))

def atoms (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) → (A : Slots branch n → Type u) →
      Tape 𝕜 repeats p A → DrawIndex repeats p → Assignment A → 𝕜
  | _, _, .refl _, _, t, j => (t j).val
  | _, _, .step i p, A, t, j =>
      match j with
      | Sum.inl j => pullback 𝕜 (childRestriction A j.val) (t (Sum.inl j)).val
      | Sum.inr j =>
          pullback 𝕜 (childRestriction A i)
            (atoms 𝕜 repeats p (childFamily A i)
              (subTape 𝕜 repeats i p A t j.1.1 j.1.2) j.2)

variable (𝕜 : Type w) [Field 𝕜]

theorem evaluate_recipe (repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (A : Slots branch n → Type u) (t : Tape 𝕜 repeats p A),
      (recipe 𝕜 repeats p).evaluate (atoms 𝕜 repeats p A t) =
        (RecursiveSampler.evaluate 𝕜 repeats p A t).val := by
  induction p with
  | refl n =>
      intro A t
      rfl
  | @step n m i p ih =>
      intro A t
      have child (h : Fin (repeats (n + 1))) (b : Bool) :
          ((recipe 𝕜 repeats p).map (factorTag repeats i p h b)).evaluate
              (atoms 𝕜 repeats (.step i p) A t) =
            (RecursiveSampler.evaluate 𝕜 repeats p (childFamily A i)
              (subTape 𝕜 repeats i p A t h b)).val ∘ childRestriction A i := by
        rw [Recipe.evaluate_map]
        change (recipe 𝕜 repeats p).evaluate (fun j =>
          atoms 𝕜 repeats p (childFamily A i) (subTape 𝕜 repeats i p A t h b) j ∘
            childRestriction A i) = _
        rw [Recipe.evaluate_pullback, ih]
      simp only [recipe, Recipe.evaluate, Recipe.evaluate_sumIndexed, child]
      funext x
      simp only [RecursiveSampler.evaluate, combine, combineFunction,
        Finset.sum_apply, Pi.add_apply, Pi.mul_apply, Function.comp_apply,
        atoms, ordinaryTag, PointwiseSpaces.pullback_apply]

theorem evaluate_factors {Z : Type*} (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) (t : Tape 𝕜 repeats p A) (other : Assignment A → Z)
    (known : ∀ j, atoms 𝕜 repeats p A t j ∈ FactoredFunctions.factoringSpace other) :
    (RecursiveSampler.evaluate 𝕜 repeats p A t).val ∈
      FactoredFunctions.factoringSpace other := by
  rw [← evaluate_recipe 𝕜 repeats p A t]
  exact Recipe.evaluate_factors other (atoms 𝕜 repeats p A t) known (recipe 𝕜 repeats p)

end
end PerfectCompleteness.StoppedSamplerRecipe

end


namespace PerfectCompleteness.UniformConditioning

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] [Nonempty Ω] [Nonempty Γ]

theorem uniform_transport (e : Ω ≃ Γ) :
    (FiniteDistribution.uniform Ω).transport e = FiniteDistribution.uniform Γ := by
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  change 1 / (Fintype.card Ω : ℝ) = 1 / (Fintype.card Γ : ℝ)
  rw [Fintype.card_congr e]

theorem uniform_probability_equiv (e : Ω ≃ Γ) (event : Γ → Bool) :
    (FiniteDistribution.uniform Ω).probability (fun x => event (e x)) =
      (FiniteDistribution.uniform Γ).probability event := by
  rw [← uniform_transport e, FiniteDistribution.probability_transport]

theorem uniform_probability (T : Ω → Prop) :
    (FiniteDistribution.uniform Ω).probability (fun x => decide (T x)) =
      (Fintype.card {x : Ω // T x} : ℝ) / (Fintype.card Ω : ℝ) := by
  calc
    _ = (∑ x : Ω, if T x then (1 : ℝ) else 0) / (Fintype.card Ω : ℝ) := by
      change (∑ x : Ω, if decide (T x) then 1 / (Fintype.card Ω : ℝ) else 0) = _
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : T x <;> simp [hx]
    _ = _ := by simp only [Fintype.card_subtype, Finset.sum_boole]

theorem uniform_probability_pos (T : Ω → Prop) [Nonempty {x : Ω // T x}] :
    0 < (FiniteDistribution.uniform Ω).probability (fun x => decide (T x)) := by
  rw [uniform_probability]
  exact div_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr Fintype.card_pos)

omit [Nonempty Ω] in
theorem uniform_subtype_pushforward_weight (T : Ω → Prop)
    [Nonempty {x : Ω // T x}] (x : Ω) :
    ((FiniteDistribution.uniform {x : Ω // T x}).pushforward Subtype.val).weight x =
      if T x then 1 / (Fintype.card {x : Ω // T x} : ℝ) else 0 := by
  change (∑ y : {x : Ω // T x},
    if y.val = x then 1 / (Fintype.card {x : Ω // T x} : ℝ) else 0) = _
  by_cases hx : T x
  · rw [ite_eq_left hx]
    rw [Finset.sum_eq_single (⟨x, hx⟩ : {x : Ω // T x})]
    · simp
    · intro y _ hy
      have hne : y.val ≠ x := fun heq => hy (Subtype.ext heq)
      simp [hne]
    · simp
  · rw [ite_eq_right hx]
    apply Finset.sum_eq_zero
    intro y _
    have hne : y.val ≠ x := fun heq => hx (heq ▸ y.property)
    simp [hne]

theorem condition_uniform (T : Ω → Prop) [Nonempty {x : Ω // T x}]
    (positive : 0 < (FiniteDistribution.uniform Ω).probability (fun x => decide (T x))) :
    (FiniteDistribution.uniform Ω).condition (fun x => decide (T x)) positive =
      (FiniteDistribution.uniform {x : Ω // T x}).pushforward Subtype.val := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  rw [uniform_subtype_pushforward_weight]
  change (if decide (T x) then
    (1 / (Fintype.card Ω : ℝ)) /
      (FiniteDistribution.uniform Ω).probability (fun x => decide (T x)) else 0) = _
  rw [uniform_probability]
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  by_cases hx : T x
  · simpa [hx] using
      div_div_div_cancel_right₀ hcard (1 : ℝ) (Fintype.card {x : Ω // T x} : ℝ)
  · simp [hx]

theorem probability_condition_uniform (T : Ω → Prop) [Nonempty {x : Ω // T x}]
    (positive : 0 < (FiniteDistribution.uniform Ω).probability (fun x => decide (T x)))
    (event : Ω → Bool) :
    ((FiniteDistribution.uniform Ω).condition (fun x => decide (T x)) positive).probability
        event =
      (FiniteDistribution.uniform {x : Ω // T x}).probability (fun x => event x.val) := by
  rw [condition_uniform, FiniteDistribution.probability_pushforward]

end
end PerfectCompleteness.UniformConditioning

end OAI
