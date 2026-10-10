import OAI.Computability.PerfectCompleteness.Construction.FactoredFunctionsLemmas
import OAI.Computability.PerfectCompleteness.Sampling.CutSamplerRefinement

namespace OAI

section

namespace PerfectCompleteness.CutSamplerLocality

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces RecursiveSampler PointwiseSpaces
open CutSamplerRefinement

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}

def View : {n m : Nat} → (p : Path branch n (m + 1)) →
    (A : Slots branch n → Type u) → (clean : Fin (branch m) → Prop) → Type u
  | _, m, .refl _, A, clean =>
      (i : {i : Fin (branch m) // ¬ clean i}) → Assignment (childFamily A i.val)
  | _, _, .step i p, A, clean =>
      ((j : OffPath i) → Assignment (childFamily A j.val)) ×
        View p (childFamily A i) clean

def view : {n m : Nat} → (p : Path branch n (m + 1)) →
    (A : Slots branch n → Type u) → (clean : Fin (branch m) → Prop) →
    Assignment A → View p A clean
  | _, _, .refl _, A, _, x => fun i => childRestriction A i.val x
  | _, _, .step i p, A, clean, x =>
      (fun j => childRestriction A j.val x,
        view p (childFamily A i) clean (childRestriction A i x))

def subTape (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (i : Fin (branch n)) (p : Path branch n m)
    (A : Slots branch (n + 1) → Type u)
    (tape : CutSamplerRefinement.Tape 𝕜 repeats (.step i p) A)
    (h : Fin (repeats (n + 1))) (b : Bool) :
    CutSamplerRefinement.Tape 𝕜 repeats p (childFamily A i) :=
  fun j => tape (Sum.inr ((h, b), j))

def ZeroAtClean (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) → (A : Slots branch n → Type u) →
    (clean : Fin (branch m) → Prop) → CutSamplerRefinement.Tape 𝕜 repeats p A → Prop
  | _, _, .refl _, _, clean, tape => ∀ i, clean i → tape () i = 0
  | _ + 1, _, .step i p, A, clean, tape =>
      ∀ h b, ZeroAtClean 𝕜 repeats p (childFamily A i) clean
        (subTape 𝕜 repeats i p A tape h b)

theorem evaluate_refl (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (A : Slots branch (m + 1) → Type u)
    (tape : CutSamplerRefinement.Tape 𝕜 repeats (.refl (m + 1)) A) :
    CutSamplerRefinement.evaluate 𝕜 repeats (.refl (m + 1)) A tape =
      UniformChildSum.recursiveSum A (tape ()) := rfl

theorem evaluate_step (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (i : Fin (branch n)) (p : Path branch n m)
    (A : Slots branch (n + 1) → Type u)
    (tape : CutSamplerRefinement.Tape 𝕜 repeats (.step i p) A) :
    CutSamplerRefinement.evaluate 𝕜 repeats (.step i p) A tape =
      RecursiveSampler.combine 𝕜 A i (repeats (n + 1))
        (fun j => tape (Sum.inl j))
        (fun h => CutSamplerRefinement.evaluate 𝕜 repeats p (childFamily A i)
          (subTape 𝕜 repeats i p A tape h false))
        (fun h => CutSamplerRefinement.evaluate 𝕜 repeats p (childFamily A i)
          (subTape 𝕜 repeats i p A tape h true)) := rfl

theorem evaluate_eq_of_view_eq (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (A : Slots branch n → Type u) (clean : Fin (branch m) → Prop)
      (tape : CutSamplerRefinement.Tape 𝕜 repeats p A),
      ZeroAtClean 𝕜 repeats p A clean tape →
      ∀ x y : Assignment A, view p A clean x = view p A clean y →
        (CutSamplerRefinement.evaluate 𝕜 repeats p A tape).val x =
          (CutSamplerRefinement.evaluate 𝕜 repeats p A tape).val y := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro A clean tape hzero x y hview
          have heval (z : Assignment A) :
              (UniformChildSum.recursiveSum (𝕜 := 𝕜) A (tape ())).val z =
                ∑ i : Fin (branch n), (tape () i).val (childRestriction A i z) := by
            have hsum := congrFun
              (UniformChildSum.childSum_apply (𝕜 := 𝕜) (childRestriction A)
                (fun i => space 𝕜 branch n (childFamily A i)) (tape ())) z
            simp only [Finset.sum_apply, PointwiseSpaces.pullback_apply] at hsum
            refine hsum.trans ?_
            refine Finset.sum_congr (ι := Fin (branch n)) ?_ ?_
            · ext i
              simp only [Finset.mem_univ]
            · intro i _
              rfl
          rw [evaluate_refl, heval x, heval y]
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : clean i
          · rw [hzero i hi]
            rfl
          · exact congrArg (tape () i).val (congrFun hview ⟨i, hi⟩)
      | step i p =>
          intro A clean tape hzero x y hview
          have hout : ∀ j : OffPath i, childRestriction A j.val x = childRestriction A j.val y :=
            congrFun (congrArg Prod.fst hview)
          have hin : view p (childFamily A i) clean (childRestriction A i x) =
              view p (childFamily A i) clean (childRestriction A i y) :=
            congrArg Prod.snd hview
          rw [evaluate_step]
          simp only [RecursiveSampler.combine, RecursiveSampler.combineFunction,
            Finset.sum_apply, Pi.add_apply, Pi.mul_apply, PointwiseSpaces.pullback_apply]
          change
            (∑ j : OffPath i, (tape (Sum.inl j)).val (childRestriction A j.val x)) +
              (∑ h, (CutSamplerRefinement.evaluate 𝕜 repeats p (childFamily A i)
                (subTape 𝕜 repeats i p A tape h false)).val (childRestriction A i x) *
                (CutSamplerRefinement.evaluate 𝕜 repeats p (childFamily A i)
                  (subTape 𝕜 repeats i p A tape h true)).val (childRestriction A i x)) =
            (∑ j : OffPath i, (tape (Sum.inl j)).val (childRestriction A j.val y)) +
              (∑ h, (CutSamplerRefinement.evaluate 𝕜 repeats p (childFamily A i)
                (subTape 𝕜 repeats i p A tape h false)).val (childRestriction A i y) *
                (CutSamplerRefinement.evaluate 𝕜 repeats p (childFamily A i)
                  (subTape 𝕜 repeats i p A tape h true)).val (childRestriction A i y))
          congr 1
          · exact Finset.sum_congr rfl (fun j _ => congrArg (tape (Sum.inl j)).val (hout j))
          · apply Finset.sum_congr rfl
            intro h _
            rw [ih p (childFamily A i) clean (subTape 𝕜 repeats i p A tape h false)
                (hzero h false) _ _ hin,
              ih p (childFamily A i) clean (subTape 𝕜 repeats i p A tape h true)
                (hzero h true) _ _ hin]

theorem evaluate_factors (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (A : Slots branch n → Type u) (clean : Fin (branch m) → Prop)
    (tape : CutSamplerRefinement.Tape 𝕜 repeats p A)
    (hzero : ZeroAtClean 𝕜 repeats p A clean tape) :
    (CutSamplerRefinement.evaluate 𝕜 repeats p A tape).val ∈
      FactoredFunctions.factoringSpace (view p A clean) :=
  evaluate_eq_of_view_eq 𝕜 repeats p A clean tape hzero

end
end PerfectCompleteness.CutSamplerLocality

end

end OAI
