import Mathlib
import OAI.Combinatorics.RamseyFive.Trees.AmbientEviction
import OAI.Combinatorics.RamseyFive.Geometry.GuardedNode
import OAI.Combinatorics.RamseyFive.Trees.TreeExposure

namespace OAI

namespace SharpRamseyFive.TreeCodec
open FiniteEntropy BinaryTree
open scoped Classical
universe u v w z s
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A→C→Type w) [∀ a c,Fintype (Ω a c)]
  (M : ∀ a c,Ω a c→Type z) (left right : ∀ a c t,M a c t→C)
  {D : Type s}

def decodedAt (out : ∀ a c t,M a c t→D) :
    (b : BinaryTree A)→(ω : Tape Ω b)→(c : C)→
    Message Ω M left right b ω c→Address b→Option D
  | .nil,_,_,_,j => nomatch j
  | .node _ _ _,_,_,none,_ => none
  | .node a _ _,ω,c,some ⟨m,_,_⟩,.inl _ => some (out a c (ω.1 c) m)
  | .node a l _,ω,c,some ⟨m,ml,_⟩,.inr (.inl j) =>
      decodedAt out l ω.2.1 (left a c (ω.1 c) m) ml j
  | .node a _ r,ω,c,some ⟨m,_,mr⟩,.inr (.inr j) =>
      decodedAt out r ω.2.2 (right a c (ω.1 c) m) mr j

omit [Fintype C] [∀ a c, Fintype (Ω a c)] in
theorem decodedAt_encoded (enc : ∀ a c t,Option (M a c t))
    (out : ∀ a c t,M a c t→D) (b : BinaryTree A) (ω : Tape Ω b) (c : C)
    (j : Address b) :
    decodedAt Ω M left right out b ω c (encoded Ω M left right enc b ω c) j =
      observe Ω M left right enc out b ω c j := by
  induction b generalizing c with
  | nil => exact nomatch j
  | node a l r ihl ihr =>
    rcases j with j | (j | j)
    · cases he:enc a c (ω.1 c) <;> simp [decodedAt,encoded,observe,probe,he]
    · cases he:enc a c (ω.1 c) <;> simp [decodedAt,encoded,observe,probe,he,ihl]
    · cases he:enc a c (ω.1 c) <;> simp [decodedAt,encoded,observe,probe,he,ihr]

omit [Fintype C] [∀ a c, Fintype (Ω a c)] in
theorem observe_invariant (enc : ∀ a c t,Option (M a c t))
    (out : ∀ a c t,M a c t→D) (Valid : C→Prop) (P : A→D→Prop)
    (hl : ∀ a c t m,Valid c→enc a c t=some m→Valid (left a c t m))
    (hr : ∀ a c t m,Valid c→enc a c t=some m→Valid (right a c t m))
    (ho : ∀ a c t m,Valid c→enc a c t=some m→P a (out a c t m))
    (b : BinaryTree A) (ω : Tape Ω b) (c : C) (hc : Valid c)
    (j : Address b) (d : D) (h : observe Ω M left right enc out b ω c j=some d) :
    P (label b j) d := by
  induction b generalizing c with
  | nil => exact nomatch j
  | node a l r ihl ihr =>
    cases he:enc a c (ω.1 c) with
    | none =>
      rcases j with j | (j | j) <;> simp [observe,probe,he] at h
    | some m =>
      rcases j with j | (j | j)
      · simp only [observe,probe,he,Option.map_some,Option.some.injEq] at h
        subst d
        exact ho a c (ω.1 c) m hc he
      · exact ihl _ (left a c (ω.1 c) m) (hl a c (ω.1 c) m hc he) j
          (by simpa [observe,probe,he] using h)
      · exact ihr _ (right a c (ω.1 c) m) (hr a c (ω.1 c) m hc he) j
          (by simpa [observe,probe,he] using h)
end SharpRamseyFive.TreeCodec

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B Ω : Type*} [Fintype A] [Fintype B] [Fintype Ω]

lemma cap_eviction_from_domination (p : Law Ω) (R : A → B → Prop)
    (X : Finset A) (Y : Finset B) (cap : Ω → Option (Finset B)) (C : ℝ)
    (hlocal : ∀ b, eventMass p (Finset.univ.filter (fun ω => Excludes b (cap ω))) ≤
      C * ((((Finset.univ.filter (fun a => R a b)) ∩ X).card : ℝ) / X.card)) :
    (∑ ω, p ω * evictionFraction Y (ambientTest (cap ω))) ≤
      C * relationMass R (uniformWeight X) (uniformWeight Y) := by
  rw [expected_ambient_eviction, relationMass_by_target, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  rw [sum_uniformWeight]
  have hg : 0 ≤ uniformWeight Y b := by unfold uniformWeight; positivity
  have h := mul_le_mul_of_nonneg_left (hlocal b) hg
  nlinarith only [h]

end SharpRamseyFive.ReverseCap

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

theorem oriented_point_cap_eviction
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ P : ℝ)
    (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ≤c*δ^2)
    (X : Finset (ℙ K V)) :
    (∑ t, orientedNodeTapeLaw f r (1000*(Nat.card K)^2) (Nat.card K) t *
      evictionFraction X (ambientTest ((orientedGuardedNodeEncoded f r σ hσ hq hd.le
        A₀ UA B₀ UB hA₀ hB₀ c δ τ P hδ t).map
        (fun m => (orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).2)))) ≤
      (50*(Nat.card K:ℝ)/(9*(c*δ))) *
        relationMass (fun b a => Incident a b) (uniformWeight B₀) (uniformWeight X) := by
  let enc := orientedGuardedNodeEncoded f r σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀ c δ τ P hδ
  let dec := orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K)
  let p := orientedNodeTapeLaw f r (1000*(Nat.card K)^2) (Nat.card K)
  have h := (orientedGuardedNode_original f r σ hσ hq hd hq3 A₀ UA B₀ UB
    hA₀ hB₀ c δ τ P hc hc9 hδ hτ).2
  have hh := cap_eviction_from_domination (map p (fun t => (enc t).map (dec t)))
    (fun b a => Incident a b) B₀ X (fun out => out.map Prod.snd)
    (50*(Nat.card K:ℝ)/(9*(c*δ))) (by
      intro a
      have he : (Finset.univ.filter (Incident a)) ∩ B₀ = B₀.filter (Incident a) := by
        ext b; simp [and_comm]
      simpa only [he] using h a)
  rw [sum_map] at hh
  simpa only [Option.map_map, Function.comp_def, enc, dec, p] using hh

theorem oriented_dual_cap_eviction
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ P : ℝ)
    (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ≤c*δ^2)
    (X : Finset (ℙ K (Dual K V))) :
    (∑ t, orientedNodeTapeLaw f r (1000*(Nat.card K)^2) (Nat.card K) t *
      evictionFraction X (ambientTest ((orientedGuardedNodeEncoded f r σ hσ hq hd.le
        A₀ UA B₀ UB hA₀ hB₀ c δ τ P hδ t).map
        (fun m => (orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).1)))) ≤
      (50*(Nat.card K:ℝ)/(9*(c*δ))) *
        relationMass Incident (uniformWeight A₀) (uniformWeight X) := by
  let enc := orientedGuardedNodeEncoded f r σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀ c δ τ P hδ
  let dec := orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K)
  let p := orientedNodeTapeLaw f r (1000*(Nat.card K)^2) (Nat.card K)
  have h := (orientedGuardedNode_original f r σ hσ hq hd hq3 A₀ UA B₀ UB
    hA₀ hB₀ c δ τ P hc hc9 hδ hτ).1
  have hh := cap_eviction_from_domination (map p (fun t => (enc t).map (dec t)))
    Incident A₀ X (fun out => out.map Prod.fst)
    (50*(Nat.card K:ℝ)/(9*(c*δ))) (by
      intro b
      have he : (Finset.univ.filter (fun a => Incident a b)) ∩ A₀ = A₀.filter (fun a => Incident a b) := by
        ext a; simp [and_comm]
      simpa only [he] using h b)
  rw [sum_map] at hh
  simpa only [Option.map_map, Function.comp_def, enc, dec, p] using hh

end SharpRamseyFive.ProjectiveIncidence

end OAI
