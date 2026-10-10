import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.ReversedBasePublic
import OAI.Combinatorics.RamseyFive.Entropy.IndependentLaw

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

abbrev TwoPublicTape (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (H : ℕ) (q : ℝ) := BaseTable U P τ × ReversedBaseTape UT P τ H q
abbrev TwoPublicMessage (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (H : ℕ) (q : ℝ) (t : TwoPublicTape U UT P τ H q) :=
  BaseMessage U P τ ⊕ ReversedBaseMessage UT P τ H q t.2
noncomputable def twoPublicLaw (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) (H : ℕ) (q : ℝ) : Law (TwoPublicTape U UT P τ H q) :=
  adaptiveLaw (baseTableLaw U P τ R L₀) (fun _=>
    adaptiveLaw (baseTableLaw UT P τ R L₀) (fun _=>universalFreshLaw (ℙ K (Dual K V)) H q))
noncomputable def twoPublicDecoded (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (H : ℕ) (q : ℝ) (t : TwoPublicTape U UT P τ H q) :
    TwoPublicMessage U UT P τ H q t→Finset (ℙ K V)
  | Sum.inl m => t.1 m
  | Sum.inr m => reversedBaseDecoded U UT P τ H q t.2 m
noncomputable def twoPublicEncoded (S U : Finset (ℙ K V))
    (T UT : Finset (ℙ K (Dual K V))) (P τ : ℝ) (H : ℕ) (n : Fin (H+1)) (q MA MB : ℝ)
    (t : TwoPublicTape U UT P τ H q) : Option (TwoPublicMessage U UT P τ H q t) :=
  if S.card≤T.card then (baseFiniteEncoded S U P τ t.1).map Sum.inl else
    (reversedBaseEncoded S U T UT P τ H n q MA MB t.2).map Sum.inr

omit [Finite K] [FiniteDimensional K V] in
theorem twoPublic_output_law (S U : Finset (ℙ K V))
    (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty)
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) (H : ℕ) (n : Fin (H+1)) (q MA MB : ℝ) :
    map (twoPublicLaw U UT P τ R L₀ H q)
      (fun t=>(twoPublicEncoded S U T UT P τ H n q MA MB t).map (twoPublicDecoded U UT P τ H q t))=
      if S.card≤T.card then baseCaptureLaw S U P τ R L₀ else
        optionCompose (baseCaptureLaw T UT P τ R L₀) (nextCapLaw S U T UT hT n q MA MB) := by
  by_cases h : S.card≤T.card
  · simp only [twoPublicEncoded,ite_eq_left h,Option.map_map,twoPublicDecoded,Function.comp_def]
    rw [twoPublicLaw]
    exact (map_independent_left _ _ (fun t : BaseTable U P τ=>(baseFiniteEncoded S U P τ t).map t)).trans
      (baseFinite_law S U P τ R L₀)
  · simp only [twoPublicEncoded,ite_eq_right h,Option.map_map,twoPublicDecoded,Function.comp_def]
    rw [twoPublicLaw]
    exact (map_independent_right _ _ (fun t : ReversedBaseTape UT P τ H q=>
      (reversedBaseEncoded S U T UT P τ H n q MA MB t).map (reversedBaseDecoded U UT P τ H q t))).trans
        (reversedBase_law S U T UT hT P τ R L₀ H n q MA MB)

omit [Finite K] [FiniteDimensional K V] in
theorem twoPublic_oriented (S U : Finset (ℙ K V))
    (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty)
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) (H : ℕ)
    (hn : reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card))≤H) :
    map (twoPublicLaw U UT P τ R L₀ H (Nat.card K))
      (fun t=>(twoPublicEncoded S U T UT P τ H ⟨_,Nat.lt_succ_of_le hn⟩ (Nat.card K)
        ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^3/T.card) ((T.card:ℝ)*Real.exp (2*P)) t).map
          (twoPublicDecoded U UT P τ H (Nat.card K) t))=twoOrientedLaw S U T UT hT P τ R L₀ := by
  rw [twoPublic_output_law S U T UT hT]
  rfl
end SharpRamseyFive.ScoreGeometry

end OAI
