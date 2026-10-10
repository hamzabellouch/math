import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.TwoPublicCaps
import OAI.Combinatorics.RamseyFive.Decoding.UniversalFresh
import OAI.Combinatorics.RamseyFive.Entropy.PublicComposition

namespace OAI


namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

abbrev UniversalFreshMessage (W : Finset B) (H : ℕ) (q : ℝ) :=
  (n : Fin (H+1)) × FreshMessage W n q

noncomputable def universalFreshDecoded (R : A→B→Prop) (W : Finset B)
    (H : ℕ) (q : ℝ) (t : UniversalFresh B H q) (m : UniversalFreshMessage W H q) : Finset A :=
  if hW : W.Nonempty then
    freshDecoded R W m.1 q (t (⟨W,hW⟩,m.1)) m.2
  else ∅

noncomputable def universalFreshEncoded (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (H : ℕ) (n : Fin (H+1)) (q M : ℝ)
    (t : UniversalFresh B H q) : Option (UniversalFreshMessage W H q) :=
  if hW : W.Nonempty then
    (freshEncoded R S U C W hCW n q M (t (⟨W,hW⟩,n))).map (fun m=>⟨n,m⟩)
  else none

lemma universalFreshEncoded_exact (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (hW : W.Nonempty) (H : ℕ) (n : Fin (H+1)) (q M : ℝ)
    (t : UniversalFresh B H q) :
    (universalFreshEncoded R S U C W hCW H n q M t).map (universalFreshDecoded R W H q t)=
      (freshEncoded R S U C W hCW n q M (t (⟨W,hW⟩,n))).map
        (freshDecoded R W n q (t (⟨W,hW⟩,n))) := by
  simp only [universalFreshEncoded,dite_eq_left hW,Option.map_map]
  congr 1
  funext m
  exact dite_eq_left hW

lemma universalFreshEncoded_law (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (hW : W.Nonempty) (H : ℕ) (n : Fin (H+1)) (q M : ℝ) :
    map (universalFreshLaw B H q) (fun t=>
      (universalFreshEncoded R S U C W hCW H n q M t).map (universalFreshDecoded R W H q t))=
      ambientCapLaw R S U C W hW n q M := by
  simp only [universalFreshEncoded_exact R S U C W hCW hW]
  exact universalFresh_output R S U C W hW hCW H n (Nat.le_of_lt_succ n.isLt) q M
end SharpRamseyFive.ReverseCap

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def publicReverseResult (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (_ : B.Nonempty)
    (H : ℕ) (n : Fin (H+1)) (q MA MB : ℝ)
    (Y : Option (Finset (ℙ K (Dual K V)))) (t : UniversalFresh (ℙ K (Dual K V)) H q) :
    Option (Finset (ℙ K V)) :=
  match Y with
  | none => none
  | some W => if _hW : ValidCap B UB MB W then
      (universalFreshEncoded Incident A UA (B∩W) W Finset.inter_subset_right H n q MA t).map
        (fun m=>UA∩universalFreshDecoded Incident W H q t m)
    else none

omit [Finite K] [FiniteDimensional K V] in
theorem publicReverseResult_law (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty)
    (H : ℕ) (n : Fin (H+1)) (q MA MB : ℝ)
    (Y : Option (Finset (ℙ K (Dual K V)))) :
    map (universalFreshLaw (ℙ K (Dual K V)) H q) (publicReverseResult A UA B UB hB H n q MA MB Y)=
      nextCapLaw A UA B UB hB n q MA MB Y := by
  cases Y with
  | none => exact map_const _ none
  | some W =>
    change map (universalFreshLaw (ℙ K (Dual K V)) H q)
      (fun t=>if _hW : ValidCap B UB MB W then
        (universalFreshEncoded Incident A UA (B∩W) W Finset.inter_subset_right H n q MA t).map
          (fun m=>UA∩universalFreshDecoded Incident W H q t m) else none) = _
    dsimp only [nextCapLaw]
    split_ifs with hv
    · have hW := (hv.source_nonempty hB).mono Finset.inter_subset_right
      have hh := congrArg (fun p=>map p (Option.map fun Z=>UA∩Z))
        (universalFreshEncoded_law Incident A UA (B∩W) W Finset.inter_subset_right hW H n q MA)
      rw [ambientCapLaw_restrict,map_comp] at hh
      simpa only [Function.comp_def,Option.map_map] using hh
    · exact map_const _ none
end SharpRamseyFive.ProjectiveIncidence

end OAI
