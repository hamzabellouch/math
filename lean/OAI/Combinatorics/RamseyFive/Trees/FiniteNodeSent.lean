import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.FourFinitePredictor

namespace OAI

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]
lemma freshEncoded_valid (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (n : ℕ) (q M : ℝ) (t : FreshTape W n q)
    (m : FreshMessage W n q) (hm : freshEncoded R S U C W hCW n q M t=some m) :
    ValidCap S U M (U∩freshDecoded R W n q t m) := by
  have hh := freshEncoded_decoded R S U C W hCW n q M t
  rw [hm,Option.map_some] at hh
  obtain ⟨row,hr,he⟩ := Option.map_eq_some_iff.mp hh.symm
  have hi := (firstAccepted_index _ _ hr).choose_spec.2
  rw [←he,cap_inter]
  exact ⟨cap_subset _ _ _ _,(Finset.mem_filter.mp hi).2.2⟩

lemma universalFreshEncoded_valid (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (H : ℕ) (n : Fin (H+1)) (q M : ℝ)
    (t : UniversalFresh B H q) (m : UniversalFreshMessage W H q)
    (hm : universalFreshEncoded R S U C W hCW H n q M t=some m) :
    ValidCap S U M (U∩universalFreshDecoded R W H q t m) := by
  unfold universalFreshEncoded at hm
  split_ifs at hm with hW
  obtain ⟨f,hf,he⟩ := Option.map_eq_some_iff.mp hm
  subst m
  simp only [universalFreshDecoded,dite_eq_left hW]
  exact freshEncoded_valid R S U C W hCW n q M _ f hf
end SharpRamseyFive.ReverseCap

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma finiteNode_sent_valid (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB c M : ℝ)
    (t : FiniteNodeTape pred H q) (m : FiniteNodeMessage pred UB H q t)
    (hm : finiteNodeEncoded pred A UA B UB H nA nB q MA MB c M t=some m) :
    ValidCap B UB MB (UB∩(finiteNodeDecoded pred UB H q t m).1) ∧
    ValidCap A UA MA (UA∩(finiteNodeDecoded pred UB H q t m).2) := by
  have hp := (finiteNode_prefixes pred A UA B UB H nA nB q MA MB c M t m hm).2.2
  have hh := ambientPair_prefixes A UA B UB (pred.decoded t.1 m.1) H nA nB q MA MB t.2 m.2 hp
  exact ⟨hh.2.1,universalFreshEncoded_valid _ _ _ _ _ _ _ _ _ _ _ _ hh.2.2⟩
end SharpRamseyFive.ProjectiveIncidence

end OAI
