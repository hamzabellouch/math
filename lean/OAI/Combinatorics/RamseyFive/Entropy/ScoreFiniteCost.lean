import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.BaseFinitePublic

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence Metadata FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
noncomputable def scoreFiniteCost (U : Finset (ℙ K V)) (σ P τ : ℝ)
    (m : ScoredMessage U σ P τ) : ℝ :=
  Real.log (Fintype.card (ℙ K V)+1:ℝ)+Real.log (Fintype.card (ScoredPayload U m.1 σ P τ):ℝ)

omit [Finite K] [FiniteDimensional K V] [Fintype V] in
lemma scoreFinite_header (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (σ P τ c a : ℝ)
    (code : TrainingCode V (listCap σ) (productCap σ) (Nat.card V))
    (t : ScoreTable U σ P τ) (m : ScoredMessage U σ P τ)
    (hm : scoreFiniteEncoded X U n σ P τ c a code t=some m) : m.1=n := by
  obtain ⟨z,_,hz⟩ := Option.map_eq_some_iff.mp hm
  exact congrArg (fun y : ScoredMessage U σ P τ=>y.1) hz.symm

omit [Finite K] [FiniteDimensional K V] [Fintype V] in
lemma scoreFinite_sound (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (σ P τ c a : ℝ)
    (code : TrainingCode V (listCap σ) (productCap σ) (Nat.card V))
    (t : ScoreTable U σ P τ) (m : ScoredMessage U σ P τ)
    (hm : scoreFiniteEncoded X U n σ P τ c a code t=some m) :
    t m⊆U ∧ ((t m).card:ℝ)≤(X.card:ℝ)*Real.exp (a*P) ∧ c*X.card≤((t m∩X).card:ℝ) := by
  obtain ⟨z,hz,he⟩ := Option.map_eq_some_iff.mp hm
  have hs := chooseMessage_sound _ t z hz
  simpa only [he] using hs

omit [Finite K] [FiniteDimensional K V] in
lemma scoreFinite_cost_of_header (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (σ P τ c a B : ℝ)
    (code : TrainingCode V (listCap σ) (productCap σ) (Nat.card V))
    (hcost : Real.log (Fintype.card (ℙ K V)+1:ℝ)+
      Real.log (Fintype.card (ScoredPayload U n σ P τ):ℝ)≤B)
    (t : ScoreTable U σ P τ) (m : ScoredMessage U σ P τ)
    (hm : scoreFiniteEncoded X U n σ P τ c a code t=some m) : scoreFiniteCost U σ P τ m≤B := by
  unfold scoreFiniteCost
  rw [scoreFinite_header X U n σ P τ c a code t m hm]
  exact hcost

end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
  {Ω : ι→Type*} [∀i,Fintype (Ω i)] {M : ∀i,Ω i→Type*}

abbrev BranchMessage (t : ∀i,Ω i) := (i : ι)×M i (t i)
noncomputable def branchDecoded (decode : ∀i t,M i t→α) (t : ∀i,Ω i)
    (m : BranchMessage (M:=M) t) : α := decode m.1 (t m.1) m.2
noncomputable def branchEncoded (i : ι) (encode : ∀t : Ω i,Option (M i t))
    (t : ∀i,Ω i) : Option (BranchMessage (M:=M) t) :=
  (encode (t i)).map (Sigma.mk i)

theorem branch_output_law (p : ∀i,Law (Ω i)) (i : ι)
    (encode : ∀t : Ω i,Option (M i t)) (decode : ∀i t,M i t→α) :
    map (piLaw p) (fun t=>(branchEncoded i encode t).map (branchDecoded decode t))=
      map (p i) (fun t=>(encode t).map (decode i t)) := by
  have hh := congrArg (fun q=>map q (fun t=>(encode t).map (decode i t))) (piLaw_eval p i)
  rw [map_comp] at hh
  simpa only [branchEncoded,branchDecoded,Option.map_map,Function.comp_def] using hh

omit [Fintype ι] [DecidableEq ι] [∀index,Fintype (Ω index)] in
lemma branch_header (i : ι) (encode : ∀t : Ω i,Option (M i t))
    (t : ∀i,Ω i) (m : BranchMessage (M:=M) t)
    (hm : branchEncoded i encode t=some m) : m.1=i := by
  obtain ⟨z,_,hz⟩ := Option.map_eq_some_iff.mp hm
  exact congrArg Sigma.fst hz.symm

omit [Fintype ι] [DecidableEq ι] [∀index,Fintype (Ω index)] in
lemma branch_sent (i : ι) (encode : ∀t : Ω i,Option (M i t))
    (t : ∀i,Ω i) (m : BranchMessage (M:=M) t)
    (hm : branchEncoded i encode t=some m) :
    ∃z,encode (t i)=some z ∧ Sigma.mk i z=m := Option.map_eq_some_iff.mp hm
end SharpRamseyFive.FiniteEntropy

end OAI
