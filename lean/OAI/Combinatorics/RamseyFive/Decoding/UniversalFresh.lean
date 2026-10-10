import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.FreshPublicFamily

namespace OAI


namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

abbrev FreshIndex (B : Type*) [Fintype B] (H : ℕ) :=
  {W : Finset B // W.Nonempty} × Fin (H+1)
abbrev UniversalFresh (B : Type*) [Fintype B] (H : ℕ) (q : ℝ) :=
  (i : FreshIndex B H)→FreshTape i.1.1 i.2 q
noncomputable def universalFreshLaw (B : Type*) [Fintype B] (H : ℕ) (q : ℝ) :
    Law (UniversalFresh B H q) :=
  piLaw fun i : FreshIndex B H=>freshTapeLaw i.1.1 i.1.2 i.2 q

lemma universalFresh_marginal (H : ℕ) (q : ℝ) (i : FreshIndex B H) :
    map (universalFreshLaw B H q) (fun t=>t i)=freshTapeLaw i.1.1 i.1.2 i.2 q :=
  piLaw_eval _ i

lemma universalFresh_output (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hW : W.Nonempty) (hCW : C⊆W) (H n : ℕ) (hn : n≤H)
    (q M : ℝ) :
    let i : FreshIndex B H := (⟨W,hW⟩,⟨n,Nat.lt_succ_of_le hn⟩)
    map (universalFreshLaw B H q)
      (fun t=>Option.map (freshDecoded R W n q (t i)) (freshEncoded R S U C W hCW n q M (t i)))=
      ambientCapLaw R S U C W hW n q M := by
  dsimp only
  rw [←fresh_public_law R S U C W hCW hW n q M]
  have hm := universalFresh_marginal (B:=B) H q
    ((⟨W,hW⟩,⟨n,Nat.lt_succ_of_le hn⟩) : FreshIndex B H)
  rw [←hm,map_comp]
  rfl

theorem universalFresh_adaptive {Θ : Type*} [Fintype Θ]
    (prior : Law Θ) (H : ℕ) (q : ℝ) (i : Θ→FreshIndex B H)
    (decode : ∀θ,FreshTape (i θ).1.1 (i θ).2 q→Option (Finset A)) :
    map (adaptiveLaw prior (fun _=>universalFreshLaw B H q)) (fun z=>decode z.1 (z.2 (i z.1)))=
      map (adaptiveLaw prior (fun θ=>map (freshTapeLaw (i θ).1.1 (i θ).1.2 (i θ).2 q) (decode θ))) Prod.snd := by
  apply Law.ext
  funext Y
  simp only [map,adaptiveLaw,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro θ _
  have hm := universalFresh_marginal H q (i θ)
  have hh := congrArg (fun p=>map p (decode θ) Y) hm
  have hh' : map (universalFreshLaw B H q) (fun t=>decode θ (t (i θ))) Y=
      map (freshTapeLaw (i θ).1.1 (i θ).1.2 (i θ).2 q) (decode θ) Y := by
    convert hh using 1; simp only [map_comp,Function.comp_def]
  calc
    _ = prior θ * map (universalFreshLaw B H q) (fun t=>decode θ (t (i θ))) Y := by
      simp only [map,Finset.mul_sum,mul_ite,mul_zero]
    _ = prior θ * map (freshTapeLaw (i θ).1.1 (i θ).1.2 (i θ).2 q) (decode θ) Y := by rw [hh']
    _ = _ := by
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,map]
      congr 1
      apply Finset.sum_congr
      · ext x; simp
      · intro x _; congr 1
end SharpRamseyFive.ReverseCap

end OAI
