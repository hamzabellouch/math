import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.FourFinitePredictor

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma finiteNodeNextLaw_produced (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (hA : A.Nonempty) (hB : B.Nonempty) (c M : ℝ) (hc : 0<c)
    (W : Finset (ℙ K V)) (hcap : CaptureBound A UA c M W)
    (H : ℕ)
    (hnA : reverseLength (Nat.card K) (Real.log ((UA.card:ℝ)/A.card))<H+1)
    (hnB : reverseLength (Nat.card K) (Real.log ((UB.card:ℝ)/B.card))<H+1) :
    finiteNodeNextLaw A UA B UB H ⟨_,hnA⟩ ⟨_,hnB⟩ (Nat.card K)
      ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card)
      ((320/c+320)*(Nat.card K:ℝ)^5/A.card) c M (some W)=
        producedPairLaw A UA B UB hB c (some W) := by
  have hW : W.Nonempty := (hcap.nonempty hA hc).mono Finset.inter_subset_right
  unfold finiteNodeNextLaw finiteNodeNextOut
  simp only [Option.bind_some,dite_eq_left hcap]
  rw [ambientPair_law _ _ _ _ hB _ hW]
  simp only [producedPairLaw,dite_eq_left hW]

theorem finiteNode_cost (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (hA : A.Nonempty) (hAU : A⊆UA) (hB : B.Nonempty) (hBU : B⊆UB)
    (c P b C : ℝ) (hc : 0<c) (hc1 : c≤1) (hP : 1≤P) (hb : b≤P)
    (hprod : (Nat.card K:ℝ)^5*Real.exp (-b)≤(A.card:ℝ)*B.card)
    (hcoef : 320/c+320≤Real.exp P)
    (hcost : ∀t m,pred.encoded A B t=some m → pred.cost t m≤
      C*(Nat.card K:ℝ)*P*(Real.log ((UA.card:ℝ)/A.card)+Real.log ((UB.card:ℝ)/B.card)+P))
    (hnA : reverseLength (Nat.card K) (Real.log ((UA.card:ℝ)/A.card))≤1000*(Nat.card K)^2)
    (hnB : reverseLength (Nat.card K) (Real.log ((UB.card:ℝ)/B.card))≤1000*(Nat.card K)^2)
    (t : FiniteNodeTape pred (1000*(Nat.card K)^2) (Nat.card K))
    (m : FiniteNodeMessage pred UB (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : finiteNodeEncoded pred A UA B UB _ ⟨_,Nat.lt_succ_of_le hnA⟩ ⟨_,Nat.lt_succ_of_le hnB⟩
      (Nat.card K) ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card)
      ((320/c+320)*(Nat.card K:ℝ)^5/A.card) c ((A.card:ℝ)*Real.exp (10*P)) t=some m) :
    finiteNodeCost pred UB (1000*(Nat.card K)^2) (Nat.card K) t m≤
      (C+2020+21*(12-Real.log c-Real.log ((9:ℝ)/10)))*(Nat.card K:ℝ)*P*
        (Real.log ((UA.card:ℝ)/A.card)+Real.log ((UB.card:ℝ)/B.card)+P) := by
  obtain ⟨hp,hcap,hr⟩ := finiteNode_prefixes pred A UA B UB _ _ _ _ _ _ _ _ t m hm
  have h₁ := hcost t.1 m.1 hp
  have h₂ := ambientPair_cost σ hσ hq hd A UA B UB hA hAU hB hBU _ c P b hc hc1 hP hb hprod hcoef
    hcap hnA hnB t.2 m.2 hr
  unfold finiteNodeCost
  nlinarith only [h₁,h₂]
end SharpRamseyFive.ProjectiveIncidence

end OAI
