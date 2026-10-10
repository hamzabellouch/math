import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.SurvivorRank
import OAI.Combinatorics.RamseyFive.Marking.WindowReciprocalScores
import OAI.Combinatorics.RamseyFive.Entropy.IndependentSampling

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {Ω I : Type*} [Fintype Ω] [Fintype I]

theorem retained_filter_loss (p : Law Ω) (eligible : I→Prop)
    (kept : Ω→I→Prop) (B : ℝ) (hB : 0≤B)
    (hkeep : ∀i,eligible i→mean p (fun z=>if kept z i then 0 else 1)≤B) :
    mean p (fun z=>(((Finset.univ.filter fun i=>eligible i ∧ kept z i)ᶜ).card:ℝ))≤
      ((Finset.univ.filter fun i=>¬eligible i).card:ℝ)+(Fintype.card I:ℝ)*B := by
  have hcard (z : Ω) :
      (((Finset.univ.filter fun i=>eligible i ∧ kept z i)ᶜ).card:ℝ)=
      ∑i,if eligible i ∧ kept z i then (0:ℝ) else 1 := by
    have heq : (Finset.univ.filter fun i=>eligible i ∧ kept z i)ᶜ =
        Finset.univ.filter (fun i=>¬(eligible i ∧ kept z i)) := by ext i; simp
    rw [heq,←Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp_all
  simp_rw [hcard]
  rw [mean_sum]
  calc
    _ ≤ ∑i,((if eligible i then 0 else 1)+B) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : eligible i
      · simpa only [hi,true_and,ite_true,zero_add] using hkeep i hi
      · simpa only [hi,false_and,ite_false,mean_const] using le_add_of_nonneg_right hB
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      congr 1
      simp only [←Finset.sum_boole]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp_all
end
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.ProjectiveIncidence
noncomputable local instance origWindowIDE (w n : ℕ) : DecidableEq (Windows.Slots w n) := Classical.decEq _
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Windows Marking
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))

theorem original_window_target_failure {w n : ℕ} (E : Finset (Fin w)) (_hE : E.Nonempty)
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (μ : Fin (E.card+1)→Law (Finset (ℙ K V)))
    (ν : Fin (E.card+1)→Law (Finset (ℙ K (Dual K V))))
    (X : Fin (E.card+1)→Finset (ℙ K V)→Finset (ℙ K V))
    (Y : Fin (E.card+1)→Finset (ℙ K (Dual K V))→Finset (ℙ K (Dual K V)))
    (hX : ∀i a,(X i a).Nonempty) (hY : ∀i b,(Y i b).Nonempty)
    (p : Law (Slots w n→FlagPair K V))
    (hinc : ∀x,0<p x→∀i,Incident (x i).1 (x i).2)
    (c δ τ P : ℝ) (hδ : 0<δ) (v : Fin w) (hv : v∈E) (j : Fin (2*n)) :
    mean (adaptiveLaw p (fun _=>adaptiveLaw (originalLevelLaw μ ν)
      (fun _=>variableTreeLaw f r w))) (fun z=>
        if z.1 (middleSlot v j)∉variableTreeDomain f r z.2.2 (Finset.univ,Finset.univ)
          (variableTreeEncoded f r z.2.2 (Finset.univ,Finset.univ)
            ⟨E.card,Nat.lt_succ_of_le (by simpa using Finset.card_le_univ E)⟩ σ hσ hq hd
            (fun i=>X i (z.2.1.1 i)) (fun i=>Y i (z.2.1.2 i))
            (fun i=>hX i _) (fun i=>hY i _) c δ τ P hδ)
          (survivorRank E v) then 1 else 0)=
      orientedTargetFailure f r σ hσ hq hd μ ν X Y hX hY p
        (fun x=>(x (middleSlot v j)).1) (fun x=>(x (middleSlot v j)).2)
        c δ τ P hδ (finiteBalanced E.card)
        ((finiteRankEquiv E.card).symm ⟨(survivorRank E v).val,survivorRank_mem_lt E v hv⟩) := by
  have hh:=variable_table_target_failure f r w
    ⟨E.card,Nat.lt_succ_of_le (by simpa using Finset.card_le_univ E)⟩ σ hσ hq hd μ ν X Y hX hY p
    (fun x=>(x (middleSlot v j)).1) (fun x=>(x (middleSlot v j)).2)
    (fun x hx=>hinc x hx _) c δ τ P hδ
    ⟨(survivorRank E v).val,survivorRank_mem_lt E v hv⟩
  exact hh
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
