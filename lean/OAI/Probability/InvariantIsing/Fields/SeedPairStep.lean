import OAI.Probability.InvariantIsing.Fields.SeedIndependentPairEvaluation

namespace OAI

/-! Measurability of one pair of root updates with both descendant paths. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

def seedPairStep (n : ℕ) (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (z₁ z₂ : ι → ℝ) (α β : LabeledLeaf n)
    (F : (Fin (n+1) → (ι → ℝ) × (ι → ℝ)) → ℝ)
    (p : (unitInterval × unitInterval) × (MarkForest unitInterval n × MarkForest unitInterval n)) : ℝ :=
  F (Fin.cons (ψ 0 z₁ p.1.1,ψ 0 z₂ p.1.2) (fun i =>
    (cascadeSeedPath n (fun j => ψ (j+1)) (z₁+ψ 0 z₁ p.1.1) p.2.1 α i,
     cascadeSeedPath n (fun j => ψ (j+1)) (z₂+ψ 0 z₂ p.1.2) p.2.2 β i)))

lemma measurable_seedPairStep (n : ℕ) (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i))) (z₁ z₂ : ι → ℝ)
    (α β : LabeledLeaf n) (F : (Fin (n+1) → (ι → ℝ) × (ι → ℝ)) → ℝ)
    (hF : Measurable F) : Measurable (seedPairStep n ψ z₁ z₂ α β F) := by
  have hA : Measurable (fun p : (unitInterval × unitInterval) ×
      (MarkForest unitInterval n × MarkForest unitInterval n) => ψ 0 z₁ p.1.1) :=
    (hψ 0).comp (measurable_const.prodMk measurable_fst.fst)
  have hB : Measurable (fun p : (unitInterval × unitInterval) ×
      (MarkForest unitInterval n × MarkForest unitInterval n) => ψ 0 z₂ p.1.2) :=
    (hψ 0).comp (measurable_const.prodMk measurable_fst.snd)
  have hP := (measurable_cascadeSeedPath n (fun j => ψ (j+1)) (fun j => hψ (j+1)) α).comp
    (((measurable_const (a := z₁)).add hA).prodMk measurable_snd.fst)
  have hR := (measurable_cascadeSeedPath n (fun j => ψ (j+1)) (fun j => hψ (j+1)) β).comp
    (((measurable_const (a := z₂)).add hB).prodMk measurable_snd.snd)
  exact hF.comp (measurable_finCons (hA.prodMk hB)
    (Measurable.of_eval fun i => ((measurable_pi_apply i).comp hP).prodMk
      ((measurable_pi_apply i).comp hR)))

lemma seedPairStep_root (n : ℕ) (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (z₁ z₂ : ι → ℝ) (α β : LabeledLeaf (n+1))
    (F : (Fin (n+1) → (ι → ℝ) × (ι → ℝ)) → ℝ)
    (g h : MarkForest unitInterval (n+1)) :
    F (fun i => (cascadeSeedPath (n+1) ψ z₁ g α i,cascadeSeedPath (n+1) ψ z₂ h β i)) =
      seedPairStep n ψ z₁ z₂ α.2 β.2 F
        (((g α.1.1 α.1.2).1,(h β.1.1 β.1.2).1),((g α.1.1 α.1.2).2,(h β.1.1 β.1.2).2)) := by
  apply congrArg F
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

end InvariantIsing

end

end OAI
