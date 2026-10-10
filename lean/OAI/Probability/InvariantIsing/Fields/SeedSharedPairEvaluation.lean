import OAI.Probability.InvariantIsing.Fields.SeedPairStep

namespace OAI

/-! The common labeled prefix determines the shared seed updates exactly. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

theorem seed_shared_pair_evaluation (n : ℕ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i))) (z₁ z₂ : ι → ℝ)
    (α β : LabeledLeaf n) (F : (Fin n → (ι → ℝ) × (ι → ℝ)) → ℝ)
    (hF : Measurable F) {C : ℝ} (hB : ∀ w, |F w| ≤ C) :
    (∫ g : MarkForest unitInterval n,
      F (fun i => (cascadeSeedPath n ψ z₁ g α i,cascadeSeedPath n ψ z₂ g β i))
      ∂(markForestLaw unitInterval n (fun _ => cascadeSeedLaw) : Measure (MarkForest unitInterval n))) =
      seedPairPathMean n ψ (labeledCommonDepth n α β) z₁ z₂ F := by
  induction n generalizing ψ z₁ z₂ with
  | zero =>
    have he (g : MarkForest unitInterval 0) :
        (fun i => (cascadeSeedPath 0 ψ z₁ g α i,cascadeSeedPath 0 ψ z₂ g β i)) = Fin.elim0 :=
      funext fun i => i.elim0
    simp only [he,integral_const,probReal_univ,one_smul,seedPairPathMean]
  | succ n ih =>
    rcases α with ⟨a,α⟩
    rcases β with ⟨b,β⟩
    let Q : Measure (MarkForest unitInterval n) := markForestLaw unitInterval n (fun _ => cascadeSeedLaw)
    by_cases hab : a = b
    · subst b
      rw [labeledCommonDepth,ite_eq_left rfl]
      let H := fun p : unitInterval × MarkForest unitInterval n =>
        seedPairStep n ψ z₁ z₂ α β F ((p.1,p.1),(p.2,p.2))
      have hH : Measurable H := (measurable_seedPairStep n ψ hψ z₁ z₂ α β F hF).comp (by fun_prop)
      have hiH : Integrable H (volume.prod Q) :=
        Integrable.of_bound hH.aestronglyMeasurable C (ae_of_all _ fun p => by
          simpa only [Real.norm_eq_abs,H,seedPairStep] using hB _)
      calc
        _ = ∫ g : MarkForest unitInterval (n+1), H (g a.1 a.2)
            ∂(markForestLaw unitInterval (n+1) (fun _ => cascadeSeedLaw) : Measure (MarkForest unitInterval (n+1))) := by
          apply integral_congr_ae
          apply ae_of_all
          intro g
          exact seedPairStep_root n ψ z₁ z₂ (a,α) (a,β) F g g
        _ = ∫ p, H p ∂volume.prod Q :=
          (markForestRoot_preserving n (fun _ => cascadeSeedLaw) a).hasLaw.integral_comp hH.aestronglyMeasurable
        _ = ∫ u, ∫ g, H (u,g) ∂Q ∂volume := integral_prod _ hiH
        _ = seedPairPathMean (n+1) ψ (labeledCommonDepth n α β+1) z₁ z₂ F := by
          rw [seedPairPathMean]
          apply integral_congr_ae
          apply ae_of_all
          intro u
          exact ih (fun j => ψ (j+1)) (fun j => hψ (j+1))
            (z₁+ψ 0 z₁ u) (z₂+ψ 0 z₂ u) α β
            (fun w => F (Fin.cons (ψ 0 z₁ u,ψ 0 z₂ u) w))
            (hF.comp (measurable_finCons measurable_const measurable_id)) (fun w => hB _)
    · rw [labeledCommonDepth,ite_eq_right hab]
      let H := seedPairStep n ψ z₁ z₂ α β F
      have hH : Measurable H := measurable_seedPairStep n ψ hψ z₁ z₂ α β F hF
      have hiH : Integrable H ((volume.prod volume).prod (Q.prod Q)) :=
        Integrable.of_bound hH.aestronglyMeasurable C (ae_of_all _ fun p => by
          simpa only [Real.norm_eq_abs,H,seedPairStep] using hB _)
      calc
        _ = ∫ g : MarkForest unitInterval (n+1),
            H (((g a.1 a.2).1,(g b.1 b.2).1),((g a.1 a.2).2,(g b.1 b.2).2))
            ∂(markForestLaw unitInterval (n+1) (fun _ => cascadeSeedLaw) : Measure (MarkForest unitInterval (n+1))) := by
          apply integral_congr_ae
          apply ae_of_all
          intro g
          exact seedPairStep_root n ψ z₁ z₂ (a,α) (b,β) F g g
        _ = ∫ p, H p ∂(volume.prod volume).prod (Q.prod Q) :=
          (markForestDistinctRoots_preserving n (fun _ => cascadeSeedLaw) a b hab).hasLaw.integral_comp hH.aestronglyMeasurable
        _ = ∫ u, ∫ g, H (u,g) ∂Q.prod Q ∂volume.prod volume := integral_prod _ hiH
        _ = seedPairPathMean (n+1) ψ 0 z₁ z₂ F := by
          rw [seedPairPathMean]
          apply integral_congr_ae
          apply ae_of_all
          intro u
          exact seed_independent_pair_evaluation n (fun j => ψ (j+1)) (fun j => hψ (j+1))
            (z₁+ψ 0 z₁ u.1) (z₂+ψ 0 z₂ u.2) α β
            (fun w => F (Fin.cons (ψ 0 z₁ u.1,ψ 0 z₂ u.2) w))
            (hF.comp (measurable_finCons measurable_const measurable_id)) (fun w => hB _)

end InvariantIsing

end

end OAI
