import OAI.Probability.InvariantIsing.Fields.SeedPairRecursion
import OAI.Probability.InvariantIsing.Core.PairProductShuffle

namespace OAI

/-! Two independent seed forests give the independent branch of the finite recursion. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

private lemma zip_finCons {A B : Type*} {n : ℕ} (a : A) (b : B)
    (f : Fin n → A) (g : Fin n → B) :
    (fun i : Fin (n+1) => ((Fin.cons a f : Fin (n+1) → A) i,
      (Fin.cons b g : Fin (n+1) → B) i)) =
        (Fin.cons (a,b) (fun i => (f i,g i)) : Fin (n+1) → A × B) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem seed_independent_pair_evaluation (n : ℕ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i))) (z₁ z₂ : ι → ℝ)
    (α β : LabeledLeaf n) (F : (Fin n → (ι → ℝ) × (ι → ℝ)) → ℝ)
    (hF : Measurable F) {C : ℝ} (hB : ∀ w, |F w| ≤ C) :
    (∫ g : MarkForest unitInterval n × MarkForest unitInterval n,
      F (fun i => (cascadeSeedPath n ψ z₁ g.1 α i,cascadeSeedPath n ψ z₂ g.2 β i))
      ∂(markForestLaw unitInterval n (fun _ => cascadeSeedLaw) : Measure (MarkForest unitInterval n)).prod
        (markForestLaw unitInterval n (fun _ => cascadeSeedLaw) : Measure (MarkForest unitInterval n))) =
      seedPairPathMean n ψ 0 z₁ z₂ F := by
  induction n generalizing ψ z₁ z₂ with
  | zero =>
    have he (g : MarkForest unitInterval 0 × MarkForest unitInterval 0) :
        (fun i => (cascadeSeedPath 0 ψ z₁ g.1 α i,cascadeSeedPath 0 ψ z₂ g.2 β i)) = Fin.elim0 :=
      funext fun i => i.elim0
    simp only [he,integral_const,probReal_univ,one_smul,seedPairPathMean]
  | succ n ih =>
    let Q : Measure (MarkForest unitInterval n) := markForestLaw unitInterval n (fun _ => cascadeSeedLaw)
    let H := fun p : (unitInterval × unitInterval) ×
        (MarkForest unitInterval n × MarkForest unitInterval n) =>
      F (Fin.cons (ψ 0 z₁ p.1.1,ψ 0 z₂ p.1.2) (fun i =>
        (cascadeSeedPath n (fun j => ψ (j+1)) (z₁+ψ 0 z₁ p.1.1) p.2.1 α.2 i,
         cascadeSeedPath n (fun j => ψ (j+1)) (z₂+ψ 0 z₂ p.1.2) p.2.2 β.2 i)))
    have hA : Measurable (fun p : (unitInterval × unitInterval) ×
        (MarkForest unitInterval n × MarkForest unitInterval n) => ψ 0 z₁ p.1.1) :=
      (hψ 0).comp (measurable_const.prodMk measurable_fst.fst)
    have hD : Measurable (fun p : (unitInterval × unitInterval) ×
        (MarkForest unitInterval n × MarkForest unitInterval n) => ψ 0 z₂ p.1.2) :=
      (hψ 0).comp (measurable_const.prodMk measurable_fst.snd)
    have hP := (measurable_cascadeSeedPath n (fun j => ψ (j+1)) (fun j => hψ (j+1)) α.2).comp
      (((measurable_const (a := z₁)).add hA).prodMk measurable_snd.fst)
    have hR := (measurable_cascadeSeedPath n (fun j => ψ (j+1)) (fun j => hψ (j+1)) β.2).comp
      (((measurable_const (a := z₂)).add hD).prodMk measurable_snd.snd)
    have hH : Measurable H := hF.comp (measurable_finCons (hA.prodMk hD)
      (Measurable.of_eval fun i => ((measurable_pi_apply i).comp hP).prodMk
        ((measurable_pi_apply i).comp hR)))
    have hiH : Integrable H ((volume.prod volume).prod (Q.prod Q)) :=
      Integrable.of_bound hH.aestronglyMeasurable C (ae_of_all _ fun p => by
        simpa only [Real.norm_eq_abs] using hB _)
    let R := fun g : MarkForest unitInterval (n+1) × MarkForest unitInterval (n+1) =>
      (((g.1 α.1.1 α.1.2).1,(g.2 β.1.1 β.1.2).1),
        ((g.1 α.1.1 α.1.2).2,(g.2 β.1.1 β.1.2).2))
    calc
      _ = ∫ g, H (R g)
          ∂(markForestLaw unitInterval (n+1) (fun _ => cascadeSeedLaw) : Measure (MarkForest unitInterval (n+1))).prod
            (markForestLaw unitInterval (n+1) (fun _ => cascadeSeedLaw) : Measure (MarkForest unitInterval (n+1))) := by
        apply integral_congr_ae
        apply ae_of_all
        intro g
        exact congrArg F (zip_finCons _ _ _ _)
      _ = ∫ p, H p ∂(volume.prod volume).prod (Q.prod Q) :=
        (markForestPairRoots_preserving n (fun _ => cascadeSeedLaw) α.1 β.1).hasLaw.integral_comp hH.aestronglyMeasurable
      _ = ∫ u, ∫ g, H (u,g) ∂Q.prod Q ∂volume.prod volume := integral_prod _ hiH
      _ = seedPairPathMean (n+1) ψ 0 z₁ z₂ F := by
        rw [seedPairPathMean]
        apply integral_congr_ae
        apply ae_of_all
        intro u
        exact ih (fun j => ψ (j+1)) (fun j => hψ (j+1))
          (z₁+ψ 0 z₁ u.1) (z₂+ψ 0 z₂ u.2) α.2 β.2
          (fun w => F (Fin.cons (ψ 0 z₁ u.1,ψ 0 z₂ u.2) w))
          (hF.comp (measurable_finCons measurable_const measurable_id)) (fun w => hB _)

end InvariantIsing

end

end OAI
