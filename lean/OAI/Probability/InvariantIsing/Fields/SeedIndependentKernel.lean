import OAI.Probability.InvariantIsing.Fields.MarkPairRecursion

namespace OAI

/-! Replacing independent uniform seeds by their normalized conditional mark kernels. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

theorem seed_independent_kernel (n : ℕ) (κ : ℕ → Kernel (ι → ℝ) (ι → ℝ))
    (hκ : ∀ i, IsMarkovKernel (κ i))
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i)))
    (hlaw : ∀ i z, volume.map (ψ i z) = κ i z) (z₁ z₂ : ι → ℝ)
    (F : (Fin n → (ι → ℝ) × (ι → ℝ)) → ℝ) (hF : Measurable F)
    {C : ℝ} (hB : ∀ w, |F w| ≤ C) :
    seedPairPathMean n ψ 0 z₁ z₂ F = markPairPathMean n κ 0 z₁ z₂ F := by
  induction n generalizing κ ψ z₁ z₂ with
  | zero => rfl
  | succ n ih =>
    let H := fun p : (ι → ℝ) × (ι → ℝ) =>
      seedPairPathMean n (fun j => ψ (j+1)) 0 (z₁+p.1) (z₂+p.2)
        (fun w => F (Fin.cons (p.1,p.2) w))
    have hH : Measurable H := measurable_seedPairPathMean n (fun j => ψ (j+1))
      (fun j => hψ (j+1)) 0 (fun p : (ι → ℝ) × (ι → ℝ) => z₁+p.1) (fun p => z₂+p.2)
      (measurable_const.add measurable_fst) (measurable_const.add measurable_snd)
      (fun (p : (ι → ℝ) × (ι → ℝ)) w => F (Fin.cons (p.1,p.2) w))
      (hF.comp (measurable_finCons measurable_fst measurable_snd))
    have hP : MeasurePreserving (fun u : unitInterval × unitInterval =>
        (ψ 0 z₁ u.1,ψ 0 z₂ u.2)) (volume.prod volume) ((κ 0 z₁).prod (κ 0 z₂)) :=
      (show MeasurePreserving (ψ 0 z₁) volume (κ 0 z₁) from
        ⟨(hψ 0).comp (measurable_const.prodMk measurable_id),hlaw 0 z₁⟩).prod
      (show MeasurePreserving (ψ 0 z₂) volume (κ 0 z₂) from
        ⟨(hψ 0).comp (measurable_const.prodMk measurable_id),hlaw 0 z₂⟩)
    let := hκ 0
    have hiH : Integrable H ((κ 0 z₁).prod (κ 0 z₂)) :=
      Integrable.of_bound hH.aestronglyMeasurable C (ae_of_all _ fun p => by
        simpa only [Real.norm_eq_abs] using seedPairPathMean_abs_le n (fun j => ψ (j+1))
          0 (z₁+p.1) (z₂+p.2) (fun w => F (Fin.cons (p.1,p.2) w)) (fun w => hB _))
    calc
      _ = ∫ p, H p ∂(κ 0 z₁).prod (κ 0 z₂) := hP.hasLaw.integral_comp hH.aestronglyMeasurable
      _ = ∫ a₁, ∫ a₂, H (a₁,a₂) ∂κ 0 z₂ ∂κ 0 z₁ := integral_prod _ hiH
      _ = markPairPathMean (n+1) κ 0 z₁ z₂ F := by
        rw [markPairPathMean]
        apply integral_congr_ae
        apply ae_of_all
        intro a₁
        apply integral_congr_ae
        apply ae_of_all
        intro a₂
        exact ih (fun j => κ (j+1)) (fun j => hκ (j+1))
          (fun j => ψ (j+1)) (fun j => hψ (j+1)) (fun j z => hlaw (j+1) z)
          (z₁+a₁) (z₂+a₂) (fun w => F (Fin.cons (a₁,a₂) w))
          (hF.comp (measurable_finCons measurable_const measurable_id)) (fun w => hB _)

end InvariantIsing

end

end OAI
