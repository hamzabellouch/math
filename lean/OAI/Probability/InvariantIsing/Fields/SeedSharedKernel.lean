import OAI.Probability.InvariantIsing.Fields.SeedIndependentKernel

namespace OAI

/-! Common-prefix seed updates become common conditional marks from the same ancestor state. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

theorem seed_shared_kernel (n : ℕ) (κ : ℕ → Kernel (ι → ℝ) (ι → ℝ))
    (hκ : ∀ i, IsMarkovKernel (κ i))
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i)))
    (hlaw : ∀ i z, volume.map (ψ i z) = κ i z) (d : ℕ) (z : ι → ℝ)
    (F : (Fin n → (ι → ℝ) × (ι → ℝ)) → ℝ) (hF : Measurable F)
    {C : ℝ} (hB : ∀ w, |F w| ≤ C) :
    seedPairPathMean n ψ d z z F = markPairPathMean n κ d z z F := by
  induction n generalizing κ ψ d z with
  | zero => rfl
  | succ n ih =>
    cases d with
    | zero => exact seed_independent_kernel (n+1) κ hκ ψ hψ hlaw z z F hF hB
    | succ d =>
      let H := fun a : ι → ℝ => seedPairPathMean n (fun j => ψ (j+1)) d
        (z+a) (z+a) (fun w => F (Fin.cons (a,a) w))
      have hH : Measurable H := measurable_seedPairPathMean n (fun j => ψ (j+1))
        (fun j => hψ (j+1)) d (fun a => z+a) (fun a => z+a)
        (measurable_const.add measurable_id) (measurable_const.add measurable_id)
        (fun a w => F (Fin.cons (a,a) w))
        (hF.comp (measurable_finCons (measurable_fst.prodMk measurable_fst) measurable_snd))
      have hP : MeasurePreserving (ψ 0 z) volume (κ 0 z) :=
        ⟨(hψ 0).comp (measurable_const.prodMk measurable_id),hlaw 0 z⟩
      calc
        _ = ∫ a, H a ∂κ 0 z := hP.hasLaw.integral_comp hH.aestronglyMeasurable
        _ = markPairPathMean (n+1) κ (d+1) z z F := by
          rw [markPairPathMean]
          apply integral_congr_ae
          apply ae_of_all
          intro a
          exact ih (fun j => κ (j+1)) (fun j => hκ (j+1))
            (fun j => ψ (j+1)) (fun j => hψ (j+1)) (fun j z => hlaw (j+1) z)
            d (z+a) (fun w => F (Fin.cons (a,a) w))
            (hF.comp (measurable_finCons measurable_const measurable_id)) (fun w => hB _)

end InvariantIsing

end

end OAI
