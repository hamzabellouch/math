import Mathlib
import OAI.Probability.Perceptron.Variational.VarianceProdMemLp

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy
variable {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [Nonempty X]
  (μ : Measure X) [IsProbabilityMeasure μ]

theorem variance_pi_le_of_measurable_bounded_differences (n : ℕ) {F : (Fin n → X) → ℝ}
    (hF : Measurable F) {K c : ℝ} (hK : ∀ x, |F x| ≤ K)
    (hdiff : ∀ x i y, |F (Function.update x i y) - F x| ≤ c) :
    variance F (Measure.pi fun _ : Fin n => μ) ≤ (n : ℝ) * c ^ 2 := by
  classical
  induction n with
  | zero =>
      rw [Measure.pi_of_empty]
      simp
  | succ n ih =>
      let ν := Measure.pi fun _ : Fin n => μ
      let G : X × (Fin n → X) → ℝ := fun p => F (Fin.cons (α := fun _ => X) p.1 p.2)
      have hG : Measurable G := hF.comp (measurableEmbedding_fin_cons (X := X) n).measurable
      have hGK (p) : |G p| ≤ K := hK _
      have hA (x : X) : variance (fun y => G (x, y)) ν ≤ (n : ℝ) * c ^ 2 := by
        apply ih (hG.comp (measurable_const.prodMk measurable_id)) (fun y => hGK (x,y))
        intro y i z
        simpa only [G, Function.comp_apply, id_eq, Fin.cons_update] using hdiff (Fin.cons x y) i.succ z
      have hHc : Measurable (fun x => ∫ y, G (x, y) ∂ν) :=
        hG.stronglyMeasurable.integral_prod_right'.measurable
      have hHosc (x x' : X) :
          |(∫ y, G (x, y) ∂ν) - ∫ y, G (x', y) ∂ν| ≤ c := by
        have hi (x : X) : Integrable (fun y => G (x, y)) ν :=
          (integrable_const K).mono'
            (hG.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
            (Filter.Eventually.of_forall fun y => hGK (x, y))
        rw [← integral_sub (hi x) (hi x')]
        have hh : ∀ y, |G (x, y) - G (x', y)| ≤ c := by
          intro y
          have hu : Function.update (Fin.cons x' y) 0 x = Fin.cons (α := fun _ => X) x y := by
            ext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          simpa only [G, hu] using hdiff (Fin.cons x' y) 0 x
        simpa using norm_integral_le_of_norm_le_const
          (μ := ν) (f := fun y => G (x,y) - G (x',y))
          (Filter.Eventually.of_forall hh)
      have hpF : MemLp F 2 (Measure.pi fun _ : Fin (n+1) => μ) :=
        MemLp.of_bound hF.aestronglyMeasurable K (Filter.Eventually.of_forall hK)
      have hpG : MemLp G 2 (μ.prod ν) :=
        MemLp.of_bound hG.aestronglyMeasurable K (Filter.Eventually.of_forall hGK)
      have hHL : MemLp (fun x => ∫ y, G (x,y) ∂ν) 2 μ :=
        MemLp.of_bound hHc.aestronglyMeasurable K (ae_of_all _ fun x => by
          simpa using norm_integral_le_of_norm_le_const (μ := ν)
            (f := fun y => G (x,y)) (ae_of_all _ fun y => hGK (x,y)))
      let x₀ : X := Classical.choice ‹Nonempty X›
      have hHrange : ∀ᵐ x ∂μ, (∫ y, G (x,y) ∂ν) ∈
          Icc ((∫ y, G (x₀,y) ∂ν)-c) ((∫ y, G (x₀,y) ∂ν)+c) := by
        exact ae_of_all _ fun x => by
          have hh := abs_le.mp (hHosc x x₀)
          constructor <;> linarith
      have hB : variance (fun x => ∫ y, G (x,y) ∂ν) μ ≤ c^2 := by
        convert variance_le_sq_of_bounded hHrange hHc.aemeasurable using 1
        ring
      have hv := variance_prod_le_memLp μ ν hpG
        (fun x => MemLp.of_bound (hG.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
          K (ae_of_all _ fun y => hGK (x,y))) hHL hA hB
      rw [variance_eq_sub hpG] at hv
      rw [variance_eq_sub hpF]
      have hmean := (measurePreserving_fin_cons μ n).integral_comp
        (measurableEmbedding_fin_cons (X := X) n) F
      have hsquare := (measurePreserving_fin_cons μ n).integral_comp
        (measurableEmbedding_fin_cons (X := X) n) (fun x => F x ^ 2)
      change (∫ x, G x ∂μ.prod ν) = _ at hmean
      change (∫ x, G x ^ 2 ∂μ.prod ν) = _ at hsquare
      simp only [Pi.pow_apply] at hv ⊢
      rw [hsquare, hmean] at hv
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using hv

end SphericalPerceptronFreeEnergy
end

end OAI
