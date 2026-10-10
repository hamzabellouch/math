import OAI.Probability.InvariantIsing.Fields.CascadeSeedCoupling
import OAI.Probability.IsingPerceptron.NoiseTreeKeep

namespace OAI

/-! Finite-depth vector cascade marking by independent uniform seeds. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

def cascadeSeedLaw : ProbabilityMeasure unitInterval := ⟨volume, inferInstance⟩

section Coordinates
variable {ι : Type} [Fintype ι]

def cascadeSeedTree : (n : ℕ) → (ℕ → ℝ) →
    (ℕ → (ι → ℝ) → unitInterval → (ι → ℝ)) → (ι → ℝ) →
      NoiseTree unitInterval n → NoiseTree (ι → ℝ) n
  | 0, _, _, _, _ => PUnit.unit
  | n+1, b, ψ, z, T =>
    (sigmaPart ((powerIntensity (b 0)).prod ((cascadeSeedLaw : Measure unitInterval).prod
      (noiseCascadeLaw unitInterval n (fun j => b (j+1)) (fun _ => cascadeSeedLaw)))) T).map
        (fun p => (p.1, (ψ 0 z p.2.1,
          cascadeSeedTree n (fun j => b (j+1)) (fun j => ψ (j+1))
            (z+ψ 0 z p.2.1) p.2.2)))

omit [Fintype ι] in
lemma measurable_cascadeSeedTree (n : ℕ) (b : ℕ → ℝ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i))) :
    Measurable (fun p : (ι → ℝ) × NoiseTree unitInterval n => cascadeSeedTree n b ψ p.1 p.2) := by
  induction n generalizing b ψ with
  | zero => exact measurable_const
  | succ n ih =>
    unfold cascadeSeedTree
    apply measurable_map_sigmaPart_param _ measurable_snd
      (G := fun p : ((ι → ℝ) × NoiseTree unitInterval (n+1)) ×
        (ℝ × (unitInterval × NoiseTree unitInterval n)) =>
          (p.2.1, (ψ 0 p.1.1 p.2.2.1,
            cascadeSeedTree n (fun j => b (j+1)) (fun j => ψ (j+1))
              (p.1.1+ψ 0 p.1.1 p.2.2.1) p.2.2.2)))
    have hmark : Measurable (fun p : ((ι → ℝ) × NoiseTree unitInterval (n+1)) ×
        (ℝ × (unitInterval × NoiseTree unitInterval n)) => ψ 0 p.1.1 p.2.2.1) :=
      (hψ 0).comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd)))
    exact (by fun_prop : Measurable (fun p : ((ι → ℝ) × NoiseTree unitInterval (n+1)) ×
      (ℝ × (unitInterval × NoiseTree unitInterval n)) => p.2.1)).prodMk
        (hmark.prodMk ((ih _ _ (fun i => hψ (i+1))).comp
          (((by fun_prop : Measurable (fun p : ((ι → ℝ) × NoiseTree unitInterval (n+1)) ×
            (ℝ × (unitInterval × NoiseTree unitInterval n)) => p.1.1)).add hmark).prodMk (by fun_prop))))

omit [Fintype ι] in
lemma cascadeSeedTree_law_succ (n : ℕ) (b : ℕ → ℝ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i))) (z : ι → ℝ) :
    let P : Measure (NoiseTree unitInterval n) :=
      noiseCascadeLaw unitInterval n (fun j => b (j+1)) (fun _ => cascadeSeedLaw)
    let G := fun p : ℝ × (unitInterval × NoiseTree unitInterval n) =>
      (p.1, (ψ 0 z p.2.1,
        cascadeSeedTree n (fun j => b (j+1)) (fun j => ψ (j+1)) (z+ψ 0 z p.2.1) p.2.2))
    (noiseCascadeLaw unitInterval (n+1) b (fun _ => cascadeSeedLaw) :
      Measure (NoiseTree unitInterval (n+1))).map (cascadeSeedTree (n+1) b ψ z) =
      poissonLaw (((powerIntensity (b 0)).prod ((cascadeSeedLaw : Measure unitInterval).prod P)).map G) := by
  intro P G
  let J := (powerIntensity (b 0)).prod ((cascadeSeedLaw : Measure unitInterval).prod P)
  have hG : Measurable G := by
    change Measurable (fun p : ℝ × (unitInterval × NoiseTree unitInterval n) =>
      (p.1, (ψ 0 z p.2.1,
        cascadeSeedTree n (fun j => b (j+1)) (fun j => ψ (j+1)) (z+ψ 0 z p.2.1) p.2.2)))
    have hmark : Measurable (fun p : ℝ × (unitInterval × NoiseTree unitInterval n) => ψ 0 z p.2.1) :=
      (hψ 0).comp (measurable_const.prodMk (measurable_fst.comp measurable_snd))
    exact measurable_fst.prodMk (hmark.prodMk
      ((measurable_cascadeSeedTree n _ _ (fun i => hψ (i+1))).comp
        ((measurable_const.add hmark).prodMk (by fun_prop))))
  rw [noiseCascadeLaw_succ]
  change (poissonLaw J).map _ = poissonLaw (J.map G)
  calc
    _ = (poissonLaw J).map (fun T => T.map G) := by
      apply Measure.map_congr
      filter_upwards [sigmaPart_eq_ae J] with T hT
      change (sigmaPart J T).map G = T.map G
      rw [hT]
    _ = _ := poissonLaw_map J hG

end Coordinates
end InvariantIsing

end

end OAI
