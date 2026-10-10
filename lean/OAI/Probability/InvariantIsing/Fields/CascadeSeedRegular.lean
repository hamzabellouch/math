import OAI.Probability.InvariantIsing.Fields.CascadeSeedTree
import OAI.Probability.IsingPerceptron.NoiseGibbsRegular

namespace OAI

/-! Regularity of uniform-seed trees, independent of the ancestor state. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal
namespace InvariantIsing

def CascadeSeedRegular (n : ℕ) (b : ℕ → ℝ) (T : NoiseTree unitInterval n) : Prop :=
  NoiseGibbsRegular n b (fun _ => cascadeSeedLaw)
    (fun _ (_ : PUnit × unitInterval) => 1) (fun _ _ => PUnit.unit) PUnit.unit T

lemma cascadeSeedRegular_ae (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) :
    ∀ᵐ T ∂(noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure _),
      CascadeSeedRegular n b T := by
  exact noiseGibbsRegular_ae n b hb (fun _ => cascadeSeedLaw)
    (fun _ => measurable_const) (fun _ => measurable_const) (fun _ _ _ => zero_lt_one)
    (fun _ _ => by simp) PUnit.unit

lemma cascadeSeedRegular_sigma {n : ℕ} {b : ℕ → ℝ} {T : NoiseTree unitInterval (n+1)}
    (hT : CascadeSeedRegular (n+1) b T) :
    sigmaPart ((powerIntensity (b 0)).prod ((cascadeSeedLaw : Measure unitInterval).prod
      (noiseCascadeLaw unitInterval n (fun j => b (j+1)) (fun _ => cascadeSeedLaw)))) T = T :=
  Marked.sigmaPart_eq_of_good _ hT.2.2.1

lemma cascadeSeedRegular_tail {n : ℕ} {b : ℕ → ℝ} {T : NoiseTree unitInterval (n+1)}
    (hT : CascadeSeedRegular (n+1) b T) :
    ∀ᵐ p ∂T, CascadeSeedRegular n (fun j => b (j+1)) p.2.2 := by
  have h := hT.2.2.2
  rwa [cascadeSeedRegular_sigma hT] at h

lemma cascadeSeedRegular_total {n : ℕ} {b : ℕ → ℝ} {T : NoiseTree unitInterval (n+1)}
    (hT : CascadeSeedRegular (n+1) b T) :
    0 < noiseTreeTotal unitInterval (n+1) T ∧ noiseTreeTotal unitInterval (n+1) T < ∞ := hT.1

theorem cascadeSeedTree_total {ι : Type} [Fintype ι] (n : ℕ) (b : ℕ → ℝ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i)))
    (T : NoiseTree unitInterval n) (hT : CascadeSeedRegular n b T) (z : ι → ℝ) :
    noiseTreeTotal (ι → ℝ) n (cascadeSeedTree n b ψ z T) = noiseTreeTotal unitInterval n T := by
  induction n generalizing b ψ z with
  | zero => rfl
  | succ n ih =>
    have hmap : Measurable (fun p : ℝ × (unitInterval × NoiseTree unitInterval n) =>
        (p.1,(ψ 0 z p.2.1,cascadeSeedTree n (fun j => b (j+1)) (fun j => ψ (j+1))
          (z+ψ 0 z p.2.1) p.2.2))) := by
      have hm : Measurable (fun p : ℝ × (unitInterval × NoiseTree unitInterval n) => ψ 0 z p.2.1) :=
        (hψ 0).comp (measurable_const.prodMk (measurable_fst.comp measurable_snd))
      exact measurable_fst.prodMk (hm.prodMk
        ((measurable_cascadeSeedTree n _ _ (fun i => hψ (i+1))).comp
          ((measurable_const.add hm).prodMk (by fun_prop))))
    rw [cascadeSeedTree, cascadeSeedRegular_sigma hT, noiseTreeTotal_succ, noiseTreeTotal_succ]
    rw [lintegral_map (show Measurable (fun p : ℝ × ((ι → ℝ) × NoiseTree (ι → ℝ) n) =>
      ENNReal.ofReal (max p.1 0) * noiseTreeTotal (ι → ℝ) n p.2.2) from
        (by fun_prop : Measurable (fun p : ℝ × ((ι → ℝ) × NoiseTree (ι → ℝ) n) =>
          ENNReal.ofReal (max p.1 0))).mul ((measurable_noiseTreeTotal (ι → ℝ) n).comp
            (measurable_snd.comp measurable_snd))) hmap]
    apply lintegral_congr_ae
    filter_upwards [cascadeSeedRegular_tail hT] with p hp
    rw [ih _ _ (fun i => hψ (i+1)) _ hp]

end InvariantIsing

end

end OAI
