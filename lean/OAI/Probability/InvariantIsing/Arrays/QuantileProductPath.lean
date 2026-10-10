import OAI.Probability.InvariantIsing.Arrays.QuantileProductKernel
import OAI.Probability.InvariantIsing.Spectral.SpectralSymbols

namespace OAI

/-! The manuscript replica-product path as a proved quantile kernel. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

def replicaProductDiagonal (da db : ℝ) (a b : ℝ → ℝ) : ℝ :=
  da * db - ∫ s, a s * b s ∂pathMeasure

def replicaProductPath (da : ℝ) (a : ℝ → ℝ) (db : ℝ) (b : ℝ → ℝ) (s : ℝ) : ℝ :=
  pathSymbol da a s * b s + a s * pathSymbol db b s + s * (a s * b s) -
    ∫ u in 0..s, a u * b u

theorem replicaProductPath_eq_quantile_kernel (p : OverlapPath) (a b : ℝ → ℝ)
    (ha : Measurable a) (hb : Measurable b) {A B : ℝ} (hA : 0 ≤ A)
    (haB : ∀ x, |a x| ≤ A) (hbB : ∀ x, |b x| ≤ B)
    (da db : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    replicaProductPath da (fun u => a (p u)) db (fun u => b (p u)) s =
      da * b (p s) + a (p s) * db -
        ((∫ u, replicaProductFirst a b (p s) (p u) +
          replicaProductSecond a b (p s) (p u) ∂pathMeasure) + a (p s) * b (p s)) := by
  rw [integral_quantile_product_kernel p a b ha hb hA haB hbB hs]
  unfold replicaProductPath pathSymbol
  ring

lemma integral_pair_quantile_map (ζ : Measure ℝ) [IsProbabilityMeasure ζ] (p : OverlapPath)
    (hl : pathMeasure.map p = ζ) (F : ℝ × ℝ → ℝ) (hF : Measurable F) :
    (∫ x, ∫ y, F (x,y) ∂ζ ∂ζ) = ∫ s, ∫ u, F (p s,p u) ∂pathMeasure ∂pathMeasure := by
  have hm : StronglyMeasurable (fun x => ∫ y, F (x,y) ∂ζ) :=
    hF.stronglyMeasurable.integral_prod_right'
  calc
    _ = ∫ x, ∫ y, F (x,y) ∂ζ ∂pathMeasure.map p := by rw [hl]
    _ = ∫ s, ∫ y, F (p s,y) ∂ζ ∂pathMeasure :=
      integral_map_of_stronglyMeasurable p.measurable hm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun s => by
        rw [← hl]
        exact integral_map_of_stronglyMeasurable p.measurable
          (hF.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable

end InvariantIsing

end

end OAI
