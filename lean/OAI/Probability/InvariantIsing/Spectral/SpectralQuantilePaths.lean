import OAI.Probability.InvariantIsing.Spectral.SpectralGGGeometry
import OAI.Probability.InvariantIsing.Core.Variational
import OAI.Probability.IsingPerceptron.OrderedQuantile

namespace OAI

/-! Simultaneous pair quantile laws of the actual spectral GG limits. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Topology

namespace InvariantIsing

def spectralLinearLaw {m : ℕ} (Q : ProbabilityMeasure (SpectralArray m)) (w : Fin m → ℝ) : Measure ℝ :=
  (Q : Measure (SpectralArray m)).map (fun x => spectralLinearArray w x 0 1)

instance spectralLinearLaw_probability {m : ℕ} (Q : ProbabilityMeasure (SpectralArray m))
    (w : Fin m → ℝ) : IsProbabilityMeasure (spectralLinearLaw Q w) :=
  (Measure.isProbabilityMeasure_map_iff
    (by unfold spectralLinearArray spectralLinearEntry; fun_prop :
      Measurable (fun x : SpectralArray m => spectralLinearArray w x 0 1)).aemeasurable).mpr inferInstance

lemma spectralLinearLaw_unit {m : ℕ} (Q : ProbabilityMeasure (SpectralArray m)) (w : Fin m → ℝ)
    (hs : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), spectralLinearArray w x 0 1 ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ y ∂spectralLinearLaw Q w, y ∈ Icc (0 : ℝ) 1 := by
  exact (ae_map_iff (by unfold spectralLinearArray spectralLinearEntry; fun_prop :
    Measurable (fun x : SpectralArray m => spectralLinearArray w x 0 1)).aemeasurable
      measurableSet_Icc).mpr hs

def spectralQuantilePath {m : ℕ} (Q : ProbabilityMeasure (SpectralArray m)) (w : Fin m → ℝ)
    (hs : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), spectralLinearArray w x 0 1 ∈ Icc (0 : ℝ) 1) :
    InvariantIsing.OverlapPath where
  val := quantileFunction (spectralLinearLaw Q w)
  monotone := monotone_quantileFunction (spectralLinearLaw_unit Q w hs)
  nonneg s := (quantileFunction_mem (spectralLinearLaw_unit Q w hs) s).1
  le_one s := (quantileFunction_mem (spectralLinearLaw_unit Q w hs) s).2

lemma spectralQuantilePath_law {m : ℕ} (Q : ProbabilityMeasure (SpectralArray m)) (w : Fin m → ℝ)
    (hs : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), spectralLinearArray w x 0 1 ∈ Icc (0 : ℝ) 1) :
    InvariantIsing.pathMeasure.map (spectralQuantilePath Q w hs) = spectralLinearLaw Q w := by
  exact quantileFunction_law (spectralLinearLaw_unit Q w hs)

/-- All pairs of required nonnegative linear overlap combinations have
simultaneous quantile laws. The total spin combination is included once its
unit bound is derived from the genuine spectral partition. -/
theorem spectralQuantilePath_pair_law {m : ℕ} {Q : ProbabilityMeasure (SpectralArray m)}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray m)))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), SpectralGram x)
    (q : Fin m → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : Equiv.Perm ℕ,
      (Q : Measure (SpectralArray m)).map (permuteSpectralArray e) = Q)
    (w z : Fin m → ℝ) (hw : ∀ a, 0 ≤ w a) (hz : ∀ a, 0 ≤ z a)
    (hws : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), spectralLinearArray w x 0 1 ∈ Icc (0 : ℝ) 1)
    (hzs : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), spectralLinearArray z x 0 1 ∈ Icc (0 : ℝ) 1) :
    InvariantIsing.pathMeasure.map
      (fun s => (spectralQuantilePath Q w hws s, spectralQuantilePath Q z hzs s)) =
      (Q : Measure (SpectralArray m)).map
        (fun x => (spectralLinearArray w x 0 1, spectralLinearArray z x 0 1)) := by
  let F := fun x : SpectralArray m => (spectralLinearArray w x 0 1, spectralLinearArray z x 0 1)
  have hm : Measurable F := by unfold F spectralLinearArray spectralLinearEntry; fun_prop
  let ρ := (Q : Measure (SpectralArray m)).map F
  let : IsProbabilityMeasure ρ := (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  have hs : ∀ᵐ x ∂ρ, x.1 ∈ Icc (0 : ℝ) 1 ∧ x.2 ∈ Icc (0 : ℝ) 1 := by
    apply (ae_map_iff hm.aemeasurable (measurableSet_Icc.prod measurableSet_Icc)).mpr
    filter_upwards [hws, hzs] with x hx hy
    exact ⟨hx, hy⟩
  have hfirst : ρ.map Prod.fst = spectralLinearLaw Q w := by
    dsimp only [ρ]
    rw [Measure.map_map measurable_fst hm]
    rfl
  have hsecond : ρ.map Prod.snd = spectralLinearLaw Q z := by
    dsimp only [ρ]
    rw [Measure.map_map measurable_snd hm]
    rfl
  have he := ordered_pair_quantile_law (spectralGG_support_ordered hgg hG q hq hd hE w z hw hz) hs
  rw [hfirst, hsecond] at he
  exact he

lemma integral_of_pair_law {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (μ : Measure Ω) (ν : Measure T) (f g : Ω → ℝ) (F G : T → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hF : Measurable F) (hG : Measurable G)
    (hl : μ.map (fun x => (f x, g x)) = ν.map (fun x => (F x, G x))) :
    (∫ x, f x * g x ∂μ) = ∫ x, F x * G x ∂ν := by
  have hm : StronglyMeasurable (fun p : ℝ × ℝ => p.1 * p.2) := by fun_prop
  calc
    _ = ∫ p : ℝ × ℝ, p.1 * p.2 ∂μ.map (fun x => (f x, g x)) :=
      (integral_map_of_stronglyMeasurable (hf.prodMk hg) hm).symm
    _ = ∫ p : ℝ × ℝ, p.1 * p.2 ∂ν.map (fun x => (F x, G x)) := by rw [hl]
    _ = _ := integral_map_of_stronglyMeasurable (hF.prodMk hG) hm

end InvariantIsing

end

end OAI
