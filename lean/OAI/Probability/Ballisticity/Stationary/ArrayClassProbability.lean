import Mathlib
import OAI.Probability.Ballisticity.Walk.ArrayGrowthEvent
import OAI.Probability.Ballisticity.Entropy.EntropyEvent
import OAI.Probability.Ballisticity.Stationary.ArrayMassSurvival
import OAI.Probability.Ballisticity.Estimates.EventRate

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience
namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

lemma class_selection_probability (L : StationaryArrayLaw ν e)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e)))
    {lam : ℝ} (hlam : 0<lam) (hmean : (∫⁻ ξ, upperNoDrop e ξ ^ (-lam) ∂Measure.infinitePi
      (fun _ : ℕ×HorizontalSpace e => ν))<⊤) (n : ℕ) (hn : 0<n) (r : ℝ) (hr : 0<r) :
    (L.law : Measure (ActualEpisodeArray e)).real
      (G.event ∩ {Y | ∃ a, CurrentClassSelection e n r (arrayCurrentData e 0 Y) a}) ≤
      max L.entropyConstant 0 / ((n:ℝ)*lam*G.ζ/2) := by
  let μ := (L.law : Measure (ActualEpisodeArray e))
  let a : ℝ := (n:ℝ)*lam*G.ζ/2
  have ha : 0<a := div_pos (mul_pos (mul_pos (Nat.cast_pos.mpr hn) hlam) G.positive_ζ) (by norm_num)
  let M := (∫⁻ ξ, upperNoDrop e ξ ^ (-lam) ∂Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν))^n
  have hM : M≠⊤ := ENNReal.pow_ne_top hmean.ne
  let B : ℕ → Set (ActualEpisodeArray e) := fun k => {Y |
    ENNReal.ofReal (Real.exp (a*(G.sequence k:ℝ)))≤ selectedClassProduct e n r lam
      (typedCurrentArrayWindow e 0 (G.sequence k) Y)}
  have hB (k : ℕ) : MeasurableSet (B k) := measurableSet_le measurable_const
    ((selectedClassProduct_measurable e n r lam).comp (typedCurrentArrayWindow_measurable e 0 _))
  have hbound (k : ℕ) : μ.real (B k)*(a*(G.sequence k:ℝ))≤
      max L.entropyConstant 0*(G.sequence k:ℝ)+M.toReal := by
    let F := typedCurrentArrayWindow e 0 (G.sequence k)
    let W := μ.map F
    have hmF : Measurable F := typedCurrentArrayWindow_measurable e 0 _
    have : IsProbabilityMeasure W :=
      (Measure.isProbabilityMeasure_map_iff hmF.aemeasurable).mpr inferInstance
    have he : klDiv W (W.fst.compProd (currentWindowReference e ν))≤
        ENNReal.ofReal (max L.entropyConstant 0*(G.sequence k:ℝ)) := by
      apply (L.entropy 0 (G.sequence k)).trans
      apply ENNReal.ofReal_le_ofReal
      nlinarith [le_max_left L.entropyConstant 0,show (0:ℝ)≤(G.sequence k:ℝ) from Nat.cast_nonneg _]
    have hh := Entropy.event_moment_budget W (W.fst.compProd (currentWindowReference e ν))
      (mul_nonneg (le_max_right _ _) (Nat.cast_nonneg _)) he _ (selectedClassProduct_measurable e n r lam) hM
      (selectedClassProduct_lintegral e ν W.fst n r lam) (a*(G.sequence k:ℝ))
    change ((μ.map F) {w | ENNReal.ofReal (Real.exp (a*(G.sequence k:ℝ)))≤ selectedClassProduct e n r lam w}).toReal * _ ≤ _ at hh
    rw [Measure.map_apply hmF (measurableSet_le measurable_const
      (selectedClassProduct_measurable e n r lam))] at hh
    exact hh
  apply event_rate μ _ (G.measurable_event.inter
    ((current_selection_event_measurable e n r).preimage (arrayCurrentData_measurable e 0))) B hB
      G.sequence G.strictMono.tendsto_atTop ha (le_max_right _ _) hbound
  have hq := array_dust_reference_facts e ν htrans μ L.consistent L.zero_sampling L.entropy_finite
  have hexp : ∀ᶠ k in atTop, Real.exp (-(G.ζ*(G.sequence k:ℝ)/2))≤r := by
    have ht : Tendsto (fun k => G.ζ*(G.sequence k:ℝ)/2) atTop atTop := by
      have hh := (tendsto_natCast_atTop_atTop.comp G.strictMono.tendsto_atTop).const_mul_atTop G.positive_ζ
      exact Tendsto.atTop_div_const (by norm_num) hh
    exact (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).eventually (ge_mem_nhds hr)
  filter_upwards [L.consistent,L.continuation,L.finite_marks,hq,G.growth] with Y hP hc hf hq hg hY
  filter_upwards [hg hY.1,hexp] with k hk hkr
  have hHfin : arrayWindowHeight e 0 (G.sequence k) Y≠⊤ :=
    ENat.sum_ne_top.mpr fun j _ => (hf (0+j)).2.1.ne
  have hcfin : arrayWindowCost e 0 (G.sequence k) Y≠⊤ :=
    ENNReal.sum_ne_top.mpr fun j _ => (hf (0+j)).2.2.2.ne
  have hh := array_selectedProduct_lower e Y hP.2 hc 0 (G.sequence k)
    (arrayWindowHeight e 0 (G.sequence k) Y).toNat n (ENat.natCast_toNat hHfin).symm hcfin
    (fun a => (hq 0 (G.sequence k)).2 a _) hr hlam.le (by linarith) hkr hY.2
  change ENNReal.ofReal (Real.exp (a*(G.sequence k:ℝ)))≤_
  convert hh using 1
  congr 2
  unfold a
  ring

end StationaryArrayLaw
end DirectionalTransience

end

end OAI
