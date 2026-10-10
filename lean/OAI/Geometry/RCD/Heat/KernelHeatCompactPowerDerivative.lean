import OAI.Geometry.RCD.Heat.CompactProductPowerDerivative
import OAI.Geometry.RCD.Heat.KernelHeatBackwardContinuity
import OAI.Geometry.RCD.Heat.KernelHeatProductDerivative

namespace OAI

/-! # Exact localized power derivatives of the heat bridge -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular]
  (Q : QuadraticCheegerEnergy μ) {ker : ℝ → X → X → ℝ}
  (hk : IsContinuousHeatKernel μ Q ker)

theorem kernelHeat_compact_power_hasDerivAt (f g : Lp ℝ 2 μ)
    {T t : ℝ} (ht : 0 < t) (htT : t < T) {Ω : Set X} (hΩ : IsCompact Ω) (q : ℕ) :
    HasDerivAt
      (fun s => ∫ x in Ω, (kernelHeat μ Q hk s f x*kernelHeat μ Q hk (T-s) g x)^q ∂μ)
      ((q:ℝ)*(∫ x in Ω,
        (kernelHeat μ Q hk t f x*kernelHeat μ Q hk (T-t) g x)^(q-1)*
          (kernelHeatGeneratorSource μ Q hk t f x*kernelHeat μ Q hk (T-t) g x-
            kernelHeat μ Q hk t f x*kernelHeatGeneratorSource μ Q hk (T-t) g x) ∂μ)) t := by
  let a := t/2
  let b := (t+T)/2
  have ha : 0 < a := half_pos ht
  have hb : b < T := by dsimp only [b]; linarith
  have htab : t ∈ Ioo a b := by dsimp only [a,b]; constructor <;> linarith
  let U := fun sx : ℝ × X => kernelHeat μ Q hk sx.1 f sx.2
  let V := fun sx : ℝ × X => kernelHeat μ Q hk (T-sx.1) g sx.2
  let DU := fun sx : ℝ × X => kernelHeatGeneratorSource μ Q hk sx.1 f sx.2
  let DV := fun sx : ℝ × X => kernelHeatGeneratorSource μ Q hk (T-sx.1) g sx.2
  have hsub : Icc a b ×ˢ Ω ⊆ Ioi (0:ℝ) ×ˢ (univ : Set X) :=
    fun sx hsx => ⟨ha.trans_le hsx.1.1,mem_univ _⟩
  have hsubB : Icc a b ×ˢ Ω ⊆ Iio T ×ˢ (univ : Set X) :=
    fun sx hsx => ⟨lt_of_le_of_lt hsx.1.2 hb,mem_univ _⟩
  have hu : ContinuousOn U (Icc a b ×ˢ Ω) :=
    (kernelHeat_continuousOn_time_space μ Q hk f).mono hsub
  have hv : ContinuousOn V (Icc a b ×ˢ Ω) :=
    (kernelHeat_backward_continuousOn μ Q hk g T).mono hsubB
  have hdu : ContinuousOn DU (Icc a b ×ˢ Ω) :=
    (kernelHeatGeneratorSource_continuousOn_time_space μ Q hk f).mono hsub
  have hdv : ContinuousOn DV (Icc a b ×ˢ Ω) :=
    (kernelHeatGeneratorSource_backward_continuousOn μ Q hk g T).mono hsubB
  have hd := compact_product_power_hasDerivAt (μ := μ) htab hΩ
    (fun s x => U (s,x)) (fun s x => V (s,x))
    (fun s x => DU (s,x)) (fun s x => -DV (s,x)) hu hv hdu hdv.neg
    (by
      intro s hs x _
      exact kernelHeat_generator_hasDerivAt μ Q hk f (ha.trans hs.1) x)
    (by
      intro s hs x _
      have hh := (kernelHeat_generator_hasDerivAt μ Q hk g
        (sub_pos.mpr (hs.2.trans hb)) x).scomp s
        ((hasDerivAt_const s T).sub (hasDerivAt_id s))
      simpa only [Function.comp_def,zero_sub,neg_smul,one_smul] using hh) q
  simpa only [U,V,DU,DV,mul_neg,← sub_eq_add_neg] using hd

end RegularPointCoordinates

end

end OAI
