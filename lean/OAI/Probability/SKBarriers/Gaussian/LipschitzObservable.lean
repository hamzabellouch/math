import Mathlib
import OAI.Probability.SKBarriers.Gaussian.SmoothedObservable

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem dyadicScalarAverage_tendsto_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    {K B L : ℝ≥0} (hfK : LipschitzWith K f) (hgL : LipschitzWith L g)
    (hB : ∀ z, |g z| ≤ B) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    Tendsto (fun n => dyadicScalarAverage β α n s t f g x) atTop
      (𝓝 (scalarCDFAverage β α s t f g x)) := by
  apply CauchySeq.tendsto_limUnder
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let h := ε/(4*((L:ℝ)+1))
  have hL : 0<(L:ℝ)+1 := by positivity
  have hh : 0<h := div_pos hε (mul_pos (by norm_num) hL)
  have hsmall : (L:ℝ)*h ≤ ε/4 := by
    calc
      _ ≤ ((L:ℝ)+1)*h := mul_le_mul_of_nonneg_right (by linarith) hh.le
      _ = ε/4 := by dsimp [h]; field_simp
  let C : ℝ≥0 := ⟨2*(B:ℝ)/h,div_nonneg (by positivity) hh.le⟩
  have hW := dyadicScalarAverage_tendsto_C1 β hα hmono hf
    (scalarWindow_hasDerivAt hgL.continuous h) (scalarWindowDerivative_continuous hgL.continuous h)
    hfK (scalarWindow_bound hgL.continuous hB hh) (C:=C)
    (scalarWindowDerivative_bound hB hh) s t ht x
  have hc := Metric.cauchySeq_iff.mp hW.cauchySeq (ε/4) (by positivity)
  obtain ⟨N,hN⟩ := hc
  refine ⟨N,fun m hm n hn => ?_⟩
  have he (j : ℕ) : |dyadicScalarAverage β α j s t f g x-
      dyadicScalarAverage β α j s t f (scalarWindow g h) x| ≤ ε/4 := by
    apply (scalarHierarchyAverage_observable_distance hf
      ⟨hgL.continuous,B,B.coe_nonneg,hB⟩
      ⟨continuous_iff_continuousAt.mpr (fun z => (scalarWindow_hasDerivAt hgL.continuous h z).continuousAt),
        B,B.coe_nonneg,scalarWindow_bound hgL.continuous hB hh⟩
      (mul_nonneg L.coe_nonneg hh.le) (fun z => ?_) _ _ _ x).trans hsmall
    rw [abs_sub_comm]
    exact scalarWindow_approx hgL hh z
  have hd := hN m hm n hn
  simp only [Real.dist_eq] at hd ⊢
  have H₁ := abs_sub_le (dyadicScalarAverage β α m s t f g x)
    (dyadicScalarAverage β α m s t f (scalarWindow g h) x)
    (dyadicScalarAverage β α n s t f g x)
  have H₂ := abs_sub_le (dyadicScalarAverage β α m s t f (scalarWindow g h) x)
    (dyadicScalarAverage β α n s t f (scalarWindow g h) x)
    (dyadicScalarAverage β α n s t f g x)
  rw [abs_sub_comm (dyadicScalarAverage β α n s t f (scalarWindow g h) x)] at H₂
  linarith [he m,he n]

theorem scalarCDFAverage_observable_distance (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    {f g a : ℝ → ℝ} (hf : BoundedDerivs f)
    {K B C L M : ℝ≥0} (hfK : LipschitzWith K f)
    (hgL : LipschitzWith L g) (haM : LipschitzWith M a)
    (hB : ∀ z, |g z| ≤ B) (hC : ∀ z, |a z| ≤ C)
    {δ : ℝ} (hδ : 0≤δ) (hga : ∀ z, |g z-a z| ≤ δ)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (x : ℝ) :
    |scalarCDFAverage β α s t f g x-scalarCDFAverage β α s t f a x| ≤ δ := by
  apply le_of_tendsto ((dyadicScalarAverage_tendsto_lipschitz β hα hmono hf hfK hgL hB s t ht x).sub
    (dyadicScalarAverage_tendsto_lipschitz β hα hmono hf hfK haM hC s t ht x)).abs
  exact Eventually.of_forall (fun n => scalarHierarchyAverage_observable_distance hf
    ⟨hgL.continuous,B,B.coe_nonneg,hB⟩ ⟨haM.continuous,C,C.coe_nonneg,hC⟩ hδ hga _ _ _ x)

end SK.Analytic

end
end

end OAI
