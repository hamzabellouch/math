import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.TripleTimeContinuity
import OAI.Geometry.WeakHessian.LocalBounds.GammaRepresentativePairing

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile195
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.weighted_heat_gamma_continuousOn {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    {f Af ξ Bξ : Lp ℝ 2 (exponentialMeasure m V)}
    (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
    (hξ : (cheeger_closedQuadraticEnergy h).IsFormGenerator ξ Bξ)
    {Cf CAf Cξ : ℝ} (hCf : 0 ≤ Cf) (hCAf : 0 ≤ CAf) (hCξ : 0 ≤ Cξ)
    (hfb : ∀ᵐ x ∂exponentialMeasure m V,|f x| ≤ Cf)
    (hAfb : ∀ᵐ x ∂exponentialMeasure m V,|Af x| ≤ CAf)
    (hξb : ∀ᵐ x ∂exponentialMeasure m V,|ξ x| ≤ Cξ) (T : ℝ) :
    ContinuousOn (fun s => ∫ x,cheegerHeat h s ξ x*
      gamma (exponentialMeasure m V) (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x
        ∂exponentialMeasure m V) (Icc 0 T) := by
  let ν := exponentialMeasure m V
  let Q := cheeger_closedQuadraticEnergy h
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hBV
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal) hν
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hnpar := (hrcd.1.global_localGradientParallelogram hfin o hrcd.2).change_measure
    (C := (Real.exp BV).toNNReal) (D := (Real.exp BV).toNNReal) hm hν
  have hgen {u A : Lp ℝ 2 ν} (hu : Q.IsFormGenerator u A) (s : ℝ) :
      IsLaplacian ν (cheegerHeat h s u) (cheegerHeat h s A) :=
    (hrcd.weighted_formGenerator_iff hfin o hBV h _ _).mpr (Q.formGenerator_heat ν hu s)
  have hb (v : Lp ℝ 2 ν) : ContinuousOn (fun s => cheegerHeat h (T-s) v) (Icc 0 T) :=
    (cheegerHeat_continuousOn hnfin h v).comp (continuous_const.sub continuous_id).continuousOn
      (fun _ hs => sub_nonneg.mpr hs.2)
  have hp (v : Lp ℝ 2 ν) : ContinuousOn (fun s => cheegerHeat h s v) (Icc 0 T) :=
    (cheegerHeat_continuousOn hnfin h v).mono Icc_subset_Ici_self
  obtain ⟨n,hn⟩ := exists_nat_ge (max Cf CAf)
  have hn1 : Cf ≤ (n:ℝ) := (le_max_left _ _).trans hn
  have hn2 : CAf ≤ (n:ℝ) := (le_max_right _ _).trans hn
  have hbf : ∀ s ∈ Icc (0:ℝ) T,∀ᵐ x ∂ν,|cheegerHeat h (T-s) f x| ≤ (n:ℝ) :=
    fun s hs => (cheegerHeat_bounded h (sub_nonneg.mpr hs.2) hCf f hfb).mono fun _ hx => hx.trans hn1
  have hbAf : ∀ s ∈ Icc (0:ℝ) T,∀ᵐ x ∂ν,|cheegerHeat h (T-s) Af x| ≤ (n:ℝ) :=
    fun s hs => (cheegerHeat_bounded h (sub_nonneg.mpr hs.2) hCAf Af hAfb).mono fun _ hx => hx.trans hn2
  have hc := ((continuousOn_integral_square_mul (hb f) (hp Bξ) n hbf).const_mul (1/2:ℝ)).sub
    (continuousOn_integral_mul_mul (hb f) (hb Af) (hp ξ) n hbf hbAf)
  apply hc.congr
  intro s hs
  exact ((hgen hf (T-s)).square_gamma_pairing_ae hnfin hnpar (hgen hξ s)
    (hrcd.weighted_heat_boundedLipschitzRepresentative hN hfull hfin o hV hBV h hf hCf hCAf hfb hAfb
      (sub_nonneg.mpr hs.2)) (cheegerHeat_bounded h hs.1 hCξ ξ hξb))
end WeakHessian

end
end InlinedFile195

end OAI
