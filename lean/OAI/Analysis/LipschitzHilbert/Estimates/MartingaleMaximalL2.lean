import OAI.Analysis.LipschitzHilbert.Estimates.MaximalL2Energy
import OAI.Analysis.LipschitzHilbert.Estimates.MartingaleLocalMaximal
import Mathlib.MeasureTheory.Function.LpOrder

namespace OAI

/-! Doob's scalar finite-horizon L2 estimate, with its exact factor four,
for the dyadic averages used in the axis-parallel rectangle count. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert

def finiteMaxSignal {Ω : Type*} (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) : ℝ :=
  (Finset.range (N+1)).sup' Finset.nonempty_range_add_one (fun i => |F i x|)

theorem finiteMaxSignal_nonneg {Ω : Type*} (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    0 ≤ finiteMaxSignal F N x := by
  exact (abs_nonneg (F 0 x)).trans (Finset.le_sup' (fun i => |F i x|) (by simp))

theorem finiteMaxSignal_measurable {Ω : Type*} [MeasurableSpace Ω]
    (F : ℕ → Ω → ℝ) (N : ℕ) (hF : ∀ i ≤ N, Measurable (F i)) :
    Measurable (finiteMaxSignal F N) :=
  Finset.measurable_range_sup'' (fun i hi => by
    simpa only [Real.norm_eq_abs] using (hF i hi).norm)

theorem finiteMaxSignal_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : ℕ → Ω → ℝ) (N : ℕ) (hF : ∀ i, MemLp (F i) 2 μ) :
    MemLp (finiteMaxSignal F N) 2 μ := by
  induction N with
  | zero =>
    have heq : finiteMaxSignal F 0 = fun x => |F 0 x| := by
      funext x
      simp [finiteMaxSignal]
    rw [heq]
    simpa only [Real.norm_eq_abs] using (hF 0).norm
  | succ N ih =>
    have heq : finiteMaxSignal F (N+1) = (fun x => |F (N+1) x|) ⊔ finiteMaxSignal F N := by
      funext x
      have hh := Finset.sup'_insert (s := Finset.range (N+1)) (H := Finset.nonempty_range_add_one)
        (b := N+1) (f := fun i => |F i x|)
      simpa only [← Finset.range_add_one, finiteMaxSignal, Pi.sup_apply] using hh
    rw [heq]
    have hn : MemLp (fun x => |F (N+1) x|) 2 μ := by
      simpa only [Real.norm_eq_abs] using (hF (N+1)).norm
    exact hn.sup ih

theorem martingale_maximal_L2 {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m) (F : ℕ → Ω → ℝ)
    (hF : Martingale F ℱ μ) (hF2 : ∀ i, MemLp (F i) 2 μ) (N : ℕ) :
    (∫ x, (finiteMaxSignal F N x)^2 ∂μ) ≤ 4 * ∫ x, (F N x)^2 ∂μ := by
  have hm (i : ℕ) : Measurable (F i) := (hF.stronglyMeasurable i).measurable.le (ℱ.le i)
  have h := maximal_L2_energy μ (finiteMaxSignal F N) (fun x => |F N x|)
    (finiteMaxSignal_measurable F N (fun i _ => hm i)) (by simpa only [Real.norm_eq_abs] using (hm N).norm)
    (finiteMaxSignal_nonneg F N) (fun x => abs_nonneg (F N x))
    (finiteMaxSignal_memLp μ F N hF2) (by simpa only [Real.norm_eq_abs] using (hF2 N).norm) (by
      intro t ht
      let ε : ℝ≥0 := ⟨t,ht.le⟩
      have hw := maximal_ineq (martingale_abs hF) (fun i x => abs_nonneg (F i x))
        (ε := ε) N
      rw [← ofReal_integral_eq_lintegral_ofReal (hF.integrable N).abs.integrableOn
        (Filter.Eventually.of_forall (fun x => abs_nonneg (F N x)))]
      have hc : (ε : ℝ≥0∞) = ENNReal.ofReal t := ENNReal.coe_nnreal_eq ε
      rw [hc] at hw
      exact hw)
  simpa only [sq_abs] using h

end LipschitzHilbert

end

end OAI
