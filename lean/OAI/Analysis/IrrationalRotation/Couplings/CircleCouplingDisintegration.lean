import OAI.Analysis.IrrationalRotation.Couplings.CircleCouplingLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling

lemma initial_disintegration {D : Type*} [MeasurableSpace D]
    (f : CoordinateSample → D) (hf : Measurable f) :
    (initialLaw.map f) ⊗ₘ Kernel.const D (Measure.dirac (none : Label)) =
      initialLaw.map (fun z => (f z, z.1)) := by
  let := initialLaw_isProbabilityMeasure
  rw [Measure.compProd_const, Measure.prod_dirac,
    Measure.map_map (show Measurable (fun d : D => (d, (none : Label))) from by fun_prop) hf]
  simp only [Function.comp_def]
  unfold initialLaw
  have hin : Measurable (fun x : ℝ => ((none : Label), (x, x))) := by fun_prop
  rw [Measure.map_map (show Measurable (fun z : CoordinateSample => (f z, (none : Label))) from by fun_prop) hin,
    Measure.map_map (show Measurable (fun z : CoordinateSample => (f z, z.1)) from by fun_prop) hin]
  rfl

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma posterior_disintegration (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) (i : ℕ) :
    ((coordinateLaw p j i).map (observedDigit p hr side i)) ⊗ₘ posterior p j side i =
      (coordinateLaw p j i).map (fun z => (observedDigit p hr side i z, z.1)) := by
  by_cases hi : i = 0
  · simpa only [coordinateLaw, posterior, ite_eq_left hi] using
      initial_disintegration (observedDigit p hr side i) (measurable_observedDigit hr side i)
  have hs := p.blockIndex_pos hp.m_pos (show 1 ≤ i by omega)
  have hm : (100 : ℝ) ≤ p.m (p.blockIndex i) := by
    exact_mod_cast (show 100 ≤ p.m (p.blockIndex i) by have := hp.m_ge_200 _ hs; omega)
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  have hd := labelsGivenDigit_disintegration hm
    (hp.coupling_a_bounds _ hs).1 (hp.coupling_a_bounds _ hs).2
    (hp.coupling_b_bounds _ hs).1 (hp.coupling_b_bounds _ hs).2
    (CircleParameterLaws.coupling_kappa_bounds _ hs).1
    (CircleParameterLaws.coupling_kappa_bounds _ hs).2
    (tag_bounds j (p.blockIndex i)).1 (tag_bounds j (p.blockIndex i)).2 side (MixedRadix.radices p.q i)
  have ho : observedDigit p hr side i = (fun z =>
      UniformQuantization.quantize (MixedRadix.radices p.q i) (endpoint side z)) := rfl
  rw [digitJoint,
    Measure.fst_map_prodMk (ho ▸ measurable_observedDigit hr side i) measurable_fst] at hd
  simpa only [coordinateLaw, posterior, ite_eq_right hi, ho, digitJoint] using hd

end Invariant233.CircleCoupling

end

end OAI
