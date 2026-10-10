import Mathlib
import OAI.Probability.Ballisticity.Entropy.OutwardOrder

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma bounded_probability_error_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : Ω → ℝ) (hm : Measurable h)
    {C ε : ℝ} (hε : 0 ≤ ε) (hb : ∀ ω, 0 ≤ h ω ∧ h ω ≤ C) :
    (∫ ω, h ω ∂μ) ≤ ε+C*μ.real {ω | ε < h ω} := by
  let E := {ω | ε < h ω}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hm
  have hg : Integrable (fun ω => ε+E.indicator (fun _ => C) ω) μ :=
    (integrable_const _).add ((integrable_const _).indicator hE)
  have hh : ∀ ω, h ω ≤ ε+E.indicator (fun _ => C) ω := by
    intro ω
    by_cases he : ω ∈ E
    · rw [Set.indicator_of_mem he]
      exact (hb ω).2.trans (by linarith)
    · rw [Set.indicator_of_notMem he,add_zero]
      exact le_of_not_gt he
  have hi : Integrable h μ := hg.mono_nonneg hm.aestronglyMeasurable
    (Eventually.of_forall fun ω => (hb ω).1) (Eventually.of_forall hh)
  have hle := integral_mono_ae hi hg (Eventually.of_forall hh)
  rw [integral_add (integrable_const _) ((integrable_const _).indicator hE),
    integral_const,integral_indicator_const _ hE] at hle
  simpa only [probReal_univ,smul_eq_mul,one_mul,mul_one,mul_comm] using hle

lemma outward_cap_locality_L1 {d : ℕ}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (e f : Direction d) (A : ℝ)
    (hloc : ∀ C ε δ : ℝ, 0 < C → 0 < ε → 0 < δ → ∃ R : ℕ,
      ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
      ∃ F : Environment d → ℝ,
        @Measurable _ _ (rowSigma (upperPairNeighborhood e a x R)) _ F ∧
        (∀ ω, 0 ≤ F ω ∧ F ω ≤ C) ∧
        (environmentLaw ν).real {ω | ε < |min (outwardCanonicalExcess e f A x ω) C-F ω|} < δ)
    {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
      ∃ F : Environment d → ℝ,
        @Measurable _ _ (rowSigma (upperPairNeighborhood e a x R)) _ F ∧
        (∀ ω, 0 ≤ F ω ∧ F ω ≤ C) ∧
        (∫ ω, |min (outwardCanonicalExcess e f A x ω) C-F ω| ∂environmentLaw ν) < ε := by
  obtain ⟨R,hR⟩ := hloc C (ε/2) (ε/(2*C)) hC (by positivity) (by positivity)
  refine ⟨R,?_⟩
  intro a x hx
  obtain ⟨F,hFm,hFb,hFerr⟩ := hR a x hx
  refine ⟨F,hFm,hFb,?_⟩
  have hFa : Measurable F := hFm.mono (rowSigma_le _) le_rfl
  have hh := bounded_probability_error_integral (environmentLaw ν)
    (fun ω => |min (outwardCanonicalExcess e f A x ω) C-F ω|)
    (((measurable_outwardCanonicalExcess e f A x).min measurable_const).sub hFa).abs
    (show 0 ≤ ε/2 by positivity) (C:=C) (fun ω => by
      refine ⟨abs_nonneg _,abs_le.mpr ⟨?_,?_⟩⟩
      · have hz : 0 ≤ min (outwardCanonicalExcess e f A x ω) C :=
          le_min (canonicalLogExcess_nonneg _ _ ω) hC.le
        linarith [(hFb ω).2]
      · linarith [min_le_right (outwardCanonicalExcess e f A x ω) C,(hFb ω).1])
  have hmul := mul_lt_mul_of_pos_left hFerr hC
  have heq : C*(ε/(2*C)) = ε/2 := by field_simp
  rw [heq] at hmul
  linarith

theorem actual_outward_cap_L1_locality {d : ℕ}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ A : ℝ, 0 < A ∧ ∀ C ε : ℝ, 0 < C → 0 < ε → ∃ R : ℕ,
      ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
      ∃ F : Environment d → ℝ,
        @Measurable _ _ (rowSigma (upperPairNeighborhood e a x R)) _ F ∧
        (∀ ω, 0 ≤ F ω ∧ F ω ≤ C) ∧
        (∫ ω, |min (outwardCanonicalExcess e f A x ω) C-F ω| ∂environmentLaw ν) < ε := by
  obtain ⟨A,c,B,hA,hc,hB,hbound,hloc⟩ := actual_outward_order ν hue e f hef htrans
  exact ⟨A,hA,fun C ε hC hε => outward_cap_locality_L1 ν e f A hloc hC hε⟩
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma outward_order_countable_event {d : ℕ}
    (ν : Measure (Row d)) (e f : Direction d) (A : ℝ)
    (hbound : ∀ (a : ℝ) (x : Lattice d × Lattice d),
      x ∈ PairAtHeight (realPosition (step e)) a →
      ∀ᵐ ω ∂environmentLaw ν, ∀ t : ℕ,
        0 < outwardKernelMass e f (t+1) x ω ∧
        -Real.log (outwardKernelMass e f (t+1) x ω) ≤
          2*A*Real.log ((t:ℝ)+2)+outwardCanonicalExcess e f A x ω) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ x : Lattice d × Lattice d,
      dot (realPosition x.1) (realPosition (step e)) =
        dot (realPosition x.2) (realPosition (step e)) →
      ∀ t : ℕ, 0 < outwardKernelMass e f (t+1) x ω ∧
        -Real.log (outwardKernelMass e f (t+1) x ω) ≤
          2*A*Real.log ((t:ℝ)+2)+outwardCanonicalExcess e f A x ω := by
  apply ae_all_iff.mpr
  intro x
  by_cases hx : dot (realPosition x.1) (realPosition (step e)) =
      dot (realPosition x.2) (realPosition (step e))
  · filter_upwards [hbound (dot (realPosition x.1) (realPosition (step e))) x ⟨rfl,hx.symm⟩] with ω hω
    exact fun _ => hω
  · exact Eventually.of_forall fun _ h => (hx h).elim

theorem actual_outward_all_pairs {d : ℕ}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ A : ℝ, 0 < A ∧
      (∀ᵐ ω ∂environmentLaw ν, ∀ x : Lattice d × Lattice d,
        dot (realPosition x.1) (realPosition (step e)) =
          dot (realPosition x.2) (realPosition (step e)) →
        ∀ t : ℕ, 0 < outwardKernelMass e f (t+1) x ω ∧
          -Real.log (outwardKernelMass e f (t+1) x ω) ≤
            2*A*Real.log ((t:ℝ)+2)+outwardCanonicalExcess e f A x ω) := by
  obtain ⟨A,c,B,hA,hc,hB,hbound,hloc⟩ := actual_outward_order ν hue e f hef htrans
  exact ⟨A,hA,outward_order_countable_event ν e f A (fun a x hx => (hbound a x hx).2.2.2.2)⟩
end DirectionalTransience

end

end

end OAI
