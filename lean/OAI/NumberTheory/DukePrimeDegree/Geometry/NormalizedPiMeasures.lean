import OAI.NumberTheory.PrimePackets.ZeroSeparation

namespace OAI

/-! # Normalization of finite products on rectangles -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable {ι : Type*} [Fintype ι] {A : ι → Type*}
  [∀ i, MeasurableSpace (A i)]

lemma pi_smul_measures (ν : (i : ι) → Measure (A i)) [∀ i, SigmaFinite (ν i)]
    (c : ι → ℝ≥0∞) [∀ i, SigmaFinite (c i • ν i)] :
    Measure.pi (fun i => c i • ν i) = (∏ i, c i) • Measure.pi ν := by
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib]

lemma sigmaFinite_anchorNormalize {B : Type*} [MeasurableSpace B]
    (ν : Measure B) [SigmaFinite ν] (V : Set B) (hV : ν V ≠ 0) :
    SigmaFinite (anchorNormalize ν V) := by
  have h : (((ν V)⁻¹).toNNReal : ℝ≥0∞) = (ν V)⁻¹ :=
    ENNReal.coe_toNNReal (ENNReal.inv_ne_top.mpr hV)
  unfold anchorNormalize
  rw [←h, Measure.coe_nnreal_smul]
  infer_instance

theorem pi_anchorNormalize (ν : (i : ι) → Measure (A i)) [∀ i, SigmaFinite (ν i)]
    (V : (i : ι) → Set (A i)) (h0 : ∀ i, ν i (V i) ≠ 0) :
    Measure.pi (fun i => anchorNormalize (ν i) (V i)) =
      anchorNormalize (Measure.pi ν) (Set.univ.pi V) := by
  let : ∀ i, SigmaFinite ((ν i (V i))⁻¹ • ν i) :=
    fun i => sigmaFinite_anchorNormalize (ν i) (V i) (h0 i)
  unfold anchorNormalize
  rw [pi_smul_measures, Measure.pi_pi,
    ENNReal.prod_inv_distrib (fun i _ _ _ _ => Or.inl (h0 i))]

end DukePrimeDegree

end

end OAI
