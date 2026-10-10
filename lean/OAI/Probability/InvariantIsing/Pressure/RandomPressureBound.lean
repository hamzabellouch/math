import OAI.Probability.InvariantIsing.Pressure.RandomOrbitSupport
import OAI.Probability.InvariantIsing.Pressure.RandomSpectralMeasurability
import OAI.Probability.InvariantIsing.Pressure.RandomUniformIntegrability

namespace OAI

/-! The operator-norm sufficient condition for uniform integrability of the
actual random pressure under its conditional orbit law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace InvariantIsing

lemma ConditionalFieldOrbitLaw.zero_field_bound {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (eig : Ω → Fin (n+1) → ℝ) (Y : Ω → ℝ)
    (heig : Measurable eig) (hY : Measurable Y)
    (H : Measure (Orthogonal (n+1))) [SFinite H]
    (hlaw : ConditionalFieldOrbitLaw P (fun ω => (eig ω,fun _ => 0)) Y H) :
    ∀ᵐ ω ∂P, |Y ω| ≤ spectralRadius (eig ω)/2 := by
  let Q := fun z : FieldSpectralData (n+1) × ℝ =>
    z.1.2 ≠ (fun _ => 0) ∨ |z.2| ≤ spectralRadius z.1.1/2
  have hQ : MeasurableSet {z | Q z} :=
    (measurableSet_eq_fun (measurable_snd.comp measurable_fst) measurable_const).compl.union
      (measurableSet_le measurable_snd.abs
        ((measurable_spectralRadius (fun z : FieldSpectralData (n+1) × ℝ => z.1.1)
          (measurable_fst.comp measurable_fst)).div_const 2))
  have hB (data : FieldSpectralData (n+1)) (U : Orthogonal (n+1)) :
      Q (data,dataPhysicalPressure data U) := by
    by_cases hc : data.2=(fun _ => 0)
    · right
      dsimp only [dataPhysicalPressure]
      rw [hc]
      have hh := abs_rotatedPressure_sub_le (Nat.succ_pos n) data.1 (fun _ => 0)
        (matrixRotation U⁻¹) (fun _ => 0) (spectralRadius data.1)
        (fun i => by simpa only [sub_zero] using abs_le_spectralRadius data.1 i)
      simpa only [rotatedPressure_constant (Nat.succ_pos n),zero_div,sub_zero] using hh
    · exact Or.inl hc
  have hh := hlaw.ae_property (Nat.succ_pos n) P _ Y (heig.prodMk measurable_const)
    hY H Q hQ hB
  simpa only [Q,ne_eq,not_true_eq_false,false_or] using hh

theorem random_pressure_uniformIntegrable_of_spectralRadius
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (eig : (N : ℕ) → Ω → Fin N → ℝ) (Y : ℕ → Ω → ℝ)
    (heig : ∀ N, Measurable (eig N)) (hY : ∀ N, Measurable (Y N))
    (H : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (H N)]
    (hlaw : ∀ N, ConditionalFieldOrbitLaw P (fun ω => (eig N ω,fun _ => 0)) (Y N) (H N))
    (hUI : UniformIntegrable (fun k ω => spectralRadius (eig (k+1) ω)) 1 P) :
    UniformIntegrable (fun k => Y (k+1)) 1 P := by
  apply uniformIntegrable_of_abs_le P _ _ (fun k => (hY (k+1)).aestronglyMeasurable) hUI
  intro k
  filter_upwards [(hlaw (k+1)).zero_field_bound P (eig (k+1)) (Y (k+1))
    (heig (k+1)) (hY (k+1)) (H (k+1))] with ω hω
  have hR : 0 ≤ spectralRadius (eig (k+1) ω) :=
    (abs_nonneg (eig (k+1) ω 0)).trans (abs_le_spectralRadius (eig (k+1) ω) 0)
  exact hω.trans ((half_le_self hR).trans (le_abs_self _))

end InvariantIsing

end

end OAI
