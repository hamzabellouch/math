import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorBump

namespace OAI

/-! A height-one injection has mass at most the area of its support square. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set MeasureTheory

theorem detectorBump_mass {b : ℝ} (hb : 0 < b) (hb₁ : b ≤ 1 / 16) :
    0 ≤ (∫ x in Icc (0 : Plane) (fun _ => 1), detectorBump b x) ∧
    (∫ x in Icc (0 : Plane) (fun _ => 1), detectorBump b x) ≤ 4 * b ^ 2 := by
  let K : Set Plane := Icc 0 (fun _ => 1)
  let S : Set Plane := Icc (fun _ => 1 / 4 - b) (fun _ => 1 / 4 + b)
  have hsub : S ⊆ K := by
    intro x hx
    constructor <;> intro j
    · have hj := hx.1 j
      dsimp at hj ⊢
      linarith
    · have hj := hx.2 j
      dsimp at hj ⊢
      linarith
  have hpoint (x : Plane) (hx : x ∈ K) :
      detectorBump b x ≤ S.indicator (fun _ => (1 : ℝ)) x := by
    by_cases hs : x ∈ S
    · rw [indicator_of_mem hs]
      exact (detectorBump_range hb hb₁ x).2
    · rw [indicator_of_notMem hs]
      have hz : detectorBump b x = 0 := by
        by_contra hn
        have hc := detectorBump_support_in_chart hb hb₁
          (fun j => ⟨hx.1 j, hx.2 j⟩) hn
        apply hs
        constructor <;> intro j
        · have hh := (abs_lt.mp (hc j)).1
          dsimp
          linarith
        · have hh := (abs_lt.mp (hc j)).2
          dsimp
          linarith
      exact hz.le
  constructor
  · exact integral_nonneg (fun x => (detectorBump_range hb hb₁ x).1)
  · have hi : IntegrableOn (detectorBump b) K :=
      (detectorBump_smooth hb).continuous.integrableOn_Icc
    have hconst : IntegrableOn (fun _ : Plane => (1 : ℝ)) K :=
      integrableOn_const isCompact_Icc.measure_lt_top.ne
    calc
      _ ≤ ∫ x in K, S.indicator (fun _ => (1 : ℝ)) x :=
        setIntegral_mono_on hi (hconst.indicator measurableSet_Icc)
          measurableSet_Icc hpoint
      _ = ∫ _x in S, (1 : ℝ) := by
        rw [setIntegral_indicator measurableSet_Icc, inter_eq_right.mpr hsub]
      _ = 4 * b ^ 2 := by
        rw [setIntegral_const]
        simp only [Measure.real, smul_eq_mul, mul_one]
        rw [Real.volume_Icc_pi_toReal (fun _ => by dsimp; linarith)]
        simp only [Fin.prod_univ_two]
        ring

end ForcedComputation.VelocityDetector

end

end OAI
