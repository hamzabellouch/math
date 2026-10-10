import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorForceSupport
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarProcessorMain

namespace OAI

/-! The detector force stays in one compact horizontal subset of the
processor chart. Continuity supplies the boundary faces of the unit cell. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set Filter
open scoped ContDiff Topology

def openUnitPlane : Set Plane := Set.pi univ (fun _ => Ioo (0 : ℝ) 1)

theorem mem_openUnitPlane {x : Plane} :
    x ∈ openUnitPlane ↔ ∀ j, 0 < x j ∧ x j < 1 := by
  simp only [openUnitPlane, Set.mem_pi, mem_univ, true_implies, mem_Ioo]

theorem openUnitPlane_open : IsOpen openUnitPlane :=
  isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)

theorem threeAtLeastTwo : Nat.AtLeastTwo 3 := ⟨Nat.le_succ 2⟩

def injectionSupport : Set Plane :=
  letI := ShearFlows.sixteenAtLeastTwo
  letI := ShearFlows.fiveAtLeastTwo
  letI := threeAtLeastTwo
  Icc (fun _ => (3 / 16 : ℝ)) (fun _ => (5 / 16 : ℝ))

theorem injectionSupport_inside : injectionSupport ⊆ openUnitPlane := by
  intro x hx
  apply mem_openUnitPlane.mpr
  intro j
  have hj : (3 / 16 : ℝ) ≤ x j ∧ x j ≤ 5 / 16 := ⟨hx.1 j, hx.2 j⟩
  constructor <;> linarith only [hj.1, hj.2]

theorem continuous_zero_on_unit_faces {f : Plane → Space} (hf : Continuous f)
    {K : Set Plane} (hK : IsClosed K)
    (hz : ∀ x ∈ openUnitPlane, x ∉ K → f x = 0)
    {x : Plane} (hx : ∀ j, x j ∈ Icc (0 : ℝ) 1) (hxK : x ∉ K) : f x = 0 := by
  have hxcl : x ∈ closure openUnitPlane := by
    apply mem_closure_pi.mpr
    intro j _
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact hx j
  have hxc : x ∈ closure (openUnitPlane ∩ Kᶜ) := hK.isOpen_compl.closure_inter ⟨hxcl, hxK⟩
  have he : EqOn f (fun _ => 0) (openUnitPlane ∩ Kᶜ) := fun y hy => hz y hy.1 hy.2
  exact he.closure hf continuous_const hxc

theorem detectorForce_fixed_horizontal_support {V : ℝ → Plane → Plane}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) {K : Set Plane}
    (hK : IsCompact K) (hKi : K ⊆ openUnitPlane)
    (hVz : ∀ s x, x ∈ openUnitPlane → x ∉ K → V s x = 0)
    (C L : ℕ) :
    IsCompact (K ∪ injectionSupport) ∧ (K ∪ injectionSupport) ⊆ openUnitPlane ∧
      ∀ t x, (∀ j, x j ∈ Icc (0 : ℝ) 1) → x ∉ K ∪ injectionSupport →
        ∀ z, detectorForce V C L (t, atHeight x z) = 0 := by
  have hK' : IsCompact (K ∪ injectionSupport) := hK.union isCompact_Icc
  refine ⟨hK', union_subset hKi injectionSupport_inside, ?_⟩
  intro t x hx hxK z
  have hi : Continuous (fun y : Plane => atHeight y z) := by
    apply continuous_pi
    intro j
    fin_cases j
    · exact continuous_apply 0
    · exact continuous_apply 1
    · exact continuous_const
  have hf : Continuous (fun y : Plane => detectorForce V C L (t, atHeight y z)) :=
    (triangularForce_smooth (detectorDrift_smooth hV C L) (detectorSource_smooth C L) 1).continuous.comp
      (continuous_const.prodMk hi)
  apply continuous_zero_on_unit_faces hf hK'.isClosed _ hx hxK
  intro y hy hyK
  let U := openUnitPlane ∩ (K ∪ injectionSupport)ᶜ
  have hU : IsOpen U := openUnitPlane_open.inter hK'.isClosed.isOpen_compl
  have hproc (s : ℝ) (q : Plane) (hq : q ∈ U) : V s q = 0 :=
    hVz s q hq.1 (fun h => hq.2 (Or.inl h))
  have hb (n : ℕ) (q : Plane) (hq : q ∈ U) : detectorBump (width L n : ℝ) q = 0 := by
    by_contra hn
    have hw : (0 : ℝ) < width L n := by exact_mod_cast width_pos L n
    have hq₁ : ∀ j, q j ∈ Icc (0 : ℝ) 1 := fun j =>
      ⟨(mem_openUnitPlane.mp hq.1 j).1.le, (mem_openUnitPlane.mp hq.1 j).2.le⟩
    have hb := detectorBump_support_in_chart hw (detector_width_small L n) hq₁ hn
    have hD : q ∈ injectionSupport := by
      constructor <;> intro j
      · have hh := (abs_lt.mp (hb j)).1
        have hs := detector_width_small L n
        linarith only [hh, hs]
      · have hh := (abs_lt.mp (hb j)).2
        have hs := detector_width_small L n
        linarith only [hh, hs]
    exact hq.2 (Or.inr hD)
  apply detectorForce_zero_of_neighborhood hV C L hU hproc hb t
  simpa only [U, horizontalLinear_eq, atHeight_horizontal, mem_inter_iff, mem_compl_iff]
    using And.intro hy hyK

theorem processor_detector_force_support (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Ω Ψ : ℝ → ℝ → Plane → Plane}
    (hP : Recorder.Planar.ProcessorProperties I hI Ω Ψ) (C L : ℕ) :
    let K := PlanarHamiltonian.commonSupport (Recorder.Planar.normalizedPulse I hI) ∪ injectionSupport
    IsCompact K ∧ K ⊆ openUnitPlane ∧
      ∀ t x, (∀ j, x j ∈ Icc (0 : ℝ) 1) → x ∉ K → ∀ z,
        detectorForce (planarSlice (Recorder.Planar.normalizedHamiltonian I hI)) C L
          (t, atHeight x z) = 0 := by
  apply detectorForce_fixed_horizontal_support
    (V := planarSlice (Recorder.Planar.normalizedHamiltonian I hI))
    hP.torus_smooth hP.compact_support.1
    (fun x hx => mem_openUnitPlane.mpr (hP.compact_support.2.1 hx)) _ C L
  intro s x hx hxK
  rw [← hP.chart_agreement s x (mem_openUnitPlane.mp hx)]
  exact image_eq_zero_of_notMem_tsupport (fun h => hxK ((hP.compact_support.2.2 s).1 h))

end ForcedComputation.VelocityDetector

end

end OAI
