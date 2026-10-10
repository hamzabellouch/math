import OAI.Analysis.LipschitzHilbert.Trees.SourcePolarizedCoefficient
import OAI.Analysis.LipschitzHilbert.Trees.SourceFourPolarizedConcentration
import OAI.Analysis.LipschitzHilbert.Estimates.IntervalPolarization

namespace OAI

/-! Exact cross-profile source intervals and their four self-family
representation. Every coefficient is the original selected integral. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (alt : ∀ j, ι j → κ → SchwartzMap (ℝ × ℝ) ℂ)
  (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2 * P.order) ≤ P.profileBound)

theorem family_mainCoefficient_physical_zero (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (g : ℝ × ℝ → EuclideanSpace ℂ κ) (j : Fin N) (u : ι j) :
    P.family.mainCoefficient d v g j u =
      P.physicalCoefficient 0 d (fun z => v (z.2, z.1)) (fun z => g (z.2, z.1)) j u := by
  simpa only [sourceReferenceToPhysical_apply, zero_mul, add_zero] using
    P.family_mainCoefficient_physical 0 d (fun z => v (z.2, z.1))
      (fun z => g (z.2, z.1)) j u

theorem polarize_mainCoefficient (c : ℂ) (hc : ‖c‖ = 1)
    (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (u : ι j) :
    (P.polarize alt hAlt c hc).family.mainCoefficient d v g j u =
      P.family.mainCoefficient d v g j u +
        conj c • (P.withProfile alt hAlt).family.mainCoefficient d v g j u := by
  rw [family_mainCoefficient_physical_zero, family_mainCoefficient_physical_zero,
    family_mainCoefficient_physical_zero]
  exact P.polarize_physicalCoefficient alt hAlt c hc 0 d
    (fun z => v (z.2, z.1)) (hv.comp measurable_swap)
    (fun z => g (z.2, z.1)) (hg.comp measurable_swap) (fun z => hg1 (z.2, z.1)) j u

def rawInterval (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (i : Fin 3) (lower upper : ℕ) (x y : ℝ) : EuclideanSpace ℂ κ :=
  planarPacketInterval coeff (fun j u k t s => P.raw i j u k t s) lower upper x y

theorem rawInterval_scaled_covariant (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (lower upper : ℕ) (x y : ℝ) :
    P.scale • covariantSignal P.frequency
        (fun k t => P.rawInterval coeff 0 lower upper x t k) y =
      P.rawInterval coeff 1 lower upper x y := by
  apply planarPacketInterval_scaled_covariant_eq
  · intro j u k t
    exact modulatedPlanarJet_differentiable (P.profile j u k) (P.actualX j u)
      (P.actualZ j u) (P.length j) P.width (-P.rowSlope j) (P.frequency k)
      P.scale t (P.length_pos j).ne' 0 x
  · intro j u k
    exact modulatedPlanarJet_covariant_zero (P.profile j u k) (P.actualX j u)
      (P.actualZ j u) (P.length j) P.width (-P.rowSlope j) (P.frequency k)
      P.scale y (P.length_pos j).ne' x

theorem polarize_rawInterval (c : ℂ) (hc : ‖c‖ = 1)
    (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (i : Fin 3) (lower upper : ℕ) (x y : ℝ) :
    (P.polarize alt hAlt c hc).rawInterval
        ((P.polarize alt hAlt c hc).family.mainCoefficient d v g) i lower upper x y =
      polarizedPacketInterval (P.family.mainCoefficient d v g)
        ((P.withProfile alt hAlt).family.mainCoefficient d v g)
        (fun j u k t s => P.raw i j u k t s)
        (fun j u k t s => (P.withProfile alt hAlt).raw i j u k t s)
        c lower upper x y := by
  unfold rawInterval polarizedPacketInterval
  congr 1
  · funext j u
    exact P.polarize_mainCoefficient alt hAlt c hc d v hv g hg hg1 j u
  · funext j u k t s
    exact congrArg (fun f : SchwartzMap ℝ ℂ => f s) (P.polarize_raw alt hAlt c hc i j u k t)

theorem cross_rawInterval_polarization
    (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (i : Fin 3) (lower upper : ℕ) (x y : ℝ) :
    let F := fun phase : Fin 4 =>
      let Q := P.polarize alt hAlt (packetPolarizationPhase phase) (packetPolarizationPhase_norm phase)
      Q.rawInterval (Q.family.mainCoefficient d v g) i lower upper x y
    (4 : ℂ) • (P.withProfile alt hAlt).rawInterval
        (P.family.mainCoefficient d v g) i lower upper x y =
      F 0 - F 1 - Complex.I • F 2 + Complex.I • F 3 := by
  dsimp only
  simp_rw [P.polarize_rawInterval alt hAlt _ _ d v hv g hg hg1]
  simpa [rawInterval, packetPolarizationPhase] using
    planarPacketInterval_cross_polarization (P.family.mainCoefficient d v g)
      ((P.withProfile alt hAlt).family.mainCoefficient d v g)
      (fun j u k t s => P.raw i j u k t s)
      (fun j u k t s => (P.withProfile alt hAlt).raw i j u k t s) lower upper x y

theorem cross_covariant_polarization (hscale : P.scale ≠ 0)
    (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (lower upper : ℕ) (x y : ℝ) :
    let F := fun (phase : Fin 4) (t : ℝ) =>
      let Q := P.polarize alt hAlt (packetPolarizationPhase phase) (packetPolarizationPhase_norm phase)
      Q.rawInterval (Q.family.mainCoefficient d v g) 0 lower upper x t
    let C := fun t => (P.withProfile alt hAlt).rawInterval
      (P.family.mainCoefficient d v g) 0 lower upper x t
    (4 : ℂ) • covariantSignal P.frequency (fun k t => C t k) y =
      covariantSignal P.frequency (fun k t => F 0 t k) y -
      covariantSignal P.frequency (fun k t => F 1 t k) y -
      Complex.I • covariantSignal P.frequency (fun k t => F 2 t k) y +
      Complex.I • covariantSignal P.frequency (fun k t => F 3 t k) y := by
  let Q := fun phase : Fin 4 => P.polarize alt hAlt
    (packetPolarizationPhase phase) (packetPolarizationPhase_norm phase)
  have hs (phase : Fin 4) : (Q phase).rawInterval
      ((Q phase).family.mainCoefficient d v g) 1 lower upper x y =
      P.scale • covariantSignal P.frequency
        (fun k t => (Q phase).rawInterval ((Q phase).family.mainCoefficient d v g)
          0 lower upper x t k) y :=
    ((Q phase).rawInterval_scaled_covariant ((Q phase).family.mainCoefficient d v g)
      lower upper x y).symm
  have h := P.cross_rawInterval_polarization alt hAlt d v hv g hg hg1 1 lower upper x y
  change (4 : ℂ) • (P.withProfile alt hAlt).rawInterval
      (P.family.mainCoefficient d v g) 1 lower upper x y =
    (Q 0).rawInterval ((Q 0).family.mainCoefficient d v g) 1 lower upper x y -
    (Q 1).rawInterval ((Q 1).family.mainCoefficient d v g) 1 lower upper x y -
    Complex.I • (Q 2).rawInterval ((Q 2).family.mainCoefficient d v g) 1 lower upper x y +
    Complex.I • (Q 3).rawInterval ((Q 3).family.mainCoefficient d v g) 1 lower upper x y at h
  rw [← (P.withProfile alt hAlt).rawInterval_scaled_covariant, hs, hs, hs, hs] at h
  simp only [show (P.withProfile alt hAlt).scale = P.scale from rfl,
    show (P.withProfile alt hAlt).frequency = P.frequency from rfl] at h
  apply smul_right_injective (M := EuclideanSpace ℂ κ) hscale
  simpa only [smul_add, smul_sub, smul_comm P.scale (4 : ℂ), smul_comm P.scale Complex.I] using h

theorem cross_interval_joint_bound (hscale : P.scale ≠ 0)
    (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (lower upper : ℕ) (x y W B : ℝ) (hW : 0 ≤ W)
    (hbound : ∀ phase : Fin 4,
      let Q := P.polarize alt hAlt (packetPolarizationPhase phase) (packetPolarizationPhase_norm phase)
      let F := fun t => Q.rawInterval (Q.family.mainCoefficient d v g) 0 lower upper x t
      ‖F y‖ + W * ‖covariantSignal P.frequency (fun k t => F t k) y‖ ≤ B) :
    let C := fun t => (P.withProfile alt hAlt).rawInterval
      (P.family.mainCoefficient d v g) 0 lower upper x t
    ‖C y‖ + W * ‖covariantSignal P.frequency (fun k t => C t k) y‖ ≤ B := by
  let Q := fun phase : Fin 4 => P.polarize alt hAlt
    (packetPolarizationPhase phase) (packetPolarizationPhase_norm phase)
  let F := fun phase : Fin 4 =>
    (Q phase).rawInterval ((Q phase).family.mainCoefficient d v g) 0 lower upper x y
  let DF := fun phase : Fin 4 => covariantSignal P.frequency
    (fun k t => (Q phase).rawInterval ((Q phase).family.mainCoefficient d v g)
      0 lower upper x t k) y
  let C := (P.withProfile alt hAlt).rawInterval
    (P.family.mainCoefficient d v g) 0 lower upper x y
  let DC := covariantSignal P.frequency (fun k t => (P.withProfile alt hAlt).rawInterval
    (P.family.mainCoefficient d v g) 0 lower upper x t k) y
  have hf : (4 : ℂ) • C = F 0 - F 1 - Complex.I • F 2 + Complex.I • F 3 :=
    P.cross_rawInterval_polarization alt hAlt d v hv g hg hg1 0 lower upper x y
  have hdf : (4 : ℂ) • DC = DF 0 - DF 1 - Complex.I • DF 2 + Complex.I • DF 3 :=
    P.cross_covariant_polarization alt hAlt hscale d v hv g hg hg1 lower upper x y
  have hb : ∀ phase, ‖F phase‖ + W * ‖DF phase‖ ≤ B := hbound
  exact four_phase_joint_bound C DC F DF W B hW hf hdf hb

end LipschitzHilbert.SourceLatticePacket

end

end OAI
