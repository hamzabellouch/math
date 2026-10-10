import OAI.MathematicalPhysics.Boltzmann.Branching.EntrySites
import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceCollisionGeometry
import OAI.MathematicalPhysics.Boltzmann.Branching.SeedEscapeMeasure
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedDampedBalance
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalEvolution
import OAI.MathematicalPhysics.Boltzmann.Compactness.SelectedOriginDeletion

namespace OAI

section

/-! # Reachable regions for a fixed finite number of physical gain collisions -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace BoltzmannNonuniqueness.ReferenceGeometry

def finiteFlightCone (N n : ℕ) (h R : ℝ) (x : V) (p : PhysicalFlightState) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ h ∧ ‖p.2.2‖ ≤ R+2*((N:ℝ)-n) ∧
    ‖p.2.1-x‖ ≤ (h-p.1)*(R+2*N)

theorem finiteFlightCone_measurable (N n : ℕ) (h R : ℝ) (x : V) :
    MeasurableSet {p | finiteFlightCone N n h R x p} := by
  unfold finiteFlightCone
  measurability

theorem finiteFlightCone_initial {N : ℕ} {h R : ℝ} (hh : 0 ≤ h)
    (x v : V) (hv : ‖v‖ ≤ R) : finiteFlightCone N N h R x (h,(x,v)) := by
  exact ⟨hh,le_rfl,by simpa using hv,by simp⟩

theorem markedChild_norm_le (m : HistoryMark) (v wp wm : V) (n : Sphere)
    (hp : ‖wp‖ ≤ 2) (hm : ‖wm‖ ≤ 2) :
    ‖markedChild m v wp wm n.1‖ ≤ ‖v‖+2 := by
  have hc (w : V) (hw : ‖w‖ ≤ 2) : ‖child v w n.1‖ ≤ ‖v‖+2 := by
    have hb := child_lipschitz v w 0 0 n.1 (mem_sphere_zero_iff_norm.mp n.2)
    have hz : child 0 0 n.1 = 0 := by simp [child]
    rw [hz,sub_zero,sub_zero,sub_zero] at hb
    exact hb.trans (add_le_add le_rfl hw)
  fin_cases m
  · change ‖v‖ ≤ ‖v‖+2; linarith
  · exact hc wp hp
  · exact hc wm hm

theorem finiteFlightCone_parameter_step {N n : ℕ} {h R : ℝ} {x : V}
    (b : BeamCoefficients) (T : ℝ) {p : PhysicalFlightState}
    (hq : finiteFlightCone N (n+1) h R x p) (m : HistoryMark)
    {s : ℝ} (hs : s ∈ Icc 0 p.1) (z : Sphere)
    (hp : ‖b.plusPartner (mediumPoint T p s)‖ ≤ 2)
    (hm : ‖b.minusPartner (mediumPoint T p s)‖ ≤ 2) :
    finiteFlightCone N n h R x (mediumParameterState b T p (m,(s,z))) := by
  rcases hq with ⟨ht₀,ht,hvel,hpos⟩
  push_cast at hvel
  have hv : ‖p.2.2‖ ≤ R+2*N := by
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have hd : ‖p.2.1+s • p.2.2-x‖ ≤ (h-(p.1-s))*(R+2*N) := by
    calc
      _ = ‖(p.2.1-x)+s • p.2.2‖ := by congr 1; module
      _ ≤ ‖p.2.1-x‖+‖s • p.2.2‖ := norm_add_le _ _
      _ = ‖p.2.1-x‖+s*‖p.2.2‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs.1]
      _ ≤ (h-p.1)*(R+2*N)+s*(R+2*N) :=
        add_le_add hpos (mul_le_mul_of_nonneg_left hv hs.1)
      _ = _ := by ring
  refine ⟨sub_nonneg.mpr hs.2,?_,?_,hd⟩
  · change p.1-s ≤ h
    linarith [hs.1]
  · change ‖markedChild m p.2.2 (b.plusPartner (mediumPoint T p s))
      (b.minusPartner (mediumPoint T p s)) z.1‖ ≤ _
    have hc := markedChild_norm_le m p.2.2 _ _ z hp hm
    linarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A bounded finite collision cone stays above the cold cutoff and in a compact phase set -/
noncomputable section
open Set
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem finiteFlightCone_displacement {N n : ℕ} {h R : ℝ} {x : V}
    {q : PhysicalFlightState} (hq : finiteFlightCone N n h R x q) :
    ‖q.2.1-x‖ ≤ h*(R+2*N) := by
  have hB : 0 ≤ R+2*N := by
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith [hq.2.2.1,norm_nonneg q.2.2]
  exact hq.2.2.2.trans (mul_le_mul_of_nonneg_right (by linarith [hq.1]) hB)

theorem finiteFlightCone_cold_domain {N n : ℕ} {t h R a η l : ℝ} {x : V}
    (ha : a ≤ t) (hl : 0 ≤ l) (hshort : h*(R+2*N) ≤ 1)
    (hx : Real.exp η*l+1 < ‖transverse x‖)
    {q : PhysicalFlightState} (hq : finiteFlightCone N n h R x q) :
    flightCharacteristicEquiv (t+h) q ∈ coldCharacteristicDomain a η l := by
  have hd := (finiteFlightCone_displacement hq).trans hshort
  have ht := norm_sub_norm_le (transverse x) (transverse q.2.1)
  have he : ‖transverse x-transverse q.2.1‖ ≤ 1 := by
    rw [← PlaneChart.transverse_sub]
    exact (LargeOutput.transverse_norm_le (x-q.2.1)).trans (by rwa [norm_sub_rev])
  have hy : Real.exp η*l < ‖transverse q.2.1‖ := by linarith
  change a ≤ t+h-q.1 ∧ 0 < ‖transverse (q.2.1-(t+h-q.1) • q.2.2+
    (t+h-q.1) • q.2.2)‖ ∧ Real.exp η*l < ‖transverse (q.2.1-(t+h-q.1) • q.2.2+
    (t+h-q.1) • q.2.2)‖
  rw [sub_add_cancel]
  exact ⟨by linarith [hq.2.1],(mul_nonneg (Real.exp_pos η).le hl).trans_lt hy,hy⟩

theorem finiteFlightCone_phase_bound {N n : ℕ} {t h R X : ℝ} {x : V}
    (ht : 0 ≤ t) (hR : 0 ≤ R) (hX : 0 ≤ X) (hx : ‖x‖ ≤ X)
    {q : PhysicalFlightState} (hq : finiteFlightCone N n h R x q) :
    ‖(flightCharacteristicEquiv (t+h) q).2‖ ≤ X+(t+2*h+1)*(R+2*N) := by
  have hh : 0 ≤ h := hq.1.trans hq.2.1
  have hB : 0 ≤ R+2*N := by positivity
  have hv : ‖q.2.2‖ ≤ R+2*N := by
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith [hq.2.2.1]
  have hpos : ‖q.2.1‖ ≤ X+h*(R+2*N) := by
    calc
      _ ≤ ‖q.2.1-x‖+‖x‖ := by simpa only [sub_add_cancel] using norm_add_le (q.2.1-x) x
      _ ≤ _ := by simpa only [add_comm] using add_le_add (finiteFlightCone_displacement hq) hx
  have htime : 0 ≤ t+h-q.1 := by linarith [hq.2.1]
  have hphase : ‖q.2.1-(t+h-q.1) • q.2.2‖ ≤ X+(t+2*h)*(R+2*N) := by
    apply (norm_sub_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg htime]
    have hm := mul_le_mul_of_nonneg_left hv htime
    have hm' := mul_le_mul_of_nonneg_right (show t+h-q.1 ≤ t+h by linarith [hq.1]) hB
    nlinarith
  rw [Prod.norm_def,max_le_iff]
  exact ⟨by change ‖q.2.1-(t+h-q.1) • q.2.2‖ ≤ _; nlinarith,
    hv.trans (by nlinarith [mul_nonneg (show 0 ≤ t+2*h by positivity) hB])⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform upper and positive transverse bounds for finitely many successive windows -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem finite_velocity_window_bounds (R b : ℕ → ℝ)
    (hR : ∀ i, 0 < R i) (hb : ∀ i, 0 < b i) (m : ℕ) :
    ∃ V β : ℝ, 0 < V ∧ 0 < β ∧ ∀ i v,
      v ∈ velocityWindow (R (min i m)) (b (min i m)) →
        ‖v‖ ≤ V ∧ β ≤ ‖transverse v‖ := by
  let I := Finset.range (m+1)
  have hI : I.Nonempty := Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero m)
  let V := I.sup' hI R
  let β := I.inf' hI b
  have hzero : 0 ∈ I := Finset.mem_range.mpr (Nat.zero_lt_succ m)
  have hV : 0 < V := (hR 0).trans_le (Finset.le_sup' R hzero)
  have hβ : 0 < β := (Finset.lt_inf'_iff hI).mpr (fun i _ => hb i)
  refine ⟨V,β,hV,hβ,?_⟩
  intro i v hv
  have hi : min i m ∈ I := Finset.mem_range.mpr (lt_of_le_of_lt (min_le_right i m)
    (Nat.lt_succ_self m))
  exact ⟨hv.1.trans (Finset.le_sup' R hi),(Finset.inf'_le b hi).trans hv.2⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # One compact phase cutoff contains all short entry histories in a fixed time window -/
noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.EuclideanFlight
namespace BoltzmannNonuniqueness.ReferenceGeometry

def phaseBallCore (M : ℝ) : Set CharacteristicPhase := {z | ‖z.2‖ ≤ M}

theorem phaseBallCore_measurable (M : ℝ) : MeasurableSet (phaseBallCore M) :=
  measurableSet_le measurable_snd.norm measurable_const

theorem finiteFlightCone_window_core {N n : ℕ} {s t U R X : ℝ} {x : V}
    (hs : 0 ≤ s) (ht : t ≤ U) (hR : 0 ≤ R) (hX : 0 ≤ X) (hx : ‖x‖ ≤ X)
    {q : PhysicalFlightState} (hq : finiteFlightCone N n (t-s) R x q) :
    flightCharacteristicEquiv t q ∈ phaseBallCore (X+(2*U+1)*(R+2*N)) := by
  have hb := finiteFlightCone_phase_bound hs hR hX hx hq
  have he : s+(t-s) = t := by ring
  rw [he] at hb
  change ‖(flightCharacteristicEquiv t q).2‖ ≤ _
  apply hb.trans
  have hB : 0 ≤ R+2*N := by positivity
  nlinarith [mul_le_mul_of_nonneg_right ht hB,mul_nonneg hs hB]

theorem exists_phaseBall_cutoff (M : ℝ) :
    ∃ β : WeakTime.Phase → ℝ, ContDiff ℝ (⊤ : ℕ∞) β ∧ HasCompactSupport β ∧
      (∀ p, 0 ≤ β p) ∧ (∀ p, β p ≤ 1) ∧ (∀ p, ‖p‖ ≤ M → β p = 1) := by
  obtain ⟨n,hn⟩ := exists_nat_gt M
  refine ⟨seedPhaseCutoff n,seedPhaseCutoff_smooth n,seedPhaseCutoff_compact n,
    (fun p => (seedPhaseCutoff_mem n p).1),(fun p => (seedPhaseCutoff_mem n p).2),?_⟩
  intro p hp
  apply (seedPhaseBump n).one_of_mem_closedBall
  rw [Metric.mem_closedBall,dist_zero_right]
  dsimp [seedPhaseBump]
  linarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
