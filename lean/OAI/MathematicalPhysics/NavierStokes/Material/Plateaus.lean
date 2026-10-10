import OAI.MathematicalPhysics.NavierStokes.Material.Clock
import OAI.MathematicalPhysics.NavierStokes.Material.Curls

namespace OAI

namespace Alternating
open scoped Topology BigOperators
open Filter
open Memory

noncomputable section

def memoryPoint (z x y : ℝ) : Space :=
  z • basisVector 0 + x • basisVector 1 + y • basisVector 2

@[simp] theorem memoryPoint_zero (z x y : ℝ) : memoryPoint z x y 0 = z := by
  simp [memoryPoint, basisVector, PiLp.add_apply, PiLp.smul_apply]

@[simp] theorem memoryPoint_one (z x y : ℝ) : memoryPoint z x y 1 = x := by
  simp [memoryPoint, basisVector, PiLp.add_apply, PiLp.smul_apply]

@[simp] theorem memoryPoint_two (z x y : ℝ) : memoryPoint z x y 2 = y := by
  simp [memoryPoint, basisVector, PiLp.add_apply, PiLp.smul_apply]

theorem memoryPoint_norm_lt {z x y : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    ‖memoryPoint z x y‖ < 2 := by
  have hh : ‖memoryPoint z x y‖ ^ 2 = z ^ 2 + x ^ 2 + y ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_succ, sq_abs, add_assoc]
  have hz' : z ^ 2 ≤ 1 := by nlinarith [hz.1, hz.2]
  have hx' : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
  have hy' : y ^ 2 ≤ 1 := by nlinarith [hy.1, hy.2]
  nlinarith [norm_nonneg (memoryPoint z x y)]

def snapshot (I : MachineInput) (hI : ValidInput I) (n : ℕ) : Space :=
  memoryPoint
    (signal (alphabetBase I.1) I.2.length
      (fun j => I.1.isHalting (configurationAt I j).state) n)
    (history (alphabetBase I.1) I.2.length (actualBlock I hI) 0 n)
    (history (alphabetBase I.1) I.2.length (actualBlock I hI) 1 n)

def slotPoint (I : MachineInput) (hI : ValidInput I) (n : ℕ) (u : ℝ) : Space :=
  (1 - u) • snapshot I hI n + u • snapshot I hI (n + 1)

@[simp] theorem slotPoint_zero (I : MachineInput) (hI : ValidInput I) (n : ℕ) :
    slotPoint I hI n 0 = snapshot I hI n := by simp [slotPoint]

@[simp] theorem slotPoint_one (I : MachineInput) (hI : ValidInput I) (n : ℕ) :
    slotPoint I hI n 1 = snapshot I hI (n + 1) := by simp [slotPoint]

theorem slotPoint_coord_zero (I : MachineInput) (hI : ValidInput I) (n : ℕ) (u : ℝ) :
    slotPoint I hI n u 0 = signalAlong (alphabetBase I.1) I.2.length
      (fun j => I.1.isHalting (configurationAt I j).state) n u := by
  simp [slotPoint, snapshot, PiLp.add_apply, PiLp.smul_apply, signalAlong]

theorem slotPoint_eq_memoryPoint (I : MachineInput) (hI : ValidInput I) (n : ℕ) (u : ℝ) :
    slotPoint I hI n u = memoryPoint
      (signalAlong (alphabetBase I.1) I.2.length
        (fun j => I.1.isHalting (configurationAt I j).state) n u)
      ((1 - u) * history (alphabetBase I.1) I.2.length (actualBlock I hI) 0 n +
        u * history (alphabetBase I.1) I.2.length (actualBlock I hI) 0 (n + 1))
      ((1 - u) * history (alphabetBase I.1) I.2.length (actualBlock I hI) 1 n +
        u * history (alphabetBase I.1) I.2.length (actualBlock I hI) 1 (n + 1)) := by
  ext i
  fin_cases i <;> simp [slotPoint, snapshot, PiLp.add_apply, PiLp.smul_apply, signalAlong]

theorem slotPoint_norm_lt (I : MachineInput) (hI : ValidInput I) (n : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) : ‖slotPoint I hI n u‖ < 2 := by
  rw [slotPoint_eq_memoryPoint]
  have hx := history_interpolation_mem (alphabetBase_ge_four I.1) (actualBlock I hI) 0 n hu
  have hy := history_interpolation_mem (alphabetBase_ge_four I.1) (actualBlock I hI) 1 n hu
  have hz := signalAlong_mem (alphabetBase_ge_four I.1) I.2.length
    (fun j => I.1.isHalting (configurationAt I j).state) n hu
  exact memoryPoint_norm_lt ⟨hz.1.le, hz.2.le⟩
    ⟨hx.1, by linarith [hx.2]⟩ ⟨hy.1, by linarith [hy.2]⟩

theorem slotPoint_donor (I : MachineInput) (hI : ValidInput I) (n : ℕ) (u : ℝ) :
    (if n % 2 = 0 then slotPoint I hI n u 1 else slotPoint I hI n u 2) =
      donor (alphabetBase I.1) I.2.length (actualBlock I hI) n := by
  have hd := (alternating_histories_step (actualBlock I hI) n).1
  by_cases hn : n % 2 = 0
  · simp only [hn] at hd
    simp only [ite_eq_left hn, slotPoint, snapshot, PiLp.add_apply, PiLp.smul_apply,
      memoryPoint_one, smul_eq_mul]
    rw [hd]
    dsimp [donor]
    rw [hn]
    ring
  · have hn' : n % 2 = 1 := by omega
    simp only [hn'] at hd
    simp only [ite_eq_right hn, slotPoint, snapshot, PiLp.add_apply, PiLp.smul_apply,
      memoryPoint_two, smul_eq_mul]
    rw [hd]
    dsimp [donor]
    rw [hn']
    ring

theorem snapshot_step (I : MachineInput) (hI : ValidInput I) (n : ℕ) :
    snapshot I hI (n + 1) - snapshot I hI n =
      if n % 2 = 0 then
        localSignal I.1 I.2.length n (donor (alphabetBase I.1) I.2.length (actualBlock I hI) n) • basisVector 0 +
        localWrite I.1 I.2.length n (donor (alphabetBase I.1) I.2.length (actualBlock I hI) n) • basisVector 2
      else
        localSignal I.1 I.2.length n (donor (alphabetBase I.1) I.2.length (actualBlock I hI) n) • basisVector 0 +
        localWrite I.1 I.2.length n (donor (alphabetBase I.1) I.2.length (actualBlock I hI) n) • basisVector 1 := by
  rw [localSignal_exact I hI n, localWrite_exact I hI n]
  by_cases hn : n % 2 = 0
  · have hnext : (n + 1) % 2 = 1 := by omega
    simp only [ite_eq_left hn]
    ext i
    fin_cases i <;>
      simp [snapshot, signal, history_succ, hnext, basisVector, PiLp.add_apply,
        PiLp.sub_apply, PiLp.smul_apply]
  · have hnext : (n + 1) % 2 = 0 := by omega
    simp only [ite_eq_right hn]
    ext i
    fin_cases i <;>
      simp [snapshot, signal, history_succ, hnext, basisVector, PiLp.add_apply,
        PiLp.sub_apply, PiLp.smul_apply]

theorem slotVelocity_at_slotPoint (I : MachineInput) (hI : ValidInput I) (n : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) :
    slotVelocity I.1 I.2.length n (slotPoint I hI n u) = snapshot I hI (n + 1) - snapshot I hI n := by
  rw [slotVelocity_on_plateau I.1 I.2.length n (slotPoint_norm_lt I hI n hu), snapshot_step]
  have hd := slotPoint_donor I hI n u
  split_ifs with hn
  · rw [ite_eq_left hn] at hd
    rw [hd]
  · rw [ite_eq_right hn] at hd
    rw [hd]

theorem slotCurve_hasDerivAt (I : MachineInput) (hI : ValidInput I) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s => slotPoint I hI n (clock s))
      (deriv clock t • slotVelocity I.1 I.2.length n (slotPoint I hI n (clock t))) t := by
  rw [slotVelocity_at_slotPoint I hI n (clock_mem t)]
  have hc := (clock_smooth.differentiable (by simp) t).hasDerivAt
  have id : (fun s => slotPoint I hI n (clock s)) =
      fun s => snapshot I hI n + clock s • (snapshot I hI (n + 1) - snapshot I hI n) := by
    funext s
    simp only [slotPoint, smul_sub, sub_smul, one_smul]
    module
  rw [id]
  exact (hc.smul_const _).const_add _

def initialCode (I : MachineInput) : ℝ :=
  ((2 * (initialConfiguration I.2).state : ℝ) +
    fraction (alphabetBase I.1) (leftDigits (width I.2.length 0) (initialConfiguration I.2)) +
    (alphabetBase I.1 : ℝ)⁻¹ ^ width I.2.length 0 *
      fraction (alphabetBase I.1) (rightDigits (width I.2.length 0) (initialConfiguration I.2))) /
        (alphabetBase I.1 : ℝ)

theorem initialCode_eq (I : MachineInput) (hI : ValidInput I) :
    initialCode I = (actualBlock I hI 0).code := by
  rw [Block.code_formula (by have := alphabetBase_ge_four I.1; omega)]
  simp [initialCode, actualBlock, Block.leftCode, Block.rightCode, configurationAt]

def loadingDisplacement (I : MachineInput) : Space :=
  (1 - epsilon (alphabetBase I.1) I.2.length 0) • basisVector 0 +
    (epsilon (alphabetBase I.1) I.2.length 0 * initialCode I) • basisVector 1

def loadingVelocity (I : MachineInput) : Space → Space :=
  localizedCurl 0 1 (oddPotential
    (fun _ => epsilon (alphabetBase I.1) I.2.length 0 * initialCode I)
    (fun _ => 1 - epsilon (alphabetBase I.1) I.2.length 0))

theorem loadingVelocity_smooth (I : MachineInput) :
    ContDiff ℝ (⊤ : ℕ∞) (loadingVelocity I) :=
  localizedCurl_smooth (oddPotential_smooth contDiff_const contDiff_const) 0 1

theorem loadingVelocity_divergence (I : MachineInput) (x : Space) :
    divergence (loadingVelocity I) x = 0 :=
  localizedCurl_divergence (oddPotential_smooth contDiff_const contDiff_const) 0 1 x

theorem loadingVelocity_support (I : MachineInput) :
    tsupport (loadingVelocity I) ⊆ Metric.closedBall 0 3 :=
  localizedCurl_support 0 1 _

theorem loadingVelocity_on_plateau (I : MachineInput) {x : Space} (hx : ‖x‖ < 2) :
    loadingVelocity I x = loadingDisplacement I := by
  unfold loadingVelocity loadingDisplacement
  rw [localizedCurl_on_plateau _ _ _ hx, oddPotential_curl (differentiable_const _) (differentiable_const _)]

theorem loadingDisplacement_eq (I : MachineInput) (hI : ValidInput I) :
    loadingDisplacement I = snapshot I hI 0 - observedParticle := by
  rw [loadingDisplacement, initialCode_eq I hI]
  ext i
  fin_cases i <;>
    simp [snapshot, signal, history, observedParticle, basisVector, PiLp.add_apply,
      PiLp.smul_apply, Finset.filter_singleton]
  all_goals ring

def loadingPoint (I : MachineInput) (u : ℝ) : Space :=
  observedParticle + u • loadingDisplacement I

theorem loadingPoint_zero (I : MachineInput) : loadingPoint I 0 = observedParticle := by
  simp [loadingPoint]

theorem loadingPoint_one (I : MachineInput) (hI : ValidInput I) :
    loadingPoint I 1 = snapshot I hI 0 := by
  simp [loadingPoint, loadingDisplacement_eq I hI]

theorem loadingPoint_norm_lt (I : MachineInput) (hI : ValidInput I) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) : ‖loadingPoint I u‖ < 2 := by
  have h0 : observedParticle ∈ Metric.ball (0 : Space) 2 := by
    simp [observedParticle, basisVector, Metric.mem_ball]
  have h1 : snapshot I hI 0 ∈ Metric.ball (0 : Space) 2 := by
    have hp := slotPoint_norm_lt I hI 0 (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    simpa using hp
  have hconv := (convex_ball (0 : Space) 2) h0 h1 (by linarith [hu.2] : 0 ≤ 1 - u) hu.1 (by ring)
  have he : loadingPoint I u = (1 - u) • observedParticle + u • snapshot I hI 0 := by
    rw [loadingPoint, loadingDisplacement_eq I hI]
    module
  simpa [he] using hconv

theorem loadingPoint_negative (I : MachineInput) (hI : ValidInput I) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) : loadingPoint I u 0 < 0 := by
  have he : 0 < epsilon (alphabetBase I.1) I.2.length 0 :=
    epsilon_pos (by have := alphabetBase_ge_four I.1; omega) _ _
  have hconv := (convex_Iio (0 : ℝ)) (show (-1 : ℝ) ∈ Set.Iio 0 by norm_num)
    (show -epsilon (alphabetBase I.1) I.2.length 0 ∈ Set.Iio 0 by simpa using neg_neg_of_pos he)
    (by linarith [hu.2] : 0 ≤ 1 - u) hu.1 (by ring)
  change (1 - u) * (-1) + u * (-epsilon (alphabetBase I.1) I.2.length 0) < 0 at hconv
  have hz : loadingPoint I u 0 =
      (1 - u) * (-1) + u * (-epsilon (alphabetBase I.1) I.2.length 0) := by
    simp [loadingPoint, loadingDisplacement_eq I hI, snapshot, signal, observedParticle,
      basisVector, PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply]
    ring
  simpa [hz] using hconv

theorem loadingCurve_hasDerivAt (I : MachineInput) (hI : ValidInput I) (t : ℝ) :
    HasDerivAt (fun s => loadingPoint I (clock s))
      (deriv clock t • loadingVelocity I (loadingPoint I (clock t))) t := by
  rw [loadingVelocity_on_plateau I (loadingPoint_norm_lt I hI (clock_mem t))]
  exact ((clock_smooth.differentiable (by simp) t).hasDerivAt.smul_const _).const_add _

end
end Alternating

end OAI
