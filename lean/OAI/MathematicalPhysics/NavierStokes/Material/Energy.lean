import OAI.MathematicalPhysics.NavierStokes.Material.Velocity
import OAI.MathematicalPhysics.NavierStokes.Material.Residual
import OAI.MathematicalPhysics.NavierStokes.Material.SpatialL2

namespace OAI

namespace Alternating
open scoped Topology BigOperators
open Filter MeasureTheory

noncomputable section

@[simp] theorem spatialPartial_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Space → E) : spatialPartial 0 g = g := by
  simp [spatialPartial]

@[simp] theorem spatialPartial_zero_function {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : MultiIndex) : spatialPartial α (fun _ : Space => (0 : E)) = fun _ => 0 := by
  have h (i : Fin 3) (r : ℕ) : (spatialD i)^[r] (fun _ : Space => (0 : E)) = fun _ => 0 := by
    induction r with
    | zero => rfl
    | succ r ih =>
      rw [Function.iterate_succ_apply', ih]
      funext x
      change fderiv ℝ (fun _ : Space => (0 : E)) x (basisVector i) = 0
      rw [fderiv_const_apply]
      rfl
  simp only [spatialPartial, h]

theorem shiftedSum_continuousInSobolev {a : ℝ → ℝ} (ha : Continuous a)
    (ha0 : ∀ s ≤ 0, a s = 0) (W : ℕ → Space → Space)
    (hW : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (W n)) (hc : ∀ n, HasCompactSupport (W n))
    (k : ℕ) (T : ℝ) : ContinuousInSobolev k (shiftedSum a W) T := by
  obtain ⟨N, hN⟩ := exists_nat_gt T
  intro α _hα
  refine ⟨SlotL2.finiteLift W hW hc a α N,
    (SlotL2.finiteLift_continuous W hW hc ha α N).continuousOn, ?_⟩
  intro t ht
  have he : shiftedSum a W t = fun x => ∑ n ∈ Finset.range N, a (t - n) • W n x := by
    funext x
    exact shiftedSum_eq_sum ha0 W N (ht.2.trans hN.le) x
  rw [he, spatialPartial_finiteCombination _ _ (fun n _ => hW n)]
  exact SlotL2.finiteLift_ae W hW hc a α N t

theorem shiftedSum_timeDerivative_on {a : ℝ → ℝ} (ha : Differentiable ℝ a)
    (ha0 : ∀ s ≤ 0, a s = 0) (W : ℕ → Space → Space)
    {N : ℕ} {t : ℝ} (ht : 0 ≤ t) (hN : t < N) (x : Space) :
    timeDerivative (shiftedSum a W) t x =
      ∑ n ∈ Finset.range N, deriv a (t - n) • W n x := by
  have hd : HasDerivAt (fun s : ℝ => ∑ n ∈ Finset.range N, a (s - n) • W n x)
      (∑ n ∈ Finset.range N, deriv a (t - n) • W n x) t := by
    apply HasDerivAt.fun_sum
    intro n _hn
    have hh := (ha (t - n)).hasDerivAt.comp t ((hasDerivAt_id t).sub_const (n : ℝ))
    simpa using hh.smul_const (W n x)
  have hd' : HasDerivAt (fun s => shiftedSum a W s x)
      (∑ n ∈ Finset.range N, deriv a (t - n) • W n x) t := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hN] with s hs
    exact shiftedSum_eq_sum ha0 W N hs.le x
  exact hd'.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 t ht)

theorem shiftedSum_c1InL2 {a : ℝ → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (ha0 : ∀ s ≤ 0, a s = 0) (W : ℕ → Space → Space)
    (hW : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (W n)) (hc : ∀ n, HasCompactSupport (W n))
    (T : ℝ) : C1InL2 (shiftedSum a W) T := by
  obtain ⟨N, hN⟩ := exists_nat_gt T
  have hda : Continuous (deriv a) := (contDiff_infty_iff_deriv.mp ha).2.continuous
  refine ⟨SlotL2.finiteLift W hW hc a 0 N, SlotL2.finiteLift W hW hc (deriv a) 0 N,
    (SlotL2.finiteLift_continuous W hW hc ha.continuous 0 N).continuousOn,
    (SlotL2.finiteLift_continuous W hW hc hda 0 N).continuousOn, ?_⟩
  intro t ht
  refine ⟨?_, ?_, (SlotL2.finiteLift_hasDerivAt W hW hc (ha.differentiable (by simp)) 0 N t).hasDerivWithinAt⟩
  · have he := SlotL2.finiteLift_ae W hW hc a 0 N t
    simp only [spatialPartial_zero] at he
    exact he.trans (Eventually.of_forall fun x => (shiftedSum_eq_sum ha0 W N (ht.2.trans hN.le) x).symm)
  · have he := SlotL2.finiteLift_ae W hW hc (deriv a) 0 N t
    simp only [spatialPartial_zero] at he
    exact he.trans (Eventually.of_forall fun x =>
      (shiftedSum_timeDerivative_on (ha.differentiable (by simp)) ha0 W ht.1 (ht.2.trans_lt hN) x).symm)

theorem zeroPressure_continuousInSobolev (k : ℕ) (T : ℝ) :
    ContinuousInSobolev k (fun (_ : ℝ) (_ : Space) => (0 : ℝ)) T := by
  intro α _hα
  refine ⟨fun _ => 0, continuous_const.continuousOn, ?_⟩
  intro t _ht
  simp

theorem bounded_finite_cylinder {u : Field} (hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u))
    {K : Set Space} (hK : IsCompact K) (hs : SupportedIn K u) (T : ℝ) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : Space, ‖u t x‖ + ‖fderiv ℝ (u t) x‖ ≤ C := by
  have hp : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℝ × Space) × Space => u p.1.1 p.2) :=
    hu.comp ((contDiff_fst.fst).prodMk contDiff_snd)
  have hdf : ContDiff ℝ (⊤ : ℕ∞) (fun tx : ℝ × Space => fderiv ℝ (u tx.1) tx.2) :=
    hp.fderiv contDiff_snd (by simp)
  have hcont : Continuous (fun tx : ℝ × Space => ‖u tx.1 tx.2‖ + ‖fderiv ℝ (u tx.1) tx.2‖) :=
    hu.continuous.norm.add hdf.continuous.norm
  obtain ⟨C, hC⟩ := ((isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) T)).prod hK).bddAbove_image hcont.continuousOn
  refine ⟨max C 0, ?_⟩
  intro t ht x
  by_cases hx : x ∈ K
  · have hh : ‖u t x‖ + ‖fderiv ℝ (u t) x‖ ≤ C := hC ⟨(t, x), ⟨ht, hx⟩, rfl⟩
    exact hh.trans (le_max_left C 0)
  · have hts : tsupport (u t) ⊆ K := by
      apply closure_minimal _ hK.isClosed
      intro y hy
      by_contra hyK
      exact hy (hs t ht.1 y hyK)
    have hfd : fderiv ℝ (u t) x = 0 := fderiv_of_notMem_tsupport ℝ (fun hh => hx (hts hh))
    rw [hs t ht.1 x hx, hfd, norm_zero, norm_zero, add_zero]
    exact le_max_right _ _

theorem shiftedSum_energyClass {a : ℝ → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (ha0 : ∀ s ≤ 0, a s = 0) (W : ℕ → Space → Space)
    (hW : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (W n))
    {K : Set Space} (hK : IsCompact K) (hs : ∀ n, tsupport (W n) ⊆ K) :
    EnergyClass (shiftedSum a W) (fun _ _ => 0) := by
  have hc (n : ℕ) : HasCompactSupport (W n) := hK.of_isClosed_subset (isClosed_tsupport _) (hs n)
  intro T _hT
  refine ⟨shiftedSum_continuousInSobolev ha.continuous ha0 W hW hc 2 T,
    shiftedSum_c1InL2 ha ha0 W hW hc T, zeroPressure_continuousInSobolev 1 T, ?_⟩
  apply bounded_finite_cylinder (shiftedSum_smooth ha ha0 W hW) hK
  apply shiftedSum_supported
  intro n x hx
  exact notMem_tsupport_iff_eventuallyEq.mp (fun hh => hx (hs n hh)) |>.self_of_nhds

theorem constructedVelocity_energyClass (I : MachineInput) :
    EnergyClass (constructedVelocity I) (fun _ _ => 0) :=
  shiftedSum_energyClass clock_pulse_smooth (fun _ => clock_pulse_nonpos)
    (velocitySlot I) (velocitySlot_smooth I) (isCompact_closedBall 0 3) (velocitySlot_support I)

def constructedForce (ν : ℝ) (I : MachineInput) : Field := residual ν (constructedVelocity I)

theorem constructedForce_smooth (ν : ℝ) (I : MachineInput) : SmoothUpToZero (constructedForce ν I) :=
  residual_smoothUpToZero ν (constructedVelocity_contDiff I)

theorem constructedForce_support (ν : ℝ) (I : MachineInput) :
    SupportedIn (Metric.closedBall 0 3) (constructedForce ν I) :=
  residual_supported ν Metric.isClosed_closedBall (constructedVelocity_support I)

theorem constructedVelocity_nsSolution (ν : ℝ) (I : MachineInput) :
    NSSolution ν (constructedForce ν I) (constructedVelocity I) (fun _ _ => 0) :=
  nsSolution_residual ν (constructedVelocity_contDiff I) (constructedVelocity_initial_zero I)
    (fun t _ht => constructedVelocity_divergence I t)

theorem explicit_navierStokes_simulation (ν : ℝ) (I : MachineInput) (hI : ValidInput I) :
    SmoothUpToZero (constructedVelocity I) ∧ SmoothUpToZero (constructedForce ν I) ∧
    SupportedIn (Metric.closedBall 0 3) (constructedVelocity I) ∧
    SupportedIn (Metric.closedBall 0 3) (constructedForce ν I) ∧
    NSSolution ν (constructedForce ν I) (constructedVelocity I) (fun _ _ => 0) ∧
    EnergyClass (constructedVelocity I) (fun _ _ => 0) ∧
    SolvesParticle (constructedVelocity I) observedParticle (constructedTrajectory I hI) ∧
    ((∃ t : ℝ, 0 ≤ t ∧ 0 < constructedTrajectory I hI t 0) ↔ Halts I) :=
  ⟨constructedVelocity_smooth I, constructedForce_smooth ν I,
    constructedVelocity_support I, constructedForce_support ν I,
    constructedVelocity_nsSolution ν I, constructedVelocity_energyClass I,
    constructedTrajectory_solves I hI, constructedTrajectory_reaches_iff I hI⟩

end
end Alternating

end OAI
