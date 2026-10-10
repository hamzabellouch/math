import OAI.Dynamics.EntropyCounterexample.ClockCharts
import OAI.Dynamics.EntropyCounterexample.C1Coordinates

namespace OAI

noncomputable section

open scoped ContDiff

namespace Problem340

def clockLocalLift (t₀ : ℝ) (x : ClockAmbient) : ℝ :=
  t₀ + (100 / (2 * Real.pi)) *
    Complex.arg (complexClockLinearIsometry.symm x /
      Complex.exp ((2 * Real.pi / 100 * t₀ : ℝ) * Complex.I))

theorem clockHomeomorph_clockLocalLift (t₀ : ℝ) (x : StandardClock) :
    clockHomeomorph ((clockLocalLift t₀ x.1 : ℝ) : AddCircle (100 : ℝ)) = x := by
  let c : Circle := circleClockHomeomorph.symm x
  let c₀ : Circle := AddCircle.toCircle (t₀ : AddCircle (100 : ℝ))
  have hc : (c : ℂ) = complexClockLinearIsometry.symm x.1 := rfl
  have hc₀ : (c₀ : ℂ) = Complex.exp ((2 * Real.pi / 100 * t₀ : ℝ) * Complex.I) := rfl
  have hlift : clockLocalLift t₀ x.1 =
      t₀ + (100 / (2 * Real.pi)) * Complex.arg ((c / c₀ : Circle) : ℂ) := by
    simp only [clockLocalLift, Circle.coe_div, hc, hc₀]
  have hangle : (2 * Real.pi / 100) *
      (t₀ + (100 / (2 * Real.pi)) * Complex.arg ((c / c₀ : Circle) : ℂ)) =
      (2 * Real.pi / 100) * t₀ + Complex.arg ((c / c₀ : Circle) : ℂ) := by
    field_simp
  rw [clockHomeomorph_apply, hlift, AddCircle.toCircle_apply_mk, hangle, Circle.exp_add,
    Circle.exp_arg]
  change circleClockHomeomorph (c₀ * (c / c₀)) = x
  simp [c, div_eq_mul_inv, mul_comm]

theorem contDiffOn_arg_slitPlane {n : ℕ∞ω} :
    ContDiffOn ℝ n Complex.arg Complex.slitPlane := by
  intro z hz
  have hlog : ContDiffAt ℝ n Complex.log z :=
    (Complex.contDiffAt_log hz).restrict_scalars ℝ
  have h := Complex.imCLM.contDiff.contDiffAt.comp z hlog
  have heq : (Complex.imCLM ∘ Complex.log) = Complex.arg := by
    funext w
    exact Complex.log_im w
  rw [heq] at h
  exact h.contDiffWithinAt

theorem clockLocalLift_extension (t₀ : ℝ) {n : ℕ∞ω} :
    ∃ U : Set ClockAmbient, IsOpen U ∧ clockParam t₀ ∈ U ∧
      ContDiffOn ℝ n (clockLocalLift t₀) U := by
  let D : ClockAmbient → ℂ := fun x => complexClockLinearIsometry.symm x /
    Complex.exp ((2 * Real.pi / 100 * t₀ : ℝ) * Complex.I)
  have hD : ContDiff ℝ n D :=
    complexClockLinearIsometry.symm.toContinuousLinearEquiv.contDiff.div_const _
  have hbase : D (clockParam t₀) = 1 := by
    simp [D, clockParam, Complex.exp_ne_zero]
  refine ⟨D ⁻¹' Complex.slitPlane, Complex.isOpen_slitPlane.preimage hD.continuous,
    ?_, ?_⟩
  · change D (clockParam t₀) ∈ Complex.slitPlane
    rw [hbase]
    exact Complex.one_mem_slitPlane
  · exact contDiffOn_const.add (contDiffOn_const.mul
      (contDiffOn_arg_slitPlane.comp hD.contDiffOn fun _ hx => hx))

theorem hasLocalC1Extension_of_clock_lift
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : StandardClock → F)
    (hf : ContDiff ℝ 1 (fun t : ℝ => f (clockHomeomorph (t : AddCircle (100 : ℝ))))) :
    HasLocalC1Extension (fun x : StandardClock => x.1) f := by
  intro x
  obtain ⟨t, rfl⟩ := clockHomeomorph.surjective x
  induction t using QuotientAddGroup.induction_on with
  | H t =>
    obtain ⟨U, hU, htU, hlocal⟩ := clockLocalLift_extension t (n := 1)
    refine ⟨U, hU, ?_,
      fun y => f (clockHomeomorph ((clockLocalLift t y : ℝ) : AddCircle (100 : ℝ))),
      hf.comp_contDiffOn hlocal, ?_⟩
    · simpa only [clockHomeomorph_coe] using htU
    · intro y _
      change f y = f (clockHomeomorph ((clockLocalLift t y.1 : ℝ) : AddCircle (100 : ℝ)))
      rw [clockHomeomorph_clockLocalLift]

theorem hasLocalC1Extension_of_clock_lift_with_parameters
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : StandardClock × E → F)
    (hf : ContDiff ℝ 1 (fun p : ℝ × E =>
      f (clockHomeomorph (p.1 : AddCircle (100 : ℝ)), p.2))) :
    HasLocalC1Extension (fun x : StandardClock × E => (x.1.1, x.2)) f := by
  rintro ⟨x, a⟩
  obtain ⟨t, rfl⟩ := clockHomeomorph.surjective x
  induction t using QuotientAddGroup.induction_on with
  | H t =>
    obtain ⟨U, hU, htU, hlocal⟩ := clockLocalLift_extension t (n := 1)
    refine ⟨U ×ˢ Set.univ, hU.prod isOpen_univ,
      ⟨?_, Set.mem_univ a⟩,
      fun p : ClockAmbient × E =>
        f (clockHomeomorph ((clockLocalLift t p.1 : ℝ) : AddCircle (100 : ℝ)), p.2),
      ?_, ?_⟩
    · simpa only [clockHomeomorph_coe] using htU
    · have hfst : ContDiffOn ℝ 1 (fun p : ClockAmbient × E => clockLocalLift t p.1)
          (U ×ˢ Set.univ) :=
        hlocal.comp contDiffOn_fst (fun _ hx => hx.1)
      have hpair : ContDiffOn ℝ 1
          (fun p : ClockAmbient × E => (clockLocalLift t p.1, p.2))
          (U ×ˢ Set.univ) := hfst.prodMk contDiffOn_snd
      convert hf.comp_contDiffOn hpair using 1
      rfl
    · rintro ⟨y, b⟩ _
      change f (y, b) =
        f (clockHomeomorph ((clockLocalLift t y.1 : ℝ) : AddCircle (100 : ℝ)), b)
      rw [clockHomeomorph_clockLocalLift]

def clockFunction {F : Type*} (b : ℝ → F) (hb : Function.Periodic b 100) :
    StandardClock → F := hb.lift ∘ clockHomeomorph.symm

@[simp]
theorem clockFunction_param {F : Type*} (b : ℝ → F)
    (hb : Function.Periodic b 100) (t : ℝ) :
    clockFunction b hb (clockHomeomorph (t : AddCircle (100 : ℝ))) = b t := by
  change hb.lift (clockHomeomorph.symm (clockHomeomorph (t : AddCircle (100 : ℝ)))) = b t
  rw [clockHomeomorph.symm_apply_apply]
  rfl

theorem hasLocalC1Extension_clockFunction
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : ℝ → F) (hb : Function.Periodic b 100) (hcont : ContDiff ℝ 1 b) :
    HasLocalC1Extension (fun x : StandardClock => x.1) (clockFunction b hb) := by
  apply hasLocalC1Extension_of_clock_lift
  simpa only [clockFunction_param] using hcont

theorem hasLocalC1Extension_of_clock_lift_on
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : Set E} (hV : IsOpen V) (f : StandardClock × E → F)
    (hf : ContDiffOn ℝ 1 (fun p : ℝ × E =>
      f (clockHomeomorph (p.1 : AddCircle (100 : ℝ)), p.2)) (Set.univ ×ˢ V)) :
    HasLocalC1Extension (fun x : StandardClock × V => (x.1.1, x.2.1))
      (fun x => f (x.1, x.2.1)) := by
  rintro ⟨x, a⟩
  obtain ⟨t, rfl⟩ := clockHomeomorph.surjective x
  induction t using QuotientAddGroup.induction_on with
  | H t =>
    obtain ⟨U, hU, htU, hlocal⟩ := clockLocalLift_extension t (n := 1)
    refine ⟨U ×ˢ V, hU.prod hV, ⟨?_, a.2⟩,
      fun p : ClockAmbient × E =>
        f (clockHomeomorph ((clockLocalLift t p.1 : ℝ) : AddCircle (100 : ℝ)), p.2),
      ?_, ?_⟩
    · simpa only [clockHomeomorph_coe] using htU
    · have hfst : ContDiffOn ℝ 1 (fun p : ClockAmbient × E => clockLocalLift t p.1)
          (U ×ˢ V) := hlocal.comp contDiffOn_fst (fun _ hx => hx.1)
      have hpair : ContDiffOn ℝ 1
          (fun p : ClockAmbient × E => (clockLocalLift t p.1, p.2)) (U ×ˢ V) :=
        hfst.prodMk contDiffOn_snd
      have hmaps : Set.MapsTo (fun p : ClockAmbient × E => (clockLocalLift t p.1, p.2))
          (U ×ˢ V) (Set.univ ×ˢ V) := fun _ hp => ⟨Set.mem_univ _, hp.2⟩
      convert hf.comp hpair hmaps using 1
      rfl
    · rintro ⟨y, b⟩ _
      change f (y, b.1) =
        f (clockHomeomorph ((clockLocalLift t y.1 : ℝ) : AddCircle (100 : ℝ)), b.1)
      rw [clockHomeomorph_clockLocalLift]

end Problem340

end

end OAI
