import OAI.Dynamics.EntropyCounterexample.Map
import OAI.Dynamics.EntropyCounterexample.ClockLift

namespace OAI

noncomputable section

namespace Problem340.Construction

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

theorem liftIco_coe_of_periodic {Y : Type*} {P : ℝ} [Fact (0 < P)]
    (a : ℝ) (f : ℝ → Y) (hf : Function.Periodic f P) (t : ℝ) :
    AddCircle.liftIco P a f (t : AddCircle P) = f t := by
  change f (AddCircle.equivIco P a (t : AddCircle P)) = f t
  rw [← hf.lift_coe (AddCircle.equivIco P a (t : AddCircle P)),
    AddCircle.coe_equivIco, hf.lift_coe]

@[simp] theorem clockIncrement_coe (D : SphereData) (t : ℝ) (z : Sphere) :
    clockIncrement D (t : AddCircle (100 : ℝ)) z = Clock.increment t (D.gate z) :=
  liftIco_coe_of_periodic 0 _ (Clock.increment_periodic (D.gate z)) t

theorem clockIncrement_mem_Icc (D : SphereData)
    (hgate : ∀ z, D.gate z ∈ Set.Icc (0 : ℝ) 1)
    (t : AddCircle (100 : ℝ)) (z : Sphere) :
    clockIncrement D t z ∈ Set.Icc (0 : ℝ) 1 := by
  change Clock.increment ((AddCircle.equivIco 100 0 t : ℝ)) (D.gate z) ∈ _
  exact ⟨Clock.increment_nonneg _ (hgate z).1,
    Clock.increment_le_one _ (hgate z).2⟩

def rawClockLift (D : SphereData) (x : RawManifold) (t₀ : ℝ) : ℕ → ℝ :=
  orbitClockLift (rawMap D) (fun y => clockIncrement D y.1 y.2.1) x t₀

@[simp] theorem rawClockLift_zero (D : SphereData) (x : RawManifold) (t₀ : ℝ) :
    rawClockLift D x t₀ 0 = t₀ := by
  simp [rawClockLift]

theorem coe_rawClockLift (D : SphereData) (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1) (n : ℕ) :
    (rawClockLift D x t₀ n : AddCircle (100 : ℝ)) = ((rawMap D)^[n] x).1 :=
  coe_orbitClockLift 100 (rawMap D) _ Prod.fst (fun _ => rfl) x t₀ h₀ n

theorem rawClockLift_succ (D : SphereData) (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1) (n : ℕ) :
    rawClockLift D x t₀ (n + 1) = rawClockLift D x t₀ n +
      Clock.increment (rawClockLift D x t₀ n) (D.gate (((rawMap D)^[n] x).2.1)) := by
  change orbitClockLift _ _ _ _ (n + 1) = _
  rw [orbitClockLift_succ]
  change rawClockLift D x t₀ n + clockIncrement D ((rawMap D)^[n] x).1
    (((rawMap D)^[n] x).2.1) = _
  rw [← coe_rawClockLift D x t₀ h₀ n, clockIncrement_coe]

theorem monotone_rawClockLift (D : SphereData)
    (hgate : ∀ z, D.gate z ∈ Set.Icc (0 : ℝ) 1)
    (x : RawManifold) (t₀ : ℝ) : Monotone (rawClockLift D x t₀) :=
  monotone_orbitClockLift (rawMap D) _
    (fun y => (clockIncrement_mem_Icc D hgate y.1 y.2.1).1) x t₀

theorem rawClockLift_step_bounds (D : SphereData)
    (hgate : ∀ z, D.gate z ∈ Set.Icc (0 : ℝ) 1)
    (x : RawManifold) (t₀ : ℝ) (n : ℕ) :
    rawClockLift D x t₀ (n + 1) - rawClockLift D x t₀ n ∈ Set.Icc (0 : ℝ) 1 :=
  orbitClockLift_step_bounds (rawMap D) _
    (fun y => clockIncrement_mem_Icc D hgate y.1 y.2.1) x t₀ n

theorem exists_rawClockLift (D : SphereData)
    (hgate : ∀ z, D.gate z ∈ Set.Icc (0 : ℝ) 1) (x : RawManifold) :
    ∃ t : ℕ → ℝ,
      (∀ n, (t n : AddCircle (100 : ℝ)) = ((rawMap D)^[n] x).1) ∧
      (∀ n, t (n + 1) = t n +
        Clock.increment (t n) (D.gate (((rawMap D)^[n] x).2.1))) ∧
      Monotone t ∧ (∀ n, t (n + 1) - t n ∈ Set.Icc (0 : ℝ) 1) := by
  obtain ⟨t₀, ht₀⟩ := QuotientAddGroup.mk_surjective x.1
  exact ⟨rawClockLift D x t₀, coe_rawClockLift D x t₀ ht₀,
    rawClockLift_succ D x t₀ ht₀, monotone_rawClockLift D hgate x t₀,
    rawClockLift_step_bounds D hgate x t₀⟩

theorem coe_rawClockLift_sub_period (D : SphereData) (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1) (k : ℤ) (n : ℕ) :
    ((rawClockLift D x t₀ n - 100 * (k : ℝ) : ℝ) : AddCircle (100 : ℝ)) =
      ((rawMap D)^[n] x).1 := by
  rw [mul_comm (100 : ℝ), ← zsmul_eq_mul, AddCircle.coe_sub,
    AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero, sub_zero]
  exact coe_rawClockLift D x t₀ h₀ n

theorem rawClockLift_sub_period_succ (D : SphereData) (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1) (k : ℤ) (n : ℕ) :
    rawClockLift D x t₀ (n + 1) - 100 * (k : ℝ) =
      (rawClockLift D x t₀ n - 100 * (k : ℝ)) +
        Clock.increment (rawClockLift D x t₀ n - 100 * (k : ℝ))
          (D.gate (((rawMap D)^[n] x).2.1)) := by
  have hper := (Clock.increment_periodic (D.gate (((rawMap D)^[n] x).2.1))).sub_int_mul_eq
    (x := rawClockLift D x t₀ n) k
  rw [mul_comm (k : ℝ) 100] at hper
  rw [hper, rawClockLift_succ D x t₀ h₀ n]
  ring

theorem input_at_passage_clock (D : SphereData) (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1) (k : ℤ) (n : ℕ)
    (hs : rawClockLift D x t₀ n - 100 * (k : ℝ) ∈ Set.Ico (0 : ℝ) 100)
    (i : Fin 3) (z : Sphere) :
    input D i (((rawMap D)^[n] x).1) z =
      baseInput D i (rawClockLift D x t₀ n - 100 * (k : ℝ)) z := by
  rw [← coe_rawClockLift_sub_period D x t₀ h₀ k n]
  exact AddCircle.liftIco_coe_apply (p := (100 : ℝ)) (a := 0)
    (by simpa only [zero_add] using hs)

theorem periodicReadout_at_passage_clock (D : SphereData) (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1) (k : ℤ) (n : ℕ)
    (hs : rawClockLift D x t₀ n - 100 * (k : ℝ) ∈ Set.Ico (0 : ℝ) 100)
    (i : Fin 3) :
    periodicReadout i (((rawMap D)^[n] x).1) =
      readoutCoeff i (rawClockLift D x t₀ n - 100 * (k : ℝ)) := by
  rw [← coe_rawClockLift_sub_period D x t₀ h₀ k n]
  exact AddCircle.liftIco_coe_apply (p := (100 : ℝ)) (a := 0)
    (by simpa only [zero_add] using hs)

theorem periodicGain_at_passage_clock (D : SphereData) (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1) (k : ℤ) (n : ℕ)
    (hs : rawClockLift D x t₀ n - 100 * (k : ℝ) ∈ Set.Ico (0 : ℝ) 100) :
    periodicGain D (((rawMap D)^[n] x).1) =
      D.gain (rawClockLift D x t₀ n - 100 * (k : ℝ)) := by
  rw [← coe_rawClockLift_sub_period D x t₀ h₀ k n]
  exact AddCircle.liftIco_coe_apply (p := (100 : ℝ)) (a := 0)
    (by simpa only [zero_add] using hs)

theorem main_update_at_passage_clock (D : SphereData) (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1) (k : ℤ) (n : ℕ)
    (hs : rawClockLift D x t₀ n - 100 * (k : ℝ) ∈ Set.Ico (0 : ℝ) 100) :
    ((rawMap D)^[n + 1] x).2.1 =
      perturbedSquare (20 * ∑ i : Fin 3,
        (readoutCoeff i (rawClockLift D x t₀ n - 100 * (k : ℝ)) : ℂ) *
          D.saturation (((rawMap D)^[n] x).2.2 i)) (((rawMap D)^[n] x).2.1) := by
  rw [Function.iterate_succ_apply']
  change perturbedSquare (readout D ((rawMap D)^[n] x).1
    ((rawMap D)^[n] x).2.2) ((rawMap D)^[n] x).2.1 = _
  simp only [readout, periodicReadout_at_passage_clock D x t₀ h₀ k n hs]

theorem register_update_at_passage_clock (D : SphereData) (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1) (k : ℤ) (n : ℕ)
    (hs : rawClockLift D x t₀ n - 100 * (k : ℝ) ∈ Set.Ico (0 : ℝ) 100)
    (i : Fin 3) :
    ((rawMap D)^[n + 1] x).2.2 i =
      (((D.gain (rawClockLift D x t₀ n - 100 * (k : ℝ)) : ℂ) *
        D.saturation (((rawMap D)^[n] x).2.2 i) +
        baseInput D i (rawClockLift D x t₀ n - 100 * (k : ℝ))
          (((rawMap D)^[n] x).2.1) : ℂ) : Sphere) := by
  rw [Function.iterate_succ_apply']
  change (((periodicGain D ((rawMap D)^[n] x).1 : ℂ) *
    D.saturation (((rawMap D)^[n] x).2.2 i) +
      input D i ((rawMap D)^[n] x).1 ((rawMap D)^[n] x).2.1 : ℂ) : Sphere) = _
  rw [periodicGain_at_passage_clock D x t₀ h₀ k n hs,
    input_at_passage_clock D x t₀ h₀ k n hs]

end Problem340.Construction

end

end OAI
