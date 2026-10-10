import OAI.Dynamics.EntropyCounterexample.Map
import OAI.Dynamics.EntropyCounterexample.RegisterErasure

namespace OAI

noncomputable section

open Filter
open scoped OnePoint

namespace Problem340.ConstructionErasure

open Construction

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

lemma inputTerm_eq_zero_of_cutoff (D : SphereData) (z : Sphere)
    (hz : D.cutoff z = 0) (i : Fin 3) (n : ℕ) (t : ℝ) :
    inputTerm D i n t z = 0 := by
  simp [inputTerm, hz]

lemma baseInput_eq_zero_of_cutoff (D : SphereData) (z : Sphere)
    (hz : D.cutoff z = 0) (i : Fin 3) (t : ℝ) :
    baseInput D i t z = 0 := by
  simp [baseInput, inputTerm_eq_zero_of_cutoff D z hz]

lemma input_eq_zero_of_cutoff (D : SphereData) (z : Sphere)
    (hz : D.cutoff z = 0) (i : Fin 3) (t : AddCircle (100 : ℝ)) :
    input D i t z = 0 := by
  simp [input, AddCircle.liftIco, baseInput_eq_zero_of_cutoff D z hz]

lemma periodicGain_lift_periodic (D : SphereData) :
    Function.Periodic (fun t : ℝ => periodicGain D (t : AddCircle (100 : ℝ))) 100 := by
  intro t
  simp only [AddCircle.coe_add, AddCircle.coe_period, add_zero]

lemma periodicGain_lift_reset (D : SphereData)
    (hgain : ∀ s ∈ Set.Icc (2 : ℝ) 5, D.gain s = 0)
    (s : ℝ) (hs : s ∈ Set.Icc (2 : ℝ) 5) :
    periodicGain D (s : AddCircle (100 : ℝ)) = 0 := by
  rw [periodicGain, AddCircle.liftIco_zero_coe_apply (show s ∈ Set.Ico (0 : ℝ) 100 by
    constructor <;> linarith [hs.1, hs.2])]
  exact hgain s hs

theorem rawMap_registers_eventually_zero
    (D : SphereData) (x : RawManifold) (t : ℕ → ℝ)
    (hS : D.saturation ((0 : ℂ) : Sphere) = 0)
    (hgain : ∀ s ∈ Set.Icc (2 : ℝ) 5, D.gain s = 0)
    (hclock : ∀ n, ((rawMap D)^[n] x).1 = (t n : AddCircle (100 : ℝ)))
    (ht : Monotone t) (htop : Tendsto t atTop atTop)
    (hstep : ∀ n, t (n + 1) ≤ t n + 1)
    (hcutoff : ∀ᶠ n in atTop, D.cutoff (((rawMap D)^[n] x).2.1) = 0) :
    ∀ᶠ n in atTop, ∀ i : Fin 3, ((rawMap D)^[n] x).2.2 i = ((0 : ℂ) : Sphere) := by
  apply RegisterErasure.eventually_all_base_of_recurring_reset
    ((0 : ℂ) : Sphere) (fun z : ℂ => (z : Sphere)) rfl
    D.saturation hS
    (fun n => periodicGain D (((rawMap D)^[n] x).1))
    (fun n i => input D i (((rawMap D)^[n] x).1) (((rawMap D)^[n] x).2.1))
    (fun n => ((rawMap D)^[n] x).2.2)
  · intro n i
    rw [Function.iterate_succ_apply']
    simp only [rawMap, Complex.real_smul]
  · filter_upwards [hcutoff] with n hn i
    exact input_eq_zero_of_cutoff D _ hn i _
  · intro N
    obtain ⟨n, hn, hzero⟩ := RegisterErasure.recurring_zero_periodic_gain t
      (fun s : ℝ => periodicGain D (s : AddCircle (100 : ℝ)))
      (periodicGain_lift_periodic D) (periodicGain_lift_reset D hgain)
      ht htop hstep N
    exact ⟨n, hn, by rw [hclock]; exact hzero⟩

theorem rawMap_registers_eventually_zero_of_norm_escape
    (D : SphereData) (x : RawManifold) (t : ℕ → ℝ) (z : ℕ → ℂ)
    (hS : D.saturation ((0 : ℂ) : Sphere) = 0)
    (hgain : ∀ s ∈ Set.Icc (2 : ℝ) 5, D.gain s = 0)
    (hclock : ∀ n, ((rawMap D)^[n] x).1 = (t n : AddCircle (100 : ℝ)))
    (hmain : ∀ n, ((rawMap D)^[n] x).2.1 = (z n : Sphere))
    (ht : Monotone t) (htop : Tendsto t atTop atTop)
    (hstep : ∀ n, t (n + 1) ≤ t n + 1)
    (hχ : HasCompactSupport (fun w : ℂ => D.cutoff (w : Sphere)))
    (hz : Tendsto (fun n => ‖z n‖) atTop atTop) :
    ∀ᶠ n in atTop, ∀ i : Fin 3, ((rawMap D)^[n] x).2.2 i = ((0 : ℂ) : Sphere) := by
  apply rawMap_registers_eventually_zero D x t hS hgain hclock ht htop hstep
  have he := RegisterErasure.eventually_cutoff_zero_of_norm_escape
    (fun w : ℂ => D.cutoff (w : Sphere)) hχ z hz
  filter_upwards [he] with n hn
  simpa only [hmain] using hn

lemma clockIncrement_infty (D : SphereData) (hgate : D.gate ∞ = 1)
    (t : AddCircle (100 : ℝ)) : clockIncrement D t ∞ = 1 := by
  simp [clockIncrement, hgate, AddCircle.liftIco]

theorem rawMap_orbit_infty (D : SphereData) (hgate : D.gate ∞ = 1)
    (t₀ : ℝ) (v : Fin 3 → Sphere) :
    ∀ n, ((rawMap D)^[n] ((t₀ : AddCircle (100 : ℝ)), ∞, v)).1 =
        ((t₀ + n : ℝ) : AddCircle (100 : ℝ)) ∧
      ((rawMap D)^[n] ((t₀ : AddCircle (100 : ℝ)), ∞, v)).2.1 = ∞ := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      constructor
      · change (((rawMap D)^[n] ((t₀ : AddCircle (100 : ℝ)), ∞, v)).1 +
          (clockIncrement D _ _ : ℝ)) = _
        rw [ih.2, clockIncrement_infty D hgate, ih.1]
        simp [Nat.cast_add, Nat.cast_one, add_assoc]
      · change perturbedSquare _ (((rawMap D)^[n] _).2.1) = ∞
        rw [ih.2]
        rfl

theorem rawMap_infty_registers_eventually_zero
    (D : SphereData) (t₀ : ℝ) (v : Fin 3 → Sphere)
    (hgate : D.gate ∞ = 1) (hχ : D.cutoff ∞ = 0)
    (hS : D.saturation ((0 : ℂ) : Sphere) = 0)
    (hgain : ∀ s ∈ Set.Icc (2 : ℝ) 5, D.gain s = 0) :
    ∀ᶠ n in atTop, ∀ i : Fin 3,
      ((rawMap D)^[n] ((t₀ : AddCircle (100 : ℝ)), ∞, v)).2.2 i = ((0 : ℂ) : Sphere) := by
  apply rawMap_registers_eventually_zero D ((t₀ : AddCircle (100 : ℝ)), ∞, v)
    (fun n => t₀ + n) hS hgain
  · intro n
    exact (rawMap_orbit_infty D hgate t₀ v n).1
  · intro m n hmn
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  · exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => t₀) atTop (nhds t₀)).add_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
  · intro n
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  · exact Eventually.of_forall (fun n => by rw [(rawMap_orbit_infty D hgate t₀ v n).2, hχ])

end Problem340.ConstructionErasure

end

end OAI
