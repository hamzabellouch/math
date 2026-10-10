import OAI.Dynamics.EntropyCounterexample.MapErasure

namespace OAI

noncomputable section

open Filter
open scoped OnePoint

namespace Problem340.ConstructionInfinityAttraction

open Construction ConstructionErasure

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

theorem raw_iterate_main_infty (D : SphereData) (x : RawManifold)
    (hx : x.2.1 = ∞) (n : ℕ) : ((rawMap D)^[n] x).2.1 = ∞ := by
  induction n with
  | zero => exact hx
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change perturbedSquare _ (((rawMap D)^[n] x).2.1) = ∞
      rw [ih]
      rfl

theorem clockIncrement_at_infty (D : SphereData) (hgate : D.gate ∞ = 1)
    (t : AddCircle (100 : ℝ)) : clockIncrement D t ∞ = 1 := by
  simp [clockIncrement, AddCircle.liftIco, hgate]

theorem raw_iterate_clock_at_infty (D : SphereData) (hgate : D.gate ∞ = 1)
    (x : RawManifold) (hx : x.2.1 = ∞) (n : ℕ) :
    ((rawMap D)^[n] x).1 = x.1 + ((n : ℝ) : AddCircle (100 : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change ((rawMap D)^[n] x).1 +
        ((clockIncrement D ((rawMap D)^[n] x).1 (((rawMap D)^[n] x).2.1) : ℝ) :
          AddCircle (100 : ℝ)) = _
      rw [raw_iterate_main_infty D x hx n, clockIncrement_at_infty D hgate, ih]
      simp only [Nat.cast_add, Nat.cast_one, AddCircle.coe_add, add_assoc]

theorem rawMap_eventually_infinity_cylinder
    (D : SphereData) (hgate : D.gate ∞ = 1)
    (hS : D.saturation ((0 : ℂ) : Sphere) = 0)
    (hgain : ∀ s ∈ Set.Icc (2 : ℝ) 5, D.gain s = 0)
    (x : RawManifold) (hx : x.2.1 = ∞) :
    ∀ᶠ n in atTop, ((rawMap D)^[n] x).2 =
      (∞, fun _ : Fin 3 => ((0 : ℂ) : Sphere)) := by
  obtain ⟨t₀, ht₀⟩ := QuotientAddGroup.mk_surjective x.1
  let t : ℕ → ℝ := fun n => t₀ + n
  have hclock : ∀ n, ((rawMap D)^[n] x).1 = (t n : AddCircle (100 : ℝ)) := by
    intro n
    rw [raw_iterate_clock_at_infty D hgate x hx n]
    simp only [t, AddCircle.coe_add, ht₀]
  have ht : Monotone t := by
    intro n m hnm
    exact add_le_add (le_refl t₀) (Nat.cast_le.mpr hnm)
  have htop : Tendsto t atTop atTop := by
    exact tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
  have hstep : ∀ n, t (n + 1) ≤ t n + 1 := by
    intro n
    simp [t, Nat.cast_add, add_assoc]
  have hreset : ∀ N : ℕ, ∃ n, N ≤ n ∧ periodicGain D (((rawMap D)^[n] x).1) = 0 := by
    intro N
    obtain ⟨n, hn, hz⟩ := RegisterErasure.recurring_zero_periodic_gain t
      (fun s : ℝ => periodicGain D (s : AddCircle (100 : ℝ)))
      (periodicGain_lift_periodic D) (periodicGain_lift_reset D hgain) ht htop hstep N
    exact ⟨n, hn, by rw [hclock n]; exact hz⟩
  have hregs : ∀ᶠ n in atTop, ∀ i : Fin 3,
      ((rawMap D)^[n] x).2.2 i = ((0 : ℂ) : Sphere) := by
    apply RegisterErasure.eventually_all_base_of_recurring_reset
      ((0 : ℂ) : Sphere) (fun z : ℂ => (z : Sphere)) rfl D.saturation hS
      (fun n => periodicGain D (((rawMap D)^[n] x).1))
      (fun n i => input D i (((rawMap D)^[n] x).1) (((rawMap D)^[n] x).2.1))
      (fun n => ((rawMap D)^[n] x).2.2)
    · intro n i
      rw [Function.iterate_succ_apply']
      simp only [rawMap, Complex.real_smul]
    · apply Filter.Eventually.of_forall
      intro n i
      rw [raw_iterate_main_infty D x hx n]
      exact input_infty D i _
    · exact hreset
  filter_upwards [hregs] with n hn
  exact Prod.ext (raw_iterate_main_infty D x hx n) (funext hn)

end Problem340.ConstructionInfinityAttraction

end

end OAI
