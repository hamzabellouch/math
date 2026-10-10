import OAI.Combinatorics.EditApproximation.Refinement.PhysicalBoundsAllSeeds
import Mathlib.Data.Rat.Lemmas

namespace OAI

/-! The actual returned values have one additional fixed denominator per tree level. -/

namespace EditApproximation

open Finset

theorem rat_den_add_dvd {D : ℕ} {x y : ℚ} (hx : x.den ∣ D) (hy : y.den ∣ D) :
    (x + y).den ∣ D := (Rat.add_den_dvd_lcm x y).trans (Nat.lcm_dvd hx hy)

theorem rat_den_min_dvd {D : ℕ} {x y : ℚ} (hx : x.den ∣ D) (hy : y.den ∣ D) :
    (min x y).den ∣ D := by
  by_cases h : x ≤ y
  · simpa only [min_eq_left h] using hx
  · simpa only [min_eq_right (le_of_not_ge h)] using hy

theorem rat_den_max_dvd {D : ℕ} {x y : ℚ} (hx : x.den ∣ D) (hy : y.den ∣ D) :
    (max x y).den ∣ D := by
  by_cases h : x ≤ y
  · simpa only [max_eq_right h] using hy
  · simpa only [max_eq_left (le_of_not_ge h)] using hx

theorem rat_den_sum_dvd {ι : Type*} (s : Finset ι) (f : ι → ℚ) (D : ℕ)
    (hf : ∀ i ∈ s, (f i).den ∣ D) : (∑ i ∈ s, f i).den ∣ D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty, Rat.den_zero, one_dvd]
  | @insert i s hi ih =>
    rw [sum_insert hi]
    exact rat_den_add_dvd (hf i (mem_insert_self _ _))
      (ih fun j hj => hf j (mem_insert_of_mem hj))

theorem rationalMinimum_den_dvd (fallback : ℚ) (values : List ℚ) (D : ℕ)
    (hfallback : fallback.den ∣ D) (hvalues : ∀ v ∈ values, v.den ∣ D) :
    (rationalMinimum fallback values).den ∣ D := by
  induction values with
  | nil => exact hfallback
  | cons v rest ih =>
    exact rat_den_min_dvd (hvalues v (by simp)) (ih fun w hw => hvalues w (by simp [hw]))

theorem rationalActualWideActions_connection_den {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (action : PhysicalRationalAction M ny)
    (ha : action ∈ rationalActualWideActions parent representatives P) : action.connection.den = 1 := by
  obtain ⟨br, _, hmem⟩ := List.mem_flatMap.mp ha
  obtain ⟨states, _, rfl⟩ := List.mem_map.mp hmem
  exact Rat.den_natCast _

theorem rationalActionValue_den_dvd {Parent Child : Type*} {M D : ℕ}
    (distance : Parent → Parent → ℚ) (L : ℚ) (child : Child → ℚ)
    (q : Parent) (action : RationalBellmanAction Parent Child M)
    (hdistance : (distance q action.center).den = 1) (hL : L.den = 1)
    (ha : action.connection.den = 1) (hchild : ∀ i, (child (action.childState i)).den ∣ D) :
    (rationalActionValue distance L child q action).den ∣ D := by
  unfold rationalActionValue
  apply rat_den_add_dvd
  · apply rat_den_add_dvd
    · have h := Rat.mul_den_dvd L (distance q action.center)
      rw [hL, hdistance, one_mul] at h
      exact h.trans (one_dvd D)
    · rw [ha]
      exact one_dvd D
  · exact rat_den_sum_dvd univ _ D (fun i _ => hchild i)

theorem stageInitial_den_one {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (state : PhysicalEntry M J target.length) :
    (stageInitial source target U N P F A state).den = 1 := by
  have hmin (fallback : ℚ) (values : List ℚ) (hf : fallback.den = 1)
      (hv : ∀ v ∈ values, v.den = 1) : (rationalMinimum fallback values).den = 1 :=
    Nat.eq_one_of_dvd_one (rationalMinimum_den_dvd fallback values 1 (by rw [hf])
      (fun v h => by rw [hv v h]))
  unfold stageInitial physicalInitialTable
  dsimp only
  split_ifs
  · exact Rat.den_natCast _
  · unfold localInitialConeTable
    split_ifs
    · exact Rat.den_zero
    · apply hmin
      · simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
          Rat.den_natCast ((32 * F + 1) * N)
      · intro v hv
        obtain ⟨r, _, rfl⟩ := List.mem_map.mp hv
        unfold initialConeValue scaledSeedValue
        apply Nat.eq_one_of_dvd_one
        apply rat_den_add_dvd
        · apply rat_den_max_dvd
          · simp only [Rat.den_natCast, dvd_refl]
          · have heq : rationalStateGap (physicalSource source state.1) target r =
                (((r.hi : ℤ) - r.lo - (physicalSource source state.1).length : ℤ) : ℚ) := by
              simp only [rationalStateGap, Int.cast_sub, Int.cast_natCast]
            rw [heq, ← Int.cast_abs]
            simp only [Rat.den_intCast, dvd_refl]
        · have heq : (32 * F : ℚ) * targetEndpointDistance state.2 r =
              ((32 * F * targetEndpointDistance state.2 r : ℕ) : ℚ) := by push_cast; rfl
          rw [heq, Rat.den_natCast]

theorem rationalPhysicalBellman_den_dvd {α : Type*} {M J D : ℕ}
    (source target : List α) (P F : ℕ)
    (initial : PhysicalEntry M J target.length → ℚ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (hinitial : ∀ state, (initial state).den ∣ D)
    (value : PhysicalEntry M J target.length → ℚ)
    (hvalue : ∀ state, (value state).den ∣ D) (state : PhysicalEntry M J target.length) :
    (rationalPhysicalBellman source target P (128 * F) initial representatives value state).den ∣ D := by
  unfold rationalPhysicalBellman
  dsimp only
  split_ifs
  · exact hinitial state
  · apply rationalMinimum_den_dvd _ _ D (hinitial state)
    intro v hv
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
    exact rationalActionValue_den_dvd _ _ _ _ _ (Rat.den_natCast _)
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using Rat.den_natCast (128 * F))
      (rationalActualWideActions_connection_den _ _ _ action ha) (fun i => hvalue _)
  · exact hinitial state

theorem stageWarmup_den_one {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (t : ℕ) (state : PhysicalEntry M J target.length) :
    (stageWarmup source target U N P F A t state).den = 1 := by
  induction t generalizing state with
  | zero => exact stageInitial_den_one source target U N P F A state
  | succ t ih =>
    apply Nat.eq_one_of_dvd_one
    exact rationalPhysicalBellman_den_dvd source target P F _ _
      (fun s => by rw [stageInitial_den_one source target U N P F A s]) _ (fun s => by
        change (stageWarmup source target U N P F A t s).den ∣ 1
        rw [ih s]) state

theorem rat_inverse_shift_den_dvd (m : ℕ) (hm : 0 < m) :
    (1 / (1 + 1 / (m : ℚ))).den ∣ m + 1 := by
  have hmp : (0 : ℚ) < m := by exact_mod_cast hm
  have heq : (1 / (1 + 1 / (m : ℚ))) = (m : ℚ) / (m + 1 : ℕ) := by
    push_cast
    field_simp
  rw [heq]
  have h : (((m : ℚ) / (m + 1 : ℕ)).den : ℤ) ∣ (m + 1 : ℕ) := by
    simpa only [Rat.divInt_eq_div, Int.cast_natCast] using Rat.den_dvd (m : ℤ) (m + 1 : ℕ)
  exact Int.natCast_dvd_natCast.mp h

theorem rationalRefinementUpdate_den_dvd (m D : ℕ) (hm : 0 < m)
    (cone : ℚ) (online : Option ℚ) (hcone : cone.den ∣ D)
    (honline : ∀ v, online = some v → v.den ∣ D) :
    (rationalRefinementUpdate (1 / (m : ℚ)) cone online).den ∣ D * (m + 1) := by
  have hstep : D ∣ D * (m + 1) := dvd_mul_right _ _
  cases online with
  | none => exact hcone.trans hstep
  | some v =>
    apply rat_den_min_dvd (hcone.trans hstep)
    apply rat_den_max_dvd _ ((honline v rfl).trans hstep)
    rw [div_eq_mul_one_div]
    exact (Rat.mul_den_dvd cone _).trans (Nat.mul_dvd_mul hcone (rat_inverse_shift_den_dvd m hm))

theorem rationalOnlineMinimum_den_dvd (values : List ℚ) (D : ℕ)
    (hvalues : ∀ v ∈ values, v.den ∣ D) (v : ℚ)
    (heq : rationalOnlineMinimum values = some v) : v.den ∣ D := by
  cases values with
  | nil => cases heq
  | cons first rest =>
    have hv : rationalMinimum first rest = v := Option.some.inj heq
    rw [← hv]
    exact rationalMinimum_den_dvd first rest D (hvalues first (by simp))
      (fun w hw => hvalues w (by simp [hw]))

theorem rationalWideStep_den_dvd {nx ny M D : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P F m : ℕ) (hm : 0 < m)
    (initial : TargetInterval ny → ℚ) (hinitial : ∀ q, (initial q).den ∣ D)
    (old current : Fin M × TargetInterval ny → ℚ)
    (hold : ∀ is, (old is).den ∣ D) (hcurrent : ∀ is, (current is).den ∣ D)
    (groups online : List (PhysicalRationalAction M ny))
    (hgroups : ∀ a ∈ groups, a ∈ rationalActualWideActions parent representatives P)
    (honline : ∀ a ∈ online, a ∈ rationalActualWideActions parent representatives P)
    (q : TargetInterval ny) :
    (rationalWideStep parent representatives P initial (128 * F) (1 / (m : ℚ))
      old current groups online q).den ∣ D * (m + 1) := by
  have hvalue (child : Fin M × TargetInterval ny → ℚ) (hchild : ∀ is, (child is).den ∣ D)
      (action : PhysicalRationalAction M ny) (ha : action ∈ rationalActualWideActions parent representatives P) :
      (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F) child q action).den ∣ D :=
    rationalActionValue_den_dvd _ _ _ _ _ (Rat.den_natCast _)
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using Rat.den_natCast (128 * F))
      (rationalActualWideActions_connection_den _ _ _ action ha) (fun i => hchild _)
  unfold rationalWideStep
  apply rationalRefinementUpdate_den_dvd m D hm
  · unfold rationalWideStepCone rationalBellman
    apply rationalMinimum_den_dvd
    · apply rationalMinimum_den_dvd _ _ D (hinitial q)
      intro v hv
      obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
      exact hvalue old hold action ha
    · intro v hv
      obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
      exact hvalue current hcurrent action (hgroups action ha)
  · intro v hv
    apply rationalOnlineMinimum_den_dvd _ D _ v hv
    intro w hw
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hw
    exact hvalue current hcurrent action (honline action ha)

theorem physicalRefinement_den_dvd {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T ell : ℕ) (hell : 0 < ell)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J) (t : ℕ)
    (q : TargetInterval target.length) :
    (physicalRefinement source target U N P F A T (1 / (ell : ℚ) ^ 10) choices node t q).den ∣
      (ell ^ 10 + 1) ^ (J - node.1.val) := by
  have hdelta : (1 / (ell : ℚ) ^ 10) = 1 / ((ell ^ 10 : ℕ) : ℚ) := by rw [Nat.cast_pow]
  by_cases hbelow : node.1.val < J
  · by_cases hleaf : (physicalSourceInterval source.length node).hi -
        (physicalSourceInterval source.length node).lo ≤ 1
    · rw [physicalRefinement_at_terminal source target U N P F A T _ choices node (Or.inr hleaf),
        stageInitial_den_one source target U N P F A]
      exact one_dvd _
    · cases t with
      | zero =>
        rw [physicalRefinement_zero source target U N P F A T _ choices node q,
          stageWarmup_den_one source target U N P F A]
        exact one_dvd _
      | succ t =>
        rw [physicalRefinement_succ source target U N P F A T _ choices node hbelow hleaf]
        dsimp only
        have hheight : J - node.1.val = (J - (node.1.val + 1)) + 1 := by omega
        rw [hheight]
        conv_rhs => rw [pow_succ]
        rw [hdelta]
        apply rationalWideStep_den_dvd _ _ P F (ell ^ 10) (pow_pos hell 10)
        · intro r
          rw [stageInitial_den_one source target U N P F A]
          exact one_dvd _
        · intro is
          simpa only [Nat.cast_pow, physicalChild] using physicalRefinement_den_dvd source target U N P F A T ell hell choices
            (physicalChild node hbelow is.1) t is.2
        · intro is
          simpa only [Nat.cast_pow, physicalChild] using physicalRefinement_den_dvd source target U N P F A T ell hell choices
            (physicalChild node hbelow is.1) (t + 1) is.2
        · exact choices.groups_mem node _ (t + 1)
        · exact choices.online_mem node _ (t + 1) q
  · rw [physicalRefinement_at_terminal source target U N P F A T _ choices node (Or.inl hbelow),
      stageInitial_den_one source target U N P F A]
    exact one_dvd _
termination_by J - node.1.val
decreasing_by
  all_goals
    unfold physicalChild
    dsimp only
    omega

end EditApproximation

end OAI
