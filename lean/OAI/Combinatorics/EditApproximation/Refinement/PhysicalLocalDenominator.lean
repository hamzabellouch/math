import OAI.Combinatorics.EditApproximation.Refinement.PhysicalValueBits
import OAI.Combinatorics.EditApproximation.Geometry.LocalOnlineProgram

namespace OAI

/-! Denominator and bit bounds for the local evaluator on every incoming
seed.  The proofs use the literal local candidates and do not pass through
the good-seed equality with the complete evaluator. -/

namespace EditApproximation

open Finset

theorem physicalLocalWarmup_den_one {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (t : ℕ) (state : PhysicalEntry M J target.length) :
    (physicalLocalWarmup source target U N P F A t state).den = 1 := by
  induction t generalizing state with
  | zero => exact stageInitial_den_one source target U N P F A state
  | succ t ih =>
    rw [physicalLocalWarmup]
    split_ifs
    · exact stageInitial_den_one source target U N P F A state
    · apply Nat.eq_one_of_dvd_one
      apply rationalMinimum_den_dvd
      · rw [stageInitial_den_one source target U N P F A]
      · intro v hv
        obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
        exact rationalActionValue_den_dvd _ _ _ _ _ (Rat.den_natCast _)
          (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using Rat.den_natCast (128 * F))
          (rationalActualWideActions_connection_den _ _ _ action ha)
          (fun i => by rw [ih])
    · exact stageInitial_den_one source target U N P F A state

theorem rationalLocalWideStep_den_dvd {α : Type*} (source target : List α) {M D : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q m : ℕ) (hm : 0 < m)
    (tau a : ℚ) (parentInitial : TargetInterval target.length → ℚ)
    (childMass childInitial old current : Fin M → TargetInterval target.length → ℚ)
    (draw : CellGroupDraws M F Q) (online : List (PhysicalRationalAction M target.length))
    (hinitial : ∀ q, (parentInitial q).den ∣ D)
    (hold : ∀ i r, (old i r).den ∣ D) (hcurrent : ∀ i r, (current i r).den ∣ D)
    (honline : ∀ action ∈ online, action.connection.den = 1)
    (q : TargetInterval target.length) :
    (rationalLocalWideStep source target parent N P F exponent Q tau a (1 / (m : ℚ))
      parentInitial childMass childInitial old current draw online q).den ∣ D * (m + 1) := by
  have hvalue (child : Fin M → TargetInterval target.length → ℚ)
      (hchild : ∀ i r, (child i r).den ∣ D)
      (action : PhysicalRationalAction M target.length) (hconn : action.connection.den = 1) :
      (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
        (fun is => child is.1 is.2) q action).den ∣ D :=
    rationalActionValue_den_dvd _ _ _ _ _ (Rat.den_natCast _)
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using Rat.den_natCast (128 * F))
      hconn (fun i => hchild _ _)
  unfold rationalLocalWideStep
  apply rationalRefinementUpdate_den_dvd m D hm
  · apply rationalMinimum_den_dvd
    · apply rationalMinimum_den_dvd _ _ D (hinitial q)
      intro v hv
      obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
      exact hvalue old hold action (rationalActualWideActions_connection_den _ _ _ action ha)
    · intro v hv
      obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
      have hwide := completeCellGroupActions_wide source target parent N P F exponent Q tau a
        parentInitial childMass childInitial current draw action
        (localCellGroupActions_subset source target parent N P F exponent Q tau a parentInitial
          childMass childInitial current draw q action ha)
      exact hvalue current hcurrent action (rationalActualWideActions_connection_den _ _ _ action hwide)
  · intro v hv
    apply rationalOnlineMinimum_den_dvd _ D _ v hv
    intro value hvalueMem
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hvalueMem
    exact hvalue current hcurrent action (honline action ha)

theorem keyedOnlineCandidate_connection_den {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b : ℕ) (tau eta kappa : ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (children : PhysicalChildTables M target.length) (t : ℕ)
    (r : TargetInterval target.length) (integer : ℕ) (action : PhysicalRationalAction M target.length)
    (h : keyedOnlineCandidate source target parent P F exponent H b tau eta kappa
      child initial children t r integer = some action) : action.connection.den = 1 := by
  unfold keyedOnlineCandidate at h
  dsimp only at h
  split_ifs at h
  split at h
  · cases h
  · cases Option.some.inj h
    exact Rat.den_zero

theorem localOnlineCandidates_connection_den {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H : ℕ) (tau a eta kappa : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (children : PhysicalChildTables M target.length) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (q : TargetInterval target.length)
    (action : PhysicalRationalAction M target.length)
    (ha : action ∈ localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      parentInitial child initial children t integer q) : action.connection.den = 1 := by
  obtain ⟨b, _, _, hcandidate⟩ :=
    (localOnlineCandidates_mem source target parent N P F exponent H tau a eta kappa
      parentInitial child initial children t integer q action).mp ha
  exact keyedOnlineCandidate_connection_den source target parent P F exponent H b tau eta kappa
    child initial children t _ _ action hcandidate

theorem physicalLocalOnline_connection_den {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F exponent H T : ℕ) (A tau eta kappa : ℚ)
    (integer : PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (node : PhysicalNode M J) (children : PhysicalChildTables M target.length)
    (t : ℕ) (q : TargetInterval target.length) (action : PhysicalRationalAction M target.length)
    (ha : action ∈ physicalLocalOnline source target U N P F exponent H T A tau eta kappa
      integer node children t q) : action.connection.den = 1 := by
  unfold physicalLocalOnline at ha
  split_ifs at ha with hbelow
  · exact localOnlineCandidates_connection_den source target (physicalSourceInterval source.length node)
      N P F exponent H tau (refinementFactor A F) eta kappa _ _ _ children (t - 1) _ q action ha
  · exact False.elim (List.not_mem_nil ha)

theorem physicalLocalRefinement_den_dvd {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F exponent Q : ℕ) (A tau : ℚ) (T ell : ℕ) (hell : 0 < ell)
    (draw : PhysicalInternalNode M J → ℕ → CellGroupDraws M F Q)
    (online : PhysicalNode M J → PhysicalChildTables M target.length → ℕ →
      TargetInterval target.length → List (PhysicalRationalAction M target.length))
    (honline : ∀ node children t q action, action ∈ online node children t q → action.connection.den = 1)
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) :
    (physicalLocalRefinement source target U N P F exponent Q A tau
      (1 / (ell : ℚ) ^ 10) T draw online node t q).den ∣ (ell ^ 10 + 1) ^ (J - node.1.val) := by
  rw [physicalLocalRefinement]
  split_ifs with hbelow hleaf
  · rw [stageInitial_den_one source target U N P F A]
    exact one_dvd _
  · dsimp only
    cases t with
    | zero =>
      rw [physicalLocalWarmup_den_one source target U N P F A]
      exact one_dvd _
    | succ t =>
      have hheight : J - node.1.val = (J - (node.1.val + 1)) + 1 := by omega
      rw [hheight]
      conv_rhs => rw [pow_succ]
      have hdelta : (1 / (ell : ℚ) ^ 10) = 1 / ((ell ^ 10 : ℕ) : ℚ) := by rw [Nat.cast_pow]
      rw [hdelta]
      apply rationalLocalWideStep_den_dvd source target _ N P F exponent Q (ell ^ 10)
        (pow_pos hell 10) tau (refinementFactor A F)
      · intro r
        rw [stageInitial_den_one source target U N P F A]
        exact one_dvd _
      · intro i r
        simpa only [Nat.cast_pow, physicalChild] using
          physicalLocalRefinement_den_dvd source target U N P F exponent Q A tau T ell hell
            draw online honline (physicalChild node hbelow i) t r
      · intro i r
        simpa only [Nat.cast_pow, physicalChild] using
          physicalLocalRefinement_den_dvd source target U N P F exponent Q A tau T ell hell
            draw online honline (physicalChild node hbelow i) (t + 1) r
      · exact honline _ _ _ _
  · rw [stageInitial_den_one source target U N P F A]
    exact one_dvd _
termination_by J - node.1.val
decreasing_by
  all_goals
    unfold physicalChild
    dsimp only
    omega

theorem physicalLocalRefinement_encoding_bits {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F exponent Q : ℕ) (A tau : ℚ) (hsize : source.length + target.length ≤ N)
    (T ell : ℕ) (hell : 0 < ell)
    (draw : PhysicalInternalNode M J → ℕ → CellGroupDraws M F Q)
    (online : PhysicalNode M J → PhysicalChildTables M target.length → ℕ →
      TargetInterval target.length → List (PhysicalRationalAction M target.length))
    (honline : ∀ node children t q action, action ∈ online node children t q → action.connection.den = 1)
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) :
    rationalEncodingBits (physicalLocalRefinement source target U N P F exponent Q A tau
      (1 / (ell : ℚ) ^ 10) T draw online node t q) ≤
        Nat.size ((32 * F + 1) * N) + 2 * (J - node.1.val) * Nat.size (ell ^ 10 + 1) + 3 := by
  let value := physicalLocalRefinement source target U N P F exponent Q A tau
    (1 / (ell : ℚ) ^ 10) T draw online node t q
  have hbounds := physicalLocalRefinement_bounds source target U N P F exponent Q A tau
    (1 / (ell : ℚ) ^ 10) T (by positivity) draw online node t q
  have hupper : value ≤ (((32 * F + 1) * N : ℕ) : ℚ) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
      hbounds.2.trans (stageInitial_upper_all_seeds source target U N P F A hsize (node, q))
  have h := rationalEncodingBits_of_den_dvd value ((32 * F + 1) * N)
    ((ell ^ 10 + 1) ^ (J - node.1.val)) (by rw [abs_of_nonneg hbounds.1]; exact hupper)
    (pow_pos (by omega) _) (physicalLocalRefinement_den_dvd source target U N P F exponent Q
      A tau T ell hell draw online honline node t q)
  have hpower := natural_power_bit_length (ell ^ 10 + 1) (J - node.1.val)
  have hpowerTwice := Nat.mul_le_mul_left 2 hpower
  simp only [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc] at hpowerTwice
  change rationalEncodingBits value ≤ _
  omega

theorem physicalLocalOnlineRefinement_den_dvd {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F exponent H Q : ℕ) (A tau eta kappa : ℚ) (T ell : ℕ) (hell : 0 < ell)
    (draw : PhysicalInternalNode M J → ℕ → CellGroupDraws M F Q)
    (integer : PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) :
    (physicalLocalRefinement source target U N P F exponent Q A tau (1 / (ell : ℚ) ^ 10)
      T draw (physicalLocalOnline source target U N P F exponent H T A tau eta kappa integer)
      node t q).den ∣ (ell ^ 10 + 1) ^ (J - node.1.val) :=
  physicalLocalRefinement_den_dvd source target U N P F exponent Q A tau T ell hell draw _
    (physicalLocalOnline_connection_den source target U N P F exponent H T A tau eta kappa integer) node t q

theorem physicalLocalWarmup_encoding_bits {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (t : ℕ) (state : PhysicalEntry M J target.length) :
    rationalEncodingBits (physicalLocalWarmup source target U N P F A t state) ≤
      Nat.size ((32 * F + 1) * N) + 3 := by
  let value := physicalLocalWarmup source target U N P F A t state
  have hbounds := physicalLocalWarmup_bounds source target U N P F A t state
  have hupper : value ≤ (((32 * F + 1) * N : ℕ) : ℚ) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
      hbounds.2.trans (stageInitial_upper_all_seeds source target U N P F A hsize state)
  have hden : value.den ∣ 1 := by
    rw [physicalLocalWarmup_den_one source target U N P F A]
  have h := rationalEncodingBits_of_den_dvd value ((32 * F + 1) * N) 1
    (by rw [abs_of_nonneg hbounds.1]; exact hupper) (by decide) hden
  simpa only [Nat.size_one, Nat.mul_one, Nat.add_assoc] using h

theorem physicalLocalOnlineRefinement_encoding_bits {α : Type*} [DecidableEq α]
    {M J R : ℕ} [NeZero R]
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F exponent H Q : ℕ) (A tau eta kappa : ℚ)
    (hsize : source.length + target.length ≤ N) (T ell : ℕ) (hell : 0 < ell)
    (draw : PhysicalInternalNode M J → ℕ → CellGroupDraws M F Q)
    (integer : PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) :
    rationalEncodingBits (physicalLocalRefinement source target U N P F exponent Q A tau
      (1 / (ell : ℚ) ^ 10) T draw
      (physicalLocalOnline source target U N P F exponent H T A tau eta kappa integer) node t q) ≤
        Nat.size ((32 * F + 1) * N) + 2 * (J - node.1.val) * Nat.size (ell ^ 10 + 1) + 3 :=
  physicalLocalRefinement_encoding_bits source target U N P F exponent Q A tau hsize T ell hell draw _
    (physicalLocalOnline_connection_den source target U N P F exponent H T A tau eta kappa integer) node t q

end EditApproximation

end OAI
