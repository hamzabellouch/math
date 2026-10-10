import OAI.Combinatorics.EditApproximation.Geometry.ListBandRegret
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRefinementSpatial
import OAI.Combinatorics.EditApproximation.Geometry.BandGroupSampling

namespace OAI

/-!
# Online actions from the actual physical child histories

The fixed representative band uses the rational warmup-average child
table. Its envelopes scan the literal initial child table. Online gains
and decrements are computed from the full physical refinement histories.
-/

namespace EditApproximation

open Finset

theorem bandCoordinate_restriction {β σ : Type*} [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : List (β → σ)) (coordinate : β × σ)
    (hcoordinate : coordinate ∈ bandCoordinates (band).toFinset) :
    ∃ action ∈ band, action coordinate.1 = coordinate.2 := by
  obtain ⟨action, haction, hcoordinate⟩ := mem_biUnion.mp hcoordinate
  obtain ⟨child, _, hequal⟩ := mem_image.mp hcoordinate
  cases hequal
  exact ⟨action, List.mem_toFinset.mp haction, rfl⟩

theorem representativeBandActions_wide {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P : ℕ) (tau theta : ℚ) (child : Fin M → TargetInterval target.length → ℚ)
    (action : Fin M → TargetInterval target.length)
    (haction : action ∈ representativeBandActions source target parent r b P tau theta child) :
    action ∈ wideActionList M parent r b P := by
  by_cases hwide : wideActionList M parent r b P = []
  · simp only [representativeBandActions, dite_eq_left hwide, List.not_mem_nil] at haction
  · by_cases hZ : 0 < rationalWideActionMinimum parent r b P hwide child
    · simp only [representativeBandActions, dite_eq_right hwide, ite_eq_left hZ] at haction
      exact (computedBandActions_mem parent r b P tau theta _ child action haction).choose_spec.1
    · simp only [representativeBandActions, dite_eq_right hwide, ite_eq_right hZ, List.not_mem_nil] at haction

theorem representativeBandActions_diameter {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P : ℕ) (tau theta : ℚ) (htau : 0 < tau) (htheta : 0 ≤ theta)
    (child : Fin M → TargetInterval target.length → ℚ)
    (first second : Fin M → TargetInterval target.length)
    (hfirst : first ∈ representativeBandActions source target parent r b P tau theta child)
    (hsecond : second ∈ representativeBandActions source target parent r b P tau theta child) (i : Fin M) :
    (targetEndpointDistance (first i) (second i) : ℝ) ≤ 4 * (theta : ℝ) * b / M := by
  by_cases hwide : wideActionList M parent r b P = []
  · simp only [representativeBandActions, dite_eq_left hwide, List.not_mem_nil] at hfirst
  · by_cases hZ : 0 < rationalWideActionMinimum parent r b P hwide child
    · simp only [representativeBandActions, dite_eq_right hwide, ite_eq_left hZ] at hfirst hsecond
      exact computedBand_child_endpoint_diameter parent r b P tau theta _ htau htheta child
        first second hfirst hsecond i
    · simp only [representativeBandActions, dite_eq_right hwide, ite_eq_right hZ, List.not_mem_nil] at hfirst


theorem canonicalRoundedBandAction_congr {ny M : ℕ} (thetaExponent b : ℕ)
    (first second : List (Fin M → TargetInterval ny))
    (hfirst : first ≠ []) (hsecond : second ≠ [])
    (initial : Fin M → TargetInterval ny → ℚ) (hequal : first = second) :
    canonicalRoundedBandAction thetaExponent b first hfirst initial =
      canonicalRoundedBandAction thetaExponent b second hsecond initial := by
  subst second
  rfl

/-- The representative wrapper preserves the literal rounded-band cost bound. -/
theorem representativeBandActions_canonical_cost {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (thetaExponent b P : ℕ) (tau : ℚ) (htau : 0 < tau)
    (child initial value : Fin M → TargetInterval target.length → ℚ)
    (hnonempty : representativeBandActions source target parent r b P tau
      ((2 : ℚ) ^ (-(thetaExponent : ℤ))) child ≠ [])
    (action : Fin M → TargetInterval target.length)
    (haction : action ∈ representativeBandActions source target parent r b P tau
      ((2 : ℚ) ^ (-(thetaExponent : ℤ))) child)
    (delta L : ℚ) (hL : 0 ≤ L)
    (hspatial : ∀ i s t, value i s ≤ (1 + delta) * value i t + L * targetEndpointDistance s t) :
    let band := representativeBandActions source target parent r b P tau
      ((2 : ℚ) ^ (-(thetaExponent : ℤ))) child
    rationalEndpointActionValue r (canonicalRoundedBandAction thetaExponent b band hnonempty initial) value ≤
      (1 + delta) * (∑ i, value i (action i)) +
        (6 * L + 2) * (2 : ℚ) ^ (-(thetaExponent : ℤ)) * ∑ i, bandChildEnvelope b band initial i := by
  by_cases hwide : wideActionList M parent r b P = []
  · simp only [representativeBandActions, dite_eq_left hwide, List.not_mem_nil] at haction
  · by_cases hZ : 0 < rationalWideActionMinimum parent r b P hwide child
    · let velocity := rationalStateGap (substring source parent.lo parent.hi) target r /
        rationalWideActionMinimum parent r b P hwide child
      have hequal : representativeBandActions source target parent r b P tau
          ((2 : ℚ) ^ (-(thetaExponent : ℤ))) child =
          computedBandActions parent r b P tau ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child := by
        simp only [representativeBandActions, dite_eq_right hwide, ite_eq_left hZ, velocity]
      have hn : computedBandActions parent r b P tau
          ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child ≠ [] := by
        rw [← hequal]
        exact hnonempty
      have ha : action ∈ computedBandActions parent r b P tau
          ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child := hequal ▸ haction
      have hbound := canonicalRoundedBandAction_cost parent r thetaExponent b P tau velocity htau
        child initial value hn action ha delta L hL hspatial
      have hcanonical := canonicalRoundedBandAction_congr thetaExponent b _ _ hnonempty hn initial hequal
      dsimp only
      rw [hcanonical]
      simpa only [hequal] using hbound
    · simp only [representativeBandActions, dite_eq_right hwide, ite_eq_right hZ, List.not_mem_nil] at haction


section PhysicalBand

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A))
  (node : PhysicalNode M J) (hbelow : node.1.val < J)

def physicalBandChildInitial (i : Fin M) (s : TargetInterval target.length) : ℚ :=
  stageInitial source target U N P F A (physicalChild node hbelow i, s)

def physicalBandChildMassTable (i : Fin M) (s : TargetInterval target.length) : ℚ :=
  stageWarmupMass source target U N P F A T (physicalChild node hbelow i, s)

def physicalBandHistory (t : ℕ) (coordinate : Fin M × TargetInterval target.length) : ℚ :=
  physicalRefinement source target U N P F A T delta choices (physicalChild node hbelow coordinate.1) t coordinate.2

def physicalBandActions (b thetaExponent : ℕ) (tau : ℚ) (r : TargetInterval target.length) :
    List (Fin M → TargetInterval target.length) :=
  representativeBandActions source target (physicalSourceInterval source.length node) r b P tau
    ((2 : ℚ) ^ (-(thetaExponent : ℤ))) (physicalBandChildMassTable source target U N P F A T node hbelow)

def physicalBandEnvelope (b thetaExponent : ℕ) (tau : ℚ) (r : TargetInterval target.length) (i : Fin M) : ℚ :=
  bandChildEnvelope b (physicalBandActions source target U N P F A T node hbelow b thetaExponent tau r)
    (physicalBandChildInitial source target U N P F A node hbelow) i

variable (b thetaExponent : ℕ) (tau : ℚ) (r : TargetInterval target.length)

local notation "band" => physicalBandActions source target U N P F A T node hbelow b thetaExponent tau r
local notation "mass" => physicalBandEnvelope source target U N P F A T node hbelow b thetaExponent tau r
local notation "history" => physicalBandHistory source target U N P F A T delta choices node hbelow
local notation "initial" => physicalBandChildInitial source target U N P F A node hbelow
local notation "theta" => (2 : ℚ) ^ (-(thetaExponent : ℤ))

theorem physicalBandEnvelope_pos (i : Fin M) : 0 < mass i :=
  bandChildEnvelope_pos b band initial i

theorem physicalBandHistory_nonincreasing (t : ℕ) (coordinate : Fin M × TargetInterval target.length) :
    history (t + 1) coordinate ≤ history t coordinate :=
  physicalRefinement_nonincreasing source target U N P F A T delta choices
    (physicalChild node hbelow coordinate.1) t coordinate.2

variable (hM : 0 < M) (hsize : source.length + target.length ≤ N)
  (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (hT : 0 < T)

include hM hsize hP hF hA hseed hT in
 theorem physicalBandHistory_bounds (t : ℕ) (coordinate : Fin M × TargetInterval target.length)
    (hcoordinate : coordinate ∈ bandCoordinates (band).toFinset) :
    0 ≤ history t coordinate ∧ history t coordinate ≤ mass coordinate.1 := by
  obtain ⟨action, haction, hequal⟩ := bandCoordinate_restriction band coordinate hcoordinate
  have hstage := physicalRefinement_stage_bounds source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices (physicalChild node hbelow coordinate.1) t coordinate.2
  have hupper := (bandChildEnvelope_lower b band initial coordinate.1).2 action haction
  change initial coordinate.1 (action coordinate.1) ≤ mass coordinate.1 at hupper
  rw [hequal] at hupper
  exact ⟨physicalRefinement_nonneg source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices (physicalChild node hbelow coordinate.1) t coordinate.2,
    (hstage.2.1.trans (hstage.2.2.1.trans hstage.2.2.2.1)).trans hupper⟩

theorem physicalBand_coordinate_distance (htau : 0 < tau)
    (first second : Fin M × TargetInterval target.length)
    (hfirst : first ∈ bandCoordinates (band).toFinset) (hsecond : second ∈ bandCoordinates (band).toFinset)
    (hsame : first.1 = second.1) :
    (targetEndpointDistance first.2 second.2 : ℝ) ≤ 4 * (theta : ℝ) * (mass first.1 : ℝ) := by
  obtain ⟨action, haction, hactionState⟩ := bandCoordinate_restriction band first hfirst
  obtain ⟨action', haction', hactionState'⟩ := bandCoordinate_restriction band second hsecond
  rw [← hsame] at hactionState'
  have htheta : 0 ≤ theta := (zpow_pos (by norm_num : (0 : ℚ) < 2) _).le
  have hdiameter := representativeBandActions_diameter source target
    (physicalSourceInterval source.length node) r b P tau theta htau htheta
    (physicalBandChildMassTable source target U N P F A T node hbelow)
    action action' haction haction' first.1
  rw [hactionState, hactionState'] at hdiameter
  have hfloorQ : (b : ℚ) / M ≤ mass first.1 := (bandChildEnvelope_lower b band initial first.1).1
  have hfloor : (b : ℝ) / M ≤ (mass first.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using (Rat.cast_le (K := ℝ)).mpr hfloorQ
  have hweighted := mul_le_mul_of_nonneg_left hfloor
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) ((Rat.cast_nonneg (K := ℝ)).mpr htheta))
  simp only [Rat.cast_zpow] at hdiameter hweighted ⊢
  calc
    _ ≤ 4 * (theta : ℝ) * ((b : ℝ) / M) := by simpa only [mul_div_assoc] using hdiameter
    _ ≤ _ := hweighted

include hM hsize hP hF hA hseed hT in
 theorem physicalBand_decrement_total (S : ℕ) (coordinate : Fin M × TargetInterval target.length)
    (hcoordinate : coordinate ∈ bandCoordinates (band).toFinset) :
    (∑ t ∈ range S, (childDecrement mass history t coordinate : ℝ)) ≤ 1 := by
  exact childDecrement_total_le mass history S coordinate
    (physicalBandEnvelope_pos source target U N P F A T node hbelow b thetaExponent tau r coordinate.1)
    (physicalBandHistory_bounds source target U N P F A T delta choices node hbelow b thetaExponent tau r
      hM hsize hP hF hA hseed hT S coordinate hcoordinate).1
    (physicalBandHistory_bounds source target U N P F A T delta choices node hbelow b thetaExponent tau r
      hM hsize hP hF hA hseed hT 0 coordinate hcoordinate).2


include hM hsize hP hF hA hseed hT in
 theorem physicalBandHistory_absolute (htau : 0 < tau) (hdelta : 0 ≤ delta)
    (t : ℕ) (first second : Fin M × TargetInterval target.length)
    (hfirst : first ∈ bandCoordinates (band).toFinset) (hsecond : second ∈ bandCoordinates (band).toFinset)
    (hsame : first.1 = second.1) :
    |(history t first : ℝ) - (history t second : ℝ)| ≤
      (delta : ℝ) * (mass first.1 : ℝ) +
        4 * ((128 * F : ℚ) : ℝ) * (theta : ℝ) * (mass first.1 : ℝ) := by
  have hfirstBounds := physicalBandHistory_bounds source target U N P F A T delta choices node hbelow
    b thetaExponent tau r hM hsize hP hF hA hseed hT t first hfirst
  have hsecondBounds := physicalBandHistory_bounds source target U N P F A T delta choices node hbelow
    b thetaExponent tau r hM hsize hP hF hA hseed hT t second hsecond
  have hmassSame : mass second.1 = mass first.1 := congrArg (fun child => mass child) hsame.symm
  rw [hmassSame] at hsecondBounds
  have hforward : history t first ≤ (1 + delta) * history t second +
      (128 * F : ℚ) * targetEndpointDistance first.2 second.2 := by
    simpa only [physicalBandHistory, hsame] using physicalRefinement_spatial source target hM U N P F A
      hsize hP hF hA hseed T hT delta hdelta choices (physicalChild node hbelow first.1) t first.2 second.2
  have hbackward : history t second ≤ (1 + delta) * history t first +
      (128 * F : ℚ) * targetEndpointDistance second.2 first.2 := by
    simpa only [physicalBandHistory, hsame] using physicalRefinement_spatial source target hM U N P F A
      hsize hP hF hA hseed T hT delta hdelta choices (physicalChild node hbelow second.1) t second.2 first.2
  have hsym : targetEndpointDistance second.2 first.2 = targetEndpointDistance first.2 second.2 := by
    unfold targetEndpointDistance
    rw [Nat.dist_comm second.2.lo, Nat.dist_comm second.2.hi]
  rw [hsym] at hbackward
  have hforwardR : (history t first : ℝ) ≤ (1 + (delta : ℝ)) * (history t second : ℝ) +
      ((128 * F : ℚ) : ℝ) * targetEndpointDistance first.2 second.2 := by exact_mod_cast hforward
  have hbackwardR : (history t second : ℝ) ≤ (1 + (delta : ℝ)) * (history t first : ℝ) +
      ((128 * F : ℚ) : ℝ) * targetEndpointDistance first.2 second.2 := by exact_mod_cast hbackward
  have habsolute := multiplicative_spatial_absolute
    ((Rat.cast_nonneg (K := ℝ)).mpr hdelta)
    ((Rat.cast_le (K := ℝ)).mpr hfirstBounds.2) ((Rat.cast_le (K := ℝ)).mpr hsecondBounds.2)
    hforwardR hbackwardR
  have hdiameter := physicalBand_coordinate_distance source target U N P F A T node hbelow
    b thetaExponent tau r htau first second hfirst hsecond hsame
  have hL : (0 : ℝ) ≤ ((128 * F : ℚ) : ℝ) := by positivity
  have hcharge := mul_le_mul_of_nonneg_left hdiameter hL
  nlinarith only [habsolute, hcharge]

include hM hsize hP hF hA hseed hT in
 theorem physicalBand_decrement_range (htau : 0 < tau) (hdelta : 0 ≤ delta)
    (t : ℕ) (first second : Fin M × TargetInterval target.length)
    (hfirst : first ∈ bandCoordinates (band).toFinset) (hsecond : second ∈ bandCoordinates (band).toFinset)
    (hsame : first.1 = second.1) :
    |(childDecrement mass history t first : ℝ) - (childDecrement mass history t second : ℝ)| ≤
      2 * (delta : ℝ) + 8 * ((128 * F : ℚ) : ℝ) * (theta : ℝ) := by
  have hmass : (0 : ℝ) < (mass first.1 : ℝ) :=
    (Rat.cast_pos (K := ℝ)).mpr (physicalBandEnvelope_pos source target U N P F A T node hbelow
      b thetaExponent tau r first.1)
  have hold := physicalBandHistory_absolute source target U N P F A T delta choices node hbelow
    b thetaExponent tau r hM hsize hP hF hA hseed hT htau hdelta t first second hfirst hsecond hsame
  have hnew := physicalBandHistory_absolute source target U N P F A T delta choices node hbelow
    b thetaExponent tau r hM hsize hP hF hA hseed hT htau hdelta (t + 1) first second hfirst hsecond hsame
  have hrange := normalized_decrement_range hmass hold hnew
  have hcancel : 2 * (4 * ((128 * F : ℚ) : ℝ) * (theta : ℝ) * (mass first.1 : ℝ)) /
      (mass first.1 : ℝ) = 8 * ((128 * F : ℚ) : ℝ) * (theta : ℝ) := by
    calc
      _ = 2 * (4 * ((128 * F : ℚ) : ℝ) * (theta : ℝ)) *
          ((mass first.1 : ℝ) / (mass first.1 : ℝ)) := by ring
      _ = _ := by rw [div_self hmass.ne']; ring
  rw [hcancel] at hrange
  simp only [childDecrement, Rat.cast_div, Rat.cast_sub, ← hsame]
  exact hrange

include hM hsize hP hF hA hseed hT in
 theorem physicalBand_gain_bounds (κ : ℚ) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (t : ℕ) (coordinate : Fin M × TargetInterval target.length)
    (hcoordinate : coordinate ∈ bandCoordinates (band).toFinset) :
    -1 ≤ (childGain mass history t coordinate : ℝ) +
        (1 - (κ : ℝ)) * childDecrement mass history t coordinate ∧
      (childGain mass history t coordinate : ℝ) +
        (1 - (κ : ℝ)) * childDecrement mass history t coordinate ≤ 0 := by
  exact childGain_decrement_bounds mass history κ t coordinate
    (physicalBandEnvelope_pos source target U N P F A T node hbelow b thetaExponent tau r coordinate.1)
    hκ (by linarith only [hκhalf])
    (physicalBandHistory_bounds source target U N P F A T delta choices node hbelow b thetaExponent tau r
      hM hsize hP hF hA hseed hT t coordinate hcoordinate)
    (physicalBandHistory_bounds source target U N P F A T delta choices node hbelow b thetaExponent tau r
      hM hsize hP hF hA hseed hT (t + 1) coordinate hcoordinate)


/-- The exact action sampler retains the order of the literal physical band. -/
def physicalBandOnlineDraw (hband : band ≠ []) (η κ : ℚ) (G K t : ℕ)
    (integer : Fin (optimizerTriangularMass K)) : Fin M → TargetInterval target.length :=
  finiteOptimizerActionDraw band hband mass
    (rationalOnlineLinear η κ (childGain mass history) (childDecrement mass history) t) G K integer

theorem physicalBandOnlineDraw_mem (hband : band ≠ []) (η κ : ℚ) (G K t : ℕ)
    (integer : Fin (optimizerTriangularMass K)) :
    physicalBandOnlineDraw source target U N P F A T delta choices node hbelow
      b thetaExponent tau r hband η κ G K t integer ∈ band :=
  finiteOptimizerActionDraw_mem band hband mass _ G K integer

theorem physicalBandOnlineDraw_wide (hband : band ≠ []) (η κ : ℚ) (G K t : ℕ)
    (integer : Fin (optimizerTriangularMass K)) :
    physicalBandOnlineDraw source target U N P F A T delta choices node hbelow
      b thetaExponent tau r hband η κ G K t integer ∈
        wideActionList M (physicalSourceInterval source.length node) r b P := by
  exact representativeBandActions_wide source target (physicalSourceInterval source.length node)
    r b P tau theta (physicalBandChildMassTable source target U N P F A T node hbelow) _
    (physicalBandOnlineDraw_mem source target U N P F A T delta choices node hbelow
      b thetaExponent tau r hband η κ G K t integer)

include hM in
/-- Exact conditional mean: only the current finite integer draw is averaged. -/
theorem physicalBandOnlineDraw_child_cost_mean (hband : band ≠ []) (η κ : ℚ)
    (G K t : ℕ) (hK : 0 < K) :
    uniformMean (fun integer : Fin (optimizerTriangularMass K) =>
      let action := physicalBandOnlineDraw source target U N P F A T delta choices node hbelow
        b thetaExponent tau r hband η κ G K t integer
      (∑ child, (history (t + 1) (child, action child) : ℝ)) +
        (κ : ℝ) * ((∑ child, (history t (child, action child) : ℝ)) -
          ∑ child, (history (t + 1) (child, action child) : ℝ))) =
      -((∑ child, mass child : ℚ) : ℝ) *
        ∑ coordinate ∈ bandCoordinates (band).toFinset,
          ((childGain mass history t coordinate : ℝ) +
            (1 - (κ : ℝ)) * childDecrement mass history t coordinate) *
              (finiteRationalOptimizer (bandCoordinates (band).toFinset)
                ((band).map (actionVector mass))
                (rationalOnlineLinear η κ (childGain mass history) (childDecrement mass history) t)
                G K coordinate : ℝ) := by
  let : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  exact finiteOptimizerActionDraw_child_cost_mean band hband mass
    (physicalBandEnvelope_pos source target U N P F A T node hbelow b thetaExponent tau r)
    history κ t _ G K hK

include hM in
 theorem physicalBandOnlineDraw_computed_mean (hband : band ≠ []) (η κ : ℚ)
    (G K H t : ℕ) (hG : G = H + (bandCoordinates (band).toFinset).card + 2)
    (hK : K = G ^ 80) (hH : 4 ≤ H) :
    uniformMean (fun integer : Fin (optimizerTriangularMass K) =>
      let action := physicalBandOnlineDraw source target U N P F A T delta choices node hbelow
        b thetaExponent tau r hband η κ G K t integer
      (∑ child, (history (t + 1) (child, action child) : ℝ)) +
        (κ : ℝ) * ((∑ child, (history t (child, action child) : ℝ)) -
          ∑ child, (history (t + 1) (child, action child) : ℝ))) =
      -((∑ child, mass child : ℚ) : ℝ) *
        ∑ coordinate ∈ bandCoordinates (band).toFinset,
          ((childGain mass history t coordinate : ℝ) +
            (1 - (κ : ℝ)) * childDecrement mass history t coordinate) *
              (computedOnlineVector (bandCoordinates (band).toFinset)
                ((band).map (actionVector mass)) η κ
                (childGain mass history) (childDecrement mass history) H t coordinate : ℝ) := by
  have hGpos : 0 < G := by omega
  have hKpos : 0 < K := by rw [hK]; exact pow_pos hGpos 80
  have hmean := physicalBandOnlineDraw_child_cost_mean source target U N P F A T delta choices
    node hbelow b thetaExponent tau r hM hband η κ G K t hKpos
  simpa only [computedOnlineVector, ← hG, ← hK] using hmean

include hM hsize hP hF hA hseed hT in
/-- The regret hypotheses are proved from the actual physical recurrence. -/
theorem physicalBand_computed_entropy_regret (htau : 0 < tau) (hdelta : 0 ≤ delta)
    (S H : ℕ) (η κ : ℚ) {comparison : Fin M → TargetInterval target.length}
    (hc : comparison ∈ band) (hH : 4 ≤ H) (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hηrange : (η : ℝ) *
      (2 * (delta : ℝ) + 8 * ((128 * F : ℚ) : ℝ) * (theta : ℝ)) ≤ (κ : ℝ)) :
    (∑ t ∈ range S, ∑ coordinate ∈ bandCoordinates (band).toFinset,
        ((childGain mass history t coordinate : ℝ) + childDecrement mass history t coordinate) *
          (actionVector mass comparison coordinate : ℝ)) -
        Real.log (bandCoordinates (band).toFinset).card / (η : ℝ) - 2 * (κ : ℝ) -
          (S : ℝ) / (H : ℝ) ^ 3 ≤
      ∑ t ∈ range S, ∑ coordinate ∈ bandCoordinates (band).toFinset,
        ((childGain mass history t coordinate : ℝ) +
          (1 - (κ : ℝ)) * childDecrement mass history t coordinate) *
            (computedOnlineVector (bandCoordinates (band).toFinset)
              ((band).map (actionVector mass)) η κ
              (childGain mass history) (childDecrement mass history) H t coordinate : ℝ) := by
  let : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hband : band ≠ [] := List.ne_nil_of_mem hc
  apply list_band_computed_entropy_regret band hband mass
    (physicalBandEnvelope_pos source target U N P F A T node hbelow b thetaExponent tau r)
    S H η κ _ (childGain mass history) (childDecrement mass history) hc hH hη hκ hκhalf hηrange
  · intro t _ coordinate _
    exact childDecrement_nonneg mass history t coordinate
      (physicalBandEnvelope_pos source target U N P F A T node hbelow b thetaExponent tau r coordinate.1)
      (physicalBandHistory_nonincreasing source target U N P F A T delta choices node hbelow t coordinate)
  · intro t _ first hfirst second hsecond hsame
    exact physicalBand_decrement_range source target U N P F A T delta choices node hbelow
      b thetaExponent tau r hM hsize hP hF hA hseed hT htau hdelta t first second hfirst hsecond hsame
  · intro coordinate hcoordinate
    exact physicalBand_decrement_total source target U N P F A T delta choices node hbelow
      b thetaExponent tau r hM hsize hP hF hA hseed hT S coordinate hcoordinate
  · intro t _ coordinate hcoordinate
    exact physicalBand_gain_bounds source target U N P F A T delta choices node hbelow
      b thetaExponent tau r hM hsize hP hF hA hseed hT κ hκ hκhalf t coordinate hcoordinate

include hM hsize hP hF hA hseed hT in
/-- Expected weighted cost regret of the returned physical-band action. -/
theorem physicalBandOnlineDraw_cost_regret (htau : 0 < tau) (hdelta : 0 ≤ delta)
    (hband : band ≠ []) (S H G K : ℕ) (η κ : ℚ)
    (hG : G = H + (bandCoordinates (band).toFinset).card + 2) (hK : K = G ^ 80)
    {comparison : Fin M → TargetInterval target.length} (hc : comparison ∈ band)
    (hH : 4 ≤ H) (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hηrange : (η : ℝ) *
      (2 * (delta : ℝ) + 8 * ((128 * F : ℚ) : ℝ) * (theta : ℝ)) ≤ (κ : ℝ)) :
    (∑ t ∈ range S, uniformMean (fun integer : Fin (optimizerTriangularMass K) =>
      let action := physicalBandOnlineDraw source target U N P F A T delta choices node hbelow
        b thetaExponent tau r hband η κ G K t integer
      (∑ child, (history (t + 1) (child, action child) : ℝ)) +
        (κ : ℝ) * ((∑ child, (history t (child, action child) : ℝ)) -
          ∑ child, (history (t + 1) (child, action child) : ℝ)))) ≤
      (∑ t ∈ range S, ∑ child, (history (t + 1) (child, comparison child) : ℝ)) +
        ((∑ child, mass child : ℚ) : ℝ) *
          (Real.log (bandCoordinates (band).toFinset).card / (η : ℝ) + 2 * (κ : ℝ) +
            (S : ℝ) / (H : ℝ) ^ 3) := by
  let : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hregret := physicalBand_computed_entropy_regret source target U N P F A T delta choices node hbelow
    b thetaExponent tau r hM hsize hP hF hA hseed hT htau hdelta S H η κ hc hH hη hκ hκhalf hηrange
  have hmass : (0 : ℝ) ≤ ((∑ child, mass child : ℚ) : ℝ) := by
    exact (Rat.cast_nonneg (K := ℝ)).mpr (sum_nonneg fun child _ =>
      (physicalBandEnvelope_pos source target U N P F A T node hbelow b thetaExponent tau r child).le)
  have hscaled := mul_le_mul_of_nonpos_left hregret (neg_nonpos.mpr hmass)
  have hmean t := physicalBandOnlineDraw_computed_mean source target U N P F A T delta choices
    node hbelow b thetaExponent tau r hM hband η κ G K H t hG hK hH
  simp_rw [hmean]
  rw [← mul_sum]
  have hcomparison t := actionVector_comparator_cost_identity (band).toFinset mass
    (physicalBandEnvelope_pos source target U N P F A T node hbelow b thetaExponent tau r)
    history t (List.mem_toFinset.mpr hc)
  have hcomparisonSum := congrArg (fun value : ℕ → ℝ => ∑ t ∈ range S, value t) (funext hcomparison)
  rw [← mul_sum] at hcomparisonSum
  nlinarith only [hscaled, hcomparisonSum]


include hM hsize hP hF hA hseed hT in
/-- Rounding is charged using the actual spatial regularity of child histories. -/
theorem physicalBand_canonical_cost (htau : 0 < tau) (hdelta : 0 ≤ delta)
    (hband : band ≠ []) (t : ℕ) (action : Fin M → TargetInterval target.length)
    (haction : action ∈ band) :
    rationalEndpointActionValue r
      (canonicalRoundedBandAction thetaExponent b band hband initial)
      (fun child state => history t (child, state)) ≤
        (1 + delta) * (∑ child, history t (child, action child)) +
          (6 * (128 * F : ℚ) + 2) * theta * ∑ child, mass child := by
  exact representativeBandActions_canonical_cost source target (physicalSourceInterval source.length node)
    r thetaExponent b P tau htau (physicalBandChildMassTable source target U N P F A T node hbelow)
    initial (fun child state => history t (child, state)) hband action haction delta (128 * F : ℚ)
    (by positivity) (fun child s s' => physicalRefinement_spatial source target hM U N P F A
      hsize hP hF hA hseed T hT delta hdelta choices (physicalChild node hbelow child) t s s')


end PhysicalBand

end EditApproximation

end OAI
