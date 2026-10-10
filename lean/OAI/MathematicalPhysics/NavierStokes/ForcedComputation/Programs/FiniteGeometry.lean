import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.FiniteLabels
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RecorderCoordinates
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.BoxBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RectangleSeparation

namespace OAI

/-! The actual finite list of rational affine instructions and the fixed
unit-torus geometric data for the initialized computation construction. -/

namespace ForcedComputation.Recorder

open Radix ShearFlows

def geometricBranches (M : Alternating.Machine) (hM : M.WellFormed) :
    List (Branch (finiteMachine M hM)) := (compileBranches M hM).dedup

def geometricInstruction (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : Instruction :=
  branchInstruction (bandScale M) (radixBase M) (radixDigit M) (stateOffset M) b

def compiledInput (M : Alternating.Machine) (hM : M.WellFormed) : Input where
  period := 1
  chart := ⟨![1 / 32, 1 / 32, 1 / 8], ![31 / 32, 31 / 32, 7 / 8]⟩
  h := bandScale M / 2
  codingHeight := 1 / 2
  centers := ⟨![1 / 8, 1 / 4], ![13 / 16, 1 / 2]⟩
  instructions := (geometricBranches M hM).map (geometricInstruction M hM)

theorem geometricInstruction_mem (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) :
    geometricInstruction M hM b ∈ (compiledInput M hM).instructions := by
  apply List.mem_map.mpr
  refine ⟨b, ?_, rfl⟩
  simpa only [geometricBranches, List.mem_dedup] using mem_compileBranches M hM b

theorem geometricInstruction_factor_pos (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : 0 < (geometricInstruction M hM b).factor :=
  headFactor_pos (lt_trans (by norm_num) (radixBase_gt_one M)) _

theorem geometricInstruction_source_positive (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : (geometricInstruction M hM b).source.positive :=
  scaledBox_positive (bandScale_pos M) _
    (sourceBox_positive (lt_trans (by norm_num) (radixBase_gt_one M)) _ _)

theorem geometricInstruction_target_positive (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : (geometricInstruction M hM b).target.positive :=
  scaledBox_positive (bandScale_pos M) _
    (targetBox_positive (lt_trans (by norm_num) (radixBase_gt_one M)) _ _ _)

theorem radixDigit_bounds_rat (M : Alternating.Machine) (a : Symbol (State M) (Alphabet M)) :
    0 ≤ radixDigit M a ∧ radixDigit M a + 1 ≤ radixBase M := by
  constructor
  · exact_mod_cast (radixDigit_bounds M a).1
  · exact_mod_cast (radixDigit_bounds M a).2

theorem geometricInstruction_source_unit (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) :
    InUnit (sourceBox (radixBase M) (radixDigit M b.left) (radixDigit M b.read)) :=
  sourceBox_inUnit (lt_trans (by norm_num) (radixBase_gt_one M))
    (radixDigit_bounds_rat M _) (radixDigit_bounds_rat M _)

theorem geometricInstruction_target_unit (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) :
    InUnit (targetBox (radixBase M) (radixDigit M b.left) (radixDigit M b.write)
      (headMoveOfInt b.displacement)) :=
  targetBox_inUnit (lt_trans (by norm_num) (radixBase_gt_one M))
    (radixDigit_bounds_rat M _) (radixDigit_bounds_rat M _) _

theorem geometricInstruction_halfWidths (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (j : Fin 2) :
    (geometricInstruction M hM b).source.halfWidth j ≤ (bandScale M : ℝ) / 2 ∧
      (geometricInstruction M hM b).target.halfWidth j ≤ (bandScale M : ℝ) / 2 := by
  have hp : (0 : ℝ) ≤ bandScale M := by exact_mod_cast (bandScale_pos M).le
  constructor
  · change (scaledBox (bandScale M) (stateOffset M b.source)
      (sourceBox (radixBase M) (radixDigit M b.left) (radixDigit M b.read))).halfWidth j ≤ _
    rw [scaledBox_halfWidth]
    nlinarith [halfWidth_le_half (geometricInstruction_source_unit M hM b) j]
  · change (scaledBox (bandScale M) (stateOffset M b.target)
      (targetBox (radixBase M) (radixDigit M b.left) (radixDigit M b.write)
        (headMoveOfInt b.displacement))).halfWidth j ≤ _
    rw [scaledBox_halfWidth]
    nlinarith [halfWidth_le_half (geometricInstruction_target_unit M hM b) j]

theorem stateBox_bounds (M : Alternating.Machine) (q : Control (State M) (Alphabet M))
    {R : RationalBox 2} (hR : InUnit R) {x : Plane}
    (hx : x ∈ (scaledBox (bandScale M) (stateOffset M q) R).carrier) :
    (1 / 8 : ℝ) ≤ x 0 ∧ x 0 ≤ 13 / 16 ∧ (1 / 4 : ℝ) ≤ x 1 ∧ x 1 ≤ 1 / 2 := by
  have h₀ := scaledBox_between (bandScale_pos M).le (stateOffset M q) hR hx 0
  have h₁ := scaledBox_between (bandScale_pos M).le (stateOffset M q) hR hx 1
  have hk : (bandScale M : ℝ) ≤ 1 / 64 := by
    have h := (Rat.cast_le (K := ℝ)).mpr (bandScale_le M)
    norm_num at h
    exact h
  have hy : (3 / 8 : ℝ) < centerY M q ∧ (centerY M q : ℝ) < 7 / 16 := by
    constructor
    · have h := (Rat.cast_lt (K := ℝ)).mpr (centerY_bounds M q).1
      norm_num at h
      exact h
    · have h := (Rat.cast_lt (K := ℝ)).mpr (centerY_bounds M q).2
      norm_num at h
      exact h
  simp only [stateOffset, Matrix.cons_val_zero, Matrix.cons_val_one,
    Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat] at h₀ h₁
  cases ht : recorderHalting M q <;> simp only [ht, Bool.false_eq_true, ite_false, ite_true] at h₀ <;>
    norm_num at h₀
  all_goals exact ⟨by linarith [h₀.1, h₀.2], by linarith [h₀.1, h₀.2],
    by linarith [h₁.1, h₁.2], by linarith [h₁.1, h₁.2]⟩

theorem stateBox_nonterminal_x (M : Alternating.Machine) (q : Control (State M) (Alphabet M))
    (hq : recorderHalting M q = false) {R : RationalBox 2} (hR : InUnit R) {x : Plane}
    (hx : x ∈ (scaledBox (bandScale M) (stateOffset M q) R).carrier) :
    1 / 4 - (bandScale M : ℝ) / 2 ≤ x 0 ∧
      x 0 ≤ 1 / 4 + (bandScale M : ℝ) / 2 := by
  have h := scaledBox_between (bandScale_pos M).le (stateOffset M q) hR hx 0
  norm_num [stateOffset, hq] at h
  constructor <;> linarith [h.1, h.2]

theorem stateBox_terminal_x (M : Alternating.Machine) (q : Control (State M) (Alphabet M))
    (hq : recorderHalting M q = true) {R : RationalBox 2} (hR : InUnit R) {x : Plane}
    (hx : x ∈ (scaledBox (bandScale M) (stateOffset M q) R).carrier) :
    3 / 4 - (bandScale M : ℝ) / 2 ≤ x 0 ∧
      x 0 ≤ 3 / 4 + (bandScale M : ℝ) / 2 := by
  have h := scaledBox_between (bandScale_pos M).le (stateOffset M q) hR hx 0
  norm_num [stateOffset, hq] at h
  constructor <;> linarith [h.1, h.2]

theorem geometricInstruction_source_bounds (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) {x : Plane}
    (hx : x ∈ (geometricInstruction M hM b).source.carrier) :
    (1 / 8 : ℝ) ≤ x 0 ∧ x 0 ≤ 13 / 16 ∧ (1 / 4 : ℝ) ≤ x 1 ∧ x 1 ≤ 1 / 2 :=
  stateBox_bounds M b.source (geometricInstruction_source_unit M hM b) hx

theorem geometricInstruction_target_bounds (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) {x : Plane}
    (hx : x ∈ (geometricInstruction M hM b).target.carrier) :
    (1 / 8 : ℝ) ≤ x 0 ∧ x 0 ≤ 13 / 16 ∧ (1 / 4 : ℝ) ≤ x 1 ∧ x 1 ≤ 1 / 2 :=
  stateBox_bounds M b.target (geometricInstruction_target_unit M hM b) hx

theorem geometricInstruction_image (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) :
    (geometricInstruction M hM b).affine '' (geometricInstruction M hM b).source.carrier =
      (geometricInstruction M hM b).target.carrier := by
  let r := radixInstruction (radixBase M) (radixDigit M b.left) (radixDigit M b.read)
    (radixDigit M b.write) (headMoveOfInt b.displacement)
  change (scaledInstruction (bandScale M) (stateOffset M b.source) (stateOffset M b.target) r).affine ''
    (scaledBox (bandScale M) (stateOffset M b.source) r.source).carrier =
    (scaledBox (bandScale M) (stateOffset M b.target) r.target).carrier
  rw [← scaledBox_image (bandScale_pos M), ← scaledBox_image (bandScale_pos M), Set.image_image]
  have he : (scaledInstruction (bandScale M) (stateOffset M b.source) (stateOffset M b.target) r).affine ∘
      embedPlane (bandScale M) (stateOffset M b.source) =
      embedPlane (bandScale M) (stateOffset M b.target) ∘ r.affine := by
    funext x
    exact scaledInstruction_action _ _ _ _ _
  simp only [Function.comp_def] at he
  have hr : r.affine '' r.source.carrier = r.target.carrier :=
    radixInstruction_image (lt_trans (by norm_num) (radixBase_gt_one M)) _ _ _ _
  rw [he, ← Set.image_image, hr]

theorem compiledInput_basic (M : Alternating.Machine) (hM : M.WellFormed) :
    0 < (compiledInput M hM).period ∧ (compiledInput M hM).chart.positive ∧
      (∀ j, (compiledInput M hM).chart.upper j - (compiledInput M hM).chart.lower j <
        (compiledInput M hM).period) ∧
      0 < (compiledInput M hM).h ∧ (compiledInput M hM).centers.nonemptyBox ∧
      ((compiledInput M hM).chart.lower 2 : ℝ) < (compiledInput M hM).codingHeight ∧
      ((compiledInput M hM).codingHeight : ℝ) < (compiledInput M hM).chart.upper 2 := by
  refine ⟨by norm_num [compiledInput], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j <;> norm_num [compiledInput]
  · intro j
    fin_cases j <;> norm_num [compiledInput]
  · exact div_pos (bandScale_pos M) (by norm_num)
  · intro j
    fin_cases j <;> norm_num [compiledInput]
  · norm_num [compiledInput]
  · norm_num [compiledInput]

theorem compiledInput_chartMargin (M : Alternating.Machine) (hM : M.WellFormed) :
    ∀ j : Fin 2,
      ((compiledInput M hM).chart.lower j.castSucc : ℝ) <
        ((compiledInput M hM).centers.lower j : ℝ) - 2 * ((compiledInput M hM).h : ℝ) ∧
      ((compiledInput M hM).centers.upper j : ℝ) + 2 * ((compiledInput M hM).h : ℝ) <
        ((compiledInput M hM).chart.upper j.castSucc : ℝ) := by
  have hs : (bandScale M : ℝ) ≤ 1 / 64 := by
    have h := (Rat.cast_le (K := ℝ)).mpr (bandScale_le M)
    norm_num at h
    exact h
  intro j
  fin_cases j <;> norm_num [compiledInput] <;> constructor <;> linarith

theorem stateBox_separation (M : Alternating.Machine)
    {q r : Control (State M) (Alphabet M)} (hqr : q ≠ r)
    {R S : RationalBox 2} (hR : InUnit R) (hS : InUnit S) :
    PositivelySeparated (scaledBox (bandScale M) (stateOffset M q) R).carrier
      (scaledBox (bandScale M) (stateOffset M r) S).carrier := by
  have hp : (0 : ℝ) < bandScale M := by exact_mod_cast bandScale_pos M
  refine ⟨3 * (bandScale M : ℝ), by positivity, ?_⟩
  intro x hx y hy
  have hgap := centerY_gap M hqr
  have hxb := scaledBox_between (bandScale_pos M).le (stateOffset M q) hR hx 1
  have hyb := scaledBox_between (bandScale_pos M).le (stateOffset M r) hS hy 1
  dsimp [stateOffset] at hxb hyb
  push_cast at hxb hyb
  have hab : 3 * (bandScale M : ℝ) ≤ |x 1 - y 1| := by
    rcases le_total (centerY M q : ℝ) (centerY M r : ℝ) with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hgap
      calc
        3 * (bandScale M : ℝ) ≤ y 1 - x 1 := by linarith [hxb.2, hyb.1]
        _ ≤ |y 1 - x 1| := le_abs_self _
        _ = |x 1 - y 1| := abs_sub_comm _ _
    · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hgap
      exact (show 3 * (bandScale M : ℝ) ≤ x 1 - y 1 by linarith [hxb.1, hyb.2]).trans
        (le_abs_self _)
  exact hab.trans (by simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (x - y) 1)

theorem geometricInstruction_source_separation (M : Alternating.Machine) (hM : M.WellFormed)
    {b c : Branch (finiteMachine M hM)} (hne : b ≠ c) :
    PositivelySeparated (geometricInstruction M hM b).source.carrier
      (geometricInstruction M hM c).source.carrier := by
  by_cases hs : b.source = c.source
  · have hpair : (symbolLabel M b.left, symbolLabel M b.read) ≠
        (symbolLabel M c.left, symbolLabel M c.read) := by
      intro h
      have hl := (symbolLabel M).injective (congrArg Prod.fst h)
      have hr := (symbolLabel M).injective (congrArg Prod.snd h)
      rcases Branch.source_symbols_differ hne hs with hn | hn
      · exact hn hr
      · exact hn hl
    have hgap := (sourceBox_gap (symbolLabel M b.left) (symbolLabel M b.read)
      (symbolLabel M c.left) (symbolLabel M c.read) hpair).scaled (bandScale_pos M)
        (stateOffset M b.source)
    have hp : 0 < (bandScale M : ℝ) * (1 / (radixBase M : ℝ)) := by
      have hk : (0 : ℝ) < bandScale M := by exact_mod_cast bandScale_pos M
      have hB : (0 : ℝ) < radixBase M := by exact_mod_cast lt_trans (by norm_num) (radixBase_gt_one M)
      positivity
    simpa only [geometricInstruction, branchInstruction, scaledInstruction, radixInstruction,
      radixBase, radixDigit, hs] using hgap.positiveSeparated hp
  · exact stateBox_separation M hs (geometricInstruction_source_unit M hM b)
      (geometricInstruction_source_unit M hM c)

theorem geometricInstruction_target_separation (M : Alternating.Machine) (hM : M.WellFormed)
    {b c : Branch (finiteMachine M hM)} (hne : b ≠ c) :
    PositivelySeparated (geometricInstruction M hM b).target.carrier
      (geometricInstruction M hM c).target.carrier := by
  by_cases ht : b.target = c.target
  · have hpair : (symbolLabel M b.left, symbolLabel M b.write) ≠
        (symbolLabel M c.left, symbolLabel M c.write) := by
      intro h
      have hl := (symbolLabel M).injective (congrArg Prod.fst h)
      have hw := (symbolLabel M).injective (congrArg Prod.snd h)
      rcases Branch.target_symbols_differ hne ht with hn | hn
      · exact hn hw
      · exact hn hl
    have hd := Branch.same_target_displacement ht
    have hgap := (targetBox_gap (symbolLabel M b.left) (symbolLabel M b.write)
      (symbolLabel M c.left) (symbolLabel M c.write) (headMoveOfInt b.displacement) hpair).scaled
        (bandScale_pos M) (stateOffset M b.target)
    have hp : 0 < (bandScale M : ℝ) * (1 / (radixBase M : ℝ) ^ 2) := by
      have hk : (0 : ℝ) < bandScale M := by exact_mod_cast bandScale_pos M
      have hB : (0 : ℝ) < radixBase M := by exact_mod_cast lt_trans (by norm_num) (radixBase_gt_one M)
      positivity
    simpa only [geometricInstruction, branchInstruction, scaledInstruction, radixInstruction,
      radixBase, radixDigit, ht, hd] using hgap.positiveSeparated hp
  · exact stateBox_separation M ht (geometricInstruction_target_unit M hM b)
      (geometricInstruction_target_unit M hM c)

/-- Transfer a separation relation through a duplicate-free finite map. -/
theorem indexed_map_separation {A B : Type*} (l : List A) (F : A → B)
    (hl : l.Nodup) (P : B → B → Prop)
    (hP : ∀ a b, a ≠ b → P (F a) (F b))
    (i j : Fin (l.map F).length) (hij : i ≠ j) : P ((l.map F)[i]) ((l.map F)[j]) := by
  let i' : Fin l.length := ⟨i.val, by simpa only [List.length_map] using i.isLt⟩
  let j' : Fin l.length := ⟨j.val, by simpa only [List.length_map] using j.isLt⟩
  have hne : l.get i' ≠ l.get j' := by
    intro he
    have heq := hl.get_inj_iff.mp he
    have hv : i.val = j.val := congrArg (fun k : Fin l.length => k.val) heq
    exact hij (Fin.ext hv)
  have hp := hP (l.get i') (l.get j') hne
  simpa only [List.get_eq_getElem, Fin.getElem_fin, List.getElem_map, i', j'] using hp

theorem compiledInput_source_separation (M : Alternating.Machine) (hM : M.WellFormed)
    (i j : Fin (compiledInput M hM).instructions.length) (hij : i ≠ j) :
    PositivelySeparated ((compiledInput M hM).instructions[i].source.carrier)
      ((compiledInput M hM).instructions[j].source.carrier) := by
  apply indexed_map_separation (geometricBranches M hM) (geometricInstruction M hM)
    (List.nodup_dedup _) (fun b c => PositivelySeparated b.source.carrier c.source.carrier)
    (fun _ _ hn => geometricInstruction_source_separation M hM hn) i j hij

theorem compiledInput_target_separation (M : Alternating.Machine) (hM : M.WellFormed)
    (i j : Fin (compiledInput M hM).instructions.length) (hij : i ≠ j) :
    PositivelySeparated ((compiledInput M hM).instructions[i].target.carrier)
      ((compiledInput M hM).instructions[j].target.carrier) := by
  apply indexed_map_separation (geometricBranches M hM) (geometricInstruction M hM)
    (List.nodup_dedup _) (fun b c => PositivelySeparated b.target.carrier c.target.carrier)
    (fun _ _ hn => geometricInstruction_target_separation M hM hn) i j hij

/-- The finite machine compiler supplies every hypothesis of the full-rectangle
solenoidal-shear realization theorem. -/
theorem compiledInput_valid (M : Alternating.Machine) (hM : M.WellFormed) :
    ValidInput (compiledInput M hM) := by
  obtain ⟨hp, hc, hcl, hh, hn, hz₀, hz₁⟩ := compiledInput_basic M hM
  refine ⟨hp, hc, hcl, hh, hn, compiledInput_chartMargin M hM, ⟨hz₀, hz₁⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
    exact geometricInstruction_source_positive M hM c
  · intro b hb
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
    exact geometricInstruction_target_positive M hM c
  · intro b hb x hx
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
    obtain ⟨h₀, h₁, h₂, h₃⟩ := geometricInstruction_source_bounds M hM c hx
    intro j
    fin_cases j <;> norm_num [compiledInput, Input.inPlanarChart] <;> constructor <;> linarith
  · intro b hb x hx
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
    obtain ⟨h₀, h₁, h₂, h₃⟩ := geometricInstruction_target_bounds M hM c hx
    intro j
    fin_cases j <;> norm_num [compiledInput, Input.inPlanarChart] <;> constructor <;> linarith
  · intro b hb
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
    exact geometricInstruction_factor_pos M hM c
  · intro b hb
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
    exact geometricInstruction_image M hM c
  · exact compiledInput_source_separation M hM
  · exact compiledInput_target_separation M hM
  · intro b hb j
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
    simpa only [compiledInput, Rat.cast_div, Rat.cast_ofNat] using
      geometricInstruction_halfWidths M hM c j
  · intro b hb
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
    have hx := geometricInstruction_source_bounds M hM c
      (center_mem (geometricInstruction_source_positive M hM c))
    intro j
    fin_cases j
    · simpa [compiledInput] using And.intro hx.1 hx.2.1
    · simpa [compiledInput] using And.intro hx.2.2.1 hx.2.2.2
  · intro b hb
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
    have hx := geometricInstruction_target_bounds M hM c
      (center_mem (geometricInstruction_target_positive M hM c))
    intro j
    fin_cases j
    · simpa [compiledInput] using And.intro hx.1 hx.2.1
    · simpa [compiledInput] using And.intro hx.2.2.1 hx.2.2.2

end ForcedComputation.Recorder

end OAI
