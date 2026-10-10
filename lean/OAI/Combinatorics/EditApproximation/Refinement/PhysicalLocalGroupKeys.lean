import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalOnlineKeys
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Every whole-cell stream used by the complete program has a bounded
physical key. Its two cell coordinates are at most n*2^exponent. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

theorem list_eraseDups_nodup {α : Type*} [BEq α] [LawfulBEq α] (items : List α) :
    items.eraseDups.Nodup := by
  cases items with
  | nil => simp
  | cons first rest =>
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨?_, list_eraseDups_nodup _⟩
    intro hmem
    have hfalse := (List.mem_filter.mp (List.mem_eraseDups.mp hmem)).2
    simp at hfalse
termination_by items.length
decreasing_by
  simpa only [List.length_cons] using
    Nat.lt_succ_of_le (List.length_filter_le (fun item => !(item == first)) rest)

theorem targetCell_coordinate_bound {n : ℕ} (exponent b : ℕ) (hb : 1 ≤ b)
    (q : TargetInterval n) :
    (targetCell ((2 : ℚ) ^ (-(exponent : ℤ)) * b) q).1 ≤ n * 2 ^ exponent ∧
    (targetCell ((2 : ℚ) ^ (-(exponent : ℤ)) * b) q).2 ≤ n * 2 ^ exponent := by
  have hside : (0 : ℚ) < (2 : ℚ) ^ (-(exponent : ℤ)) * b := by positivity
  have hcoordinate (p : ℕ) (hp : p ≤ n) :
      ⌊(p : ℚ) / ((2 : ℚ) ^ (-(exponent : ℤ)) * b)⌋₊ ≤ n * 2 ^ exponent := by
    have hcancel : ((n * 2 ^ exponent : ℕ) : ℚ) *
        ((2 : ℚ) ^ (-(exponent : ℤ)) * b) = n * b := by
      push_cast
      rw [zpow_neg, zpow_natCast]
      field_simp
    have hmul : (p : ℚ) ≤ ((n * 2 ^ exponent : ℕ) : ℚ) *
        ((2 : ℚ) ^ (-(exponent : ℤ)) * b) := by
      rw [hcancel]
      exact_mod_cast hp.trans (Nat.le_mul_of_pos_right n (by omega))
    have h := Nat.floor_le_floor ((div_le_iff₀ hside).2 hmul)
    simpa only [Nat.floor_natCast] using h
  exact ⟨hcoordinate q.lo (q.ordered.trans q.valid), hcoordinate q.hi q.valid⟩



section Keys

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent : ℕ) (A : ℚ)

theorem physicalProgramCells_bounds (node : PhysicalNode M J)
    (b : ℕ) (hb : 1 ≤ b) (cell : ℕ × ℕ)
    (hcell : cell ∈ physicalProgramCells source target U N P F A exponent node b) :
    cell.1 ≤ target.length * 2 ^ exponent ∧ cell.2 ≤ target.length * 2 ^ exponent := by
  obtain ⟨br, _, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp hcell)
  exact targetCell_coordinate_bound exponent b hb br.2

theorem physicalGroupScale_positive
    (key : PhysicalGroupKey source target U N P F A exponent) :
    1 ≤ (dyadicScales N).get key.2.1 := by
  have hm := List.get_mem (dyadicScales N) key.2.1
  obtain ⟨e, _, heq⟩ := List.mem_map.mp hm
  exact heq ▸ Nat.one_le_two_pow

def physicalGroupRawKey (key : PhysicalGroupKey source target U N P F A exponent) :
    PhysicalLocalGroupKey M J N target.length exponent :=
  let cell := (physicalProgramCells source target U N P F A exponent key.1.1
    ((dyadicScales N).get key.2.1)).get key.2.2
  let bounds := physicalProgramCells_bounds source target U N P F exponent A key.1.1
    ((dyadicScales N).get key.2.1) (physicalGroupScale_positive source target U N P F exponent A key)
    cell (List.get_mem _ key.2.2)
  (key.1, key.2.1, ⟨cell.1, Nat.lt_succ_of_le bounds.1⟩, ⟨cell.2, Nat.lt_succ_of_le bounds.2⟩)

theorem physicalGroupRawKey_injective :
    Function.Injective (physicalGroupRawKey source target U N P F exponent A) := by
  rintro ⟨node, scale, cell⟩ ⟨node', scale', cell'⟩ heq
  have hn := congrArg Prod.fst heq
  change node = node' at hn
  subst node'
  have hs := congrArg (fun key : PhysicalLocalGroupKey M J N target.length exponent => key.2.1) heq
  change scale = scale' at hs
  subst scale'
  have hlo := congrArg (fun key : PhysicalLocalGroupKey M J N target.length exponent => key.2.2.1.val) heq
  have hhi := congrArg (fun key : PhysicalLocalGroupKey M J N target.length exponent => key.2.2.2.val) heq
  simp only [physicalGroupRawKey] at hlo hhi
  have hnodup : (physicalProgramCells source target U N P F A exponent node.1
      ((dyadicScales N).get scale)).Nodup := list_eraseDups_nodup _
  have hcell := hnodup.injective_get (Prod.ext hlo hhi)
  cases hcell
  rfl

end Keys

abbrev PhysicalLocalGroupArray (M J N n exponent F Q R : ℕ)
    (key : PhysicalLocalGroupKey M J N n exponent) :=
  Fin R → ParentGroupDraw M (groupDyadicScales M ((dyadicScales N).get key.2.1) F).length
    (fun h => groupSampleCount M Q ((dyadicScales N).get key.2.1)
      (groupDyadicScaleAt M ((dyadicScales N).get key.2.1) F h))

noncomputable def physicalLocalGroupArrayLaw (M J N n exponent F Q R : ℕ)
    [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (key : PhysicalLocalGroupKey M J N n exponent) :
    Measure (PhysicalLocalGroupArray M J N n exponent F Q R key) :=
  Measure.pi fun _ : Fin R => groupSharedDrawLaw (M := M)
    (fun h => groupSampleCount M Q ((dyadicScales N).get key.2.1)
      (groupDyadicScaleAt M ((dyadicScales N).get key.2.1) F h))

instance physicalLocalGroupArrayLaw_probability (M J N n exponent F Q R : ℕ)
    [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (key : PhysicalLocalGroupKey M J N n exponent) :
    IsProbabilityMeasure (physicalLocalGroupArrayLaw M J N n exponent F Q R key) := by
  unfold physicalLocalGroupArrayLaw
  infer_instance

theorem physicalLocalGroupDrawLaw_restrict {α : Type*} [DecidableEq α] {M J : ℕ}
    [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F exponent Q R : ℕ) (A : ℚ) :
    (Measure.pi (physicalLocalGroupArrayLaw M J N target.length exponent F Q R)).map
      (fun draw (key : PhysicalGroupKey source target U N P F A exponent) =>
        draw (physicalGroupRawKey source target U N P F exponent A key)) =
    Measure.pi (fun key : PhysicalGroupKey source target U N P F A exponent =>
      Measure.pi (fun _ : Fin R => groupSharedDrawLaw (M := M)
        (fun h => groupSampleCount M Q ((dyadicScales N).get key.2.1)
          (groupDyadicScaleAt M ((dyadicScales N).get key.2.1) F h)))) :=
  finite_pi_restrict_map _ _ (physicalGroupRawKey_injective source target U N P F exponent A)

end EditApproximation

end OAI
