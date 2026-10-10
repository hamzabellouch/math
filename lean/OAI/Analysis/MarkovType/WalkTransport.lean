import OAI.Analysis.MarkovType.WalkLandmarks
import OAI.Analysis.MarkovType.FiniteCharts
import OAI.Analysis.MarkovType.IntegerCocycle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace OAI

namespace MarkovSuperreflexivity

noncomputable def walkOrbitFloor (w : List Letter) : ℤ := Int.floor (wordMap w 0)

noncomputable def walkOrbitFraction (w : List Letter) : ℝ :=
  wordMap w 0 - (walkOrbitFloor w : ℝ)

theorem wordMap_displacement_lt_of_length_le {n : ℕ} (hn : 0 < n)
    (w : List Letter) (hw : w.length ≤ n) (y : ℝ) :
    abs (wordMap w y - y) < 2 * (n : ℝ) := by
  by_cases hnil : w = []
  · subst w
    simp only [wordMap_nil_apply, sub_self, abs_zero]
    positivity
  · have hd := wordMap_displacement_lt hnil y
    have hcast : (w.length : ℝ) ≤ (n : ℝ) := by exact_mod_cast hw
    linarith

theorem wordMap_symm_displacement_lt_of_length_le {n : ℕ} (hn : 0 < n)
    (w : List Letter) (hw : w.length ≤ n) (y : ℝ) :
    abs ((wordMap w).symm y - y) < 2 * (n : ℝ) := by
  have hd := wordMap_displacement_lt_of_length_le hn w hw ((wordMap w).symm y)
  simpa only [OrderIso.apply_symm_apply, abs_sub_comm] using hd

theorem pullbackPoint_displacement_lt {n : ℕ} (hn : 0 < n)
    (w : List Letter) (hw : w.length ≤ n) (k : ℕ) (y : ℝ) :
    abs (pullbackPoint w k y - y) < 2 * (n : ℝ) := by
  apply wordMap_symm_displacement_lt_of_length_le hn
  simp only [List.length_take]
  omega

theorem walkOrbitFloor_bounds {n : ℕ} (hn : 0 < n)
    (w : List Letter) (hw : w.length ≤ n) :
    -(2 * (n : ℤ)) ≤ walkOrbitFloor w ∧
      walkOrbitFloor w ≤ 2 * (n : ℤ) - 1 := by
  apply walk_floor_bounds
  simpa only [sub_zero] using wordMap_displacement_lt_of_length_le hn w hw 0

theorem walkOrbitFraction_bounds (w : List Letter)
    (hnotint : ∀ m : ℤ, wordMap w 0 ≠ (m : ℝ)) :
    0 < walkOrbitFraction w ∧ walkOrbitFraction w < 1 :=
  walk_fractional_bounds hnotint

theorem walkOrbitFraction_add_int (w : List Letter) (j : ℤ) :
    walkOrbitFraction w + (j : ℝ) =
      wordMap w 0 + ((j - walkOrbitFloor w : ℤ) : ℝ) := by
  simp only [walkOrbitFraction, Int.cast_sub]
  ring

theorem pullbackPoint_integer_mem {n : ℕ} (w : List Letter)
    (hw : w.length ≤ n) (k : ℕ) (j : ℤ)
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ)) :
    pullbackPoint w k (j : ℝ) ∈ walkLandmarks n := by
  change (wordMap (w.take k)).symm (j : ℝ) ∈ walkLandmarks n
  rw [prefixState_int]
  obtain ⟨hlo, hhi⟩ := walk_integer_shift_mem_range hjlo hjhi
  apply orbit_shift_mem_walkLandmarks _ _ j hlo hhi
  simp only [inverseWord_length, List.length_take]
  omega

theorem pullbackPoint_fraction_mem {n : ℕ} (hn : 0 < n)
    (w : List Letter) (hw : w.length ≤ n) (k : ℕ) (j : ℤ)
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ)) :
    pullbackPoint w k (walkOrbitFraction w + (j : ℝ)) ∈ walkLandmarks n := by
  rw [walkOrbitFraction_add_int]
  change (wordMap (w.take k)).symm
    (wordMap w 0 + ((j - walkOrbitFloor w : ℤ) : ℝ)) ∈ walkLandmarks n
  rw [prefixState_wordMap_add_int]
  obtain ⟨hmlo, hmhi⟩ := walkOrbitFloor_bounds hn w hw
  apply translated_orbit_mem_walkLandmarks _ _ j (walkOrbitFloor w)
    hjlo hjhi hmlo hmhi
  simp only [List.length_drop]
  omega

theorem pullbackPoint_integer_window {n : ℕ} (hn : 0 < n)
    (w : List Letter) (hw : w.length ≤ n) (k : ℕ) (j : ℤ)
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ)) :
    0 < pullbackPoint w k (j : ℝ) ∧
      pullbackPoint w k (j : ℝ) < (walkWindowLength n : ℝ) := by
  rcases abs_lt.mp (pullbackPoint_displacement_lt hn w hw k (j : ℝ)) with
    ⟨hlo, hhi⟩
  apply walk_transport_in_window hjlo hjhi <;> linarith

theorem pullbackPoint_fraction_window {n : ℕ} (hn : 0 < n)
    (w : List Letter) (hw : w.length ≤ n) (k : ℕ) (j : ℤ)
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ))
    (hzlo : 0 < walkOrbitFraction w) (hzhi : walkOrbitFraction w < 1) :
    0 < pullbackPoint w k (walkOrbitFraction w + (j : ℝ)) ∧
      pullbackPoint w k (walkOrbitFraction w + (j : ℝ)) <
        (walkWindowLength n : ℝ) := by
  rcases abs_lt.mp
    (pullbackPoint_displacement_lt hn w hw k (walkOrbitFraction w + (j : ℝ))) with
    ⟨hlo, hhi⟩
  apply walk_transport_in_window hjlo hjhi <;> linarith

def chartCut {Λ : Finset ℝ} {B : ℕ} (C : Chart Λ B) (x : ↥Λ) : ℕ :=
  (C x).val + 1

theorem chartCut_pos {Λ : Finset ℝ} {B : ℕ} (C : Chart Λ B) (x : ↥Λ) :
    0 < chartCut C x := Nat.zero_lt_succ _

theorem chartCut_le {Λ : Finset ℝ} {B : ℕ} (C : Chart Λ B) (x : ↥Λ) :
    chartCut C x ≤ B := (C x).isLt

theorem chartCut_lt_of_lt {Λ : Finset ℝ} {B : ℕ} (C : Chart Λ B)
    {x y : ↥Λ} (hxy : (x : ℝ) < (y : ℝ)) : chartCut C x < chartCut C y :=
  Nat.add_lt_add_right (C.strictMono hxy) 1

theorem chartCut_lt_bound_of_lt {Λ : Finset ℝ} {B : ℕ} (C : Chart Λ B)
    {x y : ↥Λ} (hxy : (x : ℝ) < (y : ℝ)) : chartCut C x < B :=
  lt_of_lt_of_le (chartCut_lt_of_lt C hxy) (chartCut_le C y)

theorem chart_good_path_rank {Λ : Finset ℝ} {B n : ℕ}
    (C : Fin (n + 1) → Chart Λ B) (s : Fin n → Letter)
    (y : Fin (n + 1) → ↥Λ)
    (hgood : ∀ i : Fin n,
      Chart.Good (letterOrderIso (s i)) (C i.castSucc) (C i.succ))
    (hstep : ∀ i : Fin n,
      letterOrderIso (s i) (y i.succ : ℝ) = (y i.castSucc : ℝ)) :
    ∀ i : Fin (n + 1), C i (y i) = C 0 (y 0) := by
  intro i
  refine Fin.induction ?_ (fun k ih => ?_) i
  · rfl
  · have hmem : letterOrderIso (s k) (y k.succ : ℝ) ∈ Λ := by
      rw [hstep k]
      exact (y k.castSucc).property
    have heq : (⟨letterOrderIso (s k) (y k.succ : ℝ), hmem⟩ : ↥Λ) =
        y k.castSucc := Subtype.ext (hstep k)
    have h := hgood k (y k.succ) hmem
    rw [heq] at h
    exact h.trans ih

theorem chart_good_path_cut {Λ : Finset ℝ} {B n : ℕ}
    (C : Fin (n + 1) → Chart Λ B) (s : Fin n → Letter)
    (y : Fin (n + 1) → ↥Λ)
    (hgood : ∀ i : Fin n,
      Chart.Good (letterOrderIso (s i)) (C i.castSucc) (C i.succ))
    (hstep : ∀ i : Fin n,
      letterOrderIso (s i) (y i.succ : ℝ) = (y i.castSucc : ℝ))
    (i : Fin (n + 1)) : chartCut (C i) (y i) = chartCut (C 0) (y 0) := by
  unfold chartCut
  rw [chart_good_path_rank C s y hgood hstep i]

theorem pullbackPoint_good_path_cut {Λ : Finset ℝ} {B : ℕ}
    (w : List Letter) (C : Fin (w.length + 1) → Chart Λ B) (y₀ : ℝ)
    (hmem : ∀ k : Fin (w.length + 1), pullbackPoint w k.val y₀ ∈ Λ)
    (hgood : ∀ i : Fin w.length,
      Chart.Good (letterOrderIso (w.get i)) (C i.castSucc) (C i.succ))
    (k : Fin (w.length + 1)) :
    chartCut (C k) ⟨pullbackPoint w k.val y₀, hmem k⟩ =
      chartCut (C 0) ⟨pullbackPoint w 0 y₀, hmem 0⟩ := by
  let y : Fin (w.length + 1) → ↥Λ :=
    fun i => ⟨pullbackPoint w i.val y₀, hmem i⟩
  apply chart_good_path_cut C w.get y hgood
  intro i
  exact letterOrderIso_pullbackPoint_succ w i y₀

end MarkovSuperreflexivity

end OAI
