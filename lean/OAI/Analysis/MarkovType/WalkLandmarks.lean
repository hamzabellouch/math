import OAI.Analysis.MarkovType.PeriodicArcs
import OAI.Analysis.MarkovType.WordAction
import OAI.Analysis.MarkovType.WalkParameters
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Int.Interval

namespace OAI

namespace MarkovSuperreflexivity

abbrev WalkBoundedWord (n : ℕ) := Σ k : Fin (n + 1), Fin k.val → Letter

def WalkBoundedWord.toList {n : ℕ} (w : WalkBoundedWord n) : List Letter :=
  List.ofFn w.2

@[simp] theorem WalkBoundedWord.length_toList {n : ℕ} (w : WalkBoundedWord n) :
    w.toList.length = w.1.val := by
  simp [WalkBoundedWord.toList]

theorem WalkBoundedWord.length_toList_le {n : ℕ} (w : WalkBoundedWord n) :
    w.toList.length ≤ n := by
  rw [WalkBoundedWord.length_toList]
  exact Nat.le_of_lt_succ w.1.isLt

def WalkBoundedWord.ofList {n : ℕ} (w : List Letter) (hw : w.length ≤ n) :
    WalkBoundedWord n :=
  ⟨⟨w.length, Nat.lt_succ_of_le hw⟩, w.get⟩

@[simp] theorem WalkBoundedWord.toList_ofList {n : ℕ} (w : List Letter)
    (hw : w.length ≤ n) : (WalkBoundedWord.ofList w hw).toList = w := by
  exact List.ofFn_get w

noncomputable def walkLandmarkShifts (n : ℕ) : Finset ℤ :=
  Finset.Icc (-(2 * (n : ℤ))) ((walkWindowLength n : ℤ) + 2 * (n : ℤ))

noncomputable def walkEndpointValue (n : ℕ)
    (p : Letter × (Fin (walkWindowLength n) × Bool)) : ℝ :=
  if p.2.2 then alpha p.1 + (p.2.1.val : ℝ)
  else beta p.1 + (p.2.1.val : ℝ)

noncomputable def walkEndpoints (n : ℕ) : Finset ℝ := by
  classical
  exact Finset.univ.image (walkEndpointValue n)

noncomputable def walkOrbitPoints (n : ℕ) : Finset ℝ := by
  classical
  exact Finset.univ.biUnion fun w : WalkBoundedWord n =>
    (walkLandmarkShifts n).image fun j : ℤ => wordMap w.toList 0 + (j : ℝ)

noncomputable def walkLandmarks (n : ℕ) : Finset ℝ := by
  classical
  exact walkEndpoints n ∪ walkOrbitPoints n

theorem alpha_shift_mem_walkLandmarks (n : ℕ) (s : Letter)
    (j : Fin (walkWindowLength n)) :
    alpha s + (j.val : ℝ) ∈ walkLandmarks n := by
  classical
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_image.mpr
  refine ⟨(s, (j, true)), Finset.mem_univ _, ?_⟩
  simp [walkEndpointValue]

theorem beta_shift_mem_walkLandmarks (n : ℕ) (s : Letter)
    (j : Fin (walkWindowLength n)) :
    beta s + (j.val : ℝ) ∈ walkLandmarks n := by
  classical
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_image.mpr
  refine ⟨(s, (j, false)), Finset.mem_univ _, ?_⟩
  simp [walkEndpointValue]

theorem orbit_shift_mem_walkLandmarks {n : ℕ} (w : List Letter)
    (hw : w.length ≤ n) (j : ℤ)
    (hjlo : -(2 * (n : ℤ)) ≤ j)
    (hjhi : j ≤ (walkWindowLength n : ℤ) + 2 * (n : ℤ)) :
    wordMap w 0 + (j : ℝ) ∈ walkLandmarks n := by
  classical
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_biUnion.mpr
  refine ⟨WalkBoundedWord.ofList w hw, Finset.mem_univ _, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨j, Finset.mem_Icc.mpr ⟨hjlo, hjhi⟩, ?_⟩
  simp only [WalkBoundedWord.toList_ofList]

theorem integer_mem_walkLandmarks {n : ℕ} (j : ℤ)
    (hjlo : -(2 * (n : ℤ)) ≤ j)
    (hjhi : j ≤ (walkWindowLength n : ℤ) + 2 * (n : ℤ)) :
    (j : ℝ) ∈ walkLandmarks n := by
  have h := orbit_shift_mem_walkLandmarks ([] : List Letter)
    (Nat.zero_le n) j hjlo hjhi
  simpa only [wordMap, OrderIso.refl_apply, zero_add] using h

theorem zero_mem_walkLandmarks (n : ℕ) : (0 : ℝ) ∈ walkLandmarks n := by
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have hL : (0 : ℤ) ≤ walkWindowLength n := Int.natCast_nonneg _
  simpa only [Int.cast_zero] using
    integer_mem_walkLandmarks (n := n) 0 (by omega) (by omega)

theorem length_mem_walkLandmarks (n : ℕ) :
    (walkWindowLength n : ℝ) ∈ walkLandmarks n := by
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have hL : (0 : ℤ) ≤ walkWindowLength n := Int.natCast_nonneg _
  simpa only [Int.cast_natCast] using
    integer_mem_walkLandmarks (n := n) (walkWindowLength n) (by omega) (by omega)

theorem walkLandmarks_nonempty (n : ℕ) : (walkLandmarks n).Nonempty :=
  ⟨0, zero_mem_walkLandmarks n⟩

theorem sampled_integer_mem_walkLandmarks {n : ℕ} (j : ℤ)
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ)) :
    (j : ℝ) ∈ walkLandmarks n := by
  obtain ⟨hlo, hhi⟩ := walk_integer_shift_mem_range hjlo hjhi
  exact integer_mem_walkLandmarks j hlo hhi

theorem translated_orbit_mem_walkLandmarks {n : ℕ} (w : List Letter)
    (hw : w.length ≤ n) (j m : ℤ)
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ))
    (hmlo : -(2 * (n : ℤ)) ≤ m) (hmhi : m ≤ 2 * (n : ℤ) - 1) :
    wordMap w 0 + ((j - m : ℤ) : ℝ) ∈ walkLandmarks n := by
  obtain ⟨hlo, hhi⟩ := walk_translated_shift_mem_range hjlo hjhi hmlo hmhi
  exact orbit_shift_mem_walkLandmarks w hw (j - m) hlo hhi

end MarkovSuperreflexivity

end OAI
