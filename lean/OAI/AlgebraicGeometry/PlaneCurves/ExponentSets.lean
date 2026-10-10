import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import OAI.AlgebraicGeometry.PlaneCurves.Enclosure
import OAI.AlgebraicGeometry.PlaneCurves.Intervals

namespace OAI

/-!
# Finite exponent sets for theta coefficient spaces
-/

section

/-!
# The manuscript's actual finite exponent set
-/
namespace Nagata.FiniteExponents

/-- Every integer strictly between two real endpoints, including integral endpoints. -/
noncomputable def openIntegerInterval (U V : ℝ) : Finset ℤ :=
  Finset.Ioo ⌊U⌋ ⌈V⌉

@[simp] theorem mem_openIntegerInterval {U V : ℝ} {K : ℤ} :
    K ∈ openIntegerInterval U V ↔ U < (K : ℝ) ∧ (K : ℝ) < V := by
  simp only [openIntegerInterval, Finset.mem_Ioo, Int.floor_lt, Int.lt_ceil]

/-- Common degree of the first coefficient blocks. -/
def commonDegree (d m : ℤ) : ℤ := 3 * (d - 3 * m)

/-- Source degree in a second coefficient block. -/
def sourceDegree (d j : ℤ) : ℤ := 3 * (d - 3 * j)

/-- The first branch's lower interval endpoint. -/
noncomputable def firstLower (d m j : ℤ) (a Δ : ℝ) : ℝ :=
  (commonDegree d m : ℝ) / 9 * (a - Δ) + ((m : ℝ) - (j : ℝ)) * a

/-- The second branch's lower interval endpoint. -/
noncomputable def secondLower (d j : ℤ) (a Δ : ℝ) : ℝ :=
  (sourceDegree d j : ℝ) / 9 * (a - Δ)

/-- Lift a finite set of second coordinates to one fixed first coordinate. -/
def liftRow (j : ℤ) (s : Finset ℤ) : Finset (ℤ × ℤ) :=
  s.image (fun K => (j, K))

@[simp] theorem mem_liftRow {j j' K : ℤ} {s : Finset ℤ} :
    (j', K) ∈ liftRow j s ↔ j' = j ∧ K ∈ s := by
  constructor
  · intro h
    obtain ⟨L, hL, heq⟩ := Finset.mem_image.mp h
    have hj : j = j' := congrArg Prod.fst heq
    have hK : L = K := congrArg Prod.snd heq
    exact ⟨hj.symm, hK ▸ hL⟩
  · rintro ⟨rfl, hK⟩
    exact Finset.mem_image.mpr ⟨K, hK, rfl⟩

/-- The complete finite exponent set: positive first blocks, positive-degree
second blocks, and the possible single degree-zero block. -/
noncomputable def exponentSet (d m : ℤ) (a Δ : ℝ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc 0 m).biUnion fun j =>
    liftRow j (openIntegerInterval (firstLower d m j a Δ)
      (firstLower d m j a Δ + (commonDegree d m : ℝ)))) ∪
  ((Finset.Ioc m (d / 3)).biUnion fun j =>
    if 0 < d - 3 * j then
      liftRow j (openIntegerInterval (secondLower d j a Δ)
        (secondLower d j a Δ + (sourceDegree d j : ℝ)))
    else ∅) ∪
  (((Finset.Ioc m (d / 3)).filter fun j => d - 3 * j = 0).image fun j => (j, 0))

/-- Source-faithful membership, using integer floor division for u₀. -/
theorem mem_exponentSet_iff {d m j K : ℤ} {a Δ : ℝ} :
    (j, K) ∈ exponentSet d m a Δ ↔
      (0 ≤ j ∧ j ≤ m ∧ firstLower d m j a Δ < (K : ℝ) ∧
        (K : ℝ) < firstLower d m j a Δ + (commonDegree d m : ℝ)) ∨
      (m < j ∧ j ≤ d / 3 ∧ 0 < d - 3 * j ∧
        secondLower d j a Δ < (K : ℝ) ∧
        (K : ℝ) < secondLower d j a Δ + (sourceDegree d j : ℝ)) ∨
      (m < j ∧ j ≤ d / 3 ∧ d - 3 * j = 0 ∧ K = 0) := by
  classical
  simp only [exponentSet, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_Icc, Finset.mem_Ioc, mem_liftRow, mem_openIntegerInterval,
    Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ((⟨j', hj', hrow⟩ | ⟨j', hj', hrow⟩) | ⟨j', ⟨hj', hz⟩, heq⟩)
    · rcases hrow with ⟨rfl, hlo, hhi⟩
      exact Or.inl ⟨hj'.1, hj'.2, hlo, hhi⟩
    · split_ifs at hrow with hp
      · rw [mem_liftRow, mem_openIntegerInterval] at hrow
        rcases hrow with ⟨rfl, hlo, hhi⟩
        exact Or.inr (Or.inl ⟨hj'.1, hj'.2, hp, hlo, hhi⟩)
      · simp at hrow
    · cases heq
      exact Or.inr (Or.inr ⟨hj'.1, hj'.2, hz, rfl⟩)
  · rintro (hfirst | hsecond | hzero)
    · rcases hfirst with ⟨hj0, hjm, hlo, hhi⟩
      exact Or.inl (Or.inl ⟨j, ⟨hj0, hjm⟩, rfl, hlo, hhi⟩)
    · rcases hsecond with ⟨hjm, hjd, hp, hlo, hhi⟩
      refine Or.inl (Or.inr ⟨j, ⟨hjm, hjd⟩, ?_⟩)
      simp only [ite_eq_left hp, mem_liftRow, mem_openIntegerInterval]
      exact ⟨True.intro, hlo, hhi⟩
    · rcases hzero with ⟨hjm, hjd, hz, rfl⟩
      exact Or.inr ⟨j, ⟨⟨hjm, hjd⟩, hz⟩, rfl⟩

/-- The integer floor bound is exactly the real bound used by the enclosure. -/
theorem integer_degree_bound (d j : ℤ) :
    j ≤ d / 3 ↔ (j : ℝ) ≤ (d : ℝ) / 3 := by
  rw [Int.le_ediv_iff_mul_le (show (0 : ℤ) < 3 by decide)]
  constructor
  · intro h
    have hc : (j : ℝ) * 3 ≤ (d : ℝ) := by exact_mod_cast h
    linarith
  · intro h
    have hc : (j : ℝ) * 3 ≤ (d : ℝ) := by linarith
    exact_mod_cast hc

theorem mem_exponentSet_iff_raw {d m j K : ℤ} {a Δ : ℝ} :
    (j, K) ∈ exponentSet d m a Δ ↔
      Nagata.ExponentEnclosure.rawExponent (d : ℝ) (m : ℝ)
        (3 * ((d : ℝ) - 3 * (m : ℝ))) a Δ (j : ℝ) (K : ℝ) := by
  rw [mem_exponentSet_iff]
  unfold Nagata.ExponentEnclosure.rawExponent firstLower secondLower commonDegree sourceDegree
  have hn : (3 : ℝ) * ((d : ℝ) - 3 * (j : ℝ)) =
      3 * ((d : ℝ) - 3 * (m : ℝ)) - 9 * ((j : ℝ) - (m : ℝ)) := by ring
  have h0 : (0 : ℤ) ≤ j ↔ (0 : ℝ) ≤ (j : ℝ) := by norm_cast
  have hjm : j ≤ m ↔ (j : ℝ) ≤ (m : ℝ) := by norm_cast
  have hmj : m < j ↔ (m : ℝ) < (j : ℝ) := by norm_cast
  have hz : d - 3 * j = 0 ↔ (d : ℝ) - 3 * (j : ℝ) = 0 := by norm_cast
  have hp : 0 < d - 3 * j ↔ (0 : ℝ) < (d : ℝ) - 3 * (j : ℝ) := by norm_cast
  have hK : K = 0 ↔ (K : ℝ) = 0 := by norm_cast
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_ofNat, hn]
  simp only [h0, hjm, hmj, integer_degree_bound, hp, hz, hK]

/-- The source's degree-zero block is retained in the actual finite set. -/
theorem degree_zero_mem {d m j : ℤ} {a Δ : ℝ}
    (hjm : m < j) (hz : d - 3 * j = 0) :
    (j, 0) ∈ exponentSet d m a Δ := by
  apply mem_exponentSet_iff.mpr
  refine Or.inr (Or.inr ⟨hjm, ?_, hz, rfl⟩)
  apply (Int.le_ediv_iff_mul_le (show (0 : ℤ) < 3 by decide)).mpr
  linarith

/-- Positive common degree and the manuscript's nonintegrality condition make
S nonempty; the construction has not substituted an empty column domain. -/
theorem exponentSet_nonempty {d m : ℤ} {a Δ : ℝ}
    (hm : 0 ≤ m) (hd : 3 * m < d)
    (hU : firstLower d m 0 a Δ ∉ Set.range (Int.cast : ℤ → ℝ)) :
    (exponentSet d m a Δ).Nonempty := by
  have hh : 0 < commonDegree d m := by
    unfold commonDegree
    linarith
  let U := firstLower d m 0 a Δ
  let K : ℤ := ⌊U⌋ + 1
  have hfloor : (⌊U⌋ : ℝ) < U := Int.floor_lt_self_iff.mpr hU
  have hhreal : (1 : ℝ) ≤ (commonDegree d m : ℝ) := by exact_mod_cast hh
  have hlo : U < (K : ℝ) := by
    dsimp [K]
    simpa only [Int.cast_add, Int.cast_one] using Int.lt_floor_add_one U
  have hhi : (K : ℝ) < U + (commonDegree d m : ℝ) := by
    dsimp [K]
    push_cast
    linarith
  refine ⟨(0, K), mem_exponentSet_iff.mpr ?_⟩
  exact Or.inl ⟨le_rfl, hm, hlo, hhi⟩

/-- The actual column type supplied to interpolation is finite by construction. -/
noncomputable def Column (d m : ℤ) (a Δ : ℝ) :=
  {p : ℤ × ℤ // p ∈ exponentSet d m a Δ}

noncomputable instance columnFintype (d m : ℤ) (a Δ : ℝ) :
    Fintype (Column d m a Δ) := by
  unfold Column
  infer_instance

end Nagata.FiniteExponents

end

section

namespace Nagata.FiniteExponents

/-- This general endpoint enumeration agrees with the theta indices whenever
that lemma's nonintegrality hypothesis holds. -/
theorem openIntegerInterval_eq_thetaIndices (U : ℝ) (n : ℤ)
    (hU : U ∉ Set.range (Int.cast : ℤ → ℝ)) :
    openIntegerInterval U (U + (n : ℝ)) = Nagata.W09.thetaIndices U n := by
  ext K
  exact (mem_openIntegerInterval).trans (Nagata.W09.mem_thetaIndices_iff hU).symm

end Nagata.FiniteExponents

end

end OAI
