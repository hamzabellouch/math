import OAI.NumberTheory.DukePrimeDegree.Dynamics.OrbitRecurrence
import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootShearing

namespace OAI

/-!
# Small relative lifts on the arithmetic quotient

Open quotient charts provide a neighborhood in which any two points are
related by a matrix in a prescribed identity neighborhood. This is the
local lifting step used with compactly controlled centralizer returns.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rightOrbitMap_isOpen {n : ℕ} (x : X n) :
    IsOpenMap (fun g : G n => rightAction x g) := by
  induction x using Quotient.inductionOn with
  | h q =>
    intro U hU
    change IsOpen ((fun g => Quotient.mk _ (q * g)) '' U)
    rw [← Set.image_image]
    exact (quotient_covering n).isOpenMap _ ((Homeomorph.mulLeft q).isOpenMap _ hU)

/-- Any identity neighborhood gives a quotient neighborhood with small
relative lifts between all of its points. -/
theorem exists_open_small_relative_lifts {n : ℕ}
    (x : X n) (W : Set (G n)) (hW : W ∈ 𝓝 1) :
    ∃ V : Set (X n), IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, ∀ z ∈ V, ∃ g ∈ W, rightAction y g = z := by
  obtain ⟨K, _, hK, hKsmall⟩ := exists_compact_close_parameter_neighborhood W hW (1 : G n)
  let V := (fun g => rightAction x g) '' interior K
  refine ⟨V, rightOrbitMap_isOpen x _ isOpen_interior, ?_, ?_⟩
  · exact ⟨1, mem_interior_iff_mem_nhds.mpr hK, by simp⟩
  · rintro y ⟨a, ha, rfl⟩ z ⟨b, hb, rfl⟩
    refine ⟨a⁻¹ * b, hKsmall a (interior_subset ha) b (interior_subset hb), ?_⟩
    rw [rightAction_mul]
    congr 1
    group

/-- The matrix-ball form needed for exceptional returns. -/
theorem exists_open_matrix_relative_lifts {n : ℕ} (x : X n) {r : ℝ} (hr : 0 < r) :
    ∃ V : Set (X n), IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, ∀ z ∈ V, ∃ g ∈ matrixBall n r, rightAction y g = z :=
  exists_open_small_relative_lifts x _ ((matrixBall_isOpen n r).mem_nhds (one_mem_matrixBall n hr))

/-- Right translations are a left action of the opposite subgroup. -/
@[instance_reducible] def rightSubgroupAction {n : ℕ} (C : Subgroup (G n)) :
    MulAction (MulOpposite C) (X n) where
  smul c x := rightAction x (c.unop : G n)
  one_smul x := by change rightAction x 1 = x; simp
  mul_smul c d x := by
    change rightAction x ((d.unop : G n) * (c.unop : G n)) =
      rightAction (rightAction x (d.unop : G n)) (c.unop : G n)
    exact (rightAction_mul x _ _).symm

lemma rightSubgroupAction_continuous {n : ℕ} (C : Subgroup (G n)) :
    let := rightSubgroupAction C
    ContinuousSMul (MulOpposite C) (X n) := by
  let := rightSubgroupAction C
  constructor
  exact (continuous_rightAction_uncurry n).comp
    (continuous_snd.prodMk ((continuous_subtype_val.comp MulOpposite.continuous_unop).comp continuous_fst))

end DukePrimeDegree

end

end OAI
