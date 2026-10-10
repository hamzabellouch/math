import OAI.NumberTheory.DukePrimeDegree.Geometry.HorosphereCoordinates

namespace OAI

/-!
# Global coordinates on the contracting horosphere

The shared `(i,j)` entry belongs to the row coordinate. The remaining
column coordinates vanish at both `i` and `j`. This gives an actual
homeomorphism, with polynomial inverse, rather than only a parametrization.
-/

noncomputable section
open Matrix
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

instance rootHorosphereTopology {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    TopologicalSpace (rootHorosphereGroup hij) :=
  inferInstanceAs (TopologicalSpace {g : G n // RootHorosphereShape i j g})

abbrev HorosphereRow {n : ℕ} (i : Fin n) := {a : Fin n → ℝ // a i = 0}
abbrev HorosphereColumn {n : ℕ} (i j : Fin n) :=
  {b : Fin n → ℝ // b i = 0 ∧ b j = 0}

def horosphereCoordinates {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : rootHorosphereGroup hij) : HorosphereRow i × HorosphereColumn i j :=
  (⟨horosphereRowCoordinates i g.val, horosphereRowCoordinates_self g.val g.prop⟩,
   ⟨horosphereColumnCoordinates i j g.val,
    by simp [horosphereColumnCoordinates], horosphereColumnCoordinates_self g.val g.prop⟩)

def horosphereFromCoordinates {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (p : HorosphereRow i × HorosphereColumn i j) : rootHorosphereGroup hij :=
  ⟨rootColumnElement j p.2.val p.2.prop.2 * rootRowElement i p.1.val p.1.prop,
   rootHorosphereShape_mul hij (rootColumnElement_shape i j p.2.val p.2.prop.2)
     (rootRowElement_shape i j p.1.val p.1.prop)⟩

lemma horosphereFromCoordinates_coordinates {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : rootHorosphereGroup hij) :
    horosphereFromCoordinates hij (horosphereCoordinates hij g) = g := by
  apply Subtype.ext
  exact (rootHorosphere_column_row_factorization hij g.val g.prop).symm

lemma horosphereCoordinates_fromCoordinates {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (p : HorosphereRow i × HorosphereColumn i j) :
    horosphereCoordinates hij (horosphereFromCoordinates hij p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    funext s
    change (rootColumnElement j p.2.val p.2.prop.2 * rootRowElement i p.1.val p.1.prop).val i s -
      (1 : Matrix (Fin n) (Fin n) ℝ) i s = p.1.val s
    rw [rootColumn_mul_rootRow_entry hij]
    simp [p.2.prop.1]
  · apply Subtype.ext
    funext r
    change (if r = i then 0 else
      (rootColumnElement j p.2.val p.2.prop.2 * rootRowElement i p.1.val p.1.prop).val r j -
        (1 : Matrix (Fin n) (Fin n) ℝ) r j) = p.2.val r
    by_cases hr : r = i
    · subst r
      simp [p.2.prop.1]
    · rw [ite_eq_right hr, rootColumn_mul_rootRow_entry hij]
      simp [hr]

lemma continuous_horosphereCoordinates {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Continuous (horosphereCoordinates hij) := by
  have hc : Continuous (fun g : rootHorosphereGroup hij => g.val) :=
    continuous_subtype_val
  have hm : Continuous (fun g : rootHorosphereGroup hij => g.val.val) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous.comp hc
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    apply continuous_pi
    intro s
    change Continuous (fun g : rootHorosphereGroup hij =>
      g.val.val i s - (1 : Matrix (Fin n) (Fin n) ℝ) i s)
    exact (((continuous_apply s).comp ((continuous_apply i).comp hm)).sub continuous_const)
  · apply Continuous.subtype_mk
    apply continuous_pi
    intro r
    change Continuous (fun g : rootHorosphereGroup hij =>
      if r = i then 0 else g.val.val r j - (1 : Matrix (Fin n) (Fin n) ℝ) r j)
    split_ifs
    · exact continuous_const
    · exact (((continuous_apply j).comp ((continuous_apply r).comp hm)).sub continuous_const)

lemma continuous_horosphereFromCoordinates {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Continuous (horosphereFromCoordinates hij) := by
  apply Continuous.subtype_mk
  apply Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.continuous_iff.mpr
  change Continuous (fun p : HorosphereRow i × HorosphereColumn i j =>
    (horosphereFromCoordinates hij p).val.val)
  apply continuous_pi
  intro r
  apply continuous_pi
  intro s
  have he (p : HorosphereRow i × HorosphereColumn i j) :
      (horosphereFromCoordinates hij p).val.val r s =
        (1 : Matrix (Fin n) (Fin n) ℝ) r s + (if s = j then p.2.val r else 0) +
          (if r = i then p.1.val s else 0) := rootColumn_mul_rootRow_entry hij _ _ _ _ r s
  simp_rw [he]
  apply Continuous.add
  · apply Continuous.add continuous_const
    split_ifs
    · exact (continuous_apply r).comp (continuous_subtype_val.comp continuous_snd)
    · exact continuous_const
  · split_ifs
    · exact (continuous_apply s).comp (continuous_subtype_val.comp continuous_fst)
    · exact continuous_const

def horosphereHomeomorph {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    rootHorosphereGroup hij ≃ₜ HorosphereRow i × HorosphereColumn i j where
  toFun := horosphereCoordinates hij
  invFun := horosphereFromCoordinates hij
  left_inv := horosphereFromCoordinates_coordinates hij
  right_inv := horosphereCoordinates_fromCoordinates hij
  continuous_toFun := continuous_horosphereCoordinates hij
  continuous_invFun := continuous_horosphereFromCoordinates hij

end DukePrimeDegree

end

end OAI
