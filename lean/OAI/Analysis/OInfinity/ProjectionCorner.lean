import OAI.Analysis.OInfinity.RowCocycleDefect

namespace OAI

/-! # Unital C⋆ structure and unitary paths in a projection corner

The corner has unit `q`; its inclusion in the ambient algebra is nonunital.
A corner unitary becomes an ambient unitary by adding `1-q`, preserving
norm differences and therefore the quantitative path estimates.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

def projectionCornerAlgebra (q : E) (hq : star q = q) : NonUnitalStarSubalgebra ℂ E where
  carrier := {x | q * x = x ∧ x * q = x}
  zero_mem' := by simp
  add_mem' hx hy := by
    exact ⟨by rw [mul_add, hx.1, hy.1], by rw [add_mul, hx.2, hy.2]⟩
  mul_mem' hx hy := ⟨by rw [← mul_assoc, hx.1], by rw [mul_assoc, hy.2]⟩
  smul_mem' c x hx :=
    ⟨by rw [mul_smul_comm, hx.1], by rw [smul_mul_assoc, hx.2]⟩
  star_mem' hx := ⟨by simpa only [star_mul, hq] using congrArg star hx.2,
    by simpa only [star_mul, hq] using congrArg star hx.1⟩

lemma projectionCornerAlgebra_closed (q : E) (hq : star q = q) :
    IsClosed (projectionCornerAlgebra q hq : Set E) :=
  (isClosed_eq (by fun_prop) continuous_id).inter
    (isClosed_eq (by fun_prop) continuous_id)

/-- The closed supported corner, equipped below with unit `q`. -/
abbrev ProjectionCorner (q : E) (hq : star q = q) (_hqq : q * q = q) : Type _ :=
  projectionCornerAlgebra q hq

instance projectionCornerClosed (q : E) (hq : star q = q) :
    IsClosed (projectionCornerAlgebra q hq : Set E) := projectionCornerAlgebra_closed q hq

instance projectionCornerSemiring (q : E) (hq : star q = q) (hqq : q * q = q) :
    Semiring (ProjectionCorner q hq hqq) where
  __ : NonUnitalSemiring (ProjectionCorner q hq hqq) :=
    inferInstanceAs (NonUnitalSemiring (projectionCornerAlgebra q hq))
  one := ⟨q, hqq, hqq⟩
  one_mul x := Subtype.ext x.property.1
  mul_one x := Subtype.ext x.property.2

instance projectionCornerRing (q : E) (hq : star q = q) (hqq : q * q = q) :
    Ring (ProjectionCorner q hq hqq) where
  __ : Semiring (ProjectionCorner q hq hqq) := projectionCornerSemiring q hq hqq
  __ : NonUnitalRing (ProjectionCorner q hq hqq) :=
    inferInstanceAs (NonUnitalRing (projectionCornerAlgebra q hq))

instance projectionCornerNormedRing (q : E) (hq : star q = q) (hqq : q * q = q) :
    NormedRing (ProjectionCorner q hq hqq) where
  __ : Ring (ProjectionCorner q hq hqq) := projectionCornerRing q hq hqq
  __ : NonUnitalNormedRing (ProjectionCorner q hq hqq) :=
    inferInstanceAs (NonUnitalNormedRing (projectionCornerAlgebra q hq))

instance projectionCornerAlgebraStructure (q : E) (hq : star q = q) (hqq : q * q = q) :
    Algebra ℂ (ProjectionCorner q hq hqq) :=
  Algebra.ofModule (fun _ _ _ => Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ => Subtype.ext (mul_smul_comm _ _ _))

instance projectionCornerNormedAlgebra (q : E) (hq : star q = q) (hqq : q * q = q) :
    NormedAlgebra ℂ (ProjectionCorner q hq hqq) where
  __ := projectionCornerAlgebraStructure q hq hqq
  norm_smul_le c x := by exact norm_smul_le c (x : E)

instance projectionCornerCStarAlgebra (q : E) (hq : star q = q) (hqq : q * q = q) :
    CStarAlgebra (ProjectionCorner q hq hqq) where
  __ : NormedRing (ProjectionCorner q hq hqq) := projectionCornerNormedRing q hq hqq
  __ : NormedAlgebra ℂ (ProjectionCorner q hq hqq) := projectionCornerNormedAlgebra q hq hqq
  __ : StarRing (ProjectionCorner q hq hqq) :=
    inferInstanceAs (StarRing (projectionCornerAlgebra q hq))
  __ : CompleteSpace (ProjectionCorner q hq hqq) :=
    inferInstanceAs (CompleteSpace (projectionCornerAlgebra q hq))
  __ : StarModule ℂ (ProjectionCorner q hq hqq) :=
    inferInstanceAs (StarModule ℂ (projectionCornerAlgebra q hq))
  norm_mul_self_le x := (CStarRing.norm_star_mul_self (x := (x : E))).symm.le

instance projectionCornerNontrivial (q : E) (hq : star q = q) (hqq : q * q = q)
    [NeZero q] : Nontrivial (ProjectionCorner q hq hqq) := by
  apply nontrivial_of_ne (0 : ProjectionCorner q hq hqq) 1
  intro h
  have he := congrArg (fun x : ProjectionCorner q hq hqq => (x : E)) h
  exact (NeZero.ne q) he.symm

/-- The algebra inclusion sends the corner unit to `q`. -/
def projectionCornerInclusion (q : E) (hq : star q = q) (hqq : q * q = q) :
    ProjectionCorner q hq hqq →⋆ₙₐ[ℂ] E where
  toFun x := x
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

lemma projectionCornerInclusion_one (q : E) (hq : star q = q) (hqq : q * q = q) :
    projectionCornerInclusion q hq hqq 1 = q := rfl

/-- Extending by the complementary identity gives an ambient unitary. -/
def projectionCornerUnitary (q : E) (hq : star q = q) (hqq : q * q = q)
    (u : unitary (ProjectionCorner q hq hqq)) : unitary E := by
  let x : E := (u : ProjectionCorner q hq hqq)
  have hl : q * x = x := (u : ProjectionCorner q hq hqq).property.1
  have hr : x * q = x := (u : ProjectionCorner q hq hqq).property.2
  have hxs : star x * x = q := congrArg
    (fun y : ProjectionCorner q hq hqq => (y : E)) u.property.1
  have hsx : x * star x = q := congrArg
    (fun y : ProjectionCorner q hq hqq => (y : E)) u.property.2
  have hls : q * star x = star x := by
    simpa only [star_mul, hq] using congrArg star hr
  have hrs : star x * q = star x := by
    simpa only [star_mul, hq] using congrArg star hl
  refine ⟨x + (1 - q), ?_, ?_⟩
  · change star (x + (1 - q)) * (x + (1 - q)) = 1
    simp only [star_add, star_sub, star_one, hq, add_mul, mul_add, mul_sub,
      sub_mul, one_mul, mul_one, hxs, hqq, hl, hrs]
    abel
  · change (x + (1 - q)) * star (x + (1 - q)) = 1
    simp only [star_add, star_sub, star_one, hq, add_mul, mul_add, mul_sub,
      sub_mul, one_mul, mul_one, hsx, hqq, hr, hls]
    abel

lemma projectionCornerUnitary_one (q : E) (hq : star q = q) (hqq : q * q = q) :
    projectionCornerUnitary q hq hqq 1 = 1 := by
  apply Subtype.ext
  change q + (1 - q) = 1
  abel

lemma projectionCornerUnitary_continuous (q : E) (hq : star q = q) (hqq : q * q = q) :
    Continuous (projectionCornerUnitary q hq hqq) := by
  apply Continuous.subtype_mk
  change Continuous (fun u : unitary (ProjectionCorner q hq hqq) =>
    ((u : ProjectionCorner q hq hqq) : E) + (1 - q))
  exact (continuous_subtype_val.comp continuous_subtype_val).add continuous_const

lemma projectionCornerUnitary_sub_norm (q : E) (hq : star q = q) (hqq : q * q = q)
    (u v : unitary (ProjectionCorner q hq hqq)) :
    ‖(projectionCornerUnitary q hq hqq u : E) - projectionCornerUnitary q hq hqq v‖ =
      ‖(u : ProjectionCorner q hq hqq) - v‖ := by
  change ‖(((u : ProjectionCorner q hq hqq) : E) + (1 - q)) -
    (((v : ProjectionCorner q hq hqq) : E) + (1 - q))‖ =
      ‖((u : ProjectionCorner q hq hqq) : E) - ((v : ProjectionCorner q hq hqq) : E)‖
  congr 1
  abel

/-- Quantitative paths lift to the ambient algebra with no loss. -/
lemma projectionCornerPath_controlled (q : E) (hq : star q = q) (hqq : q * q = q)
    {u v : unitary (ProjectionCorner q hq hqq)}
    (p : Path u v) (L : ℝ)
    (hp : ∀ a b, ‖(p a : ProjectionCorner q hq hqq) - p b‖ ≤ L * |(a : ℝ) - b|) :
    ∃ r : Path (projectionCornerUnitary q hq hqq u) (projectionCornerUnitary q hq hqq v),
      ∀ a b, ‖(r a : E) - r b‖ ≤ L * |(a : ℝ) - b| := by
  refine ⟨p.map (projectionCornerUnitary_continuous q hq hqq), ?_⟩
  intro a b
  exact (projectionCornerUnitary_sub_norm q hq hqq (p a) (p b)).trans_le (hp a b)

end WeakPureInfiniteness

end

end OAI
