import Mathlib
import OAI.Computability.MaxCut.Games.RowErasureSliceQuotient
import OAI.Computability.MaxCut.Games.OrientationVectors

namespace OAI

noncomputable section

section

open scoped BigOperators

namespace MaxCutGames.Gadget.OrientedBlockKernel

open Quadratic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The actual binary-linear embedding belonging to an oriented child. -/
def orientedBlockLinear (i : BlockOrientationIndex F) :
    Vec F →ₗ[ZMod 2] Vec F × Vec F :=
  (U (lineGenerator i.1)).subtype.comp i.2.toLinearMap

/-- The nonlinear-change indicator for the actual oriented quadratic block. -/
def orientedBlockChange (i : BlockOrientationIndex F) (p : Vec F × Vec F)
    (d : Vec F) : ℚ := by
  classical
  exact if blockObservable (p + orientedBlockLinear i d) ≠ blockObservable p then 1 else 0

variable [∀ A : FieldLine F, Fintype (BlockOrientation A)]

/-- For one fixed field line, random orientation sends a fixed nonzero
logical difference uniformly onto that line's nonzero block perturbations. -/
theorem mean_orientations_change (A : FieldLine F) (p : Vec F × Vec F)
    (d : Vec F) (hd : d ≠ 0) :
    (𝔼 J : BlockOrientation A, orientedBlockChange ⟨A, J⟩ p d) =
      1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1) := by
  classical
  let : Finite (U (lineGenerator A) ≃ₗ[ZMod 2] U (lineGenerator A)) := DFunLike.finite _
  let := Fintype.ofFinite (U (lineGenerator A) ≃ₗ[ZMod 2] U (lineGenerator A))
  calc
    _ = nonzeroBlockChangeProbability (lineGenerator A) p := by
      unfold nonzeroBlockChangeProbability orientedBlockChange
      simp only [Fintype.expect_eq_sum_div_card]
      exact OrientationVectors.mean_iso_nonzero (chosenBlockOrientation A) d hd
        (fun u => if blockObservable (p + (u.val : Vec F × Vec F)) ≠
          blockObservable p then 1 else 0)
    _ = _ := nonzeroBlockChangeProbability_eq _ (lineGenerator_ne_zero A) p

variable [Fintype (FieldLine F)] [Fintype (Vec F ≃ₗ[ZMod 2] Vec F)]

/-- Equal orientation-fiber sizes make the pair-index average exactly an
independent uniform line followed by a uniform orientation of that line. -/
theorem mean_block_pairs (f : BlockOrientationIndex F → ℚ) :
    (𝔼 i : BlockOrientationIndex F, f i) =
      𝔼 A : FieldLine F, 𝔼 J : BlockOrientation A, f ⟨A, J⟩ := by
  classical
  calc
    _ = 𝔼 z : FieldLine F × (Vec F ≃ₗ[ZMod 2] Vec F),
        f ((blockOrientationIndexEquiv (F := F)).symm z) := by
      exact Fintype.expect_equiv (blockOrientationIndexEquiv (F := F)) _ _
        (fun i => by simp)
    _ = 𝔼 A : FieldLine F, 𝔼 a : Vec F ≃ₗ[ZMod 2] Vec F,
        f ⟨A, (blockOrientationEquiv A).symm a⟩ := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      rfl
    _ = _ := by
      apply Finset.expect_congr rfl
      intro A _
      exact Fintype.expect_equiv (blockOrientationEquiv A).symm _ _ (fun _ => rfl)

/-- Pointwise in the initial aggregate: the actual oriented-child average
has the exact one-level nonlinear survival rate. -/
theorem mean_oriented_block_change (p : Vec F × Vec F) (d : Vec F) (hd : d ≠ 0) :
    (𝔼 i : BlockOrientationIndex F, orientedBlockChange i p d) =
      1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1) := by
  classical
  have : Nonempty (FieldLine F) := Fintype.card_pos_iff.mp (by
    simpa only [Nat.card_eq_fintype_card] using (card_FieldLine_pos (F := F)))
  rw [mean_block_pairs]
  simp_rw [mean_orientations_change _ p d hd]
  exact Fintype.expect_const _

/-- The averaged block kernel required by the parent-noise recurrence,
now proved for the concrete quadratic construction. -/
theorem mean_oriented_block_kernel (d : Vec F) (hd : d ≠ 0) :
    (𝔼 i : BlockOrientationIndex F, 𝔼 p : Vec F × Vec F,
      orientedBlockChange i p d) =
      1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1) := by
  rw [Finset.expect_comm]
  simp_rw [mean_oriented_block_change _ d hd]
  exact Fintype.expect_const _

end MaxCutGames.Gadget.OrientedBlockKernel
end

namespace MaxCutGames.Quadratic

section

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
theorem squareMap_injective : Function.Injective (fun x : F => x ^ 2) := by
  intro x y h
  change x ^ 2 = y ^ 2 at h
  have hs : (x + y) ^ 2 = 0 := by
    rw [CharTwo.add_sq, h, CharTwo.add_self_eq_zero]
  have hz : x + y = 0 := (sq_eq_zero_iff).mp hs
  exact (add_eq_zero_iff_eq_neg.mp hz).trans (CharTwo.neg_eq y)

/-- The unique square root, obtained by bijectivity of the finite square map. -/
noncomputable def squareRoot (c : F) : F :=
  Classical.choose (Finite.surjective_of_injective squareMap_injective c)

@[simp] theorem squareRoot_sq (c : F) : squareRoot c ^ 2 = c :=
  Classical.choose_spec (Finite.surjective_of_injective squareMap_injective c)

@[simp] theorem squareRoot_of_sq (c : F) : squareRoot (c ^ 2) = c := by
  apply squareMap_injective
  exact squareRoot_sq _

theorem squareRoot_unique {c r : F} (h : r ^ 2 = c) : r = squareRoot c := by
  apply squareMap_injective
  change r ^ 2 = squareRoot c ^ 2
  rw [h, squareRoot_sq]

end

section

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The field trace to the binary prime field. -/
noncomputable abbrev traceBinary : F →ₗ[ZMod 2] ZMod 2 := Algebra.trace (ZMod 2) F

omit [CharP F 2] in
theorem trace_square (x : F) : traceBinary (x ^ 2) = traceBinary x := by
  simpa only [traceBinary, FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    ZMod.card] using
    Algebra.trace_eq_of_algEquiv
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F) x

/-- Moving a square from the first factor through the trace. -/
theorem trace_square_mul (t c : F) :
    traceBinary (t ^ 2 * c) = traceBinary (t * squareRoot c) := by
  calc
    traceBinary (t ^ 2 * c) = traceBinary ((t * squareRoot c) ^ 2) := by
      rw [mul_pow, squareRoot_sq]
    _ = traceBinary (t * squareRoot c) := trace_square _

omit [CharP F 2] in
/-- The trace pairing detects every nonzero field element. -/
theorem trace_mul_vanish_iff (a : F) :
    (∀ t : F, traceBinary (t * a) = 0) ↔ a = 0 := by
  constructor
  · intro h
    apply (traceForm_nondegenerate (ZMod 2) F).1 a
    intro t
    simpa only [Algebra.traceForm_apply, mul_comm] using h t
  · rintro rfl
    simp

theorem trace_quadratic_vanish_iff (a c : F) :
    (∀ t : F, traceBinary (t * a + t ^ 2 * c) = 0) ↔ a = squareRoot c := by
  have heq (t : F) :
      traceBinary (t * a + t ^ 2 * c) = traceBinary (t * (a + squareRoot c)) := by
    rw [map_add, trace_square_mul, mul_add, map_add]
  simp_rw [heq]
  rw [trace_mul_vanish_iff, add_eq_zero_iff_eq_neg, CharTwo.neg_eq]

end

/-!
# Trace coordinates for families of binary characters

The trace pairing identifies the binary dual of `F³` with `F³` itself.  Its
inverse is linear, so a common-parent family of binary functionals produces
one binary-linear lift `g`, as required by the all-lifts genericity theorem.
-/

section

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
private theorem dot_add_first_inline_TraceDual (x y z : Vec F) :
    dot (x + y) z = dot x z + dot y z := by
  simp only [dot, Pi.add_apply]
  ring

/-- The trace dot product, as an actual binary bilinear form. -/
def traceDotForm : LinearMap.BilinForm (ZMod 2) (Vec F) where
  toFun z :=
    { toFun := fun y => traceBinary (dot z y)
      map_add' := by
        intro x y
        rw [dot_add_right, map_add]
      map_smul' := by
        intro c y
        have hc : c = 0 ∨ c = 1 := by
          fin_cases c
          · exact Or.inl rfl
          · exact Or.inr rfl
        rcases hc with rfl | rfl <;> simp }
  map_add' := by
    intro z w
    apply LinearMap.ext
    intro y
    change traceBinary (dot (z + w) y) =
      traceBinary (dot z y) + traceBinary (dot w y)
    rw [dot_add_first_inline_TraceDual, map_add]
  map_smul' := by
    intro c z
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl <;> ext y <;> simp

omit [Finite F] [CharP F 2] in
@[simp] theorem traceDotForm_apply (z y : Vec F) :
    traceDotForm z y = traceBinary (dot z y) := rfl

omit [CharP F 2] in
/-- Nondegeneracy holds coordinate by coordinate over the finite field. -/
theorem traceDotForm_nondegenerate :
    (traceDotForm (F := F)).Nondegenerate := by
  constructor
  · intro z hz
    ext i
    apply (trace_mul_vanish_iff (z i)).mp
    intro t
    have h := hz (Pi.single i t)
    have hd : dot z (Pi.single i t) = t * z i := by
      fin_cases i <;> simp [dot, mul_comm]
    simpa only [traceDotForm_apply, hd] using h
  · intro z hz
    ext i
    apply (trace_mul_vanish_iff (z i)).mp
    intro t
    have h := hz (Pi.single i t)
    have hd : dot (Pi.single i t) z = t * z i := by
      fin_cases i <;> simp [dot]
    simpa only [traceDotForm_apply, hd] using h

/-- The exact binary trace-pairing identification. -/
def traceDualEquiv : Vec F ≃ₗ[ZMod 2] (Vec F →ₗ[ZMod 2] ZMod 2) :=
  traceDotForm.toDual traceDotForm_nondegenerate

omit [CharP F 2] in
@[simp] theorem traceDualEquiv_apply (z y : Vec F) :
    traceDualEquiv z y = traceBinary (dot z y) := rfl

omit [CharP F 2] in
@[simp] theorem traceDualEquiv_symm_apply
    (γ : Vec F →ₗ[ZMod 2] ZMod 2) (y : Vec F) :
    traceBinary (dot (traceDualEquiv.symm γ) y) = γ y := by
  change traceDualEquiv (traceDualEquiv.symm γ) y = γ y
  rw [LinearEquiv.apply_symm_apply]

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- Taking trace coordinates preserves linear dependence on the family index. -/
def representTraceFamily (γ : W →ₗ[ZMod 2] (Vec F →ₗ[ZMod 2] ZMod 2)) :
    W →ₗ[ZMod 2] Vec F :=
  traceDualEquiv.symm.toLinearMap.comp γ

omit [CharP F 2] in
theorem representTraceFamily_spec
    (γ : W →ₗ[ZMod 2] (Vec F →ₗ[ZMod 2] ZMod 2)) (z : W) (y : Vec F) :
    traceBinary (dot (representTraceFamily γ z) y) = γ z y :=
  traceDualEquiv_symm_apply (γ z) y

end

/-!
# The binary trace annihilator of a quadratic-block hyperplane

The trace annihilator of the field hyperplane perpendicular to a nonzero
vector is exactly its field line.  Scaling test vectors first upgrades binary
trace orthogonality to field-valued orthogonality; explicit coordinate test
vectors then identify the annihilator.  No earlier gadget result is used.
-/

section

variable {F : Type*} [Field F]

private theorem dot_sub_right_inline_BlockTrace (v y z : Vec F) :
    dot v (y - z) = dot v y - dot v z := by
  simp [dot]
  ring

private theorem dot_single_inline_BlockTrace (v : Vec F) (i : Fin 3) (a : F) :
    dot v (Pi.single i a) = v i * a := by
  fin_cases i <;> simp [dot]

/-- The field-valued annihilator of a nonzero vector's perpendicular
hyperplane is the line generated by that vector. -/
theorem annihilator_hyperplane_iff_mem_line {v z : Vec F} (hv : v ≠ 0) :
    (∀ y ∈ hyperplane v, dot z y = 0) ↔ z ∈ line v := by
  constructor
  · intro hz
    have hv' : ∃ i : Fin 3, v i ≠ 0 := by
      by_contra! h
      exact hv (funext h)
    obtain ⟨i, hi⟩ := hv'
    apply (mem_line_iff v z).mpr
    refine ⟨z i / v i, ?_⟩
    ext j
    have hy : Pi.single j (1 : F) - (v j / v i) • Pi.single i (1 : F) ∈
        hyperplane v := by
      rw [mem_hyperplane, dot_sub_right_inline_BlockTrace, dot_smul_right, dot_single_inline_BlockTrace, dot_single_inline_BlockTrace]
      simp [div_mul_cancel₀ _ hi]
    have hzero := hz _ hy
    rw [dot_sub_right_inline_BlockTrace, dot_smul_right, dot_single_inline_BlockTrace, dot_single_inline_BlockTrace,
      mul_one, mul_one, sub_eq_zero] at hzero
    change (z i / v i) * v j = z j
    rw [hzero]
    simp only [div_eq_mul_inv]
    ring
  · intro hz y hy
    obtain ⟨t, rfl⟩ := (mem_line_iff v z).mp hz
    rw [dot_smul_left, (mem_hyperplane v y).mp hy, mul_zero]

variable [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [CharP F 2] in
/-- Exact trace-annihilator identity for the field hyperplane.  Trace
nondegeneracy is provided by the proved finite-field trace pairing theorem. -/
theorem trace_annihilator_hyperplane_iff_mem_line {v z : Vec F} (hv : v ≠ 0) :
    (∀ y ∈ hyperplane v, traceBinary (dot z y) = 0) ↔ z ∈ line v := by
  rw [← annihilator_hyperplane_iff_mem_line hv]
  constructor
  · intro hz y hy
    apply (trace_mul_vanish_iff (dot z y)).mp
    intro t
    have ht := hz (t • y) ((hyperplane v).smul_mem t hy)
    simpa only [dot_smul_right] using ht
  · intro hz y hy
    rw [hz y hy, map_zero]

omit [CharP F 2] in
/-- The same annihilator identity in set notation, using the actual trace. -/
theorem trace_annihilator_hyperplane (v : Vec F) (hv : v ≠ 0) :
    {z : Vec F | ∀ y ∈ hyperplane v, Algebra.trace (ZMod 2) F (dot z y) = 0} =
      (line v : Set (Vec F)) := by
  ext z
  exact trace_annihilator_hyperplane_iff_mem_line hv

end

/-!
# Character kernels on quadratic blocks

The character with horizontal coefficient `g` and vertical coefficient `z`
annihilates the block attached to `Fz` precisely when the alignment
equation holds.  The predicate below is annihilation of the actual binary
submodule, rather than an abstract replacement for that condition.
-/

section

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite F] [Algebra (ZMod 2) F] in
/-- A field-valued identity before applying the binary trace. -/
theorem dot_Q_smul (z : Vec F) (t : F) :
    dot z (Q (t • z)) = t ^ 2 * (z 0 * z 1 * z 2) := by
  change z 0 * ((t * z 1) * (t * z 2)) +
      z 1 * ((t * z 0) * (t * z 2)) +
      z 2 * ((t * z 0) * (t * z 1)) = _
  calc
    _ = (t ^ 2 * (z 0 * z 1 * z 2)) +
        (t ^ 2 * (z 0 * z 1 * z 2)) +
        (t ^ 2 * (z 0 * z 1 * z 2)) := by ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]

/-- The binary character with separate horizontal and vertical coefficients. -/
noncomputable def blockCharacter (g z : Vec F) (p : Vec F × Vec F) : ZMod 2 :=
  traceBinary (dot g p.1 + dot z p.2)

/-- Literal annihilation of every vector in the block attached to `v`. -/
def BlockAnnihilates (g z v : Vec F) : Prop :=
  ∀ p ∈ U v, blockCharacter g z p = 0

omit [Finite F] in
theorem blockCharacter_on_quadratic (g z : Vec F) (t : F) :
    blockCharacter g z (t • z, Q (t • z)) =
      traceBinary (t * dot g z + t ^ 2 * (z 0 * z 1 * z 2)) := by
  simp only [blockCharacter, dot_smul_right, dot_Q_smul]

/-- The exact quadratic-block kernel criterion on the line of the character. -/
theorem blockAnnihilates_self_iff (g z : Vec F) :
    BlockAnnihilates g z z ↔ dot g z = squareRoot (z 0 * z 1 * z 2) := by
  constructor
  · intro h
    apply (trace_quadratic_vanish_iff _ _).mp
    intro t
    have hm : (t • z, Q (t • z)) ∈ U z := by
      simpa only [add_zero] using pair_mem_U z (t • z) 0
        ((mem_line_iff z (t • z)).mpr ⟨t, rfl⟩) (Submodule.zero_mem _)
    simpa only [blockCharacter_on_quadratic] using h _ hm
  · intro h p hp
    obtain ⟨a, ha, w, hw, rfl⟩ := (mem_U_iff_exists z p).mp hp
    obtain ⟨t, rfl⟩ := (mem_line_iff z a).mp ha
    change traceBinary (dot g (t • z) + dot z (Q (t • z) + w)) = 0
    rw [dot_add_right, (mem_hyperplane z w).mp hw, add_zero,
      dot_smul_right, dot_Q_smul]
    exact (trace_quadratic_vanish_iff _ _).mpr h t

omit [Finite F] in
/-- The binary block is independent of the nonzero generator of its field line. -/
theorem U_smul_ne_zero (v : Vec F) {t : F} (ht : t ≠ 0) : U (t • v) = U v := by
  have hl : line (t • v) = line v :=
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ht) v
  ext p
  simp only [mem_U, hl, dot_smul_left, mul_eq_zero, ht, false_or]

omit [Finite F] in
theorem U_eq_of_nonzero_mem_line {v z : Vec F} (hz : z ≠ 0)
    (hm : z ∈ line v) : U z = U v := by
  obtain ⟨t, rfl⟩ := (mem_line_iff v z).mp hm
  have ht : t ≠ 0 := by
    intro ht
    apply hz
    simp [ht]
  exact U_smul_ne_zero v ht

/-- A character in a block's kernel has its vertical coefficient on that line. -/
theorem mem_line_of_blockAnnihilates {g z v : Vec F} (hv : v ≠ 0)
    (h : BlockAnnihilates g z v) : z ∈ line v := by
  apply (trace_annihilator_hyperplane_iff_mem_line hv).mp
  intro y hy
  have hm : (0, y) ∈ U v := by
    simpa only [Q_zero, zero_add] using
      pair_mem_U v 0 y (Submodule.zero_mem _) hy
  simpa only [blockCharacter, dot_zero_right, zero_add] using h _ hm

/-- Full nonzero-character criterion, including the field-line condition. -/
theorem blockAnnihilates_iff {g z v : Vec F} (hv : v ≠ 0) (hz : z ≠ 0) :
    BlockAnnihilates g z v ↔
      z ∈ line v ∧ dot g z = squareRoot (z 0 * z 1 * z 2) := by
  constructor
  · intro h
    have hm := mem_line_of_blockAnnihilates hv h
    refine ⟨hm, (blockAnnihilates_self_iff g z).mp ?_⟩
    simpa only [BlockAnnihilates, U_eq_of_nonzero_mem_line hz hm] using h
  · rintro ⟨hm, ha⟩
    have h := (blockAnnihilates_self_iff g z).mpr ha
    simpa only [BlockAnnihilates, U_eq_of_nonzero_mem_line hz hm] using h

end

section

open Module
open scoped BigOperators Matrix

variable {R F V ι n E : Type*}
variable [Field R] [Field F] [Algebra R F]
variable [AddCommGroup V] [Module R V]
variable [Fintype ι] [Fintype n]

/-- The `|n| * |ι|` alignment columns for a fixed parametrization and input set.
The input set is represented by any map `point : E → V`; no injectivity is
needed for the exact algebraic equivalence. -/
def alignmentMatrix (b : Basis ι R V) (point : E → V) (z : V → n → F) :
    Matrix E (n × ι) F :=
  fun e ij => algebraMap R F (b.repr (point e) ij.2) * z (point e) ij.1

/-- Basis values of a linear lift give the coefficients of the alignment
column combination.  The identity holds for every lift, without selecting
one in advance of the parametrization. -/
theorem dot_lift_eq_alignment_mulVec (b : Basis ι R V)
    (point : E → V) (z : V → n → F) (g : V →ₗ[R] (n → F)) (e : E) :
    (∑ i, z (point e) i * g (point e) i) =
      (alignmentMatrix b point z *ᵥ (fun ij => g (b ij.2) ij.1)) e := by
  have hg : g (point e) = ∑ j, b.repr (point e) j • g (b j) := by
    calc
      g (point e) = g (∑ j, b.repr (point e) j • b j) :=
        congrArg g (b.sum_repr (point e)).symm
      _ = ∑ j, b.repr (point e) j • g (b j) := by simp only [map_sum, map_smul]
  rw [hg]
  simp only [Matrix.mulVec, dotProduct, alignmentMatrix,
    Finset.sum_apply, Algebra.smul_def, Pi.mul_apply,
    Pi.algebraMap_apply, Finset.mul_sum,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Existence of *any* linear lift aligning on the chosen inputs is one
column-membership event.  In particular there is no field-size-dependent
union bound over the possible lifts. -/
theorem exists_lift_alignment_iff_mem_range (b : Basis ι R V)
    (point : E → V) (z : V → n → F) (c : E → F) :
    (∃ g : V →ₗ[R] (n → F), ∀ e,
      (∑ i, z (point e) i * g (point e) i) = c e) ↔
      c ∈ LinearMap.range (alignmentMatrix b point z).mulVecLin := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨fun ij => g (b ij.2) ij.1, ?_⟩
    ext e
    change (alignmentMatrix b point z *ᵥ (fun ij => g (b ij.2) ij.1)) e = c e
    rw [← dot_lift_eq_alignment_mulVec]
    exact hg e
  · rintro ⟨u, hu⟩
    let g : V →ₗ[R] (n → F) := b.constr R (fun j i => u (i, j))
    refine ⟨g, ?_⟩
    intro e
    rw [dot_lift_eq_alignment_mulVec b point z g e]
    have hg : (fun ij : n × ι => g (b ij.2) ij.1) = u := by
      funext ij
      exact congrFun (b.constr_basis R (fun j i => u (i, j)) ij.2) ij.1
    rw [hg]
    exact congrFun hu e

/-- The column-space dimension is at most the number of free basis values.
For three field coordinates and a binary basis of size `r`, this is `3r`. -/
theorem finrank_alignment_range_le (b : Basis ι R V)
    (point : E → V) (z : V → n → F) [Fintype E] :
    Module.finrank F (LinearMap.range (alignmentMatrix b point z).mulVecLin) ≤
      Fintype.card n * Fintype.card ι := by
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod] using
      (LinearMap.finrank_range_le (alignmentMatrix b point z).mulVecLin)

end

section

open Module
open scoped BigOperators

section AlignmentEvents

variable {R F V ι n : Type*}
variable [Field R] [Field F] [Algebra R F]
variable [AddCommGroup V] [Module R V]
variable [Fintype V] [Fintype ι] [Fintype n]

/-- Nonzero inputs aligned by a specified linear lift. -/
def alignmentEvent (z : V → n → F) (g : V →ₗ[R] (n → F)) (c : V → F) :
    Finset V := by
  classical
  exact Finset.univ.filter (fun v => v ≠ 0 ∧ (∑ i, z v i * g v i) = c v)

/-- Exact finite bad-set reduction.  Its right hand side quantifies only over
input sets, while column membership already accounts for every linear lift. -/
theorem all_lifts_bound_iff_subsets (b : Basis ι R V) (z : V → n → F)
    (c : V → F) (k : ℕ) :
    (∀ g : V →ₗ[R] (n → F), (alignmentEvent z g c).card ≤ k) ↔
      ∀ E : Finset V, 0 ∉ E → E.card = k + 1 →
        (fun e : E => c e) ∉
          LinearMap.range (alignmentMatrix b (fun e : E => (e : V)) z).mulVecLin := by
  classical
  constructor
  · intro h E hzero hcard hmem
    obtain ⟨g, hg⟩ := (exists_lift_alignment_iff_mem_range b
      (fun e : E => (e : V)) z (fun e : E => c e)).mpr hmem
    have hsubset : E ⊆ alignmentEvent z g c := by
      intro v hv
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hg ⟨v, hv⟩⟩
      intro hvzero
      exact hzero (hvzero ▸ hv)
    have hle := (Finset.card_le_card hsubset).trans (h g)
    omega
  · intro h g
    by_contra hbad
    have hlarge : k + 1 ≤ (alignmentEvent z g c).card := by omega
    obtain ⟨E, hsub, hcard⟩ := Finset.exists_subset_card_eq hlarge
    have hzero : (0 : V) ∉ E := by
      intro hz
      have hh := (Finset.mem_filter.mp (hsub hz)).2.1
      exact hh rfl
    apply h E hzero hcard
    apply (exists_lift_alignment_iff_mem_range b
      (fun e : E => (e : V)) z (fun e : E => c e)).mp
    refine ⟨g, ?_⟩
    intro e
    exact (Finset.mem_filter.mp (hsub e.property)).2.2

theorem all_lifts_bound_of_card_le (z : V → n → F) (c : V → F) (k : ℕ)
    (hcard : Fintype.card V - 1 ≤ k) (g : V →ₗ[R] (n → F)) :
    (alignmentEvent z g c).card ≤ k := by
  classical
  have hsub : alignmentEvent z g c ⊆ Finset.univ.erase (0 : V) := by
    intro v hv
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hv).2.1, Finset.mem_univ _⟩
  have hle := Finset.card_le_card hsub
  simpa using hle.trans (by simpa using hcard)

end AlignmentEvents

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The cubic square-root right hand side of the alignment equation. -/
def alignmentRightHandSide (z : Fin 3 → F) : F := squareRoot (z 0 * z 1 * z 2)

/-- The complete genericity predicate. The universal linear
map quantifier occurs inside the property of the selected subspace. -/
def IsGeneric (S : Submodule (ZMod 2) (Fin 3 → F)) : Prop := by
  classical
  exact
    (∀ z w : S, z ≠ 0 → w ≠ 0 →
      (∃ t : F, (z : Fin 3 → F) = t • (w : Fin 3 → F)) → z = w) ∧
    (∀ g : S →ₗ[ZMod 2] (Fin 3 → F),
      (alignmentEvent (R := ZMod 2) (fun z : S => (z : Fin 3 → F)) g
        (fun z : S => alignmentRightHandSide (z : Fin 3 → F))).card ≤
          3 * Module.finrank (ZMod 2) S)

end

/-!
# Rank-loss accounting for quadratic blocks

A nonzero kernel character determines the field line of a lossy block.  On
a generic space there is at most one such character on each field line, so
the rank drops by at most one.  Counting the possible determining characters
also bounds the number of lossy lines.  These are deterministic statements;
the random orientation may be selected only after this data is fixed.
-/

variable {R V W I : Type*} [Field R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

/-- A vector space with at most one nonzero vector has dimension at most one.
The statement is deliberately independent of any characteristic assumption. -/
theorem finrank_le_one_of_nonzero_unique
    (h : ∀ v w : V, v ≠ 0 → w ≠ 0 → v = w) :
    Module.finrank R V ≤ 1 := by
  classical
  by_cases hex : ∃ v : V, v ≠ 0
  · obtain ⟨v, hv⟩ := hex
    apply finrank_le_one v
    intro w
    by_cases hw : w = 0
    · exact ⟨0, by simp [hw]⟩
    · exact ⟨1, by simpa using h v w hv hw⟩
  · apply finrank_le_one (0 : V)
    intro w
    have hw : w = 0 := by
      by_contra hw
      exact hex ⟨w, hw⟩
    exact ⟨0, by simp [hw]⟩

/-- Nonproportionality of a generic character space makes every child kernel
at most one-dimensional once the field-line kernel criterion is applied. -/
theorem finrank_ker_le_one_of_nonzero_unique (f : V →ₗ[R] W)
    (h : ∀ v w : V, v ≠ 0 → w ≠ 0 → f v = 0 → f w = 0 → v = w) :
    Module.finrank R f.ker ≤ 1 := by
  apply finrank_le_one_of_nonzero_unique
  intro v w hv hw
  apply Subtype.ext
  apply h v w
  · intro hv0
    apply hv
    exact Subtype.ext hv0
  · intro hw0
    apply hw
    exact Subtype.ext hw0
  · exact v.property
  · exact w.property

/-- Consequently the image rank can lose at most one dimension. -/
theorem finrank_source_le_range_add_one [FiniteDimensional R V]
    (f : V →ₗ[R] W)
    (h : ∀ v w : V, v ≠ 0 → w ≠ 0 → f v = 0 → f w = 0 → v = w) :
    Module.finrank R V ≤ Module.finrank R f.range + 1 := by
  have hk := finrank_ker_le_one_of_nonzero_unique f h
  have hr := f.finrank_range_add_finrank_ker
  omega

variable [Fintype V] [Fintype I] [DecidableEq I]

/-- The actual finite event of a child map having a nonzero kernel. -/
def lossIndices (f : I → V →ₗ[R] W) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => ∃ v : V, v ≠ 0 ∧ f i v = 0)

def alignedCharacters (aligned : V → Prop) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => v ≠ 0 ∧ aligned v)

theorem lossIndices_subset_image (f : I → V →ₗ[R] W)
    (aligned : V → Prop) (lineOf : V → I)
    (hkernel : ∀ i v, v ≠ 0 → f i v = 0 → aligned v ∧ lineOf v = i) :
    lossIndices f ⊆ (alignedCharacters aligned).image lineOf := by
  classical
  intro i hi
  obtain ⟨v, hv, hfv⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨halign, hline⟩ := hkernel i v hv hfv
  apply Finset.mem_image.mpr
  exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv, halign⟩, hline⟩

/-- The cardinality bound does not union over lifts or orientations. -/
theorem card_lossIndices_le_card_aligned (f : I → V →ₗ[R] W)
    (aligned : V → Prop) (lineOf : V → I)
    (hkernel : ∀ i v, v ≠ 0 → f i v = 0 → aligned v ∧ lineOf v = i) :
    (lossIndices f).card ≤ (alignedCharacters aligned).card := by
  classical
  exact (Finset.card_le_card (lossIndices_subset_image f aligned lineOf hkernel)).trans
    (Finset.card_image_le (s := alignedCharacters aligned) (f := lineOf))

theorem card_lossIndices_le (f : I → V →ₗ[R] W)
    (aligned : V → Prop) (lineOf : V → I) (r : ℕ)
    (hkernel : ∀ i v, v ≠ 0 → f i v = 0 → aligned v ∧ lineOf v = i)
    (hgeneric : (alignedCharacters aligned).card ≤ 3 * r) :
    (lossIndices f).card ≤ 3 * r :=
  (card_lossIndices_le_card_aligned f aligned lineOf hkernel).trans hgeneric

theorem card_lossIndices_le_nonzero (f : I → V →ₗ[R] W)
    (lineOf : V → I)
    (hkernel : ∀ i v, v ≠ 0 → f i v = 0 → lineOf v = i) :
    (lossIndices f).card ≤ Fintype.card V - 1 := by
  classical
  have h := card_lossIndices_le_card_aligned f (fun _ => True) lineOf
    (fun i v hv hfv => ⟨trivial, hkernel i v hv hfv⟩)
  simpa [alignedCharacters, Finset.filter_ne'] using h

end MaxCutGames.Quadratic

end

end OAI
