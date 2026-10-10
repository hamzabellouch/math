import OAI.NumberTheory.DukePrimeDegree.Dynamics.BlockDiagonalAlgebra
import OAI.NumberTheory.PrimePackets.ZetaResidues
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.Dimension.Free

namespace OAI

/-!
# Rational diagonal stabilizers of actual lattices

The rational coordinate space below is constructed from an actual lattice
matrix. Its diagonal stabilizer is a concrete subalgebra of real coordinate
functions, not a separately assumed field action. The absence of lattice
vectors on coordinate hyperplanes makes this algebra a field of degree
dividing the ambient dimension.
-/

noncomputable section
open Matrix Module Set
open scoped BigOperators Classical

namespace DukePrimeDegree
open PrimeDegreePackets

/-- Rational linear combinations of the rows of a real lattice matrix. -/
def rationalRowMap {n : ℕ} (g : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℝ) where
  toFun z := ∑ i, z i • g i
  map_add' z w := by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a z := by
    simp only [RingHom.id_apply, Pi.smul_apply, Finset.smul_sum, smul_smul, smul_eq_mul]

lemma rationalRowMap_apply {n : ℕ} (g : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℚ) :
    rationalRowMap g z = Matrix.vecMul (fun i => (z i : ℝ)) g := by
  ext i
  simp [rationalRowMap, Matrix.vecMul, dotProduct, Finset.sum_apply, Rat.smul_def]

lemma rationalRowMap_injective {n : ℕ} (g : G n) :
    Function.Injective (rationalRowMap g.val) := by
  intro z w h
  simp only [rationalRowMap_apply] at h
  have hu : IsUnit g.val := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [g.property]; simp)
  have H := Matrix.vecMul_injective_of_isUnit hu h
  exact funext (fun i => Rat.cast_injective (congrFun H i))

def rationalRowSpace {n : ℕ} (g : G n) : Submodule ℚ (Fin n → ℝ) :=
  LinearMap.range (rationalRowMap g.val)

instance {n : ℕ} (g : G n) : FiniteDimensional ℚ (rationalRowSpace g) :=
  Module.Finite.range _

lemma finrank_rationalRowSpace {n : ℕ} (g : G n) :
    Module.finrank ℚ (rationalRowSpace g) = n := by
  let e := LinearEquiv.ofInjective (rationalRowMap g.val) (rationalRowMap_injective g)
  change Module.finrank ℚ (LinearMap.range (rationalRowMap g.val)) = n
  rw [← e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

lemma row_mem_rationalRowSpace {n : ℕ} (g : G n) (i : Fin n) :
    g.val i ∈ rationalRowSpace g := by
  refine ⟨Pi.single i 1, ?_⟩
  change (∑ x : Fin n, ((Pi.single i (1 : ℚ) : Fin n → ℚ) x) • g.val x) = g.val i
  simp only [Pi.single_apply, ite_smul, one_smul, zero_smul]
  simpa only [Finset.mem_univ, ite_true] using Finset.sum_ite_eq' Finset.univ i g.val

/-- The rational row space is small over `ℚ`, but spans the whole real
coordinate space. This retains the actual invertible lattice matrix. -/
theorem real_span_rationalRowSpace {n : ℕ} (g : G n) :
    Submodule.span ℝ (rationalRowSpace g : Set (Fin n → ℝ)) = ⊤ := by
  have hrows : LinearIndependent ℝ g.val :=
    Matrix.linearIndependent_rows_of_det_ne_zero (by rw [g.property]; exact one_ne_zero)
  have hspan := hrows.span_eq_top_of_card_eq_finrank'
    (by simp : Fintype.card (Fin n) = Module.finrank ℝ (Fin n → ℝ))
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact row_mem_rationalRowSpace g i

/-- The generic-lattice condition also excludes coordinate zeroes in
the rational span; localization introduces no new linear relations. -/
theorem rationalRowSpace_no_coordinate_zero {n : ℕ} (g : G n)
    (hzero : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ j, v j ≠ 0) :
    ∀ v ∈ rationalRowSpace g, ∀ j, v j = 0 → v = 0 := by
  intro v hv j hvj
  obtain ⟨z, rfl⟩ := hv
  have hliZ : LinearIndependent ℤ (fun i : Fin n => g.val i j) := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha i
    have he : integerRowMap g.val a = 0 := by
      by_contra hne
      have hm : integerRowMap g.val a ∈ rowLattice g.val := by
        rw [← integerRowMap_range]
        exact ⟨a, rfl⟩
      exact hzero _ hm hne j (by simpa [integerRowMap, Finset.sum_apply] using ha)
    have ha0 : a = 0 := (integerRowMap_injective g) (he.trans (map_zero _).symm)
    exact congrFun ha0 i
  have hliQ : LinearIndependent ℚ (fun i : Fin n => g.val i j) :=
    hliZ.localization ℚ (nonZeroDivisors ℤ)
  have hsum : ∑ i, z i • g.val i j = 0 := by
    simpa [rationalRowMap, Finset.sum_apply] using hvj
  have hz : z = 0 := funext (Fintype.linearIndependent_iff.mp hliQ z hsum)
  rw [hz, map_zero]

/-- Real diagonal coordinate functions preserving the rational space. -/
def rationalDiagonalStabilizer {n : ℕ} (W : Submodule ℚ (Fin n → ℝ)) :
    Subalgebra ℚ (Fin n → ℝ) where
  carrier := {a | ∀ w ∈ W, a * w ∈ W}
  zero_mem' := by intro w _; simpa only [zero_mul] using W.zero_mem
  one_mem' := by intro w hw; simpa using hw
  add_mem' := by
    intro a b ha hb w hw
    simpa only [add_mul] using W.add_mem (ha w hw) (hb w hw)
  mul_mem' := by
    intro a b ha hb w hw
    simpa only [mul_assoc] using ha (b * w) (hb w hw)
  algebraMap_mem' := by
    intro a w hw
    simpa only [Algebra.smul_def] using W.smul_mem a hw

lemma mem_rationalDiagonalStabilizer {n : ℕ} (W : Submodule ℚ (Fin n → ℝ))
    (a : Fin n → ℝ) :
    a ∈ rationalDiagonalStabilizer W ↔ ∀ w ∈ W, a * w ∈ W := Iff.rfl

/-- The diagonal stabilizer is exactly the set of diagonals conjugate to
rational matrices by the actual lattice matrix. In particular, this
algebra is intrinsically attached to the rational lattice structure. -/
theorem mem_rationalDiagonalStabilizer_iff_rational_matrix {n : ℕ}
    (g : G n) (a : Fin n → ℝ) :
    a ∈ rationalDiagonalStabilizer (rationalRowSpace g) ↔
      ∃ B : Matrix (Fin n) (Fin n) ℚ,
        B.map (algebraMap ℚ ℝ) * g.val = g.val * Matrix.diagonal a := by
  constructor
  · intro ha
    have hrow (i : Fin n) : ∃ z : Fin n → ℚ,
        rationalRowMap g.val z = a * g.val i :=
      ha _ (row_mem_rationalRowSpace g i)
    choose B hB using hrow
    refine ⟨B, ?_⟩
    ext i j
    have he := congrFun (hB i) j
    rw [Matrix.mul_diagonal]
    change (∑ k, (B i k : ℝ) * g.val k j) = g.val i j * a j
    simpa [rationalRowMap, Finset.sum_apply, Rat.smul_def, mul_comm] using he
  · rintro ⟨B, hB⟩ w ⟨z, rfl⟩
    have hrow (i : Fin n) : a * g.val i ∈ rationalRowSpace g := by
      refine ⟨B i, ?_⟩
      ext j
      have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hB
      rw [Matrix.mul_diagonal] at he
      change (∑ k, (B i k : ℝ) * g.val k j) = g.val i j * a j at he
      simpa [rationalRowMap, Finset.sum_apply, Rat.smul_def, mul_comm] using he
    have hsum : (∑ i, z i • (a * g.val i)) ∈ rationalRowSpace g :=
      Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hrow i))
    convert hsum using 1
    ext j
    simp [rationalRowMap, Finset.sum_apply, Finset.mul_sum, Rat.smul_def, mul_left_comm]

/-- The rational matrix representing a stabilizing diagonal is unique. -/
theorem rationalDiagonalMatrix_unique {n : ℕ} (g : G n) (a : Fin n → ℝ)
    {B C : Matrix (Fin n) (Fin n) ℚ}
    (hB : B.map (algebraMap ℚ ℝ) * g.val = g.val * Matrix.diagonal a)
    (hC : C.map (algebraMap ℚ ℝ) * g.val = g.val * Matrix.diagonal a) : B = C := by
  have hu : IsUnit g.val := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [g.property]; simp)
  have he := hu.mul_right_cancel (hB.trans hC.symm)
  exact Matrix.map_injective (FaithfulSMul.algebraMap_injective ℚ ℝ) he

/-- The stabilizer acts on its defining rational coordinate space. -/
instance rationalDiagonalStabilizerModule {n : ℕ} (W : Submodule ℚ (Fin n → ℝ)) :
    Module (rationalDiagonalStabilizer W) W where
  smul a w := ⟨a.val * w.val, a.property w.val w.property⟩
  one_smul w := by apply Subtype.ext; change (1 : Fin n → ℝ) * w.val = w.val; exact one_mul _
  mul_smul a b w := by apply Subtype.ext; exact mul_assoc _ _ _
  smul_zero a := by apply Subtype.ext; change a.val * 0 = 0; exact mul_zero _
  smul_add a v w := by apply Subtype.ext; exact mul_add _ _ _
  add_smul a b w := by apply Subtype.ext; exact add_mul _ _ _
  zero_smul w := by apply Subtype.ext; change (0 : Fin n → ℝ) * w.val = 0; exact zero_mul _

@[simp] lemma rationalDiagonalStabilizer_smul_val {n : ℕ}
    (W : Submodule ℚ (Fin n → ℝ)) (a : rationalDiagonalStabilizer W) (w : W) :
    (a • w : W).val = a.val * w.val := rfl

instance rationalDiagonalStabilizerTower {n : ℕ} (W : Submodule ℚ (Fin n → ℝ)) :
    IsScalarTower ℚ (rationalDiagonalStabilizer W) W where
  smul_assoc a b w := by
    apply Subtype.ext
    ext i
    simp only [rationalDiagonalStabilizer_smul_val, Pi.mul_apply,
      Subalgebra.coe_smul, Submodule.coe_smul, Pi.smul_apply]
    simp only [Rat.smul_def, mul_assoc]

/-- Evaluation of the action at a fixed vector is rational linear. -/
def rationalDiagonalActionAt {n : ℕ} (W : Submodule ℚ (Fin n → ℝ)) (w : W) :
    rationalDiagonalStabilizer W →ₗ[ℚ] W where
  toFun a := a • w
  map_add' a b := add_smul a b w
  map_smul' a b := smul_assoc a b w

lemma rationalDiagonalActionAt_injective {n : ℕ}
    (W : Submodule ℚ (Fin n → ℝ))
    (hzero : ∀ v ∈ W, ∀ j, v j = 0 → v = 0)
    (w : W) (hw : w ≠ 0) : Function.Injective (rationalDiagonalActionAt W w) := by
  intro a b hab
  apply Subtype.ext
  ext j
  have hwj : w.val j ≠ 0 := by
    intro hj
    exact hw (Subtype.ext (hzero w.val w.property j hj))
  have hj := congrArg (fun v : W => v.val j) hab
  change a.val j * w.val j = b.val j * w.val j at hj
  exact mul_right_cancel₀ hwj hj

/-- Evaluation in any coordinate is faithful on the actual stabilizer. -/
def rationalDiagonalEval {n : ℕ} (W : Submodule ℚ (Fin n → ℝ)) (j : Fin n) :
    rationalDiagonalStabilizer W →ₐ[ℚ] ℝ where
  toFun a := a.val j
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

lemma rationalDiagonalEval_injective {n : ℕ}
    (W : Submodule ℚ (Fin n → ℝ))
    (hzero : ∀ v ∈ W, ∀ j, v j = 0 → v = 0)
    (w : W) (hw : w ≠ 0) (j : Fin n) :
    Function.Injective (rationalDiagonalEval W j) := by
  intro a b hab
  apply rationalDiagonalActionAt_injective W hzero w hw
  have hval : ((a - b) • w : W).val j = 0 := by
    change (a.val j - b.val j) * w.val j = 0
    change a.val j = b.val j at hab
    rw [hab, sub_self, zero_mul]
  have hz := hzero _ ((a - b) • w : W).property j hval
  have hz' : (a - b) • w = (0 : W) := Subtype.ext hz
  change a • w = b • w
  exact sub_eq_zero.mp (by simpa only [sub_smul] using hz')

/-- The field degree is forced by the concrete action on the rational
coordinate space. The field structure itself is derived from faithful
evaluation, rather than supplied as an input. -/
theorem rationalDiagonalStabilizer_degree_dvd {n : ℕ} (hn : 0 < n)
    (W : Submodule ℚ (Fin n → ℝ)) [FiniteDimensional ℚ W] [Nontrivial W]
    (hzero : ∀ v ∈ W, ∀ j, v j = 0 → v = 0) :
    Module.finrank ℚ (rationalDiagonalStabilizer W) ∣ Module.finrank ℚ W := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  let : FiniteDimensional ℚ (rationalDiagonalStabilizer W) :=
    FiniteDimensional.of_injective (rationalDiagonalActionAt W w)
      (rationalDiagonalActionAt_injective W hzero w hw)
  let : IsDomain (rationalDiagonalStabilizer W) :=
    Function.Injective.isDomain (rationalDiagonalEval W ⟨0, hn⟩)
      (rationalDiagonalEval_injective W hzero w hw _)
  let : Field (rationalDiagonalStabilizer W) :=
    fieldOfFiniteDimensional ℚ (rationalDiagonalStabilizer W)
  exact Module.finrank_dvd_finrank_right ℚ (rationalDiagonalStabilizer W) W

/-- In prime dimension the rational diagonal stabilizer has degree one
or full degree. This is applied to the actual row space of a lattice. -/
theorem rationalDiagonalStabilizer_prime_dichotomy {n : ℕ} (hn : n.Prime)
    (W : Submodule ℚ (Fin n → ℝ)) [FiniteDimensional ℚ W]
    (hdim : Module.finrank ℚ W = n)
    (hzero : ∀ v ∈ W, ∀ j, v j = 0 → v = 0) :
    Module.finrank ℚ (rationalDiagonalStabilizer W) = 1 ∨
      Module.finrank ℚ (rationalDiagonalStabilizer W) = n := by
  let : Nontrivial W := Module.nontrivial_of_finrank_pos (by rw [hdim]; exact hn.pos)
  apply (Nat.dvd_prime hn).mp
  simpa only [hdim] using rationalDiagonalStabilizer_degree_dvd hn.pos W hzero

/-- Specialization to the rational span of the given lattice matrix. -/
theorem rationalRowSpace_prime_dichotomy {n : ℕ} (hn : n.Prime) (g : G n)
    (hzero : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ j, v j ≠ 0) :
    Module.finrank ℚ (rationalDiagonalStabilizer (rationalRowSpace g)) = 1 ∨
      Module.finrank ℚ (rationalDiagonalStabilizer (rationalRowSpace g)) = n :=
  rationalDiagonalStabilizer_prime_dichotomy hn (rationalRowSpace g)
    (finrank_rationalRowSpace g) (rationalRowSpace_no_coordinate_zero g hzero)

/-- If the stabilizer has full degree, its coordinate embeddings are
pairwise distinct. The real spanning condition rules out proportional
coordinate functionals on the rational space. -/
theorem rationalDiagonalStabilizer_separates {n : ℕ}
    (W : Submodule ℚ (Fin n → ℝ)) [FiniteDimensional ℚ W] [Nontrivial W]
    (hzero : ∀ v ∈ W, ∀ j, v j = 0 → v = 0)
    (hspan : Submodule.span ℝ (W : Set (Fin n → ℝ)) = ⊤)
    (hdim : Module.finrank ℚ (rationalDiagonalStabilizer W) = Module.finrank ℚ W)
    {i j : Fin n} (hij : i ≠ j) :
    ∃ a : rationalDiagonalStabilizer W, a.val i ≠ a.val j := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have hinj := rationalDiagonalActionAt_injective W hzero w hw
  let : FiniteDimensional ℚ (rationalDiagonalStabilizer W) :=
    FiniteDimensional.of_injective (rationalDiagonalActionAt W w) hinj
  have hsurj : Function.Surjective (rationalDiagonalActionAt W w) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  by_contra hnone
  push Not at hnone
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    w.val j • (LinearMap.proj i) - w.val i • (LinearMap.proj j)
  have hW : (W : Set (Fin n → ℝ)) ⊆ f.ker := by
    intro v hv
    obtain ⟨a, ha⟩ := hsurj ⟨v, hv⟩
    change f v = 0
    have hev : v = a.val * w.val := congrArg Subtype.val ha.symm
    rw [hev]
    change w.val j * (a.val i * w.val i) - w.val i * (a.val j * w.val j) = 0
    rw [hnone a]
    ring
  have hker : (⊤ : Submodule ℝ (Fin n → ℝ)) ≤ f.ker := by
    rw [← hspan]
    exact Submodule.span_le.mpr hW
  have he := hker (show Pi.single i (1 : ℝ) ∈ (⊤ : Submodule ℝ (Fin n → ℝ)) from trivial)
  change f (Pi.single i 1) = 0 at he
  have hwj : w.val j ≠ 0 := fun hj => hw (Subtype.ext (hzero _ w.property j hj))
  apply hwj
  simpa [f, Pi.single_apply, hij, hij.symm] using he

/-- In prime dimension, a repeated coordinate embedding leaves only
the rational scalars in the actual diagonal stabilizer. -/
theorem rationalRowSpace_stabilizer_eq_bot_of_repeated_coordinate {n : ℕ}
    (hn : n.Prime) (g : G n)
    (hzero : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ j, v j ≠ 0)
    {i j : Fin n} (hij : i ≠ j)
    (heq : ∀ a : rationalDiagonalStabilizer (rationalRowSpace g), a.val i = a.val j) :
    rationalDiagonalStabilizer (rationalRowSpace g) = ⊥ := by
  let : Nonempty (Fin n) := ⟨⟨0, hn.pos⟩⟩
  have hz := rationalRowSpace_no_coordinate_zero g hzero
  let W := rationalRowSpace g
  let : Nontrivial W := Module.nontrivial_of_finrank_pos
    (by change 0 < Module.finrank ℚ (rationalRowSpace g); rw [finrank_rationalRowSpace]; exact hn.pos)
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  let : FiniteDimensional ℚ (rationalDiagonalStabilizer W) :=
    FiniteDimensional.of_injective (rationalDiagonalActionAt W w)
      (rationalDiagonalActionAt_injective W hz w hw)
  apply Subalgebra.finrank_eq_one_iff.mp
  rcases rationalRowSpace_prime_dichotomy hn g hzero with h | h
  · exact h
  · have hfull : Module.finrank ℚ (rationalDiagonalStabilizer W) = Module.finrank ℚ W :=
      h.trans (finrank_rationalRowSpace g).symm
    obtain ⟨a, ha⟩ := rationalDiagonalStabilizer_separates W hz
      (real_span_rationalRowSpace g) hfull hij
    exact False.elim (ha (heq a))

/-- Coordinate functions constant on each root block, viewed over `ℚ`. -/
def blockCoordinateAlgebra {n : ℕ} (r : Setoid (Fin n)) :
    Subalgebra ℚ (Fin n → ℝ) where
  carrier := {a | ∀ i j, r i j → a i = a j}
  zero_mem' := fun _ _ _ => rfl
  one_mem' := fun _ _ _ => rfl
  add_mem' := by
    intro a b ha hb i j hij
    change a i + b i = a j + b j
    rw [ha i j hij, hb i j hij]
  mul_mem' := by
    intro a b ha hb i j hij
    change a i * b i = a j * b j
    rw [ha i j hij, hb i j hij]
  algebraMap_mem' := fun _ _ _ _ => rfl

/-- The actual rational lattice stabilizer intersected with the block
centralizer. Both conditions refer to the given lattice and partition. -/
def rationalBlockStabilizer {n : ℕ} (g : G n) (r : Setoid (Fin n)) :
    Subalgebra ℚ (Fin n → ℝ) :=
  rationalDiagonalStabilizer (rationalRowSpace g) ⊓ blockCoordinateAlgebra r

/-- In prime dimension, a nontrivial root block leaves only rational
scalars in the rational block centralizer. No rationality of the real
block algebra is assumed or asserted here. -/
theorem rationalBlockStabilizer_eq_bot {n : ℕ} (hn : n.Prime) (g : G n)
    (hzero : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ j, v j ≠ 0)
    (r : Setoid (Fin n)) (hblock : ∃ i j, i ≠ j ∧ r i j) :
    rationalBlockStabilizer g r = ⊥ := by
  let : Nonempty (Fin n) := ⟨⟨0, hn.pos⟩⟩
  let W := rationalRowSpace g
  let A := rationalBlockStabilizer g r
  let : Nontrivial W := Module.nontrivial_of_finrank_pos
    (by change 0 < Module.finrank ℚ (rationalRowSpace g); rw [finrank_rationalRowSpace]; exact hn.pos)
  have hz := rationalRowSpace_no_coordinate_zero g hzero
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  let e : A →ₐ[ℚ] rationalDiagonalStabilizer W := Subalgebra.inclusion inf_le_left
  have heinj : Function.Injective e := Subalgebra.inclusion_injective _
  let f : A →ₗ[ℚ] W := (rationalDiagonalActionAt W w).comp e.toLinearMap
  have hfinj : Function.Injective f :=
    (rationalDiagonalActionAt_injective W hz w hw).comp heinj
  let : FiniteDimensional ℚ A := FiniteDimensional.of_injective f hfinj
  let : Module A W := Module.compHom W e.toRingHom
  let : IsScalarTower ℚ A W := by
    refine ⟨?_⟩
    intro q a v
    change e (q • a) • v = q • (e a • v)
    rw [map_smul, smul_assoc]
  let : IsDomain A := Function.Injective.isDomain
    ((rationalDiagonalEval W ⟨0, hn.pos⟩).comp e)
    ((rationalDiagonalEval_injective W hz w hw _).comp heinj)
  let : Field A := fieldOfFiniteDimensional ℚ A
  have hdiv : Module.finrank ℚ A ∣ n := by
    have h := Module.finrank_dvd_finrank_right ℚ A W
    simpa only [W, finrank_rationalRowSpace] using h
  apply Subalgebra.finrank_eq_one_iff.mp
  rcases (Nat.dvd_prime hn).mp hdiv with h | h
  · exact h
  · have hdim : Module.finrank ℚ A = Module.finrank ℚ W :=
      h.trans (finrank_rationalRowSpace g).symm
    have hsurj : Function.Surjective f :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hfinj
    obtain ⟨i, j, hij, hrij⟩ := hblock
    let L : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
      w.val j • (LinearMap.proj i) - w.val i • (LinearMap.proj j)
    have hW : (W : Set (Fin n → ℝ)) ⊆ L.ker := by
      intro v hv
      obtain ⟨a, ha⟩ := hsurj ⟨v, hv⟩
      change L v = 0
      have hev : v = a.val * w.val := congrArg Subtype.val ha.symm
      have heq : a.val i = a.val j := a.property.2 i j hrij
      rw [hev]
      change w.val j * (a.val i * w.val i) - w.val i * (a.val j * w.val j) = 0
      rw [heq]
      ring
    have hker : (⊤ : Submodule ℝ (Fin n → ℝ)) ≤ L.ker := by
      rw [← real_span_rationalRowSpace g]
      exact Submodule.span_le.mpr hW
    have htest := hker
      (show Pi.single i (1 : ℝ) ∈ (⊤ : Submodule ℝ (Fin n → ℝ)) from trivial)
    change L (Pi.single i 1) = 0 at htest
    have hwj : w.val j ≠ 0 := fun hj => hw (Subtype.ext (hz _ w.property j hj))
    exact False.elim (hwj (by simpa [L, Pi.single_apply, hij, Ne.symm hij] using htest))

end DukePrimeDegree

end

end OAI
