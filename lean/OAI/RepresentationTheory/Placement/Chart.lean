import Mathlib
import OAI.RepresentationTheory.Unitary.Basic

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.PlacementInduction
variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]

/- A transitive action with actual chosen representatives. For the application,
Ω is the set of ordered placements; the fiber group fixes the base placement. -/
structure Chart (a : G →* Equiv.Perm Ω) where
  base : Ω
  rep : Ω → G
  reaches : ∀ x, a (rep x) base=x

namespace Chart
variable {a : G →* Equiv.Perm Ω} (C : Chart a)

def stabilizer : Subgroup G where
  carrier := {g | a g C.base=C.base}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    change a (g*h) C.base=C.base
    change a g C.base=C.base at hg
    change a h C.base=C.base at hh
    rw [map_mul,Equiv.Perm.mul_apply,hh,hg]
  inv_mem' {g} hg := by
    change a g⁻¹ C.base=C.base
    change a g C.base=C.base at hg
    apply (a g).injective
    have hi : a g⁻¹=(a g)⁻¹ := map_inv a g
    rw [hi,Equiv.Perm.coe_inv,Equiv.apply_symm_apply,hg]

def cocycle (g : G) (x : Ω) : C.stabilizer :=
  ⟨(C.rep (a g x))⁻¹*g*C.rep x,by
    change a ((C.rep (a g x))⁻¹*g*C.rep x) C.base=C.base
    simp only [map_mul,Equiv.Perm.mul_apply,C.reaches,map_inv,Equiv.Perm.coe_inv]
    exact (Equiv.symm_apply_eq _).mpr (C.reaches (a g x)).symm⟩

omit [Fintype G] [Fintype Ω] [DecidableEq Ω] in
@[simp] lemma cocycle_mul (g h : G) (x : Ω) :
    C.cocycle (g*h) x=C.cocycle g (a h x)*C.cocycle h x := by
  apply Subtype.ext
  change (C.rep (a (g*h) x))⁻¹*(g*h)*C.rep x=
    ((C.rep (a g (a h x)))⁻¹*g*C.rep (a h x))*((C.rep (a h x))⁻¹*h*C.rep x)
  rw [map_mul,Equiv.Perm.mul_apply]
  group

omit [Fintype G] [Fintype Ω] [DecidableEq Ω] in
@[simp] lemma cocycle_one (x : Ω) : C.cocycle 1 x=1 := by
  apply Subtype.ext
  change (C.rep (a 1 x))⁻¹*1*C.rep x=1
  rw [map_one,Equiv.Perm.one_apply,mul_one,inv_mul_cancel]

omit [Fintype G] [Fintype Ω] [DecidableEq Ω] in
lemma cocycle_inv (g : G) (x : Ω) :
    C.cocycle g⁻¹ (a g x)=(C.cocycle g x)⁻¹ := by
  have hh := C.cocycle_mul g⁻¹ g x
  rw [inv_mul_cancel,C.cocycle_one] at hh
  exact eq_inv_of_mul_eq_one_left hh.symm

variable (ρ : UnitaryIrrep C.stabilizer)

/- Literal placement-by-fiber block matrix of the induced unitary action. -/
def matrix (g : G) : Matrix (Ω × Fin ρ.dimension) (Ω × Fin ρ.dimension) ℂ :=
  fun y x => if y.1=a g x.1 then ρ.matrix (C.cocycle g x.1) y.2 x.2 else 0

omit [Fintype G] in
lemma matrix_mul (g h : G) : C.matrix ρ (g*h)=C.matrix ρ g*C.matrix ρ h := by
  ext y x
  rcases y with ⟨y,i⟩
  rcases x with ⟨x,j⟩
  rw [Matrix.mul_apply,Fintype.sum_prod_type]
  have hs : (∑ z : Ω, ∑ k : Fin ρ.dimension,
      C.matrix ρ g (y,i) (z,k)*C.matrix ρ h (z,k) (x,j))=
    ∑ k : Fin ρ.dimension, C.matrix ρ g (y,i) (a h x,k)*C.matrix ρ h (a h x,k) (x,j) := by
    apply Finset.sum_eq_single (a h x)
    · intro z _ hz
      simp only [matrix,ite_eq_right hz,mul_zero,Finset.sum_const_zero]
    · simp
  rw [hs]
  by_cases he : y=a (g*h) x
  · have he' : y=a g (a h x) := by simpa only [map_mul,Equiv.Perm.mul_apply] using he
    simp only [matrix,ite_eq_left he,ite_eq_left he',ite_true]
    rw [C.cocycle_mul,map_mul,Matrix.mul_apply]
  · have he' : ¬ y=a g (a h x) := by simpa only [map_mul,Equiv.Perm.mul_apply] using he
    simp only [matrix,ite_eq_right he,ite_eq_right he',zero_mul,Finset.sum_const_zero]

omit [Fintype G] [Fintype Ω] in
lemma matrix_one : C.matrix ρ 1=1 := by
  ext y x
  rcases y with ⟨y,i⟩
  rcases x with ⟨x,j⟩
  simp only [matrix,map_one,Equiv.Perm.one_apply,C.cocycle_one,Matrix.one_apply,Prod.mk.injEq]
  by_cases hy : y=x <;> by_cases hi : i=j <;> simp [hy,hi]

def action : G →* Matrix (Ω × Fin ρ.dimension) (Ω × Fin ρ.dimension) ℂ where
  toFun := C.matrix ρ
  map_one' := C.matrix_one ρ
  map_mul' := C.matrix_mul ρ

omit [Fintype G] [Fintype Ω] in
lemma matrix_inv (g : G) : C.matrix ρ g⁻¹=(C.matrix ρ g).conjTranspose := by
  ext y x
  rcases y with ⟨y,i⟩
  rcases x with ⟨x,j⟩
  by_cases he : x=a g y
  · have he' : y=a g⁻¹ x := by
      rw [he,map_inv,Equiv.Perm.coe_inv,Equiv.symm_apply_apply]
    simp only [Matrix.conjTranspose_apply,matrix,ite_eq_left he,ite_eq_left he']
    rw [he,C.cocycle_inv,ρ.matrix_inv]
    rfl
  · have he' : ¬ y=a g⁻¹ x := by
      intro hh
      apply he
      rw [hh,map_inv,Equiv.Perm.coe_inv,Equiv.apply_symm_apply]
    simp only [matrix,ite_eq_right he,ite_eq_right he',Matrix.conjTranspose_apply,star_zero]

omit [Fintype G] in
lemma matrix_unitary (g : G) : (C.matrix ρ g).conjTranspose*C.matrix ρ g=1 := by
  rw [← C.matrix_inv,← C.matrix_mul,inv_mul_cancel,C.matrix_one]

omit [Fintype G] in
lemma trace_matrix (g : G) : Matrix.trace (C.matrix ρ g)=
    ∑ x : Ω, if a g x=x then Matrix.trace (ρ.matrix (C.cocycle g x)) else 0 := by
  rw [Matrix.trace,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : a g x=x
  · simp only [Matrix.diag,matrix,ite_eq_left hx.symm,ite_eq_left hx,Matrix.trace]
  · simp only [Matrix.diag,matrix,ite_eq_right (Ne.symm hx),Finset.sum_const_zero,ite_eq_right hx]

end Chart
end CoordinateSweeps.PlacementInduction

namespace CoordinateSweeps.PlacementInduction.Chart
variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]
    {a : G →* Equiv.Perm Ω} (C : Chart a)

omit [Fintype G] [Fintype Ω] [DecidableEq Ω] in
lemma invrep_reaches (x : Ω) : a (C.rep x)⁻¹ x=C.base := by
  rw [map_inv,Equiv.Perm.coe_inv]
  exact (Equiv.symm_apply_eq _).mpr (C.reaches x).symm

/- Actual orbit--stabilizer decomposition, including its fiber cardinal factor. -/
def decompose : G ≃ Ω × C.stabilizer where
  toFun g := (a g C.base,⟨(C.rep (a g C.base))⁻¹*g,by
    change a ((C.rep (a g C.base))⁻¹*g) C.base=C.base
    rw [map_mul,Equiv.Perm.mul_apply,C.invrep_reaches]⟩)
  invFun x := C.rep x.1*x.2.val
  left_inv g := by
    change C.rep (a g C.base)*((C.rep (a g C.base))⁻¹*g)=g
    group
  right_inv x := by
    rcases x with ⟨x,h⟩
    have hx : a (C.rep x*h.val) C.base=x := by
      rw [map_mul,Equiv.Perm.mul_apply,h.property,C.reaches]
    apply Prod.ext
    · exact hx
    · apply Subtype.ext
      change (C.rep (a (C.rep x*h.val) C.base))⁻¹*(C.rep x*h.val)=h.val
      rw [hx]
      group

omit [DecidableEq Ω] in
lemma card_group : Fintype.card G=Fintype.card Ω*Fintype.card C.stabilizer := by
  simpa only [Fintype.card_prod] using Fintype.card_congr C.decompose

def fixedEquiv (x : Ω) : C.stabilizer ≃ {g : G // a g x=x} where
  toFun h := ⟨C.rep x*h.val*(C.rep x)⁻¹,by
    rw [map_mul,map_mul,Equiv.Perm.mul_apply,Equiv.Perm.mul_apply,C.invrep_reaches,
      h.property,C.reaches]⟩
  invFun g := ⟨(C.rep x)⁻¹*g.val*C.rep x,by
    change a ((C.rep x)⁻¹*g.val*C.rep x) C.base=C.base
    rw [map_mul,map_mul,Equiv.Perm.mul_apply,Equiv.Perm.mul_apply,C.reaches,g.property,C.invrep_reaches]⟩
  left_inv h := by
    apply Subtype.ext
    change (C.rep x)⁻¹*(C.rep x*h.val*(C.rep x)⁻¹)*C.rep x=h.val
    group
  right_inv g := by
    apply Subtype.ext
    change C.rep x*((C.rep x)⁻¹*g.val*C.rep x)*(C.rep x)⁻¹=g.val
    group

omit [Fintype G] [Fintype Ω] [DecidableEq Ω] in
lemma cocycle_fixed (x : Ω) (h : C.stabilizer) :
    C.cocycle ((C.fixedEquiv x h).val) x=h := by
  apply Subtype.ext
  change (C.rep (a (C.fixedEquiv x h).val x))⁻¹*(C.rep x*h.val*(C.rep x)⁻¹)*C.rep x=h.val
  rw [(C.fixedEquiv x h).property]
  group

end CoordinateSweeps.PlacementInduction.Chart

namespace CoordinateSweeps.PlacementInduction.Chart
open UnitaryIrrep
variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]
    {a : G →* Equiv.Perm Ω} (C : Chart a)

omit [Fintype Ω] in
lemma fixed_character_sum (ρ : UnitaryIrrep C.stabilizer) (τ : UnitaryIrrep G) (x : Ω) :
    (∑ g : G, if a g x=x then Matrix.trace (ρ.matrix (C.cocycle g x))*Matrix.trace (τ.matrix g⁻¹) else 0)=
      ∑ h : C.stabilizer, Matrix.trace (ρ.matrix h)*Matrix.trace (τ.matrix (h.val)⁻¹) := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun g : G => a g x=x) _ (by intro g; simp) (fun g =>
    Matrix.trace (ρ.matrix (C.cocycle g x))*Matrix.trace (τ.matrix g⁻¹))]
  rw [← (C.fixedEquiv x).sum_comp]
  apply Finset.sum_congr rfl
  intro h _
  rw [C.cocycle_fixed]
  congr 1
  change Matrix.trace (τ.matrix (C.rep x*h.val*(C.rep x)⁻¹)⁻¹)=_
  rw [show (C.rep x*h.val*(C.rep x)⁻¹)⁻¹=C.rep x*h.val⁻¹*(C.rep x)⁻¹ by group]
  exact trace_conj τ.matrix _ _

lemma induced_character_sum (ρ : UnitaryIrrep C.stabilizer) (τ : UnitaryIrrep G) :
    (∑ g : G, Matrix.trace (C.action ρ g)*Matrix.trace (τ.matrix g⁻¹))=
      (Fintype.card Ω : ℂ)*
        ∑ h : C.stabilizer, Matrix.trace (ρ.matrix h)*Matrix.trace (τ.matrix (h.val)⁻¹) := by
  change (∑ g : G, Matrix.trace (C.matrix ρ g)*Matrix.trace (τ.matrix g⁻¹))=_
  simp_rw [C.trace_matrix,Finset.sum_mul]
  rw [Finset.sum_comm]
  have hm (g : G) (x : Ω) :
      (if a g x=x then Matrix.trace (ρ.matrix (C.cocycle g x)) else 0)*Matrix.trace (τ.matrix g⁻¹)=
        if a g x=x then Matrix.trace (ρ.matrix (C.cocycle g x))*Matrix.trace (τ.matrix g⁻¹) else 0 := by
    split_ifs <;> simp
  simp only [hm,C.fixed_character_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

/- Finite Frobenius reciprocity for the literal placement matrices. The RHS
is the actual Hom space in restriction, not an assumed branching coefficient. -/
theorem multiplicity_eq (ρ : UnitaryIrrep C.stabilizer) (τ : UnitaryIrrep G) :
    Module.finrank ℂ (τ.asRepresentation.IntertwiningMap (matrixRepresentation (C.action ρ)))=
      Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap
        (matrixRepresentation (τ.matrix.comp C.stabilizer.subtype))) := by
  have hl := τ.character_sum_multiplicity (C.action ρ)
  have hr := ρ.character_sum_multiplicity (τ.matrix.comp C.stabilizer.subtype)
  have he := C.induced_character_sum ρ τ
  have hs : (∑ h : C.stabilizer, Matrix.trace (ρ.matrix h)*Matrix.trace (τ.matrix (h.val)⁻¹))=
      (Fintype.card C.stabilizer : ℂ)*Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap
        (matrixRepresentation (τ.matrix.comp C.stabilizer.subtype))) := by
    rw [← hr]
    have hh := Equiv.sum_comp (Equiv.inv C.stabilizer) (fun h : C.stabilizer =>
      Matrix.trace (τ.matrix h.val)*Matrix.trace (ρ.matrix h⁻¹))
    simpa only [Equiv.inv_apply,MonoidHom.comp_apply,Subgroup.subtype_apply,Subgroup.coe_inv,inv_inv,mul_comm]
      using hh
  rw [hs,hl,C.card_group,Nat.cast_mul] at he
  have hcard : (Fintype.card Ω : ℂ)*(Fintype.card C.stabilizer : ℂ) ≠ 0 := by
    rw [← Nat.cast_mul,← C.card_group]
    exact_mod_cast Fintype.card_ne_zero
  have he' := mul_left_cancel₀ hcard (he.trans (mul_assoc _ _ _).symm)
  exact_mod_cast he'

/- The induced moment really dominates each target moment by its branching multiplicity. -/
theorem induced_moment_bound (ρ : UnitaryIrrep C.stabilizer) (τ : UnitaryIrrep G)
    {W : Type*} [Fintype W] (w : W → ℂ) (g : W → G) (q : ℕ) :
    (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap
      (matrixRepresentation (τ.matrix.comp C.stabilizer.subtype))) : ℝ)*
        (Matrix.trace (((averageMatrix τ.matrix w g).conjTranspose*averageMatrix τ.matrix w g)^q)).re ≤
          (Matrix.trace (((averageMatrix (C.action ρ) w g).conjTranspose*averageMatrix (C.action ρ) w g)^q)).re := by
  rw [← C.multiplicity_eq ρ τ]
  exact τ.multiplicity_moment_le (C.action ρ) (fun g => (C.matrix_inv ρ g).symm) w g q

end CoordinateSweeps.PlacementInduction.Chart

namespace CoordinateSweeps.OrderedPlacements
variable {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]

def action : Equiv.Perm X →* Equiv.Perm (I ↪ X) where
  toFun g :=
    { toFun := fun x => x.trans g.toEmbedding
      invFun := fun x => x.trans g.symm.toEmbedding
      left_inv := fun x => by ext i; simp
      right_inv := fun x => by ext i; simp }
  map_one' := by ext x i; rfl
  map_mul' g h := by ext x i; rfl

omit [Fintype I] [Fintype X] [DecidableEq X] in
@[simp] lemma action_apply (g : Equiv.Perm X) (x : I ↪ X) (i : I) : action g x i=g (x i) := rfl

def rangeEquiv (x0 x : I ↪ X) : Set.range x0 ≃ Set.range x :=
  (Equiv.ofInjective x0 x0.injective).symm.trans (Equiv.ofInjective x x.injective)

omit [Fintype I] [Fintype X] [DecidableEq X] in
lemma rangeEquiv_apply (x0 x : I ↪ X) (i : I) :
    (rangeEquiv x0 x ⟨x0 i,⟨i,rfl⟩⟩).val=x i := by
  have he : (Equiv.ofInjective x0 x0.injective).symm ⟨x0 i,⟨i,rfl⟩⟩=i :=
    (Equiv.ofInjective x0 x0.injective).symm_apply_apply i
  change x ((Equiv.ofInjective x0 x0.injective).symm ⟨x0 i,⟨i,rfl⟩⟩)=x i
  rw [he]

/- Every ordered placement is reached by an actual permutation extending the
bijection on its marked positions. No cardinal or transitivity axiom is used. -/
def chart (x0 : I ↪ X) : PlacementInduction.Chart (action (I := I) (X := X)) where
  base := x0
  rep x := Equiv.extendSubtype (rangeEquiv x0 x)
  reaches x := by
    ext i
    change Equiv.extendSubtype (rangeEquiv x0 x) (x0 i)=x i
    rw [Equiv.extendSubtype_apply_of_mem _ _ (show x0 i ∈ Set.range x0 from ⟨i,rfl⟩)]
    exact rangeEquiv_apply x0 x i

lemma mem_stabilizer_iff (x0 : I ↪ X) (g : Equiv.Perm X) :
    g ∈ (chart x0).stabilizer ↔ ∀ i, g (x0 i)=x0 i := by
  change action g x0=x0 ↔ _
  constructor
  · intro h i
    exact congrArg (fun x : I ↪ X => x i) h
  · intro h
    ext i
    exact h i

omit [DecidableEq X] in
lemma card_placements : Fintype.card (I ↪ X)=(Fintype.card X).descFactorial (Fintype.card I) :=
  Fintype.card_embedding_eq

end CoordinateSweeps.OrderedPlacements

namespace CoordinateSweeps.PlacementInduction.Chart
open UnitaryIrrep
variable {G Ω W : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω] [Fintype W]
    {a : G →* Equiv.Perm Ω} (C : Chart a)

def transition (_ : Chart a) (w : W → ℝ) (g : W → G) (y x : Ω) : ℝ :=
  ∑ ω, if y=a (g ω) x then w ω else 0

def conditionalBlock (ρ : UnitaryIrrep C.stabilizer) (w : W → ℝ) (g : W → G) (y x : Ω) :
    Matrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ :=
  (C.transition w g y x : ℂ)⁻¹ •
    ∑ ω, if y=a (g ω) x then (w ω : ℂ) • ρ.matrix (C.cocycle (g ω) x) else 0

omit [Fintype G] [Fintype Ω] in
lemma transition_nonneg (w : W → ℝ) (hw : ∀ ω, 0 ≤ w ω) (g : W → G) (y x : Ω) :
    0 ≤ C.transition w g y x := by
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact hw ω
  · exact le_refl 0

omit [Fintype G] in
lemma transition_columns (w : W → ℝ) (hs : ∑ ω, w ω=1) (g : W → G) (x : Ω) :
    ∑ y, C.transition w g y x=1 := by
  unfold transition
  rw [Finset.sum_comm]
  simpa only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hs

omit [Fintype G] in
lemma transition_rows (w : W → ℝ) (hs : ∑ ω, w ω=1) (g : W → G) (y : Ω) :
    ∑ x, C.transition w g y x=1 := by
  unfold transition
  rw [Finset.sum_comm]
  have he (ω : W) : (∑ x : Ω, if y=a (g ω) x then w ω else 0)=w ω := by
    have hh := Equiv.sum_comp (a (g ω)) (fun x => if y=x then w ω else 0)
    simpa only [Finset.sum_ite_eq,Finset.mem_univ,ite_true] using hh
  simpa only [he] using hs

omit [Fintype G] [Fintype Ω] in
lemma weight_le_transition (w : W → ℝ) (hw : ∀ ω, 0 ≤ w ω) (g : W → G)
    (x y : Ω) (ω : W) (hω : y=a (g ω) x) : w ω ≤ C.transition w g y x := by
  have hh := Finset.single_le_sum (s := (Finset.univ : Finset W))
    (f := fun ν => if y=a (g ν) x then w ν else 0)
    (fun ν _ => by split_ifs; exact hw ν; exact le_refl 0) (Finset.mem_univ ω)
  simpa only [transition,ite_eq_left hω] using hh

omit [Fintype G] [Fintype Ω] in
lemma zero_transition_sum (ρ : UnitaryIrrep C.stabilizer) (w : W → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (g : W → G) (y x : Ω) (hz : C.transition w g y x=0) :
    (∑ ω, if y=a (g ω) x then (w ω : ℂ) • ρ.matrix (C.cocycle (g ω) x) else 0)=0 := by
  apply Finset.sum_eq_zero
  intro ω _
  by_cases hω : y=a (g ω) x
  · have hh := C.weight_le_transition w hw g x y ω hω
    rw [hz] at hh
    have hwz : w ω=0 := le_antisymm hh (hw ω)
    simp [hω,hwz]
  · exact ite_eq_right hω

/- Every induced average block is exactly probability times its actual normalized
conditional fiber operator, including impossible transitions. -/
omit [Fintype G] in
theorem average_block (ρ : UnitaryIrrep C.stabilizer) (w : W → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (g : W → G) (y x : Ω) :
    (averageMatrix (C.action ρ) (fun ω => (w ω : ℂ)) g).submatrix (fun i => (y,i)) (fun j => (x,j))=
      (C.transition w g y x : ℂ) • C.conditionalBlock ρ w g y x := by
  have he : (averageMatrix (C.action ρ) (fun ω => (w ω : ℂ)) g).submatrix
      (fun i => (y,i)) (fun j => (x,j))=
      ∑ ω, if y=a (g ω) x then (w ω : ℂ) • ρ.matrix (C.cocycle (g ω) x) else 0 := by
    ext i j
    simp only [averageMatrix,Matrix.submatrix_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro ω _
    change (w ω : ℂ)*(if y=a (g ω) x then ρ.matrix (C.cocycle (g ω) x) i j else 0)=
      (if y=a (g ω) x then (w ω : ℂ) • ρ.matrix (C.cocycle (g ω) x) else 0) i j
    split_ifs <;> simp
  rw [he,conditionalBlock,smul_smul]
  by_cases hz : C.transition w g y x=0
  · rw [C.zero_transition_sum ρ w hw g y x hz,smul_zero]
  · rw [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hz),one_smul]

end CoordinateSweeps.PlacementInduction.Chart

namespace CoordinateSweeps.PlacementInduction.Chart
variable {G Ω W : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω] [Fintype W]
    {a : G →* Equiv.Perm Ω} (C : Chart a)

def pointFix (_ : Chart a) (x : Ω) : Subgroup G where
  carrier g := a g x=x
  one_mem' := by change a 1 x=x; simp
  mul_mem' {g h} hg hh := by change a (g*h) x=x; rw [map_mul,Equiv.Perm.mul_apply,hh,hg]
  inv_mem' {g} hg := by
    change a g⁻¹ x=x
    rw [map_inv,Equiv.Perm.coe_inv]
    exact (Equiv.symm_apply_eq _).mpr hg.symm

def pointEquiv (x : Ω) : C.stabilizer ≃* C.pointFix x where
  toEquiv := C.fixedEquiv x
  map_mul' h k := by
    apply Subtype.ext
    change C.rep x*(h.val*k.val)*(C.rep x)⁻¹=
      (C.rep x*h.val*(C.rep x)⁻¹)*(C.rep x*k.val*(C.rep x)⁻¹)
    group

/- The remaining symmetric-group type transported to the actual input placement. -/
def pointIrrep (ρ : UnitaryIrrep C.stabilizer) (x : Ω) : UnitaryIrrep (C.pointFix x) where
  dimension := ρ.dimension
  positive := ρ.positive
  matrix := ρ.matrix.comp (C.pointEquiv x).symm.toMonoidHom
  unitary g := ρ.unitary _
  irreducible S hS := ρ.irreducible S (by
    intro g v hv
    have hh := hS (C.pointEquiv x g) v hv
    change (ρ.matrix ((C.pointEquiv x).symm (C.pointEquiv x g))).mulVec v ∈ S at hh
    simpa only [MulEquiv.symm_apply_apply] using hh)

def transitionResidual (x y : Ω) (g₀ g : G) (h₀ : y=a g₀ x) (hg : y=a g x) : C.pointFix x :=
  ⟨g₀⁻¹*g,by
    change a (g₀⁻¹*g) x=x
    rw [map_mul,Equiv.Perm.mul_apply,← hg,h₀,map_inv,Equiv.Perm.coe_inv,Equiv.symm_apply_apply]⟩

omit [Fintype G] [Fintype Ω] [DecidableEq Ω] in
lemma cocycle_residual (x y : Ω) (g₀ g : G) (h₀ : y=a g₀ x) (hg : y=a g x) :
    C.cocycle g x=C.cocycle g₀ x*(C.pointEquiv x).symm (C.transitionResidual x y g₀ g h₀ hg) := by
  apply Subtype.ext
  change (C.rep (a g x))⁻¹*g*C.rep x=
    ((C.rep (a g₀ x))⁻¹*g₀*C.rep x)*((C.rep x)⁻¹*(g₀⁻¹*g)*C.rep x)
  rw [← hg,← h₀]
  group

/- Normalized residual law on the true point stabilizer. The reference is any
compatible transition; it is a unitary frame, not a new hypothesis on the law. -/
def transitionAverage (ρ : UnitaryIrrep C.stabilizer) (w : W → ℝ) (g : W → G)
    (x y : Ω) (ω₀ : W) (h₀ : y=a (g ω₀) x) : Matrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ :=
  (C.transition w g y x : ℂ)⁻¹ • ∑ ω : {ω : W // y=a (g ω) x},
    (w ω.val : ℂ) • ρ.matrix
      ((C.pointEquiv x).symm (C.transitionResidual x y (g ω₀) (g ω.val) h₀ ω.property))

/- Exact moving-frame identity for each normalized block. -/
omit [Fintype G] [Fintype Ω] in
theorem conditionalBlock_eq (ρ : UnitaryIrrep C.stabilizer) (w : W → ℝ) (g : W → G)
    (x y : Ω) (ω₀ : W) (h₀ : y=a (g ω₀) x) :
    C.conditionalBlock ρ w g y x=ρ.matrix (C.cocycle (g ω₀) x)*C.transitionAverage ρ w g x y ω₀ h₀ := by
  unfold conditionalBlock transitionAverage
  rw [Matrix.mul_smul,Matrix.mul_sum]
  congr 1
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun ω => y=a (g ω) x) (Finset.univ.filter (fun ω => y=a (g ω) x))
    (by intro ω; simp)]
  apply Finset.sum_congr rfl
  intro ω _
  change (w ω.val : ℂ) • ρ.matrix (C.cocycle (g ω.val) x)=
    ρ.matrix (C.cocycle (g ω₀) x)*((w ω.val : ℂ) •
      ρ.matrix ((C.pointEquiv x).symm (C.transitionResidual x y (g ω₀) (g ω.val) h₀ ω.property)))
  rw [Matrix.mul_smul,← map_mul]
  congr 2
  exact C.cocycle_residual x y (g ω₀) (g ω.val) h₀ ω.property

end CoordinateSweeps.PlacementInduction.Chart

end
end
open scoped Matrix.Norms.L2Operator

end OAI
