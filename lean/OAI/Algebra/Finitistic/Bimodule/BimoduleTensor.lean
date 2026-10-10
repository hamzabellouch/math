import OAI.Algebra.Finitistic.Bar.Balanced

namespace OAI
open scoped TensorProduct
open TensorProduct
noncomputable section

namespace DerivedBar.BimoduleTensor
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [IsScalarTower k D X]
variable (V : Type u) [AddCommGroup V] [Module k V] [Module D V] [IsScalarTower k D V]

/-- Noncommutative balancing relations for an arbitrary (D,D)-bimodule X. -/
def relations : Submodule D (X ⊗[k] V) :=
  Submodule.span D {z | ∃ (x : X) (d : D) (v : V),
    z = (MulOpposite.op d • x) ⊗ₜ[k] v - x ⊗ₜ[k] (d • v)}

/-- Genuine balanced X ⊗_D V, with its exterior left D-action. -/
abbrev tensor := (X ⊗[k] V) ⧸ relations k D X V

def quotient : X ⊗[k] V →ₗ[D] tensor k D X V := (relations k D X V).mkQ

omit [IsScalarTower k D V] in
theorem balanced (x : X) (d : D) (v : V) :
    quotient k D X V ((MulOpposite.op d • x) ⊗ₜ[k] v) =
      quotient k D X V (x ⊗ₜ[k] (d • v)) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨x, d, v, rfl⟩)

section Maps
variable (W U : Type u) [AddCommGroup W] [Module k W] [Module D W] [IsScalarTower k D W]
  [AddCommGroup U] [Module k U] [Module D U] [IsScalarTower k D U]

theorem map_relations (h : V →ₗ[D] W) : relations k D X V ≤
    ((quotient k D X W).comp (AlgebraTensorModule.lTensor D X (h.restrictScalars k))).ker := by
  apply Submodule.span_le.mpr
  rintro z ⟨x, d, v, rfl⟩
  change quotient k D X W ((AlgebraTensorModule.lTensor D X (h.restrictScalars k))
    ((MulOpposite.op d • x) ⊗ₜ[k] v - x ⊗ₜ[k] (d • v))) = 0
  simp only [map_sub, AlgebraTensorModule.lTensor_tmul, LinearMap.coe_restrictScalars,
    LinearMap.map_smul]
  rw [balanced, sub_self]

def map (h : V →ₗ[D] W) : tensor k D X V →ₗ[D] tensor k D X W :=
  (relations k D X V).liftQ
    ((quotient k D X W).comp (AlgebraTensorModule.lTensor D X (h.restrictScalars k)))
    (map_relations k D X V W h)

@[simp] theorem map_quotient (h : V →ₗ[D] W) (x : X) (v : V) :
    map k D X V W h (quotient k D X V (x ⊗ₜ[k] v)) =
      quotient k D X W (x ⊗ₜ[k] h v) := rfl

theorem map_comp (h : V →ₗ[D] W) (g : W →ₗ[D] U) :
    map k D X V U (g.comp h) = (map k D X W U g).comp (map k D X V W h) := by
  apply (relations k D X V).linearMap_qext
  apply AlgebraTensorModule.ext
  intro x v
  rfl

@[simp] theorem map_zero : map k D X V W 0 = 0 := by
  apply (relations k D X V).linearMap_qext
  apply AlgebraTensorModule.ext
  intro x v
  change quotient k D X W (x ⊗ₜ[k] (0 : W)) = 0
  rw [TensorProduct.tmul_zero, _root_.map_zero]

@[simp] theorem map_id : map k D X V V LinearMap.id = LinearMap.id := by
  apply (relations k D X V).linearMap_qext
  apply AlgebraTensorModule.ext
  intro x v
  rfl

theorem map_add (h g : V →ₗ[D] W) :
    map k D X V W (h+g) = map k D X V W h + map k D X V W g := by
  apply (relations k D X V).linearMap_qext
  apply AlgebraTensorModule.ext
  intro x v
  change quotient k D X W (x ⊗ₜ[k] (h v + g v)) =
    quotient k D X W (x ⊗ₜ[k] h v) + quotient k D X W (x ⊗ₜ[k] g v)
  rw [TensorProduct.tmul_add, _root_.map_add]
end Maps

variable [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X]

/-- The bimodule right action, bilinear over the field. -/
def rightMul : X →ₗ[k] D →ₗ[k] X where
  toFun x :=
    { toFun := fun d => MulOpposite.op d • x
      map_add' := by intro a b; simp [add_smul]
      map_smul' := by intro c d; simp [MulOpposite.op_smul, smul_assoc] }
  map_add' := by intro x y; ext d; simp [smul_add]
  map_smul' := by intro c x; ext d; simp [smul_comm (MulOpposite.op d) c]

/-- Multiplication X ⊗_k D → X respects the arbitrary exterior D-action. -/
def rightAction : X ⊗[k] D →ₗ[D] X :=
  { (TensorProduct.lift (rightMul k D X)).toAddHom with
    map_smul' := by
      intro a z
      induction z using TensorProduct.inductionOn with
      | tmul x d =>
        change (TensorProduct.lift (rightMul k D X)) (a • (x ⊗ₜ[k] d)) =
          a • ((TensorProduct.lift (rightMul k D X)) (x ⊗ₜ[k] d))
        rw [TensorProduct.smul_tmul']
        exact (smul_comm a (MulOpposite.op d) x).symm
      | add v w hv hw => simp_all [smul_add] }

@[simp] theorem rightAction_tmul (x : X) (d : D) :
    rightAction k D X (x ⊗ₜ[k] d) = MulOpposite.op d • x := rfl

variable (W : Type u) [AddCommGroup W] [Module k W]

/-- Collapse the first two slots using the right D-action on X. -/
def collapse : X ⊗[k] (D ⊗[k] W) →ₗ[D] X ⊗[k] W :=
  { ((TensorProduct.map ((rightAction k D X).restrictScalars k) LinearMap.id).comp
      (TensorProduct.assoc k X D W).symm.toLinearMap).toAddHom with
    map_smul' := by
      intro a z
      induction z using TensorProduct.inductionOn with
      | tmul x v =>
        induction v using TensorProduct.inductionOn with
        | tmul d w =>
          rw [TensorProduct.smul_tmul']
          change (MulOpposite.op d • (a • x)) ⊗ₜ[k] w =
            a • ((MulOpposite.op d • x) ⊗ₜ[k] w)
          rw [TensorProduct.smul_tmul', ← smul_comm a (MulOpposite.op d) x]
        | add v w hv hw => simp_all [TensorProduct.tmul_add, smul_add]
      | add v w hv hw => simp_all [smul_add] }

@[simp] theorem collapse_tmul (x : X) (d : D) (w : W) :
    collapse k D X W (x ⊗ₜ[k] (d ⊗ₜ[k] w)) = (MulOpposite.op d • x) ⊗ₜ[k] w := rfl

/-- The collapse descends through the actual balancing relations. -/
theorem relations_le_ker_collapse : relations k D X (D ⊗[k] W) ≤ (collapse k D X W).ker := by
  apply Submodule.span_le.mpr
  rintro z ⟨x, d, v, rfl⟩
  change collapse k D X W ((MulOpposite.op d • x) ⊗ₜ[k] v - x ⊗ₜ[k] (d • v)) = 0
  induction v using TensorProduct.inductionOn with
  | tmul a w =>
    rw [_root_.map_sub, collapse_tmul, TensorProduct.smul_tmul', smul_eq_mul, collapse_tmul]
    simp [← mul_smul, ← MulOpposite.op_mul]
  | add v w hv hw =>
    simp only [TensorProduct.tmul_add, smul_add, _root_.map_sub, _root_.map_add] at *
    rw [sub_eq_zero.mp hv, sub_eq_zero.mp hw, sub_self]

def descend : tensor k D X (D ⊗[k] W) →ₗ[D] X ⊗[k] W :=
  (relations k D X (D ⊗[k] W)).liftQ (collapse k D X W) (relations_le_ker_collapse k D X W)

def insert : X ⊗[k] W →ₗ[D] tensor k D X (D ⊗[k] W) :=
  (quotient k D X (D ⊗[k] W)).comp
    (AlgebraTensorModule.lTensor D X (TensorProduct.mk k D W 1))

@[simp] theorem descend_quotient (z : X ⊗[k] (D ⊗[k] W)) :
    descend k D X W (quotient k D X (D ⊗[k] W) z) = collapse k D X W z := rfl

omit [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X] in
@[simp] theorem insert_tmul (x : X) (w : W) :
    insert k D X W (x ⊗ₜ[k] w) = quotient k D X (D ⊗[k] W) (x ⊗ₜ[k] (1 ⊗ₜ[k] w)) := rfl

theorem descend_insert : (descend k D X W).comp (insert k D X W) = LinearMap.id := by
  apply AlgebraTensorModule.ext
  intro x w
  simp only [LinearMap.comp_apply, insert_tmul, descend_quotient, collapse_tmul,
    MulOpposite.op_one, one_smul, LinearMap.id_apply]

theorem insert_descend : (insert k D X W).comp (descend k D X W) = LinearMap.id := by
  apply (relations k D X (D ⊗[k] W)).linearMap_qext
  apply AlgebraTensorModule.ext
  intro x v
  induction v using TensorProduct.inductionOn with
  | tmul d w =>
    change insert k D X W (collapse k D X W (x ⊗ₜ[k] (d ⊗ₜ[k] w))) =
      quotient k D X (D ⊗[k] W) (x ⊗ₜ[k] (d ⊗ₜ[k] w))
    rw [collapse_tmul, insert_tmul, balanced]
    simp [TensorProduct.smul_tmul']
  | add v w hv hw => simp_all [TensorProduct.tmul_add]

/-- Genuine X ⊗_D (D ⊗_k W) ≅ X ⊗_k W, with no flatness of X. -/
def freeEquiv : tensor k D X (D ⊗[k] W) ≃ₗ[D] X ⊗[k] W :=
  LinearEquiv.ofLinearMap (descend k D X W) (insert k D X W)
    (descend_insert k D X W) (insert_descend k D X W)
end DerivedBar.BimoduleTensor

end

end OAI
