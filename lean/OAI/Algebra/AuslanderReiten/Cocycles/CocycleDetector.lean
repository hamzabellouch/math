import OAI.Algebra.AuslanderReiten.Bar.ModuleBarCochain
import OAI.Algebra.AuslanderReiten.Algebras.TSimple
import OAI.Algebra.AuslanderReiten.Cocycles.SparseCocycle

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct

namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q
local notation "S" => Resolution.Simple q

def simpleGenerator : S := Submodule.Quotient.mk (Resolution.vertexF q)

@[simp] theorem simpleGenerator_coordinate : Resolution.simpleCoordinate q (simpleGenerator q) = 1 := by
  simp [simpleGenerator, Resolution.vertexF]

theorem vector_smul_simple (hq1 : 1 + q ≠ 0) (i : TIndex) (s : S) :
    T.vector q i • s = if i = (false, .f) then s else 0 := by
  apply Resolution.simpleCoordinate_injective q hq1
  rw [Resolution.t_simple_character]
  have hc : (T.vector q i).base.coeff .f = if i = (false, .f) then 1 else 0 := by
    change T.coefficient q (false, .f) (T.vector q i) = _
    simp [eq_comm]
  rw [hc]
  split_ifs <;> simp

private theorem tx_product : T.vector q (false, .t) * T.vector q (false, .x) = T.vector q (false, .j) := by
  apply T.coordinate_ext q
  intro i
  rw [multiplication_coefficient]
  simp [multiplicationCoefficient, multiplication, eq_comm]

private theorem ty_product : T.vector q (false, .t) * T.vector q (false, .y) = q ^ 2 • T.vector q (false, .j) := by
  apply T.coordinate_ext q
  intro i
  rw [multiplication_coefficient]
  simp [multiplicationCoefficient, multiplication, eq_comm, mul_ite]

private theorem xJ_product : T.vector q (false, .x) * T.vector q (true, .j) = T.vector q (true, .t) := by
  apply T.coordinate_ext q
  intro i
  rw [multiplication_coefficient]
  simp [multiplicationCoefficient, multiplication, eq_comm]

private theorem yJ_product : T.vector q (false, .y) * T.vector q (true, .j) = q ^ 2 • T.vector q (true, .t) := by
  apply T.coordinate_ext q
  intro i
  rw [multiplication_coefficient]
  simp [multiplicationCoefficient, multiplication, eq_comm, mul_ite]

def detector : ModuleBar.moduleObject k R S 4 :=
  q ^ 2 • ((1 : R) ⊗ₜ[k] (T.vector q (false, .t) ⊗ₜ[k]
    (T.vector q (false, .x) ⊗ₜ[k] (T.vector q (true, .j) ⊗ₜ[k] simpleGenerator q)))) +
  (1 : R) ⊗ₜ[k] (T.vector q (false, .t) ⊗ₜ[k]
    (T.vector q (false, .y) ⊗ₜ[k] (T.vector q (true, .j) ⊗ₜ[k] simpleGenerator q)))

theorem detector_evaluation (hq1 : 1 + q ≠ 0) :
    ModuleBar.cochain3 k R S (p q) (detector q) = q ^ 3 • simpleGenerator q := by
  change ModuleBar.cochain3Linear k R S (p q) (detector q) = _
  simp only [detector, map_add, map_smul]
  rw [ModuleBar.cochain3Linear_tmul k R S (p q),
    ModuleBar.cochain3Linear_tmul k R S (p q)]
  simp only [one_mul, p_txJ, p_tyJ, zero_smul, smul_zero, zero_add]
  rw [smul_assoc, vector_smul_simple q hq1]
  simp

theorem detector_evaluation_ne_zero (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    ModuleBar.cochain3 k R S (p q) (detector q) ≠ 0 := by
  rw [detector_evaluation q hq1]
  intro hz
  change q ^ 3 • (simpleGenerator q : S) = 0 at hz
  have hh := congrArg (Resolution.simpleCoordinate q) hz
  apply pow_ne_zero 3 hq
  simpa only [map_smul, simpleGenerator_coordinate, smul_eq_mul, mul_one, map_zero] using hh

private theorem hom_tmul_t (hq1 : 1 + q ≠ 0)
    (g : ModuleBar.moduleObject k R S 3 →ₗ[R] ModuleBar.moduleObject k R S 0)
    (x : ModuleBar.object k R S 2) :
    g (T.vector q (false, .t) ⊗ₜ[k] x) = 0 := by
  have he := g.map_smul (T.vector q (false, .t))
    ((1 : R) ⊗ₜ[k] x : ModuleBar.moduleObject k R S 3)
  change g ((T.vector q (false, .t) * 1) ⊗ₜ[k] x) = _ at he
  rw [mul_one] at he
  rw [he]
  change T.vector q (false, .t) • (g ((1 : R) ⊗ₜ[k] x) : S) = 0
  convert! vector_smul_simple q hq1 (false, .t) (g ((1 : R) ⊗ₜ[k] x) : S) using 1

variable [CharP k 2]

theorem detector_boundary (hq1 : 1 + q ≠ 0)
    (g : ModuleBar.moduleObject k R S 3 →ₗ[R] ModuleBar.moduleObject k R S 0) :
    g (ModuleBar.differential k R S 3 (detector q)) = 0 := by
  let gk : ModuleBar.object k R S 3 →ₗ[k] S := g.restrictScalars k
  have hJ : T.vector q (true, .j) • simpleGenerator q = 0 := by
    rw [vector_smul_simple q hq1]
    simp
  change gk (ModuleBar.boundary k R S 3 (detector q)) = 0
  simp only [detector, map_add, map_smul]
  simp only [ModuleBar.boundary_succ_tmul k R S 2, ModuleBar.boundary_succ_tmul k R S 1,
    ModuleBar.boundary_succ_tmul k R S 0, ModuleBar.boundary_zero_tmul k R S,
    ModuleBar.left_tmul k R S 2, ModuleBar.left_tmul k R S 1, ModuleBar.left_tmul k R S 0,
    one_mul, tx_product, ty_product, xJ_product, yJ_product,
    hJ, TensorProduct.tmul_zero, TensorProduct.tmul_add,
    TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', map_add, map_smul, add_zero]
  have ht (x : ModuleBar.object k R S 2) : gk (T.vector q (false, .t) ⊗ₜ[k] x) = 0 :=
    hom_tmul_t q hq1 g x
  rw [ht, ht]
  simp only [zero_add, smul_add]
  exact SparseParity.module_add_self_eq_zero (k := k) _

end ArExplicit.CocycleData

end

end OAI
