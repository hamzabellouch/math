import OAI.NumberTheory.Ostmann.Tree.CycleProjection
import OAI.NumberTheory.Ostmann.Tree.CycleQuartetActions
import OAI.NumberTheory.Ostmann.Tree.QuartetFactorization
import OAI.NumberTheory.Ostmann.Tree.TensorActionProjection

namespace OAI

namespace Ostmann.Tree.CycleFiberProjection
noncomputable section
open scoped BigOperators
open QuartetFactorization CycleQuartet
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {k b : ℕ} (P : LeafPartition (k+2) b)
  (c : BalancedSelection P.label (quartetCut k).label)

local instance productFiberFintype {m : Fˣ} : Fintype (ProductFiber m) := Fintype.ofFinite _
local instance cutFiberFintype (totals : Leaves k → Fˣ) :
    Fintype {M : Leaves (k+2) → Fˣ // (bottomCut k).project M=totals} := Fintype.ofFinite _

omit [Fintype F] [DecidableEq F] in
theorem bottom_project_act (z : Fˣ) (M : Leaves (k+2) → Fˣ) :
    (bottomCut k).project (c.act z M)=(bottomCut k).project M := by
  have h := quartet_cycle_project P c z M
  have he : Density.Cut.project (F := F) (quartetCut k)=
      Density.Cut.project (F := F) (bottomCut k) :=
    congrArg (fun C : Density.Cut (k+2) k => Density.Cut.project (F := F) C) (cut_unique _ _)
  simpa only [he] using h

def fiberProjection (totals : Leaves k → Fˣ) (fs : Leaves k → Frame F)
    (g : F → ℂ) (D : Fˣ) (m : ∀ v, ProductFiber (totals v)) : ℂ :=
  letI : ∀ v, MulAction Fˣ (ProductFiber (totals v)) := fun v => fiberMulAction P c v (totals v)
  Ostmann.FiniteField.actionProjection (F := F)
    (fun v (a : ProductFiber (totals v)) => (fs v).value g D a.val) m

theorem projection_zero_of_invalid (T : Diagram F (k+2)) (g : F → ℂ)
    (totals : Leaves k → Fˣ)
    (h : propagate k T.parameters T.rootLeft T.rootRight
      (Density.rootCoefficient T.parameters) totals = none)
    (M : {M : Leaves (k+2) → Fˣ // (bottomCut k).project M=totals}) :
    c.projection (T.value g) M.val = 0 := by
  unfold BalancedSelection.projection Arithmetic.ResidueHaar.average
  have he (z : Fˣ) : T.value g (c.act z M.val)=0 := by
    apply diagram_value_zero_of_invalid
    unfold ancestorFrames
    rw [bottom_project_act P c,M.property,h]
  simp only [he,Finset.sum_const_zero,mul_zero]

theorem projection_eq_fiberProjection (T : Diagram F (k+2)) (g : F → ℂ)
    (totals : Leaves k → Fˣ) (fs : Leaves k → Frame F)
    (h : propagate k T.parameters T.rootLeft T.rootRight
      (Density.rootCoefficient T.parameters) totals = some fs)
    (M : {M : Leaves (k+2) → Fˣ // (bottomCut k).project M=totals}) :
    c.projection (T.value g) M.val =
      fiberProjection P c totals fs g T.denominator (productFiberEquiv k totals M) := by
  unfold BalancedSelection.projection Arithmetic.ResidueHaar.average
    fiberProjection Ostmann.FiniteField.actionProjection
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  change T.value g (c.act z M.val) = _
  rw [diagram_factorization]
  have he : ancestorFrames T (c.act z M.val)=some fs := by
    unfold ancestorFrames
    rw [bottom_project_act P c,M.property,h]
  rw [he]
  change (∏ v,(fs v).value g T.denominator (bottomLeaves k (c.act z M.val) v)) = _
  apply Finset.prod_congr rfl
  intro v _
  rw [bottomLeaves_act P c]
  rfl

theorem real_average_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) :
    Density.average (fun x => f (e x))=Density.average f := by
  unfold Density.average
  rw [Fintype.card_congr e,e.sum_comp]

theorem projection_energy_on_fiber (T : Diagram F (k+2)) (g : F → ℂ)
    (totals : Leaves k → Fˣ) (fs : Leaves k → Frame F)
    (h : propagate k T.parameters T.rootLeft T.rootRight
      (Density.rootCoefficient T.parameters) totals = some fs) :
    Density.average (fun M : {M : Leaves (k+2) → Fˣ // (bottomCut k).project M=totals} =>
      ‖c.projection (T.value g) M.val‖^2) =
    Density.average (fun m : ∀ v, ProductFiber (totals v) =>
      ‖fiberProjection P c totals fs g T.denominator m‖^2) := by
  simp_rw [projection_eq_fiberProjection P c T g totals fs h]
  have he := real_average_equiv (productFiberEquiv k totals)
    (fun m => ‖fiberProjection P c totals fs g T.denominator m‖^2)
  simpa only [real_average_fintype_congr _
    (inferInstance : Fintype (∀ v, ProductFiber (totals v)))] using he

theorem projection_energy_zero_of_invalid (T : Diagram F (k+2)) (g : F → ℂ)
    (totals : Leaves k → Fˣ)
    (h : propagate k T.parameters T.rootLeft T.rootRight
      (Density.rootCoefficient T.parameters) totals = none) :
    Density.average (fun M : {M : Leaves (k+2) → Fˣ // (bottomCut k).project M=totals} =>
      ‖c.projection (T.value g) M.val‖^2) = 0 := by
  simp only [projection_zero_of_invalid P c T g totals h,norm_zero,zero_pow (by decide : 2 ≠ 0),
    Density.average,Finset.sum_const_zero,mul_zero]

end
end Ostmann.Tree.CycleFiberProjection

end OAI
