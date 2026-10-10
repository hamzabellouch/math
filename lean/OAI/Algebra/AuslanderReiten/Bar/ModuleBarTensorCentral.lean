import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorGeneration
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorProducts
import OAI.Algebra.AuslanderReiten.Ext.ExtCentralGeneration

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R S M N : Type u) [Field k] [CharP k 2]
  [Ring R] [Algebra k R] [Module.Finite k R] [Ring S] [Algebra k S] [Module.Finite k S]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [Module.Finite k M]
  [AddCommGroup N] [Module S N] [Module k N] [IsScalarTower k S N] [Module.Finite k N]
variable [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
  [HasDerivedCategory (ModuleCat.{u} (R ⊗[k] S))]
variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)
variable (r : AbsoluteBar.Cochain3 k S) (hr : AbsoluteBar.IsCocycle3 k S r)
variable (a : Ext (ModuleCat.of R M) (ModuleCat.of R M) 3)
  (ha : extClass3 k R M p hp = a)
  (b : Ext (ModuleCat.of S N) (ModuleCat.of S N) 3)
  (hb : extClass3 k S N r hr = b)
local notation "X" => ExternalTensor.moduleObject k R S M N
variable (hgen : ∀ n : ℕ, ∀ z : ExternalTensor.extCoefficients k R S
    (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) (3*n+3),
  ∃ u v : ExternalTensor.extCoefficients k R S
    (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) (3*n),
    z = ExternalTensor.coefficientFirst k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) a (3*n) u +
    ExternalTensor.coefficientSecond k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) b (3*n) v)
include ha hb hgen

theorem tensor_cubic_central
    (hhom : ∀ f : ExternalTensor.moduleObject k R S M N ⟶ ExternalTensor.moduleObject k R S M N,
      ∃ c : k, ∀ z : ExternalTensor.moduleObject k R S M N,
        f.hom z = (algebraMap k (R ⊗[k] S) c) • z)
    (n : ℕ) (x : Ext X X (3*n)) :
    (tensorFirst k R S M N p hp).comp x (by omega : 3+3*n=3*(n+1)) =
      x.comp (tensorFirst k R S M N p hp) (by omega) ∧
    (tensorSecond k R S M N r hr).comp x (by omega : 3+3*n=3*(n+1)) =
      x.comp (tensorSecond k R S M N r hr) (by omega) := by
  refine ResolutionProducts.cubicCentral_of_generation
    (tensorFirst k R S M N p hp) (tensorSecond k R S M N r hr)
    (tensorCubics_commute k R S M N p hp r hr) ?_ ?_ n x
  · intro y
    obtain ⟨c, rfl⟩ := ResolutionProducts.extZero_scalar_of_hom (k := k)
      (fun f => by
        obtain ⟨c, hc⟩ := hhom f
        exact ⟨c, ResolutionProducts.scalar_end_hom X f c hc⟩) y
    constructor <;>
      rw [Ext.comp_smul, Ext.smul_comp, Ext.comp_mk₀_id, Ext.mk₀_id_comp]
  · intro j y
    exact tensor_generation k R S M N p hp r hr a ha b hb (3*j) (hgen j) y

end ArExplicit.ModuleBar

end

end OAI
