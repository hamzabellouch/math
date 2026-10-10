import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTwistAction
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarExtTwist
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarCubic
import OAI.Algebra.AuslanderReiten.Ext.CubicExtAction
import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionHomology

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.ModuleBar
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [CharP k 2]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)

theorem twistExtAction_extMk (n : ℕ)
    (f g : (resolution k R M).complex.X n ⟶ ModuleCat.of R M)
    (hf : (resolution k R M).complex.d (n+1) n ≫ f = 0)
    (hg : (resolution k R M).complex.d (n+1) n ≫ g = 0)
    (hfg : ∀ x : moduleObject k R M (n+1), g.hom x =
      e.symm (f.hom (transport k R M h e (n+1) x))) :
    twistExtAction k R M h e he n ((resolution k R M).extMk f (n+1) rfl hf) =
      (resolution k R M).extMk g (n+1) rfl hg := by
  let f' : LinearMap.ker (ExternalTensor.homShort k R (Y := ModuleCat.of R M)
      (resolution k R M) n).g.hom := ⟨f.hom, by
    rw [ExternalTensor.homShort_outgoing]
    exact congrArg ModuleCat.Hom.hom hf⟩
  let g' : LinearMap.ker (ExternalTensor.homShort k R (Y := ModuleCat.of R M)
      (resolution k R M) n).g.hom := ⟨g.hom, by
    rw [ExternalTensor.homShort_outgoing]
    exact congrArg ModuleCat.Hom.hom hg⟩
  exact twistExtAction_cycle k R M h e he n f' g' hfg

omit [CharP k 2] in
theorem transportedHom_closed (n : ℕ) (f : moduleObject k R M (n+1) →ₗ[R] M)
    (hf : f.comp (differential k R M (n+1))=0) :
    (transportedHom k R M h e he (n+1) f).comp (differential k R M (n+1))=0 := by
  change (transportHom k R M h e he (n+1) f).comp (differential k R M (n+1))=0
  rw [← transportHom_differential, hf, map_zero]

def transportedCochain (n : ℕ)
    (f : (resolution k R M).complex.X n ⟶ ModuleCat.of R M) :
    (resolution k R M).complex.X n ⟶ ModuleCat.of R M :=
  ModuleCat.ofHom (X := (resolution k R M).complex.X n) (Y := ModuleCat.of R M)
    (transportedHom k R M h e he (n+1) f.hom)

theorem transportedCochain_closed (n : ℕ)
    (f : (resolution k R M).complex.X n ⟶ ModuleCat.of R M)
    (hf : (resolution k R M).complex.d (n+1) n ≫ f=0) :
    (resolution k R M).complex.d (n+1) n ≫ transportedCochain k R M h e he n f=0 := by
  change (complex k R M).d (n+1) n ≫ f=0 at hf
  change (complex k R M).d (n+1) n ≫ transportedCochain k R M h e he n f=0
  rw [complex_d] at hf ⊢
  apply ModuleCat.hom_ext
  exact transportedHom_closed k R M h e he n f.hom (congrArg ModuleCat.Hom.hom hf)

theorem twistExtAction_extMk_transported (n : ℕ)
    (f : (resolution k R M).complex.X n ⟶ ModuleCat.of R M)
    (hf : (resolution k R M).complex.d (n+1) n ≫ f=0) :
    twistExtAction k R M h e he n ((resolution k R M).extMk f (n+1) rfl hf) =
      (resolution k R M).extMk (transportedCochain k R M h e he n f) (n+1) rfl
        (transportedCochain_closed k R M h e he n f hf) :=
  twistExtAction_extMk k R M h e he n f _ hf _ (fun _ => rfl)

variable [HasDerivedCategory (ModuleCat.{u} R)]
variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)

theorem extClass3_comp_extMk (n : ℕ)
    (f : (resolution k R M).complex.X n ⟶ ModuleCat.of R M)
    (hf : (resolution k R M).complex.d (n+1) n ≫ f=0) :
    (extClass3 k R M p hp).comp ((resolution k R M).extMk f (n+1) rfl hf)
      (by omega : 3+n=n+3) =
    (resolution k R M).extMk (cubicMap k R M p n ≫ f) (n+4) rfl
      (ResolutionProducts.cubicPrecomp_closed (resolution k R M) (cubicMap k R M p)
        (cubicMap_comm k R M p hp) f hf) := by
  rw [← cubicCocycle_endExt k R M p hp]
  exact ResolutionProducts.cubic_endExt_comp_extMk (k := k) (resolution k R M)
    (cubicMap k R M p) (cubicMap_comm k R M p hp) f hf

variable (c : k)
variable (hpc : ∀ a b d m, p (h a) (h b) (h d) • e m = c • e (p a b d • m))
include hpc

omit [HasDerivedCategory (ModuleCat R)] in
theorem transportedCochain_cubic (n : ℕ)
    (f : (resolution k R M).complex.X n ⟶ ModuleCat.of R M) :
    transportedCochain k R M h e he (n+3) (cubicMap k R M p n ≫ f) =
      c • (cubicMap k R M p n ≫ transportedCochain k R M h e he n f) := by
  apply ModuleCat.hom_ext
  exact transportHom_suffixComparison k R M h e he p c hpc n f.hom

omit hpc [HasDerivedCategory (ModuleCat R)] in
private theorem extMk_congr (n : ℕ)
    (f g : (resolution k R M).complex.X n ⟶ ModuleCat.of R M)
    (hf : (resolution k R M).complex.d (n+1) n ≫ f=0)
    (hg : (resolution k R M).complex.d (n+1) n ≫ g=0) (hfg : f=g) :
    (resolution k R M).extMk f (n+1) rfl hf =
      (resolution k R M).extMk g (n+1) rfl hg := by
  subst g
  rfl

omit hpc [HasDerivedCategory (ModuleCat R)] in
private theorem extMk_smul_native (n : ℕ)
    (f : (resolution k R M).complex.X n ⟶ ModuleCat.of R M)
    (hf : (resolution k R M).complex.d (n+1) n ≫ f=0) (a : k)
    (ha : (resolution k R M).complex.d (n+1) n ≫ (a • f)=0) :
    (resolution k R M).extMk (a • f) (n+1) rfl ha =
      a • (resolution k R M).extMk f (n+1) rfl hf := by
  rw [Ext.smul_eq_comp_mk₀, ProjectiveResolution.extMk_comp_mk₀]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change a • f.hom x = (algebraMap k R a) • f.hom x
  exact (IsScalarTower.algebraMap_smul R a (f.hom x)).symm

theorem twistExtAction_cubic (n : ℕ)
    (x : Ext (moduleObject k R M 0) (ModuleCat.of R M) n) :
    twistExtAction k R M h e he (n+3) ((extClass3 k R M p hp).comp x (by omega : 3+n=n+3)) =
      c • (extClass3 k R M p hp).comp (twistExtAction k R M h e he n x) (by omega : 3+n=n+3) := by
  obtain ⟨f,hf,rfl⟩ := (resolution k R M).extMk_surjective x (n+1) rfl
  rw [extClass3_comp_extMk, twistExtAction_extMk_transported,
    twistExtAction_extMk_transported, extClass3_comp_extMk]
  have hc := ResolutionProducts.cubicPrecomp_closed (resolution k R M) (cubicMap k R M p)
    (cubicMap_comm k R M p hp) (transportedCochain k R M h e he n f)
    (transportedCochain_closed k R M h e he n f hf)
  have hsc : (resolution k R M).complex.d (n+3+1) (n+3) ≫
      (c • (cubicMap k R M p n ≫ transportedCochain k R M h e he n f)) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hc) x
    change (transportedCochain k R M h e he n f).hom
      ((cubicMap k R M p n).hom
        (((resolution k R M).complex.d (n+4) (n+3)).hom x)) = 0 at hx
    change c • (transportedCochain k R M h e he n f).hom
      ((cubicMap k R M p n).hom
        (((resolution k R M).complex.d (n+4) (n+3)).hom x)) = 0
    rw [hx, smul_zero]
  refine (extMk_congr k R M (n+3) _ _ _ hsc
    (transportedCochain_cubic k R M h e he p c hpc n f)).trans ?_
  exact extMk_smul_native k R M (n+3)
    (cubicMap k R M p n ≫ transportedCochain k R M h e he n f) hc c hsc

end ArExplicit.ModuleBar

end

end OAI
