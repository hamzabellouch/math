import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FiniteCentralKernel
import OAI.GroupTheory.SimpleAmenable.Homology.IntegralTransgressionHomology

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section IntegralTransgressionFinite
open Classical
namespace IntegralTransgression
open groupHomology CategoryTheory
variable {H E : Type} [Group H] [Group E]
variable (q : H →* E) (hq : Function.Surjective q) (hc : q.ker ≤ Subgroup.center H)

 theorem onCycles_kills_homology_kernel :
    (H2π (coefficients E)).hom.ker ≤ (onCycles q hq hc).ker := by
  intro x hx
  have hb := (H2π_eq_zero_iff x).mp hx
  obtain ⟨y,hy⟩ := hb
  change onChains q hq hc x.val=0
  rw [←hy]
  exact LinearMap.congr_fun (onChains_d3 q hq hc) y

theorem cycles_to_h2_surjective : Function.Surjective (H2π (coefficients E)) := by
  intro x
  induction x using H2_induction_on with
  | h x => exact ⟨x,rfl⟩

noncomputable def transgression : H2 (coefficients E) →ₗ[ℤ] Additive (Kernel q hc) :=
by
  let f : cycles₂ (coefficients E) →ₗ[ℤ] H2 (coefficients E) := (H2π (coefficients E)).hom
  have hf : Function.Surjective f := cycles_to_h2_surjective
  have hk : f.ker ≤ (onCycles q hq hc).ker := onCycles_kills_homology_kernel q hq hc
  exact factorThrough f hf (onCycles q hq hc) hk

@[simp] theorem transgression_cycle (x : cycles₂ (coefficients E)) :
    transgression q hq hc (H2π (coefficients E) x)=onCycles q hq hc x :=
  factorThrough_apply _ _ _ _ x

theorem transgression_surjective [Group.IsPerfect H] :
    Function.Surjective (transgression q hq hc) := by
  intro k
  obtain ⟨x,hx⟩ := onCycles_surjective q hq hc k
  exact ⟨H2π (coefficients E) x,(transgression_cycle q hq hc x).trans hx⟩

include hq hc in

theorem kernel_fg [Group.IsPerfect H] [Module.Finite ℤ (H2 (coefficients E))] :
    Group.FG q.ker := by
  have : Module.Finite ℤ (Additive (Kernel q hc)) :=
    Module.Finite.of_surjective (transgression q hq hc) (transgression_surjective q hq hc)
  have : AddGroup.FG (Additive (Kernel q hc)) := Module.Finite.iff_addGroup_fg.mp inferInstance
  have : Group.FG (Kernel q hc) := GroupFG.iff_add_fg.mpr inferInstance
  exact this

end IntegralTransgression
end IntegralTransgressionFinite

section HomologyFinitePresentation

theorem universalKernel_fg_of_integral_h2 {E : Type} [Group E] [Group.IsPerfect E]
    [Module.Finite ℤ (groupHomology.H2 (IntegralTransgression.coefficients E))] :
    Group.FG (universalProjection E).ker :=
  IntegralTransgression.kernel_fg (universalProjection E)
    (universalProjection_surjective E) (universalProjection_central E)

theorem finitelyPresented_of_central_cover_h2 {H E : Type} [Group H] [Group E]
    [Group.IsPerfect E] [Group.IsFinitelyPresented H]
    [Module.Finite ℤ (groupHomology.H2 (IntegralTransgression.coefficients E))]
    (q : H →* E) (hq : Function.Surjective q) (hc : q.ker ≤ Subgroup.center H) :
    Group.IsFinitelyPresented E := by
  have := universalKernel_fg_of_integral_h2 (E:=E)
  exact finitelyPresented_of_central_cover q hq hc

end HomologyFinitePresentation

section IntegralHomologyConjugation
open Classical CategoryTheory Finsupp groupHomology
namespace IntegralHomology

abbrev coefficients (E : Type) [Group E] := IntegralTransgression.coefficients E

variable {E F : Type} [Group E] [Group F]

noncomputable def coefficientMap (f : E →* F) : coefficients E ⟶ Rep.res f (coefficients F) :=
  Rep.ofHom ⟨LinearMap.id,fun _ => rfl⟩

noncomputable def mapH2 (f : E →* F) : H2 (coefficients E) →ₗ[ℤ] H2 (coefficients F) :=
  (groupHomology.map f (coefficientMap f) 2).hom

noncomputable def mapC2 (f : E →* F) : (E×E →₀ ℤ) →ₗ[ℤ] (F×F →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (Prod.map f f)

@[simp] theorem mapC2_single (f : E →* F) (x y : E) (n : ℤ) :
    mapC2 f (single (x,y) n)=single (f x,f y) n := by
  simp [mapC2]

noncomputable def prism1 (c : E) : (E →₀ ℤ) →ₗ[ℤ] (E×E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => single (c,x) 1 - single (MulAut.conj c x,c) 1)

noncomputable def prism2 (c : E) : (E×E →₀ ℤ) →ₗ[ℤ] (E×E×E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun xy =>
    single (c,xy.1,xy.2) 1 - single (MulAut.conj c xy.1,c,xy.2) 1 +
      single (MulAut.conj c xy.1,MulAut.conj c xy.2,c) 1)

@[simp] theorem prism1_single (c x : E) (n : ℤ) :
    prism1 c (single x n)=single (c,x) n-single (MulAut.conj c x,c) n := by
  simp [prism1,smul_sub,Finsupp.smul_single]

@[simp] theorem prism2_single (c x y : E) (n : ℤ) :
    prism2 c (single (x,y) n)=single (c,x,y) n-single (MulAut.conj c x,c,y) n+
      single (MulAut.conj c x,MulAut.conj c y,c) n := by
  simp [prism2,smul_sub,smul_add,Finsupp.smul_single]

lemma boundary2_single (x y : E) (n : ℤ) :
    d₂₁ (coefficients E) (single (x,y) n)=single y n-single (x*y) n+single x n := by
  rw [d₂₁_single]
  rfl

lemma boundary3_single (x y z : E) (n : ℤ) :
    d₃₂ (coefficients E) (single (x,y,z) n)=
      single (y,z) n-single (x*y,z) n+single (x,y*z) n-single (x,y) n := by
  rw [d₃₂_single]
  rfl

theorem prism_identity (c : E) :
    (d₃₂ (coefficients E)).hom.comp (prism2 c) +
      (prism1 c).comp (d₂₁ (coefficients E)).hom =
        LinearMap.id - mapC2 (MulAut.conj c).toMonoidHom := by
  apply Finsupp.lhom_ext
  intro xy n
  rcases xy with ⟨x,y⟩
  change d₃₂ (coefficients E) (prism2 c (single (x,y) n)) +
    prism1 c (d₂₁ (coefficients E) (single (x,y) n)) =
    single (x,y) n-mapC2 (MulAut.conj c).toMonoidHom (single (x,y) n)
  rw [prism2_single, map_add, map_sub, boundary3_single, boundary3_single,
    boundary3_single, boundary2_single, map_add, map_sub, prism1_single,
    prism1_single, prism1_single, mapC2_single]
  simp only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,MulAut.conj_apply,mul_assoc,
    inv_mul_cancel_left,inv_mul_cancel,mul_one]
  abel

end IntegralHomology
end IntegralHomologyConjugation

end SimpleAmenable
end
end

end OAI
