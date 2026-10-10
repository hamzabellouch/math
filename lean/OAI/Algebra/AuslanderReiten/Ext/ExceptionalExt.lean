import OAI.Algebra.AuslanderReiten.Ext.BaseExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra

namespace ArExplicit.Resolution

open ArExplicit.Letter ArExplicit.BaseAlgebra

variable {k : Type*} [Field k] [CharP k 2] (q : k)

local notation "C" => BaseAlgebra k q

theorem dualHom_exceptional_decomposition (hq : q ≠ 0) (hq1 : 1 + q ≠ 0)
    (g : E q →ₗ[C] C) (hg : g.comp (dEll q q) = 0) :
    ∃ f : E q →ₗ[C] C, f.comp (dEll q 1) =
      g - (g (vertexE q)).coeff v • exceptionalHom q := by
  let r := (g (vertexE q)).coeff v
  let g' := g - r • exceptionalHom q
  have hg' : g'.comp (dEll q q) = 0 := by
    simp [g', LinearMap.sub_comp, LinearMap.smul_comp, hg, exceptionalHom_cocycle]
  have hc : leftEll q q (evaluateE q g') = 0 := by
    rw [← evaluateE_precompose, hg']
    rfl
  have hv : ((evaluateE q g' : rightE q) : C).coeff v = 0 := by
    simp [evaluateE, g', r, exceptionalHom, fromRightE, vertexE, exceptionalCycle,
      sub_eq_add_neg, basis_mul, multiplicationTable]
  obtain ⟨a, ha⟩ := (exceptional_boundary_iff q hq hq1 _ hc).mpr hv
  refine ⟨fromRightE q a, ?_⟩
  apply (homEEquiv q).injective
  change evaluateE q ((fromRightE q a).comp (dEll q 1)) = evaluateE q g'
  rw [evaluateE_precompose, evaluateE_fromRightE, ha]

omit [CharP k 2] in

theorem extMk_smul_regular {M : ModuleCat C} (P : ProjectiveResolution M) {n : ℕ}
    (f : P.complex.X n ⟶ ModuleCat.of C C) (m : ℕ) (hm : n + 1 = m)
    (hf : P.complex.d m n ≫ f = 0) (r : k)
    (hrf : P.complex.d m n ≫ (r • f) = 0) :
    P.extMk (r • f) m hm hrf = r • P.extMk f m hm hf := by
  rw [Ext.smul_eq_comp_mk₀, P.extMk_comp_mk₀]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change r • f.hom a = algebraMap k C r * f.hom a
  exact Algebra.smul_def r _

def exceptionalExtLinear (h : NoPositivePowerOne q) :
    k →ₗ[k] Ext (ModuleCat.of C (Simple q)) (ModuleCat.of C C) 2 :=
  LinearMap.toSpanSingleton k _ (regular_ext_two_class q h)

theorem exceptionalExtLinear_injective (h : NoPositivePowerOne q) (hq : q ≠ 0) :
    Function.Injective (exceptionalExtLinear q h) := by
  intro a b hab
  have heq : (a - b) • regular_ext_two_class q h = 0 := by
    change a • regular_ext_two_class q h = b • regular_ext_two_class q h at hab
    rw [sub_smul, hab, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp heq).resolve_right (regular_ext_two_class_ne_zero q h hq))

theorem regular_ext_two_representative (h : NoPositivePowerOne q) (hq : q ≠ 0)
    (g : (projectiveResolution q h).complex.X 2 ⟶ ModuleCat.of C C)
    (hg : (projectiveResolution q h).complex.d 3 2 ≫ g = 0) :
    (projectiveResolution q h).extMk g 3 rfl hg =
      (g.hom (vertexE q)).coeff v • regular_ext_two_class q h := by
  let P := projectiveResolution q h
  have hg' : g.hom.comp (dEll q q) = 0 := by
    have hh := congrArg ModuleCat.Hom.hom hg
    change g.hom.comp (dEll q (q ^ 1)) = 0 at hh
    simpa only [pow_one] using! hh
  let r := (g.hom (vertexE q)).coeff v
  obtain ⟨f, hf⟩ := dualHom_exceptional_decomposition q hq (by simpa using h 1 (by decide)) g.hom hg'
  let vHom : P.complex.X 2 ⟶ ModuleCat.of C C := ModuleCat.ofHom (exceptionalHom q)
  have hv : P.complex.d 3 2 ≫ vHom = 0 := by
    apply ModuleCat.hom_ext
    change (exceptionalHom q).comp (dEll q (q ^ 1)) = 0
    simpa only [pow_one] using exceptionalHom_cocycle q
  have hrv : P.complex.d 3 2 ≫ (r • vHom) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    have hb := congrArg (fun z => z.hom b) hv
    change r • vHom.hom ((P.complex.d 3 2).hom b) = 0
    change vHom.hom ((P.complex.d 3 2).hom b) = 0 at hb
    rw [hb, smul_zero]
  have hd : P.complex.d 3 2 ≫ (g - r • vHom) = 0 := by
    rw [Preadditive.comp_sub, hg, hrv, sub_zero]
  have hbound : P.extMk (g - r • vHom) 3 rfl hd = 0 := by
    apply (P.extMk_eq_zero_iff _ 3 rfl hd 1 rfl).mpr
    refine ⟨ModuleCat.ofHom f, ?_⟩
    apply ModuleCat.hom_ext
    change f.comp (dEll q (q ^ 0)) = (g - r • vHom).hom
    apply LinearMap.ext
    intro b
    have hb := LinearMap.congr_fun hf b
    simpa [r, vHom, pow_zero, Algebra.smul_def] using! hb
  have hrep : P.extMk vHom 3 rfl hv = regular_ext_two_class q h := rfl
  rw [← P.sub_extMk g (r • vHom) 3 rfl hg hrv, extMk_smul_regular q P vHom 3 rfl hv r hrv, hrep] at hbound
  exact sub_eq_zero.mp hbound

theorem exceptionalExtLinear_surjective (h : NoPositivePowerOne q) (hq : q ≠ 0) :
    Function.Surjective (exceptionalExtLinear q h) := by
  intro a
  obtain ⟨g, hg, rfl⟩ := (projectiveResolution q h).extMk_surjective a 3 rfl
  exact ⟨(g.hom (vertexE q)).coeff v, (regular_ext_two_representative q h hq g hg).symm⟩

def exceptionalExtEquiv (h : NoPositivePowerOne q) (hq : q ≠ 0) :
    k ≃ₗ[k] Ext (ModuleCat.of C (Simple q)) (ModuleCat.of C C) 2 :=
  LinearEquiv.ofBijective (exceptionalExtLinear q h)
    ⟨exceptionalExtLinear_injective q h hq, exceptionalExtLinear_surjective q h hq⟩

theorem regular_ext_two_finrank (h : NoPositivePowerOne q) (hq : q ≠ 0) :
    Module.finrank k (Ext (ModuleCat.of C (Simple q)) (ModuleCat.of C C) 2) = 1 := by
  rw [← (exceptionalExtEquiv q h hq).finrank_eq]
  exact Module.finrank_self k

theorem regular_ext_two_right_action (h : NoPositivePowerOne q) (hq : q ≠ 0)
    (a : Ext (ModuleCat.of C (Simple q)) (ModuleCat.of C C) 2) (b : C) :
    a.comp (Ext.mk₀ (ModuleCat.ofHom (rightMultiply q b))) (add_zero 2) = b.coeff f • a := by
  let P := projectiveResolution q h
  obtain ⟨g, hg, rfl⟩ := P.extMk_surjective a 3 rfl
  have hgc : g.hom.comp (dEll q q) = 0 := by
    have hh := congrArg ModuleCat.Hom.hom hg
    change g.hom.comp (dEll q (q ^ 1)) = 0 at hh
    simpa only [pow_one] using! hh
  let gl : E q →ₗ[C] C := g.hom
  have hgl : gl.comp (dEll q q) = 0 := hgc
  have hc : leftEll q q (evaluateE q gl) = 0 := by
    rw [← evaluateE_precompose, hgl]
    rfl
  rw [P.extMk_comp_mk₀]
  rw [regular_ext_two_representative q h hq, regular_ext_two_representative q h hq]
  change (g.hom (vertexE q) * b).coeff v • regular_ext_two_class q h = _
  have hcoeff := exceptional_right_action q hq (by simpa using h 1 (by decide))
    (evaluateE q gl) hc b
  change (g.hom (vertexE q) * b).coeff v = (g.hom (vertexE q)).coeff v * b.coeff f at hcoeff
  rw [hcoeff, mul_comm, mul_smul]

theorem exceptionalExtEquiv_right_action (h : NoPositivePowerOne q) (hq : q ≠ 0)
    (r : k) (b : C) :
    (exceptionalExtEquiv q h hq r).comp (Ext.mk₀ (ModuleCat.ofHom (rightMultiply q b)))
        (add_zero 2) = exceptionalExtEquiv q h hq (r * b.coeff f) := by
  rw [regular_ext_two_right_action q h hq]
  change b.coeff f • (r • regular_ext_two_class q h) = (r * b.coeff f) • regular_ext_two_class q h
  rw [← mul_smul, mul_comm]

end ArExplicit.Resolution

end

end OAI
