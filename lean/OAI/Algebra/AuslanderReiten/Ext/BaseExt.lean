import OAI.Algebra.AuslanderReiten.Duality.DualResolution

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace ArExplicit.Resolution

open ArExplicit.Letter ArExplicit.BaseAlgebra

variable {k : Type*} [Field k] [CharP k 2] (q : k)

local notation "C" => BaseAlgebra k q

theorem dualHom_exact_one (g : E q →ₗ[C] C) (hg : g.comp (dEll q 1) = 0) :
    ∃ f : F q →ₗ[C] C, f.comp (dU q) = g := by
  have hc : leftEll q 1 (evaluateE q g) = 0 := by
    rw [← evaluateE_precompose, hg]
    rfl
  obtain ⟨a, ha⟩ := (leftU_exact q (evaluateE q g)).mp hc
  refine ⟨fromRightF q a, ?_⟩
  apply (homEEquiv q).injective
  change evaluateE q ((fromRightF q a).comp (dU q)) = evaluateE q g
  rw [evaluate_precompose_dU, evaluateF_fromRightF, ha]

theorem dualHom_exact_tail (r : k) (hq : q ≠ 0) (hr : 1 + r ≠ 0)
    (hqr : 1 + q * r ≠ 0) (g : E q →ₗ[C] C)
    (hg : g.comp (dEll q (q * r)) = 0) :
    ∃ f : E q →ₗ[C] C, f.comp (dEll q r) = g := by
  have hc : leftEll q (q * r) (evaluateE q g) = 0 := by
    rw [← evaluateE_precompose, hg]
    rfl
  obtain ⟨a, ha⟩ := (leftEll_exact q r hq hr hqr (evaluateE q g)).mp hc
  refine ⟨fromRightE q a, ?_⟩
  apply (homEEquiv q).injective
  change evaluateE q ((fromRightE q a).comp (dEll q r)) = evaluateE q g
  rw [evaluateE_precompose, evaluateE_fromRightE, ha]

omit [CharP k 2] in

theorem hom_simple_regular_eq_zero (g : Simple q →ₗ[C] C) : g = 0 := by
  let f := g.comp (LinearMap.range (dU q)).mkQ
  have hf : f.comp (dU q) = 0 := by
    rw [LinearMap.comp_assoc, LinearMap.range_mkQ_comp, LinearMap.comp_zero]
  have hz : evaluateF q f = 0 := by
    apply leftU_injective q
    rw [← evaluate_precompose_dU, hf, map_zero]
    rfl
  have hf0 : f = 0 := (homFEquiv q).injective hz
  apply LinearMap.ext
  intro a
  refine Submodule.Quotient.induction_on _ a ?_
  intro b
  exact LinearMap.congr_fun hf0 b

omit [CharP k 2] in

theorem regular_ext_zero :
    Subsingleton (Ext (ModuleCat.of C (Simple q)) (ModuleCat.of C C) 0) := by
  refine ⟨fun a b => ?_⟩
  apply Ext.homEquiv₀.injective
  apply ModuleCat.hom_ext
  exact (hom_simple_regular_eq_zero q (Ext.homEquiv₀ a).hom).trans
    (hom_simple_regular_eq_zero q (Ext.homEquiv₀ b).hom).symm

theorem regular_ext_one (h : NoPositivePowerOne q) :
    Subsingleton (Ext (ModuleCat.of C (Simple q)) (ModuleCat.of C C) 1) := by
  let P := projectiveResolution q h
  have hz : ∀ a : Ext (ModuleCat.of C (Simple q)) (ModuleCat.of C C) 1, a = 0 := by
    intro a
    obtain ⟨g, hg, rfl⟩ := P.extMk_surjective a 2 rfl
    apply (P.extMk_eq_zero_iff g 2 rfl hg 0 rfl).mpr
    have hg' : g.hom.comp (dEll q 1) = 0 := by
      have hh := congrArg ModuleCat.Hom.hom hg
      change g.hom.comp (dEll q (q ^ 0)) = 0 at hh
      simpa only [pow_zero] using hh
    obtain ⟨f, hf⟩ := dualHom_exact_one q g.hom hg'
    refine ⟨ModuleCat.ofHom f, ?_⟩
    apply ModuleCat.hom_ext
    exact hf
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

theorem regular_ext_tail (h : NoPositivePowerOne q) (hq : q ≠ 0) (n : ℕ) :
    Subsingleton (Ext (ModuleCat.of C (Simple q)) (ModuleCat.of C C) (n + 3)) := by
  let P := projectiveResolution q h
  have hz : ∀ a : Ext (ModuleCat.of C (Simple q)) (ModuleCat.of C C) (n + 3), a = 0 := by
    intro a
    obtain ⟨g, hg, rfl⟩ := P.extMk_surjective a (n + 4) rfl
    apply (P.extMk_eq_zero_iff g (n + 4) rfl hg (n + 2) rfl).mpr
    have hg' : g.hom.comp (dEll q (q * q ^ (n + 1))) = 0 := by
      have hh := congrArg ModuleCat.Hom.hom hg
      change (ChainComplex.of.d (objects q) (differential q) ((n + 3) + 1) (n + 3) ≫ g).hom = 0 at hh
      rw [ChainComplex.of_d] at hh
      change g.hom.comp (dEll q (q ^ (n + 2))) = 0 at hh
      simpa only [pow_succ'] using hh
    obtain ⟨f, hf⟩ := dualHom_exact_tail q (q ^ (n + 1)) hq
      (h _ (by omega)) (by simpa [← pow_succ'] using h (n + 2) (by omega)) g.hom hg'
    refine ⟨ModuleCat.ofHom f, ?_⟩
    apply ModuleCat.hom_ext
    change (ChainComplex.of.d (objects q) (differential q) ((n + 2) + 1) (n + 2) ≫ ModuleCat.ofHom f).hom = g.hom
    rw [ChainComplex.of_d]
    change f.comp (dEll q (q ^ (n + 1))) = g.hom
    exact hf
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

theorem regular_ext_vanish (h : NoPositivePowerOne q) (hq : q ≠ 0)
    (n : ℕ) (hn : n ≠ 2) :
    Subsingleton (Ext (ModuleCat.of C (Simple q)) (ModuleCat.of C C) n) := by
  match n with
  | 0 => exact regular_ext_zero q
  | 1 => exact regular_ext_one q h
  | 2 => exact (hn rfl).elim
  | n + 3 => exact regular_ext_tail q h hq n

def exceptionalHom : E q →ₗ[C] C := fromRightE q (exceptionalCycle q)

omit [CharP k 2] in
theorem exceptionalHom_cocycle : (exceptionalHom q).comp (dEll q q) = 0 := by
  apply (homEEquiv q).injective
  change evaluateE q ((exceptionalHom q).comp (dEll q q)) = 0
  rw [evaluateE_precompose]
  simpa only [exceptionalHom, evaluateE_fromRightE] using exceptionalCycle_closed q q

theorem exceptionalHom_not_boundary (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    ¬ ∃ f : E q →ₗ[C] C, f.comp (dEll q 1) = exceptionalHom q := by
  rintro ⟨f, hf⟩
  apply exceptionalCycle_not_boundary q hq hq1
  refine ⟨evaluateE q f, ?_⟩
  rw [← evaluateE_precompose, hf]
  exact evaluateE_fromRightE q (exceptionalCycle q)

def regular_ext_two_class (h : NoPositivePowerOne q) :
    Ext (ModuleCat.of C (Simple q)) (ModuleCat.of C C) 2 :=
  (projectiveResolution q h).extMk (ModuleCat.ofHom (exceptionalHom q)) 3 rfl (by
    apply ModuleCat.hom_ext
    change (exceptionalHom q).comp (dEll q (q ^ 1)) = 0
    simpa only [pow_one] using exceptionalHom_cocycle q)

theorem regular_ext_two_class_ne_zero (h : NoPositivePowerOne q) (hq : q ≠ 0) :
    regular_ext_two_class q h ≠ 0 := by
  intro hz
  obtain ⟨f, hf⟩ := ((projectiveResolution q h).extMk_eq_zero_iff _ 3 rfl _ 1 rfl).mp hz
  apply exceptionalHom_not_boundary q hq (by simpa using h 1 (by decide))
  refine ⟨f.hom, ?_⟩
  have hh := congrArg ModuleCat.Hom.hom hf
  change f.hom.comp (dEll q (q ^ 0)) = exceptionalHom q at hh
  simpa only [pow_zero] using! hh

end ArExplicit.Resolution

end

end OAI
