import Mathlib
import OAI.Analysis.SymmetricDomains.HorizontalGraphComplexification
import OAI.Analysis.SymmetricDomains.SquarefreeRelationOffDenominator

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Polynomial

theorem polynomial_gcd_specialization_data
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (p q : R[X]) :
    ∃ a b c : R, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
      ∃ A B C' U V : R[X],
        C a*p = A*B ∧ C b*q = A*C' ∧ C c*A = p*U+q*V := by
  classical
  let e := algebraMap R K
  have hi : Function.Injective (Polynomial.map e) :=
    Polynomial.map_injective e (IsFractionRing.injective R K)
  let g := EuclideanDomain.gcd (p.map e) (q.map e)
  obtain ⟨w,hw⟩ := EuclideanDomain.gcd_dvd_left (p.map e) (q.map e)
  obtain ⟨j,hj⟩ := EuclideanDomain.gcd_dvd_right (p.map e) (q.map e)
  change p.map e = g*w at hw
  change q.map e = g*j at hj
  obtain ⟨a,ha,A,hA⟩ := polynomial_clear_denominators (R := R) g
  obtain ⟨b,hb,B,hB⟩ := polynomial_clear_denominators (R := R) w
  obtain ⟨c,hc,C',hC⟩ := polynomial_clear_denominators (R := R) j
  obtain ⟨u,hu,U,hU⟩ := polynomial_clear_denominators (R := R)
    (EuclideanDomain.gcdA (p.map e) (q.map e))
  obtain ⟨v,hv,V,hV⟩ := polynomial_clear_denominators (R := R)
    (EuclideanDomain.gcdB (p.map e) (q.map e))
  refine ⟨a*b,a*c,u*v,mul_ne_zero ha hb,mul_ne_zero ha hc,mul_ne_zero hu hv,
    A,B,C',C (a*v)*U,C (a*u)*V,?_,?_,?_⟩
  · apply hi
    simp only [Polynomial.map_mul,Polynomial.map_C,map_mul]
    rw [hA,hB,hw]
    dsimp only [e]
    ring
  · apply hi
    simp only [Polynomial.map_mul,Polynomial.map_C,map_mul]
    rw [hA,hC,hj]
    dsimp only [e]
    ring
  · apply hi
    simp only [Polynomial.map_mul,Polynomial.map_C,map_mul,Polynomial.map_add]
    rw [hA,hU,hV]
    dsimp only [g,e]
    rw [EuclideanDomain.gcd_eq_gcd_ab]
    ring

end

theorem real_analytic_local_inverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {a : E} (hf : AnalyticAt ℝ f a)
    (i : E ≃L[ℝ] F) (hi : HasFDerivAt f (i : E →L[ℝ] F) a) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ a ∈ e.source ∧
      AnalyticAt ℝ e.symm (f a) := by
  have hs : HasStrictFDerivAt f (i : E →L[ℝ] F) a := by
    simpa only [hi.fderiv] using hf.hasStrictFDerivAt
  let e := hs.toOpenPartialHomeomorph f
  refine ⟨e, hs.toOpenPartialHomeomorph_coe, hs.mem_toOpenPartialHomeomorph_source, ?_⟩
  obtain ⟨p, hp⟩ := hf
  have he : (e : E → F) = f := hs.toOpenPartialHomeomorph_coe
  have hpe : HasFPowerSeriesAt e p a := he ▸ hp
  have hcoeff : p 1 = (continuousMultilinearCurryFin1 ℝ E F).symm
      (i : E →L[ℝ] F) := by
    apply (continuousMultilinearCurryFin1 ℝ E F).injective
    simpa using hp.hasFDerivAt.unique hi
  simpa only [he] using
    (e.hasFPowerSeriesAt_symm hs.mem_toOpenPartialHomeomorph_source hpe hcoeff).analyticAt

noncomputable def real_triangularDifferentialEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E × ℝ →L[ℝ] ℝ) (ha : L (0, 1) ≠ 0) : (E × ℝ) ≃L[ℝ] (E × ℝ) := by
  let A := ContinuousLinearMap.fst ℝ E ℝ
  let B := ContinuousLinearMap.snd ℝ E ℝ
  let C := L.comp ((ContinuousLinearMap.inl ℝ E ℝ).comp A)
  let inv := A.prod ((L (0, 1))⁻¹ • (B - C))
  have hL : ∀ (u : E) (v : ℝ), L (u, v) = L (u, 0) + v * L (0, 1) := by
    intro u v
    have h : (u, v) = (u, 0) + v • (0, (1 : ℝ)) := by simp
    rw [h, map_add, map_smul]
    simp
  refine ContinuousLinearEquiv.equivOfInverse (A.prod L) inv ?_ ?_
  · intro p
    ext
    · rfl
    · change (L (0, 1))⁻¹ * (L (p.1, p.2) - L (p.1, 0)) = p.2
      rw [hL p.1 p.2]
      field_simp [ha]
      ring
  · intro p
    ext
    · rfl
    · change L (p.1, (L (0, 1))⁻¹ * (p.2 - L (p.1, 0))) = p.2
      rw [hL]
      field_simp [ha]
      ring

@[simp] theorem real_triangularDifferentialEquiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E × ℝ →L[ℝ] ℝ) (ha : L (0, 1) ≠ 0) (p : E × ℝ) :
    real_triangularDifferentialEquiv L ha p = (p.1, L p) := rfl

theorem real_analytic_implicit_scalar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E × ℝ → ℝ} {a : E} {b : ℝ}
    (hF : AnalyticAt ℝ F (a, b)) (hzero : F (a, b) = 0)
    (L : E × ℝ →L[ℝ] ℝ) (hL : HasFDerivAt F L (a, b))
    (hsimple : L (0, 1) ≠ 0) :
    ∃ g : E → ℝ, AnalyticAt ℝ g a ∧ g a = b ∧
      (∀ᶠ y in 𝓝 a, F (y, g y) = 0) ∧
      (∀ᶠ p in 𝓝 (a, b), F p = 0 → p.2 = g p.1) := by
  let G : E × ℝ → E × ℝ := fun p => (p.1, F p)
  have hG : AnalyticAt ℝ G (a, b) :=
    ((ContinuousLinearMap.fst ℝ E ℝ).analyticAt (a, b)).prod hF
  have hdG : HasFDerivAt G (real_triangularDifferentialEquiv L hsimple : _ →L[ℝ] _) (a, b) :=
    hasFDerivAt_fst.prodMk hL
  obtain ⟨e, he, hmem, hia⟩ := real_analytic_local_inverse hG
    (real_triangularDifferentialEquiv L hsimple) hdG
  have hGab : G (a, b) = (a, 0) := by simp [G, hzero]
  rw [hGab] at hia
  let g : E → ℝ := fun y => (e.symm (y, 0)).2
  have hiac : AnalyticAt ℝ (fun y : E => e.symm (y, 0)) a :=
    hia.comp (f := fun y : E => (y, 0))
      ((ContinuousLinearMap.inl ℝ E ℝ).analyticAt a)
  have hg : AnalyticAt ℝ g a :=
    ((ContinuousLinearMap.snd ℝ E ℝ).analyticAt _).comp hiac
  have hsource : e.symm (a, 0) = (a, b) := by
    rw [← hGab, ← he]
    exact e.left_inv hmem
  refine ⟨g, hg, congrArg Prod.snd hsource, ?_, ?_⟩
  · have hright := e.eventually_right_inverse' hmem
    rw [he, hGab] at hright
    have ht : Tendsto (fun y : E => (y, (0 : ℝ))) (𝓝 a) (𝓝 (a, 0)) :=
      (continuous_id.prodMk continuous_const).continuousAt.tendsto
    filter_upwards [ht.eventually hright] with y hy
    have hfst : (e.symm (y, 0)).1 = y := congrArg Prod.fst hy
    have hsnd : F (e.symm (y, 0)) = 0 := congrArg Prod.snd hy
    change F (y, (e.symm (y, 0)).2) = 0
    have hpair : (y, (e.symm (y, 0)).2) = e.symm (y, 0) :=
      Prod.ext hfst.symm rfl
    rw [hpair]
    exact hsnd
  · have hleft := e.eventually_left_inverse hmem
    rw [he] at hleft
    filter_upwards [hleft] with p hp hz
    have hGp : G p = (p.1, 0) := by simp [G, hz]
    rw [hGp] at hp
    exact (congrArg Prod.snd hp).symm

theorem real_polynomial_analytic_root {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℝ)) (a : Fin d → ℝ) (b : ℝ)
    (hroot : Polynomial.eval₂ (MvPolynomial.eval a) b P = 0)
    (hsimple : Polynomial.eval₂ (MvPolynomial.eval a) b P.derivative ≠ 0) :
    ∃ g : (Fin d → ℝ) → ℝ, AnalyticAt ℝ g a ∧ g a = b ∧
      (∀ᶠ y in 𝓝 a, Polynomial.eval₂ (MvPolynomial.eval y) (g y) P = 0) ∧
      (∀ᶠ p in 𝓝 (a, b), Polynomial.eval₂ (MvPolynomial.eval p.1) p.2 P = 0 →
        p.2 = g p.1) := by
  let F : ((Fin d → ℝ) × ℝ) → ℝ := fun p =>
    Polynomial.eval₂ (MvPolynomial.eval p.1) p.2 P
  have hF : AnalyticAt ℝ F (a, b) := by
    have hpoly : ∀ j : ℕ, AnalyticAt ℝ
        (fun p : ((Fin d → ℝ) × ℝ) => MvPolynomial.eval p.1 (P.coeff j)) (a, b) := by
      intro j
      exact (AnalyticOnNhd.eval_mvPolynomial (P.coeff j) _ (Set.mem_univ _)).comp
        ((ContinuousLinearMap.fst ℝ (Fin d → ℝ) ℝ).analyticAt _)
    simp only [F, Polynomial.eval₂_eq_sum_range]
    exact
      Finset.analyticAt_fun_sum (Finset.range (P.natDegree + 1)) (fun j _ =>
        (hpoly j).mul (((ContinuousLinearMap.snd ℝ (Fin d → ℝ) ℝ).analyticAt _).pow j))
  let L := fderiv ℝ F (a,b)
  have hL : HasFDerivAt F L (a,b) := hF.differentiableAt.hasFDerivAt
  have hv : L (0,1) = Polynomial.eval₂ (MvPolynomial.eval a) b P.derivative := by
    have h1 : HasDerivAt (fun z => F (a,z)) (L (0,1)) b :=
      hL.comp_hasDerivAt b ((hasDerivAt_const b a).prodMk (hasDerivAt_id b))
    have h2 := (P.map (MvPolynomial.eval a)).hasDerivAt b
    simp only [Polynomial.derivative_map, Polynomial.eval_map] at h2
    exact h1.unique h2
  exact real_analytic_implicit_scalar hF hroot L hL (hv ▸ hsimple)

end Release061

end

end OAI
