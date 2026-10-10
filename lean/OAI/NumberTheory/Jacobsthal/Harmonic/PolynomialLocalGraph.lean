import OAI.NumberTheory.Jacobsthal.Estimates.RegularImplicitArc
import OAI.NumberTheory.Jacobsthal.Partitions.NestedCoordinates

namespace OAI

namespace Erdos970

section

open Filter
open scoped Topology ContDiff
namespace ErdosDivisibleInflection

open ErdosImplicitCurvature

noncomputable def planeEval (Q : Bivariate) (p : ℝ × ℝ) : ℝ := peval Q p.1 p.2

theorem contDiff_planeEval (Q : Bivariate) (n : ℕ∞ω) : ContDiff ℝ n (planeEval Q) := by
  unfold planeEval
  induction Q using MvPolynomial.induction_on with
  | C c => simpa [planeEval] using (contDiff_const (c := c) : ContDiff ℝ n (fun _ : ℝ × ℝ => c))
  | add P Q hP hQ =>
      simpa only [planeEval, peval_add] using hP.add hQ
  | mul_X P i hP =>
      fin_cases i
      · simpa [peval] using hP.mul contDiff_fst
      · simpa [peval] using hP.mul contDiff_snd

theorem fderiv_planeEval_inr (Q : Bivariate) (x y : ℝ) :
    fderiv ℝ (planeEval Q) (x,y) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ =
      (1 : ℝ →L[ℝ] ℝ).smulRight (peval (partialY Q) x y) := by
  have hF := ((contDiff_planeEval Q 1).differentiable (by norm_num) (x,y)).hasFDerivAt
  have hp : HasFDerivAt (fun t : ℝ => (x,t)) (ContinuousLinearMap.inr ℝ ℝ ℝ) y := by
    have hlin : HasFDerivAt (ContinuousLinearMap.inr ℝ ℝ ℝ) (ContinuousLinearMap.inr ℝ ℝ ℝ) y :=
      (ContinuousLinearMap.inr ℝ ℝ ℝ).hasFDerivAt
    simpa using hlin.const_add (x,0)
  have hc := hF.comp y hp
  have hy : HasDerivAt (fun t => peval Q x t) (peval (partialY Q) x y) y := by
    simpa using hasDerivAt_peval Q (fun _ => x) id 0 1 y (hasDerivAt_const y x) (hasDerivAt_id y)
  exact hc.unique hy.hasFDerivAt

theorem scalar_map_invertible (b : ℝ) (hb : b ≠ 0) :
    ((1 : ℝ →L[ℝ] ℝ).smulRight b).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (1 : ℝ →L[ℝ] ℝ).smulRight b⁻¹)
  · ext
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul, hb]
  · ext
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul, hb]

end ErdosDivisibleInflection

end

section

open Set Filter
open scoped Topology
namespace ErdosLocalFiberGraphs
open ErdosImplicitCurvature ErdosDivisibleInflection ErdosCriticalGeometry

def boundedFiber (Q : Bivariate) (x L U : ℝ) : Set ℝ :=
  {y | y ∈ Icc L U ∧ peval Q x y = 0}

noncomputable def verticalPolynomial (Q : Bivariate) (x : ℝ) : Polynomial ℝ :=
  (nestedY ℝ Q).map (Polynomial.evalRingHom x)

theorem verticalPolynomial_eval (Q : Bivariate) (x y : ℝ) :
    (verticalPolynomial Q x).eval y = peval Q x y := by
  have hv : (fun i : Fin 2 => if i = 0 then x else y) = ![x,y] := by
    funext i
    fin_cases i <;> simp
  have h := eval_nestedY ℝ Q x y
  change (verticalPolynomial Q x).eval y = MvPolynomial.eval ![x,y] Q at h
  simpa only [peval,hv] using h

theorem boundedFiber_finite (Q : Bivariate) (x L U z : ℝ)
    (hz : peval Q x z ≠ 0) : (boundedFiber Q x L U).Finite := by
  have hp : verticalPolynomial Q x ≠ 0 := by
    intro he
    apply hz
    rw [← verticalPolynomial_eval, he, Polynomial.eval_zero]
  apply (Polynomial.finite_setOfPred_isRoot hp).subset
  intro y hy
  change (verticalPolynomial Q x).eval y = 0
  exact (verticalPolynomial_eval Q x y).trans hy.2

theorem boundedFiber_interior (Q : Bivariate) (x L U : ℝ)
    (hL : peval Q x L ≠ 0) (hU : peval Q x U ≠ 0) :
    boundedFiber Q x L U ⊆ Ioo L U := by
  intro y hy
  constructor
  · exact lt_of_le_of_ne hy.1.1 (fun he => hL (he ▸ hy.2))
  · exact lt_of_le_of_ne hy.1.2 (fun he => hU (he ▸ hy.2))

theorem compact_nonzero_eventually (Q : Bivariate) (x : ℝ) (K : Set ℝ)
    (hK : IsCompact K) (hne : ∀ y ∈ K, peval Q x y ≠ 0) :
    ∀ᶠ t in 𝓝 x, ∀ y ∈ K, peval Q t y ≠ 0 := by
  have ho : IsOpen {p : ℝ × ℝ | planeEval Q p ≠ 0} :=
    isOpen_ne.preimage (contDiff_planeEval Q 0).continuous
  obtain ⟨A,B,hA,_,hxA,hKB,hAB⟩ :=
    generalized_tube_lemma isCompact_singleton hK ho (by
      rintro ⟨t,y⟩ ⟨ht,hy⟩
      have ht' : t = x := ht
      subst t
      exact hne y hy)
  filter_upwards [hA.mem_nhds (hxA (mem_singleton x))] with t ht
  intro y hy
  exact hAB (a := (t,y)) ⟨ht,hKB hy⟩

end ErdosLocalFiberGraphs

end

section

open Filter
open scoped Topology ContDiff
namespace ErdosDivisibleInflection
open ErdosImplicitCurvature

theorem exists_local_real_graph (Q : Bivariate) (x y : ℝ)
    (hQ : peval Q x y = 0) (hQy : peval (partialY Q) x y ≠ 0) :
    ∃ (a b : ℝ) (f : ℝ → ℝ), a < x ∧ x < b ∧ f x = y ∧
      ContDiffOn ℝ 2 f (Set.Ioo a b) ∧
      (∀ t ∈ Set.Ioo a b, peval Q t (f t) = 0) ∧
      (∀ t ∈ Set.Ioo a b, peval (partialY Q) t (f t) ≠ 0) := by
  have hc : ContDiffAt ℝ 2 (planeEval Q) (x,y) := (contDiff_planeEval Q 2).contDiffAt
  have hi : (fderiv ℝ (planeEval Q) (x,y) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [fderiv_planeEval_inr]
    exact scalar_map_invertible _ hQy
  let f := hc.implicitFunction (by norm_num) hi
  have hfx : f x = y := hc.implicitFunction_apply_self (by norm_num) hi
  have hcf : ContDiffAt ℝ 2 f x := hc.contDiffAt_implicitFunction (by norm_num) hi
  have hcurve : ∀ᶠ t in 𝓝 x, peval Q t (f t) = 0 := by
    have h := hc.eventually_apply_implicitFunction (by norm_num) hi
    exact h.mono fun t ht => ht.trans hQ
  have hpair : ContinuousAt (fun t : ℝ => (t,f t)) x :=
    continuousAt_id.prodMk hcf.continuousAt
  have hplane : ContinuousAt (planeEval (partialY Q)) (x,f x) :=
    (contDiff_planeEval (partialY Q) 0).continuous.continuousAt
  have hcy : ContinuousAt (fun t => peval (partialY Q) t (f t)) x := by
    change ContinuousAt (planeEval (partialY Q) ∘ (fun t : ℝ => (t,f t))) x
    exact ContinuousAt.comp (f := fun t : ℝ => (t,f t)) hplane hpair
  have hny : ∀ᶠ t in 𝓝 x, peval (partialY Q) t (f t) ≠ 0 := by
    apply hcy.eventually_ne
    rwa [hfx]
  obtain ⟨U,hU,hfU⟩ := hcf.contDiffOn (m := 2) le_rfl (by norm_num)
  have hN : U ∩ {t | peval Q t (f t) = 0} ∩ {t | peval (partialY Q) t (f t) ≠ 0} ∈ 𝓝 x :=
    inter_mem (inter_mem hU hcurve) hny
  obtain ⟨eps,heps,hball⟩ := Metric.mem_nhds_iff.mp hN
  have hsub : Set.Ioo (x-eps) (x+eps) ⊆
      U ∩ {t | peval Q t (f t) = 0} ∩ {t | peval (partialY Q) t (f t) ≠ 0} := by
    simpa only [Real.ball_eq_Ioo] using hball
  refine ⟨x-eps,x+eps,f,by linarith,by linarith,hfx,hfU.mono ?_,?_,?_⟩
  · exact fun t ht => (hsub ht).1.1
  · exact fun t ht => (hsub ht).1.2
  · exact fun t ht => (hsub ht).2

end ErdosDivisibleInflection

end

end Erdos970

end OAI
