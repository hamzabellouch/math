import Mathlib

namespace OAI

/-! Polynomial Specialization. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold BigOperators
namespace PolynomialSpecialization
open MvPolynomial

lemma eval_analyticAt {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℂ) (x : σ → ℂ) :
    AnalyticAt ℂ (fun y => eval y p) x := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [eval_C] using (analyticAt_const (v := c) (x := x))
  | add p q hp hq =>
      have he : (fun y => eval y (p+q))=((fun y => eval y p)+(fun y => eval y q)) := by
        funext y
        exact eval_add
      rw [he]
      exact hp.add hq
  | mul_X p i hp =>
      have he : (fun y => eval y (p*X i))=((fun y => eval y p)*(fun y => y i)) := by
        funext y
        simp only [eval_mul,eval_X,Pi.mul_apply]
      rw [he]
      exact hp.mul ((ContinuousLinearMap.proj i : (σ → ℂ) →L[ℂ] ℂ).analyticAt x)

lemma eq_zero_of_zero_on_open {σ : Type*} [Fintype σ]
    (p : MvPolynomial σ ℂ) {U : Set (σ → ℂ)} (hU : IsOpen U) (hne : U.Nonempty)
    (hp : ∀a∈U,eval a p=0) : p=0 := by
  obtain ⟨a,ha⟩ := hne
  have hz : (fun y => eval y p) =ᶠ[𝓝 a] 0 := by
    filter_upwards [hU.mem_nhds ha] with y hy
    exact hp y hy
  have he := (show AnalyticOnNhd ℂ (fun y => eval y p) univ from
    fun y _ => eval_analyticAt p y).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ a) hz
  apply MvPolynomial.funext
  intro y
  simpa using he (mem_univ y)

lemma exists_simultaneously_nonzero {σ ι : Type*} [Fintype σ] [Fintype ι]
    (p : ι → MvPolynomial σ ℂ) (hp : ∀i,p i≠0)
    {U : Set (σ → ℂ)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃a∈U,∀i,eval a (p i)≠0 := by
  classical
  by_contra! h
  have he : (∏i,p i)=0 := eq_zero_of_zero_on_open _ hU hne (by
    intro a ha
    obtain ⟨i,hi⟩ := h a ha
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi)
  exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) he

 

theorem generic_specialization {σ ι : Type*} [Fintype σ] [Fintype ι]
    (p : ι → MvPolynomial (Option σ) ℂ) (hp : ∀i,p i≠0)
    {U : Set (σ → ℂ)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃a∈U,∀i,Polynomial.map (eval a) (optionEquivLeft ℂ σ (p i))≠0 := by
  classical
  have hc : ∀i,∃n,(optionEquivLeft ℂ σ (p i)).coeff n≠0 := by
    intro i
    by_contra! h
    apply hp i
    apply (optionEquivLeft ℂ σ).injective
    rw [map_zero]
    exact Polynomial.ext (by simpa using h)
  choose n hn using hc
  obtain ⟨a,ha,h⟩ := exists_simultaneously_nonzero
    (fun i => (optionEquivLeft ℂ σ (p i)).coeff (n i)) hn hU hne
  refine ⟨a,ha,fun i he => h i ?_⟩
  have hec := congrArg (fun q : Polynomial ℂ => q.coeff (n i)) he
  simpa only [Polynomial.coeff_map,Polynomial.coeff_zero] using hec

 

theorem finite_fiber {ι B : Type*} [Fintype ι]
    (T : Set B) (f : B → ι → ℂ) (hf : Set.InjOn f T)
    (p : ι → Polynomial ℂ) (hp : ∀i,p i≠0)
    (hroot : ∀b∈T,∀i,(p i).IsRoot (f b i)) : T.Finite := by
  let R (i : ι) := {c : ℂ // (p i).IsRoot c}
  let : ∀i,Finite (R i) := fun i => (Polynomial.finite_setOfPred_isRoot (hp i)).to_subtype
  let g : T → ∀i,R i := fun b i => ⟨f b.val i,hroot b.val b.property i⟩
  have hg : Function.Injective g := by
    intro a b he
    apply Subtype.ext
    apply hf a.property b.property
    funext i
    exact congrArg Subtype.val (congrFun he i)
  let : Finite T := Finite.of_injective g hg
  exact Set.toFinite T

end PolynomialSpecialization

end

end OAI
