import Mathlib
import OAI.Analysis.PathSelection.SectorPolynomials

namespace OAI

/-! Recursive clock monomials, leading terms and coefficient-field algebra. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex Metric
open scoped Asymptotics
namespace DegeneratingTrees.Clock

 

def ClockGerm : List (ℝ → ℝ) → (ℝ → ℂ) → Prop
  | [], f => Puiseux f
  | X::xs, f => ∃ (F : ℂ → ℂ) (E : Set ℝ) (b : ℝ → ℂ → ℂ),
      SectorExpansion F E b ∧
      (∀ β ∈ E, ClockGerm xs (fun t => b β (X t : ℂ)) ∧
        SectorEventually (fun z => AnalyticAt ℂ (b β) z)) ∧
      f =ᶠ[atTop] fun t => F (X t : ℂ)

 

def ValidClocks : List (ℝ → ℝ) → Prop
  | [] => True
  | X::xs => ValidClocks xs ∧ ClockGerm xs (fun t => (X t : ℂ)) ∧
      Tendsto X atTop atTop ∧
      match xs with
      | [] => ∃ c : ℝ, 0 < c ∧ X =ᶠ[atTop] fun t => c*t
      | Y::_ => Y =o[atTop] X

lemma ClockGerm.congr {xs : List (ℝ → ℝ)} {f g : ℝ → ℂ}
    (hf : ClockGerm xs f) (hfg : f =ᶠ[atTop] g) : ClockGerm xs g := by
  cases xs with
  | nil => exact Puiseux.congr hf hfg
  | cons X xs =>
    obtain ⟨F,E,b,hF,hb,he⟩ := hf
    exact ⟨F,E,b,hF,hb,hfg.symm.trans he⟩

lemma eventually_analytic_congr {f g : ℝ → ℂ}
    (hf : ∀ᶠ x : ℝ in atTop, AnalyticAt ℝ f x) (he : f =ᶠ[atTop] g) :
    ∀ᶠ x : ℝ in atTop, AnalyticAt ℝ g x := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp he
  filter_upwards [hf,eventually_gt_atTop T] with x hx hxT
  exact hx.congr ((eventually_gt_nhds hxT).mono (fun y hy => hT y hy.le))

 

theorem ClockGerm.eventually_analytic {xs : List (ℝ → ℝ)}
    (hxs : ValidClocks xs) {f : ℝ → ℂ} (hf : ClockGerm xs f) :
    ∀ᶠ t : ℝ in atTop, AnalyticAt ℝ f t := by
  induction xs generalizing f with
  | nil => exact Puiseux.eventually_analytic hf
  | cons X xs ih =>
    obtain ⟨hxs,hX,hXt,hrel⟩ := hxs
    have hXa := ih hxs hX
    obtain ⟨F,E,b,hF,hb,he⟩ := hf
    obtain ⟨ω,R,ε,C,hω,hε,hC,hFa,hbound⟩ := hF.remainders 0
    apply eventually_analytic_congr (g := f) _ he.symm
    filter_upwards [hXa,hXt.eventually (hω.real_discs R)] with t hXa ht
    have hFpoint := hFa (X t:ℂ) (ht.2 (mem_closedBall_self (by linarith [ht.1])))
    exact (hFpoint.restrictScalars (𝕜 := ℝ)).comp (f := fun t : ℝ => (X t:ℂ)) hXa

lemma ClockGerm.real_eventually_analytic {xs : List (ℝ → ℝ)}
    (hxs : ValidClocks xs) {f : ℝ → ℝ} (hf : ClockGerm xs (fun t => (f t:ℂ))) :
    ∀ᶠ t : ℝ in atTop, AnalyticAt ℝ f t := by
  filter_upwards [hf.eventually_analytic hxs] with t ht
  exact (Complex.reCLM.analyticAt _).comp ht

 

inductive LogMonomial : List (ℝ → ℝ) → (ℝ → ℝ) → Prop
  | base (p : ℚ) : LogMonomial [] (fun t => (p:ℝ)*Real.log t)
  | step {xs : List (ℝ → ℝ)} {M X : ℝ → ℝ} (h : LogMonomial xs M) (β : ℝ) :
      LogMonomial (X::xs) (fun t => β*X t+M t)

def RayLeading (xs : List (ℝ → ℝ)) (f : ℝ → ℂ) : Prop :=
  ∃ M : ℝ → ℝ, LogMonomial xs M ∧ ∃ C : ℂ, C ≠ 0 ∧
    Tendsto (fun t => (Real.exp (-M t):ℂ)*f t) atTop (𝓝 C)

 

lemma continuous_tail_surjective {X : ℝ → ℝ} (hX : Tendsto X atTop atTop)
    (hc : ∀ᶠ t : ℝ in atTop, ContinuousAt X t) (T : ℝ) :
    ∃ S : ℝ, ∀ y ≥ S, ∃ t ≥ T, X t=y := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp hc
  let a := max A T
  refine ⟨X a,?_⟩
  intro y hy
  obtain ⟨b,hb,hby⟩ := ((eventually_ge_atTop a).and (hX.eventually_ge_atTop y)).exists
  have hcont : ContinuousOn X (Icc a b) := fun t ht =>
    (hA t ((le_max_left _ _).trans ht.1)).continuousWithinAt
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc hb hcont ⟨hy,hby⟩
  exact ⟨t,(le_max_right _ _).trans ht.1,he⟩

lemma eventually_of_comp_clock {X : ℝ → ℝ} {P : ℝ → Prop}
    (hX : Tendsto X atTop atTop) (hc : ∀ᶠ t : ℝ in atTop, ContinuousAt X t)
    (hP : ∀ᶠ t : ℝ in atTop, P (X t)) : ∀ᶠ y : ℝ in atTop, P y := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp hP
  obtain ⟨S,hS⟩ := continuous_tail_surjective hX hc T
  filter_upwards [eventually_ge_atTop S] with y hy
  obtain ⟨t,ht,rfl⟩ := hS y hy
  exact hT t ht

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma ValidClocks.lower_small {X : ℝ → ℝ} {xs : List (ℝ → ℝ)}
    (h : ValidClocks (X::xs)) : Real.log =o[atTop] X ∧ ∀ Y ∈ xs, Y =o[atTop] X := by
  induction xs generalizing X with
  | nil =>
    obtain ⟨_,_,_,c,hc,he⟩ := h
    refine ⟨?_,by simp⟩
    exact (Asymptotics.IsLittleO.const_mul_right hc.ne' Real.isLittleO_log_id_atTop).congr'
      EventuallyEq.rfl he.symm
  | cons Y ys ih =>
    obtain ⟨hys,hX,hXt,hYX⟩ := h
    have hh := ih hys
    refine ⟨hh.1.trans hYX,?_⟩
    intro Z hZ
    rcases List.mem_cons.mp hZ with rfl | hZ
    · exact hYX
    · exact (hh.2 Z hZ).trans hYX

lemma LogMonomial.isLittleO {xs : List (ℝ → ℝ)} {M H : ℝ → ℝ}
    (hM : LogMonomial xs M) (hlog : Real.log =o[atTop] H)
    (hxs : ∀ X ∈ xs, X =o[atTop] H) : M =o[atTop] H := by
  induction hM with
  | base p => exact hlog.const_mul_left _
  | @step xs M X hM β ih =>
    exact ((hxs X (List.mem_cons_self)).const_mul_left β).add
      (ih (fun Y hY => hxs Y (List.mem_cons_of_mem _ hY)))

lemma LogMonomial.neg {xs : List (ℝ → ℝ)} {M : ℝ → ℝ}
    (hM : LogMonomial xs M) : LogMonomial xs (fun t => -M t) := by
  induction hM with
  | base p =>
    convert LogMonomial.base (-p) using 1
    funext t; push_cast; ring
  | @step xs M X hM β ih =>
    convert LogMonomial.step (X := X) ih (-β) using 1
    funext t; ring

lemma subexponential_exp_of_littleO {M X : ℝ → ℝ}
    (hX : Tendsto X atTop atTop) (hM : M =o[atTop] X) :
    Subexponential atTop X (fun t => (Real.exp (M t):ℂ)) := by
  intro ε hε
  filter_upwards [hM.bound hε,hX.eventually_gt_atTop 0] with t ht hXt
  rw [Complex.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  simp only [Real.norm_eq_abs,abs_of_pos hXt] at ht
  exact (le_abs_self _).trans ht

lemma subexponential_of_eventually_bounded {X : ℝ → ℝ} {f : ℝ → ℂ}
    (hX : Tendsto X atTop atTop) {C : ℝ} (hf : ∀ᶠ t in atTop, ‖f t‖ ≤ C) :
    Subexponential atTop X f := by
  intro ε hε
  have ht : Tendsto (fun t => Real.exp (ε*X t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_const_mul_atTop_of_pos hε).mpr hX)
  filter_upwards [hf,ht.eventually_ge_atTop C] with t ht hC
  exact ht.trans hC

lemma subexponential_congr {X : ℝ → ℝ} {f g : ℝ → ℂ}
    (hf : Subexponential atTop X f) (he : f =ᶠ[atTop] g) : Subexponential atTop X g := by
  intro ε hε
  filter_upwards [hf ε hε,he] with t ht he
  simpa only [←he] using ht

lemma RayLeading.inv {xs : List (ℝ → ℝ)} {f : ℝ → ℂ} (h : RayLeading xs f) :
    RayLeading xs (fun t => (f t)⁻¹) := by
  obtain ⟨M,hM,C,hC,ht⟩ := h
  refine ⟨fun t => -M t,hM.neg,C⁻¹,inv_ne_zero hC,?_⟩
  apply (ht.inv₀ hC).congr'
  exact Eventually.of_forall (fun t => by
    simp only [mul_inv_rev,←Complex.ofReal_inv,←Real.exp_neg,neg_neg,mul_comm])

lemma RayLeading.eventually_nonzero {xs : List (ℝ → ℝ)} {f : ℝ → ℂ}
    (h : RayLeading xs f) : ∀ᶠ t : ℝ in atTop, f t ≠ 0 := by
  obtain ⟨M,hM,C,hC,ht⟩ := h
  filter_upwards [ht.eventually_ne hC] with t ht
  exact (mul_ne_zero_iff.mp ht).2

lemma RayLeading.subexponential {xs : List (ℝ → ℝ)} {f : ℝ → ℂ} {X : ℝ → ℝ}
    (h : RayLeading xs f) (hX : Tendsto X atTop atTop)
    (hlog : Real.log =o[atTop] X) (hxs : ∀ Y ∈ xs, Y =o[atTop] X) :
    Subexponential atTop X f := by
  obtain ⟨M,hM,C,hC,ht⟩ := h
  have hMb := subexponential_exp_of_littleO hX (hM.isLittleO hlog hxs)
  have hb := subexponential_of_eventually_bounded hX
    ((ht.norm.eventually_lt_const (show ‖C‖ < ‖C‖+1 by linarith)).mono (fun _ h => h.le))
  apply subexponential_congr (hMb.mul hb)
  exact Eventually.of_forall (fun t => by
    dsimp only
    rw [←mul_assoc,←Complex.ofReal_mul,←Real.exp_add,add_neg_cancel]
    simp)

 
lemma RayLeading.eventually_sign {xs : List (ℝ → ℝ)} {f : ℝ → ℝ}
    (h : RayLeading xs (fun t => (f t:ℂ))) :
    (∀ᶠ t : ℝ in atTop, 0 < f t) ∨ (∀ᶠ t : ℝ in atTop, f t < 0) := by
  obtain ⟨M,hM,C,hC,ht⟩ := h
  have ht' : Tendsto (fun t => Real.exp (-M t)*f t) atTop (𝓝 C.re) := by
    simpa only [Function.comp_def,←Complex.ofReal_mul,Complex.ofReal_re] using
      Complex.continuous_re.continuousAt.tendsto.comp ht
  have hCi : C.im=0 := by
    have hi : Tendsto (fun _ : ℝ => (0:ℝ)) atTop (𝓝 C.im) := by
      simpa only [Function.comp_def,←Complex.ofReal_mul,Complex.ofReal_im] using
        Complex.continuous_im.continuousAt.tendsto.comp ht
    exact tendsto_nhds_unique hi tendsto_const_nhds
  have hCr : C.re ≠ 0 := fun hz => hC (Complex.ext hz hCi)
  rcases lt_or_gt_of_ne hCr with hn | hp
  · right
    filter_upwards [ht'.eventually_lt_const hn] with t ht
    exact neg_of_mul_neg_right ht (Real.exp_pos _).le
  · left
    filter_upwards [ht'.eventually_const_lt hp] with t ht
    exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp ht

lemma Puiseux.rayLeading {f : ℝ → ℂ} (hf : Puiseux f)
    (hne : ¬ f =ᶠ[atTop] 0) : RayLeading [] f := by
  obtain ⟨q,C,hC,ht⟩ := hf.leading hne
  refine ⟨fun t => (q:ℝ)*Real.log t,LogMonomial.base q,C,hC,?_⟩
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  rw [Real.rpow_def_of_pos ht,Real.exp_neg,Complex.ofReal_inv]
  congr 2
  rw [mul_comm]

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

 

theorem ClockGerm.leading_or_zero {xs : List (ℝ → ℝ)} (hxs : ValidClocks xs)
    {f : ℝ → ℂ} (hf : ClockGerm xs f) : f =ᶠ[atTop] 0 ∨ RayLeading xs f := by
  induction xs generalizing f with
  | nil =>
    by_cases hz : f =ᶠ[atTop] 0
    · exact Or.inl hz
    · exact Or.inr (Puiseux.rayLeading hf hz)
  | cons X xs ih =>
    have hsmall := hxs.lower_small
    obtain ⟨hxs,hX,hXt,hrel⟩ := hxs
    have hXcont := (hX.real_eventually_analytic hxs).mono (fun _ hx => hx.continuousAt)
    obtain ⟨F,E,b,hF,hb,he⟩ := hf
    have hcoeff : ∀ β ∈ E, (∀ᶠ x : ℝ in atTop, b β (x:ℂ)=0) ∨
        ((∀ᶠ x : ℝ in atTop, b β (x:ℂ) ≠ 0) ∧
        Subexponential atTop id (fun x : ℝ => (b β (x:ℂ))⁻¹)) := by
      intro β hβ
      rcases ih hxs (hb β hβ).1 with hz | hl
      · exact Or.inl (eventually_of_comp_clock hXt hXcont hz)
      · refine Or.inr ⟨eventually_of_comp_clock hXt hXcont hl.eventually_nonzero,?_⟩
        have hg := hl.inv.subexponential hXt hsmall.1 hsmall.2
        intro ε hε
        exact eventually_of_comp_clock hXt hXcont (hg ε hε)
    rcases hF.leading_or_zero_general (fun β hβ => (hb β hβ).2) hcoeff with
      hz | ⟨β,hβ,hbne,ht⟩
    · left
      filter_upwards [he,hXt.eventually hz] with t he hz
      exact he.trans hz
    · right
      have hbcompne := hXt.eventually hbne
      have hbnz : ¬ (fun t : ℝ => b β (X t:ℂ)) =ᶠ[atTop] 0 := by
        intro hz
        obtain ⟨t,ht,hz⟩ := (hbcompne.and hz).exists
        exact ht hz
      obtain ⟨M,hM,C,hC,htb⟩ := (ih hxs (hb β hβ).1).resolve_left hbnz
      refine ⟨fun t => β*X t+M t,LogMonomial.step hM β,C,hC,?_⟩
      have hp := (ht.comp hXt).mul htb
      simp only [one_mul] at hp
      apply hp.congr'
      filter_upwards [he,hbcompne] with t he hne
      dsimp [Function.comp_def]
      rw [he]
      calc
        ((Real.exp (-β*X t):ℂ)*(b β (X t:ℂ))⁻¹*F (X t:ℂ)) *
            ((Real.exp (-M t):ℂ)*b β (X t:ℂ)) =
            ((Real.exp (-β*X t):ℂ)*(Real.exp (-M t):ℂ)) *
              ((b β (X t:ℂ))⁻¹*b β (X t:ℂ))*F (X t:ℂ) := by ring
        _ = (Real.exp (-(β*X t+M t)):ℂ)*F (X t:ℂ) := by
          rw [inv_mul_cancel₀ hne,mul_one,←Complex.ofReal_mul,←Real.exp_add]
          congr 2; ring_nf

lemma ClockGerm.leading {xs : List (ℝ → ℝ)} (hxs : ValidClocks xs)
    {f : ℝ → ℂ} (hf : ClockGerm xs f) (hne : ¬ f =ᶠ[atTop] 0) : RayLeading xs f :=
  (hf.leading_or_zero hxs).resolve_left hne

lemma ClockGerm.eventually_nonzero {xs : List (ℝ → ℝ)} (hxs : ValidClocks xs)
    {f : ℝ → ℂ} (hf : ClockGerm xs f) (hne : ¬ f =ᶠ[atTop] 0) :
    ∀ᶠ t : ℝ in atTop, f t ≠ 0 := (hf.leading hxs hne).eventually_nonzero

 

theorem ClockGerm.eventually_sign {xs : List (ℝ → ℝ)} (hxs : ValidClocks xs)
    {f : ℝ → ℝ} (hf : ClockGerm xs (fun t => (f t:ℂ)))
    (hne : ¬ f =ᶠ[atTop] 0) :
    (∀ᶠ t : ℝ in atTop, 0 < f t) ∨ (∀ᶠ t : ℝ in atTop, f t < 0) := by
  apply (hf.leading hxs ?_).eventually_sign
  intro hz
  exact hne (hz.mono (fun _ hx => Complex.ofReal_eq_zero.mp hx))

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
attribute [local instance] Classical.propDecidable
namespace DegeneratingTrees.Clock

lemma ClockGerm.const (xs : List (ℝ → ℝ)) (c : ℂ) : ClockGerm xs (fun _ => c) := by
  induction xs with
  | nil => exact puiseux_const c
  | cons X xs ih =>
    exact ⟨fun _ => c,{0},fun _ _ => c,SectorExpansion.const c,
      fun _ _ => ⟨ih,SectorEventually.truth.mono (fun _ _ => analyticAt_const)⟩,
      Filter.EventuallyEq.rfl⟩

lemma ClockGerm.neg {xs : List (ℝ → ℝ)} {f : ℝ → ℂ} (hf : ClockGerm xs f) :
    ClockGerm xs (fun t => -f t) := by
  induction xs generalizing f with
  | nil => exact Puiseux.neg hf
  | cons X xs ih =>
    obtain ⟨F,E,b,hF,hb,he⟩ := hf
    refine ⟨fun z => -F z,E,fun β z => -b β z,hF.neg,?_,he.fun_comp Neg.neg⟩
    intro β hβ
    exact ⟨ih (hb β hβ).1,((hb β hβ).2).mono (fun _ hx => hx.neg)⟩

lemma ClockGerm.add {xs : List (ℝ → ℝ)} {f g : ℝ → ℂ}
    (hf : ClockGerm xs f) (hg : ClockGerm xs g) : ClockGerm xs (fun t => f t+g t) := by
  induction xs generalizing f g with
  | nil => exact Puiseux.add hf hg
  | cons X xs ih =>
    obtain ⟨F,E,b,hF,hb,he⟩ := hf
    obtain ⟨G,D,c,hG,hc,he'⟩ := hg
    refine ⟨fun z => F z+G z,E ∪ D,
      fun β z => (if β ∈ E then b β z else 0)+(if β ∈ D then c β z else 0),
      hF.add hG,?_,he.add he'⟩
    intro β _
    have h1 : ClockGerm xs (fun t => if β ∈ E then b β (X t:ℂ) else 0) ∧
        SectorEventually (fun z => AnalyticAt ℂ (fun w => if β ∈ E then b β w else 0) z) := by
      by_cases hβ : β ∈ E
      · simpa only [ite_eq_left hβ] using hb β hβ
      · simp only [ite_eq_right hβ]
        exact ⟨ClockGerm.const _ 0,SectorEventually.truth.mono (fun _ _ => analyticAt_const)⟩
    have h2 : ClockGerm xs (fun t => if β ∈ D then c β (X t:ℂ) else 0) ∧
        SectorEventually (fun z => AnalyticAt ℂ (fun w => if β ∈ D then c β w else 0) z) := by
      by_cases hβ : β ∈ D
      · simpa only [ite_eq_left hβ] using hc β hβ
      · simp only [ite_eq_right hβ]
        exact ⟨ClockGerm.const _ 0,SectorEventually.truth.mono (fun _ _ => analyticAt_const)⟩
    exact ⟨ih h1.1 h2.1,(h1.2.and h2.2).mono (fun _ hx => hx.1.add hx.2)⟩

lemma ClockGerm.sub {xs : List (ℝ → ℝ)} {f g : ℝ → ℂ}
    (hf : ClockGerm xs f) (hg : ClockGerm xs g) : ClockGerm xs (fun t => f t-g t) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma puiseux_of_comp_clock {X : ℝ → ℝ} {f : ℝ → ℂ}
    (hX : Puiseux (fun t => (X t:ℂ))) (hXt : Tendsto X atTop atTop)
    (hf : Puiseux (fun t => f (X t))) : Puiseux f := by
  obtain ⟨I,hI,hIt,hl,hr⟩ := hX.inverse_change hXt
  exact (hf.comp_unbounded hI hIt).congr (hl.mono (fun t ht => by simp [ht]))

lemma firstClock_expansion_iff {X : ℝ → ℝ} (hX : Puiseux (fun t => (X t:ℂ)))
    (hXt : Tendsto X atTop atTop) {f : ℝ → ℂ} :
    ClockGerm (X :: []) f ↔ ∃ F : ℂ → ℂ,ExpansionOver PuiseuxSector F ∧
      f =ᶠ[atTop] fun t => F (X t:ℂ) := by
  constructor
  · rintro ⟨F,E,b,hF,hb,he⟩
    refine ⟨F,⟨E,b,hF,?_⟩,he⟩
    intro β hβ
    exact ⟨(hb β hβ).2,puiseux_of_comp_clock hX hXt (hb β hβ).1⟩
  · rintro ⟨F,⟨E,b,hF,hb⟩,he⟩
    exact ⟨F,E,b,hF,fun β hβ => ⟨(hb β hβ).2.comp_unbounded hX hXt,(hb β hβ).1⟩,he⟩

lemma ClockGerm.first_mul {X : ℝ → ℝ} (hX : Puiseux (fun t => (X t:ℂ)))
    (hXt : Tendsto X atTop atTop) {f g : ℝ → ℂ}
    (hf : ClockGerm (X :: []) f) (hg : ClockGerm (X :: []) g) :
    ClockGerm (X :: []) (fun t => f t*g t) := by
  obtain ⟨F,hF,he⟩ := (firstClock_expansion_iff hX hXt).mp hf
  obtain ⟨G,hG,he'⟩ := (firstClock_expansion_iff hX hXt).mp hg
  exact (firstClock_expansion_iff hX hXt).mpr
    ⟨fun z => F z*G z,hF.mul puiseux_lowerSectorData hG,he.mul he'⟩

lemma ClockGerm.first_inv {X : ℝ → ℝ} (hX : Puiseux (fun t => (X t:ℂ)))
    (hXt : Tendsto X atTop atTop) {f : ℝ → ℂ}
    (hf : ClockGerm (X :: []) f) : ClockGerm (X :: []) (fun t => (f t)⁻¹) := by
  obtain ⟨F,hF,he⟩ := (firstClock_expansion_iff hX hXt).mp hf
  exact (firstClock_expansion_iff hX hXt).mpr
    ⟨fun z => (F z)⁻¹,hF.inv puiseux_lowerSectorData,he.inv⟩

end DegeneratingTrees.Clock
end

end OAI
