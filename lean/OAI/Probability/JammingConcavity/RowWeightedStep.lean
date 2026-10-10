import Mathlib
import OAI.Probability.JammingConcavity.RowSmoothApproxFinite

namespace OAI

/-! Row Weighted Step. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
open Classical
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
open scoped NNReal BigOperators
open MeasureTheory Metric Set
open Metric
open scoped RealInnerProductSpace
open Filter
open Finset Set
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open scoped BigOperators Classical
open scoped ENNReal NNReal Topology BigOperators Matrix MatrixOrder
open scoped BigOperators RealInnerProductSpace
open scoped NNReal Topology BigOperators
open scoped NNReal BigOperators RealInnerProductSpace
open scoped ENNReal NNReal BigOperators MatrixOrder
open scoped MatrixOrder
open scoped NNReal
open scoped BigOperators NNReal
open scoped NNReal ENNReal BigOperators Topology
open scoped Topology ENNReal NNReal
open scoped Matrix.Norms.L2Operator MatrixOrder Topology NNReal ENNReal BigOperators
open scoped Topology ENNReal NNReal BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped Topology NNReal ENNReal BigOperators
open scoped BigOperators NNReal Topology
open scoped Topology NNReal ENNReal BigOperators MatrixOrder
open scoped Topology NNReal ENNReal BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators NNReal
open Set Filter
open scoped Topology

namespace MicroscopicJamming
lemma row_step_weighted_terminal {u v : ℝ → ℝ} {A B C κ Av Bv Cv κv Q L ε : ℝ}
    (hQ : 0 < Q) (hu : RowAnalyticTerminal u A B C κ Q)
    (hv : RowAnalyticTerminal v Av Bv Cv κv Q) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    {rs : List (ℝ × ℝ)} (hrs : ∀ r ∈ rs,0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (hT : gaussianStepTime rs=Q)
    (hgu : ∀ t ∈ Set.Icc 0 Q,∀ x,|deriv (gaussianStepPath rs u t) x| ≤ L*(1+|x|))
    (hgv : ∀ t ∈ Set.Icc 0 Q,∀ x,|deriv (gaussianStepPath rs v t) x| ≤ L*(1+|x|))
    (hterm : ∀ x, |u x-v x| ≤ ε*(1+x^2)^2) :
    |gaussianRowComposition rs u 0-gaussianRowComposition rs v 0| ≤ ε*Real.exp ((10+8*L)*Q) := by
  obtain ⟨D,J,hD,hJ,hpath⟩ := gaussian_step_path A B C κ Q hQ hu.2.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2.1
  obtain ⟨E,K,hE,hK,hpathv⟩ := gaussian_step_path Av Bv Cv κv Q hQ hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2.1
  obtain ⟨_,htu,htimeu,hspaceu⟩ := hpath u hu rs hrs hT.le
  obtain ⟨_,htv,htimev,hspacev⟩ := hpathv v hv rs hrs hT.le
  have hxu (t : ℝ) (ht : t ∈ Set.Icc 0 Q) := hspaceu t ht.1 (hT ▸ ht.2)
  have hxv (t : ℝ) (ht : t ∈ Set.Icc 0 Q) := hspacev t ht.1 (hT ▸ ht.2)
  have hcu := gaussianStepPath_jointly_continuous hD hJ hT htimeu
    (fun t ht htR => ⟨(hspaceu t ht htR).1,fun x => ((hspaceu t ht htR).2.2 x).1⟩)
  have hcv := gaussianStepPath_jointly_continuous hE hK hT htimev
    (fun t ht htR => ⟨(hspacev t ht htR).1,fun x => ((hspacev t ht htR).2.2 x).1⟩)
  let W := |B|+A*(1+Q)+(|Bv|+Av*(1+Q))
  have hWu : 0 ≤ |B|+A*(1+Q) := by have := hu.2.1; positivity
  have hWv : 0 ≤ |Bv|+Av*(1+Q) := by have := hv.2.1; positivity
  have hW : 0 ≤ W := add_nonneg hWu hWv
  have hbu (t : ℝ) (ht : t ∈ Set.Icc 0 Q) (x : ℝ) : |gaussianStepPath rs u t x| ≤ W*(1+x^2) :=
    (gaussianStepPath_global_value_bound hQ hu hrs hT ht x).trans (mul_le_mul_of_nonneg_right (by dsimp [W]; linarith) (by positivity))
  have hbv (t : ℝ) (ht : t ∈ Set.Icc 0 Q) (x : ℝ) : |gaussianStepPath rs v t x| ≤ W*(1+x^2) :=
    (gaussianStepPath_global_value_bound hQ hv hrs hT ht x).trans (mul_le_mul_of_nonneg_right (by dsimp [W]; linarith) (by positivity))
  have hh := row_weighted_terminal_bound hQ hW hL hε hcu hcv
    (fun t ht => ⟨(hxu t ht).1,(hxu t ht).2.1⟩) (fun t ht => ⟨(hxv t ht).1,(hxv t ht).2.1⟩)
    (fun t ht x => gaussianStepPath_right_pde hQ hu hrs hT.le (hT ▸ ht) x)
    (fun t ht x => gaussianStepPath_right_pde hQ hv hrs hT.le (hT ▸ ht) x)
    (fun t _ => gaussianStepRightCoefficient_bounds hrs t) hbu hbv hgu hgv
    (fun x => by simpa only [hT] using (by rw [htu x,htv x]; exact hterm x :
      |gaussianStepPath rs u (gaussianStepTime rs) x-gaussianStepPath rs v (gaussianStepTime rs) x| ≤ ε*(1+x^2)^2))
  simpa only [gaussianStepPath_zero (fun r hr => (hrs r hr).2.2)] using hh

lemma row_composition_weighted_Lipschitz {u v : ℝ → ℝ} {A B C κ Av Bv Cv κv Q L H Hv ε : ℝ}
    (hQ : 0 < Q) (hu : RowAnalyticTerminal u A B C κ Q)
    (hv : RowAnalyticTerminal v Av Bv Cv κv Q) (hub : RowBoundedTerminal u L H)
    (hvb : RowBoundedTerminal v L Hv) (hε : 0 ≤ ε)
    {rs : List (ℝ × ℝ)} (hrs : ∀ r ∈ rs,0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (hT : gaussianStepTime rs=Q) (hterm : ∀ x, |u x-v x| ≤ ε*(1+x^2)^2) :
    |gaussianRowComposition rs u 0-gaussianRowComposition rs v 0| ≤ ε*Real.exp ((10+8*L)*Q) := by
  apply row_step_weighted_terminal hQ hu hv hub.L_nonneg hε hrs hT _ _ hterm
  · intro t ht x
    obtain ⟨K,hK⟩ := rowBoundedComposition_terminal hub (gaussianStepRemainder rs t)
      (gaussianStepRemainder_valid hrs ht.1).1
    exact (hK.slope x).trans (by nlinarith [mul_nonneg hub.L_nonneg (abs_nonneg x)])
  · intro t ht x
    obtain ⟨K,hK⟩ := rowBoundedComposition_terminal hvb (gaussianStepRemainder rs t)
      (gaussianStepRemainder_valid hrs ht.1).1
    exact (hK.slope x).trans (by nlinarith [mul_nonneg hvb.L_nonneg (abs_nonneg x)])
end MicroscopicJamming

 
open Set Filter MeasureTheory
open scoped Topology

namespace MicroscopicJamming
abbrev rowConv (φ u : ℝ → ℝ) : ℝ → ℝ := convolution φ u (.mul ℝ ℝ) volume
lemma rowConv_integrable {φ u : ℝ → ℝ} (hφ : Continuous φ) (hs : HasCompactSupport φ)
    (hu : Continuous u) (x : ℝ) : Integrable (fun y => φ y*u (x-y)) :=
  hs.convolutionExists_left_of_continuous_right (.mul ℝ ℝ) hφ.locallyIntegrable hu x
lemma row_iterated_smooth {φ : ℝ → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (n : ℕ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (iteratedDeriv n φ) := by
  induction n with
  | zero => simpa using hφ
  | succ n ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2
lemma row_iterated_compact {φ : ℝ → ℝ} (hs : HasCompactSupport φ) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n φ) := by
  induction n with
  | zero => simpa using hs
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv
lemma rowConv_deriv {φ u : ℝ → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    (hs : HasCompactSupport φ) (hu : Continuous u) : deriv (rowConv φ u)=rowConv (deriv φ) u := by
  funext x
  exact (hs.hasDerivAt_convolution_left (.mul ℝ ℝ) (hφ.of_le (by simp)) hu.locallyIntegrable x).deriv
lemma rowConv_iterated {φ u : ℝ → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    (hs : HasCompactSupport φ) (hu : Continuous u) (n : ℕ) :
    iteratedDeriv n (rowConv φ u)=rowConv (iteratedDeriv n φ) u := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iteratedDeriv_succ,ih,rowConv_deriv (row_iterated_smooth hφ n) (row_iterated_compact hs n) hu,←iteratedDeriv_succ]
lemma row_integral_deriv_zero {φ : ℝ → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    (hs : HasCompactSupport φ) : (∫ x, deriv φ x)=0 := by
  have he : rowConv φ (fun _ => (1:ℝ))=fun _ => ∫ x,φ x := by
    funext x; simp [rowConv,convolution_def]
  have hd := congrFun (rowConv_deriv (u:=fun _ => (1:ℝ)) hφ hs continuous_const) 0
  rw [he] at hd
  simpa [rowConv,convolution_def] using hd.symm
lemma row_integral_iterated_zero {φ : ℝ → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    (hs : HasCompactSupport φ) {n : ℕ} (hn : 1 ≤ n) : (∫ x,iteratedDeriv n φ x)=0 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  rw [iteratedDeriv_succ]
  exact row_integral_deriv_zero (row_iterated_smooth hφ k) (row_iterated_compact hs k)
lemma rowConv_iterated_bound {φ u : ℝ → ℝ} {L : ℝ}
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (hs : HasCompactSupport φ) (hu : Continuous u)
    (_hL : 0 ≤ L) (hlip : ∀ x y, |u x-u y| ≤ L*|x-y|) {n : ℕ} (hn : 1 ≤ n) :
    ∃ K : ℝ, ∀ x, |iteratedDeriv n (rowConv φ u) x| ≤ K := by
  let ψ := iteratedDeriv n φ
  have hcψ : Continuous ψ := (row_iterated_smooth hφ n).continuous
  have hsψ : HasCompactSupport ψ := row_iterated_compact hs n
  have hiψ : Integrable ψ := hcψ.integrable_of_hasCompactSupport hsψ
  have him : Integrable (fun y => |ψ y| *|y|) :=
    (hcψ.abs.mul continuous_abs).integrable_of_hasCompactSupport (hsψ.abs.mul_right)
  refine ⟨L*(∫ y, |ψ y| *|y|),fun x => ?_⟩
  rw [rowConv_iterated hφ hs hu n]
  have hi := rowConv_integrable hcψ hsψ hu x
  have he : rowConv ψ u x=∫ y,ψ y*(u (x-y)-u x) := by
    simp only [rowConv,convolution_def,ContinuousLinearMap.mul_apply']
    rw [show (fun y => ψ y*(u (x-y)-u x))=(fun y => ψ y*u (x-y)-ψ y*u x) by funext y; ring,
      integral_sub hi (hiψ.mul_const (u x)),integral_mul_const,row_integral_iterated_zero hφ hs hn]
    simp
  rw [he]
  calc
    _ ≤ ∫ y, |ψ y*(u (x-y)-u x)| := abs_integral_le_integral_abs
    _ ≤ ∫ y,L*(|ψ y| *|y|) := integral_mono_of_nonneg (Eventually.of_forall (by intro y; positivity)) (him.const_mul L)
      (Eventually.of_forall (fun y => by
        dsimp only
        rw [abs_mul]
        have hh := hlip (x-y) x
        simp only [sub_sub_cancel_left,abs_neg] at hh
        nlinarith [mul_le_mul_of_nonneg_left hh (abs_nonneg (ψ y))]))
    _ = _ := integral_const_mul _ _
end MicroscopicJamming

 
open Set Filter MeasureTheory
open scoped Topology

namespace MicroscopicJamming
lemma rowReal_Lipschitz {u : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ x y, |u x-u y| ≤ L*|x-y|) : LipschitzWith ⟨L,hL⟩ u := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |u x-u y| ≤ L*|x-y|
  exact h x y
lemma rowConv_lipschitz {φ u : ℝ → ℝ} {L : ℝ} (hφ : Continuous φ) (hs : HasCompactSupport φ)
    (hn : ∀ x, 0 ≤ φ x) (h1 : (∫ x,φ x)=1) (hu : Continuous u)
    (hlip : ∀ x y, |u x-u y| ≤ L*|x-y|) : ∀ x y, |rowConv φ u x-rowConv φ u y| ≤ L*|x-y| := by
  intro x y
  have hi : Integrable φ := hφ.integrable_of_hasCompactSupport hs
  change |(∫ z,φ z*u (x-z))-(∫ z,φ z*u (y-z))| ≤ _
  rw [←integral_sub (rowConv_integrable hφ hs hu x) (rowConv_integrable hφ hs hu y)]
  calc
    _ ≤ ∫ z,|φ z*u (x-z)-φ z*u (y-z)| := abs_integral_le_integral_abs
    _ ≤ ∫ z,φ z*(L*|x-y|) := integral_mono_of_nonneg (Eventually.of_forall (fun _ => abs_nonneg _))
      (hi.mul_const _) (Eventually.of_forall (fun z => by
        dsimp only
        rw [←mul_sub,abs_mul,abs_of_nonneg (hn z)]
        have hh := hlip (x-z) (y-z)
        simp only [sub_sub_sub_cancel_right] at hh
        exact mul_le_mul_of_nonneg_left hh (hn z)))
    _ = _ := by rw [integral_mul_const,h1,one_mul]
lemma rowConv_concave {φ u : ℝ → ℝ} (hφ : Continuous φ) (hs : HasCompactSupport φ)
    (hn : ∀ x, 0 ≤ φ x) (hu : Continuous u) (hc : ConcaveOn ℝ univ u) :
    ConcaveOn ℝ univ (rowConv φ u) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  change a*(∫ z,φ z*u (x-z))+b*(∫ z,φ z*u (y-z)) ≤ ∫ z,φ z*u (a*x+b*y-z)
  rw [←integral_const_mul,←integral_const_mul,←integral_add
    ((rowConv_integrable hφ hs hu x).const_mul a) ((rowConv_integrable hφ hs hu y).const_mul b)]
  apply integral_mono ((rowConv_integrable hφ hs hu x).const_mul a |>.add ((rowConv_integrable hφ hs hu y).const_mul b)) (rowConv_integrable hφ hs hu _)
  intro z
  have hh := hc.2 (mem_univ (x-z)) (mem_univ (y-z)) ha hb hab
  simp only [smul_eq_mul] at hh
  have he : a*(x-z)+b*(y-z)=a*x+b*y-z := by calc
    _ = a*x+b*y-(a+b)*z := by ring
    _ = _ := by rw [hab]; ring
  rw [he] at hh
  dsimp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left hh (hn z)]
lemma rowConv_upper {φ u : ℝ → ℝ} {B : ℝ} (hφ : Continuous φ) (hs : HasCompactSupport φ)
    (hn : ∀ x, 0 ≤ φ x) (h1 : (∫ x,φ x)=1) (hu : Continuous u) (hb : ∀ x,u x ≤ B) (x : ℝ) :
    rowConv φ u x ≤ B := by
  have hi : Integrable φ := hφ.integrable_of_hasCompactSupport hs
  calc
    _ ≤ ∫ z,φ z*B := integral_mono (rowConv_integrable hφ hs hu x) (hi.mul_const B)
      (fun z => mul_le_mul_of_nonneg_left (hb _) (hn z))
    _ = B := by rw [integral_mul_const,h1,one_mul]
lemma rowConv_approx {φ u : ℝ → ℝ} {L δ : ℝ} (hφ : Continuous φ) (hs : HasCompactSupport φ)
    (hn : ∀ x, 0 ≤ φ x) (h1 : (∫ x,φ x)=1) (hu : Continuous u) (hL : 0 ≤ L)
    (hr : ∀ x, φ x≠0 → |x| ≤ δ) (hlip : ∀ x y, |u x-u y| ≤ L*|x-y|) (x : ℝ) :
    |rowConv φ u x-u x| ≤ L*δ := by
  have hi : Integrable φ := hφ.integrable_of_hasCompactSupport hs
  have he : rowConv φ u x-u x=∫ y,φ y*(u (x-y)-u x) := by
    change (∫ y,φ y*u (x-y))-u x= _
    simp only [mul_sub]
    rw [integral_sub (rowConv_integrable hφ hs hu x) (hi.mul_const _),integral_mul_const,h1,one_mul]
  rw [he]
  calc
    _ ≤ ∫ y,|φ y*(u (x-y)-u x)| := abs_integral_le_integral_abs
    _ ≤ ∫ y,φ y*(L*δ) := integral_mono_of_nonneg (Eventually.of_forall (fun _ => abs_nonneg _))
      (hi.mul_const _) (Eventually.of_forall (fun y => by
        dsimp only
        by_cases hz : φ y=0
        · simp [hz]
        rw [abs_mul,abs_of_nonneg (hn y)]
        apply mul_le_mul_of_nonneg_left _ (hn y)
        have hh := hlip (x-y) x
        simp only [sub_sub_cancel_left,abs_neg] at hh
        exact hh.trans (mul_le_mul_of_nonneg_left (hr y hz) hL)))
    _ = _ := by rw [integral_mul_const,h1,one_mul]
end MicroscopicJamming

 
open Set Filter MeasureTheory
open scoped Topology

namespace MicroscopicJamming
lemma row_smooth_bounded_analytic {u : ℝ → ℝ} {L B Q : ℝ}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (hc : ConcaveOn ℝ univ u) (hL : 0 ≤ L)
    (hlip : ∀ x y, |u x-u y| ≤ L*|x-y|) (hb : ∀ x,u x ≤ B)
    (hd : ∀ n : ℕ,2 ≤ n → ∃ K : ℝ,∀ x,|iteratedDeriv n u x| ≤ K) :
    ∃ A C H : ℝ, RowAnalyticTerminal u A B C 0 Q ∧ RowBoundedTerminal u L H := by
  obtain ⟨K,hK⟩ := hd 2 le_rfl
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hslope (x : ℝ) : |deriv u x| ≤ L := by
    have hh := norm_deriv_le_of_lipschitz (rowReal_Lipschitz hL hlip) (x₀:=x)
    change |deriv u x| ≤ L at hh
    exact hh
  have hcurve (x : ℝ) : |deriv (deriv u) x| ≤ K := by simpa [iteratedDeriv_succ,iteratedDeriv_zero] using hK x
  have hnonpos (x : ℝ) : deriv (deriv u) x ≤ 0 := by
    have ha : Antitone (deriv u) := fun a b hab => hc.antitoneOn_deriv (fun z _ => hu.differentiable (by simp) z) (mem_univ a) (mem_univ b) hab
    exact ha.deriv_nonpos
  refine ⟨|u 0|+L,K,K,?_,?_,?_,hL,hK0,hslope,hcurve⟩
  · refine ⟨hu,by positivity,hK0,le_rfl,by simp,hd,fun x => ⟨?_,hb x,(abs_le.mp (hcurve x)).1,hnonpos x⟩⟩
    have hh := (abs_le.mp (hlip x 0)).1
    simp only [sub_zero] at hh
    have hx : |x| ≤ 1+x^2 := by nlinarith [sq_nonneg (|x|-1),sq_abs x]
    nlinarith [le_abs_self (u 0),neg_abs_le (u 0),mul_le_mul_of_nonneg_left hx hL,mul_nonneg (abs_nonneg (u 0)) (sq_nonneg x)]
  · exact hu.differentiable (by simp)
  · exact (contDiff_infty_iff_deriv.mp hu).2.differentiable (by simp)
lemma rowCap_lipschitz {u : ℝ → ℝ} {L : ℝ} (_hL : 0 ≤ L)
    (hlip : ∀ x y,|u x-u y| ≤ L*|x-y|) (B : ℝ) :
    ∀ x y,|min (u x) B-min (u y) B| ≤ L*|x-y| := by
  intro x y
  have h := abs_min_sub_min_le_max (u x) B (u y) B
  simp only [sub_self,abs_zero,max_eq_left (abs_nonneg (u x-u y))] at h
  exact h.trans (hlip x y)
lemma rowCap_error {u : ℝ → ℝ} {L ε : ℝ} (hL : 0 ≤ L) (hε : 0<ε)
    (hlip : ∀ x y,|u x-u y| ≤ L*|x-y|) (x : ℝ) :
    |min (u x) (u 0+L^2/ε)-u x| ≤ ε*x^2 := by
  by_cases hx : u x ≤ u 0+L^2/ε
  · rw [min_eq_left hx,sub_self,abs_zero]; positivity
  · rw [min_eq_right (le_of_not_ge hx),abs_of_nonpos (by linarith)]
    have hh := (abs_le.mp (hlip x 0)).2
    simp only [sub_zero] at hh
    have hdiv : (L^2/ε)*ε=L^2 := div_mul_cancel₀ _ hε.ne'
    have hab := sq_abs x
    have hs := two_mul_le_add_sq L (ε*|x|)
    simp only [mul_pow,sq_abs] at hs
    have hp := mul_nonneg hL (abs_nonneg x)
    have hh2 : ε*(u x-u 0) ≤ ε*(L*|x|) := mul_le_mul_of_nonneg_left hh hε.le
    apply (mul_le_mul_iff_right₀ hε).mp
    nlinarith [mul_nonneg hε.le hp]
lemma row_lipschitz_analytic_approx_one {u : ℝ → ℝ} {L ε Q : ℝ}
    (hc : ConcaveOn ℝ univ u) (hL : 0 ≤ L) (hlip : ∀ x y,|u x-u y| ≤ L*|x-y|) (hε : 0<ε) :
    ∃ v : ℝ → ℝ, ∃ A B C H : ℝ,
      RowAnalyticTerminal v A B C 0 Q ∧ RowBoundedTerminal v L H ∧ ConcaveOn ℝ univ v ∧
      (∀ x,|v x-u x| ≤ ε*(L+1)*(1+x^2)^2) := by
  let φ : ContDiffBump (0:ℝ) := ⟨ε/2,ε,half_pos hε,half_lt_self hε⟩
  let v (x : ℝ) := min (u x) (u 0+L^2/ε)
  have hvl := rowCap_lipschitz hL hlip (u 0+L^2/ε)
  have hvc : Continuous v := (rowReal_Lipschitz hL hvl).continuous
  have hvs : ConcaveOn ℝ univ v := hc.inf (concaveOn_const (c:=u 0+L^2/ε) convex_univ)
  have hφc : Continuous (φ.normed volume) := φ.continuous_normed
  have hφs : HasCompactSupport (φ.normed volume) := φ.hasCompactSupport_normed
  have hφn : ∀ x,0 ≤ φ.normed volume x := φ.nonneg_normed
  have hφ1 : (∫ x,φ.normed volume x)=1 := φ.integral_normed
  let w := rowConv (φ.normed volume) v
  have hw : ContDiff ℝ (↑(⊤:ℕ∞)) w := hφs.contDiff_convolution_left (.mul ℝ ℝ) φ.contDiff_normed hvc.locallyIntegrable
  have hwc := rowConv_concave hφc hφs hφn hvc hvs
  have hwl := rowConv_lipschitz hφc hφs hφn hφ1 hvc hvl
  obtain ⟨A,C,H,hwA,hwB⟩ := row_smooth_bounded_analytic (Q:=Q) hw hwc hL hwl
    (rowConv_upper hφc hφs hφn hφ1 hvc (fun x => min_le_right _ _))
    (fun n hn => rowConv_iterated_bound φ.contDiff_normed hφs hvc hL hvl (by omega))
  refine ⟨w,A,u 0+L^2/ε,C,H,hwA,hwB,hwc,fun x => ?_⟩
  have hr (y : ℝ) (hy : φ.normed volume y≠0) : |y| ≤ ε := by
    have hh : y ∈ Function.support (φ.normed volume) := hy
    rw [φ.support_normed_eq] at hh
    have hh' : |y|<ε := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hh
    exact hh'.le
  have h1 := rowConv_approx hφc hφs hφn hφ1 hvc hL hr hvl x
  have h2 := rowCap_error hL hε hlip x
  have ht : |w x-u x| ≤ |w x-v x|+|v x-u x| := by simpa only [sub_add_sub_cancel] using abs_add_le (w x-v x) (v x-u x)
  have hx : 0 ≤ x^2 := sq_nonneg x
  have he : ε*(L+x^2) ≤ ε*(L+1)*(1+x^2)^2 := by
    have hh : L+x^2 ≤ (L+1)*(1+x^2)^2 := by nlinarith [mul_nonneg hL hx,mul_nonneg hL (sq_nonneg (x^2)),sq_nonneg (x^2)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hε.le
  dsimp [w] at ht ⊢
  dsimp [v] at h2 ht
  linarith
end MicroscopicJamming

 
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace MicroscopicJamming
lemma rowBounded_lip {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H) :
    ∀ x y,|u x-u y| ≤ L*|x-y| := by
  intro x y
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le (fun z (_ : z∈(univ : Set ℝ)) => hu.diff z) (fun z _ => by simpa only [Real.norm_eq_abs] using hu.slope z) convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs] using hh
lemma row_pointwise_lip {u : ℝ → ℝ} {v : ℕ → ℝ → ℝ} {L : ℝ}
    (hlip : ∀ n x y,|v n x-v n y| ≤ L*|x-y|)
    (hlim : ∀ x,Tendsto (fun n => v n x) atTop (𝓝 (u x))) :
    ∀ x y,|u x-u y| ≤ L*|x-y| := by
  intro x y
  exact le_of_tendsto ((hlim x).sub (hlim y)).abs (Eventually.of_forall (fun n => hlip n x y))
lemma row_linear_limit_bound {u : ℝ → ℝ} {v : ℕ → ℝ → ℝ} {L : ℝ}
    (hlip : ∀ n x y,|v n x-v n y| ≤ L*|x-y|)
    (hlim : Tendsto (fun n => v n 0) atTop (𝓝 (u 0))) :
    ∃ M : ℝ,0 ≤ M ∧ ∀ n x,|v n x| ≤ M+L*|x| := by
  obtain ⟨M,hM⟩ := hlim.abs.bddAbove_range
  refine ⟨max M 0,le_max_right _ _,fun n x => ?_⟩
  have hh := hlip n x 0
  simp only [sub_zero] at hh
  have h0 : |v n 0| ≤ M := hM ⟨n,rfl⟩
  have ht : |v n x| ≤ |v n x-v n 0|+|v n 0| := by simpa only [sub_add_cancel] using abs_add_le (v n x-v n 0) (v n 0)
  linarith [le_max_left M 0]
lemma row_linear_operator_limit {u : ℝ → ℝ} {v : ℕ → ℝ → ℝ} {M L a T : ℝ}
    (_hM : 0 ≤ M) (hL : 0 ≤ L) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hu : Continuous u) (hv : ∀ n,Continuous (v n))
    (hb : ∀ n x,|v n x| ≤ M+L*|x|)
    (hlim : ∀ x,Tendsto (fun n => v n x) atTop (𝓝 (u x))) (x : ℝ) :
    Tendsto (fun n => gaussianRowOperator a T (v n) x) atTop (𝓝 (gaussianRowOperator a T u x)) := by
  let E (y : ℝ) := Real.exp (M+L*|y|)
  have hg : RowExpGrowth E := ⟨Real.exp M,L,(Real.exp_pos _).le,hL,fun y => by
    rw [show E y=Real.exp (M+L*|y|) from rfl,abs_of_pos (Real.exp_pos _),Real.exp_add]⟩
  have hi : Integrable (fun z => E (x+Real.sqrt T*z)) (gaussianReal 0 1) := hg.integrable_affine (by fun_prop) _ _
  have hvb (n : ℕ) (y : ℝ) : ‖v n y‖ ≤ E y := by
    rw [Real.norm_eq_abs]
    exact (hb n y).trans (by have hh := Real.add_one_le_exp (M+L*|y|); dsimp [E]; linarith)
  have heb (n : ℕ) (y : ℝ) : ‖Real.exp (a*v n y)‖ ≤ E y := by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      a*v n y ≤ a*|v n y| := mul_le_mul_of_nonneg_left (le_abs_self _) ha
      _ ≤ |v n y| := mul_le_of_le_one_left (abs_nonneg _) ha1
      _ ≤ _ := hb n y
  by_cases hz : a=0
  · simp only [gaussianRowOperator,hz,ite_true]
    exact tendsto_integral_of_dominated_convergence (fun z => E (x+Real.sqrt T*z))
      (fun n => ((hv n).comp (by fun_prop)).aestronglyMeasurable) hi
      (fun n => Eventually.of_forall (fun z => hvb n _)) (Eventually.of_forall (fun z => hlim _))
  · have he : Tendsto (fun n => gaussianHeat (fun y => Real.exp (a*v n y)) T x) atTop
        (𝓝 (gaussianHeat (fun y => Real.exp (a*u y)) T x)) := by
      exact tendsto_integral_of_dominated_convergence (fun z => E (x+Real.sqrt T*z))
        (fun n => (by fun_prop)) hi (fun n => Eventually.of_forall (fun z => heb n _))
        (Eventually.of_forall (fun z => (Real.continuous_exp.tendsto _).comp ((hlim (x+Real.sqrt T*z)).const_mul a)))
    have hui : Integrable (fun z => Real.exp (a*u (x+Real.sqrt T*z))) (gaussianReal 0 1) := by
      apply hi.mono' (by fun_prop)
      filter_upwards [] with z
      exact le_of_tendsto (((Real.continuous_exp.tendsto _).comp ((hlim (x+Real.sqrt T*z)).const_mul a)).norm) (Eventually.of_forall (fun n => heb n _))
    have hp : 0<gaussianHeat (fun y => Real.exp (a*u y)) T x := integral_exp_pos hui
    simpa only [gaussianRowOperator,hz,ite_false] using (he.log hp.ne').const_mul (1/a)
lemma row_composition_terminal_limit {u : ℝ → ℝ} {v : ℕ → ℝ → ℝ} {L : ℝ} {H : ℕ → ℝ}
    (hv : ∀ n,RowBoundedTerminal (v n) L (H n))
    (hlim : ∀ x,Tendsto (fun n => v n x) atTop (𝓝 (u x)))
    (rs : List (ℝ × ℝ)) (hrs : ∀ r∈rs,0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) :
    ∀ x,Tendsto (fun n => gaussianRowComposition rs (v n) x) atTop (𝓝 (gaussianRowComposition rs u x)) := by
  induction rs with
  | nil => exact hlim
  | cons r rs ih =>
    have htail : ∀ r∈rs,0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2 := fun r hr => hrs r (List.mem_cons_of_mem _ hr)
    have hlimr := ih htail
    have hbr (n : ℕ) := rowBoundedComposition_terminal (hv n) rs htail
    have hlip (n : ℕ) := rowBounded_lip (hbr n).choose_spec
    have hlc := row_pointwise_lip hlip hlimr
    obtain ⟨M,hM,hb⟩ := row_linear_limit_bound hlip (hlimr 0)
    intro x
    exact row_linear_operator_limit hM (hv 0).L_nonneg (hrs r (by simp)).1 (hrs r (by simp)).2.1
      (rowReal_Lipschitz (hv 0).L_nonneg hlc).continuous (fun n => (hbr n).choose_spec.diff.continuous) hb hlimr x
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
lemma row_lipschitz_profile_conclusions {u : ℝ → ℝ} {L Q : ℝ}
    (hc : ConcaveOn ℝ univ u) (hL : 0 ≤ L) (hlip : ∀ x y,|u x-u y| ≤ L*|x-y|)
    (hQ : 0 ≤ Q) : RowProfileConclusions u Q := by
  rcases eq_or_lt_of_le hQ with h0 | hQ
  · subst Q; exact rowProfile_zero u
  let δ (n : ℕ) := 1/((n:ℝ)+1)
  have hδ (n : ℕ) : 0<δ n := by dsimp [δ]; positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)
  choose v A B C H hv hvb hvc herr using fun n => row_lipschitz_analytic_approx_one (Q:=Q) hc hL hlip (hδ n)
  let e (n : ℕ) := δ n*(L+1)
  have hen (n : ℕ) : 0 ≤ e n := by dsimp [e]; positivity
  have helim : Tendsto e atTop (𝓝 0) := by simpa only [zero_mul] using hδlim.mul_const (L+1)
  have hlim (x : ℝ) : Tendsto (fun n => v n x) atTop (𝓝 (u x)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (g:=fun n => e n*(1+x^2)^2) (fun _ => dist_nonneg) (fun n => by rw [Real.dist_eq]; exact herr n x)
    simpa only [zero_mul] using helim.mul_const ((1+x^2)^2)
  let K := Real.exp ((10+8*L)*Q)
  have hbound (rs : List (ℝ × ℝ)) (hrs : ∀ r∈rs,0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
      (ht : gaussianStepTime rs=Q) (n m : ℕ) :
      |gaussianRowComposition rs (v n) 0-gaussianRowComposition rs (v m) 0| ≤ (e n+e m)*K := by
    apply row_composition_weighted_Lipschitz hQ (hv n) (hv m) (hvb n) (hvb m) (add_nonneg (hen n) (hen m)) hrs ht
    intro x
    have hh := abs_sub_le (v n x) (u x) (v m x)
    rw [abs_sub_comm (u x)] at hh
    have h1 : |v n x-u x| ≤ e n*(1+x^2)^2 := herr n x
    have h2 : |v m x-u x| ≤ e m*(1+x^2)^2 := herr m x
    nlinarith
  have hfinite (rs : List (ℝ × ℝ)) (hrs : ∀ r∈rs,0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) :=
    row_composition_terminal_limit hvb hlim rs hrs 0
  apply row_terminal_profile_passage hQ hv hvb hvc
    (show Tendsto (fun n => e n*K) atTop (𝓝 0) by simpa only [zero_mul] using helim.mul_const K) _ (fun rs hrs _ => hfinite rs hrs)
  intro rs hrs ht n
  have hh := le_of_tendsto_of_tendsto ((tendsto_const_nhds.sub (hfinite rs hrs)).abs)
    ((tendsto_const_nhds.add helim).mul_const K) (Eventually.of_forall (hbound rs hrs ht n))
  simpa only [add_zero,abs_sub_comm] using hh
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
def rowCapSlope (R x : ℝ) := min (max (-1-x) 0) R
def rowHingeCap (β R x : ℝ) := β*(rowCapSlope R x*(1+x)+(rowCapSlope R x)^2/2)
lemma rowCapSlope_bounds {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    0 ≤ rowCapSlope R x ∧ rowCapSlope R x ≤ R :=
  ⟨le_min (le_max_right _ _) hR,min_le_right _ _⟩
lemma rowHingeCap_opt {β R s : ℝ} (hβ : 0 ≤ β) (hR : 0 ≤ R)
    (hs : 0 ≤ s) (hsR : s ≤ R) (x : ℝ) :
    rowHingeCap β R x ≤ β*(s*(1+x)+s^2/2) := by
  apply mul_le_mul_of_nonneg_left _ hβ
  dsimp [rowCapSlope]
  by_cases hx : -1-x ≤ 0
  · rw [max_eq_right hx,min_eq_left hR]
    nlinarith [mul_nonneg hs (show 0 ≤ 1+x by linarith),sq_nonneg s]
  · rw [max_eq_left (le_of_not_ge hx)]
    by_cases hxR : -1-x ≤ R
    · rw [min_eq_left hxR]; nlinarith [sq_nonneg (s-(-1-x))]
    · rw [min_eq_right (le_of_not_ge hxR)]
      nlinarith [sq_nonneg (R-s),mul_nonneg (show 0 ≤ R-s by linarith) (show 0 ≤ -1-x-R by linarith)]
lemma rowHingeCap_concave {β R : ℝ} (hβ : 0 ≤ β) (hR : 0 ≤ R) :
    ConcaveOn ℝ univ (rowHingeCap β R) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  let s := rowCapSlope R (a*x+b*y)
  have hs := rowCapSlope_bounds hR (a*x+b*y)
  have hx := rowHingeCap_opt hβ hR hs.1 hs.2 x
  have hy := rowHingeCap_opt hβ hR hs.1 hs.2 y
  have hc : rowHingeCap β R (a*x+b*y)=a*(β*(s*(1+x)+s^2/2))+b*(β*(s*(1+y)+s^2/2)) := by
    dsimp [rowHingeCap,s]
    nlinarith [congrArg (fun t : ℝ => t*β*rowCapSlope R (a*x+b*y)) hab,
      congrArg (fun t : ℝ => t*β*(rowCapSlope R (a*x+b*y))^2) hab]
  rw [hc]
  exact add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
lemma rowHingeCap_sub_le {β R : ℝ} (hβ : 0 ≤ β) (hR : 0 ≤ R) (x y : ℝ) :
    rowHingeCap β R x-rowHingeCap β R y ≤ β*R*|x-y| := by
  have hs := rowCapSlope_bounds hR y
  have hh := rowHingeCap_opt hβ hR hs.1 hs.2 x
  have hb : β*rowCapSlope R y ≤ β*R := mul_le_mul_of_nonneg_left hs.2 hβ
  have ht := mul_le_mul_of_nonneg_left (le_abs_self (x-y)) (mul_nonneg hβ hs.1)
  have ht' := mul_le_mul_of_nonneg_right hb (abs_nonneg (x-y))
  dsimp [rowHingeCap] at hh ⊢
  nlinarith
lemma rowHingeCap_lip {β R : ℝ} (hβ : 0 ≤ β) (hR : 0 ≤ R) (x y : ℝ) :
    |rowHingeCap β R x-rowHingeCap β R y| ≤ β*R*|x-y| := by
  rw [abs_le]
  have h1 := rowHingeCap_sub_le hβ hR x y
  have h2 := rowHingeCap_sub_le hβ hR y x
  rw [abs_sub_comm y x] at h2
  constructor <;> linarith
lemma rowHingeCap_upper {β R : ℝ} (hβ : 0 ≤ β) (hR : 0 ≤ R) (x : ℝ) :
    rowHingeCap β R x ≤ 0 := by
  simpa using rowHingeCap_opt hβ hR (le_refl 0) hR x
lemma rowHingeCap_lower {β R : ℝ} (hβ : 0 ≤ β) (hR : 0 ≤ R) (x : ℝ) :
    -β*rowQuadraticHinge x ≤ rowHingeCap β R x := by
  dsimp [rowHingeCap,rowQuadraticHinge]
  by_cases hx : -1-x ≤ 0
  · simp [rowCapSlope,max_eq_right hx,min_eq_left hR]
  · rw [max_eq_left (le_of_not_ge hx)]
    nlinarith [mul_nonneg hβ (sq_nonneg (rowCapSlope R x-(-1-x)))]
lemma rowHinge_quadratic {β : ℝ} (hβ : 0 ≤ β) (x : ℝ) :
    -β*(1+x^2) ≤ -β*rowQuadraticHinge x := by
  dsimp [rowQuadraticHinge]
  by_cases hx : -1-x ≤ 0
  · rw [max_eq_right hx]; nlinarith [mul_nonneg hβ (sq_nonneg x)]
  · rw [max_eq_left (le_of_not_ge hx)]
    nlinarith [mul_nonneg hβ (sq_nonneg (x-1))]
lemma rowHingeCap_eq {β R : ℝ} (hR : 0 ≤ R) {x : ℝ} (hx : -1-x ≤ R) :
    rowHingeCap β R x = -β*rowQuadraticHinge x := by
  dsimp [rowHingeCap,rowCapSlope,rowQuadraticHinge]
  rw [min_eq_left (max_le hx hR)]
  by_cases h : -1-x ≤ 0
  · simp [max_eq_right h]
  · rw [max_eq_left (le_of_not_ge h)]; ring
lemma rowHingeCap_error {β R : ℝ} (hβ : 0 ≤ β) (hR : 0 < R) (x : ℝ) :
    |rowHingeCap β R x-(-β*rowQuadraticHinge x)| ≤ (2*β/R^2)*(1+x^2)^2 := by
  rw [abs_of_nonneg (sub_nonneg.mpr (rowHingeCap_lower hβ hR.le x))]
  by_cases hx : -1-x ≤ R
  · rw [rowHingeCap_eq hR.le hx,sub_self]; positivity
  · have hR2 : 0<R^2 := sq_pos_of_pos hR
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hR2).mpr
    have hb : rowHingeCap β R x-(-β*rowQuadraticHinge x) ≤ β*(1+x^2) := by
      linarith [rowHingeCap_upper hβ hR.le x,rowHinge_quadratic hβ x]
    have hs : R^2 ≤ 2*(1+x^2) := by
      have ha : R < -1-x := lt_of_not_ge hx
      have hsq : R^2 ≤ (-1-x)^2 := sq_le_sq₀ hR.le (by linarith) |>.2 ha.le
      nlinarith [sq_nonneg (x-1)]
    calc
      _ ≤ (β*(1+x^2))*R^2 := mul_le_mul_of_nonneg_right hb hR2.le
      _ ≤ (β*(1+x^2))*(2*(1+x^2)) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
end MicroscopicJamming

 
open Set Filter MeasureTheory
open scoped Topology

namespace MicroscopicJamming
lemma rowConv_quadratic_lower {φ u : ℝ → ℝ} {A : ℝ} (hφ : Continuous φ) (hs : HasCompactSupport φ)
    (hn : ∀ x,0 ≤ φ x) (h1 : (∫ x,φ x)=1) (hu : Continuous u) (hA : 0 ≤ A)
    (hb : ∀ x,-A*(1+x^2) ≤ u x) (hr : ∀ x,φ x≠0 → |x| ≤ 1) (x : ℝ) :
    -(3*A)*(1+x^2) ≤ rowConv φ u x := by
  have hi : Integrable φ := hφ.integrable_of_hasCompactSupport hs
  calc
    _ = ∫ y,φ y*(-(3*A)*(1+x^2)) := by rw [integral_mul_const,h1,one_mul]
    _ ≤ _ := integral_mono (hi.mul_const _) (rowConv_integrable hφ hs hu x) (fun y => by
      by_cases hz : φ y=0
      · simp [hz]
      apply mul_le_mul_of_nonneg_left _ (hn y)
      have hy : y^2 ≤ 1 := by have hh:=hr y hz; nlinarith [sq_abs y,abs_nonneg y]
      have hh : 1+(x-y)^2 ≤ 3*(1+x^2) := by nlinarith [sq_nonneg (x+y)]
      have hm := mul_le_mul_of_nonneg_left hh hA
      linarith [hb (x-y)])
lemma row_hinge_analytic_approx_one {β R δ Q : ℝ} (hβ : 0<β) (hR : 0<R)
    (hδ : 0<δ) (hδ1 : δ ≤ 1) :
    ∃ v : ℝ → ℝ, ∃ C H : ℝ,
      RowAnalyticTerminal v (3*β) 0 C 0 Q ∧ RowBoundedTerminal v (β*R) H ∧ ConcaveOn ℝ univ v ∧
      (∀ x,|v x-(-β*rowQuadraticHinge x)| ≤ (β*R*δ+2*β/R^2)*(1+x^2)^2) := by
  let φ : ContDiffBump (0:ℝ) := ⟨δ/2,δ,half_pos hδ,half_lt_self hδ⟩
  let u := rowHingeCap β R
  have hL : 0 ≤ β*R := mul_nonneg hβ.le hR.le
  have hul := rowHingeCap_lip hβ.le hR.le
  have huc : Continuous u := (rowReal_Lipschitz hL hul).continuous
  have hφc : Continuous (φ.normed volume) := φ.continuous_normed
  have hφs : HasCompactSupport (φ.normed volume) := φ.hasCompactSupport_normed
  have hφn : ∀ x,0 ≤ φ.normed volume x := φ.nonneg_normed
  have hφ1 : (∫ x,φ.normed volume x)=1 := φ.integral_normed
  have hr (y : ℝ) (hy : φ.normed volume y≠0) : |y| ≤ δ := by
    have hh : y ∈ Function.support (φ.normed volume) := hy
    rw [φ.support_normed_eq] at hh
    have hh' : |y|<δ := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hh
    exact hh'.le
  let v := rowConv (φ.normed volume) u
  have hv : ContDiff ℝ (↑(⊤:ℕ∞)) v := hφs.contDiff_convolution_left (.mul ℝ ℝ) φ.contDiff_normed huc.locallyIntegrable
  have hvc := rowConv_concave hφc hφs hφn huc (rowHingeCap_concave hβ.le hR.le)
  have hvl := rowConv_lipschitz hφc hφs hφn hφ1 huc hul
  have hvu := rowConv_upper hφc hφs hφn hφ1 huc (rowHingeCap_upper hβ.le hR.le)
  have hlow (x : ℝ) : -(3*β)*(1+x^2) ≤ v x :=
    rowConv_quadratic_lower hφc hφs hφn hφ1 huc hβ.le
      (fun y => (rowHinge_quadratic hβ.le y).trans (rowHingeCap_lower hβ.le hR.le y)) (fun y hy => (hr y hy).trans hδ1) x
  obtain ⟨A,C,H,hvA,hvB⟩ := row_smooth_bounded_analytic (Q:=Q) hv hvc hL hvl hvu
    (fun n hn => rowConv_iterated_bound φ.contDiff_normed hφs huc hL hul (by omega))
  refine ⟨v,C,H,⟨hvA.1,by positivity,hvA.2.2.1,hvA.2.2.2.1,hvA.2.2.2.2.1,hvA.2.2.2.2.2.1,fun x => ⟨hlow x,(hvA.2.2.2.2.2.2 x).2⟩⟩,hvB,hvc,fun x => ?_⟩
  have hm := rowConv_approx hφc hφs hφn hφ1 huc hL hr hul x
  have he := rowHingeCap_error hβ.le hR x
  have ht : |v x-(-β*rowQuadraticHinge x)| ≤ |v x-u x|+|u x-(-β*rowQuadraticHinge x)| := by
    simpa only [sub_add_sub_cancel] using abs_add_le (v x-u x) (u x-(-β*rowQuadraticHinge x))
  have hh : β*R*δ ≤ β*R*δ*(1+x^2)^2 := by
    have hx : 1 ≤ (1+x^2)^2 := by nlinarith [sq_nonneg x,sq_nonneg (x^2)]
    exact le_mul_of_one_le_right (by positivity) hx
  dsimp [v,u] at hm ht ⊢
  nlinarith
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
lemma row_concave_quadratic_slope {f : ℝ → ℝ} {K : ℝ}
    (hf : Differentiable ℝ f) (hc : ConcaveOn ℝ univ f) (hK : 0 ≤ K)
    (hb : ∀ x,|f x| ≤ K*(1+x^2)) (x : ℝ) :
    |deriv f x| ≤ (8*K)*(1+|x|) := by
  let d := 1+|x|
  have hd : 0<d := by dsimp [d]; positivity
  have hsq (y : ℝ) (hy : |y| ≤ 2*d) : 2+y^2+x^2 ≤ 8*d^2 := by
    have hx : |x| ≤ d := by dsimp [d]; linarith
    have hh : y^2 ≤ (2*d)^2 := by nlinarith [sq_abs y,abs_nonneg y]
    have hh' : x^2 ≤ d^2 := by nlinarith [sq_abs x,abs_nonneg x]
    have hd1 : 1 ≤ d := by dsimp [d]; linarith [abs_nonneg x]
    nlinarith
  have hy1 : |x+d| ≤ 2*d := by have hh := abs_add_le x d; rw [abs_of_pos hd] at hh; dsimp [d] at *; linarith
  have hy2 : |x-d| ≤ 2*d := by have hh := abs_sub x d; rw [abs_of_pos hd] at hh; dsimp [d] at *; linarith
  have h1 := hc.slope_le_deriv (mem_univ x) (mem_univ (x+d)) (by linarith) (hf x)
  have h2 := hc.deriv_le_slope (mem_univ (x-d)) (mem_univ x) (by linarith) (hf x)
  rw [slope_def_field,show x+d-x=d by ring] at h1
  rw [slope_def_field,show x-(x-d)=d by ring] at h2
  have h1' := (div_le_iff₀ hd).mp h1
  have h2' := (le_div_iff₀ hd).mp h2
  have b1 := (abs_le.mp (hb (x+d))).1
  have b2 := (abs_le.mp (hb (x-d))).1
  have bx := (abs_le.mp (hb x)).2
  have k1 := mul_le_mul_of_nonneg_left (hsq (x+d) hy1) hK
  have k2 := mul_le_mul_of_nonneg_left (hsq (x-d) hy2) hK
  have hl : -(8*K)*d ≤ deriv f x := by
    apply (mul_le_mul_iff_right₀ hd).mp
    nlinarith
  have hu : deriv f x ≤ (8*K)*d := by
    apply (mul_le_mul_iff_right₀ hd).mp
    nlinarith
  exact abs_le.mpr ⟨by dsimp [d] at hl; nlinarith,hu⟩
lemma row_step_concave_slope {u : ℝ → ℝ} {A B C Q : ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C 0 Q)
    {rs : List (ℝ × ℝ)} (hrs : ∀ r∈rs,0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (hT : gaussianStepTime rs=Q) {t : ℝ} (ht : t∈Set.Icc 0 Q) (x : ℝ) :
    |deriv (gaussianStepPath rs u t) x| ≤ (8*(|B|+A*(1+Q)))*(1+|x|) := by
  have hv := gaussianStepRemainder_valid hrs ht.1
  have htime : gaussianStepTime (gaussianStepRemainder rs t) ≤ Q := by
    rw [hv.2,hT,max_eq_left (sub_nonneg.mpr ht.2)]; linarith [ht.1]
  obtain ⟨hd,hd',hb⟩ := gaussian_step_bounds u A B C 0 Q hQ hu _ hv.1 htime
  have hc : ConcaveOn ℝ univ (gaussianRowComposition (gaussianStepRemainder rs t) u) :=
    concaveOn_univ_of_deriv2_nonpos hd hd' (fun y => by simpa using (hb y).2.2)
  change |deriv (gaussianRowComposition (gaussianStepRemainder rs t) u) x| ≤ _
  exact row_concave_quadratic_slope hd hc (by have := hu.2.1; positivity)
    (gaussianStepPath_global_value_bound hQ hu hrs hT ht) x
end MicroscopicJamming

end

end OAI
