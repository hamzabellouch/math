import Mathlib
import OAI.Probability.JammingConcavity.RowVariableComparison

namespace OAI

/-! Row Mixed Calculus. -/

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
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace Higher

def spacePartial (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => f (p.1,x)) p.2

def timePartial (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun t => f (t,p.2)) p.1

lemma spacePartial_eq_fderiv {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p) : spacePartial f p=fderiv ℝ f p (0,1) := by
  exact (hf.hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv
lemma timePartial_eq_fderiv {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p) : timePartial f p=fderiv ℝ f p (1,0) := by
  exact (hf.hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).deriv

lemma partial_space_smooth {f : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f S) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (spacePartial f) S := by
  apply ((hf.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const).congr
  intro p hp
  exact spacePartial_eq_fderiv ((hf.contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp))
lemma partial_time_smooth {f : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f S) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (timePartial f) S := by
  apply ((hf.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const).congr
  intro p hp
  exact timePartial_eq_fderiv ((hf.contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp))

lemma partial_time_space_commute {f : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f S) {p : ℝ × ℝ} (hp : p ∈ S) :
    timePartial (spacePartial f) p=spacePartial (timePartial f) p := by
  have hfa := hf.contDiffAt (hS.mem_nhds hp)
  have hfd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) p :=
    (hf.fderiv_of_isOpen hS (by simp)).contDiffAt (hS.mem_nhds hp)
  have hdx := (hfd.differentiableAt (by simp)).hasFDerivAt.clm_apply
    (hasFDerivAt_const ((0,1) : ℝ × ℝ) p)
  have hdt := (hfd.differentiableAt (by simp)).hasFDerivAt.clm_apply
    (hasFDerivAt_const ((1,0) : ℝ × ℝ) p)
  have hex : spacePartial f =ᶠ[𝓝 p] fun z => fderiv ℝ f z (0,1) := by
    filter_upwards [hS.mem_nhds hp] with z hz
    exact spacePartial_eq_fderiv ((hf.contDiffAt (hS.mem_nhds hz)).differentiableAt (by simp))
  have het : timePartial f =ᶠ[𝓝 p] fun z => fderiv ℝ f z (1,0) := by
    filter_upwards [hS.mem_nhds hp] with z hz
    exact timePartial_eq_fderiv ((hf.contDiffAt (hS.mem_nhds hz)).differentiableAt (by simp))
  have hx := (hdx.congr_of_eventuallyEq hex).comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  have ht := (hdt.congr_of_eventuallyEq het).comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  change deriv (fun t => spacePartial f (t,p.2)) p.1 = deriv (fun x => timePartial f (p.1,x)) p.2
  dsimp only [Function.comp_def,id_eq] at hx ht
  rw [hx.deriv,ht.deriv]
  simpa using (hfa.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞); exact WithTop.coe_le_coe.mpr le_top)).eq (1,0) (0,1)

lemma iterated_space_smooth {f : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f S) (n : ℕ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p => iteratedDeriv n (fun x => f (p.1,x)) p.2) S := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    have he : (fun p => iteratedDeriv (n+1) (fun x => f (p.1,x)) p.2) =
        spacePartial (fun p => iteratedDeriv n (fun x => f (p.1,x)) p.2) := by
      funext p
      rw [iteratedDeriv_succ]
      rfl
    rw [he]
    exact partial_space_smooth hS ih

 

lemma time_iterated_space {f : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f S) (n : ℕ) {p : ℝ × ℝ} (hp : p ∈ S) :
    timePartial (fun p => iteratedDeriv n (fun x => f (p.1,x)) p.2) p =
      iteratedDeriv n (fun x => timePartial f (p.1,x)) p.2 := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    have hh := partial_time_space_commute hS (iterated_space_smooth hS hf n) hp
    have he : (fun p => iteratedDeriv (n+1) (fun x => f (p.1,x)) p.2) =
        spacePartial (fun p => iteratedDeriv n (fun x => f (p.1,x)) p.2) := by
      funext z
      rw [iteratedDeriv_succ]
      rfl
    rw [he]
    rw [hh,spacePartial,iteratedDeriv_succ]
    apply Filter.EventuallyEq.deriv_eq
    have hm : Continuous (fun x : ℝ => (p.1,x)) := continuous_const.prodMk continuous_id
    filter_upwards [hm.continuousAt.preimage_mem_nhds (hS.mem_nhds hp)] with x hx
    exact ih hx
end Higher
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace Higher
lemma normalizedHeatJet_iterated_continuous {u : ℝ → ℝ} (hu : SmoothPolynomial u)
    {a B : ℝ} (ha : 0 ≤ a) (hB : ∀ x,u x ≤ B) (k n : ℕ) :
    Continuous (fun p : ℝ × ℝ => iteratedDeriv k (normalizedHeatJet u a p.1 n) p.2) := by
  induction k using Nat.strong_induction_on generalizing n with
  | h k ih =>
    cases k with
    | zero => simpa using normalizedHeatJet_jointly_continuous hu ha hB n
    | succ k =>
      have hc (T : ℝ) (p : ℕ) : ContDiff ℝ (k : WithTop ℕ∞) (normalizedHeatJet u a T p) :=
        (normalizedHeatJet_smooth hu ha hB T p).of_le
          (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
      have hd (T : ℝ) : deriv (normalizedHeatJet u a T n) = fun x =>
          normalizedHeatJet u a T (n+1) x-normalizedHeatJet u a T n x*normalizedHeatJet u a T 1 x := by
        funext x
        exact (normalizedHeatJet_space hu ha hB T n x).deriv
      have he (T x : ℝ) : iteratedDeriv (k+1) (normalizedHeatJet u a T n) x =
          iteratedDeriv k (normalizedHeatJet u a T (n+1)) x-
          ∑ i ∈ Finset.range (k+1),(k.choose i:ℝ)*iteratedDeriv i (normalizedHeatJet u a T n) x*
            iteratedDeriv (k-i) (normalizedHeatJet u a T 1) x := by
        rw [iteratedDeriv_succ',hd T,
          iteratedDeriv_fun_sub (hc T (n+1)).contDiffAt ((hc T n).mul (hc T 1)).contDiffAt,
          iteratedDeriv_fun_mul (hc T n).contDiffAt (hc T 1).contDiffAt]
      simp only [he]
      apply (ih k (by omega) (n+1)).sub
      apply continuous_finsetSum
      intro i hi
      exact ((ih i (Finset.mem_range.mp hi) n).const_mul (k.choose i:ℝ)).mul (ih (k-i) (by omega) 1)

lemma gaussianRowOperator_iterated_continuous {u : ℝ → ℝ} (hu : SmoothPolynomial u)
    {a B : ℝ} (ha : 0 ≤ a) (hB : ∀ x,u x ≤ B) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => iteratedDeriv n (gaussianRowOperator a p.1 u) p.2) := by
  by_cases haz : a=0
  · subst a
    have he (r : ℝ) : gaussianRowOperator 0 r u = gaussianHeat u r := by funext x; simp [gaussianRowOperator]
    simp only [he,heat_iterated_derivative hu]
    exact heat_jointly_continuous (hu.continuous n) (hu.growth n)
  · cases n with
    | zero =>
      simp only [iteratedDeriv_zero]
      have he (t x : ℝ) : gaussianRowOperator a t u x=(1/a)*Real.log (gaussianHeat (fun y => Real.exp (a*u y)) t x) := by
        simp [gaussianRowOperator,haz]
      simp only [he]
      exact ((heat_jointly_continuous (exp_smoothPolynomial hu ha hB).smooth.continuous
        (by simpa using (exp_smoothPolynomial hu ha hB).growth 0)).log
          (fun p => (exp_heat_pos hu.smooth.continuous hB ha).ne')).const_mul (1/a)
    | succ n =>
      have he (t x : ℝ) : iteratedDeriv (n+1) (gaussianRowOperator a t u) x =
          (1/a)*iteratedDeriv n (normalizedHeatJet u a t 1) x := by
        rw [iteratedDeriv_succ',gaussianRowOperator_deriv_normalized hu ha haz hB]
        exact iteratedDeriv_const_mul_field (n:=n) (x:=x) (1/a) _
      simp only [he]
      exact (normalizedHeatJet_iterated_continuous hu ha hB n 1).const_mul (1/a)

lemma gaussianRowOperator_iterated_growth {u : ℝ → ℝ} {A B C κ Q a L : ℝ}
    (hu : Twice.RowTwiceTerminal u A B C κ Q) (hs : SmoothPolynomial u)
    (ha : 0 ≤ a) (hL : 0 ≤ L) (hsub : a*κ*L<1) (n : ℕ) :
    UniformPolynomialGrowth (Icc 0 L) (fun t x => iteratedDeriv n (gaussianRowOperator a t u) x) := by
  by_cases haz : a=0
  · subst a
    have he (r : ℝ) : gaussianRowOperator 0 r u = gaussianHeat u r := by funext x; simp [gaussianRowOperator]
    simp only [he,heat_iterated_derivative hs]
    exact heat_uniform_growth hu hL (hs.continuous n).measurable (hs.growth n)
  · cases n with
    | zero =>
      let H := A*(1+L)+|B|
      have hH : 0 ≤ H := by dsimp [H]; have hA := hu.A_nonneg; positivity
      refine ⟨2,H,hH,fun t ht x => ?_⟩
      simp only [iteratedDeriv_zero]
      have hb := gaussianRowOperator_barrier (R:=0) hu.differentiable.continuous.measurable
        hu.A_nonneg (by norm_num) ha ht.1 (fun x => by simpa using And.intro (hu.bounds x).1 (hu.bounds x).2.1) x
      have hbase : 1 ≤ (1+|x|)^2 := by nlinarith [sq_abs x,sq_nonneg x,abs_nonneg x]
      have hh : (1+x^2+t) ≤ (1+L)*(1+|x|)^2 := by
        nlinarith [sq_abs x,abs_nonneg x,mul_nonneg hL (sq_nonneg x),mul_nonneg hL (abs_nonneg x),ht.2]
      have h0 := mul_le_mul_of_nonneg_left hh hu.A_nonneg
      have h1 := mul_le_mul_of_nonneg_left hbase (abs_nonneg B)
      have h2 := mul_nonneg (abs_nonneg B) (sq_nonneg (1+|x|))
      rw [abs_le]
      dsimp [H]
      constructor <;> nlinarith [hb.1,hb.2,le_abs_self B,
        mul_nonneg (mul_nonneg hu.A_nonneg (show 0≤1+L by linarith)) (sq_nonneg (1+|x|))]
    | succ n =>
      have he (t x : ℝ) : iteratedDeriv (n+1) (gaussianRowOperator a t u) x =
          (1/a)*iteratedDeriv n (normalizedHeatJet u a t 1) x := by
        rw [iteratedDeriv_succ',gaussianRowOperator_deriv_normalized hs ha haz (fun x => (hu.bounds x).2.1)]
        exact iteratedDeriv_const_mul_field (n:=n) (x:=x) (1/a) _
      simpa only [he] using (normalizedHeatJet_iterated_growth hu hs ha hL hsub n 1).const_mul (1/a)
end Higher
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace Higher

lemma iteratedDeriv_iteratedDeriv (n k : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv n (iteratedDeriv k f)=iteratedDeriv (n+k) f := by
  simp only [iteratedDeriv_eq_iterate,Function.iterate_add_apply]

lemma gaussianRowOperator_jet_equation {u : ℝ → ℝ} {A B C κ Q a T : ℝ}
    (hu : Twice.RowTwiceTerminal u A B C κ Q) (hs : SmoothPolynomial u)
    (ha : 0 ≤ a) (hT : 0<T) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun t => iteratedDeriv n (gaussianRowOperator a t u) x)
      ((1/2:ℝ)*iteratedDeriv (n+2) (gaussianRowOperator a T u) x+
        (a/2)*∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*
          iteratedDeriv (i+1) (gaussianRowOperator a T u) x*
          iteratedDeriv (n-i+1) (gaussianRowOperator a T u) x) T := by
  let F : ℝ × ℝ → ℝ := fun p => gaussianRowOperator a p.1 u p.2
  have hf := gaussianRowOperator_jointly_smooth hs ha (fun x => (hu.bounds x).2.1)
  have hn := iterated_space_smooth heatDomain_open hf n
  have hnp := (hn.contDiffAt (heatDomain_open.mem_nhds (show (T,x) ∈ heatDomain from ⟨hT,mem_univ _⟩))).differentiableAt (by simp)
  have htime := hnp.hasFDerivAt.comp_hasDerivAt T
    ((hasDerivAt_id T).prodMk (hasDerivAt_const T x))
  have hmix := time_iterated_space heatDomain_open hf n (show (T,x) ∈ heatDomain from ⟨hT,mem_univ _⟩)
  have hbase : (fun y => timePartial F (T,y)) = fun y =>
      (1/2:ℝ)*(iteratedDeriv 2 (gaussianRowOperator a T u) y+
        a*(iteratedDeriv 1 (gaussianRowOperator a T u) y)^2) := by
    funext y
    simpa only [timePartial,F,iteratedDeriv_succ,iteratedDeriv_zero] using ((Twice.gaussianRowOperator_calculus hu ha hT).2.2 y).deriv
  have hh (k : ℕ) : ContDiff ℝ (n : WithTop ℕ∞) (iteratedDeriv k (gaussianRowOperator a T u)) := by
    rw [← contDiffOn_univ]
    exact ((iterated_space_smooth heatDomain_open hf k).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun y _ => (show (T,y) ∈ heatDomain from ⟨hT,mem_univ _⟩))).of_le
        (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hd : deriv (fun t => iteratedDeriv n (gaussianRowOperator a t u) x) T =
      (1/2:ℝ)*iteratedDeriv (n+2) (gaussianRowOperator a T u) x+
        (a/2)*∑ i ∈ Finset.range (n+1),(n.choose i:ℝ)*
          iteratedDeriv (i+1) (gaussianRowOperator a T u) x*
          iteratedDeriv (n-i+1) (gaussianRowOperator a T u) x := by
    change timePartial (fun p => iteratedDeriv n (fun y => F (p.1,y)) p.2) (T,x) = _
    rw [hmix,hbase,iteratedDeriv_const_mul_field]
    rw [iteratedDeriv_fun_add (hh 2).contDiffAt (contDiff_const.mul ((hh 1).pow 2)).contDiffAt]
    rw [iteratedDeriv_const_mul_field]
    simp only [pow_two]
    rw [iteratedDeriv_fun_mul (hh 1).contDiffAt (hh 1).contDiffAt]
    simp only [iteratedDeriv_iteratedDeriv]
    ring

  have hdif : DifferentiableAt ℝ (fun t => iteratedDeriv n (gaussianRowOperator a t u) x) T := by
    simpa only [Function.comp_def,id_eq] using htime.differentiableAt
  exact hdif.hasDerivAt.congr_deriv hd
end Higher
end MicroscopicJamming

 
open Set Filter
open scoped BigOperators

namespace MicroscopicJamming
namespace Higher
lemma jet_square_decompose (m : ℕ) (v : ℕ → ℝ) :
    (∑ i ∈ Finset.range (m+3+1), ((m+3).choose i:ℝ)*v (i+1)*v (m+3-i+1)) =
      2*v 1*v (m+4)+2*(m+3)*v 2*v (m+3)+
      ∑ j ∈ Finset.range m, ((m+3).choose (j+2):ℝ)*v (j+3)*v (m+2-j) := by
  rw [show m+3+1=(m+2)+1+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ,
    Finset.sum_range_succ',Finset.sum_range_succ']
  simp only [Nat.choose_self,Nat.cast_one,Nat.sub_zero,
    Nat.zero_add, Nat.choose_zero_right,one_mul,Nat.choose_one_right,Nat.cast_add,Nat.cast_ofNat]
  have hc : (m+3).choose (m+2)=m+3 := by
    exact Nat.choose_succ_self_right (m+2)
  rw [hc]
  have hs : (∑ x ∈ Finset.range m, ((m+3).choose (x+1+1):ℝ)*v (x+1+1+1)*v (m+3-(x+1+1)+1)) =
      ∑ j ∈ Finset.range m, ((m+3).choose (j+2):ℝ)*v (j+3)*v (m+2-j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have he : m+3-(j+1+1)+1=m+2-j := by omega
    simp only [he,Nat.add_assoc]
  rw [hs]
  simp only [Nat.cast_add,Nat.cast_ofNat]
  have h1 : m+3-1+1=m+3 := by omega
  have h2 : m+3-(m+2)+1=2 := by omega
  simp only [h1,h2,Nat.sub_self,Nat.zero_add]
  ring
end Higher
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace Higher
lemma gaussianRowOperator_higher_equation {u : ℝ → ℝ} {A B C κ Q a T : ℝ}
    (hu : Twice.RowTwiceTerminal u A B C κ Q) (hs : SmoothPolynomial u)
    (ha : 0 ≤ a) (hT : 0<T) (m : ℕ) (x : ℝ) :
    HasDerivAt (fun t => iteratedDeriv (m+3) (gaussianRowOperator a t u) x)
      ((1/2:ℝ)*iteratedDeriv (m+5) (gaussianRowOperator a T u) x+
        a*iteratedDeriv 1 (gaussianRowOperator a T u) x*iteratedDeriv (m+4) (gaussianRowOperator a T u) x+
        (m+3)*a*iteratedDeriv 2 (gaussianRowOperator a T u) x*iteratedDeriv (m+3) (gaussianRowOperator a T u) x+
        (a/2)*∑ j ∈ Finset.range m, ((m+3).choose (j+2):ℝ)*
          iteratedDeriv (j+3) (gaussianRowOperator a T u) x*iteratedDeriv (m+2-j) (gaussianRowOperator a T u) x) T := by
  convert gaussianRowOperator_jet_equation hu hs ha hT (m+3) x using 1
  rw [jet_square_decompose m (fun j => iteratedDeriv j (gaussianRowOperator a T u) x)]
  simp only [Nat.add_assoc]
  ring

lemma gaussianRowOperator_jet_bound {u : ℝ → ℝ} {A B C κ Q a L D K H S : ℝ}
    (m : ℕ) (hu : Twice.RowTwiceTerminal u A B C κ Q) (hs : SmoothPolynomial u)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hL : 0 < L) (hsub : a*κ*L < 1)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (hfirst : ∀ T ∈ Icc 0 L, ∀ x, |deriv (gaussianRowOperator a T u) x| ≤ D*(1+|x|))
    (hsecond : ∀ T ∈ Icc 0 L, ∀ x, deriv (deriv (gaussianRowOperator a T u)) x ≤ K)
    (hsource : ∀ T ∈ Icc 0 L, ∀ x, |(a/2)*∑ j ∈ Finset.range m, ((m+3).choose (j+2):ℝ)*
      iteratedDeriv (j+3) (gaussianRowOperator a T u) x*iteratedDeriv (m+2-j) (gaussianRowOperator a T u) x| ≤ S)
    (hinit : ∀ x, |iteratedDeriv (m+3) u x| ≤ H) :
    ∀ T ∈ Icc 0 L, ∀ x, |iteratedDeriv (m+3) (gaussianRowOperator a T u) x| ≤
      (H+S*T)*Real.exp ((m+3)*K*T) := by
  let F : ℝ → ℝ → ℝ := fun t => gaussianRowOperator a t u
  let U : ℝ → ℝ → ℝ := fun t => iteratedDeriv (m+3) (F t)
  let b : ℝ → ℝ → ℝ := fun t x => a*iteratedDeriv 1 (F t) x
  let r : ℝ → ℝ → ℝ := fun t x => (m+3)*a*iteratedDeriv 2 (F t) x
  let e : ℝ → ℝ → ℝ := fun t x => (a/2)*∑ j ∈ Finset.range m, ((m+3).choose (j+2):ℝ)*
    iteratedDeriv (j+3) (F t) x*iteratedDeriv (m+2-j) (F t) x
  let d : ℝ → ℝ → ℝ := fun t x => (1/2:ℝ)*iteratedDeriv (m+5) (F t) x+
    a*iteratedDeriv 1 (F t) x*iteratedDeriv (m+4) (F t) x+
    (m+3)*a*iteratedDeriv 2 (F t) x*iteratedDeriv (m+3) (F t) x+e t x
  have hsp (t : ℝ) (ht : t ∈ Icc 0 L) : SmoothPolynomial (F t) :=
    gaussianRowOperator_smoothPolynomial hu hs ha ht.1
      ((mul_le_mul_of_nonneg_left ht.2 (mul_nonneg ha hu.kappa_nonneg)).trans_lt hsub)
  have hU1 (t : ℝ) : deriv (U t)=iteratedDeriv (m+4) (F t) :=
    (iteratedDeriv_succ (n:=m+3)).symm
  have hU2 (t : ℝ) : deriv (deriv (U t))=iteratedDeriv (m+5) (F t) := by
    rw [hU1 t]; exact (iteratedDeriv_succ (n:=m+4)).symm
  have hUx (t : ℝ) (ht : t ∈ Icc 0 L) :
      Differentiable ℝ (U t) ∧ Differentiable ℝ (deriv (U t)) := by
    refine ⟨(hsp t ht).differentiable (m+3),?_⟩
    rw [hU1 t]
    exact (hsp t ht).differentiable (m+4)
  have hUb (t : ℝ) (ht : t ∈ Icc 0 L) (x : ℝ) : |b t x| ≤ D*(1+|x|) := by
    change |a*iteratedDeriv 1 (gaussianRowOperator a t u) x| ≤ _
    rw [abs_mul,abs_of_nonneg ha,iteratedDeriv_one]
    exact (mul_le_mul_of_nonneg_left (hfirst t ht x) ha).trans
      (mul_le_of_le_one_left (by positivity) ha1)
  have hUr (t : ℝ) (ht : t ∈ Ioc 0 L) (x : ℝ) : r t x ≤ (m+3)*K := by
    have hsec := hsecond t ⟨ht.1.le,ht.2⟩ x
    have hh := mul_le_mul_of_nonneg_left hsec ha
    have hh' := mul_le_of_le_one_left hK ha1
    dsimp [r,F]
    simp only [iteratedDeriv_succ,iteratedDeriv_zero]
    have hhh : a*deriv (deriv (gaussianRowOperator a t u)) x≤K := hh.trans hh'
    convert mul_le_mul_of_nonneg_left hhh (show 0≤(m:ℝ)+3 by positivity) using 1
    first | rfl | ring
  have hUp (t : ℝ) (ht : t ∈ Ioc 0 L) (x : ℝ) :
      |d t x-(1/2:ℝ)*deriv (deriv (U t)) x-b t x*deriv (U t) x-r t x*U t x| ≤ S := by
    rw [hU2 t,hU1 t]
    have heq : d t x-(1/2:ℝ)*iteratedDeriv (m+5) (F t) x-b t x*iteratedDeriv (m+4) (F t) x-r t x*U t x=e t x := by
      dsimp [d,b,r,U]; ring
    rw [heq]
    exact hsource t ⟨ht.1.le,ht.2⟩ x
  have he : F 0=u := funext (fun x => gaussianRowOperator_zero a u x)
  apply forward_reaction_source_bound hL hD (show 0 ≤ ((m:ℝ)+3)*K by positivity) hH hS
    (gaussianRowOperator_iterated_continuous hs ha (fun x => (hu.bounds x).2.1) (m+3)).continuousOn
    hUx (fun t ht x => gaussianRowOperator_higher_equation hu hs ha ht.1 m x)
    hUb (gaussianRowOperator_iterated_growth hu hs ha hL.le hsub (m+3)) hUr hUp
  intro x
  change |iteratedDeriv (m+3) (F 0) x| ≤ H
  rw [he]
  exact hinit x
end Higher
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace Higher

lemma jet_source_bound {m : ℕ} {a H : ℝ} (ha : 0≤a) (ha1 : a≤1) (hH : 0≤H)
    {v : ℕ → ℝ} (hv : ∀ k, 3≤k → k < m+3 → |v k|≤H) :
    |(a/2)*∑ j ∈ Finset.range m, ((m+3).choose (j+2):ℝ)*v (j+3)*v (m+2-j)| ≤
      (∑ j ∈ Finset.range m, ((m+3).choose (j+2):ℝ))*H^2 := by
  have hsum : |∑ j ∈ Finset.range m, ((m+3).choose (j+2):ℝ)*v (j+3)*v (m+2-j)| ≤
      (∑ j ∈ Finset.range m, ((m+3).choose (j+2):ℝ))*H^2 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
    have h1 := hv (j+3) (by omega) (by omega)
    have h2 := hv (m+2-j) (by omega) (by omega)
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (abs_nonneg _) hH)
      (Nat.cast_nonneg ((m+3).choose (j+2)): (0:ℝ)≤_)]
  rw [abs_mul,abs_of_nonneg (div_nonneg ha (by norm_num))]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans
    (mul_le_of_le_one_left (by positivity) (by linarith))

lemma gaussianRowComposition_all_jets {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) :
    ∀ n : ℕ, 2≤n → ∃ H : ℝ, 0≤H ∧ ∀ rs : List (ℝ × ℝ),
      (∀ r ∈ rs, 0≤r.1 ∧ r.1≤1 ∧ 0≤r.2) → gaussianStepTime rs≤Q →
      ∀ x, |iteratedDeriv n (gaussianRowComposition rs u) x|≤H := by
  classical
  let K := C+κ/(1-κ*Q)
  have hden : 0<1-κ*Q := by linarith [hu.2.2.2.2.1]
  have hK : 0≤K := add_nonneg hu.2.2.1 (div_nonneg hu.2.2.2.1 hden.le)
  obtain ⟨D,hD,hfirst⟩ := gaussian_step_slope A B C κ Q hQ hu.2.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2.1
  have hc2 (rs : List (ℝ × ℝ)) (hrs : ∀ r ∈ rs, 0≤r.1 ∧ r.1≤1 ∧ 0≤r.2)
      (hT : gaussianStepTime rs≤Q) (x : ℝ) : |iteratedDeriv 2 (gaussianRowComposition rs u) x|≤K := by
    have hb := (gaussian_step_bounds u A B C κ Q hQ hu rs hrs hT).2.2 x
    have hcap : κ/(1-κ*gaussianStepTime rs)≤κ/(1-κ*Q) :=
      div_le_div_of_nonneg_left hu.2.2.2.1 hden
        (by nlinarith [mul_le_mul_of_nonneg_left hT hu.2.2.2.1])
    simp only [iteratedDeriv_succ,iteratedDeriv_zero]
    rw [abs_le]
    dsimp [K]
    constructor <;> linarith [hb.2.1,hb.2.2,hu.2.2.1,div_nonneg hu.2.2.2.1 hden.le]
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases heq : n=2
    · subst n; exact ⟨K,hK,hc2⟩
    obtain ⟨m,rfl⟩ : ∃ m,n=m+3 := ⟨n-3,by omega⟩
    have hh : ∀ k, ∃ H : ℝ, 0≤H ∧ (2≤k → k < m+3 → ∀ rs : List (ℝ × ℝ),
        (∀ r ∈ rs,0≤r.1 ∧ r.1≤1 ∧ 0≤r.2) → gaussianStepTime rs≤Q →
        ∀ x,|iteratedDeriv k (gaussianRowComposition rs u) x|≤H) := by
      intro k
      by_cases hk : 2≤k ∧ k < m+3
      · obtain ⟨H,hH,hB⟩ := ih k hk.2 hk.1
        exact ⟨H,hH,fun _ _ => hB⟩
      · exact ⟨0,le_rfl,fun hk' hkn => (hk ⟨hk',hkn⟩).elim⟩
    choose H hH hbound using hh
    let V := ∑ k ∈ Finset.range (m+3), H k
    have hV : 0≤V := Finset.sum_nonneg (fun i _ => hH i)
    have hlow (k : ℕ) (hk : 3≤k) (hkn : k < m+3) (rs : List (ℝ × ℝ))
        (hrs : ∀ r ∈ rs,0≤r.1 ∧ r.1≤1 ∧ 0≤r.2) (hT : gaussianStepTime rs≤Q) (x : ℝ) :
        |iteratedDeriv k (gaussianRowComposition rs u) x|≤V :=
      (hbound k (by omega) hkn rs hrs hT x).trans
        (Finset.single_le_sum (fun i _ => hH i) (Finset.mem_range.mpr hkn))
    obtain ⟨H₀,h₀⟩ := hu.2.2.2.2.2.1 (m+3) (by omega)
    have hH₀ : 0≤H₀ := (abs_nonneg _).trans (h₀ 0)
    let S := (∑ j ∈ Finset.range m, ((m+3).choose (j+2):ℝ))*V^2
    have hS : 0≤S := mul_nonneg (Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)) (sq_nonneg _)
    have hstep : ∀ rs : List (ℝ × ℝ), (∀ r ∈ rs,0≤r.1 ∧ r.1≤1 ∧ 0≤r.2) →
        gaussianStepTime rs≤Q → ∀ x, |iteratedDeriv (m+3) (gaussianRowComposition rs u) x|≤
        (H₀+S*gaussianStepTime rs)*Real.exp (((m:ℝ)+3)*K*gaussianStepTime rs) := by
      intro rs
      induction rs with
      | nil => intro _ _ x; simpa [gaussianRowComposition,gaussianStepTime] using h₀ x
      | cons r rs ihr =>
        intro hrs hsum
        have hr := hrs r (by simp)
        have ht : ∀ v ∈ rs,0≤v.1 ∧ v.1≤1 ∧ 0≤v.2 := fun v hv => hrs v (by simp [hv])
        have htime : gaussianStepTime (r::rs)=r.2+gaussianStepTime rs := by simp [gaussianStepTime]
        rw [htime] at hsum ⊢
        have htq : gaussianStepTime rs≤Q := by linarith [hr.2.2]
        have htn : 0≤gaussianStepTime rs := gaussianStepTime_nonneg (fun r hr => (ht r hr).2.2)
        have htw := gaussianRowComposition_twice hQ hu ht htq
        have hsp := gaussianRowComposition_smoothPolynomial hQ hu rs ht htq
        have hinitial := ihr ht htq
        by_cases hz : r.2=0
        · have he : gaussianRowComposition (r::rs) u=gaussianRowComposition rs u := by
            funext x
            change gaussianRowOperator r.1 r.2 (gaussianRowComposition rs u) x=_
            rw [hz,gaussianRowOperator_zero]
          rw [he,hz,zero_add]
          exact hinitial
        · have hT : 0<r.2 := lt_of_le_of_ne hr.2.2 (Ne.symm hz)
          have hvalid (T : ℝ) (hT' : T∈Icc 0 r.2) :
              ∀ v ∈ (r.1,T)::rs,0≤v.1 ∧ v.1≤1 ∧ 0≤v.2 := by
            intro v hv
            rcases List.mem_cons.mp hv with h | h
            · subst v; exact ⟨hr.1,hr.2.1,hT'.1⟩
            · exact ht v h
          have htot (T : ℝ) (hT' : T∈Icc 0 r.2) : gaussianStepTime ((r.1,T)::rs)≤Q := by
            have hh : T+gaussianStepTime rs≤Q := by linarith [hT'.2]
            simpa [gaussianStepTime] using hh
          have hsec (T : ℝ) (hT' : T∈Icc 0 r.2) (x : ℝ) :
              deriv (deriv (gaussianRowOperator r.1 T (gaussianRowComposition rs u))) x≤K := by
            simpa only [iteratedDeriv_succ,iteratedDeriv_zero,gaussianRowComposition] using
              (le_abs_self _).trans (hc2 ((r.1,T)::rs) (hvalid T hT') (htot T hT') x)
          have hsrc (T : ℝ) (hT' : T∈Icc 0 r.2) (x : ℝ) :
              |(r.1/2)*∑ j ∈ Finset.range m, ((m+3).choose (j+2):ℝ)*
                iteratedDeriv (j+3) (gaussianRowOperator r.1 T (gaussianRowComposition rs u)) x*
                iteratedDeriv (m+2-j) (gaussianRowOperator r.1 T (gaussianRowComposition rs u)) x|≤S :=
            jet_source_bound hr.1 hr.2.1 hV (fun k hk hkn =>
              hlow k hk hkn ((r.1,T)::rs) (hvalid T hT') (htot T hT') x)
          have hbb := gaussianRowOperator_jet_bound m htw hsp hr.1 hr.2.1 hT
            (gaussianRowComposition_block_subcritical hQ hu ht hr.1 hr.2.1 hr.2.2 hsum)
            hD hK (by positivity : 0≤(H₀+S*gaussianStepTime rs)*Real.exp (((m:ℝ)+3)*K*gaussianStepTime rs)) hS
            (fun T hT' => hfirst u hu ((r.1,T)::rs) (hvalid T hT') (htot T hT')) hsec hsrc hinitial
          intro x
          have hb := hbb r.2 ⟨hT.le,le_rfl⟩ x
          have he : Real.exp (((m:ℝ)+3)*K*(r.2+gaussianStepTime rs)) =
              Real.exp (((m:ℝ)+3)*K*gaussianStepTime rs)*Real.exp (((m:ℝ)+3)*K*r.2) := by
            rw [← Real.exp_add]; congr 1; ring
          have hexp : 1≤Real.exp (((m:ℝ)+3)*K*gaussianStepTime rs) := Real.one_le_exp (by positivity)
          apply hb.trans
          rw [he]
          have hmul := mul_le_mul_of_nonneg_right hexp (mul_nonneg hS hr.2.2)
          have hh := mul_le_mul_of_nonneg_right hmul (Real.exp_nonneg (((m:ℝ)+3)*K*r.2))
          nlinarith
    refine ⟨(H₀+S*Q)*Real.exp (((m:ℝ)+3)*K*Q),by positivity,fun rs hrs hT x => ?_⟩
    have htn := gaussianStepTime_nonneg (fun r hr => (hrs r hr).2.2)
    apply (hstep rs hrs hT x).trans
    apply mul_le_mul
    · nlinarith
    · apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hT (by positivity)
    · exact Real.exp_nonneg _
    · positivity
end Higher
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming

lemma CylinderConvergence.deriv_and_differentiable {f : ℕ → ℝ → ℝ → ℝ}
    {F : ℝ → ℝ → ℝ} {S : Set ℝ} {K : ℝ}
    (hv : CylinderConvergence f F S) (hK : 0≤K)
    (hd : ∀ n t,t∈S → Differentiable ℝ (f n t) ∧ Differentiable ℝ (deriv (f n t)))
    (hb : ∀ n t,t∈S → ∀ x,|deriv (deriv (f n t)) x|≤K) :
    CylinderConvergence (fun n t => deriv (f n t)) (fun t => deriv (F t)) S ∧
      ∀ t ∈ S,Differentiable ℝ (F t) := by
  have hc : CylinderCauchy f S := fun R hR => (hv R hR).uniformCauchySeqOn
  obtain ⟨G,hG⟩ := (hc.deriv hK hd hb).exists_limit
  have hder := cylinder_limit_hasDerivAt hv hG (fun n t ht => (hd n t ht).1)
  refine ⟨fun R hR => (hG R hR).congr_right (fun p hp => (hder p.1 hp.1 p.2).deriv.symm),?_⟩
  intro t ht x
  exact (hder t ht x).differentiableAt

lemma CylinderConvergence.all_jets {f : ℕ → ℝ → ℝ → ℝ} {F : ℝ → ℝ → ℝ} {S : Set ℝ}
    (hv : CylinderConvergence f F S)
    (hs : ∀ n t,t∈S → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f n t))
    (hb : ∀ k : ℕ,2≤k → ∃ H : ℝ,0≤H ∧ ∀ n t,t∈S → ∀ x,|iteratedDeriv k (f n t) x|≤H) :
    (∀ k : ℕ, CylinderConvergence (fun n t => iteratedDeriv k (f n t))
      (fun t => iteratedDeriv k (F t)) S) ∧
    (∀ t∈S,ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F t)) ∧
    (∀ k : ℕ,2≤k → ∃ H : ℝ,0≤H ∧ ∀ t∈S,∀ x,|iteratedDeriv k (F t) x|≤H) := by
  have hd (k n : ℕ) (t : ℝ) (ht : t∈S) : Differentiable ℝ (iteratedDeriv k (f n t)) :=
    (contDiff_iff_iteratedDeriv.mp (hs n t ht)).2 k (by simp)
  have hdiff (k : ℕ) (hc : CylinderConvergence (fun n t => iteratedDeriv k (f n t))
      (fun t => iteratedDeriv k (F t)) S) :
      CylinderConvergence (fun n t => iteratedDeriv (k+1) (f n t))
        (fun t => iteratedDeriv (k+1) (F t)) S ∧
      ∀ t∈S,Differentiable ℝ (iteratedDeriv k (F t)) := by
    obtain ⟨H,hH,hbd⟩ := hb (k+2) (by omega)
    have hdx (n : ℕ) (t : ℝ) (ht : t∈S) :
        Differentiable ℝ (iteratedDeriv k (f n t)) ∧ Differentiable ℝ (deriv (iteratedDeriv k (f n t))) := by
      refine ⟨hd k n t ht,?_⟩
      simpa only [← iteratedDeriv_succ] using hd (k+1) n t ht
    have hh := hc.deriv_and_differentiable hH hdx (fun n t ht x => by
      simpa only [← iteratedDeriv_succ] using hbd n t ht x)
    simpa only [← iteratedDeriv_succ] using hh
  have hcv : ∀ k : ℕ,CylinderConvergence (fun n t => iteratedDeriv k (f n t))
      (fun t => iteratedDeriv k (F t)) S := by
    intro k
    induction k with
    | zero => simpa using hv
    | succ k ih => exact (hdiff k ih).1
  refine ⟨hcv,?_,?_⟩
  · intro t ht
    apply contDiff_of_differentiable_iteratedDeriv
    intro k _
    exact (hdiff k (hcv k)).2 t ht
  · intro k hk
    obtain ⟨H,hH,hbd⟩ := hb k hk
    refine ⟨H,hH,fun t ht x => ?_⟩
    exact le_of_tendsto ((hcv k).tendsto_at ht x).abs (Eventually.of_forall (fun n => hbd n t ht x))
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming

lemma continuousOn_all_jets {F : ℝ → ℝ → ℝ} {S : Set ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (S ×ˢ univ))
    (hs : ∀ t∈S,ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F t))
    (hb : ∀ k : ℕ,2≤k → ∃ H : ℝ,0≤H ∧ ∀ t∈S,∀ x,|iteratedDeriv k (F t) x|≤H) :
    ∀ k : ℕ, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (F p.1) p.2) (S ×ˢ univ) := by
  have hd (k : ℕ) (t : ℝ) (ht : t∈S) : Differentiable ℝ (iteratedDeriv k (F t)) :=
    (contDiff_iff_iteratedDeriv.mp (hs t ht)).2 k (by simp)
  intro k
  induction k with
  | zero => simpa using hc
  | succ k ih =>
    obtain ⟨H,hH,hbd⟩ := hb (k+2) (by omega)
    have hh := continuousOn_spatial_deriv ih
      (fun t ht => And.intro (hd k t ht) (by simpa only [←iteratedDeriv_succ] using hd (k+1) t ht))
      hH (fun t ht x => by simpa only [←iteratedDeriv_succ] using hbd t ht x)
    simpa only [←iteratedDeriv_succ] using hh

 

lemma row_variance_all_jets {A B C κ Q : ℝ} {u m : ℝ → ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q)
    (hm : ContinuousOn m (Icc 0 Q)) (hmb : ∀ t∈Icc 0 Q,0 ≤ m t ∧ m t≤1)
    {F : ℝ → ℝ → ℝ} (hF : RowClassicalVarianceSolution Q u m F) :
    (∀ t∈Icc 0 Q,ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F t)) ∧
    (∀ k : ℕ,ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (F p.1) p.2) (Icc 0 Q ×ˢ univ)) ∧
    (∀ k : ℕ,2≤k → ∃ H : ℝ,0≤H ∧ ∀ t∈Icc 0 Q,∀ x,|iteratedDeriv k (F t) x|≤H) := by
  obtain ⟨L,hL,hh⟩ := row_variance_existence A B C κ Q hQ hu.2.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2.1
  obtain ⟨G,hG,_,huniq,hconv⟩ := hh u hu m hm hmb
  obtain ⟨rs,hrs,hT,hrm⟩ := exists_gaussian_grid_approximation hQ hm hmb
  have hc : CylinderConvergence (fun n => gaussianStepPath (rs n) u) F (Icc 0 Q) := by
    intro R hR
    exact (hconv rs hrs hT hrm R hR).congr_right (fun p hp => huniq F hF p.1 hp.1 p.2)
  have hvalid (n : ℕ) (t : ℝ) (ht : t∈Icc 0 Q) :
      (∀ r∈gaussianStepRemainder (rs n) t,0≤r.1 ∧ r.1≤1 ∧ 0≤r.2) ∧
      gaussianStepTime (gaussianStepRemainder (rs n) t)≤Q := by
    obtain ⟨hv,he⟩ := gaussianStepRemainder_valid (hrs n) ht.1
    refine ⟨hv,?_⟩
    rw [he,hT,max_eq_left (by linarith [ht.2])]
    linarith [ht.1]
  have hs (n : ℕ) (t : ℝ) (ht : t∈Icc 0 Q) :
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gaussianStepPath (rs n) u t) :=
    (Higher.gaussianRowComposition_smoothPolynomial hQ hu _ (hvalid n t ht).1 (hvalid n t ht).2).smooth
  have hb : ∀ k : ℕ,2≤k → ∃ H : ℝ,0≤H ∧ ∀ n t,t∈Icc 0 Q → ∀ x,
      |iteratedDeriv k (gaussianStepPath (rs n) u t) x|≤H := by
    intro k hk
    obtain ⟨H,hH,hh⟩ := Higher.gaussianRowComposition_all_jets hQ hu k hk
    exact ⟨H,hH,fun n t ht x => hh _ (hvalid n t ht).1 (hvalid n t ht).2 x⟩
  have hj := hc.all_jets hs hb
  exact ⟨hj.2.1,continuousOn_all_jets hF.1 hj.2.1 hj.2.2,hj.2.2⟩
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace Higher

def JointSpatialSmooth (S : Set ℝ) (F : ℝ → ℝ → ℝ) : Prop :=
  (∀ t∈S,ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F t)) ∧
    ∀ n : ℕ,ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv n (F p.1) p.2) (S ×ˢ univ)

lemma JointSpatialSmooth.jet {S : Set ℝ} {F : ℝ → ℝ → ℝ}
    (hf : JointSpatialSmooth S F) (n : ℕ) :
    JointSpatialSmooth S (fun t => iteratedDeriv n (F t)) := by
  refine ⟨fun t ht => ?_,fun k => ?_⟩
  · apply contDiff_of_differentiable_iteratedDeriv
    intro k _
    simpa only [iteratedDeriv_iteratedDeriv] using (contDiff_iff_iteratedDeriv.mp (hf.1 t ht)).2 (k+n) (by simp)
  · simpa only [iteratedDeriv_iteratedDeriv] using hf.2 (k+n)

lemma JointSpatialSmooth.add {S : Set ℝ} {F G : ℝ → ℝ → ℝ}
    (hf : JointSpatialSmooth S F) (hg : JointSpatialSmooth S G) :
    JointSpatialSmooth S (fun t x => F t x+G t x) := by
  refine ⟨fun t ht => (hf.1 t ht).add (hg.1 t ht),fun n => ?_⟩
  apply ((hf.2 n).add (hg.2 n)).congr
  intro p hp
  exact iteratedDeriv_fun_add ((hf.1 p.1 hp.1).of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))).contDiffAt
    ((hg.1 p.1 hp.1).of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))).contDiffAt

lemma JointSpatialSmooth.coeff_mul {S : Set ℝ} {F : ℝ → ℝ → ℝ} {a : ℝ → ℝ}
    (hf : JointSpatialSmooth S F) (ha : ContinuousOn a S) :
    JointSpatialSmooth S (fun t x => a t*F t x) := by
  refine ⟨fun t ht => contDiff_const.mul (hf.1 t ht),fun n => ?_⟩
  apply ((ha.comp continuousOn_fst (fun p hp => hp.1)).mul (hf.2 n)).congr
  intro p hp
  exact iteratedDeriv_const_mul_field (n:=n) (x:=p.2) (a p.1) (F p.1)

lemma JointSpatialSmooth.mul {S : Set ℝ} {F G : ℝ → ℝ → ℝ}
    (hf : JointSpatialSmooth S F) (hg : JointSpatialSmooth S G) :
    JointSpatialSmooth S (fun t x => F t x*G t x) := by
  refine ⟨fun t ht => (hf.1 t ht).mul (hg.1 t ht),fun n => ?_⟩
  have hc : ContinuousOn (fun p : ℝ × ℝ => ∑ i∈Finset.range (n+1),
      (n.choose i:ℝ)*iteratedDeriv i (F p.1) p.2*iteratedDeriv (n-i) (G p.1) p.2) (S ×ˢ univ) := by
    apply continuousOn_finsetSum
    intro i _
    exact (continuousOn_const.mul (hf.2 i)).mul (hg.2 (n-i))
  apply hc.congr
  intro p hp
  exact iteratedDeriv_fun_mul ((hf.1 p.1 hp.1).of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))).contDiffAt
    ((hg.1 p.1 hp.1).of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))).contDiffAt

lemma JointSpatialSmooth.row_rhs {S : Set ℝ} {F : ℝ → ℝ → ℝ} {a m : ℝ → ℝ}
    (hf : JointSpatialSmooth S F) (ha : ContinuousOn a S) (hm : ContinuousOn m S) :
    JointSpatialSmooth S (fun t x => -(a t)*(iteratedDeriv 2 (F t) x+m t*(iteratedDeriv 1 (F t) x)^2)) := by
  have hh := ((hf.jet 2).add (((hf.jet 1).mul (hf.jet 1)).coeff_mul hm)).coeff_mul ha.neg
  simpa only [pow_two,Pi.neg_apply] using hh
end Higher
end MicroscopicJamming

end

end OAI
