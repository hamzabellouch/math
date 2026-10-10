import Mathlib
import OAI.Probability.JammingConcavity.ParabolicInterior

namespace OAI

/-! Row Variable Comparison. -/

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
namespace VariableDiffusion
lemma backward_positive_strict_compact {Q R : ℝ} (hQ : 0 < Q) (hR : 0 < R)
    {U b d a : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 Q ×ˢ Icc (-R) R))
    (hx : ∀ t ∈ Icc 0 Q, Differentiable ℝ (U t))
    (ht : ∀ t ∈ Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => U s x) (d t x) (Ici t) t)
    (ha : ∀ t ∈ Ico 0 Q, ∀ x, 0 ≤ a t x)
    (hp : ∀ t ∈ Ico 0 Q, ∀ x ∈ Ioo (-R) R, 0 < U t x →
      0 < d t x+a t x*deriv (deriv (U t)) x+b t x*deriv (U t) x)
    (hterm : ∀ x ∈ Icc (-R) R, U Q x ≤ 0)
    (hleft : ∀ t ∈ Icc 0 Q, U t (-R) ≤ 0)
    (hright : ∀ t ∈ Icc 0 Q, U t R ≤ 0) :
    ∀ t ∈ Icc 0 Q, ∀ x ∈ Icc (-R) R, U t x ≤ 0 := by
  have hne : (Icc 0 Q ×ˢ Icc (-R) R).Nonempty :=
    ⟨(0,0),⟨le_rfl,hQ.le⟩,by constructor <;> linarith⟩
  obtain ⟨p,hpS,hmax⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn hne hc
  suffices h : U p.1 p.2 ≤ 0 by
    intro t ht' x hx'
    exact (hmax (show (t,x) ∈ Icc 0 Q ×ˢ Icc (-R) R from ⟨ht',hx'⟩)).trans h
  by_contra hn
  have hpos : 0 < U p.1 p.2 := lt_of_not_ge hn
  have htQ : p.1 < Q := lt_of_le_of_ne hpS.1.2 (by
    intro he
    have hh := hterm p.2 hpS.2
    rw [← he] at hh
    exact (not_le_of_gt hpos) hh)
  have hxl : -R < p.2 := lt_of_le_of_ne hpS.2.1 (by
    intro he
    have hh := hleft p.1 hpS.1
    rw [he] at hh
    exact (not_le_of_gt hpos) hh)
  have hxr : p.2 < R := lt_of_le_of_ne hpS.2.2 (by
    intro he
    have hh := hright p.1 hpS.1
    rw [← he] at hh
    exact (not_le_of_gt hpos) hh)
  have hxmax : IsMaxOn (U p.1) (Icc (-R) R) p.2 :=
    fun x hx' => hmax (show (p.1,x) ∈ Icc 0 Q ×ˢ Icc (-R) R from ⟨hpS.1,hx'⟩)
  have hxlocal : IsLocalMax (U p.1) p.2 :=
    hxmax.isLocalMax (Icc_mem_nhds hxl hxr)
  have hzero := hxlocal.deriv_eq_zero
  have hsecond := localMax_second_deriv_nonpos (hx p.1 hpS.1) hxlocal
  have htmax : IsMaxOn (fun t => U t p.2) (Icc p.1 Q) p.1 :=
    fun t ht' => hmax (show (t,p.2) ∈ Icc 0 Q ×ˢ Icc (-R) R from ⟨⟨hpS.1.1.trans ht'.1,ht'.2⟩,hpS.2⟩)
  have htan : Q-p.1 ∈ posTangentConeAt (Icc p.1 Q) p.1 :=
    sub_mem_posTangentConeAt_of_segment_subset (segment_eq_Icc htQ.le ▸ Subset.rfl)
  have hd := (ht p.1 ⟨hpS.1.1,htQ⟩ p.2).mono (show Icc p.1 Q ⊆ Ici p.1 from fun _ h => h.1)
  have hnonpos : (Q-p.1)*d p.1 p.2 ≤ 0 := by
    simpa only [ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.toSpanSingleton_apply,one_apply_eq_self,smul_eq_mul] using
      htmax.isLocalMaxOn.hasFDerivWithinAt_nonpos hd htan
  have hdt : d p.1 p.2 ≤ 0 := by nlinarith [sub_pos.mpr htQ]
  have hstrict := hp p.1 ⟨hpS.1.1,htQ⟩ p.2 ⟨hxl,hxr⟩ hpos
  rw [hzero,mul_zero,add_zero] at hstrict
  have hmul := mul_nonpos_of_nonneg_of_nonpos (ha p.1 ⟨hpS.1.1,htQ⟩ p.2) hsecond
  linarith

lemma polynomial_transport_neg (n : ℕ) {K A a b x : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A)
    (ha : a ≤ A) (hb : |b| ≤ K*(1+|x|)) :
    -(4*A*(n+2)^2+4*K*(n+2)+1)*(1+x^2)^(n+2)+
      a*(2*(n+2)*(1+x^2)^(n+1)+4*(n+2)*(n+1)*x^2*(1+x^2)^n)+
      b*(2*(n+2)*x*(1+x^2)^(n+1)) < 0 := by
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have hnorm : (1+|x|)*|x| ≤ 2*(1+x^2) := by
    nlinarith [sq_abs x,sq_nonneg (|x|-1)]
  have hbx : b*x ≤ 2*K*(1+x^2) := calc
    b*x ≤ |b*x| := le_abs_self _
    _ = |b| * |x| := abs_mul _ _
    _ ≤ K*(1+|x|)*|x| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    _ ≤ 2*K*(1+x^2) := by nlinarith [mul_le_mul_of_nonneg_left hnorm hK]
  have hq : 1+x^2 ≤ (1+x^2)^2 := by nlinarith [sq_nonneg x,sq_nonneg (x^2)]
  have hxq : x^2 ≤ (1+x^2)^2 := by nlinarith [sq_nonneg (x^2)]
  have h1 := mul_le_mul_of_nonneg_left hq (show 0 ≤ 2*A*((n:ℝ)+2) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hxq (show 0 ≤ 4*A*((n:ℝ)+2)*(n+1) by positivity)
  have h3 := mul_le_mul_of_nonneg_left hbx (show 0 ≤ 2*((n:ℝ)+2)*(1+x^2) by positivity)
  have h4 := mul_le_mul_of_nonneg_right ha
    (show 0 ≤ 2*((n:ℝ)+2)*(1+x^2)+4*(n+2)*(n+1)*x^2 by positivity)
  have hneg : -(4*A*((n:ℝ)+2)^2+4*K*(n+2)+1)*(1+x^2)^2+
      a*(2*(n+2)*(1+x^2)+4*(n+2)*(n+1)*x^2)+2*(n+2)*b*x*(1+x^2) < 0 := by
    nlinarith [sq_pos_of_pos (show 0 < 1+x^2 by positivity),
      mul_nonneg (show 0≤2*A*((n:ℝ)+2) by positivity) (sq_nonneg (1+x^2))]
  have hmul := mul_neg_of_pos_of_neg (show 0 < (1+x^2)^n by positivity) hneg
  convert hmul using 1; first | rfl | (simp only [pow_add,pow_one]; ring)

lemma backward_polynomial_bound {Q K C A : ℝ} (n : ℕ) (hQ : 0 < Q) (hK : 0 ≤ K) (hA : 0 ≤ A) (hC : 0 ≤ C)
    {U b d a : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 Q ×ˢ univ))
    (hx : ∀ t ∈ Icc 0 Q, Differentiable ℝ (U t) ∧ Differentiable ℝ (deriv (U t)))
    (ht : ∀ t ∈ Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => U s x) (d t x) (Ici t) t)
    (ha : ∀ t ∈ Icc 0 Q, ∀ x, 0 ≤ a t x ∧ a t x ≤ A)
    (hb : ∀ t ∈ Icc 0 Q, ∀ x, |b t x| ≤ K*(1+|x|))
    (hg : ∀ t ∈ Icc 0 Q, ∀ x, U t x ≤ C*(1+x^2)^n)
    (hp : ∀ t ∈ Ico 0 Q, ∀ x, 0 < U t x →
      0 ≤ d t x+a t x*deriv (deriv (U t)) x+b t x*deriv (U t) x)
    (hterm : ∀ x, U Q x ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ t ∈ Icc 0 Q, ∀ x, U t x ≤ polynomialBarrier n ε (4*A*(n+2)^2+4*K*(n+2)+1) Q t x := by
  let c := 4*A*(n+2)^2+4*K*(n+2)+1
  have hcpos : 0 ≤ c := by dsimp [c]; positivity
  let V : ℝ → ℝ → ℝ := fun t x => U t x-polynomialBarrier n ε c Q t x
  let vd : ℝ → ℝ → ℝ := fun t x => d t x+c*polynomialBarrier n ε c Q t x
  have hvx (t : ℝ) (ht' : t ∈ Icc 0 Q) (x : ℝ) :
      HasDerivAt (V t) (deriv (U t) x-ε*Real.exp (c*(Q-t))*(2*(n+2)*x*(1+x^2)^(n+1))) x :=
    ((hx t ht').1 x).hasDerivAt.sub (polynomialBarrier_space n ε c Q t x)
  have hvxx (t : ℝ) (ht' : t ∈ Icc 0 Q) (x : ℝ) :
      deriv (deriv (V t)) x=deriv (deriv (U t)) x-
        ε*Real.exp (c*(Q-t))*(2*(n+2)*(1+x^2)^(n+1)+4*(n+2)*(n+1)*x^2*(1+x^2)^n) := by
    have he : deriv (V t)=fun y => deriv (U t) y-deriv (polynomialBarrier n ε c Q t) y := by
      ext y
      rw [(hvx t ht' y).deriv,(polynomialBarrier_space n ε c Q t y).deriv]
    rw [he]
    exact (((hx t ht').2 x).hasDerivAt.sub (polynomialBarrier_space2 n ε c Q t x)).deriv
  have hvtime (t : ℝ) (ht' : t ∈ Ico 0 Q) (x : ℝ) :
      HasDerivWithinAt (fun s => V s x) (vd t x) (Ici t) t := by
    convert (ht t ht' x).sub (polynomialBarrier_time n ε c Q t x).hasDerivWithinAt using 1; first | rfl | (dsimp [V,vd]; ring)
  have hvp (t : ℝ) (ht' : t ∈ Ico 0 Q) (x : ℝ) (hV : 0 < V t x) :
      0 < vd t x+a t x*deriv (deriv (V t)) x+b t x*deriv (V t) x := by
    have htcc : t ∈ Icc 0 Q := ⟨ht'.1,ht'.2.le⟩
    rw [hvxx t htcc x,(hvx t htcc x).deriv]
    have hneg := polynomial_transport_neg n hK hA (ha t htcc x).2 (hb t htcc x)
    have hneg' := mul_neg_of_pos_of_neg (mul_pos hε (Real.exp_pos (c*(Q-t)))) hneg
    have hUp : 0 < U t x := by
      have : 0 ≤ polynomialBarrier n ε c Q t x := by unfold polynomialBarrier; positivity
      dsimp [V] at hV
      linarith
    have hP := hp t ht' x hUp
    dsimp [vd,polynomialBarrier,c] at *
    nlinarith
  intro t ht' x
  let R := |x|+C/ε+1
  have hdiv : 0 ≤ C/ε := div_nonneg hC hε.le
  have hR1 : 1 ≤ R := by dsimp [R]; linarith [abs_nonneg x]
  have hR : 0 < R := by linarith
  have hxR : x ∈ Icc (-R) R := by
    dsimp [R]; constructor <;> linarith [le_abs_self x,neg_abs_le x]
  have hCR : C ≤ ε*(1+R^2) := by
    have hr : C/ε ≤ 1+R^2 := by dsimp [R] at hR1 ⊢; nlinarith [abs_nonneg x,sq_nonneg R]
    have hh := (div_le_iff₀ hε).mp hr
    nlinarith
  have hCR2 : C ≤ ε*(1+R^2)^2 := hCR.trans (mul_le_mul_of_nonneg_left
    (by nlinarith [sq_nonneg R,sq_nonneg (R^2)]) hε.le)
  have hB (s : ℝ) (hs : s ∈ Icc 0 Q) :
      C*(1+R^2)^n ≤ polynomialBarrier n ε c Q s R := by
    have he : 1 ≤ Real.exp (c*(Q-s)) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hcpos (sub_nonneg.mpr hs.2))
    calc
      C*(1+R^2)^n ≤ (ε*(1+R^2)^2)*(1+R^2)^n := mul_le_mul_of_nonneg_right hCR2 (by positivity)
      _ = ε*(1+R^2)^(n+2) := by rw [pow_add]; ring
      _ ≤ Real.exp (c*(Q-s))*(ε*(1+R^2)^(n+2)) := le_mul_of_one_le_left (by positivity) he
      _ = _ := by unfold polynomialBarrier; ring
  have hVc : ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2) (Icc 0 Q ×ˢ Icc (-R) R) := by
    apply (hc.mono (by intro p hp'; exact ⟨hp'.1,mem_univ _⟩)).sub
    have hh : Continuous (fun p : ℝ × ℝ => polynomialBarrier n ε c Q p.1 p.2) := by
      unfold polynomialBarrier
      fun_prop
    exact hh.continuousOn
  have hcomp := backward_positive_strict_compact (b := b) (a := a) hQ hR hVc
    (fun s hs y => (hvx s hs y).differentiableAt) hvtime (fun t ht x => (ha t ⟨ht.1,ht.2.le⟩ x).1) (fun s hs y _ => hvp s hs y)
    (fun y _ => by
      dsimp [V]
      have hn : 0 ≤ polynomialBarrier n ε c Q Q y := by unfold polynomialBarrier; positivity
      linarith [hterm y])
    (fun s hs => by
      dsimp [V]
      have hh := hg s hs (-R)
      have hh' := hB s hs
      simp only [neg_sq] at hh
      have he : polynomialBarrier n ε c Q s (-R)=polynomialBarrier n ε c Q s R := by simp [polynomialBarrier]
      rw [he]
      linarith)
    (fun s hs => by dsimp [V]; linarith [hg s hs R,hB s hs])
  have hh := hcomp t ht' x hxR
  dsimp [V] at hh
  linarith

lemma backward_polynomial_comparison {Q K A : ℝ} (hQ : 0 < Q) (hK : 0 ≤ K) (hA : 0 ≤ A)
    {U b d a : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 Q ×ˢ univ))
    (hx : ∀ t ∈ Icc 0 Q, Differentiable ℝ (U t) ∧ Differentiable ℝ (deriv (U t)))
    (ht : ∀ t ∈ Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => U s x) (d t x) (Ici t) t)
    (ha : ∀ t ∈ Icc 0 Q, ∀ x, 0 ≤ a t x ∧ a t x ≤ A)
    (hb : ∀ t ∈ Icc 0 Q, ∀ x, |b t x| ≤ K*(1+|x|))
    (hg : Higher.UniformPolynomialGrowth (Icc 0 Q) U)
    (hp : ∀ t ∈ Ico 0 Q, ∀ x, 0 < U t x →
      0 ≤ d t x+a t x*deriv (deriv (U t)) x+b t x*deriv (U t) x)
    (hterm : ∀ x, U Q x ≤ 0) :
    ∀ t ∈ Icc 0 Q, ∀ x, U t x ≤ 0 := by
  obtain ⟨n,C,hC,hg⟩ := hg
  have hg' (t : ℝ) (ht' : t ∈ Icc 0 Q) (x : ℝ) : U t x ≤ (C*2^n)*(1+x^2)^n := calc
    U t x ≤ |U t x| := le_abs_self _
    _ ≤ C*(1+|x|)^n := hg t ht' x
    _ ≤ C*(2*(1+x^2))^n := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (by nlinarith [sq_abs x,sq_nonneg (|x|-1)]) n) hC
    _ = _ := by rw [mul_pow]; ring
  intro t ht' x
  by_contra hn
  have hpos : 0 < U t x := lt_of_not_ge hn
  let M := Real.exp ((4*A*(n+2)^2+4*K*(n+2)+1)*(Q-t))*(1+x^2)^(n+2)
  have hM : 0 < M := by dsimp [M]; positivity
  let ε := U t x/(2*M)
  have hε : 0 < ε := div_pos hpos (by positivity)
  have hh := backward_polynomial_bound n hQ hK hA (show 0 ≤ C*2^n by positivity) hc hx ht ha hb hg' hp hterm hε t ht' x
  have he : polynomialBarrier n ε (4*A*(n+2)^2+4*K*(n+2)+1) Q t x=U t x/2 := by
    dsimp only [polynomialBarrier]
    rw [mul_assoc]
    change (U t x/(2*M))*M=U t x/2
    field_simp
  rw [he] at hh
  linarith

end VariableDiffusion
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace VariableDiffusion
lemma backward_reaction_source_upper {Q K R H S A : ℝ} (hQ : 0 < Q) (hK : 0 ≤ K) (hA : 0 ≤ A) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    {U b d r a : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 Q ×ˢ univ))
    (hx : ∀ t ∈ Icc 0 Q, Differentiable ℝ (U t) ∧ Differentiable ℝ (deriv (U t)))
    (ht : ∀ t ∈ Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => U s x) (d t x) (Ici t) t)
    (ha : ∀ t ∈ Icc 0 Q, ∀ x, 0 ≤ a t x ∧ a t x ≤ A)
    (hb : ∀ t ∈ Icc 0 Q, ∀ x, |b t x| ≤ K*(1+|x|))
    (hg : Higher.UniformPolynomialGrowth (Icc 0 Q) U)
    (hr : ∀ t ∈ Ico 0 Q, ∀ x, r t x ≤ R)
    (hp : ∀ t ∈ Ico 0 Q, ∀ x,
      -S ≤ d t x+a t x*deriv (deriv (U t)) x+b t x*deriv (U t) x+r t x*U t x)
    (hterm : ∀ x, U Q x ≤ H) :
    ∀ t ∈ Icc 0 Q, ∀ x, U t x ≤ (H+S*(Q-t))*Real.exp (R*(Q-t)) := by
  let E : ℝ → ℝ := fun t => Real.exp (R*(t-Q))
  let V : ℝ → ℝ → ℝ := fun t x => E t*U t x-(H+S*(Q-t))
  let vd : ℝ → ℝ → ℝ := fun t x => E t*(d t x+R*U t x)+S
  have hE (t : ℝ) : HasDerivAt E (R*E t) t := by
    convert (((hasDerivAt_id t).sub_const Q).const_mul R).exp using 1 <;> first | rfl | (dsimp [E]; ring)
  have hEc : Continuous E := continuous_iff_continuousAt.mpr (fun t => (hE t).continuousAt)
  have hEp (t : ℝ) : 0 < E t := Real.exp_pos _
  have hEl (t : ℝ) (ht' : t ∈ Icc 0 Q) : E t ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hR (sub_nonpos.mpr ht'.2))
  have hvx (t : ℝ) (ht' : t ∈ Icc 0 Q) (x : ℝ) :
      HasDerivAt (V t) (E t*deriv (U t) x) x :=
    (((hx t ht').1 x).hasDerivAt.const_mul (E t)).sub_const (H+S*(Q-t))
  have hvxx (t : ℝ) (ht' : t ∈ Icc 0 Q) (x : ℝ) :
      HasDerivAt (deriv (V t)) (E t*deriv (deriv (U t)) x) x := by
    have he : deriv (V t)=fun y => E t*deriv (U t) y := funext (fun y => (hvx t ht' y).deriv)
    rw [he]
    exact ((hx t ht').2 x).hasDerivAt.const_mul (E t)
  have hvtime (t : ℝ) (ht' : t ∈ Ico 0 Q) (x : ℝ) :
      HasDerivWithinAt (fun s => V s x) (vd t x) (Ici t) t := by
    have hW : HasDerivAt (fun s : ℝ => H+S*(Q-s)) (-S) t := by
      convert (HasDerivAt.const_add H (((hasDerivAt_const t Q).sub (hasDerivAt_id t)).const_mul S)) using 1 <;> first | rfl | ring
    convert ((hE t).hasDerivWithinAt.mul (ht t ht' x)).sub hW.hasDerivWithinAt using 1;
      first | rfl | (dsimp [vd]; ring)
  have hWnon (t : ℝ) (ht' : t ∈ Icc 0 Q) : 0 ≤ H+S*(Q-t) := by
    have := sub_nonneg.mpr ht'.2
    positivity
  have hWle (t : ℝ) (ht' : t ∈ Icc 0 Q) : H+S*(Q-t) ≤ H+S*Q := by nlinarith [ht'.1]
  have hvg : Higher.UniformPolynomialGrowth (Icc 0 Q) V := by
    obtain ⟨n,C,hC,hg⟩ := hg
    refine ⟨n,C+H+S*Q,by positivity,fun t ht' x => ?_⟩
    have he := mul_le_mul_of_nonneg_right (hEl t ht') (abs_nonneg (U t x))
    have hp1 : 1 ≤ (1+|x|)^n := one_le_pow₀ (by linarith [abs_nonneg x])
    calc
      |V t x| ≤ |E t*U t x|+|H+S*(Q-t)| := abs_sub _ _
      _ = E t*|U t x|+(H+S*(Q-t)) := by rw [abs_mul,abs_of_pos (hEp t),abs_of_nonneg (hWnon t ht')]
      _ ≤ |U t x|+(H+S*Q) := by simpa only [one_mul] using add_le_add he (hWle t ht')
      _ ≤ C*(1+|x|)^n+(H+S*Q)*(1+|x|)^n :=
        add_le_add (hg t ht' x) (le_mul_of_one_le_right (by positivity) hp1)
      _ = _ := by ring
  have hvc : ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2) (Icc 0 Q ×ˢ univ) :=
    ((hEc.comp continuous_fst).continuousOn.mul hc).sub
      (continuousOn_const.add (continuousOn_const.mul (continuousOn_const.sub continuousOn_fst)))
  have hcomp := backward_polynomial_comparison hQ hK hA hvc
    (fun t ht' => ⟨fun x => (hvx t ht' x).differentiableAt,fun x => (hvxx t ht' x).differentiableAt⟩)
    hvtime ha hb hvg (fun t ht' x hpos => ?_) (fun x => ?_)
  · intro t ht' x
    have h := hcomp t ht' x
    dsimp [V] at h
    have hexp : E t*Real.exp (R*(Q-t))=1 := by rw [← Real.exp_add]; convert Real.exp_zero using 1; congr 1; ring
    have hh := mul_le_mul_of_nonneg_right (show E t*U t x ≤ H+S*(Q-t) by linarith) (Real.exp_nonneg (R*(Q-t)))
    calc
      U t x = (E t*Real.exp (R*(Q-t)))*U t x := by rw [hexp,one_mul]
      _ = E t*U t x*Real.exp (R*(Q-t)) := by ring
      _ ≤ _ := hh
  · rw [(hvxx t ⟨ht'.1,ht'.2.le⟩ x).deriv,(hvx t ⟨ht'.1,ht'.2.le⟩ x).deriv]
    have hpp := hp t ht' x
    have hrp := hr t ht' x
    have hUp : 0 ≤ E t*U t x := by dsimp [V] at hpos; linarith [hWnon t ⟨ht'.1,ht'.2.le⟩]
    have hnn := mul_nonneg (sub_nonneg.mpr hrp) hUp
    dsimp [vd]
    calc
      _ = E t*(d t x+a t x*deriv (deriv (U t)) x+b t x*deriv (U t) x+r t x*U t x)+
          (R-r t x)*(E t*U t x)+S := by ring
      _ ≥ 0 := by
        have hh := mul_le_mul_of_nonneg_left hpp (hEp t).le
        have he := mul_le_mul_of_nonneg_right (hEl t ⟨ht'.1,ht'.2.le⟩) hS
        nlinarith
  · dsimp [V,E]
    simp only [sub_self,mul_zero,Real.exp_zero,one_mul,add_zero]
    exact sub_nonpos.mpr (hterm x)

lemma backward_reaction_source_bound {Q K R H S A : ℝ} (hQ : 0 < Q) (hK : 0 ≤ K) (hA : 0 ≤ A) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    {U b d r a : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 Q ×ˢ univ))
    (hx : ∀ t ∈ Icc 0 Q, Differentiable ℝ (U t) ∧ Differentiable ℝ (deriv (U t)))
    (ht : ∀ t ∈ Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => U s x) (d t x) (Ici t) t)
    (ha : ∀ t ∈ Icc 0 Q, ∀ x, 0 ≤ a t x ∧ a t x ≤ A)
    (hb : ∀ t ∈ Icc 0 Q, ∀ x, |b t x| ≤ K*(1+|x|))
    (hg : Higher.UniformPolynomialGrowth (Icc 0 Q) U)
    (hr : ∀ t ∈ Ico 0 Q, ∀ x, r t x ≤ R)
    (hp : ∀ t ∈ Ico 0 Q, ∀ x,
      |d t x+a t x*deriv (deriv (U t)) x+b t x*deriv (U t) x+r t x*U t x| ≤ S)
    (hterm : ∀ x, |U Q x| ≤ H) :
    ∀ t ∈ Icc 0 Q, ∀ x, |U t x| ≤ (H+S*(Q-t))*Real.exp (R*(Q-t)) := by
  have hupper := backward_reaction_source_upper hQ hK hA hR hH hS hc hx ht ha hb hg hr (fun t ht x => (abs_le.mp (hp t ht x)).1)
    (fun x => (le_abs_self _).trans (hterm x))
  have hn1 (t : ℝ) (ht' : t ∈ Icc 0 Q) : deriv (fun x => -U t x)=fun x => -deriv (U t) x := by
    funext x; exact ((hx t ht').1 x).hasDerivAt.neg.deriv
  have hn2 (t : ℝ) (ht' : t ∈ Icc 0 Q) : deriv (deriv (fun x => -U t x))=fun x => -deriv (deriv (U t)) x := by
    rw [hn1 t ht']; funext x; exact ((hx t ht').2 x).hasDerivAt.neg.deriv
  have hneg := backward_reaction_source_upper (U:=fun t x => -U t x) (d:=fun t x => -d t x)
    hQ hK hA hR hH hS hc.neg
    (fun t ht' => ⟨(hx t ht').1.neg,by rw [hn1 t ht']; exact (hx t ht').2.neg⟩)
    (fun t ht' x => (ht t ht' x).neg) ha hb
    (by simpa only [neg_one_mul] using hg.const_mul (-1)) hr
    (fun t ht' x => by rw [hn2 t ⟨ht'.1,ht'.2.le⟩,hn1 t ⟨ht'.1,ht'.2.le⟩]; linarith [(abs_le.mp (hp t ht' x)).2])
    (fun x => (neg_le_abs _).trans (hterm x))
  intro t ht' x
  rw [abs_le]
  exact ⟨by linarith [hneg t ht' x],hupper t ht' x⟩

end VariableDiffusion
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace VariableDiffusion

lemma polynomialBarrier_growth (n : ℕ) (e c Q : ℝ) :
    Higher.UniformPolynomialGrowth (Icc 0 Q) (polynomialBarrier n e c Q) := by
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f:=fun t : ℝ => e*Real.exp (c*(Q-t))) (by fun_prop)
  refine ⟨2*(n+2),max B 0,le_max_right _ _,fun t ht x => ?_⟩
  have hp : 1+x^2 ≤ (1+|x|)^2 := by nlinarith [sq_abs x,abs_nonneg x]
  have hb := hB t ht
  rw [Real.norm_eq_abs] at hb
  calc
    |polynomialBarrier n e c Q t x| = |e*Real.exp (c*(Q-t))| *(1+x^2)^(n+2) := by
      unfold polynomialBarrier; rw [abs_mul,abs_of_nonneg (show 0 ≤ (1+x^2)^(n+2) by positivity)]
    _ ≤ max B 0*((1+|x|)^2)^(n+2) := mul_le_mul (hb.trans (le_max_left _ _))
      (pow_le_pow_left₀ (by positivity) hp _) (by positivity) (le_max_right _ _)
    _ = _ := by rw [←pow_mul]

lemma backward_polynomial_source_upper {Q K R H S A : ℝ} (n : ℕ)
    (hQ : 0 < Q) (hK : 0 ≤ K) (hA : 0 ≤ A) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    {U b d r a : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 Q ×ˢ univ))
    (hx : ∀ t ∈ Icc 0 Q, Differentiable ℝ (U t) ∧ Differentiable ℝ (deriv (U t)))
    (ht : ∀ t ∈ Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => U s x) (d t x) (Ici t) t)
    (ha : ∀ t ∈ Icc 0 Q, ∀ x, 0 ≤ a t x ∧ a t x ≤ A)
    (hb : ∀ t ∈ Icc 0 Q, ∀ x, |b t x| ≤ K*(1+|x|))
    (hg : Higher.UniformPolynomialGrowth (Icc 0 Q) U)
    (hr : ∀ t ∈ Ico 0 Q, ∀ x, r t x ≤ R)
    (hp : ∀ t ∈ Ico 0 Q, ∀ x,
      -S*(1+x^2)^(n+2) ≤ d t x+a t x*deriv (deriv (U t)) x+b t x*deriv (U t) x+r t x*U t x)
    (hterm : ∀ x, U Q x ≤ H*(1+x^2)^(n+2)) :
    ∀ t ∈ Icc 0 Q, ∀ x, U t x ≤
      polynomialBarrier n (H+S) (R+(4*A*(n+2)^2+4*K*(n+2)+1)+1) Q t x := by
  let c := 4*A*(n+2)^2+4*K*(n+2)+1
  let g := R+c+1
  let W := polynomialBarrier n (H+S) g Q
  let V := fun t x => U t x-W t x
  let vd := fun t x => d t x+g*W t x
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hg0 : 0 ≤ g := by dsimp [g]; positivity
  have hWx (t x : ℝ) := polynomialBarrier_space n (H+S) g Q t x
  have hWxx (t x : ℝ) := polynomialBarrier_space2 n (H+S) g Q t x
  have hvx (t : ℝ) (htt : t∈Icc 0 Q) (x : ℝ) :
      HasDerivAt (V t) (deriv (U t) x-deriv (W t) x) x := by
    exact ((hx t htt).1 x).hasDerivAt.sub (hWx t x).differentiableAt.hasDerivAt
  have hvxx (t : ℝ) (htt : t∈Icc 0 Q) (x : ℝ) :
      HasDerivAt (deriv (V t)) (deriv (deriv (U t)) x-deriv (deriv (W t)) x) x := by
    have he : deriv (V t)=fun y => deriv (U t) y-deriv (W t) y := funext (fun y => (hvx t htt y).deriv)
    rw [he]
    exact ((hx t htt).2 x).hasDerivAt.sub (hWxx t x).differentiableAt.hasDerivAt
  have hvt (t : ℝ) (htt : t∈Ico 0 Q) (x : ℝ) :
      HasDerivWithinAt (fun s => V s x) (vd t x) (Ici t) t := by
    convert (ht t htt x).sub (polynomialBarrier_time n (H+S) g Q t x).hasDerivWithinAt using 1;
      first | rfl | (dsimp [vd,W]; ring)
  have hWc : Continuous (fun p : ℝ × ℝ => W p.1 p.2) := by dsimp [W,polynomialBarrier]; fun_prop
  have hWP (t : ℝ) (htt : t∈Ico 0 Q) (x : ℝ) :
      -g*W t x+a t x*deriv (deriv (W t)) x+b t x*deriv (W t) x+r t x*W t x ≤ -S*(1+x^2)^(n+2) := by
    have htcc : t∈Icc 0 Q := ⟨htt.1,htt.2.le⟩
    have hn := (polynomial_transport_neg n hK hA (ha t htcc x).2 (hb t htcc x)).le
    have hm := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ (H+S)*Real.exp (g*(Q-t)) by positivity) hn
    have he : 1 ≤ Real.exp (g*(Q-t)) := Real.one_le_exp_iff.mpr (mul_nonneg hg0 (sub_nonneg.mpr htcc.2))
    have hw : S*(1+x^2)^(n+2) ≤ W t x := by
      calc
        _ ≤ (H+S)*(1+x^2)^(n+2) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ ≤ ((H+S)*(1+x^2)^(n+2))*Real.exp (g*(Q-t)) := le_mul_of_one_le_right (by positivity) he
        _ = _ := by dsimp [W,polynomialBarrier]; ring
    have hrw := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hr t htt x))
      (show 0 ≤ W t x by dsimp [W,polynomialBarrier]; positivity)
    rw [(hWx t x).deriv,(hWxx t x).deriv]
    dsimp [W,polynomialBarrier,g,c] at *
    nlinarith
  have hvp (t : ℝ) (htt : t∈Ico 0 Q) (x : ℝ) :
      -(0:ℝ) ≤ vd t x+a t x*deriv (deriv (V t)) x+b t x*deriv (V t) x+r t x*V t x := by
    rw [(hvx t ⟨htt.1,htt.2.le⟩ x).deriv,(hvxx t ⟨htt.1,htt.2.le⟩ x).deriv]
    have hh := hp t htt x
    have hw := hWP t htt x
    dsimp [vd,V]
    linarith
  have hvterm (x : ℝ) : V Q x ≤ 0 := by
    have hh := hterm x
    dsimp [V,W,polynomialBarrier]
    simp only [sub_self,mul_zero,Real.exp_zero,mul_one]
    nlinarith [show 0 ≤ (1+x^2)^(n+2) by positivity]
  have hh := backward_reaction_source_upper hQ hK hA hR (le_refl 0) (le_refl 0)
    (hc.sub hWc.continuousOn)
    (fun t htt => ⟨fun x => (hvx t htt x).differentiableAt,fun x => (hvxx t htt x).differentiableAt⟩)
    hvt ha hb (hg.sub (polynomialBarrier_growth n (H+S) g Q)) hr hvp hvterm
  intro t htt x
  have hv := hh t htt x
  simp only [zero_mul,add_zero] at hv
  dsimp [V] at hv
  exact sub_nonpos.mp hv

lemma backward_polynomial_source_bound {Q K R H S A : ℝ} (n : ℕ)
    (hQ : 0 < Q) (hK : 0 ≤ K) (hA : 0 ≤ A) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    {U b d r a : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 Q ×ˢ univ))
    (hx : ∀ t ∈ Icc 0 Q, Differentiable ℝ (U t) ∧ Differentiable ℝ (deriv (U t)))
    (ht : ∀ t ∈ Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => U s x) (d t x) (Ici t) t)
    (ha : ∀ t ∈ Icc 0 Q, ∀ x, 0 ≤ a t x ∧ a t x ≤ A)
    (hb : ∀ t ∈ Icc 0 Q, ∀ x, |b t x| ≤ K*(1+|x|))
    (hg : Higher.UniformPolynomialGrowth (Icc 0 Q) U)
    (hr : ∀ t ∈ Ico 0 Q, ∀ x, r t x ≤ R)
    (hp : ∀ t ∈ Ico 0 Q, ∀ x,
      |d t x+a t x*deriv (deriv (U t)) x+b t x*deriv (U t) x+r t x*U t x| ≤ S*(1+x^2)^(n+2))
    (hterm : ∀ x, |U Q x| ≤ H*(1+x^2)^(n+2)) :
    ∀ t ∈ Icc 0 Q, ∀ x, |U t x| ≤
      polynomialBarrier n (H+S) (R+(4*A*(n+2)^2+4*K*(n+2)+1)+1) Q t x := by
  have hupper := backward_polynomial_source_upper n hQ hK hA hR hH hS hc hx ht ha hb hg hr
    (fun t ht x => by linarith [(abs_le.mp (hp t ht x)).1])
    (fun x => (le_abs_self _).trans (hterm x))
  have hn1 (t : ℝ) (htt : t∈Icc 0 Q) : deriv (fun x => -U t x)=fun x => -deriv (U t) x := by
    funext x; exact ((hx t htt).1 x).hasDerivAt.neg.deriv
  have hn2 (t : ℝ) (htt : t∈Icc 0 Q) : deriv (deriv (fun x => -U t x))=fun x => -deriv (deriv (U t)) x := by
    rw [hn1 t htt]; funext x; exact ((hx t htt).2 x).hasDerivAt.neg.deriv
  have hneg := backward_polynomial_source_upper (U:=fun t x => -U t x) (d:=fun t x => -d t x)
    n hQ hK hA hR hH hS hc.neg
    (fun t htt => ⟨(hx t htt).1.neg,by rw [hn1 t htt]; exact (hx t htt).2.neg⟩)
    (fun t htt x => (ht t htt x).neg) ha hb
    (by simpa only [neg_one_mul] using hg.const_mul (-1)) hr
    (fun t htt x => by rw [hn2 t ⟨htt.1,htt.2.le⟩,hn1 t ⟨htt.1,htt.2.le⟩]; linarith [(abs_le.mp (hp t htt x)).2])
    (fun x => (neg_le_abs _).trans (hterm x))
  intro t htt x
  rw [abs_le]
  exact ⟨by linarith [hneg t htt x],hupper t htt x⟩
end VariableDiffusion
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace Higher

def FamilyGrowth {ι : Type*} (P : ι → Prop) (T : Set ℝ) (F : ι → ℝ → ℝ → ℝ) : Prop :=
  ∃ n : ℕ,∃ C : ℝ,0≤C ∧ ∀ i,P i → ∀ t∈T,∀ x,|F i t x|≤C*(1+|x|)^n

lemma FamilyGrowth.const {ι : Type*} (P : ι → Prop) (T : Set ℝ) (c : ℝ) :
    FamilyGrowth P T (fun _ _ _ => c) :=
  ⟨0,|c|,abs_nonneg _,fun _ _ _ _ _ => by simp⟩

lemma FamilyGrowth.of_bound {ι : Type*} {P : ι → Prop} {T : Set ℝ} {F : ι → ℝ → ℝ → ℝ}
    {C : ℝ} (hC : 0≤C) (hF : ∀ i,P i → ∀ t∈T,∀ x,|F i t x|≤C) : FamilyGrowth P T F :=
  ⟨0,C,hC,fun i hi t ht x => by simpa using hF i hi t ht x⟩

lemma FamilyGrowth.of_linear_bound {ι : Type*} {P : ι → Prop} {T : Set ℝ} {F : ι → ℝ → ℝ → ℝ}
    {C : ℝ} (hC : 0≤C) (hF : ∀ i,P i → ∀ t∈T,∀ x,|F i t x|≤C*(1+|x|)) : FamilyGrowth P T F :=
  ⟨1,C,hC,fun i hi t ht x => by simpa using hF i hi t ht x⟩

lemma FamilyGrowth.of_quadratic_bound {ι : Type*} {P : ι → Prop} {T : Set ℝ} {F : ι → ℝ → ℝ → ℝ}
    {C : ℝ} (hC : 0≤C) (hF : ∀ i,P i → ∀ t∈T,∀ x,|F i t x|≤C*(1+x^2)) : FamilyGrowth P T F := by
  refine ⟨2,C,hC,fun i hi t ht x => (hF i hi t ht x).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC
  nlinarith [sq_abs x,abs_nonneg x]

lemma FamilyGrowth.comp {ι κ : Type*} {P : ι → Prop} {R : κ → Prop} {T : Set ℝ}
    {F : ι → ℝ → ℝ → ℝ} (hf : FamilyGrowth P T F) (g : κ → ι) (hg : ∀ i,R i → P (g i)) :
    FamilyGrowth R T (fun i => F (g i)) := by
  obtain ⟨n,C,hC,hf⟩ := hf
  exact ⟨n,C,hC,fun i hi => hf (g i) (hg i hi)⟩

lemma FamilyGrowth.add {ι : Type*} {P : ι → Prop} {T : Set ℝ} {F G : ι → ℝ → ℝ → ℝ}
    (hf : FamilyGrowth P T F) (hg : FamilyGrowth P T G) :
    FamilyGrowth P T (fun i t x => F i t x+G i t x) := by
  obtain ⟨n,C,hC,hf⟩ := hf
  obtain ⟨m,D,hD,hg⟩ := hg
  refine ⟨max n m,C+D,by positivity,fun i hi t ht x => ?_⟩
  calc
    |F i t x+G i t x| ≤ |F i t x|+|G i t x| := abs_add_le _ _
    _ ≤ C*(1+|x|)^n+D*(1+|x|)^m := add_le_add (hf i hi t ht x) (hg i hi t ht x)
    _ ≤ C*(1+|x|)^(max n m)+D*(1+|x|)^(max n m) := add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [abs_nonneg x]) (le_max_left _ _)) hC)
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [abs_nonneg x]) (le_max_right _ _)) hD)
    _ = _ := by ring

lemma FamilyGrowth.mul {ι : Type*} {P : ι → Prop} {T : Set ℝ} {F G : ι → ℝ → ℝ → ℝ}
    (hf : FamilyGrowth P T F) (hg : FamilyGrowth P T G) :
    FamilyGrowth P T (fun i t x => F i t x*G i t x) := by
  obtain ⟨n,C,hC,hf⟩ := hf
  obtain ⟨m,D,hD,hg⟩ := hg
  refine ⟨n+m,C*D,by positivity,fun i hi t ht x => ?_⟩
  calc
    |F i t x*G i t x| = |F i t x| * |G i t x| := abs_mul _ _
    _ ≤ C*(1+|x|)^n*(D*(1+|x|)^m) := mul_le_mul (hf i hi t ht x) (hg i hi t ht x) (abs_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

lemma FamilyGrowth.const_mul {ι : Type*} {P : ι → Prop} {T : Set ℝ} {F : ι → ℝ → ℝ → ℝ}
    (hf : FamilyGrowth P T F) (c : ℝ) : FamilyGrowth P T (fun i t x => c*F i t x) :=
  (FamilyGrowth.const P T c).mul hf

lemma FamilyGrowth.sub {ι : Type*} {P : ι → Prop} {T : Set ℝ} {F G : ι → ℝ → ℝ → ℝ}
    (hf : FamilyGrowth P T F) (hg : FamilyGrowth P T G) :
    FamilyGrowth P T (fun i t x => F i t x-G i t x) := by
  simpa only [neg_one_mul,sub_eq_add_neg] using hf.add (hg.const_mul (-1))

lemma FamilyGrowth.congr {ι : Type*} {P : ι → Prop} {T : Set ℝ} {F G : ι → ℝ → ℝ → ℝ}
    (hf : FamilyGrowth P T F) (he : ∀ i,P i → ∀ t∈T,∀ x,F i t x=G i t x) : FamilyGrowth P T G := by
  obtain ⟨n,C,hC,hf⟩ := hf
  exact ⟨n,C,hC,fun i hi t ht x => by rw [←he i hi t ht x]; exact hf i hi t ht x⟩

lemma FamilyGrowth.finset_sum {ι κ : Type*} {P : ι → Prop} {T : Set ℝ}
    (s : Finset κ) {F : κ → ι → ℝ → ℝ → ℝ}
    (hf : ∀ k∈s,FamilyGrowth P T (F k)) : FamilyGrowth P T (fun i t x => ∑ k∈s,F k i t x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using FamilyGrowth.const P T 0
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using (hf a (Finset.mem_insert_self _ _)).add
      (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))

lemma FamilyGrowth.individual {ι : Type*} {P : ι → Prop} {T : Set ℝ} {F : ι → ℝ → ℝ → ℝ}
    (hf : FamilyGrowth P T F) {i : ι} (hi : P i) : UniformPolynomialGrowth T (F i) := by
  obtain ⟨n,C,hC,hf⟩ := hf
  exact ⟨n,C,hC,hf i hi⟩

lemma FamilyGrowth.polynomial_source {ι : Type*} {P : ι → Prop} {T : Set ℝ} {F : ι → ℝ → ℝ → ℝ}
    (hf : FamilyGrowth P T F) :
    ∃ n : ℕ,∃ C : ℝ,0≤C ∧ ∀ i,P i → ∀ t∈T,∀ x,|F i t x|≤C*(1+x^2)^(n+2) := by
  obtain ⟨n,C,hC,hf⟩ := hf
  refine ⟨n,C*2^n,by positivity,fun i hi t ht x => ?_⟩
  have hp : 1+|x| ≤ 2*(1+x^2) := by nlinarith [sq_abs x,sq_nonneg (|x|-1)]
  calc
    _ ≤ C*(1+|x|)^n := hf i hi t ht x
    _ ≤ C*(2*(1+x^2))^n := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hp _) hC
    _ = (C*2^n)*(1+x^2)^n := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by nlinarith [sq_nonneg x]) (by omega)) (by positivity)

end Higher
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace Higher

def heatDomain : Set (ℝ × ℝ) := Ioi (0:ℝ) ×ˢ univ
lemma heatDomain_open : IsOpen heatDomain := isOpen_Ioi.prod isOpen_univ

lemma heatJet_hasFDeriv {u : ℝ → ℝ} (hu : SmoothPolynomial u) (n : ℕ)
    {p : ℝ × ℝ} (hp : p ∈ heatDomain) :
    HasFDerivAt (fun p : ℝ × ℝ => gaussianHeat (iteratedDeriv n u) p.1 p.2)
      (((1/2:ℝ)*gaussianHeat (iteratedDeriv (n+2) u) p.1 p.2) •
        ContinuousLinearMap.fst ℝ ℝ ℝ +
        gaussianHeat (iteratedDeriv (n+1) u) p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  have htime := heat_jointly_continuous (hu.continuous (n+2)) (hu.growth (n+2))
  have hspace := heat_jointly_continuous (hu.continuous (n+1)) (hu.growth (n+1))
  have hh := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (E₁ := ℝ) (E₂ := ℝ) (F := ℝ)
    (f := fun t x => gaussianHeat (iteratedDeriv n u) t x)
    (f₁ := fun t x => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      ((1/2:ℝ)*gaussianHeat (iteratedDeriv (n+2) u) t x))
    (f₂ := fun t x => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      (gaussianHeat (iteratedDeriv (n+1) u) t x))
    (show ∀ᶠ v : ℝ × ℝ in 𝓝 p, HasFDerivAt
      (fun t => gaussianHeat (iteratedDeriv n u) t v.2)
      ((1 : ℝ →L[ℝ] ℝ).smulRight ((1/2:ℝ)*gaussianHeat (iteratedDeriv (n+2) u) v.1 v.2)) v.1 from by
      filter_upwards [heatDomain_open.mem_nhds hp] with v hv
      exact (heat_jet_time_derivative hu hv.1 n v.2).hasFDerivAt)
    (Eventually.of_forall fun v => (space_derivative (hu.continuous n).measurable
      (hu.continuous (n+1)).measurable (hu.growth n) (hu.growth (n+1))
      (fun y => by simpa only [iteratedDeriv_succ] using (hu.differentiable n y).hasDerivAt)
      v.1 v.2).hasFDerivAt)
    (by
      convert (htime.continuousAt.const_mul (1/2:ℝ)).smul (continuousAt_const (y := (1 : ℝ →L[ℝ] ℝ))) using 1; ext v; simp [Function.HasUncurry.uncurry,mul_comm])
    (by
      convert hspace.continuousAt.smul (continuousAt_const (y := (1 : ℝ →L[ℝ] ℝ))) using 1; ext v; simp [Function.HasUncurry.uncurry,mul_comm])
  have he : ((1 : ℝ →L[ℝ] ℝ).smulRight ((1/2:ℝ)*gaussianHeat (iteratedDeriv (n+2) u) p.1 p.2)).coprod
      ((1 : ℝ →L[ℝ] ℝ).smulRight (gaussianHeat (iteratedDeriv (n+1) u) p.1 p.2)) =
      ((1/2:ℝ)*gaussianHeat (iteratedDeriv (n+2) u) p.1 p.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
       gaussianHeat (iteratedDeriv (n+1) u) p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro z
    simp [ContinuousLinearMap.coprod_apply,mul_comm]
  simpa only [Function.HasUncurry.uncurry, id_eq, he] using hh.hasFDerivAt

lemma heatJet_contDiffOn {u : ℝ → ℝ} (hu : SmoothPolynomial u) (k n : ℕ) :
    ContDiffOn ℝ (k : WithTop ℕ∞)
      (fun p : ℝ × ℝ => gaussianHeat (iteratedDeriv n u) p.1 p.2) heatDomain := by
  induction k generalizing n with
  | zero => exact contDiffOn_zero.mpr (heat_jointly_continuous (hu.continuous n) (hu.growth n)).continuousOn
  | succ k ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiffOn_succ_iff_fderiv_of_isOpen heatDomain_open]
    refine ⟨fun p hp => (heatJet_hasFDeriv hu n hp).differentiableAt.differentiableWithinAt,?_,?_⟩
    · simp
    · have hc : ContDiffOn ℝ (k : WithTop ℕ∞) (fun p : ℝ × ℝ =>
          ((1/2:ℝ)*gaussianHeat (iteratedDeriv (n+2) u) p.1 p.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
          gaussianHeat (iteratedDeriv (n+1) u) p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) heatDomain :=
        ((contDiffOn_const.mul (ih (n+2))).smul contDiffOn_const).add
          ((ih (n+1)).smul contDiffOn_const)
      apply hc.congr
      intro p hp
      exact (heatJet_hasFDeriv hu n hp).fderiv

lemma heat_jointly_smooth {u : ℝ → ℝ} (hu : SmoothPolynomial u) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => gaussianHeat u p.1 p.2) heatDomain := by
  rw [contDiffOn_infty]
  intro k
  simpa using heatJet_contDiffOn hu k 0

lemma gaussianRowOperator_jointly_smooth {u : ℝ → ℝ} (hu : SmoothPolynomial u)
    {a B : ℝ} (ha : 0 ≤ a) (hB : ∀ x,u x ≤ B) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => gaussianRowOperator a p.1 u p.2) heatDomain := by
  by_cases haz : a=0
  · simpa [gaussianRowOperator,haz] using heat_jointly_smooth hu
  · have hh := (heat_jointly_smooth (exp_smoothPolynomial hu ha hB)).log
      (fun p _ => (exp_heat_pos hu.smooth.continuous hB ha).ne')
    simpa [gaussianRowOperator,haz,div_eq_mul_inv,mul_comm] using hh.mul contDiffOn_const
end Higher
end MicroscopicJamming

end

end OAI
