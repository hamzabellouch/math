import Mathlib
import OAI.Probability.JammingConcavity.GaussianStepRight
import OAI.Probability.JammingConcavity.UniformPolynomialGrowth

namespace OAI

/-! Polynomial Comparison. -/

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
open Set Filter
open scoped Topology

namespace MicroscopicJamming

lemma backward_positive_strict_compact {Q R : ℝ} (hQ : 0 < Q) (hR : 0 < R)
    {U b d : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 Q ×ˢ Icc (-R) R))
    (hx : ∀ t ∈ Icc 0 Q, Differentiable ℝ (U t))
    (ht : ∀ t ∈ Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => U s x) (d t x) (Ici t) t)
    (hp : ∀ t ∈ Ico 0 Q, ∀ x ∈ Ioo (-R) R, 0 < U t x →
      0 < d t x+(1/2:ℝ)*deriv (deriv (U t)) x+b t x*deriv (U t) x)
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
  linarith

def polynomialBarrier (n : ℕ) (ε c Q t x : ℝ) : ℝ :=
  ε*Real.exp (c*(Q-t))*(1+x^2)^(n+2)

lemma polynomialBarrier_space (n : ℕ) (ε c Q t x : ℝ) :
    HasDerivAt (polynomialBarrier n ε c Q t)
      (ε*Real.exp (c*(Q-t))*(2*(n+2)*x*(1+x^2)^(n+1))) x := by
  unfold polynomialBarrier
  convert (((hasDerivAt_const x 1).add ((hasDerivAt_id x).pow 2)).pow (n+2)).const_mul
    (ε*Real.exp (c*(Q-t))) using 1 <;> first | rfl | (simp only [Nat.cast_add,Nat.cast_ofNat,show n+2-1=n+1 by omega,Pi.add_apply,Pi.pow_apply,id_eq]; ring)

lemma polynomialBarrier_space2 (n : ℕ) (ε c Q t x : ℝ) :
    HasDerivAt (deriv (polynomialBarrier n ε c Q t))
      (ε*Real.exp (c*(Q-t))*(2*(n+2)*(1+x^2)^(n+1)+4*(n+2)*(n+1)*x^2*(1+x^2)^n)) x := by
  have he : deriv (polynomialBarrier n ε c Q t)=
      fun y => ε*Real.exp (c*(Q-t))*(2*(n+2)*y*(1+y^2)^(n+1)) :=
    funext fun y => (polynomialBarrier_space n ε c Q t y).deriv
  rw [he]
  convert (((hasDerivAt_id x).const_mul (2*((n:ℝ)+2))).mul
    (((hasDerivAt_const x 1).add ((hasDerivAt_id x).pow 2)).pow (n+1))).const_mul
    (ε*Real.exp (c*(Q-t))) using 1 <;> first | rfl | (simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,Pi.add_apply,Pi.pow_apply,id_eq]; ring)

lemma polynomialBarrier_time (n : ℕ) (ε c Q t x : ℝ) :
    HasDerivAt (fun s => polynomialBarrier n ε c Q s x)
      (-c*polynomialBarrier n ε c Q t x) t := by
  unfold polynomialBarrier
  convert ((((hasDerivAt_const t Q).sub (hasDerivAt_id t)).const_mul c).exp.const_mul ε).mul_const
    ((1+x^2)^(n+2)) using 1 <;> first | rfl | (simp only [Pi.sub_apply,id_eq]; ring)

lemma polynomial_transport_neg (n : ℕ) {K b x : ℝ} (hK : 0 ≤ K)
    (hb : |b| ≤ K*(1+|x|)) :
    -(2*(n+2)^2+4*K*(n+2)+1)*(1+x^2)^(n+2)+
      (1/2:ℝ)*(2*(n+2)*(1+x^2)^(n+1)+4*(n+2)*(n+1)*x^2*(1+x^2)^n)+
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
  have h1 := mul_le_mul_of_nonneg_left hq (show 0 ≤ (n:ℝ)+2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hxq (show 0 ≤ 2*((n:ℝ)+2)*(n+1) by positivity)
  have h3 := mul_le_mul_of_nonneg_left hbx (show 0 ≤ 2*((n:ℝ)+2)*(1+x^2) by positivity)
  have hneg : -(2*((n:ℝ)+2)^2+4*K*(n+2)+1)*(1+x^2)^2+
      (n+2)*(1+x^2)+2*(n+2)*(n+1)*x^2+2*(n+2)*b*x*(1+x^2) < 0 := by
    nlinarith [sq_nonneg x,sq_pos_of_pos (show 0 < 1+x^2 by positivity)]
  have hmul := mul_neg_of_pos_of_neg (show 0 < (1+x^2)^n by positivity) hneg
  convert hmul using 1; first | rfl | (simp only [pow_add,pow_one]; ring)

lemma backward_polynomial_bound {Q K C : ℝ} (n : ℕ) (hQ : 0 < Q) (hK : 0 ≤ K) (hC : 0 ≤ C)
    {U b d : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 Q ×ˢ univ))
    (hx : ∀ t ∈ Icc 0 Q, Differentiable ℝ (U t) ∧ Differentiable ℝ (deriv (U t)))
    (ht : ∀ t ∈ Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => U s x) (d t x) (Ici t) t)
    (hb : ∀ t ∈ Icc 0 Q, ∀ x, |b t x| ≤ K*(1+|x|))
    (hg : ∀ t ∈ Icc 0 Q, ∀ x, U t x ≤ C*(1+x^2)^n)
    (hp : ∀ t ∈ Ico 0 Q, ∀ x, 0 < U t x →
      0 ≤ d t x+(1/2:ℝ)*deriv (deriv (U t)) x+b t x*deriv (U t) x)
    (hterm : ∀ x, U Q x ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ t ∈ Icc 0 Q, ∀ x, U t x ≤ polynomialBarrier n ε (2*(n+2)^2+4*K*(n+2)+1) Q t x := by
  let c := 2*(n+2)^2+4*K*(n+2)+1
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
      0 < vd t x+(1/2:ℝ)*deriv (deriv (V t)) x+b t x*deriv (V t) x := by
    have htcc : t ∈ Icc 0 Q := ⟨ht'.1,ht'.2.le⟩
    rw [hvxx t htcc x,(hvx t htcc x).deriv]
    have hneg := polynomial_transport_neg n hK (hb t htcc x)
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
  have hcomp := backward_positive_strict_compact (b := b) hQ hR hVc
    (fun s hs y => (hvx s hs y).differentiableAt) hvtime (fun s hs y _ => hvp s hs y)
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

lemma backward_polynomial_comparison {Q K : ℝ} (hQ : 0 < Q) (hK : 0 ≤ K)
    {U b d : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 Q ×ˢ univ))
    (hx : ∀ t ∈ Icc 0 Q, Differentiable ℝ (U t) ∧ Differentiable ℝ (deriv (U t)))
    (ht : ∀ t ∈ Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => U s x) (d t x) (Ici t) t)
    (hb : ∀ t ∈ Icc 0 Q, ∀ x, |b t x| ≤ K*(1+|x|))
    (hg : Higher.UniformPolynomialGrowth (Icc 0 Q) U)
    (hp : ∀ t ∈ Ico 0 Q, ∀ x, 0 < U t x →
      0 ≤ d t x+(1/2:ℝ)*deriv (deriv (U t)) x+b t x*deriv (U t) x)
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
  let M := Real.exp ((2*(n+2)^2+4*K*(n+2)+1)*(Q-t))*(1+x^2)^(n+2)
  have hM : 0 < M := by dsimp [M]; positivity
  let ε := U t x/(2*M)
  have hε : 0 < ε := div_pos hpos (by positivity)
  have hh := backward_polynomial_bound n hQ hK (show 0 ≤ C*2^n by positivity) hc hx ht hb hg' hp hterm hε t ht' x
  have he : polynomialBarrier n ε (2*(n+2)^2+4*K*(n+2)+1) Q t x=U t x/2 := by
    dsimp only [polynomialBarrier]
    rw [mul_assoc]
    change (U t x/(2*M))*M=U t x/2
    field_simp
  rw [he] at hh
  linarith

end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming

lemma backward_reaction_upper {Q K R H : ℝ} (hQ : 0 < Q) (hK : 0 ≤ K) (hR : 0 ≤ R) (hH : 0 ≤ H)
    {U b d r : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 Q ×ˢ univ))
    (hx : ∀ t ∈ Icc 0 Q, Differentiable ℝ (U t) ∧ Differentiable ℝ (deriv (U t)))
    (ht : ∀ t ∈ Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => U s x) (d t x) (Ici t) t)
    (hb : ∀ t ∈ Icc 0 Q, ∀ x, |b t x| ≤ K*(1+|x|))
    (hg : Higher.UniformPolynomialGrowth (Icc 0 Q) U)
    (hr : ∀ t ∈ Ico 0 Q, ∀ x, r t x ≤ R)
    (hp : ∀ t ∈ Ico 0 Q, ∀ x,
      d t x+(1/2:ℝ)*deriv (deriv (U t)) x+b t x*deriv (U t) x+r t x*U t x=0)
    (hterm : ∀ x, U Q x ≤ H) :
    ∀ t ∈ Icc 0 Q, ∀ x, U t x ≤ H*Real.exp (R*(Q-t)) := by
  let E : ℝ → ℝ := fun t => Real.exp (R*(t-Q))
  let V : ℝ → ℝ → ℝ := fun t x => E t*U t x-H
  let vd : ℝ → ℝ → ℝ := fun t x => E t*(d t x+R*U t x)
  have hE (t : ℝ) : HasDerivAt E (R*E t) t := by
    convert (((hasDerivAt_id t).sub_const Q).const_mul R).exp using 1 <;> first | rfl | (dsimp [E]; ring)
  have hEc : Continuous E := continuous_iff_continuousAt.mpr (fun t => (hE t).continuousAt)
  have hEp (t : ℝ) : 0 < E t := Real.exp_pos _
  have hEl (t : ℝ) (ht' : t ∈ Icc 0 Q) : E t ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hR (sub_nonpos.mpr ht'.2))
  have hvx (t : ℝ) (ht' : t ∈ Icc 0 Q) (x : ℝ) :
      HasDerivAt (V t) (E t*deriv (U t) x) x :=
    (((hx t ht').1 x).hasDerivAt.const_mul (E t)).sub_const H
  have hvxx (t : ℝ) (ht' : t ∈ Icc 0 Q) (x : ℝ) :
      HasDerivAt (deriv (V t)) (E t*deriv (deriv (U t)) x) x := by
    have he : deriv (V t)=fun y => E t*deriv (U t) y := funext (fun y => (hvx t ht' y).deriv)
    rw [he]
    exact ((hx t ht').2 x).hasDerivAt.const_mul (E t)
  have hvtime (t : ℝ) (ht' : t ∈ Ico 0 Q) (x : ℝ) :
      HasDerivWithinAt (fun s => V s x) (vd t x) (Ici t) t := by
    convert ((hE t).hasDerivWithinAt.mul (ht t ht' x)).sub_const H using 1; first | rfl | (dsimp [vd]; ring)
  have hvg : Higher.UniformPolynomialGrowth (Icc 0 Q) V := by
    obtain ⟨n,C,hC,hg⟩ := hg
    refine ⟨n,C+H,add_nonneg hC hH,fun t ht' x => ?_⟩
    have he := mul_le_mul_of_nonneg_right (hEl t ht') (abs_nonneg (U t x))
    have hp1 : 1 ≤ (1+|x|)^n := one_le_pow₀ (by linarith [abs_nonneg x])
    calc
      |V t x| ≤ |E t*U t x|+|H| := abs_sub _ _
      _ = E t*|U t x|+H := by rw [abs_mul,abs_of_pos (hEp t),abs_of_nonneg hH]
      _ ≤ |U t x|+H := by linarith
      _ ≤ C*(1+|x|)^n+H*(1+|x|)^n := add_le_add (hg t ht' x) (le_mul_of_one_le_right hH hp1)
      _ = _ := by ring
  have hvc : ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2) (Icc 0 Q ×ˢ univ) :=
    ((hEc.comp continuous_fst).continuousOn.mul hc).sub continuousOn_const
  have hcomp := backward_polynomial_comparison hQ hK hvc
    (fun t ht' => ⟨fun x => (hvx t ht' x).differentiableAt,fun x => (hvxx t ht' x).differentiableAt⟩)
    hvtime hb hvg (fun t ht' x hpos => ?_) (fun x => ?_)
  · intro t ht' x
    have h := hcomp t ht' x
    dsimp [V] at h
    have hexp : E t*Real.exp (R*(Q-t))=1 := by rw [← Real.exp_add]; convert Real.exp_zero using 1; congr 1; ring
    have hh := mul_le_mul_of_nonneg_right (show E t*U t x ≤ H by linarith) (Real.exp_nonneg (R*(Q-t)))
    calc
      U t x = (E t*Real.exp (R*(Q-t)))*U t x := by rw [hexp,one_mul]
      _ = E t*U t x*Real.exp (R*(Q-t)) := by ring
      _ ≤ _ := hh
  · rw [(hvxx t ⟨ht'.1,ht'.2.le⟩ x).deriv,(hvx t ⟨ht'.1,ht'.2.le⟩ x).deriv]
    have hpp := hp t ht' x
    have hrp := hr t ht' x
    have hUp : 0 ≤ E t*U t x := by dsimp [V] at hpos; linarith
    have hnn := mul_nonneg (sub_nonneg.mpr hrp) hUp
    dsimp [vd]
    calc
      _ = E t*(d t x+(1/2:ℝ)*deriv (deriv (U t)) x+b t x*deriv (U t) x+r t x*U t x)+
          (R-r t x)*(E t*U t x) := by ring
      _ ≥ 0 := by rw [hpp,mul_zero,zero_add]; exact hnn
  · dsimp [V,E]
    simp only [sub_self,mul_zero,Real.exp_zero,one_mul]
    exact sub_nonpos.mpr (hterm x)

lemma backward_reaction_bound {Q K R H : ℝ} (hQ : 0 < Q) (hK : 0 ≤ K) (hR : 0 ≤ R) (hH : 0 ≤ H)
    {U b d r : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 Q ×ˢ univ))
    (hx : ∀ t ∈ Icc 0 Q, Differentiable ℝ (U t) ∧ Differentiable ℝ (deriv (U t)))
    (ht : ∀ t ∈ Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => U s x) (d t x) (Ici t) t)
    (hb : ∀ t ∈ Icc 0 Q, ∀ x, |b t x| ≤ K*(1+|x|))
    (hg : Higher.UniformPolynomialGrowth (Icc 0 Q) U)
    (hr : ∀ t ∈ Ico 0 Q, ∀ x, r t x ≤ R)
    (hp : ∀ t ∈ Ico 0 Q, ∀ x,
      d t x+(1/2:ℝ)*deriv (deriv (U t)) x+b t x*deriv (U t) x+r t x*U t x=0)
    (hterm : ∀ x, |U Q x| ≤ H) :
    ∀ t ∈ Icc 0 Q, ∀ x, |U t x| ≤ H*Real.exp (R*(Q-t)) := by
  have hupper := backward_reaction_upper hQ hK hR hH hc hx ht hb hg hr hp
    (fun x => (le_abs_self _).trans (hterm x))
  have hn1 (t : ℝ) (ht' : t ∈ Icc 0 Q) : deriv (fun x => -U t x)=fun x => -deriv (U t) x := by
    funext x; exact ((hx t ht').1 x).hasDerivAt.neg.deriv
  have hn2 (t : ℝ) (ht' : t ∈ Icc 0 Q) : deriv (deriv (fun x => -U t x))=fun x => -deriv (deriv (U t)) x := by
    rw [hn1 t ht']; funext x; exact ((hx t ht').2 x).hasDerivAt.neg.deriv
  have hneg := backward_reaction_upper (U:=fun t x => -U t x) (d:=fun t x => -d t x)
    hQ hK hR hH hc.neg
    (fun t ht' => ⟨(hx t ht').1.neg,by rw [hn1 t ht']; exact (hx t ht').2.neg⟩)
    (fun t ht' x => (ht t ht' x).neg) hb
    (by simpa only [neg_one_mul] using hg.const_mul (-1)) hr
    (fun t ht' x => by rw [hn2 t ⟨ht'.1,ht'.2.le⟩,hn1 t ⟨ht'.1,ht'.2.le⟩]; linarith [hp t ht' x])
    (fun x => (neg_le_abs _).trans (hterm x))
  intro t ht' x
  rw [abs_le]
  exact ⟨by linarith [hneg t ht' x],hupper t ht' x⟩

lemma forward_reaction_bound {Q K R H : ℝ} (hQ : 0 < Q) (hK : 0 ≤ K) (hR : 0 ≤ R) (hH : 0 ≤ H)
    {U b d r : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 Q ×ˢ univ))
    (hx : ∀ t ∈ Icc 0 Q, Differentiable ℝ (U t) ∧ Differentiable ℝ (deriv (U t)))
    (ht : ∀ t ∈ Ioc 0 Q, ∀ x, HasDerivAt (fun s => U s x) (d t x) t)
    (hb : ∀ t ∈ Icc 0 Q, ∀ x, |b t x| ≤ K*(1+|x|))
    (hg : Higher.UniformPolynomialGrowth (Icc 0 Q) U)
    (hr : ∀ t ∈ Ioc 0 Q, ∀ x, r t x ≤ R)
    (hp : ∀ t ∈ Ioc 0 Q, ∀ x,
      d t x-(1/2:ℝ)*deriv (deriv (U t)) x-b t x*deriv (U t) x-r t x*U t x=0)
    (hterm : ∀ x, |U 0 x| ≤ H) :
    ∀ t ∈ Icc 0 Q, ∀ x, |U t x| ≤ H*Real.exp (R*t) := by
  have hm (t : ℝ) (ht' : t ∈ Icc 0 Q) : Q-t ∈ Icc 0 Q :=
    ⟨by linarith [ht'.2],by linarith [ht'.1]⟩
  have hmo (t : ℝ) (ht' : t ∈ Ico 0 Q) : Q-t ∈ Ioc 0 Q :=
    ⟨by linarith [ht'.2],by linarith [ht'.1]⟩
  have hvc : ContinuousOn (fun p : ℝ × ℝ => U (Q-p.1) p.2) (Icc 0 Q ×ˢ univ) :=
    hc.comp (show ContinuousOn (fun p : ℝ × ℝ => (Q-p.1,p.2)) _ by fun_prop)
      (fun p hp' => ⟨hm p.1 hp'.1,mem_univ _⟩)
  have hvt (t : ℝ) (ht' : t ∈ Ico 0 Q) (x : ℝ) :
      HasDerivWithinAt (fun s => U (Q-s) x) (-d (Q-t) x) (Ici t) t := by
    convert ((ht (Q-t) (hmo t ht') x).comp t ((hasDerivAt_const t Q).sub (hasDerivAt_id t))).hasDerivWithinAt using 1 <;>
      first | rfl | ring
  have hcomp := backward_reaction_bound (U:=fun t => U (Q-t)) (b:=fun t => b (Q-t))
    (d:=fun t x => -d (Q-t) x) (r:=fun t => r (Q-t)) hQ hK hR hH hvc
    (fun t ht' => hx (Q-t) (hm t ht')) hvt (fun t ht' => hb (Q-t) (hm t ht'))
    (hg.comp (fun t ht' => hm t ht')) (fun t ht' => hr (Q-t) (hmo t ht'))
    (fun t ht' x => by linarith [hp (Q-t) (hmo t ht') x])
    (fun x => by simpa using hterm x)
  intro t ht' x
  simpa only [sub_sub_cancel] using hcomp (Q-t) (hm t ht') x
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace Higher

 

lemma gaussianRowOperator_third_bound {u : ℝ → ℝ} {A B C κ Q a L D K H : ℝ}
    (hu : Twice.RowTwiceTerminal u A B C κ Q) (hs : SmoothPolynomial u)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hL : 0 < L) (hsub : a*κ*L < 1)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hfirst : ∀ T ∈ Icc 0 L, ∀ x, |deriv (gaussianRowOperator a T u) x| ≤ D*(1+|x|))
    (hsecond : ∀ T ∈ Icc 0 L, ∀ x, deriv (deriv (gaussianRowOperator a T u)) x ≤ K)
    (hthird : ∀ x, |iteratedDeriv 3 u x| ≤ H) :
    ∀ T ∈ Icc 0 L, ∀ x, |iteratedDeriv 3 (gaussianRowOperator a T u) x| ≤ H*Real.exp (3*K*T) := by
  let F : ℝ → ℝ → ℝ := fun t => gaussianRowOperator a t u
  let U : ℝ → ℝ → ℝ := fun t => iteratedDeriv 3 (F t)
  let b : ℝ → ℝ → ℝ := fun t x => a*iteratedDeriv 1 (F t) x
  let r : ℝ → ℝ → ℝ := fun t x => 3*a*iteratedDeriv 2 (F t) x
  let d : ℝ → ℝ → ℝ := fun t x => (1/2:ℝ)*iteratedDeriv 5 (F t) x+
    a*iteratedDeriv 1 (F t) x*iteratedDeriv 4 (F t) x+3*a*iteratedDeriv 2 (F t) x*iteratedDeriv 3 (F t) x
  have hsp (t : ℝ) (ht : t ∈ Icc 0 L) : SmoothPolynomial (F t) :=
    gaussianRowOperator_smoothPolynomial hu hs ha ht.1
      ((mul_le_mul_of_nonneg_left ht.2 (mul_nonneg ha hu.kappa_nonneg)).trans_lt hsub)
  have hU1 (t : ℝ) : deriv (U t)=iteratedDeriv 4 (F t) :=
    (iteratedDeriv_succ (n:=3)).symm
  have hU2 (t : ℝ) : deriv (deriv (U t))=iteratedDeriv 5 (F t) := by
    rw [hU1 t]; exact (iteratedDeriv_succ (n:=4)).symm
  have hUx (t : ℝ) (ht : t ∈ Icc 0 L) :
      Differentiable ℝ (U t) ∧ Differentiable ℝ (deriv (U t)) := by
    refine ⟨(hsp t ht).differentiable 3,?_⟩
    rw [hU1 t]
    exact (hsp t ht).differentiable 4
  have hUb (t : ℝ) (ht : t ∈ Icc 0 L) (x : ℝ) : |b t x| ≤ D*(1+|x|) := by
    change |a*iteratedDeriv 1 (gaussianRowOperator a t u) x| ≤ _
    rw [abs_mul,abs_of_nonneg ha,iteratedDeriv_one]
    exact (mul_le_mul_of_nonneg_left (hfirst t ht x) ha).trans
      (mul_le_of_le_one_left (by positivity) ha1)
  have hUr (t : ℝ) (ht : t ∈ Ioc 0 L) (x : ℝ) : r t x ≤ 3*K := by
    have hsec := hsecond t ⟨ht.1.le,ht.2⟩ x
    have hh := mul_le_mul_of_nonneg_left hsec ha
    have hh' := mul_le_of_le_one_left hK ha1
    dsimp [r,F]
    simp only [iteratedDeriv_succ,iteratedDeriv_zero]
    nlinarith
  have hUp (t : ℝ) (ht : t ∈ Ioc 0 L) (x : ℝ) :
      d t x-(1/2:ℝ)*deriv (deriv (U t)) x-b t x*deriv (U t) x-r t x*U t x=0 := by
    rw [hU2 t,hU1 t]
    dsimp [d,b,r,U]; ring
  have he : F 0=u := funext (fun x => gaussianRowOperator_zero a u x)
  apply forward_reaction_bound hL hD (show 0 ≤ 3*K by positivity) hH
    (gaussianRowOperator_third_continuous hs ha (fun x => (hu.bounds x).2.1)).continuousOn
    hUx (fun t ht x => gaussianRowOperator_third_equation hs ha (fun x => (hu.bounds x).2.1) ht.1 x)
    hUb (gaussianRowOperator_third_growth hu hs ha hL.le hsub) hUr hUp
  intro x
  change |iteratedDeriv 3 (F 0) x| ≤ H
  rw [he]
  exact hthird x
end Higher
end MicroscopicJamming

 
open Set

namespace MicroscopicJamming
namespace Higher

lemma gaussianRowComposition_third_bound {u : ℝ → ℝ} {A B C κ Q H : ℝ}
    (hQ : 0 < Q) (hu : RowAnalyticTerminal u A B C κ Q) (hH : 0 ≤ H)
    (hthird : ∀ x, |iteratedDeriv 3 u x| ≤ H) :
    ∀ rs : List (ℝ × ℝ), (∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) →
      gaussianStepTime rs ≤ Q → ∀ x,
      |iteratedDeriv 3 (gaussianRowComposition rs u) x| ≤
        H*Real.exp (3*(C+κ/(1-κ*Q))*gaussianStepTime rs) := by
  let K := C+κ/(1-κ*Q)
  have hden : 0 < 1-κ*Q := by linarith [hu.2.2.2.2.1]
  have hK : 0 ≤ K := add_nonneg hu.2.2.1 (div_nonneg hu.2.2.2.1 hden.le)
  obtain ⟨D,hD,hfirst⟩ := gaussian_step_slope A B C κ Q hQ hu.2.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2.1
  intro rs
  induction rs with
  | nil => intro _ _ x; simpa [gaussianRowComposition,gaussianStepTime] using hthird x
  | cons r rs ih =>
    intro hrs hsum
    have hr := hrs r (by simp)
    have ht : ∀ v ∈ rs, 0 ≤ v.1 ∧ v.1 ≤ 1 ∧ 0 ≤ v.2 := fun v hv => hrs v (by simp [hv])
    have htime : gaussianStepTime (r::rs)=r.2+gaussianStepTime rs := by simp [gaussianStepTime]
    rw [htime] at hsum ⊢
    have htq : gaussianStepTime rs ≤ Q := by linarith [hr.2.2]
    have htw := gaussianRowComposition_twice hQ hu ht htq
    have hsp := gaussianRowComposition_smoothPolynomial hQ hu rs ht htq
    have hinitial : ∀ x, |iteratedDeriv 3 (gaussianRowComposition rs u) x| ≤
        H*Real.exp (3*K*gaussianStepTime rs) := ih ht htq
    by_cases hz : r.2=0
    · have he : gaussianRowComposition (r::rs) u=gaussianRowComposition rs u := by
        funext x
        change gaussianRowOperator r.1 r.2 (gaussianRowComposition rs u) x=_
        rw [hz,gaussianRowOperator_zero]
      rw [he,hz,zero_add]
      exact hinitial
    · have hT : 0 < r.2 := lt_of_le_of_ne hr.2.2 (Ne.symm hz)
      have hvalid (T : ℝ) (hT' : T ∈ Icc 0 r.2) :
          ∀ v ∈ (r.1,T)::rs, 0 ≤ v.1 ∧ v.1 ≤ 1 ∧ 0 ≤ v.2 := by
        intro v hv
        rcases List.mem_cons.mp hv with h | h
        · subst v; exact ⟨hr.1,hr.2.1,hT'.1⟩
        · exact ht v h
      have htot (T : ℝ) (hT' : T ∈ Icc 0 r.2) : gaussianStepTime ((r.1,T)::rs) ≤ Q := by
        have hh : T+gaussianStepTime rs ≤ Q := by linarith [hT'.2]
        simpa [gaussianStepTime] using hh
      have hsec (T : ℝ) (hT' : T ∈ Icc 0 r.2) (x : ℝ) :
          deriv (deriv (gaussianRowOperator r.1 T (gaussianRowComposition rs u))) x ≤ K := by
        have hh := ((gaussian_step_bounds u A B C κ Q hQ hu _ (hvalid T hT') (htot T hT')).2.2 x).2.2
        have hcap : κ/(1-κ*gaussianStepTime ((r.1,T)::rs)) ≤ κ/(1-κ*Q) :=
          div_le_div_of_nonneg_left hu.2.2.2.1 hden
            (by nlinarith [mul_le_mul_of_nonneg_left (htot T hT') hu.2.2.2.1])
        exact hh.trans (by dsimp [K]; linarith [hu.2.2.1])
      have hh := gaussianRowOperator_third_bound htw hsp hr.1 hr.2.1 hT
        (gaussianRowComposition_block_subcritical hQ hu ht hr.1 hr.2.1 hr.2.2 hsum)
        hD hK (mul_nonneg hH (Real.exp_nonneg _))
        (fun T hT' => hfirst u hu ((r.1,T)::rs) (hvalid T hT') (htot T hT')) hsec hinitial
      intro x
      have hbound := hh r.2 ⟨hT.le,le_rfl⟩ x
      have he : (H*Real.exp (3*K*gaussianStepTime rs))*Real.exp (3*K*r.2)=
          H*Real.exp (3*K*(r.2+gaussianStepTime rs)) := by
        rw [mul_assoc,← Real.exp_add]
        congr 2
        ring
      rw [he] at hbound
      exact hbound
end Higher

 

theorem gaussian_step_third : GaussianStepThirdStatement := by
  intro u A B C κ Q hQ hu
  obtain ⟨H,hthird⟩ := hu.2.2.2.2.2.1 3 (by norm_num)
  have hH : 0 ≤ H := (abs_nonneg _).trans (hthird 0)
  let K := C+κ/(1-κ*Q)
  have hden : 0 < 1-κ*Q := by linarith [hu.2.2.2.2.1]
  have hK : 0 ≤ K := add_nonneg hu.2.2.1 (div_nonneg hu.2.2.2.1 hden.le)
  refine ⟨H*Real.exp (3*K*Q),mul_nonneg hH (Real.exp_nonneg _),?_⟩
  intro rs hrs hsum t ht htT
  obtain ⟨hv,hvT⟩ := gaussianStepRemainder_valid hrs ht
  rw [max_eq_left (sub_nonneg.mpr htT)] at hvT
  have hvQ : gaussianStepTime (gaussianStepRemainder rs t) ≤ Q := by rw [hvT]; linarith
  have hs := Higher.gaussianRowComposition_smoothPolynomial hQ hu _ hv hvQ
  have hb := Higher.gaussianRowComposition_third_bound hQ hu hH hthird _ hv hvQ
  refine ⟨?_,fun x => ?_⟩
  · change Differentiable ℝ (deriv (deriv (gaussianRowComposition (gaussianStepRemainder rs t) u)))
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hs.differentiable 2
  · have hh := (hb x).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hvQ (by positivity : 0 ≤ 3*K))) hH)
    change |deriv (deriv (deriv (gaussianRowComposition (gaussianStepRemainder rs t) u))) x| ≤ _
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,K] using hh
end MicroscopicJamming

 
 

namespace MicroscopicJamming

def GaussianStepGradientTimeStatement : Prop :=
  ∀ A B C κ Q : ℝ, 0 < Q → 0 ≤ A → 0 ≤ C → 0 ≤ κ → κ*Q < 1 →
  ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧
  ∀ u : ℝ → ℝ, RowAnalyticTerminal u A B C κ Q →
  ∀ rs : List (ℝ × ℝ), (∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) →
    gaussianStepTime rs ≤ Q →
  ∀ s t : ℝ, 0 ≤ s → s ≤ gaussianStepTime rs →
    0 ≤ t → t ≤ gaussianStepTime rs →
  ∀ x h : ℝ, 0 < h → h ≤ 1 →
    |deriv (gaussianStepPath rs u t) x-deriv (gaussianStepPath rs u s) x| ≤
      2*D*(1+(|x|+1)^2)*(|t-s|/h)+2*K*h
end MicroscopicJamming

 
open Set

namespace MicroscopicJamming

lemma deriv_secant_error {f : ℝ → ℝ} {K x h : ℝ}
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f))
    (hK : 0 ≤ K) (hb : ∀ z, |deriv (deriv f) z| ≤ K) (hh : 0 < h) :
    |deriv f x-(f (x+h)-f x)/h| ≤ K*h := by
  obtain ⟨c,hc,he⟩ := exists_deriv_eq_slope f (show x<x+h by linarith)
    hf.continuous.continuousOn hf.differentiableOn
  have he' : deriv f c=(f (x+h)-f x)/h := by simpa using he
  rw [←he']
  have hv := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := deriv f) (s := univ) (C := K) (fun z _ => hf' z)
    (fun z _ => by simpa only [Real.norm_eq_abs] using hb z)
    convex_univ (x := c) (y := x) (mem_univ _) (mem_univ _)
  simp only [Real.norm_eq_abs] at hv
  apply hv.trans
  apply mul_le_mul_of_nonneg_left _ hK
  rw [abs_of_neg (by linarith [hc.1] : x-c<0)]
  linarith [hc.2]

theorem gaussian_step_gradient_time : GaussianStepGradientTimeStatement := by
  intro A B C κ Q hQ hA hC hk hsub
  obtain ⟨D,L,hD,hL,hpath⟩ := gaussian_step_path A B C κ Q hQ hA hC hk hsub
  let K := C+κ/(1-κ*Q)
  have hden : 0<1-κ*Q := by linarith
  have hK : 0 ≤ K := add_nonneg hC (div_nonneg hk hden.le)
  refine ⟨D,K,hD,hK,?_⟩
  intro u hu rs hrs hsum s t hs hsT ht htT x h hh hh1
  obtain ⟨_,_,htime,hspace⟩ := hpath u hu rs hrs hsum
  have hcurv (v : ℝ) (hv : 0 ≤ v) (hvT : v ≤ gaussianStepTime rs) (z : ℝ) :
      |deriv (deriv (gaussianStepPath rs u v)) z| ≤ K := by
    have hz := ((hspace v hv hvT).2.2 z).2
    have hsmall : gaussianStepTime rs-v ≤ Q := by linarith
    have hden' : 0 < 1-κ*(gaussianStepTime rs-v) := by
      nlinarith [mul_le_mul_of_nonneg_left hsmall hk]
    have hcap : κ/(1-κ*(gaussianStepTime rs-v)) ≤ κ/(1-κ*Q) :=
      div_le_div_of_nonneg_left hk hden (by nlinarith [mul_le_mul_of_nonneg_left hsmall hk])
    rw [abs_le]
    dsimp [K]
    constructor <;> linarith [div_nonneg hk hden.le,hz.1,hz.2]
  have heT := deriv_secant_error (hspace t ht htT).1 (hspace t ht htT).2.1 hK (hcurv t ht htT) (x:=x) hh
  have heS := deriv_secant_error (hspace s hs hsT).1 (hspace s hs hsT).2.1 hK (hcurv s hs hsT) (x:=x) hh
  let E := D*(1+(|x|+1)^2)*|t-s|
  have hb (y : ℝ) (hy : |y| ≤ |x|+1) :
      |gaussianStepPath rs u t y-gaussianStepPath rs u s y| ≤ E := by
    have hy2 : y^2 ≤ (|x|+1)^2 := by
      have hh := (sq_le_sq₀ (abs_nonneg y) (by positivity : 0 ≤ |x|+1)).mpr hy
      simpa only [sq_abs] using hh
    exact (htime s t hs ht y).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hD) (abs_nonneg _))
  have hx1 : |x+h| ≤ |x|+1 := by
    have hh' := abs_add_le x h
    rw [abs_of_pos hh] at hh'
    linarith
  have hx0 : |x| ≤ |x|+1 := by linarith
  have hv1 := hb (x+h) hx1
  have hv0 := hb x hx0
  have hslope : |(gaussianStepPath rs u t (x+h)-gaussianStepPath rs u t x)/h-
      (gaussianStepPath rs u s (x+h)-gaussianStepPath rs u s x)/h| ≤ 2*E/h := by
    rw [← sub_div,abs_div,abs_of_pos hh]
    apply div_le_div_of_nonneg_right _ hh.le
    have he : (gaussianStepPath rs u t (x+h)-gaussianStepPath rs u t x)-
        (gaussianStepPath rs u s (x+h)-gaussianStepPath rs u s x)=
        (gaussianStepPath rs u t (x+h)-gaussianStepPath rs u s (x+h))-
        (gaussianStepPath rs u t x-gaussianStepPath rs u s x) := by ring
    rw [he]
    exact (abs_sub _ _).trans (by linarith)
  have ht1 := abs_sub_le (deriv (gaussianStepPath rs u t) x)
    ((gaussianStepPath rs u t (x+h)-gaussianStepPath rs u t x)/h)
    (deriv (gaussianStepPath rs u s) x)
  have ht2 := abs_sub_le ((gaussianStepPath rs u t (x+h)-gaussianStepPath rs u t x)/h)
    ((gaussianStepPath rs u s (x+h)-gaussianStepPath rs u s x)/h)
    (deriv (gaussianStepPath rs u s) x)
  rw [abs_sub_comm (deriv (gaussianStepPath rs u s) x)] at heS
  have he : 2*E/h=2*D*(1+(|x|+1)^2)*(|t-s|/h) := by dsimp [E]; ring
  rw [he] at hslope
  linarith
end MicroscopicJamming

end

end OAI
