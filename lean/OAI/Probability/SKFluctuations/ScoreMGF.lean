import Mathlib
import OAI.Probability.SKFluctuations.MomentNorm
import OAI.Probability.SKFluctuations.Projection

namespace OAI

/-! Score M G F. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Hierarchy Filter Set
open scoped Topology NNReal BigOperators

 theorem ExpNormBounded.integrable_tiltedLaw {ι : Type*} [Fintype ι]
    {F A : (ι → ℝ) → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F)
    (hA : ExpNormBounded A) (q : ι → ℝ≥0) (m : ℝ) :
    Integrable A (tiltedLaw (Measure.pi fun i => gaussianReal 0 (q i)) m F) := by
  let μ := Measure.pi fun i => gaussianReal 0 (q i)
  have hW := ExpNormBounded.exp_lipschitz hF m
  have hi := hW.integrable q
  have hp := partition_pos m hi
  unfold tiltedLaw
  rw [integrable_withDensity_iff
    (((hF.continuous.measurable.const_mul m).exp.div_const _).ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (div_nonneg (Real.exp_nonneg _) hp.le)]
  have h := ((hA.mul hW).integrable q).div_const (∫ z, Real.exp (m*F z) ∂μ)
  simpa only [mul_div_assoc] using h

 theorem ExpNormBounded.exp_vectorDot {ι : Type*} [Fintype ι] (v : ι → ℝ) (t : ℝ) :
    ExpNormBounded (fun z => Real.exp (t*GaussianCalculus.vectorDot v z)) := by
  let L : (ι → ℝ) →L[ℝ] ℝ := ∑ i, v i • (ContinuousLinearMap.proj i)
  have hL (z : ι → ℝ) : L z = GaussianCalculus.vectorDot v z := by simp [L,GaussianCalculus.vectorDot]
  simpa only [hL] using ExpNormBounded.exp_lipschitz L.lipschitzWith t

 theorem gaussianVectorScore_exp_expBounded {ι : Type*} [Fintype ι] (m t : ℝ)
    {G : ι → (ι → ℝ) → ℝ} (hG : ∀ i, BddSmooth 0 (G i)) (v : ι → ℝ) :
    ExpNormBounded (fun z => Real.exp (t*gaussianVectorScore m G v z)) := by
  have hb : BddSmooth 0 (fun z => -(t*m)*(∑ i, v i*G i z)) :=
    (BddSmooth.sum Finset.univ (fun i _ => (hG i).const_mul (v i))).const_mul (-(t*m))
  have he := (ExpNormBounded.exp_vectorDot v t).mul
    (ExpNormBounded.bddSmooth (hb.comp_contDiff Real.contDiff_exp))
  convert he using 1
  funext z
  dsimp only [gaussianVectorScore]
  rw [← Real.exp_add]
  congr 1
  ring

 

 theorem gaussian_ode_bound {f d : ℝ → ℝ} (hd : ∀ t, HasDerivAt f (d t) t)
    (h0 : f 0 = 1) (Q : ℝ)
    (hpos : ∀ t, 0 ≤ t → d t ≤ Q*t*f t)
    (hneg : ∀ t, t ≤ 0 → Q*t*f t ≤ d t) (t : ℝ) :
    f t ≤ Real.exp (Q*t^2/2) := by
  let g := fun t => Real.exp (-(Q*t^2/2))*f t
  let dg := fun t => Real.exp (-(Q*t^2/2))*(d t-Q*t*f t)
  have hgd (s : ℝ) : HasDerivAt g (dg s) s := by
    have hp : HasDerivAt (fun t : ℝ => -(Q*t^2/2)) (-Q*s) s := by
      convert (((hasDerivAt_id s).pow 2).const_mul Q |>.div_const 2).neg using 1 <;>
        first | rfl | simp; ring
    convert hp.exp.mul (hd s) using 1; first | rfl | dsimp [g,dg]; ring
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun s => (hgd s).continuousAt
  have hg0 : g 0 = 1 := by simp [g,h0]
  have hg : g t ≤ 1 := by
    by_cases ht : 0 ≤ t
    · have hmono : AntitoneOn g (Ici 0) := antitoneOn_of_deriv_nonpos (convex_Ici 0)
        hgc.continuousOn (fun s _ => (hgd s).differentiableAt.differentiableWithinAt)
        (fun s hs => by
          rw [(hgd s).deriv]
          apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
          exact sub_nonpos.mpr (hpos s (interior_subset hs)))
      simpa only [hg0] using hmono (mem_Ici.mpr le_rfl) ht ht
    · have hmono : MonotoneOn g (Iic 0) := monotoneOn_of_deriv_nonneg (convex_Iic 0)
        hgc.continuousOn (fun s _ => (hgd s).differentiableAt.differentiableWithinAt)
        (fun s hs => by
          rw [(hgd s).deriv]
          apply mul_nonneg (Real.exp_nonneg _)
          exact sub_nonneg.mpr (hneg s (show s ∈ Iic (0:ℝ) from interior_subset hs)))
      have ht' := le_of_not_ge ht
      simpa only [hg0] using hmono ht' (mem_Iic.mpr le_rfl) ht'
  have hh := mul_le_mul_of_nonneg_left hg (Real.exp_nonneg (Q*t^2/2))
  simpa only [g,← mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul,mul_one] using hh

 
 theorem tiltedMean_vectorScore_exp_identity {n : ℕ}
    {F : (Fin (n+1) → ℝ) → ℝ}
    {G : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ}
    {H : Fin (n+1) → Fin (n+1) → (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : ∀ i, BddSmooth 0 (G i))
    (hH : ∀ i j, BddSmooth 0 (H i j))
    (hdF : ∀ i x t, HasDerivAt (fun s : ℝ => F (x+s • Pi.single i 1))
      (G i (x+t • Pi.single i 1)) t)
    (hdG : ∀ j i x t, HasDerivAt (fun s : ℝ => G j (x+s • Pi.single i 1))
      (H j i (x+t • Pi.single i 1)) t)
    (v : Fin (n+1) → ℝ) (m t : ℝ) :
    tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m F
      (fun z => gaussianVectorScore m G v z*Real.exp (t*gaussianVectorScore m G v z)) =
    tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m F
      (fun z => Real.exp (t*gaussianVectorScore m G v z)*t*
        ((∑ i, v i^2)-m*∑ i, v i*(∑ j, v j*H j i z))) := by
  let S := gaussianVectorScore m G v
  let E := fun z => Real.exp (t*S z)
  let dS := fun i z => v i-m*∑ j, v j*H j i z
  have hE : ExpNormBounded E := gaussianVectorScore_exp_expBounded m t hG v
  have hdS (i) : ExpNormBounded (dS i) := (ExpNormBounded.const (v i)).sub
    ((ExpNormBounded.sum Finset.univ (fun j _ =>
      (ExpNormBounded.bddSmooth (hH j i)).const_mul (v j))).const_mul m)
  have hh := tiltedMean_vectorScore hF hG hdF hE
    (fun i => hE.mul ((hdS i).const_mul t))
    (fun i x u => ((gaussianVectorScore_hasDerivAt hdG m v i x u).const_mul t).exp) m v
  have he (z : Fin (n+1) → ℝ) :
      (∑ i, v i*(E z*(t*dS i z))) =
        E z*t*((∑ i, v i^2)-m*∑ i, v i*(∑ j, v j*H j i z)) := by
    dsimp only [dS]
    simp_rw [show ∀ i, v i*(E z*(t*(v i-m*∑ j, v j*H j i z))) =
      E z*t*(v i^2)-E z*t*m*(v i*∑ j, v j*H j i z) by intro i; ring]
    simp only [Finset.sum_sub_distrib,← Finset.mul_sum]
    ring
  simp_rw [he] at hh
  simpa only [S,E,mul_comm (Real.exp _) (gaussianVectorScore m G v _)] using hh

 

 theorem gaussianVectorScore_hasSubgaussianMGF {n : ℕ}
    {F : (Fin (n+1) → ℝ) → ℝ}
    {G : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ}
    {H : Fin (n+1) → Fin (n+1) → (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : ∀ i, BddSmooth 0 (G i))
    (hH : ∀ i j, BddSmooth 0 (H i j))
    (hdF : ∀ i x t, HasDerivAt (fun s : ℝ => F (x+s • Pi.single i 1))
      (G i (x+t • Pi.single i 1)) t)
    (hdG : ∀ j i x t, HasDerivAt (fun s : ℝ => G j (x+s • Pi.single i 1))
      (H j i (x+t • Pi.single i 1)) t)
    (v : Fin (n+1) → ℝ) (hconv : ∀ z, 0 ≤ ∑ i, v i*(∑ j, v j*H j i z))
    {m : ℝ} (hm : 0 ≤ m) :
    HasSubgaussianMGF (gaussianVectorScore m G v)
      ⟨∑ i, v i^2, Finset.sum_nonneg (fun i _ => sq_nonneg (v i))⟩
      (tiltedLaw (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m F) := by
  let ν := Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1
  let μ := tiltedLaw ν m F
  let S := gaussianVectorScore m G v
  let Q := ∑ i, v i^2
  let B := fun z => ∑ i, v i*(∑ j, v j*H j i z)
  have hi := (ExpNormBounded.exp_lipschitz hF m).integrable (fun _ => 1)
  let : IsProbabilityMeasure μ := tiltedLaw_isProbability hi
  have hE (t : ℝ) : ExpNormBounded (fun z => Real.exp (t*S z)) :=
    gaussianVectorScore_exp_expBounded m t hG v
  have hI (t : ℝ) : Integrable (fun z => Real.exp (t*S z)) μ :=
    (hE t).integrable_tiltedLaw hF (fun _ => 1) m
  have hset : integrableExpSet S μ = univ := Set.eq_univ_of_forall hI
  have hd (t : ℝ) := hasDerivAt_mgf (X := S) (μ := μ) (t := t)
    (by simp only [hset,interior_univ,mem_univ])
  have hB : ExpNormBounded B := ExpNormBounded.sum Finset.univ fun i _ =>
    (ExpNormBounded.sum Finset.univ (fun j _ =>
      (ExpNormBounded.bddSmooth (hH j i)).const_mul (v j))).const_mul (v i)
  have hR (t : ℝ) : ExpNormBounded (fun z => Real.exp (t*S z)*t*(Q-m*B z)) :=
    ((hE t).mul (ExpNormBounded.const t)).mul ((ExpNormBounded.const Q).sub (hB.const_mul m))
  have he (t : ℝ) : (∫ z, S z*Real.exp (t*S z) ∂μ) =
      tiltedMean ν m F (fun z => Real.exp (t*S z)*t*(Q-m*B z)) := by
    rw [integral_tiltedLaw hF.continuous.measurable hi]
    exact tiltedMean_vectorScore_exp_identity hF hG hH hdF hdG v m t
  have hL (t : ℝ) : tiltedMean ν m F (fun z => (Q*t)*Real.exp (t*S z)) =
      Q*t*mgf S μ t := by
    rw [mgf,integral_tiltedLaw hF.continuous.measurable hi]
    simp only [tiltedMean,mul_assoc,integral_const_mul]
    ring
  refine ⟨hI,fun t => ?_⟩
  exact gaussian_ode_bound hd mgf_zero Q
    (fun t ht => by
      rw [he t,← hL t]
      exact tiltedMean_expNormBounded_mono hF m (hR t) ((hE t).const_mul (Q*t))
        (fun z => by
          have h := mul_nonneg hm (hconv z)
          have he0 := Real.exp_nonneg (t*S z)
          dsimp only [B] at h ⊢
          nlinarith [mul_nonneg (mul_nonneg he0 ht) h]))
    (fun t ht => by
      rw [he t,← hL t]
      exact tiltedMean_expNormBounded_mono hF m ((hE t).const_mul (Q*t)) (hR t)
        (fun z => by
          have h := mul_nonneg hm (hconv z)
          have he0 := Real.exp_nonneg (t*S z)
          dsimp only [B] at h ⊢
          nlinarith [mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos he0 ht) h])) t

end SKFluctuations.GaussianCalculus

 

 

open scoped BigOperators
namespace SKFluctuations.Hierarchy

 theorem odd_power_gap_le (k : ℕ) {x y : ℝ} (hyx : y ≤ x) :
    (x-y)^(2*k+1) ≤ (2:ℝ)^(2*k)*(x^(2*k+1)-y^(2*k+1)) := by
  have hd : 0 ≤ x-y := sub_nonneg.mpr hyx
  have hp : 0 ≤ x^(2*k+1)-y^(2*k+1) :=
    sub_nonneg.mpr ((odd_two_mul_add_one k).strictMono_pow.monotone hyx)
  have htwo : 1 ≤ (2:ℝ)^(2*k) := one_le_pow₀ (by norm_num)
  have hs : x^(2*k+1)-y^(2*k+1) ≤ (2:ℝ)^(2*k)*(x^(2*k+1)-y^(2*k+1)) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right htwo hp
  by_cases hy : 0 ≤ y
  · have h := pow_add_pow_le hd hy (by omega : 2*k+1 ≠ 0)
    rw [sub_add_cancel] at h
    exact (by linarith : (x-y)^(2*k+1) ≤ x^(2*k+1)-y^(2*k+1)).trans hs
  by_cases hx : x ≤ 0
  · have h := pow_add_pow_le hd (neg_nonneg.mpr hx) (by omega : 2*k+1 ≠ 0)
    rw [show x-y+-x = -y by ring, (odd_two_mul_add_one k).neg_pow,
      (odd_two_mul_add_one k).neg_pow] at h
    exact (by linarith : (x-y)^(2*k+1) ≤ x^(2*k+1)-y^(2*k+1)).trans hs
  · have h := add_pow_le (le_of_not_ge hx) (neg_nonneg.mpr (le_of_not_ge hy)) (2*k+1)
    simpa only [Nat.add_sub_cancel, (odd_two_mul_add_one k).neg_pow, sub_eq_add_neg] using h

 

 theorem odd_power_coercivity (k : ℕ) (x y : ℝ) :
    |x-y|^(2*k+2) ≤ (2:ℝ)^(2*k)*((x^(2*k+1)-y^(2*k+1))*(x-y)) := by
  have haux {x y : ℝ} (h : y ≤ x) :
      |x-y|^(2*k+2) ≤ (2:ℝ)^(2*k)*((x^(2*k+1)-y^(2*k+1))*(x-y)) := by
    have hh := mul_le_mul_of_nonneg_right (odd_power_gap_le k h) (sub_nonneg.mpr h)
    rw [abs_of_nonneg (sub_nonneg.mpr h),show 2*k+2=(2*k+1)+1 by omega,pow_succ]
    simpa only [mul_assoc] using hh
  rcases le_total y x with h | h
  · exact haux h
  · have hh := haux h
    rw [abs_sub_comm y x] at hh
    have he : (y^(2*k+1)-x^(2*k+1))*(y-x) =
        (x^(2*k+1)-y^(2*k+1))*(x-y) := by ring
    rwa [he] at hh

 

 theorem finite_centered_odd_covariance {S : Type*} [Fintype S]
    (p Y : S → ℝ) (hp : ∀ s, 0 ≤ p s) (hs : ∑ s, p s = 1)
    (c : ℝ) (k : ℕ) :
    (∑ s, p s*|Y s-(∑ t, p t*Y t)|^(2*k+2)) ≤
      (2:ℝ)^(2*k)*((∑ s, p s*(Y s-c)^(2*k+1)*Y s)-
        (∑ s, p s*(Y s-c)^(2*k+1))*(∑ s, p s*Y s)) := by
  let M := ∑ t, p t*Y t
  have he (s : S) : Y s-M = (Y s-c)-(M-c) := by ring
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun s _ =>
    mul_le_mul_of_nonneg_left (odd_power_coercivity k (Y s-c) (M-c)) (hp s))
  simp_rw [← he] at hsum
  have hc : (∑ s, p s*((2:ℝ)^(2*k)*(((Y s-c)^(2*k+1)-(M-c)^(2*k+1))*(Y s-M)))) =
      (2:ℝ)^(2*k)*((∑ s, p s*(Y s-c)^(2*k+1)*Y s)-
        (∑ s, p s*(Y s-c)^(2*k+1))*M) := by
    have ht (s : S) : p s*((2:ℝ)^(2*k)*(((Y s-c)^(2*k+1)-(M-c)^(2*k+1))*(Y s-M))) =
        (2:ℝ)^(2*k)*(p s*(Y s-c)^(2*k+1)*Y s-
          p s*(Y s-c)^(2*k+1)*M-(M-c)^(2*k+1)*(p s*Y s)+
          (M-c)^(2*k+1)*M*p s) := by ring
    simp only [ht,Finset.sum_add_distrib,Finset.sum_sub_distrib,
      ← Finset.sum_mul,← Finset.mul_sum,hs]
    dsimp [M]
    ring
  rw [hc] at hsum
  exact hsum

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

omit [Fintype ι] in
 theorem OrderedSteps.nonneg {a : ℝ} {steps : List (GaussianStep ι)}
    (ha : OrderedSteps a steps) : 0 ≤ a := by
  cases steps with
  | nil => exact ha.1
  | cons st tail => cases st; exact ha.1

 theorem gaussianHierarchyResponse_odd_coercivity {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) (c : ℝ) (k : ℕ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    a*(∑ s, hierarchyAtom w φ steps s x *
      |φ s v-gaussianHierarchyMean w φ (fun s => φ s v) steps x|^(2*k+2)) ≤
      (2:ℝ)^(2*k)*gaussianHierarchyResponse w φ (fun s => (φ s v-c)^(2*k+1)) v steps x := by
  have hA (s t : S) : 0 ≤
      ((φ s v-c)^(2*k+1)-(φ t v-c)^(2*k+1))*(φ s v-φ t v) := by
    by_cases hst : φ t v ≤ φ s v
    · exact mul_nonneg (sub_nonneg.mpr ((odd_two_mul_add_one k).strictMono_pow.monotone
        (sub_le_sub_right hst c))) (sub_nonneg.mpr hst)
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr
        ((odd_two_mul_add_one k).strictMono_pow.monotone
          (sub_le_sub_right (le_of_not_ge hst) c))) (sub_nonpos.mpr (le_of_not_ge hst))
  have h1 := finite_centered_odd_covariance (fun s => hierarchyAtom w φ steps s x)
    (fun s => φ s v) (fun s => hierarchyAtom_nonneg hw φ steps ha s x)
    (hierarchyAtom_sum hw φ steps ha x) c k
  have h2 := gaussianHierarchyResponse_comonotone_lower hw φ
    (fun s => (φ s v-c)^(2*k+1)) v hA steps ha x
  have h1' : (∑ s, hierarchyAtom w φ steps s x *
      |φ s v-gaussianHierarchyMean w φ (fun s => φ s v) steps x|^(2*k+2)) ≤
    (2:ℝ)^(2*k)*hierarchyCovariance w φ (fun s => (φ s v-c)^(2*k+1))
      (fun s => φ s v) steps x := by
    simpa only [hierarchyCovariance,gaussianHierarchyMean_atoms hw φ steps ha,
      mul_comm,mul_left_comm,mul_assoc] using h1
  calc
    _ ≤ a*((2:ℝ)^(2*k)*hierarchyCovariance w φ
        (fun s => (φ s v-c)^(2*k+1)) (fun s => φ s v) steps x) :=
      mul_le_mul_of_nonneg_left h1' ha.nonneg
    _ = (2:ℝ)^(2*k)*(a*hierarchyCovariance w φ
        (fun s => (φ s v-c)^(2*k+1)) (fun s => φ s v) steps x) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

 theorem gaussianHierarchyResponse_pi [DecidableEq ι] {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x v : ι → ℝ) :
    gaussianHierarchyResponse w φ A v steps x =
      ∑ i, v i*gaussianHierarchyResponse w φ A (Pi.single i 1) steps x := by
  simp_rw [gaussianHierarchyResponse_eq_lineDeriv hw φ A steps ha]
  exact (gaussianHierarchyMean_smooth hw φ A steps ha 1).lineDeriv_pi x v

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

theorem gaussianHierarchyHessian_linear_components {κ : Type*} [Fintype κ] [DecidableEq κ]
    {w : S → ℝ} (hw : ∀ s, 0 < w s) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (L : (κ → ℝ) →L[ℝ] (ι → ℝ)) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) (v u : κ → ℝ) :
    gaussianHierarchyHessian w φ steps x (L v) (L u) =
      ∑ i, u i*(∑ j, v j*gaussianHierarchyHessian w φ steps x
        (L (Pi.single j 1)) (L (Pi.single i 1))) := by
  have he (v : κ → ℝ) : L v = ∑ i, v i • L (Pi.single i 1) := by
    have hv : v = ∑ i, v i • Pi.single i 1 := by
      ext j
      simp [Pi.single_apply]
    conv_lhs => rw [hv]
    simp only [map_sum,map_smul]
  rw [gaussianHierarchyHessian_symm w φ steps x (L v) (L u),he u,
    gaussianHierarchyHessian_sum_left hw φ steps ha]
  apply Finset.sum_congr rfl
  intro i _
  rw [gaussianHierarchyHessian_smul_left hw φ steps ha,
    gaussianHierarchyHessian_symm w φ steps x _ (L v),he v,
    gaussianHierarchyHessian_sum_left hw φ steps ha]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [gaussianHierarchyHessian_smul_left hw φ steps ha]

noncomputable def hierarchyAffineScore {κ : Type*} [Fintype κ]
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (L : (κ → ℝ) →L[ℝ] (ι → ℝ)) (steps : List (GaussianStep ι))
    (x : ι → ℝ) (m : ℝ) (v z : κ → ℝ) : ℝ :=
  vectorDot v z-m*gaussianHierarchyMean w φ (fun s => φ s (L v)) steps (x+L z)

theorem hierarchyAffineScore_eq {κ : Type*} [Fintype κ] [DecidableEq κ]
    {w : S → ℝ} (hw : ∀ s, 0 < w s) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (L : (κ → ℝ) →L[ℝ] (ι → ℝ)) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) (m : ℝ) (v : κ → ℝ) :
    hierarchyAffineScore w φ L steps x m v = gaussianVectorScore m
      (fun i z => gaussianHierarchyMean w φ (fun s => φ s (L (Pi.single i 1))) steps (x+L z)) v := by
  funext z
  simp only [hierarchyAffineScore,gaussianVectorScore,
    gaussianHierarchyMean_linear_components hw φ L steps ha v]

theorem hierarchyAffineScore_hasSubgaussianMGF {n : ℕ}
    {w : S → ℝ} (hw : ∀ s, 0 < w s) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ)) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) {m : ℝ} (hm : 0 ≤ m)
    (v : Fin (n+1) → ℝ) :
    HasSubgaussianMGF (hierarchyAffineScore w φ L steps x m v)
      ⟨∑ i, v i^2, Finset.sum_nonneg (fun i _ => sq_nonneg (v i))⟩
      (tiltedLaw (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m
        (fun z => gaussianHierarchy w φ steps (x+L z))) := by
  obtain ⟨C,hF⟩ := gaussianHierarchy_lipschitz hw φ steps ha
  rw [hierarchyAffineScore_eq hw φ L steps ha x m v]
  apply gaussianVectorScore_hasSubgaussianMGF
    (hF.comp ((isometry_add_left x).lipschitzWith.comp L.lipschitzWith))
    (fun i => (gaussianHierarchyMean_smooth hw φ (fun s => φ s (L (Pi.single i 1))) steps ha 0).affine L x)
    (fun j i => (gaussianHierarchyResponse_smooth hw φ (fun s => φ s (L (Pi.single j 1)))
      (L (Pi.single i 1)) steps ha 0).affine L x)
  · intro i y t
    simpa only [Function.comp_def,map_add,map_smul,add_assoc] using
      gaussianHierarchy_hasDerivAt hw φ steps ha (x+L y) (L (Pi.single i 1)) t
  · intro j i y t
    simpa only [Function.comp_def,map_add,map_smul,add_assoc] using
      gaussianHierarchyMean_hasDerivAt hw φ (fun s => φ s (L (Pi.single j 1))) steps ha
        (x+L y) (L (Pi.single i 1)) t
  · intro z
    have hc := gaussianHierarchyHessian_nonneg hw φ steps ha (x+L z) (L v)
    rw [gaussianHierarchyHessian_linear_components hw φ L steps ha (x+L z) v v] at hc
    simpa only [gaussianHierarchyHessian] using hc
  · exact hm

theorem hierarchyAffineScore_even_bound {n : ℕ}
    {w : S → ℝ} (hw : ∀ s, 0 < w s) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ)) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) {m : ℝ} (hm : 0 ≤ m)
    (v : Fin (n+1) → ℝ) (k : ℕ) :
    tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m
      (fun z => gaussianHierarchy w φ steps (x+L z))
      (fun z => hierarchyAffineScore w φ L steps x m v z^(2*k)) ≤
        gaussianEvenConstant k*(∑ i, v i^2)^k := by
  obtain ⟨C,hF⟩ := gaussianHierarchy_lipschitz hw φ steps ha
  rw [hierarchyAffineScore_eq hw φ L steps ha x m v]
  apply tiltedMean_vectorScore_even_bound
    (hF.comp ((isometry_add_left x).lipschitzWith.comp L.lipschitzWith))
    (fun i => (gaussianHierarchyMean_smooth hw φ (fun s => φ s (L (Pi.single i 1))) steps ha 0).affine L x)
    (fun j i => (gaussianHierarchyResponse_smooth hw φ (fun s => φ s (L (Pi.single j 1)))
      (L (Pi.single i 1)) steps ha 0).affine L x)
  · intro i y t
    simpa only [Function.comp_def,map_add,map_smul,add_assoc] using
      gaussianHierarchy_hasDerivAt hw φ steps ha (x+L y) (L (Pi.single i 1)) t
  · intro j i y t
    simpa only [Function.comp_def,map_add,map_smul,add_assoc] using
      gaussianHierarchyMean_hasDerivAt hw φ (fun s => φ s (L (Pi.single j 1))) steps ha
        (x+L y) (L (Pi.single i 1)) t
  · intro z
    have hc := gaussianHierarchyHessian_nonneg hw φ steps ha (x+L z) (L v)
    rw [gaussianHierarchyHessian_linear_components hw φ L steps ha (x+L z) v v] at hc
    simpa only [gaussianHierarchyHessian] using hc
  · exact hm

 

theorem tiltedMean_hierarchyAffineScore {n : ℕ}
    {w : S → ℝ} (hw : ∀ s, 0 < w s) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ)) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) (m : ℝ)
    (A : S → ℝ) (v : Fin (n+1) → ℝ) :
    tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m
      (fun z => gaussianHierarchy w φ steps (x+L z))
      (fun z => gaussianHierarchyMean w φ A steps (x+L z)*hierarchyAffineScore w φ L steps x m v z) =
    tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m
      (fun z => gaussianHierarchy w φ steps (x+L z))
      (fun z => gaussianHierarchyResponse w φ A (L v) steps (x+L z)) := by
  obtain ⟨C,hF⟩ := gaussianHierarchy_lipschitz hw φ steps ha
  let M := fun z => gaussianHierarchyMean w φ A steps (x+L z)
  have hM : BddSmooth 1 M := (gaussianHierarchyMean_smooth hw φ A steps ha 1).affine L x
  have hd (i) (y : Fin (n+1) → ℝ) (t : ℝ) :
    HasDerivAt (fun s => M (y+s • Pi.single i 1))
      (gaussianHierarchyResponse w φ A (L (Pi.single i 1)) steps (x+L (y+t • Pi.single i 1))) t := by
    simpa only [M,map_add,map_smul,add_assoc] using
      gaussianHierarchyMean_hasDerivAt hw φ A steps ha (x+L y) (L (Pi.single i 1)) t
  have he (z : Fin (n+1) → ℝ) :
      (∑ i, v i*gaussianHierarchyResponse w φ A (L (Pi.single i 1)) steps (x+L z)) =
        gaussianHierarchyResponse w φ A (L v) steps (x+L z) := by
    have hdir (u : Fin (n+1) → ℝ) :
        lineDeriv ℝ M z u = gaussianHierarchyResponse w φ A (L u) steps (x+L z) := by
      apply HasLineDerivAt.lineDeriv
      simpa only [HasLineDerivAt,M,map_add,map_smul,add_assoc,zero_smul,add_zero] using
        gaussianHierarchyMean_hasDerivAt hw φ A steps ha (x+L z) (L u) 0
    simpa only [hdir] using (hM.lineDeriv_pi z v).symm
  rw [hierarchyAffineScore_eq hw φ L steps ha x m v]
  have hh := tiltedMean_vectorScore
    (hF.comp ((isometry_add_left x).lipschitzWith.comp L.lipschitzWith))
    (fun i => (gaussianHierarchyMean_smooth hw φ (fun s => φ s (L (Pi.single i 1))) steps ha 0).affine L x)
    (fun i y t => by
      simpa only [Function.comp_def,map_add,map_smul,add_assoc] using
        gaussianHierarchy_hasDerivAt hw φ steps ha (x+L y) (L (Pi.single i 1)) t)
    (ExpNormBounded.bddSmooth hM.1)
    (fun i => ExpNormBounded.bddSmooth
      ((gaussianHierarchyResponse_smooth hw φ A (L (Pi.single i 1)) steps ha 0).affine L x))
    hd m v
  simpa only [M,he,Function.comp_def] using hh

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
variable {E D : Type*} [AddCommMonoid E] [MeasurableSpace E]
  [MeasurableAdd₂ E] [MeasurableSpace D]

def forwardScore : (n : ℕ) → (Fin n → D → E) →
    (Fin n → E → D → ℝ) → E → (Fin n → D) → ℝ
  | 0, _, _, _, _ => 0
  | n+1, inc, S, x, p => S 0 x (p 0) +
      forwardScore n (fun i => inc i.succ) (fun i => S i.succ)
        (x+inc 0 (p 0)) (Fin.tail p)

theorem measurable_forwardScore (n : ℕ) {inc : Fin n → D → E}
    {S : Fin n → E → D → ℝ} (hinc : ∀ i, Measurable (inc i))
    (hS : ∀ i, Measurable (Function.uncurry (S i))) :
    Measurable (fun xp : E × (Fin n → D) => forwardScore n inc S xp.1 xp.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have ht : Measurable (fun xp : E × (Fin (n+1) → D) => S 0 xp.1 (xp.2 0)) :=
      (hS 0).comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
    have hs : Measurable (fun xp : E × (Fin (n+1) → D) =>
        (xp.1+inc 0 (xp.2 0), Fin.tail xp.2)) :=
      (measurable_fst.add ((hinc 0).comp ((measurable_pi_apply 0).comp measurable_snd))).prodMk
        (Measurable.of_eval (fun i => (measurable_pi_apply i.succ).comp measurable_snd))
    exact ht.add ((ih (fun i => hinc i.succ) (fun i => hS i.succ)).comp hs)

noncomputable def forwardLaw (n : ℕ) (μ : Fin n → Measure D)
    (inc : Fin n → D → E) (T : Fin n → E → D → ℝ≥0∞) (x : E) :
    Measure (Fin n → D) := (Measure.pi μ).withDensity (forwardWeight n inc T x)

theorem forwardLaw_isProbability (n : ℕ) (μ : Fin n → Measure D)
    [∀ i, IsProbabilityMeasure (μ i)] {inc : Fin n → D → E} {T : Fin n → E → D → ℝ≥0∞}
    (hinc : ∀ i, Measurable (inc i)) (hT : ∀ i, Measurable (Function.uncurry (T i)))
    (h1 : ∀ i x, ∫⁻ z, T i x z ∂μ i = 1) (x : E) :
    IsProbabilityMeasure (forwardLaw n μ inc T x) := by
  refine ⟨?_⟩
  rw [forwardLaw,withDensity_apply _ MeasurableSet.univ]
  simpa only [Measure.restrict_univ] using lintegral_forwardWeight n μ hinc hT h1 x

theorem lintegral_forwardScore_exp_le (n : ℕ) (μ : Fin n → Measure D)
    [∀ i, IsProbabilityMeasure (μ i)] {inc : Fin n → D → E}
    {T : Fin n → E → D → ℝ≥0∞} {S : Fin n → E → D → ℝ}
    (hinc : ∀ i, Measurable (inc i)) (hT : ∀ i, Measurable (Function.uncurry (T i)))
    (hS : ∀ i, Measurable (Function.uncurry (S i))) (c : Fin n → ℝ≥0)
    (hmgf : ∀ i x t, (∫⁻ z, T i x z*ENNReal.ofReal (Real.exp (t*S i x z)) ∂μ i) ≤
      ENNReal.ofReal (Real.exp (c i*t^2/2))) (x : E) (t : ℝ) :
    (∫⁻ p, forwardWeight n inc T x p*ENNReal.ofReal (Real.exp (t*forwardScore n inc S x p))
      ∂Measure.pi μ) ≤ ENNReal.ofReal (Real.exp ((∑ i, c i : ℝ≥0)*t^2/2)) := by
  induction n generalizing x with
  | zero => simp [forwardWeight,forwardScore]
  | succ n ih =>
    have hw : Measurable (forwardWeight (n+1) inc T x) :=
      (measurable_forwardWeight _ hinc hT).comp (measurable_const.prodMk measurable_id)
    have hs : Measurable (forwardScore (n+1) inc S x) :=
      (measurable_forwardScore _ hinc hS).comp (measurable_const.prodMk measurable_id)
    have hsplit := lintegral_fin_cons μ (hw.mul ((hs.const_mul t).exp.ennreal_ofReal))
    change (∫⁻ p, forwardWeight (n+1) inc T x p *
      ENNReal.ofReal (Real.exp (t*forwardScore (n+1) inc S x p)) ∂Measure.pi μ) = _ at hsplit
    rw [hsplit]
    simp only [Pi.mul_apply,forwardWeight,forwardScore,Fin.cons_zero,Fin.tail_cons,mul_add,Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_nonneg _)]
    have htail (z : D) := ih (fun i => μ i.succ) (fun i => hinc i.succ)
      (fun i => hT i.succ) (fun i => hS i.succ) (fun i => c i.succ)
      (fun i => hmgf i.succ) (x+inc 0 z)
    let C := ENNReal.ofReal (Real.exp ((∑ i : Fin n, c i.succ : ℝ≥0)*t^2/2))
    calc
      _ ≤ ∫⁻ z, (T 0 x z*ENNReal.ofReal (Real.exp (t*S 0 x z)))*C ∂μ 0 := by
        apply lintegral_mono
        intro z
        have hw' : Measurable (forwardWeight n (fun i => inc i.succ) (fun i => T i.succ) (x+inc 0 z)) := (measurable_forwardWeight n (fun i => hinc i.succ)
          (fun i => hT i.succ)).comp
          (measurable_const.prodMk (measurable_id : Measurable (id : (Fin n → D) → _)))
        have hs' : Measurable (forwardScore n (fun i => inc i.succ) (fun i => S i.succ) (x+inc 0 z)) := (measurable_forwardScore n (fun i => hinc i.succ)
          (fun i => hS i.succ)).comp
          (measurable_const.prodMk (measurable_id : Measurable (id : (Fin n → D) → _)))
        simp_rw [show ∀ p : Fin n → D,
          (T 0 x z*forwardWeight n (fun i => inc i.succ) (fun i => T i.succ) (x+inc 0 z) p)*
              (ENNReal.ofReal (Real.exp (t*S 0 x z))*ENNReal.ofReal
                (Real.exp (t*forwardScore n (fun i => inc i.succ) (fun i => S i.succ) (x+inc 0 z) p))) =
          (T 0 x z*ENNReal.ofReal (Real.exp (t*S 0 x z)))*
            (forwardWeight n (fun i => inc i.succ) (fun i => T i.succ) (x+inc 0 z) p*
              ENNReal.ofReal (Real.exp (t*forwardScore n (fun i => inc i.succ) (fun i => S i.succ) (x+inc 0 z) p))) by
                intro p; ring]
        have heq := lintegral_const_mul (T 0 x z*ENNReal.ofReal (Real.exp (t*S 0 x z)))
          (hw'.mul ((hs'.const_mul t).exp.ennreal_ofReal)) (μ := Measure.pi (fun i => μ i.succ))
        simp only [Pi.mul_apply] at heq
        rw [heq]
        gcongr; exact htail z
      _ = (∫⁻ z, T 0 x z*ENNReal.ofReal (Real.exp (t*S 0 x z)) ∂μ 0)*C := by
        apply lintegral_mul_const
        exact ((hT 0).comp (measurable_const.prodMk measurable_id)).mul
          ((((hS 0).comp (measurable_const.prodMk measurable_id)).const_mul t).exp.ennreal_ofReal)
      _ ≤ ENNReal.ofReal (Real.exp (c 0*t^2/2))*C := by gcongr; exact hmgf 0 x t
      _ = _ := by
        dsimp only [C]
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),← Real.exp_add,Fin.sum_univ_succ,NNReal.coe_add]
        congr 2
        ring

 

theorem forwardScore_hasSubgaussianMGF (n : ℕ) (μ : Fin n → Measure D)
    [∀ i, IsProbabilityMeasure (μ i)] {inc : Fin n → D → E}
    {T : Fin n → E → D → ℝ≥0∞} {S : Fin n → E → D → ℝ}
    (hinc : ∀ i, Measurable (inc i)) (hT : ∀ i, Measurable (Function.uncurry (T i)))
    (hS : ∀ i, Measurable (Function.uncurry (S i))) (c : Fin n → ℝ≥0)
    (hmgf : ∀ i x, HasSubgaussianMGF (S i x) (c i) ((μ i).withDensity (T i x))) (x : E) :
    HasSubgaussianMGF (forwardScore n inc S x) (∑ i, c i) (forwardLaw n μ inc T x) := by
  have ht (i) (y : E) : Measurable (T i y) := (hT i).comp (measurable_const.prodMk measurable_id)
  have hs (i) (y : E) : Measurable (S i y) := (hS i).comp (measurable_const.prodMk measurable_id)
  have hw : Measurable (forwardWeight n inc T x) :=
    (measurable_forwardWeight _ hinc hT).comp (measurable_const.prodMk measurable_id)
  have hS' : Measurable (forwardScore n inc S x) :=
    (measurable_forwardScore _ hinc hS).comp (measurable_const.prodMk measurable_id)
  have hL (t : ℝ) : (∫⁻ p, ENNReal.ofReal (Real.exp (t*forwardScore n inc S x p))
      ∂forwardLaw n μ inc T x) ≤ ENNReal.ofReal (Real.exp ((∑ i, c i : ℝ≥0)*t^2/2)) := by
    rw [forwardLaw,lintegral_withDensity_eq_lintegral_mul _ hw ((hS'.const_mul t).exp.ennreal_ofReal)]
    exact lintegral_forwardScore_exp_le n μ hinc hT hS c (fun i y t => by
      have hh := ENNReal.ofReal_le_ofReal (hmgf i y |>.mgf_le t)
      rw [mgf,ofReal_integral_eq_lintegral_ofReal (hmgf i y |>.integrable_exp_mul t)
        (Eventually.of_forall fun z => Real.exp_nonneg _),
        lintegral_withDensity_eq_lintegral_mul _ (ht i y) (((hs i y).const_mul t).exp.ennreal_ofReal)] at hh
      exact hh) x t
  have hi (t : ℝ) : Integrable (fun p => Real.exp (t*forwardScore n inc S x p)) (forwardLaw n μ inc T x) := by
    refine ⟨((hS'.const_mul t).exp).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun p => Real.exp_nonneg _)]
    exact (hL t).trans_lt ENNReal.ofReal_lt_top
  refine ⟨hi,fun t => ?_⟩
  have hh := hL t
  rw [← ofReal_integral_eq_lintegral_ofReal (hi t) (Eventually.of_forall fun p => Real.exp_nonneg _)] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg _)).mp hh

end SKFluctuations.Hierarchy

end

end OAI
