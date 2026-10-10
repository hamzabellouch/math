import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CoulombNear

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter Laplacian InnerProductSpace MeasureTheory
open scoped Topology BigOperators

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE

lemma second_fderiv_scalar_comp {u : TFSpace → ℝ} {g : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (hg : ContDiff ℝ 2 g) (x v : TFSpace) :
    fderiv ℝ (fderiv ℝ (g ∘ u)) x v v =
      deriv (deriv g) (u x)*(fderiv ℝ u x v)^2+
        deriv g (u x)*fderiv ℝ (fderiv ℝ u) x v v := by
  have hud (z : TFSpace) := (hu.differentiable (by norm_num) z)
  have hgd (z : ℝ) := (hg.differentiable (by norm_num) z)
  have hud' (z : TFSpace) := ((hu.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).differentiable (by norm_num) z)
  have hgd' (z : ℝ) := differentiableAt_deriv_of_contDiffAt (hg.contDiffAt (x := z))
  have hcu := hg.comp hu
  have hcu' := (hcu.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).differentiable (by norm_num) x
  have he : (fun z => fderiv ℝ (g ∘ u) z v) =
      fun z => deriv g (u z)*fderiv ℝ u z v := by
    funext z
    rw [((hgd (u z)).hasDerivAt.comp_hasFDerivAt z (hud z).hasFDerivAt).fderiv]
    rfl
  rw [← fderiv_apply_const_scalar hcu' v v,he]
  have h1 := (hgd' (u x)).hasDerivAt.comp_hasFDerivAt x (hud x).hasFDerivAt
  have h2 : DifferentiableAt ℝ (fun z => fderiv ℝ u z v) x :=
    (hud' x).clm_apply (differentiableAt_const v)
  rw [show (fun z => deriv g (u z)*fderiv ℝ u z v) =
      (deriv g ∘ u)*(fun z => fderiv ℝ u z v) from rfl,
    fderiv_mul h1.differentiableAt h2]
  simp only [add_apply,smul_apply,smul_eq_mul,
    Function.comp_apply]
  rw [h1.fderiv,fderiv_apply_const_scalar (hud' x)]
  simp only [smul_apply,smul_eq_mul]
  ring

lemma laplacian_scalar_comp_lower {u : TFSpace → ℝ} {g : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (hg : ContDiff ℝ 2 g) (x : TFSpace)
    (hpos : 0 ≤ deriv (deriv g) (u x)) :
    deriv g (u x)*Δ u x ≤ Δ (g ∘ u) x := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [second_fderiv_scalar_comp hu hg]
  exact le_add_of_nonneg_left (mul_nonneg hpos (sq_nonneg _))

def smoothPositive (ε t : ℝ) : ℝ := (t+Real.sqrt (t^2+ε^2))/2

lemma smoothPositive_contDiff {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 2 (smoothPositive ε) := by
  exact (contDiff_id.add (((contDiff_id.pow 2).add contDiff_const).sqrt
    (fun t => ne_of_gt (by positivity)))).div_const 2

lemma smoothRoot_hasDerivAt {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (fun z : ℝ => Real.sqrt (z^2+ε^2))
      (t/Real.sqrt (t^2+ε^2)) t := by
  have hq : t^2+ε^2 ≠ 0 := ne_of_gt (by positivity)
  have hd : HasDerivAt (fun z : ℝ => Real.sqrt (z^2+ε^2))
      (2*t/(2*Real.sqrt (t^2+ε^2))) t := by
    simpa only [Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one] using
      ((((hasDerivAt_id t).pow 2).add_const (ε^2)).sqrt hq)
  convert hd using 1
  ring

lemma smoothPositive_deriv {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    deriv (smoothPositive ε) t = (1+t/Real.sqrt (t^2+ε^2))/2 := by
  have hh := ((hasDerivAt_id t).add (smoothRoot_hasDerivAt hε t)).div_const 2
  exact hh.deriv

lemma smoothPositive_deriv_bounds {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 ≤ deriv (smoothPositive ε) t ∧ deriv (smoothPositive ε) t ≤ 1 := by
  have hq : 0 < Real.sqrt (t^2+ε^2) := Real.sqrt_pos.mpr (by positivity)
  have hs := Real.sq_sqrt (by positivity : 0 ≤ t^2+ε^2)
  have ha : |t| ≤ Real.sqrt (t^2+ε^2) := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg ε]
  have hlo : -1 ≤ t/Real.sqrt (t^2+ε^2) := (le_div_iff₀ hq).mpr (by linarith [(abs_le.mp ha).1])
  have hhi : t/Real.sqrt (t^2+ε^2) ≤ 1 := (div_le_iff₀ hq).mpr (by linarith [(abs_le.mp ha).2])
  rw [smoothPositive_deriv hε]
  constructor <;> linarith

lemma smoothPositive_second_nonneg {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 ≤ deriv (deriv (smoothPositive ε)) t := by
  have hq : t^2+ε^2 ≠ 0 := ne_of_gt (by positivity)
  have hqs : 0 < Real.sqrt (t^2+ε^2) := Real.sqrt_pos.mpr (by positivity)
  have hd' := smoothRoot_hasDerivAt hε t
  have he : deriv (smoothPositive ε) = fun z => (1+z/Real.sqrt (z^2+ε^2))/2 :=
    funext (smoothPositive_deriv hε)
  rw [he]
  have hquot := (hasDerivAt_id t).div hd' hqs.ne'
  have hh : HasDerivAt (fun z => (1+z/Real.sqrt (z^2+ε^2))/2)
      (((Real.sqrt (t^2+ε^2)-t*(t/Real.sqrt (t^2+ε^2)))/Real.sqrt (t^2+ε^2)^2)/2) t := by
    simpa only [Pi.add_apply,Pi.div_apply,id_eq,one_mul,zero_add] using
      ((hasDerivAt_const t 1).add hquot |>.div_const 2)
  rw [hh.deriv]
  have hnum : 0 ≤ Real.sqrt (t^2+ε^2)-t*(t/Real.sqrt (t^2+ε^2)) := by
    rw [← mul_div_assoc,sub_nonneg,div_le_iff₀ hqs]
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ t^2+ε^2),sq_nonneg ε]
  exact div_nonneg (div_nonneg (by simpa only [one_mul] using hnum) (sq_nonneg _)) (by norm_num)

def smoothMaximum (ε : ℝ) (u v : TFSpace → ℝ) (x : TFSpace) : ℝ :=
  v x+smoothPositive ε (u x-v x)

lemma smoothMaximum_contDiff {ε : ℝ} (hε : 0 < ε) {u v : TFSpace → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
    ContDiff ℝ 2 (smoothMaximum ε u v) :=
  hv.add ((smoothPositive_contDiff hε).comp (hu.sub hv))

theorem smoothMaximum_laplacian_lower {ε : ℝ} (hε : 0 < ε) {u v : TFSpace → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (x : TFSpace) {h : ℝ}
    (huL : h ≤ Δ u x) (hvL : h ≤ Δ v x) :
    h ≤ Δ (smoothMaximum ε u v) x := by
  have hd := laplacian_scalar_comp_lower (hu.sub hv) (smoothPositive_contDiff hε) x
    (smoothPositive_second_nonneg hε (u x-v x))
  obtain ⟨hp0,hp1⟩ := smoothPositive_deriv_bounds hε (u x-v x)
  change deriv (smoothPositive ε) (u x-v x)*Δ (u-v) x ≤ Δ (smoothPositive ε ∘ (u-v)) x at hd
  rw [(hu.contDiffAt (x := x)).laplacian_sub hv.contDiffAt] at hd
  change deriv (smoothPositive ε) (u x-v x)*(Δ u x-Δ v x) ≤ _ at hd
  change h ≤ Δ (v+smoothPositive ε ∘ (u-v)) x
  have hc : ContDiff ℝ 2 (smoothPositive ε ∘ (u-v)) :=
    (smoothPositive_contDiff hε).comp (hu.sub hv)
  rw [hv.contDiffAt.laplacian_add hc.contDiffAt]
  nlinarith [mul_nonneg hp0 (sub_nonneg.mpr huL),
    mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hvL)]

lemma smoothPositive_bounds {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    max t 0 ≤ smoothPositive ε t ∧ smoothPositive ε t ≤ max t 0+ε/2 := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ t^2+ε^2)
  have hp := Real.sqrt_nonneg (t^2+ε^2)
  have hlo : |t| ≤ Real.sqrt (t^2+ε^2) := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg ε]
  have hhi : Real.sqrt (t^2+ε^2) ≤ |t|+ε := by
    nlinarith [abs_nonneg t,sq_abs t,mul_nonneg (abs_nonneg t) hε]
  by_cases ht : 0 ≤ t
  · rw [max_eq_left ht,abs_of_nonneg ht] at *
    dsimp [smoothPositive]
    constructor <;> linarith
  · have ht' := le_of_not_ge ht
    rw [max_eq_right ht',abs_of_nonpos ht'] at *
    dsimp [smoothPositive]
    constructor <;> linarith

lemma smoothMaximum_bounds {ε : ℝ} (hε : 0 ≤ ε) (u v : TFSpace → ℝ) (x : TFSpace) :
    max (u x) (v x) ≤ smoothMaximum ε u v x ∧
    smoothMaximum ε u v x ≤ max (u x) (v x)+ε/2 := by
  obtain ⟨hl,hh⟩ := smoothPositive_bounds hε (u x-v x)
  dsimp [smoothMaximum]
  by_cases hvu : v x ≤ u x
  · rw [max_eq_left hvu,max_eq_left (sub_nonneg.mpr hvu)] at *
    constructor <;> linarith
  · have huv := le_of_not_ge hvu
    rw [max_eq_right huv,max_eq_right (sub_nonpos.mpr huv)] at *
    constructor <;> linarith

lemma smoothMaximum_norm_bound {ε C : ℝ} (hε : 0 ≤ ε) {u v : TFSpace → ℝ}
    (x : TFSpace) (hu : ‖u x‖ ≤ C) (hv : ‖v x‖ ≤ C) :
    ‖smoothMaximum ε u v x‖ ≤ C+ε/2 := by
  have hb := smoothMaximum_bounds hε u v x
  have hu' := abs_le.mp hu
  have hv' := abs_le.mp hv
  rw [Real.norm_eq_abs,abs_le]
  constructor
  · linarith [le_max_left (u x) (v x)]
  · linarith [max_le hu'.2 hv'.2]

lemma smoothMaximum_tendsto {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    {u v : ι → TFSpace → ℝ} {a b : ℝ} (x : TFSpace)
    (hε0 : ∀ᶠ i in l, 0 ≤ ε i) (hε : Tendsto ε l (𝓝 0))
    (hu : Tendsto (fun i => u i x) l (𝓝 a))
    (hv : Tendsto (fun i => v i x) l (𝓝 b)) :
    Tendsto (fun i => smoothMaximum (ε i) (u i) (v i) x) l (𝓝 (max a b)) := by
  have hm := hu.max hv
  have he := hm.add (hε.div_const 2)
  simp only [zero_div,add_zero] at he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hm he
  · filter_upwards [hε0] with i hi
    exact (smoothMaximum_bounds hi (u i) (v i) x).1
  · filter_upwards [hε0] with i hi
    exact (smoothMaximum_bounds hi (u i) (v i) x).2

end CoulombBarrier

end

end OAI
