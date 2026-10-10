import Mathlib
import OAI.Analysis.AffineBernstein.GaussCoordinates

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section SupportArea
open Filter
open scoped Topology
variable {n : ℕ}

lemma homogeneousSupport_gradient_monotone {K : Set (Space n)}
    (hK : IsCompact K) (hne : K.Nonempty) {x y : Space n}
    (hx : DifferentiableAt ℝ (homogeneousSupport K) x)
    (hy : DifferentiableAt ℝ (homogeneousSupport K) y) :
    0 ≤ inner ℝ (x-y) (gradient (homogeneousSupport K) x -
      gradient (homogeneousSupport K) y) := by
  obtain ⟨hgx,heqx⟩ := gaussPoint_mem_support hK hne hx
  obtain ⟨hgy,heqy⟩ := gaussPoint_mem_support hK hne hy
  have hxy := homogeneousSupport_le hK hgy x
  have hyx := homogeneousSupport_le hK hgx y
  rw [heqx] at hxy
  rw [heqy] at hyx
  dsimp only [gaussPoint] at hxy hyx
  simp only [inner_sub_left,inner_sub_right]
  linarith

/- The identity-shifted true Gauss map is injective wherever the support is
smooth, even though the punctured domain is not convex. -/
lemma shiftedGauss_injOn {K : Set (Space n)} (hK : IsCompact K) (hne : K.Nonempty)
    {D : Set (Space n)} (hD : ∀ x ∈ D, DifferentiableAt ℝ (homogeneousSupport K) x) :
    Set.InjOn (fun x => gradient (homogeneousSupport K) x + x) D := by
  intro x hx y hy he
  have hm := homogeneousSupport_gradient_monotone hK hne (hD x hx) (hD y hy)
  have he' : gradient (homogeneousSupport K) x - gradient (homogeneousSupport K) y = y-x :=
    sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using he)
  rw [he',show y-x = -(x-y) by abel,inner_neg_right,real_inner_self_eq_norm_sq] at hm
  have hh : ‖x-y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hh)

lemma homogeneousSupport_second_nonneg {K : Set (Space n)}
    (hK : IsCompact K) (hne : K.Nonempty) {x : Space n}
    (hh : ContDiffAt ℝ ∞ (homogeneousSupport K) x) (v : Space n) :
    0 ≤ fderiv ℝ (fderiv ℝ (homogeneousSupport K)) x v v := by
  let H := homogeneousSupport K
  let G := gradient H
  let γ := fun t : ℝ => x+t • v
  let f := fun t : ℝ => inner ℝ (G (γ t)) v
  have hγ : HasDerivAt γ v 0 := by
    simpa [γ] using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have hdG := (contDiffAt_gradient hh).differentiableAt (by simp)
  have hdf : HasDerivAt f (inner ℝ (fderiv ℝ G x v) v) 0 := by
    have hdG' : HasFDerivAt G (fderiv ℝ G x) (γ 0) := by simpa [G,H,γ] using hdG.hasFDerivAt
    simpa [f,γ] using (hdG'.comp_hasDerivAt 0 hγ).inner ℝ (hasDerivAt_const 0 v)
  have hds : ∀ᶠ t in 𝓝 (0:ℝ), DifferentiableAt ℝ H (γ t) := by
    have he := (hh.of_le (show (1:WithTop ℕ∞) ≤ (∞:WithTop ℕ∞) by simp)).eventually (by simp)
    have hc : Tendsto γ (𝓝 0) (𝓝 x) := by simpa only [ContinuousAt,γ,zero_smul,add_zero] using hγ.continuousAt
    filter_upwards [hc.eventually he] with t ht
    exact ht.differentiableAt (by norm_num)
  have hlim := hasDerivAt_iff_tendsto_slope.mp hdf
  have hn : 0 ≤ inner ℝ (fderiv ℝ G x v) v := by
    apply ge_of_tendsto hlim
    filter_upwards [hds.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht hnot
    have hm := homogeneousSupport_gradient_monotone hK hne ht (hh.differentiableAt (by simp))
    have hm' : 0 ≤ t * (f t - f 0) := by
      simpa [γ,f,G,H,inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_comm v,
        mul_sub] using hm
    rw [slope_def_field]
    simp only [sub_zero]
    exact div_nonneg_iff.mpr (by
      rcases le_total 0 t with h | h
      · exact Or.inl ⟨by
          have hp : 0 < t := lt_of_le_of_ne h (Ne.symm hnot)
          exact nonneg_of_mul_nonneg_right hm' hp,h⟩
      · exact Or.inr ⟨by
          have hp : t < 0 := lt_of_le_of_ne h hnot
          exact nonpos_of_mul_nonneg_right hm' hp,h⟩)
  simpa only [G,H,inner_fderiv_gradient hh] using hn

lemma homogeneousSupport_hessian_posSemidef {K : Set (Space n)}
    (hK : IsCompact K) (hne : K.Nonempty) {x : Space n}
    (hh : ContDiffAt ℝ ∞ (homogeneousSupport K) x) :
    (hessian (homogeneousSupport K) x).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.isHermitian_iff_isSymm.mpr (by
      ext i j
      rw [Matrix.transpose_apply,hessian_eq_second hh,hessian_eq_second hh]
      exact hh.isSymmSndFDerivAt (by simp) _ _)
  · intro v
    have hp := homogeneousSupport_second_nonneg hK hne hh (WithLp.toLp 2 v)
    rw [second_fderiv_eq_sum hh] at hp
    simpa [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc] using hp

end SupportArea

open scoped Matrix

end AffineBernstein
end

end OAI
