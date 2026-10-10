import Mathlib
import OAI.MeasureTheory.Falconer.Angular.AngularBinKernel
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Angular.CoordNormBound

namespace OAI

/-! Canonical spherical measures and differential identities. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer
open Set Metric
open scoped ContDiff Topology

lemma scalar_cap_partitionND (t : ℝ) (M : ℤ)
    (hlo : -M ≤ ⌊t⌋) (hhi : ⌊t⌋+1 ≤ M) :
    ∑ k ∈ Finset.Icc (-M) M, PlanarFalconer.angularBinKernel (t-k) = 1 := by
  classical
  have hsub : ({⌊t⌋,⌊t⌋+1} : Finset ℤ) ⊆ Finset.Icc (-M) M := by
    intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> simp only [Finset.mem_Icc] <;> omega
  rw [← Finset.sum_subset hsub]
  · simpa only [Finset.sum_pair (show ⌊t⌋ ≠ ⌊t⌋+1 by omega)] using
      PlanarFalconer.angularBinKernel_floor_partition t
  · intro k _ hk
    exact PlanarFalconer.angularBinKernel_translate_zero t k (by simpa using hk)

noncomputable def fullCapGridND (d : ℕ) (δ : ℝ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(⌈δ⁻¹⌉+2)) (⌈δ⁻¹⌉+2))

lemma fullCapGridND_partition {d : ℕ} {δ : ℝ} (hδ : 0<δ)
    (w : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖ ≤ 1) :
    ∑ a ∈ fullCapGridND d δ, tensorCapND δ a w = 1 := by
  classical
  simp only [tensorCapND_apply,fullCapGridND]
  rw [← Finset.prod_univ_sum (fun _ : Fin d => Finset.Icc (-(⌈δ⁻¹⌉+2)) (⌈δ⁻¹⌉+2))
    (fun i k => PlanarFalconer.angularBinKernel (δ⁻¹*w i-k))]
  have he (i : Fin d) : ∑ k ∈ Finset.Icc (-(⌈δ⁻¹⌉+2)) (⌈δ⁻¹⌉+2),
      PlanarFalconer.angularBinKernel (δ⁻¹*w i-k) = 1 := by
    have hb : |w i| ≤ 1 := (show |w i| ≤ ‖w‖ by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le w i).trans hw
    have hlow := Int.lt_floor_add_one (δ⁻¹*w i)
    have hhigh := Int.floor_le (δ⁻¹*w i)
    have hceil := Int.le_ceil (δ⁻¹)
    have hm := mul_le_mul_of_nonneg_left (abs_le.mp hb).1 (le_of_lt (inv_pos.mpr hδ))
    have hp := mul_le_mul_of_nonneg_left (abs_le.mp hb).2 (le_of_lt (inv_pos.mpr hδ))
    apply scalar_cap_partitionND
    · have h : -((⌈δ⁻¹⌉:ℝ)+2) ≤ (⌊δ⁻¹*w i⌋:ℝ) := by linarith
      exact_mod_cast h
    · have h : (⌊δ⁻¹*w i⌋:ℝ)+1 ≤ (⌈δ⁻¹⌉:ℝ)+2 := by linarith
      exact_mod_cast h
  simp only [he,Finset.prod_const_one]

noncomputable def capGridPointND {d : ℕ} (δ : ℝ) (a : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) :=
  δ • WithLp.toLp 2 (fun i => (a i:ℝ))

lemma tensorCapND_support_dist {d : ℕ} {δ : ℝ} (hδ : 0<δ)
    (a : Fin d → ℤ) {w : EuclideanSpace ℝ (Fin d)}
    (hw : tensorCapND δ a w ≠ 0) : dist w (capGridPointND δ a) ≤ (d+1:ℝ)*δ := by
  rw [dist_eq_norm]
  apply coord_norm_boundND hδ.le
  have hc := tensorCapKernelND_support hw
  intro i
  have hc : |δ⁻¹*w i-a i| ≤ 1 := hc i
  have he : (w-capGridPointND δ a) i = δ*(δ⁻¹*w i-a i) := by
    change w i-δ*(a i:ℝ) = _
    field_simp
  rw [he,abs_mul,abs_of_pos hδ]
  exact mul_le_of_le_one_right hδ.le hc

lemma tensorCapND_tsupport_dist {d : ℕ} {δ : ℝ} (hδ : 0<δ)
    (a : Fin d → ℤ) {w : EuclideanSpace ℝ (Fin d)}
    (hw : w ∈ tsupport (tensorCapND δ a)) : dist w (capGridPointND δ a) ≤ (d+1:ℝ)*δ := by
  have hs : tsupport (tensorCapND δ a) ⊆ closedBall (capGridPointND δ a) ((d+1:ℝ)*δ) := by
    apply closure_minimal _ isClosed_closedBall
    intro w hw
    exact tensorCapND_support_dist hδ a hw
  exact hs hw

noncomputable def sphereCapGridND (d : ℕ) (δ : ℝ) : Finset (Fin d → ℤ) := by
  classical
  exact (fullCapGridND d δ).filter (fun a => 1/2 ≤ ‖capGridPointND δ a‖)

lemma sphereCapGridND_partition {d : ℕ} {δ : ℝ} (hδ : 0<δ)
    (hsmall : (d+1:ℝ)*δ ≤ 1/2) (w : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖=1) :
    ∑ a ∈ sphereCapGridND d δ, tensorCapND δ a w = 1 := by
  classical
  rw [← fullCapGridND_partition hδ w hw.le]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro a ha hna
  by_contra hn
  have hd := tensorCapND_support_dist hδ a hn
  have he : 1/2 ≤ ‖capGridPointND δ a‖ := by
    have hh := norm_le_insert' w (capGridPointND δ a)
    rw [hw,← dist_eq_norm] at hh
    linarith
  exact hna (Finset.mem_filter.mpr ⟨ha,he⟩)

noncomputable def sphereCapCenterND {d : ℕ} (δ : ℝ) (a : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) :=
  ‖capGridPointND δ a‖⁻¹ • capGridPointND δ a

lemma sphereCapCenterND_norm {d : ℕ} {δ : ℝ} {a : Fin d → ℤ}
    (ha : a ∈ sphereCapGridND d δ) : ‖sphereCapCenterND δ a‖=1 := by
  classical
  have hn : 0 < ‖capGridPointND δ a‖ := lt_of_lt_of_le (by norm_num) (Finset.mem_filter.mp ha).2
  simp [sphereCapCenterND,norm_smul,inv_mul_cancel₀ hn.ne']

lemma sphereCapCenterND_dist {d : ℕ} {δ : ℝ} (hδ : 0<δ) {a : Fin d → ℤ}
    (ha : a ∈ sphereCapGridND d δ) {w : EuclideanSpace ℝ (Fin d)} (hw : ‖w‖=1)
    (hs : w ∈ tsupport (tensorCapND δ a)) : dist w (sphereCapCenterND δ a) ≤ 2*(d+1:ℝ)*δ := by
  classical
  have hn : 0 < ‖capGridPointND δ a‖ := lt_of_lt_of_le (by norm_num) (Finset.mem_filter.mp ha).2
  have hd := tensorCapND_tsupport_dist hδ a hs
  have ht : dist (capGridPointND δ a) (sphereCapCenterND δ a) = |‖capGridPointND δ a‖-1| := by
    rw [dist_eq_norm,sphereCapCenterND]
    have he : capGridPointND δ a - ‖capGridPointND δ a‖⁻¹ • capGridPointND δ a =
        (1-‖capGridPointND δ a‖⁻¹) • capGridPointND δ a := by rw [sub_smul,one_smul]
    rw [he]
    rw [norm_smul,Real.norm_eq_abs]
    have heq : |(1-‖capGridPointND δ a‖⁻¹)*‖capGridPointND δ a‖| =
        |1-‖capGridPointND δ a‖⁻¹| *‖capGridPointND δ a‖ := by rw [abs_mul,abs_of_pos hn]
    rw [← heq,sub_mul,one_mul,inv_mul_cancel₀ hn.ne']
  have hh : |‖capGridPointND δ a‖-1| ≤ dist w (capGridPointND δ a) := by
    rw [dist_comm,dist_eq_norm]
    simpa only [hw] using abs_norm_sub_norm_le (capGridPointND δ a) w
  calc
    _ ≤ dist w (capGridPointND δ a)+dist (capGridPointND δ a) (sphereCapCenterND δ a) := dist_triangle _ _ _
    _ ≤ 2*((d+1:ℝ)*δ) := by rw [ht]; linarith
    _ = _ := by ring

end CurrentFalconer
end
end

end OAI
