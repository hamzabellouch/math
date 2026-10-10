import Mathlib
import OAI.Analysis.AffineBernstein.CompletePositiveCap

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Metric

lemma affineEpigraph_vertical_ray {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    {o : Space n × ℝ} (ho : o ∈ (fun z => L z+v) '' sourceEpigraph Ω u)
    {t : ℝ} (ht : 0 ≤ t) : o+t • L ((0 : Space n),1) ∈
      (fun z => L z+v) '' sourceEpigraph Ω u := by
  obtain ⟨z,hz,rfl⟩ := ho
  refine ⟨z+t • ((0 : Space n),1),sourceEpigraph_vertical_ray hz ht,?_⟩
  dsimp only
  rw [map_add,map_smul]
  abel

lemma affineEpigraph_positive_vertical {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    {b R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hcap : ∀ z ∈ (fun z => L z+v) '' sourceEpigraph Ω u, z.2 ≤ b → ‖z‖ ≤ R)
    {o : Space n × ℝ} (ho : o ∈ (fun z => L z+v) '' sourceEpigraph Ω u)
    (hgap : o.2 ≤ b-ε) :
    0 < (L (0,1)).2 ∧ ‖((L (0,1)).2)⁻¹ • (L (0,1)).1‖ ≤ (2*R+1)/ε := by
  let q : Space n × ℝ := L (0,1)
  have hq : q ≠ 0 := by
    intro hz
    have h : ((0 : Space n),(1:ℝ)) = 0 := L.injective (hz.trans (map_zero L).symm)
    have := congrArg Prod.snd h
    norm_num at this
  have hn : 0 < ‖q‖ := norm_pos_iff.mpr hq
  let e : Space n × ℝ := ‖q‖⁻¹ • q
  have he : ‖e‖ = 1 := by
    simp only [e, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hrec (t : ℝ) (ht : 0 ≤ t) : o+t • e ∈
      (fun z => L z+v) '' sourceEpigraph Ω u := by
    simpa only [e,smul_smul] using affineEpigraph_vertical_ray L v ho
      (mul_nonneg ht (inv_nonneg.mpr hn.le))
  obtain ⟨hepos,_,hebound⟩ := cap_normalized_vertical_bound
    (ContinuousLinearMap.snd ℝ (Space n) ℝ) hR hε hcap ho hgap he hrec
  change 0 < e.2 at hepos
  have hqp : 0 < q.2 := by
    have heq : e.2 = ‖q‖⁻¹*q.2 := rfl
    rw [heq] at hepos
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp hepos
  have hnorm := (norm_fst_le (e.2⁻¹ • e)).trans hebound
  have heq : (e.2⁻¹ • e).1 = q.2⁻¹ • q.1 := by
    simp only [e,Prod.smul_snd,Prod.smul_fst,smul_eq_mul,mul_inv_rev,inv_inv,smul_smul]
    congr 1
    field_simp [hn.ne']
  rw [heq] at hnorm
  exact ⟨hqp,hnorm⟩

lemma norm_verticalShear_le {n : ℕ} (p : Space n) (z : Space n × ℝ) :
    ‖verticalShear p z‖ ≤ (1+‖p‖)*‖z‖ := by
  rw [verticalShear_apply,Prod.norm_def]
  apply max_le
  · calc
      _ ≤ ‖z.1‖+‖z.2 • p‖ := norm_sub_le _ _
      _ ≤ ‖z‖+‖z‖*‖p‖ := add_le_add (norm_fst_le z)
        (by rw [norm_smul]; exact mul_le_mul_of_nonneg_right (norm_snd_le z) (norm_nonneg p))
      _ = _ := by ring
  · calc
      ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
      _ ≤ (1+‖p‖)*‖z‖ := by nlinarith [norm_nonneg p,norm_nonneg z]

lemma shear_image_cap {n : ℕ} (p : Space n) (D : Set (Space n × ℝ)) (b : ℝ) :
    {z | z ∈ verticalShear p '' D ∧ z.2 ≤ b} =
      verticalShear p '' {z | z ∈ D ∧ z.2 ≤ b} := by
  ext z
  constructor
  · rintro ⟨⟨y,hy,rfl⟩,hb⟩
    exact ⟨y,⟨hy,hb⟩,rfl⟩
  · rintro ⟨y,⟨hy,hb⟩,rfl⟩
    exact ⟨⟨y,hy,rfl⟩,hb⟩

lemma shear_horizontal_ball {n : ℕ} (p : Space n) {D : Set (Space n × ℝ)}
    {o : Space n × ℝ} {r : ℝ} (hball : Metric.ball o r ⊆ D) :
    ∀ x ∈ Metric.ball (verticalShear p o).1 r,
      (x,o.2) ∈ verticalShear p '' D := by
  intro x hx
  let y : Space n × ℝ := (x+o.2 • p,o.2)
  have hy : dist y o = dist x (verticalShear p o).1 := by
    rw [Prod.dist_eq]
    simp only [y,verticalShear_apply,dist_self]
    rw [max_eq_left dist_nonneg,dist_eq_norm,dist_eq_norm]
    congr 1
    abel
  refine ⟨y,hball (by rwa [mem_ball,hy]),?_⟩
  simp [y]

lemma affine_image_after_shear {n : ℕ} (p : Space n)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ) (D : Set (Space n × ℝ)) :
    (fun z => (L.trans (verticalShear p)) z+verticalShear p v) '' D =
      verticalShear p '' ((fun z => L z+v) '' D) := by
  rw [Set.image_image]
  congr 1
  funext z
  exact (map_add (verticalShear p) (L z) v).symm

end AffineBernstein

end

end OAI
