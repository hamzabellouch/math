import Mathlib

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I X : Type*} [DecidableEq I]

theorem far_exchange (Fj Fs : Finset I) (y d : I → ℝ) {R D α : ℝ}
    (hy : ∀ i, 0 ≤ y i) (hd : ∀ i, 0 ≤ d i)
    (hmj : ∑ i ∈ Fj, y i=1) (hms : ∑ i ∈ Fs, y i=1)
    (hα : 0 ≤ α) (hα1 : α < 1) (hD : D ≤ α*R)
    (hupper : ∀ i ∈ Fs \ Fj, d i ≤ R+D)
    (hlower : ∀ i ∈ Fj \ Fs, R-D ≤ d i) :
    (∑ i ∈ Fs, y i*d i) ≤ (1+α)/(1-α)*(∑ i ∈ Fj, y i*d i) := by
  let κ := (1+α)/(1-α)
  have hden : 0 < 1-α := sub_pos.mpr hα1
  have hκ : 1 ≤ κ := (le_div_iff₀ hden).mpr (by linarith only [hα])
  have hκ0 : 0 ≤ κ := le_trans (by norm_num) hκ
  have hκid : κ*(1-α)=1+α := div_mul_cancel₀ _ hden.ne'
  have hr : R+D ≤ κ*(R-D) := by
    apply (mul_le_mul_iff_of_pos_left hden).mp
    calc
      (1-α)*(R+D) ≤ (1+α)*(R-D) := by nlinarith only [hD]
      _ = (1-α)*(κ*(R-D)) := by rw [← mul_assoc,mul_comm (1-α),hκid]
  let c := ∑ i ∈ Fs ∩ Fj, y i*d i
  let m := ∑ i ∈ Fs \ Fj, y i
  have hm0 : 0 ≤ m := sum_nonneg (fun i _ => hy i)
  have hc0 : 0 ≤ c := sum_nonneg (fun i _ => mul_nonneg (hy i) (hd i))
  have hm : (∑ i ∈ Fj \ Fs, y i)=m := by
    have h1 := sum_inter_add_sum_sdiff Fs Fj y
    have h2 := sum_inter_add_sum_sdiff Fj Fs y
    rw [hms] at h1
    rw [hmj,inter_comm Fj Fs] at h2
    dsimp only [m]
    linarith only [h1,h2]
  have hup : (∑ i ∈ Fs, y i*d i) ≤ c+(R+D)*m := by
    rw [← sum_inter_add_sum_sdiff Fs Fj (fun i => y i*d i)]
    apply add_le_add le_rfl
    dsimp only [m]
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    exact (mul_le_mul_of_nonneg_left (hupper i hi) (hy i)).trans_eq (mul_comm _ _)
  have hlo : c+(R-D)*m ≤ ∑ i ∈ Fj, y i*d i := by
    rw [← sum_inter_add_sum_sdiff Fj Fs (fun i => y i*d i),inter_comm Fj Fs,← hm]
    apply add_le_add le_rfl
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    exact (mul_comm (R-D) (y i)).le.trans (mul_le_mul_of_nonneg_left (hlower i hi) (hy i))
  calc
    _ ≤ c+(R+D)*m := hup
    _ ≤ κ*c+κ*((R-D)*m) := add_le_add (le_mul_of_one_le_left hc0 hκ)
      ((mul_le_mul_of_nonneg_right hr hm0).trans_eq (by ring))
    _ = κ*(c+(R-D)*m) := by ring
    _ ≤ κ*(∑ i ∈ Fj, y i*d i) := mul_le_mul_of_nonneg_left hlo hκ0

omit [DecidableEq I] in
 theorem bundle_relocation [PseudoMetricSpace X] (j s t i u : X) {β δ Ls Lt : ℝ}
    (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hsep : β+δ < 1)
    (hD : dist j s ≤ β*Ls) (hLs : Ls ≤ dist s t) (hLt : Lt ≤ dist s t)
    (hi : dist t i ≤ δ*Lt) (hu : dist t u ≤ δ*Lt) :
    dist j u ≤ (1+2*δ/(1-β-δ))*dist j i := by
  have hden : 0 < 1-β-δ := by linarith only [hsep]
  have hDj : dist j s ≤ β*dist s t := hD.trans (mul_le_mul_of_nonneg_left hLs hβ)
  have hdi : dist t i ≤ δ*dist s t := hi.trans (mul_le_mul_of_nonneg_left hLt hδ)
  have hdu : dist t u ≤ δ*dist s t := hu.trans (mul_le_mul_of_nonneg_left hLt hδ)
  have htri := dist_triangle s j t
  have htri' := dist_triangle j i t
  rw [dist_comm s j] at htri
  rw [dist_comm i t] at htri'
  have hbase : (1-β-δ)*dist s t ≤ dist j i := by linarith only [htri,htri',hDj,hdi]
  have hdst : dist s t ≤ dist j i/(1-β-δ) := (le_div_iff₀ hden).mpr (by nlinarith only [hbase])
  have hnew := dist_triangle j i u
  have hnew' := dist_triangle i t u
  rw [dist_comm i t] at hnew'
  have hh := mul_le_mul_of_nonneg_left hdst (show 0 ≤ 2*δ by positivity)
  calc
    dist j u ≤ dist j i+2*δ*dist s t := by linarith only [hnew,hnew',hdi,hdu]
    _ ≤ dist j i+2*δ*(dist j i/(1-β-δ)) := add_le_add le_rfl hh
    _ = _ := by ring

omit [DecidableEq I] in
 theorem extra_star_charge {β δ γ L c V : ℝ} (hβ : 0 ≤ β) (hδ : 0 < δ)
    (hγ : 0 ≤ γ) (hcharge : δ*L*c ≤ V) :
    (β+1+δ)*γ*c*L ≤ ((β+1+δ)*γ/δ)*V := by
  have hc := mul_le_mul_of_nonneg_left hcharge
    (show 0 ≤ (β+1+δ)*γ/δ by positivity)
  have he : (β+1+δ)*γ/δ*(δ*L*c)=(β+1+δ)*γ*c*L := by field_simp
  rw [he] at hc
  exact hc

end MetricKMedian.Preparation
end
end

end OAI
