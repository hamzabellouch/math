import Mathlib
import OAI.Analysis.CoulombIonization.Localization.GridPacketRadius

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
namespace CoulombAtom

lemma exists_nat_cube_between {M : ℝ} (hM : 1 ≤ M) :
    ∃ n : ℕ, 0 < n ∧ M ≤ (n:ℝ)^3 ∧ (n:ℝ)^3 ≤ 8*M := by
  have hex : ∃ n : ℕ, M ≤ (n:ℝ)^3 := by
    obtain ⟨n,hn⟩ := exists_nat_gt M
    have hn1 : (1:ℝ) ≤ n := le_trans hM hn.le
    have hn0 : (0:ℝ) ≤ n := by positivity
    have hpow : (n:ℝ) ≤ (n:ℝ)^3 := by
      nlinarith [mul_nonneg (sq_nonneg (n:ℝ)) (sub_nonneg.mpr hn1)]
    exact ⟨n,le_trans hn.le hpow⟩
  let n := Nat.find hex
  have hl : M ≤ (n:ℝ)^3 := Nat.find_spec hex
  have hn : 0 < n := by
    by_contra hh
    have he : n = 0 := by omega
    rw [he] at hl
    norm_num at hl
    linarith
  refine ⟨n,hn,hl,?_⟩
  by_cases he : n = 1
  · rw [he]; norm_num; linarith
  have hn2 : 2 ≤ n := by omega
  have hp : ((n-1:ℕ):ℝ)^3 < M := lt_of_not_ge (Nat.find_min hex (by dsimp [n]; omega))
  have hb : (n:ℝ) ≤ 2*((n-1:ℕ):ℝ) := by exact_mod_cast (show n ≤ 2*(n-1) by omega)
  have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ n) hb 3
  nlinarith

lemma packet_kinetic_absorb {B x : ℝ} (hB : 0 < B) (hx : 0 ≤ x) :
    x^2/B^2 ≤ 1/B^4+x^3/B := by
  have hu : 0 ≤ x*B := mul_nonneg hx hB.le
  have hcube : (x*B)^2 ≤ 1+(x*B)^3 := by
    by_cases hh : x*B ≤ 1
    · have hc : 0 ≤ (x*B)^3 := pow_nonneg hu _
      nlinarith [mul_nonneg hu (sub_nonneg.mpr hh)]
    · have hh : 1 ≤ x*B := (not_le.mp hh).le
      nlinarith [mul_nonneg (sq_nonneg (x*B)) (sub_nonneg.mpr hh)]
  apply (div_le_iff₀ (pow_pos hB 2)).mpr
  have he : (1/B^4+x^3/B)*B^2 = (1+(x*B)^3)/B^2 := by field_simp
  rw [he]
  apply (le_div_iff₀ (pow_pos hB 2)).mpr
  nlinarith

def packetFieldConstant : ℝ := 1+9*packetKineticConstant+8*packetRepulsionConstant

lemma packetFieldConstant_pos : 0 < packetFieldConstant := by
  dsimp [packetFieldConstant]
  have := packetKineticConstant_nonneg
  have := packetRepulsionConstant_nonneg
  linarith

lemma field_cap_of_grid_bounds {B δ A C F : ℝ} (hB : 0 < B) (hδ : 0 ≤ δ)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, 0 < n → (n:ℝ)^3*F ≤ δ+A*(n:ℝ)^5/B^2+C*(n:ℝ)^6/B) :
    F ≤ (1+9*A+8*C)*(1/B^4+1/B+Real.sqrt (δ/B)) := by
  let s := Real.sqrt (δ/B)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : δ = B*s^2 := by
    have hh := Real.sq_sqrt (div_nonneg hδ hB.le)
    dsimp only [s]
    exact (eq_div_iff hB.ne').mp hh |>.symm.trans (mul_comm _ _)
  obtain ⟨n,hn,hlo,hhi⟩ := exists_nat_cube_between (le_max_left 1 (B*s))
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have ht : 0 < (n:ℝ)^3 := pow_pos hn' _
  have hlo' : B*s ≤ (n:ℝ)^3 := le_trans (le_max_right _ _) hlo
  have hhi' : (n:ℝ)^3 ≤ 8*(1+B*s) := by
    have hb : max 1 (B*s) ≤ 1+B*s := max_le (by linarith [mul_nonneg hB.le hs]) (by linarith)
    linarith
  have hdiv : δ/(n:ℝ)^3 ≤ s := by
    apply (div_le_iff₀ ht).mpr
    rw [hs2]
    nlinarith [mul_le_mul_of_nonneg_right hlo' hs]
  have hkin := packet_kinetic_absorb hB hn'.le
  have hrep : (n:ℝ)^3/B ≤ 8/B+8*s := by
    apply (div_le_iff₀ hB).mpr
    have he : (8/B+8*s)*B = 8*(1+B*s) := by field_simp
    rw [he]
    exact hhi'
  have hbasic : F ≤ δ/(n:ℝ)^3+A*((n:ℝ)^2/B^2)+C*((n:ℝ)^3/B) := by
    calc
      F = ((n:ℝ)^3*F)/(n:ℝ)^3 := by field_simp
      _ ≤ (δ+A*(n:ℝ)^5/B^2+C*(n:ℝ)^6/B)/(n:ℝ)^3 :=
        div_le_div_of_nonneg_right (h n hn) ht.le
      _ = _ := by field_simp
  have hstep : F ≤ A*(1/B^4)+(1+8*(A+C))*s+8*(A+C)*(1/B) := by
    have hk := mul_le_mul_of_nonneg_left hkin hA
    have hr := mul_le_mul_of_nonneg_left hrep (add_nonneg hA hC)
    simp only [div_eq_mul_inv] at hbasic hk hr hdiv ⊢
    nlinarith only [hbasic,hk,hr,hdiv]
  have hb4 : 0 ≤ 1/B^4 := by positivity
  have hb1 : 0 ≤ 1/B := by positivity
  have h1 : A ≤ 1+9*A+8*C := by linarith
  have h2 : 1+8*(A+C) ≤ 1+9*A+8*C := by linarith
  have h3 : 8*(A+C) ≤ 1+9*A+8*C := by linarith
  nlinarith [mul_le_mul_of_nonneg_right h1 hb4,mul_le_mul_of_nonneg_right h2 hs,
    mul_le_mul_of_nonneg_right h3 hb1]

end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

end

end OAI
