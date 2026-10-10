import OAI.MeasureTheory.Falconer.Geometry.TwoNormalProjection
import OAI.MeasureTheory.Falconer.Geometry.TripleGridRounding

namespace OAI

/-! # Covering a transverse rectangle by codimension-two neighborhoods -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem orthonormal_rectangle_cover {d : ℕ} (v : Fin 2 → Space d)
    (hv : Orthonormal ℝ v) (a b : ℝ) {r R : ℝ} (hr : 0 < r) (hR : r ≤ R) :
    ∃ V : Submodule ℝ (Space d), Module.finrank ℝ V = d-2 ∧
      ∃ S : Finset (Space d), (S.card:ℝ) ≤ 63*(R/r) ∧
        {x | |inner ℝ (v 0) x-a| ≤ r ∧ |inner ℝ (v 1) x-b| ≤ R} ⊆
          ⋃ p ∈ S, affineSubspaceNeighborhood V p r := by
  classical
  obtain ⟨V,hV,hproj⟩ := orthonormal_pair_complement v hv
  let L := Nat.ceil (R/(r/2)+1)
  let I := Finset.Icc (-3:ℤ) 3
  let J := Finset.Icc (-(L:ℤ)) (L:ℤ)
  let p : ℤ × ℤ → Space d := fun z =>
    (a+(r/2)*(z.1:ℝ)) • v 0 + (b+(r/2)*(z.2:ℝ)) • v 1
  let S := (I.product J).image p
  have hR0 : 0 ≤ R := hr.le.trans hR
  have hcard : (S.card:ℝ) ≤ 63*(R/r) := by
    have hI : I.card = 7 := by norm_num [I]
    have hJ : J.card = 2*L+1 := by dsimp [J]; rw [Int.card_Icc]; omega
    have hS : (S.card:ℝ) ≤ 7*(2*(L:ℝ)+1) := by
      have hh : S.card ≤ I.card*J.card :=
        (Finset.card_image_le (s := I.product J) (f := p)).trans_eq (Finset.card_product I J)
      rw [hI,hJ] at hh
      exact_mod_cast hh
    have hL : (L:ℝ) ≤ 2*(R/r)+2 := by
      calc
        (L:ℝ) ≤ R/(r/2)+1+1 := (Nat.ceil_lt_add_one (by positivity)).le
        _ = 2*(R/r)+2 := by field_simp; ring
    have hratio : 1 ≤ R/r := (le_div_iff₀ hr).mpr (by simpa using hR)
    nlinarith
  refine ⟨V,hV,S,hcard,?_⟩
  intro x hx
  let i := round ((inner ℝ (v 0) x-a)/(r/2))
  let j := round ((inner ℝ (v 1) x-b)/(r/2))
  have hi : i ∈ I := Finset.mem_Icc.mpr
    (round_bound (by positivity : 0 < r/2) 3
      (by rw [show r/(r/2) = 2 by field_simp]; norm_num) _ hx.1)
  have hj : j ∈ J := Finset.mem_Icc.mpr
    (round_bound (by positivity : 0 < r/2) L (Nat.le_ceil _) _ hx.2)
  refine mem_iUnion₂.mpr ⟨p (i,j),Finset.mem_image.mpr
    ⟨(i,j),Finset.mem_product.mpr ⟨hi,hj⟩,rfl⟩,?_⟩
  have hvij := orthonormal_iff_ite.mp hv
  have h0 : |inner ℝ (v 0) (x-p (i,j))| ≤ r/4 := by
    have he : inner ℝ (v 0) (x-p (i,j)) = inner ℝ (v 0) x-a-(r/2)*(i:ℝ) := by
      simp [p,inner_sub_right,inner_add_right,inner_smul_right,hvij,hv.norm_eq_one]
      ring
    rw [he]
    convert round_mesh_error (by positivity : 0 < r/2) (inner ℝ (v 0) x-a) using 1; ring
  have h1 : |inner ℝ (v 1) (x-p (i,j))| ≤ r/4 := by
    have he : inner ℝ (v 1) (x-p (i,j)) = inner ℝ (v 1) x-b-(r/2)*(j:ℝ) := by
      simp [p,inner_sub_right,inner_add_right,inner_smul_right,hvij,hv.norm_eq_one]
      ring
    rw [he]
    convert round_mesh_error (by positivity : 0 < r/2) (inner ℝ (v 1) x-b) using 1; ring
  change ‖Vᗮ.starProjection (x-p (i,j))‖ ≤ r
  exact (hproj _).trans (by linarith)

theorem orthonormal_rectangle_mass {d : ℕ} (μ : Measure (Space d))
    (v : Fin 2 → Space d) (hv : Orthonormal ℝ v) (a b : ℝ) {r R C α : ℝ}
    (hr : 0 < r) (hR : r ≤ R) (hC : 0 ≤ C)
    (hplane : ∀ V : Submodule ℝ (Space d), Module.finrank ℝ V = d-2 →
      ∀ p, μ (affineSubspaceNeighborhood V p r) ≤ ENNReal.ofReal (C*r^α)) :
    μ {x | |inner ℝ (v 0) x-a| ≤ r ∧ |inner ℝ (v 1) x-b| ≤ R} ≤
      ENNReal.ofReal (63*(R/r)*(C*r^α)) := by
  obtain ⟨V,hV,S,hcard,hcover⟩ := orthonormal_rectangle_cover v hv a b hr hR
  apply (measure_mono hcover).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc
    _ ≤ ∑ _p ∈ S, ENNReal.ofReal (C*r^α) := Finset.sum_le_sum fun p _ => hplane V hV p
    _ = ENNReal.ofReal ((S.card:ℝ)*(C*r^α)) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hcard (mul_nonneg hC (Real.rpow_nonneg hr.le _)))

end Falconer

end OAI
