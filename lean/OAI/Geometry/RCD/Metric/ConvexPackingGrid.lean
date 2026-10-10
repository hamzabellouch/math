import OAI.Geometry.RCD.Sobolev.ConvexSubprobability
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.LinearIndependent.Defs

namespace OAI

/-! # Separated finite grids inside the convex hull of independent points -/

open Set Metric
open scoped BigOperators
noncomputable section
namespace RegularPointCoordinates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def convexGridPoint {m N : ℕ} (v : Fin m → E) (j : Fin m → Fin N) : E :=
  ∑ i, (((j i).val:ℝ)/((N:ℝ)*m)) • v i

theorem convexGridPoint_mem {K : Set E} (hK : Convex ℝ K) (h0 : 0 ∈ K)
    {m N : ℕ} (hm : 0 < m) (hN : 0 < N) (v : Fin m → E) (hv : ∀ i, v i ∈ K)
    (j : Fin m → Fin N) : convexGridPoint v j ∈ K := by
  apply convex_subprobability_sum_mem hK h0 v hv _ (fun _ => by positivity)
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hm
  have hNR : 0 < (N:ℝ) := by exact_mod_cast hN
  calc
    (∑ i : Fin m, ((j i).val:ℝ)/((N:ℝ)*m)) ≤ ∑ _i : Fin m, 1/(m:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply (div_le_iff₀ (mul_pos hNR hmR)).mpr
      have hi : ((j i).val:ℝ) ≤ N := by exact_mod_cast (j i).isLt.le
      convert hi using 1
      field_simp
    _ = 1 := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; field_simp

theorem convexGridPoint_separated {m : ℕ} (hm : 0 < m) (v : Fin m → E)
    (hlin : LinearIndependent ℝ v) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ i j : Fin m → Fin N, i ≠ j →
      1/(C*N*m) ≤ dist (convexGridPoint v i) (convexGridPoint v j) := by
  let L := Fintype.linearCombination ℝ v
  obtain ⟨C,hC,hanti⟩ := L.injective_iff_antilipschitz.mp hlin.fintypeLinearCombination_injective
  refine ⟨C,hC,?_⟩
  intro N hN i j hij
  obtain ⟨k,hk⟩ := Function.ne_iff.mp hij
  have hkn : (i k).val ≠ (j k).val := fun h => hk (Fin.ext h)
  let u : Fin m → ℝ := fun k => ((i k).val:ℝ)/((N:ℝ)*m)
  let w : Fin m → ℝ := fun k => ((j k).val:ℝ)/((N:ℝ)*m)
  have hden : 0 < (N:ℝ)*m := mul_pos (by exact_mod_cast hN) (by exact_mod_cast hm)
  have hgap : 1/((N:ℝ)*m) ≤ |u k-w k| := by
    dsimp only [u,w]
    rw [← sub_div,abs_div,abs_of_pos hden]
    apply div_le_div_of_nonneg_right _ hden.le
    rcases lt_or_gt_of_ne hkn with hlt | hgt
    · have hh : ((i k).val:ℝ)+1 ≤ (j k).val := by exact_mod_cast hlt
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hh : ((j k).val:ℝ)+1 ≤ (i k).val := by exact_mod_cast hgt
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hcoord : |u k-w k| ≤ dist u w := by
    simpa only [dist_eq_norm,Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (u-w) k
  have hbound := hanti.le_mul_dist u w
  change dist u w ≤ (C:ℝ)*dist (convexGridPoint v i) (convexGridPoint v j) at hbound
  have hquot := (div_le_iff₀ (show (0:ℝ)<C from hC)).mpr (by nlinarith [(hgap.trans hcoord).trans hbound] :
    1/((N:ℝ)*m) ≤ dist (convexGridPoint v i) (convexGridPoint v j)*(C:ℝ))
  convert hquot using 1
  field_simp

end RegularPointCoordinates

end

end OAI
