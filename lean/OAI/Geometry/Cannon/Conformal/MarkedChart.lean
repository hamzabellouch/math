import Mathlib
import OAI.Geometry.Cannon.Modulus.BoundaryNormalizedAnnularCarriers
import OAI.Geometry.Cannon.Conformal.Chart

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
namespace CannonMobius
open Set Metric Topology
open scoped OnePoint

def markedChart (i : Fin 3) : Sphere ≃ₜ Sphere:=![1,chartZero,chartOne] i
lemma markedChart_biholomorphic (i : Fin 3) : markedChart i∈biholomorphic := by
  fin_cases i
  · exact biholomorphic.one_mem
  · exact biholomorphic.mul_mem (affine_biholomorphic _ _ _) inversion_biholomorphic
  · exact biholomorphic.mul_mem
      (biholomorphic.mul_mem (affine_biholomorphic _ _ _) inversion_biholomorphic)
      (affine_biholomorphic _ _ _)
lemma markedChart_isometry (i : Fin 3) : Isometry (markedChart i) := by
  fin_cases i
  · exact isometry_id
  · exact chartZero_isometry
  · exact chartOne_isometry
lemma markedChart_pole (i : Fin 3) : markedChart i (std i)=∞ := by
  fin_cases i
  · rfl
  · change affine 4 0 _ (inv ((0:ℂ):Sphere))=∞
    rw [inv_zero,affine_infty]
  · change affine 5 (-1) _ (inv (affine (-1) 1 _ ((1:ℂ):Sphere)))=∞
    rw [affine_coe]
    norm_num
lemma markedChart_other (i j : Fin 3) (hij : i≠j) :
    ∃ z : ℂ,markedChart i (std j)=(z:Sphere) ∧ ‖z‖≤4 := by
  fin_cases i <;> fin_cases j <;> try contradiction
  · exact ⟨0,rfl,by norm_num⟩
  · exact ⟨1,rfl,by norm_num⟩
  · refine ⟨0,?_,by norm_num⟩
    change affine 4 0 _ (inv ∞)=_
    rw [inv_infty,affine_coe]
    norm_num
  · exact ⟨4,by simpa [markedChart,std] using chartZero_finite (z:=1) (by norm_num),by norm_num⟩
  · refine ⟨-1,?_,by norm_num⟩
    change affine 5 (-1) _ (inv (affine (-1) 1 (by norm_num) ∞))=_
    rw [affine_infty,inv_infty,affine_coe]
    norm_num
  · exact ⟨4,by simpa [markedChart,std] using chartOne_finite (z:=0) (by norm_num),by norm_num⟩

lemma coordinate_bound_away_pole {δ : ℝ} (hδ : 0<δ) :
    ∃ B : ℝ,1≤B ∧ ∀ z : ℂ,δ≤dist (z:Sphere) ∞ → ‖z‖≤B := by
  let K : Set Sphere:={p | δ≤dist p ∞}
  have hK : IsClosed K:=isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hinfinity : ∞∉K := by simpa [K] using hδ
  have hc:=CannonTileTopology.compact_trace hK hinfinity
  obtain ⟨B,hB⟩:=hc.isBounded.subset_closedBall 0
  refine ⟨max 1 B,le_max_left _ _,?_⟩
  intro z hz
  have hh:=hB hz
  rw [mem_closedBall,dist_zero_right] at hh
  exact hh.trans (le_max_right _ _)

lemma coordinate_comparison {B : ℝ} (_hB : 0≤B) {z w : ℂ}
    (hz : ‖z‖≤B) (hw : ‖w‖≤B) :
    dist z w≤(B^2+4)*dist (z:Sphere) (w:Sphere) := by
  have he:=coe_dist_sq z w
  have hd : 0<(‖z‖^2+4)*(‖w‖^2+4):=by positivity
  have hz2:=pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hw2:=pow_le_pow_left₀ (norm_nonneg w) hw 2
  have hden : (‖z‖^2+4)*(‖w‖^2+4)≤(B^2+4)^2 := by
    calc
      _ ≤ (B^2+4)*(B^2+4):=mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      _ = _:=by ring
  have hs : dist z w^2 ≤ ((B^2+4)*dist (z:Sphere) (w:Sphere))^2 := by
    have hh:=(div_eq_iff hd.ne').mp he.symm
    have hm:=mul_le_mul_of_nonneg_left hden (sq_nonneg (dist (z:Sphere) (w:Sphere)))
    nlinarith [sq_nonneg (dist z w)]
  have hn : 0≤(B^2+4)*dist (z:Sphere) (w:Sphere):=by positivity
  nlinarith [dist_nonneg (x:=z) (y:=w)]
end CannonMobius

end
end
end
end

end OAI
