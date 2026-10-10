import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.FullSet

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma HasSecondTaylor.nonneg_of_localMin {f : E → ℝ}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasSecondTaylor f 0 B)
    (hm : IsLocalMin f 0) (v:E) : 0≤B v v := by
  by_contra hn
  have hB : B v v<0 := lt_of_not_ge hn
  have hv : v≠0 := by
    intro he; subst v; simp at hB
  have hnv : 0<‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  let ε := -(B v v)/(4*‖v‖^2)
  have hε : 0<ε := div_pos (neg_pos.mpr hB) (by positivity)
  have hεeq : ε*‖v‖^2 = -(B v v)/4 := by
    dsimp [ε]; field_simp
  obtain ⟨r,hr,H⟩ := Metric.eventually_nhds_iff.mp ((hf.eventually hε).and hm)
  let δ := r/(2*(‖v‖+1))
  have hδ : 0<δ := div_pos hr (by positivity)
  have hδeq : δ*(2*(‖v‖+1))=r := div_mul_cancel₀ _ (by positivity)
  have hmem : δ • v∈Metric.ball (0:E) r := by
    rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hδ]
    nlinarith [norm_nonneg v]
  obtain ⟨ht,hm'⟩ := H hmem
  have hbil : B (δ • v) (δ • v)=δ^2*B v v := by
    simp only [map_smul,smul_apply,smul_eq_mul]; ring
  have hnorm : ‖δ • v‖^2=δ^2*‖v‖^2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hδ,mul_pow]
  rw [hbil,hnorm] at ht
  simp only [zero_apply,sub_zero] at ht
  have hupper := (abs_le.mp ht).2
  have hmul : ε*(δ^2*‖v‖^2)=δ^2*(-(B v v)/4) := by
    calc
      _=δ^2*(ε*‖v‖^2) := by ring
      _=_ := by rw [hεeq]
  rw [hmul] at hupper
  have hneg := mul_neg_of_pos_of_neg (sq_pos_of_pos hδ) hB
  change f 0≤f (δ • v) at hm'
  nlinarith
end WeakMTWTransport

end

end OAI
