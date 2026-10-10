import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarInstability
import OAI.Probability.SKBarriers.SpinGlass.FiniteScalarGap

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem finiteParisiInf_temperature_upper {β γ δ : ℝ} (hβ : 0 < β) (hβγ : β ≤ γ)
    (hδ : 0 < δ) (hgap : finiteParisiInf β ≤ Real.log 2+β^2/4-2*δ) :
    finiteParisiInf γ ≤ finiteParisiInf β+
      (γ^2-β^2)/4*(1-(β^2/γ^2)*(2*δ/β^2)^2) := by
  have hγ : 0 < γ := hβ.trans_le hβγ
  have hK : 0 ≤ (γ^2-β^2)/4 := by nlinarith
  apply le_of_forall_pos_le_add
  intro ε hε
  have hsmall : 0 < min ε δ := lt_min hε hδ
  obtain ⟨p,hp,hpLt⟩ := exists_lt_of_csInf_lt (finiteParisiValues_nonempty β)
    (show finiteParisiInf β < finiteParisiInf β+min ε δ by linarith)
  obtain ⟨k,Q,hm,hQ,rfl⟩ := hp
  have hg : extendedQuantileParisi k β Q ≤ Real.log 2+β^2/4-δ := by
    linarith [min_le_right ε δ]
  have hS := quantileSecondMoment_of_gap hβ hδ.le Q hm hQ hg
  obtain ⟨hm',hQ'⟩ := rescaledQuantiles_admissible hβ hβγ Q hm hQ
  have HT := finiteParisiInf_le γ ((β/γ)^2 • Q) hm' hQ'
  rw [extendedQuantileParisi_temperature_rescale hβ hγ Q] at HT
  have HP : (γ^2-β^2)/4*(1-(β^2/γ^2)*quantileSecondMoment k Q) ≤
      (γ^2-β^2)/4*(1-(β^2/γ^2)*(2*δ/β^2)^2) := by
    apply mul_le_mul_of_nonneg_left _ hK
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left hS (by positivity)) 1
  linarith [min_le_left ε δ]

theorem exists_strict_finiteParisiInf_secant {β : ℝ} (hβ : 1 < β) :
    ∃ γ : ℝ, β < γ ∧ (finiteParisiInf γ-finiteParisiInf β)/(γ-β) < β/2 := by
  have hβpos : 0 < β := lt_trans zero_lt_one hβ
  let δ := (Real.log 2+β^2/4-finiteParisiInf β)/2
  have hδ : 0 < δ := by dsimp only [δ]; linarith [finiteParisiInf_lt_annealed hβ]
  let c := (2*δ/β^2)^2
  have hc : 0 < c := sq_pos_of_pos (div_pos (mul_pos (by norm_num) hδ) (sq_pos_of_pos hβpos))
  let S := fun γ : ℝ => (γ+β)/4*(1-(β^2/γ^2)*c)
  have HS : ContinuousAt S β := by
    dsimp only [S]
    fun_prop (disch := positivity)
  have hS : S β < β/2 := by
    dsimp only [S]
    rw [div_self (sq_pos_of_pos hβpos).ne',one_mul]
    nlinarith [mul_pos hβpos hc]
  have HE : ∀ᶠ γ in 𝓝[>] β, S γ < β/2 :=
    (HS.tendsto.eventually (eventually_lt_nhds hS)).filter_mono nhdsWithin_le_nhds
  have HM : ∀ᶠ γ in 𝓝[>] β, β < γ := self_mem_nhdsWithin
  obtain ⟨γ,hγβ,hγS⟩ := (HM.and HE).exists
  have hβγ : β < γ := hγβ
  have HU := finiteParisiInf_temperature_upper hβpos hβγ.le hδ
    (show finiteParisiInf β ≤ Real.log 2+β^2/4-2*δ by dsimp only [δ]; linarith)
  have hd : 0 < γ-β := sub_pos.mpr hβγ
  have he : ((γ^2-β^2)/4*(1-(β^2/γ^2)*c))/(γ-β) = S γ := by
    dsimp only [S]
    field_simp [hd.ne', (hβpos.trans hβγ).ne']
    ring
  refine ⟨γ,hβγ,lt_of_le_of_lt ?_ hγS⟩
  rw [← he]
  exact div_le_div_of_nonneg_right (by dsimp only [c]; linarith [HU]) hd.le
end SK.Analytic

end
end

end

end OAI
