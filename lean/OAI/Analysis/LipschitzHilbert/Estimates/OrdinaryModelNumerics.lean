import OAI.Analysis.LipschitzHilbert.Packets.PacketDataModelConfig
import Mathlib.Algebra.Order.Archimedean.Basic

namespace OAI

/-! Fixed choices of the separation gaps in the ordinary packet model.
They depend only on the spectral and selector constants, never on the
number of scales, sites, carriers, or the input functions. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData

structure OrdinaryModelNumerics (cStar cEta cb radius : ℝ) where
  gap : ℕ
  packGap : ℕ
  K : ℕ
  hgap : (cStar/cEta)*(1+1/(2:ℝ)^(gap+1))+1/(2:ℝ)^(gap+1)≤cb/4
  hpack : (1+cb/4)/(2:ℝ)^packGap≤cb/4
  hK : radius+1≤(2:ℝ)^K

theorem exists_ordinary_model_numerics (cStar cEta cb radius : ℝ)
    (hcStar : 0≤cStar) (hcEta : 0<cEta) (hcb : 0<cb)
    (hsmall : cStar/cEta<cb/4) :
    Nonempty (OrdinaryModelNumerics cStar cEta cb radius) := by
  let a := cStar/cEta
  let delta := cb/4-a
  have ha : 0≤a := div_nonneg hcStar hcEta.le
  have hd : 0<delta := sub_pos.mpr hsmall
  obtain ⟨gap,hgap⟩ := pow_unbounded_of_one_lt ((a+1)/delta) (by norm_num : (1:ℝ)<2)
  obtain ⟨packGap,hpack⟩ := pow_unbounded_of_one_lt ((1+cb/4)/(cb/4))
    (by norm_num : (1:ℝ)<2)
  obtain ⟨K,hK⟩ := pow_unbounded_of_one_lt (radius+1) (by norm_num : (1:ℝ)<2)
  refine ⟨⟨gap,packGap,K,?_,?_,hK.le⟩⟩
  · have hp : 0<(2:ℝ)^gap := pow_pos (by norm_num) _
    have hp' : 0<(2:ℝ)^(gap+1) := pow_pos (by norm_num) _
    have hg : a+1<2^gap*delta := (div_lt_iff₀ hd).mp hgap
    have hg' : (a+1)/(2:ℝ)^(gap+1)≤delta := by
      apply (div_le_iff₀ hp').mpr
      rw [pow_succ]
      nlinarith
    have he : a*(1+1/(2:ℝ)^(gap+1))+1/(2:ℝ)^(gap+1) =
        a+(a+1)/(2:ℝ)^(gap+1) := by ring
    change a*(1+1/(2:ℝ)^(gap+1))+1/(2:ℝ)^(gap+1)≤cb/4
    rw [he]
    dsimp only [delta] at hg'
    linarith
  · have hp : 0<(2:ℝ)^packGap := pow_pos (by norm_num) _
    have hc : 0<cb/4 := by positivity
    exact (div_le_iff₀ hp).mpr (by
      have h := (div_lt_iff₀ hc).mp hpack
      nlinarith)

end LipschitzHilbert.PacketLatticeData

end

end OAI
