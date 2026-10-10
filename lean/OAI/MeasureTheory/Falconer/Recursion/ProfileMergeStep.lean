import OAI.MeasureTheory.Falconer.Estimates.DyadicSecantError
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact

namespace OAI

/-! The low-slope absorption step in the profile decomposition. The new
interval has exactly the prescribed slope and retains the lower chord bound. -/
namespace Falconer
open Set

theorem exists_superlinear_merge_left {f : ℝ → ℝ} (hf : Continuous f)
    {a c b s ε : ℝ} (hac : a < c) (hcb : c < b) (hε : 0 ≤ ε)
    (hab : s*(b-a) < f b-f a)
    (hk : intervalSecantSlope f c (b-c) < s)
    (herr : ∀ x ∈ Icc c b, -ε*(b-c) ≤ intervalSecantError f c (b-c) x) :
    ∃ u ∈ Ioo a c, f b-f u = s*(b-u) ∧
      ∀ x ∈ Icc u b, f u+s*(x-u)-ε*(b-u) ≤ f x := by
  let k := intervalSecantSlope f c (b-c)
  have hbc : b-c ≠ 0 := sub_ne_zero.mpr hcb.ne'
  have hkb : f b-f c = k*(b-c) := by
    dsimp [k,intervalSecantSlope]
    rw [show c+(b-c) = b by ring,div_mul_cancel₀ _ hbc]
  let g : ℝ → ℝ := fun x => f x-s*x-(f b-s*b)
  have hg : Continuous g := (hf.sub (continuous_const.mul continuous_id)).sub continuous_const
  have hga : g a < 0 := by dsimp [g]; nlinarith
  have hgc : 0 < g c := by
    have hm := mul_lt_mul_of_pos_right hk (sub_pos.mpr hcb)
    dsimp [g]
    change k*(b-c) < s*(b-c) at hm
    nlinarith [hkb]
  let Z := Icc a c ∩ {x | g x = 0}
  have hZ : IsCompact Z := isCompact_Icc.inter_right (isClosed_eq hg continuous_const)
  have hZne : Z.Nonempty := by
    obtain ⟨u,hu,hgu⟩ := intermediate_value_Icc hac.le hg.continuousOn ⟨hga.le,hgc.le⟩
    exact ⟨u,hu,hgu⟩
  obtain ⟨u,hu,hmax⟩ := hZ.exists_isGreatest hZne
  have hgu : g u = 0 := hu.2
  have hua : a < u := lt_of_le_of_ne hu.1.1 (by
    intro he
    have hz := hgu
    rw [← he] at hz
    linarith)
  have huc : u < c := lt_of_le_of_ne hu.1.2 (by
    intro he
    have hz := hgu
    rw [he] at hz
    linarith)
  have hleft : ∀ x ∈ Icc u c, 0 ≤ g x := by
    intro x hx
    by_contra hn
    have hneg : g x < 0 := lt_of_not_ge hn
    have hux : u < x := lt_of_le_of_ne hx.1 (by
      intro he
      rw [← he,hgu] at hneg
      linarith)
    obtain ⟨v,hv,hgv⟩ := intermediate_value_Icc hx.2 hg.continuousOn ⟨hneg.le,hgc.le⟩
    have hvZ : v ∈ Z := ⟨⟨hu.1.1.trans (hx.1.trans hv.1),hv.2⟩,hgv⟩
    have hle := hmax hvZ
    linarith [hv.1]
  refine ⟨u,⟨hua,huc⟩,?_,?_⟩
  · have hz := hgu
    dsimp [g] at hz
    linarith
  · intro x hx
    have hz := hgu
    dsimp [g] at hz
    by_cases hxc : x ≤ c
    · have hgx := hleft x ⟨hx.1,hxc⟩
      dsimp [g] at hgx
      have heps := mul_nonneg hε (sub_nonneg.mpr (hx.1.trans hx.2))
      nlinarith
    · have hx' : x ∈ Icc c b := ⟨le_of_not_ge hxc,hx.2⟩
      have he := herr x hx'
      change -ε*(b-c) ≤ f x-f c-k*(x-c) at he
      have hslope := mul_le_mul_of_nonneg_right hk.le (sub_nonneg.mpr hx.2)
      change k*(b-x) ≤ s*(b-x) at hslope
      have herrscale := mul_le_mul_of_nonneg_left (sub_le_sub_left huc.le b) hε
      nlinarith [hkb]

end Falconer

end OAI
