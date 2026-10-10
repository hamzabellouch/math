import OAI.MeasureTheory.Falconer.Recursion.ProfileMergeStep

namespace OAI

/-! The global profile lower bound supplies every noninitial merge. -/
namespace Falconer
open Set

theorem exists_superlinear_merge_above_cutoff {f : ℝ → ℝ} (hf : Continuous f)
    {c b s t m ε η : ℝ} (hcb : c < b) (hc : 0 < c) (hbm : b ≤ m)
    (hst : s < t) (hη : 0 ≤ η) (hf0 : f 0 = 0)
    (hlower : ∀ x ∈ Icc 0 m, t*x-ε*m ≤ f x)
    (hcut : ε*m/(t-s) < b)
    (hk : intervalSecantSlope f c (b-c) < s)
    (herr : ∀ x ∈ Icc c b, -η*(b-c) ≤ intervalSecantError f c (b-c) x) :
    ∃ u ∈ Ioo 0 c, f b-f u = s*(b-u) ∧ b-c ≤ b-u ∧
      ∀ x ∈ Icc u b, f u+s*(x-u)-η*(b-u) ≤ f x := by
  have hmul := (div_lt_iff₀ (sub_pos.mpr hst)).mp hcut
  have hb := hlower b ⟨(hc.trans hcb).le,hbm⟩
  have hwhole : s*(b-0) < f b-f 0 := by rw [hf0]; nlinarith
  obtain ⟨u,hu,hs,he⟩ := exists_superlinear_merge_left hf hc hcb hη hwhole hk herr
  exact ⟨u,hu,hs,sub_le_sub_left hu.2.le b,he⟩

end Falconer

end OAI
