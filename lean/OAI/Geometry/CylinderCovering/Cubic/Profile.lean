import OAI.Geometry.CylinderCovering.Angular.Margins

namespace OAI

noncomputable section
namespace CylinderCovering.Cubic

theorem profileMax_eq_sSup {a b : ℝ} (hab : a ≤ b) :
    profileMax a b = sSup (profile '' Set.Icc a b) := by
  have hbdd : BddAbove (profile '' Set.Icc a b) := by
    refine ⟨profileMax a b, ?_⟩
    rintro z ⟨q, hq, rfl⟩
    exact profile_le_max_endpoints hq.1 hq.2
  apply le_antisymm
  · apply max_le
    · exact le_csSup hbdd ⟨a, ⟨le_rfl, hab⟩, rfl⟩
    · exact le_csSup hbdd ⟨b, ⟨hab, le_rfl⟩, rfl⟩
  · apply csSup_le
    · exact ⟨profile a, a, ⟨le_rfl, hab⟩, rfl⟩
    · rintro z ⟨q, hq, rfl⟩
      exact profile_le_max_endpoints hq.1 hq.2

theorem profileMax_attained {a b : ℝ} (hab : a ≤ b) :
    ∃ q ∈ Set.Icc a b, profile q = profileMax a b := by
  rcases le_total (profile a) (profile b) with h | h
  · exact ⟨b, ⟨hab, le_rfl⟩, (max_eq_right h).symm⟩
  · exact ⟨a, ⟨le_rfl, hab⟩, (max_eq_left h).symm⟩

theorem profileMax_isGreatest {a b : ℝ} (hab : a ≤ b) :
    IsGreatest (profile '' Set.Icc a b) (profileMax a b) := by
  constructor
  · obtain ⟨q, hq, heq⟩ := profileMax_attained hab
    exact ⟨q, hq, heq⟩
  · rintro z ⟨q, hq, rfl⟩
    exact profile_le_max_endpoints hq.1 hq.2

end CylinderCovering.Cubic

end

end OAI
