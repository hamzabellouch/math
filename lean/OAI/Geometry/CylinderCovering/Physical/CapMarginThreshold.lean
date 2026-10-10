import OAI.Geometry.CylinderCovering.Physical.CapFinite

namespace OAI

open Set Filter
open scoped Topology
noncomputable section
namespace RadialPhysical
open CylinderCovering

theorem physical_cap_fixed_margin_threshold
    (centered square : Bool) (b beta : ℝ) (hb : 0 < b) (hbeta : 0 < beta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ eta : ℝ, 0 < eta → eta < delta →
      ∀ tagU tagL : (N : ℕ) → Fin N → ℝ,
        (∀ N, RadialRiemann.IsTagged (-b) b N (tagU N)) →
        (∀ N, RadialRiemann.IsTagged (-b) b N (tagL N)) →
        ∃ C : (N : ℕ) → Fin (2*N) → TriangularCovering.TriCylinder,
          PhysicalFamilyConclusion centered b eta
            (physicalModelCap centered square b eta beta) tagU tagL C := by
  have hfamily : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ),
      ∀ tagU tagL : (N : ℕ) → Fin N → ℝ,
        (∀ N, RadialRiemann.IsTagged (-b) b N (tagU N)) →
        (∀ N, RadialRiemann.IsTagged (-b) b N (tagL N)) →
        ∃ C : (N : ℕ) → Fin (2*N) → TriangularCovering.TriCylinder,
          PhysicalFamilyConclusion centered b eta
            (physicalModelCap centered square b eta beta) tagU tagL C := by
    filter_upwards [eventually_physicalModelCap_covers centered square hb hbeta]
      with eta hcover
    intro tagU tagL htagU htagL
    exact physical_family_of_sweep_cover centered b eta hb
      (physicalModelCap centered square b eta beta)
      (physicalModelCap_continuous centered square b eta beta).continuousOn
      (fun s _ => physicalModelCap_nonneg centered square b eta beta s hbeta.le)
      hcover tagU tagL htagU htagL
  obtain ⟨delta, hdelta, h⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hfamily
  exact ⟨delta, hdelta, fun eta heta hlt => h ⟨heta, hlt⟩⟩

theorem physical_cap_unit_margin_threshold
    (centered square : Bool) (b : ℝ) (hb : 0 < b) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ eta : ℝ, 0 < eta → eta < delta →
      ∀ tagU tagL : (N : ℕ) → Fin N → ℝ,
        (∀ N, RadialRiemann.IsTagged (-b) b N (tagU N)) →
        (∀ N, RadialRiemann.IsTagged (-b) b N (tagL N)) →
        ∃ C : (N : ℕ) → Fin (2*N) → TriangularCovering.TriCylinder,
          PhysicalFamilyConclusion centered b eta
            (physicalModelCap centered square b eta 1) tagU tagL C :=
  physical_cap_fixed_margin_threshold centered square b 1 hb (by norm_num)

end RadialPhysical

end

end OAI
