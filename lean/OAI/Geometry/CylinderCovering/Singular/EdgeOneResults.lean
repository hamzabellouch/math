import OAI.Geometry.CylinderCovering.Singular.EdgeOneResultsDefinitions
import OAI.Geometry.CylinderCovering.Singular.EdgeOneDifferential
import OAI.Geometry.CylinderCovering.Singular.CutoffDefinitions

namespace OAI

noncomputable section
namespace SingularEdgeOne

lemma flexibleCutoff_iff_admissible (p : ℝ) (rho padding : ℝ → ℝ) :
    FlexibleCutoff p rho padding ↔ CylinderCovering.SingularCutoff.Admissible p rho padding :=
  Iff.rfl

lemma edgeA_eq_canonical (p : ℝ) : edgeA p = CylinderCovering.SingularCutoff.boundaryCoefficient p := rfl
lemma edgeG_eq_canonical (p : ℝ) : edgeG p = CylinderCovering.SingularCutoff.energyCoefficient p := rfl

theorem dictionary : DictionaryStatement where
  field_components p w l hl := ⟨edgeU_eq p w l, edgeV_eq p w hl⟩
  hamiltonian p w l hl := edgeField_Hamiltonian p w (l := l) hl
  ceiling_formula p w c := ⟨edgeCeiling_level p w, ceiling_rescaling p w c⟩
  physical_energy p w c l hl := physical_speed_rescaling_sqrt p w c (l := l) hl
  tetrahedron_image := physicalSimilarity_tetrahedron
  lower_image p c D hD := physicalSimilarity_lower p c (D := D) hD
  upper_image p c D hD := physicalSimilarity_upper p c (D := D) hD
  physical_cost p c D hD hpos := physical_cost_dictionary p c (D := D) hD hpos
  derivative_conjugacy p c z hz := scaled_derivative_conjugacy p c (z := z) hz
  spectral_conjugacy p c mu z hz := scaled_eigenvalue_iff p c mu (z := z) hz
  exact_parameters k gamma hk :=
    ⟨exact_cutoff_dictionary (k := k) hk gamma, exact_padding_dictionary (k := k) hk⟩
  boundary_integral := edgeA_integral
  energy_integral p hp := edgeG_integral (p := p) hp
  coefficient_formula p hp :=
    ⟨edge_coefficient (p := p) hp, edge_coefficient_eq_scaled (p := p) hp⟩
  coefficient_negative p hp hmax := edge_coefficient_neg (p := p) hp hmax
  coefficient_limits := ⟨edgeA_limit, edgeG_limit⟩

end SingularEdgeOne

end

end OAI
