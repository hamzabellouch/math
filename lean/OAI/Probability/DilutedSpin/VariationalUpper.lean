import OAI.Probability.DilutedSpin.DenseUpper
import OAI.Probability.DilutedSpin.MixedPatterns

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory KernelTower PrescribedTree Set Filter
open scoped NNReal BigOperators Topology
variable {N q : ℕ} [NeZero N]

lemma pressure_le_phi (M : Model (q+1)) (hM : Admissible M) (r : ℕ) :
    pressure M N ≤ phi M r := by
  obtain ⟨m,hm⟩ := exponents_nonempty r
  apply le_csInf
  · exact ⟨functional M r (zeroHierarchy (r+1)) m,zeroHierarchy (r+1),m,hm,rfl⟩
  · rintro v ⟨ζ,m,hm,rfl⟩
    exact pressure_le_functional M hM r ζ m hm

lemma pressure_le_variationalValue (M : Model (q+1)) (hM : Admissible M) :
    pressure M N ≤ variationalValue M := by
  apply le_ciInf
  intro r
  exact pressure_le_phi M hM r

lemma phi_le_functional (M : Model (q+1)) (hM : Admissible M)
    (r : ℕ) (ζ : Hierarchy (r+1)) (m : Fin r → ℝ) (hm : Exponents m) :
    phi M r ≤ functional M r ζ m := by
  apply csInf_le
  · refine ⟨pressure M 1,?_⟩
    rintro v ⟨ζ,m,hm,rfl⟩
    exact pressure_le_functional M hM r ζ m hm
  · exact ⟨ζ,m,hm,rfl⟩

lemma variationalValue_le_phi (M : Model (q+1)) (hM : Admissible M) (r : ℕ) :
    variationalValue M ≤ phi M r := by
  apply ciInf_le
  refine ⟨pressure M 1,?_⟩
  rintro v ⟨r,rfl⟩
  exact pressure_le_phi M hM r

lemma variationalValue_le_functional (M : Model (q+1)) (hM : Admissible M)
    (r : ℕ) (ζ : Hierarchy (r+1)) (m : Fin r → ℝ) (hm : Exponents m) :
    variationalValue M ≤ functional M r ζ m :=
  (variationalValue_le_phi M hM r).trans (phi_le_functional M hM r ζ m hm)

end DilutedSpinGlass

end

end OAI
