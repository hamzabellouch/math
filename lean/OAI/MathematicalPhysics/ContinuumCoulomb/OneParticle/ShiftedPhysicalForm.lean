import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteTensorFormError
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.Dilation

namespace OAI

/-! Exact energy offset between the manufactured form and the physical
Coulomb Hamiltonian. All identities hold on the full weak-H1 domain. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem nuclearPerturbedForm_physical_identity {M n : ℕ}
    (nuc : Coulomb.Nuclei M) (W F : Position → ℝ) (scale offset : ℝ)
    (hsplit : ∀ y, W y+F y = -scale⁻¹*Coulomb.attraction nuc y-offset)
    (w : Coulomb.H1Vector n) (hI : nuclearFormIntegrable F w) :
    nuclearPerturbedForm (fun x => ∑ i, W (Coulomb.position x i)) F w =
      Coulomb.kinetic w-scale⁻¹*Coulomb.nuclearEnergy nuc w-
        (n:ℝ)*offset*Coulomb.mass w := by
  have hpoint (s : SpinConfiguration n) (x : Configuration n) :
      (∑ i, W (Coulomb.position x i))*‖w.value s x‖^2 =
        -scale⁻¹*((∑ i, Coulomb.attraction nuc (Coulomb.position x i))*‖w.value s x‖^2)-
        (n:ℝ)*offset*‖w.value s x‖^2-
        ∑ i, F (Coulomb.position x i)*‖w.value s x‖^2 := by
    have he (i : Fin n) : W (Coulomb.position x i) =
        -scale⁻¹*Coulomb.attraction nuc (Coulomb.position x i)-offset-F (Coulomb.position x i) := by
      linarith only [hsplit (Coulomb.position x i)]
    simp_rw [he]
    simp only [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  have hi (s : SpinConfiguration n) :
      (∫ x, (∑ i, W (Coulomb.position x i))*‖w.value s x‖^2)+
        ∑ i, ∫ x, F (Coulomb.position x i)*‖w.value s x‖^2 =
      -scale⁻¹*(∫ x, (∑ i, Coulomb.attraction nuc (Coulomb.position x i))*‖w.value s x‖^2)-
        (n:ℝ)*offset*(∫ x, ‖w.value s x‖^2) := by
    simp_rw [hpoint]
    have ha : Integrable (fun x => -scale⁻¹*
        ((∑ i, Coulomb.attraction nuc (Coulomb.position x i))*‖w.value s x‖^2)) :=
      (w.nuclear_integrable nuc s).const_mul _
    have hb : Integrable (fun x => (n:ℝ)*offset*‖w.value s x‖^2) :=
      (w.value_L2 s).norm.integrable_sq.const_mul _
    have hc : Integrable (fun x => ∑ i, F (Coulomb.position x i)*‖w.value s x‖^2) :=
      integrable_finsetSum _ (fun i _ => hI s i)
    have hsub := integral_sub (ha.sub hb) hc
    have hsub' := integral_sub ha hb
    simp only [Pi.sub_apply] at hsub hsub'
    rw [hsub,hsub',
      integral_const_mul,integral_const_mul,
      integral_finsetSum _ (fun i _ => hI s i)]
    ring
  unfold nuclearPerturbedForm boundedPotentialForm nuclearErrorEnergy Coulomb.nuclearEnergy Coulomb.mass
  rw [add_assoc,← Finset.sum_add_distrib]
  simp_rw [hi]
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum]
  ring

theorem dilated_physicalForm_shift {M n : ℕ}
    (nuc : Coulomb.Nuclei M) (W F : Position → ℝ) {scale : ℝ} (hscale : 0 < scale)
    (offset : ℝ) (hsplit : ∀ y, W y+F y = -scale⁻¹*Coulomb.attraction nuc y-offset)
    (w : Coulomb.H1Vector n) (hI : nuclearFormIntegrable F w) :
    Coulomb.form (dilatedNuclei nuc scale (ne_of_gt hscale))
        (normalizedDilation w scale (ne_of_gt hscale)) =
      scale^2*(nuclearPerturbedForm (fun x => ∑ i, W (Coulomb.position x i)) F w+
        scale⁻¹*Coulomb.pairEnergy w)+(scale^2*(n:ℝ)*offset)*Coulomb.mass w := by
  rw [form_normalizedDilation nuc w hscale,
    nuclearPerturbedForm_physical_identity nuc W F scale offset hsplit w hI]
  field_simp [ne_of_gt hscale]
  ring

end ContinuumCoulomb

end

end OAI
