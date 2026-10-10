import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CenteredGaussEquiv
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.GridNuclei
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.FormStability

namespace OAI

/-! The centered label list and the analytic finite grid describe the same
nuclear cloud, including after physical dilation. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem formGroundEnergy_eq_of_attraction {m l : ℕ} (S : Coulomb.Nuclei m)
    (T : Coulomb.Nuclei l) (h : ∀ x, Coulomb.attraction S x=Coulomb.attraction T x) (n : ℕ) :
    formGroundEnergy S n=formGroundEnergy T n := by
  have he (w : Coulomb.H1Vector n) : Coulomb.form S w=Coulomb.form T w := by
    unfold Coulomb.form Coulomb.nuclearEnergy
    simp_rw [h]
  simp only [formGroundEnergy,he]

instance centeredGridIndices_nonempty (r : Fin 3 → ℕ) :
    Nonempty {k // k ∈ centeredGridIndices r} :=
  ⟨⟨0,(mem_centeredGridIndices r 0).mpr (fun i => by simp)⟩⟩

namespace CenteredGaussLabels

private theorem gauss_point_injective {h : ℝ} (hh : 0 < h) :
    Function.Injective (gaussLatticePoint h) := by
  intro a b hab
  by_contra hne
  have hs := gaussLatticePoint_separation hh a b hne
  rw [hab,sub_self,norm_zero] at hs
  linarith

def nuclei (r : Radii) (G : Position → Position) (hG : Function.Injective G)
    {h : ℝ} (hh : 0 < h) : Coulomb.Nuclei (labels r).length where
  nonempty := by rw [labels_length]; positivity
  position a := G (gaussLatticePoint h (RationalGaussNodes.index ((labels r).get a).1 ((labels r).get a).2))
  distinct := by
    intro a b hab
    have he := gauss_point_injective hh (hG hab)
    apply (enumerationEquiv r).injective
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun x : GaussLatticeIndex => x.1) he
    · exact congrArg (fun x : GaussLatticeIndex => x.2) he
  charge _ := 1
  charge_ge_one _ := le_rfl

theorem nuclei_attraction (r : Radii) (G : Position → Position) (hG : Function.Injective G)
    {h : ℝ} (hh : 0 < h) (x : Position) :
    Coulomb.attraction (nuclei r G hG hh) x =
      Coulomb.attraction
        (gridNuclei (fun k : {k // k ∈ centeredGridIndices (radiiVector r)} => k.val)
          Subtype.val_injective G hG hh) x := by
  rw [gridNuclei_attraction]
  simp only [Coulomb.attraction,nuclei,one_mul]
  simpa only [Fintype.sum_prod_type,gridGaussIndex] using
    sum_enumeration r (fun a => Coulomb.coulombKernel (x-G (gaussLatticePoint h a)))

theorem nuclei_ground (r : Radii) (G : Position → Position) (hG : Function.Injective G)
    {h : ℝ} (hh : 0 < h) (n : ℕ) :
    formGroundEnergy (nuclei r G hG hh) n =
      formGroundEnergy
        (gridNuclei (fun k : {k // k ∈ centeredGridIndices (radiiVector r)} => k.val)
          Subtype.val_injective G hG hh) n :=
  formGroundEnergy_eq_of_attraction _ _ (nuclei_attraction r G hG hh) n

theorem dilated_nuclei_ground (r : Radii) (G : Position → Position) (hG : Function.Injective G)
    {h scale : ℝ} (hh : 0 < h) (hs : 0 < scale) (n : ℕ) :
    formGroundEnergy (dilatedNuclei (nuclei r G hG hh) scale hs.ne') n =
      formGroundEnergy (dilatedNuclei
        (gridNuclei (fun k : {k // k ∈ centeredGridIndices (radiiVector r)} => k.val)
          Subtype.val_injective G hG hh) scale hs.ne') n := by
  apply formGroundEnergy_eq_of_attraction
  intro x
  rw [attraction_dilatedNuclei _ hs,attraction_dilatedNuclei _ hs,nuclei_attraction]

theorem nuclei_totalCharge (r : Radii) (G : Position → Position) (hG : Function.Injective G)
    {h : ℝ} (hh : 0 < h) : Coulomb.totalCharge (nuclei r G hG hh)=(labels r).length := by
  simp [Coulomb.totalCharge,nuclei]

end CenteredGaussLabels
end ContinuumCoulomb

end

end OAI
