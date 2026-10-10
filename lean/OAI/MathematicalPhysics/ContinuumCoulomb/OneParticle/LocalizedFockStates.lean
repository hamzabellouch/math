import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ClassicalSlaterSynthesis
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.OrthonormalLocalizedModes

namespace OAI

/-! Every state of the actual full half-filled Fock space is realized by
an antisymmetric weak-H1 continuum state in the corrected localized modes.
The continuum mass is exactly the finite occupation norm. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb
open HubbardGlobal

private theorem euclidean_norm_change_fintype {ι : Type*} (F G : Fintype ι)
    (c : EuclideanSpace ℂ ι) :
    (letI := F; ‖c‖) = (letI := G; ‖c‖) := by
  have h : F = G := Subsingleton.elim _ _
  subst G
  rfl

def localizedSpinMode (freq : ℝ) {m : ℕ} (u : Fin (m+1) → PlanarPosition)
    (j : Fin ((2*m+1)+1)) : Position → Fin 2 → ℂ :=
  realSpinOrbital (correctedLocalizedMode freq u ((siteModes m).symm j).1) ((siteModes m).symm j).2

theorem localizedSpinMode_C1 (freq : ℝ) {m : ℕ} (u : Fin (m+1) → PlanarPosition)
    (j : Fin ((2*m+1)+1)) (s : Fin 2) : ContDiff ℝ 1 (fun x => localizedSpinMode freq u j x s) :=
  realSpinOrbital_C1 _ (correctedLocalizedMode_C1 freq u _) _ s

theorem localizedSpinMode_memLp {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin (m+1) → PlanarPosition) (j : Fin ((2*m+1)+1)) (s : Fin 2) :
    MemLp (fun x => localizedSpinMode freq u j x s) 2 :=
  realSpinOrbital_memLp _ (correctedLocalizedMode_memLp hfreq u _) _ s

theorem localizedSpinMode_partial_memLp {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin (m+1) → PlanarPosition) (j : Fin ((2*m+1)+1)) (s : Fin 2) (b : Fin 3) :
    MemLp (fun x => fderiv ℝ (fun y => localizedSpinMode freq u j y s) x (EuclideanSpace.single b 1)) 2 :=
  realSpinOrbital_partial_memLp _ (correctedLocalizedMode_C1 freq u _)
    (correctedLocalizedMode_partial_memLp hfreq u _) _ s b

theorem localizedSpinMode_inner {freq D : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin (m+1) → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : (m+1 : ℕ) * localizedOverlapBound D ≤ 1/2) (i j : Fin ((2*m+1)+1)) :
    (∑ s : Fin 2, ∫ x, star (localizedSpinMode freq u i x s) * localizedSpinMode freq u j x s) =
      if i=j then (1 : ℂ) else 0 := by
  exact selectedRealSpinOrbitals_orthonormal (correctedLocalizedMode freq u) (by
    intro a b
    by_cases hab : a=b
    · simpa only [hab, ite_true] using correctedLocalizedMode_inner hfreq u hsep hs a b
    · simpa only [hab, ite_false] using correctedLocalizedMode_inner hfreq u hsep hs a b)
    (siteModes m).symm (siteModes m).symm.injective i j

def localizedFockState {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin (m+1) → PlanarPosition) (c : EuclideanSpace ℂ (HalfFilledBasis m)) : Coulomb.H1Vector (m+1) :=
  classicalSlaterSynthesis (localizedSpinMode freq u) (localizedSpinMode_C1 freq u)
    (localizedSpinMode_memLp hfreq u) (localizedSpinMode_partial_memLp hfreq u) c

theorem localizedFockState_antisymmetric {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin (m+1) → PlanarPosition) (c : EuclideanSpace ℂ (HalfFilledBasis m)) :
    Coulomb.Antisymmetric (localizedFockState hfreq u c) :=
  classicalSlaterSynthesis_antisymmetric _ _ _ _ _

theorem localizedFockState_mass {freq D : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin (m+1) → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : (m+1 : ℕ) * localizedOverlapBound D ≤ 1/2) (c : EuclideanSpace ℂ (HalfFilledBasis m)) :
    Coulomb.mass (localizedFockState hfreq u c) = ‖c‖^2 := by
  have h := classicalSlaterSynthesis_mass (localizedSpinMode freq u) (localizedSpinMode_C1 freq u)
    (localizedSpinMode_memLp hfreq u) (localizedSpinMode_partial_memLp hfreq u)
    (localizedSpinMode_inner hfreq u hsep hs) c
  exact h.trans (congrArg (fun t : ℝ => t^2)
    (euclidean_norm_change_fintype
      (inferInstance : Fintype (SlaterOccupation.Occupied (2*m+1) (m+1)))
      (inferInstance : Fintype (HalfFilledBasis m)) c))

def localizedFockFormState {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin (m+1) → PlanarPosition) (c : EuclideanSpace ℂ (HalfFilledBasis m)) : FormState (m+1) :=
  ⟨localizedFockState hfreq u c, localizedFockState_antisymmetric hfreq u c⟩

theorem localizedFockFormState_normalized {freq D : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin (m+1) → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : (m+1 : ℕ) * localizedOverlapBound D ≤ 1/2) (c : EuclideanSpace ℂ (HalfFilledBasis m))
    (hc : ‖c‖=1) : normSq (localizedFockFormState hfreq u c) = 1 := by
  change Coulomb.mass (localizedFockState hfreq u c) = 1
  rw [localizedFockState_mass hfreq u hsep hs, hc, one_pow]

end ContinuumCoulomb

end

end OAI
