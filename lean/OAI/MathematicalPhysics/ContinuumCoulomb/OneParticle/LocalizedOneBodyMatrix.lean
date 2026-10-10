import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteTensorFormCompression
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.WeightedSpinOrbitals
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedSpinOperator
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteOneBodyCorrection

namespace OAI

/-! The actual spinful one-body matrix is precisely the corrected spatial
matrix, repeated in the two conserved spin components. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem localizedSpinResidual_matrix {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hf : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin (m+1) → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ)
    (a b : Fin ((2*m+1)+1)) :
    flatResidualMatrix (localizedSpinMode freq u) (localizedSpinResidual rho H S freq scale u) a b =
      let p := (HubbardGlobal.siteModes m).symm
      if (p a).2=(p b).2 then
        (correctedManufacturedOneBodyMatrix rho H S freq scale u (p a).1 (p b).1:ℂ) else 0 := by
  let p := (HubbardGlobal.siteModes m).symm
  have hi : Integrable (fun x => correctedLocalizedMode freq u (p a).1 x*
      correctedManufacturedResidual rho H S freq scale u (p b).1 x) :=
    (correctedLocalizedMode_memLp hf u _).integrable_mul
      (correctedManufacturedResidual_memLp hrho hH hS hf scale u hδ hcoeff _)
  have h := flatWeighted_realSpinOrbital_inner (fun _ => 1)
    (correctedLocalizedMode freq u (p a).1)
    (correctedManufacturedResidual rho H S freq scale u (p b).1)
    (by simpa only [one_mul] using hi) (p a).2 (p b).2
  simpa only [flatResidualMatrix,localizedSpinMode,localizedSpinResidual,
    correctedManufacturedOneBodyMatrix,Complex.ofReal_one,one_mul] using h

theorem localizedSpin_nuclear_integrable {freq : ℝ} {m : ℕ}
    (u : Fin (m+1) → PlanarPosition) (F : Position → ℝ)
    (hI : ∀ i j, Integrable (fun x => F x*correctedLocalizedMode freq u i x*
      correctedLocalizedMode freq u j x)) (a b : Fin ((2*m+1)+1)) :
    Integrable (fun z => (F (WithLp.toLp 2 z.2):ℂ)*
      (star (Coulomb.flatSpinOrbital (localizedSpinMode freq u a) z)*
        Coulomb.flatSpinOrbital (localizedSpinMode freq u b) z)) Coulomb.spinSpaceMeasure := by
  exact flatWeighted_realSpinOrbital_integrable F _ _ (hI _ _) _ _

theorem localizedSpin_nuclear_matrix {freq : ℝ} {m : ℕ}
    (u : Fin (m+1) → PlanarPosition) (F : Position → ℝ)
    (hI : ∀ i j, Integrable (fun x => F x*correctedLocalizedMode freq u i x*
      correctedLocalizedMode freq u j x)) (a b : Fin ((2*m+1)+1)) :
    flatNuclearMatrix (localizedSpinMode freq u) F a b =
      let p := (HubbardGlobal.siteModes m).symm
      if (p a).2=(p b).2 then
        ((∫ x, F x*correctedLocalizedMode freq u (p a).1 x*
          correctedLocalizedMode freq u (p b).1 x : ℝ):ℂ) else 0 := by
  exact flatWeighted_realSpinOrbital_inner F _ _ (hI _ _) _ _

theorem localizedSpin_oneBody_matrix {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hf : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin (m+1) → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ)
    (F : Position → ℝ)
    (hI : ∀ i j, Integrable (fun x => F x*correctedLocalizedMode freq u i x*
      correctedLocalizedMode freq u j x)) (a b : Fin ((2*m+1)+1)) :
    flatResidualMatrix (localizedSpinMode freq u) (localizedSpinResidual rho H S freq scale u) a b+
      flatNuclearMatrix (localizedSpinMode freq u) F a b =
      let p := (HubbardGlobal.siteModes m).symm
      if (p a).2=(p b).2 then
        (correctedNuclearOneBodyMatrix rho H S freq scale u F (p a).1 (p b).1:ℂ) else 0 := by
  rw [localizedSpinResidual_matrix hrho hH hS hf scale u hδ hcoeff,
    localizedSpin_nuclear_matrix u F hI]
  dsimp only
  split_ifs <;> simp only [correctedNuclearOneBodyMatrix,Complex.ofReal_add,add_zero]

end ContinuumCoulomb

end

end OAI
