import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SplitFormIntegrals

namespace OAI

/-! Fubini identities for the full split-coordinate kinetic and potential
forms. No domain restriction beyond compact C1 test functions is introduced. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem split_integral_planar (g : SplitPosition → ℝ) (hg : Integrable g) :
    (∫ z : ℝ, ∫ r : PlanarPosition, g (r,z)) = ∫ p, g p := by
  have hi : Integrable g (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hg
  simpa only [Measure.volume_eq_prod] using (integral_prod_symm _ hi).symm

theorem split_integral_vertical (g : SplitPosition → ℝ) (hg : Integrable g) :
    (∫ r : PlanarPosition, ∫ z : ℝ, g (r,z)) = ∫ p, g p := by
  have hi : Integrable g (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hg
  simpa only [Measure.volume_eq_prod] using (integral_prod _ hi).symm

def splitRealKinetic (f : SplitPosition → ℝ) : ℝ :=
  (1/2:ℝ)*((∑ a : Fin 2, ∫ p, (splitPlanarPartial f a p)^2) +
    ∫ p, (splitVerticalPartial f p)^2)

def splitRealForm (V : SplitPosition → ℝ) (f : SplitPosition → ℝ) : ℝ :=
  splitRealKinetic f+∫ p, V p*f p^2

def splitSeparablePotential {m : ℕ} (u : Fin m → PlanarPosition)
    (freq S : ℝ) (p : SplitPosition) : ℝ :=
  planarWellSum u p.1+verticalCapPotential freq S p.2

theorem splitPlanarForm_eq {m : ℕ} (u : Fin m → PlanarPosition)
    {f : SplitPosition → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    splitPlanarForm u f =
      (1/2:ℝ)*(∑ a : Fin 2, ∫ p, (splitPlanarPartial f a p)^2) +
      ∫ p, planarWellSum u p.1*f p^2 := by
  have hk (a : Fin 2) : Integrable (fun z : ℝ => ∫ r : PlanarPosition,
      (splitPlanarPartial f a (r,z))^2) := by
    have hi : Integrable (fun p => (splitPlanarPartial f a p)^2) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact splitPlanarPartial_square_integrable hf hc a
    exact hi.integral_prod_right
  have hp : Integrable (fun p : SplitPosition => planarWellSum u p.1*f p^2) :=
    split_potential_integrable hf.continuous hc ((planarWellSum_continuous u).comp continuous_fst)
  have hp' : Integrable (fun z : ℝ => ∫ r : PlanarPosition, planarWellSum u r*f (r,z)^2) := by
    have hi : Integrable (fun p : SplitPosition => planarWellSum u p.1*f p^2)
        (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact hp
    exact hi.integral_prod_right
  unfold splitPlanarForm
  simp_rw [planarTestForm, splitPlanarPartial_eq hf]
  rw [integral_add ((integrable_finsetSum _ (fun a _ => hk a)).const_mul _) hp',
    integral_const_mul, integral_finsetSum _ (fun a _ => hk a)]
  simp_rw [split_integral_planar _ (splitPlanarPartial_square_integrable hf hc _)]
  rw [split_integral_planar _ hp]

theorem splitVerticalForm_eq (freq S : ℝ)
    {f : SplitPosition → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    splitVerticalForm freq S f =
      (1/2:ℝ)*(∫ p, (splitVerticalPartial f p)^2) +
      ∫ p, verticalCapPotential freq S p.2*f p^2 := by
  have hk := splitVerticalPartial_square_integrable hf hc
  have hk' : Integrable (fun r : PlanarPosition => ∫ z : ℝ,
      (splitVerticalPartial f (r,z))^2) := by
    have hi : Integrable (fun p => (splitVerticalPartial f p)^2) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact hk
    exact hi.integral_prod_left
  have hp : Integrable (fun p : SplitPosition => verticalCapPotential freq S p.2*f p^2) := by
    apply split_potential_integrable hf.continuous hc
    unfold verticalCapPotential
    fun_prop
  have hp' : Integrable (fun r : PlanarPosition => ∫ z : ℝ, verticalCapPotential freq S z*f (r,z)^2) := by
    have hi : Integrable (fun p : SplitPosition => verticalCapPotential freq S p.2*f p^2)
        (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact hp
    exact hi.integral_prod_left
  unfold splitVerticalForm
  simp_rw [verticalCappedForm, splitVerticalPartial_eq hf]
  rw [integral_add (hk'.const_mul _) hp', integral_const_mul,
    split_integral_vertical _ hk, split_integral_vertical _ hp]

theorem splitSeparableForm_eq {m : ℕ} (u : Fin m → PlanarPosition) (freq S : ℝ)
    {f : SplitPosition → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    splitRealForm (splitSeparablePotential u freq S) f =
      splitPlanarForm u f+splitVerticalForm freq S f := by
  have hp : Integrable (fun p : SplitPosition => planarWellSum u p.1*f p^2) :=
    split_potential_integrable hf.continuous hc ((planarWellSum_continuous u).comp continuous_fst)
  have hv : Integrable (fun p : SplitPosition => verticalCapPotential freq S p.2*f p^2) := by
    apply split_potential_integrable hf.continuous hc
    unfold verticalCapPotential
    fun_prop
  rw [splitPlanarForm_eq u hf hc, splitVerticalForm_eq freq S hf hc]
  unfold splitRealForm splitRealKinetic splitSeparablePotential
  simp_rw [add_mul]
  rw [integral_add hp hv]
  ring

end ContinuumCoulomb

end

end OAI
