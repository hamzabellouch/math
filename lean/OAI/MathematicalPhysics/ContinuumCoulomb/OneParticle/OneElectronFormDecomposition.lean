import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CorrectedCrossBound

namespace OAI

/-! Exact full-graph decomposition into the corrected orbital component and
its orthogonal remainder. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem correctedOneElectron_graph_decomposition {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (v : Coulomb.H1Vector 1) :
    h1Coordinates v = h1Coordinates (correctedOneElectronProjection hfreq u v)+
      h1Coordinates (correctedOneElectronRemainder hfreq u v) := by
  funext a
  apply Lp.ext
  filter_upwards [(h1Coordinate_memLp v a).coeFn_toLp,
    (h1Coordinate_memLp (correctedOneElectronProjection hfreq u v) a).coeFn_toLp,
    (h1Coordinate_memLp (correctedOneElectronRemainder hfreq u v) a).coeFn_toLp,
    Lp.coeFn_add (h1Coordinates (correctedOneElectronProjection hfreq u v) a)
      (h1Coordinates (correctedOneElectronRemainder hfreq u v) a)] with x hv hp hr ha
  change h1Coordinates v a x = _ at hv
  change h1Coordinates (correctedOneElectronProjection hfreq u v) a x = _ at hp
  change h1Coordinates (correctedOneElectronRemainder hfreq u v) a x = _ at hr
  change h1Coordinates v a x = (h1Coordinates (correctedOneElectronProjection hfreq u v) a+
    h1Coordinates (correctedOneElectronRemainder hfreq u v) a) x
  rw [ha]
  simp only [Pi.add_apply]
  rw [hv,hp,hr]
  cases a <;> simp only [h1CoordinateFunction,correctedOneElectronRemainder,Coulomb.H1Vector.add,
    Coulomb.H1Vector.rsmul,Complex.ofReal_neg,Complex.ofReal_one] <;> ring

theorem correctedOneElectron_form_decomposition {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (v : Coulomb.H1Vector 1)
    (V : Configuration 1 → ℝ) (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B) :
    boundedPotentialForm V v =
      boundedPotentialForm V (correctedOneElectronProjection hfreq u v)+
      boundedPotentialForm V (correctedOneElectronRemainder hfreq u v)+
      2*graphBoundedCross (BoundedPotential.operator V hV B hB)
        (h1Coordinates (correctedOneElectronProjection hfreq u v))
        (h1Coordinates (correctedOneElectronRemainder hfreq u v)) := by
  simp only [boundedPotentialForm_eq_graph V hV B hB]
  rw [correctedOneElectron_graph_decomposition hfreq u v]
  exact graphBoundedForm_add _ (boundedPotential_operator_symmetric V hV B hB) _ _

/-- Scalar absorption of a mixed form; the denominator is the retained
complement gap and no square root is introduced into the reduction. -/
theorem absorb_cross_term {c B p q δ : ℝ}
    (hB : 0 ≤ B) (hp : 0 ≤ p) (hq : 0 ≤ q) (hδ : 0 < δ)
    (hc : c^2 ≤ B*p*q) : -(B/δ)*p-δ*q ≤ 2*c := by
  let a := B/δ*p
  let b := δ*q
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := mul_nonneg hδ.le hq
  have hab : a*b = B*p*q := by dsimp [a,b]; field_simp
  have hc' : c^2 ≤ a*b := by rwa [hab]
  have h : -a-b ≤ 2*c := by
    by_contra hh
    have hneg : 2*c < -a-b := lt_of_not_ge hh
    have hprod := mul_pos (by linarith : 0 < -2*c-(a+b))
      (by linarith : 0 < -2*c+(a+b))
    nlinarith only [hc',sq_nonneg (a-b),hprod]
  simpa only [a,b,neg_mul] using h

end ContinuumCoulomb

end

end OAI
