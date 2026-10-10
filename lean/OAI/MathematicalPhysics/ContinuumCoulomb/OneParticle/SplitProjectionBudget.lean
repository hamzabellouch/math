import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SplitProjectionPairing

namespace OAI

/-! The full planar slice penalty is controlled by transverse mass and
the finite family of actual tensor-orbital coefficients. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarCoefficient_mass_split {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    (∫ z, (planarCoefficient u f z)^2) =
      (∫ z, (planarCoefficient u (verticalResidual freq f) z)^2) +
        (∫ p, f p*localizedMode freq u p)^2 := by
  let a := verticalCoefficient freq f
  let c := ∫ r, a r*normalizedPlanarMode (r-u)
  let b := planarCoefficient u f
  let r := planarCoefficient u (verticalResidual freq f)
  have ha : MemLp a 2 := (verticalCoefficient_contraction hfreq f hf).1
  have hl := verticalLift_memLp hfreq a ha
  have hr := (planarCoefficient_contraction u (verticalResidual freq f)
    (verticalResidual_mass hfreq f hf).1).1
  have hbeq : b =ᵐ[volume] fun z => r z+c*verticalMode freq z := by
    have hs := planarCoefficient_sub_ae u f (verticalLift freq a) hf hl
    filter_upwards [hs] with z hz
    have he := planarCoefficient_lift u freq a z
    change r z = b z-planarCoefficient u (verticalLift freq a) z at hz
    rw [he] at hz
    change b z = r z+c*verticalMode freq z
    dsimp [c]
    linarith
  rw [verticalCoefficient_pair_tensor hfreq u f hf]
  change (∫ z, (b z)^2) = (∫ z, (r z)^2)+c^2
  calc
    _ = ∫ z, (r z+c*verticalMode freq z)^2 :=
      integral_congr_ae (hbeq.mono (fun z hz => by rw [hz]))
    _ = (∫ z, (r z)^2)+(2*c)*(∫ z, r z*verticalMode freq z)+
        c^2*(∫ z, (verticalMode freq z)^2) := by
      have he : (fun z => (r z+c*verticalMode freq z)^2) =
          (fun z => (r z)^2+((2*c)*(r z*verticalMode freq z)+c^2*(verticalMode freq z)^2)) := by
        funext z
        ring
      have hc := hr.integrable_mul (verticalMode_memLp hfreq)
      rw [he,integral_add (f := fun z => (r z)^2)
        (g := fun z => (2*c)*(r z*verticalMode freq z)+c^2*(verticalMode freq z)^2)
        hr.integrable_sq
        ((hc.const_mul (2*c)).add ((verticalMode_square_integrable hfreq).const_mul (c^2))),
        integral_add (f := fun z => (2*c)*(r z*verticalMode freq z))
          (g := fun z => c^2*(verticalMode freq z)^2)
          (hc.const_mul (2*c)) ((verticalMode_square_integrable hfreq).const_mul (c^2)),
        integral_const_mul,integral_const_mul]
      ring
    _ = _ := by
      rw [residual_planarCoefficient_orthogonal hfreq u f hf,verticalMode_normalized hfreq]
      ring

/-- The estimate removes the spurious infinite-dimensional planar penalty
in the excited transverse sector, retaining only actual tensor coefficients. -/
theorem split_projection_budget {freq D : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    (∫ z, ∑ i, (planarCoefficient (u i) f z)^2) ≤
      (1+m*localizedOverlapBound D)*
        ((∫ p, f p^2)-(∫ r, (verticalCoefficient freq f r)^2)) +
      ∑ i, (∫ p, f p*localizedMode freq (u i) p)^2 := by
  have hR := verticalResidual_mass hfreq f hf
  have hb := split_planar_frame_bound u hsep (verticalResidual freq f) hR.1
  rw [hR.2] at hb
  have he : (∫ z, ∑ i, (planarCoefficient (u i) f z)^2) =
      (∫ z, ∑ i, (planarCoefficient (u i) (verticalResidual freq f) z)^2) +
      ∑ i, (∫ p, f p*localizedMode freq (u i) p)^2 := by
    rw [integral_finsetSum _ (fun i _ => (planarCoefficient_contraction (u i) f hf).1.integrable_sq),
      integral_finsetSum _ (fun i _ =>
        (planarCoefficient_contraction (u i) (verticalResidual freq f) hR.1).1.integrable_sq)]
    simp_rw [planarCoefficient_mass_split hfreq _ f hf]
    rw [Finset.sum_add_distrib]
  rw [he]
  exact add_le_add hb le_rfl

end ContinuumCoulomb

end

end OAI
