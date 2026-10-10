import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarWellBottom

namespace OAI

/-! Exact ground-state transform for the actual manufactured planar well. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def planarGroundQuotient (u : PlanarPosition → ℝ) (x : PlanarPosition) : ℝ :=
  u x/planarResolventMode x

theorem planarGroundQuotient_C1 {u : PlanarPosition → ℝ} (hu : ContDiff ℝ 1 u) :
    ContDiff ℝ 1 (planarGroundQuotient u) :=
  hu.div (planarResolventMode_C7.of_le (by norm_num))
    (fun x => (planarResolventMode_positive x).ne')

theorem planarGroundQuotient_compact {u : PlanarPosition → ℝ} (hc : HasCompactSupport u) :
    HasCompactSupport (planarGroundQuotient u) := by
  change HasCompactSupport (fun x => u x*(planarResolventMode x)⁻¹)
  exact hc.mul_right

theorem planarGroundQuotient_energy (u : PlanarPosition → ℝ)
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    (∑ a : Fin 2, ∫ x, planarResolventMode x^2 *
      planarPartial (planarGroundQuotient u) (planarAxis a) x^2) =
      2*planarTestForm manufacturedPlanarWell u + ∫ x, u x^2 := by
  let phi := planarResolventMode
  let v := planarGroundQuotient u
  have hp : ContDiff ℝ 2 phi := planarResolventMode_C7.of_le (by norm_num)
  have hv : ContDiff ℝ 1 v := planarGroundQuotient_C1 hu
  have hvc : HasCompactSupport v := planarGroundQuotient_compact hc
  have hfactor (x : PlanarPosition) : phi x*v x = u x := by
    dsimp [phi,v,planarGroundQuotient]
    field_simp [(planarResolventMode_positive x).ne']
  have hf : (fun x => phi x*v x) = u := funext hfactor
  have hB (x : PlanarPosition) : phi x*planarLaplacian phi x*v x^2 =
      (2*manufacturedPlanarWell x+1)*u x^2 := by
    rw [manufacturedPlanarWell_eigen_equation]
    calc
      _ = (2*manufacturedPlanarWell x+1)*(phi x*v x)^2 := by ring
      _ = _ := by rw [hfactor]
  have hc2 : HasCompactSupport (fun x => u x^2) :=
    hc.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have hiP : Integrable (fun x => manufacturedPlanarWell x*u x^2) :=
    (manufacturedPlanarWell_C7.continuous.mul (hu.continuous.pow 2)).integrable_of_hasCompactSupport
      hc2.mul_left
  have hiM : Integrable (fun x => u x^2) :=
    (hu.continuous.pow 2).integrable_of_hasCompactSupport hc2
  have hpot : (∫ x, (2*manufacturedPlanarWell x+1)*u x^2) =
      2*(∫ x, manufacturedPlanarWell x*u x^2)+(∫ x, u x^2) := by
    rw [show (fun x => (2*manufacturedPlanarWell x+1)*u x^2) =
      (fun x => 2*(manufacturedPlanarWell x*u x^2)+u x^2) from by funext x; ring]
    rw [integral_add (hiP.const_mul 2) hiM,integral_const_mul]
  calc
    _ = ∑ a : Fin 2, ∫ x, planarPartial (fun y => phi y*v y) (planarAxis a) x^2+
        phi x*planarPartial (planarPartial phi (planarAxis a)) (planarAxis a) x*v x^2 := by
      exact Finset.sum_congr rfl (fun a _ => (planar_ground_transform_direction phi v hp hv hvc _).symm)
    _ = (∑ a : Fin 2, ∫ x, planarPartial u (planarAxis a) x^2)+
        ∫ x, (2*manufacturedPlanarWell x+1)*u x^2 := by
      rw [planar_transform_energy_split phi v hp hv hvc,hf]
      simp_rw [hB]
    _ = _ := by
      rw [hpot]
      unfold planarTestForm
      ring

end ContinuumCoulomb

end

end OAI
