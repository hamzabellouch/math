import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RealOneElectronState
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OrbitalGraphBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.WeightedSourcePairing
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CompactOrbitalDensity

namespace OAI

/-! Removal of the compact cutoff in the nuclear matrix element. The
full weak-H1 absolute form estimate controls the removed orbital tail. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem orbital_nuclear_cutoff_error {freq : ℝ} (hfreq : 0 < freq) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (B R : ℝ), 0 ≤ B → 1 ≤ R →
    ∀ (F : Position → ℝ), Measurable F →
    (∀ (w : Coulomb.H1Vector 1) (s : SpinConfiguration 1),
      Integrable (fun x => |F (Coulomb.position x 0)| * ‖w.value s x‖^2)) →
    (∀ (w : Coulomb.H1Vector 1) (s : SpinConfiguration 1),
      (∫ x, |F (Coulomb.position x 0)| * ‖w.value s x‖^2) ≤
        B*((∫ x, ‖w.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖w.gradient s (0,k) x‖^2)) →
    ∀ u v : PlanarPosition,
      Integrable (fun x => F x*continuumLocalizedMode freq u x*continuumLocalizedMode freq v x) ∧
      Integrable (fun x => F x*compactOrbitalDensity freq R u v x) ∧
      |(∫ x, F x*continuumLocalizedMode freq u x*continuumLocalizedMode freq v x)-
        ∫ x, F x*compactOrbitalDensity freq R u v x| ≤ C*B/R^12 := by
  obtain ⟨T,hT,ht⟩ := orbitalRemainder_graph_bound hfreq
  obtain ⟨A,hA,ha⟩ := continuumLocalizedMode_graph_uniform freq
  let C := T+A
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hC0 : 0 ≤ C := add_nonneg hT0 hA0
  refine ⟨C,by dsimp [C]; linarith,?_⟩
  intro B R hB hR F hF hI hbound u v
  have hR0 : 0 < R := by linarith
  have hu := (continuumLocalizedMode_C7 freq u).of_le (show (1 : WithTop ℕ∞) ≤ 7 by norm_num)
  have hv := (continuumLocalizedMode_C7 freq v).of_le (show (1 : WithTop ℕ∞) ≤ 7 by norm_num)
  have hrem := orbitalRemainder_C1 freq R u
  have hIr := real_nuclear_integrable_transfer F hI _ hrem
    (orbitalRemainder_memLp hfreq hR0 u) (orbitalRemainder_deriv_memLp hfreq hR u)
  have hIu := real_nuclear_integrable_transfer F hI _ hu
    (continuumLocalizedMode_memLp hfreq u) (continuumLocalizedMode_fderiv_memLp hfreq u)
  have hIv := real_nuclear_integrable_transfer F hI _ hv
    (continuumLocalizedMode_memLp hfreq v) (continuumLocalizedMode_fderiv_memLp hfreq v)
  have hbr : (∫ x, |F x| *orbitalRemainder freq R u x^2) ≤ B*(T/R^24) := by
    exact (real_nuclear_form_transfer F B hbound _ hrem
      (orbitalRemainder_memLp hfreq hR0 u) (orbitalRemainder_deriv_memLp hfreq hR u)).trans
      (mul_le_mul_of_nonneg_left (ht R hR u) hB)
  have hbv : (∫ x, |F x| *continuumLocalizedMode freq v x^2) ≤ B*A := by
    exact (real_nuclear_form_transfer F B hbound _ hv
      (continuumLocalizedMode_memLp hfreq v) (continuumLocalizedMode_fderiv_memLp hfreq v)).trans
      (mul_le_mul_of_nonneg_left (ha v) hB)
  obtain ⟨hir,hsq⟩ := weighted_source_pairing F _ _ hF hrem.continuous.measurable hv.continuous.measurable hIr hIv
  have hiuv := (weighted_source_pairing F _ _ hF hu.continuous.measurable hv.continuous.measurable hIu hIv).1
  have he (x : Position) : F x*compactOrbitalDensity freq R u v x =
      F x*continuumLocalizedMode freq u x*continuumLocalizedMode freq v x-
      F x*orbitalRemainder freq R u x*continuumLocalizedMode freq v x := by
    dsimp [compactOrbitalDensity,orbitalRemainder]
    ring
  have hic : Integrable (fun x => F x*compactOrbitalDensity freq R u v x) := by
    simp_rw [he]
    exact hiuv.sub hir
  refine ⟨hiuv,hic,?_⟩
  have heI : (∫ x, F x*continuumLocalizedMode freq u x*continuumLocalizedMode freq v x)-
      (∫ x, F x*compactOrbitalDensity freq R u v x) =
      ∫ x, F x*orbitalRemainder freq R u x*continuumLocalizedMode freq v x := by
    simp_rw [he]
    rw [integral_sub hiuv hir]
    ring
  rw [heI]
  apply (sq_le_sq₀ (abs_nonneg _) (div_nonneg (mul_nonneg hC0 hB) (pow_nonneg hR0.le 12))).mp
  have hp := mul_le_mul hbr hbv
    (integral_nonneg (fun x => mul_nonneg (abs_nonneg (F x)) (sq_nonneg _)))
    (mul_nonneg hB (div_nonneg hT0 (pow_nonneg hR0.le 24)))
  apply hsq.trans (hp.trans ?_)
  have hTA : T*A ≤ C^2 := by dsimp [C]; nlinarith [sq_nonneg T,sq_nonneg A]
  calc
    (B*(T/R^24))*(B*A) = (T*A)*B^2/(R^12)^2 := by rw [← pow_mul]; norm_num; ring
    _ ≤ C^2*B^2/(R^12)^2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hTA (sq_nonneg B)) (sq_nonneg _)
    _ = (C*B/R^12)^2 := by ring

end ContinuumCoulomb

end

end OAI
