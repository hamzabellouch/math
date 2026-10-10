import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedOrbitalGram

namespace OAI

/-! The actual uncut planar modes satisfy the finite-frame bound needed
when combining planar and transverse spectral estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

private theorem frame_bound_from_synthesis {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {m : ℕ} (v : Fin m → E) {C : ℝ} (hC : 0 ≤ C)
    (hsynth : ∀ d : Fin m → ℝ, ‖∑ i, d i • v i‖^2 ≤ C*∑ i, (d i)^2)
    (f : E) : ∑ i, (inner ℝ (v i) f)^2 ≤ C*‖f‖^2 := by
  let d : Fin m → ℝ := fun i => inner ℝ (v i) f
  let S : ℝ := ∑ i, (d i)^2
  let g : E := ∑ i, d i • v i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hg : ‖g‖^2 ≤ C*S := hsynth d
  have hpair : inner ℝ g f = S := by
    simp only [g, S, sum_inner, real_inner_smul_left, d, pow_two]
  have hcs : S^2 ≤ ‖g‖^2*‖f‖^2 := by
    rw [← hpair]
    simpa only [pow_two, real_inner_self_eq_norm_sq] using real_inner_mul_inner_self_le g f
  have hh : S^2 ≤ C*S*‖f‖^2 := hcs.trans
    (mul_le_mul_of_nonneg_right hg (sq_nonneg _))
  change S ≤ C*‖f‖^2
  rcases eq_or_lt_of_le hS with hs | hs
  · rw [← hs]
    exact mul_nonneg hC (sq_nonneg _)
  · nlinarith

def planarOrbitalL2 (u : PlanarPosition) : Lp ℝ 2 (volume : Measure PlanarPosition) :=
  (normalizedPlanarMode_memLp.comp_measurePreserving
    (measurePreserving_sub_right volume u)).toLp (fun r => normalizedPlanarMode (r-u))

theorem planarOrbitalL2_inner (u v : PlanarPosition) :
    inner ℝ (planarOrbitalL2 u) (planarOrbitalL2 v) = planarModeOverlap u v := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    (normalizedPlanarMode_memLp.comp_measurePreserving
      (measurePreserving_sub_right volume u)).coeFn_toLp,
    (normalizedPlanarMode_memLp.comp_measurePreserving
      (measurePreserving_sub_right volume v)).coeFn_toLp] with r hu hv
  change inner ℝ (planarOrbitalL2 u r) (planarOrbitalL2 v r) = _
  change planarOrbitalL2 u r = normalizedPlanarMode (r-u) at hu
  change planarOrbitalL2 v r = normalizedPlanarMode (r-v) at hv
  rw [hu,hv, RCLike.inner_apply, conj_trivial]
  exact mul_comm _ _

theorem planarOrbitalL2_frame_bound {D : ℝ} {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (f : Lp ℝ 2 (volume : Measure PlanarPosition)) :
    ∑ i, (inner ℝ (planarOrbitalL2 (u i)) f)^2 ≤
      (1+m*localizedOverlapBound D)*‖f‖^2 := by
  apply frame_bound_from_synthesis (fun i => planarOrbitalL2 (u i))
    (by have h := localizedOverlapBound_nonnegative D; positivity)
  intro d
  have he : ‖∑ i, d i • planarOrbitalL2 (u i)‖^2 =
      ∑ i, ∑ j, planarModeOverlap (u i) (u j)*d i*d j := by
    rw [← real_inner_self_eq_norm_sq]
    simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
      planarOrbitalL2_inner]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact dualMatrix_quadratic_upper _ (localizedOverlapBound_nonnegative D)
    (fun i => (planarModeOverlap_diagonal (u i)).le) (planarModeOverlap_offsite u hsep) d

/-- Integral form, usable on almost-everywhere L2 slices. -/
theorem planar_modes_frame_bound {D : ℝ} {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (f : PlanarPosition → ℝ) (hf : MemLp f 2) :
    ∑ i, (∫ r, f r*normalizedPlanarMode (r-u i))^2 ≤
      (1+m*localizedOverlapBound D)*(∫ r, f r^2) := by
  have h := planarOrbitalL2_frame_bound u hsep (hf.toLp f)
  have hi (i : Fin m) : inner ℝ (planarOrbitalL2 (u i)) (hf.toLp f) =
      ∫ r, f r*normalizedPlanarMode (r-u i) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,
      (normalizedPlanarMode_memLp.comp_measurePreserving
        (measurePreserving_sub_right volume (u i))).coeFn_toLp] with r hfr hmr
    change inner ℝ (planarOrbitalL2 (u i) r) (hf.toLp f r) = _
    change planarOrbitalL2 (u i) r = normalizedPlanarMode (r-u i) at hmr
    rw [hfr, hmr, RCLike.inner_apply, conj_trivial]
  have hn : ‖hf.toLp f‖^2 = ∫ r, f r^2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with r hr
    rw [hr, RCLike.inner_apply, conj_trivial]
    ring
  simpa only [hi, hn] using h

end ContinuumCoulomb

end

end OAI
