import OAI.Geometry.RCD.Harmonic.BoundedHarmonicNorm
import OAI.Geometry.RCD.Coordinates.LocalConstantRepresentative
import OAI.Geometry.RCD.Harmonic.LocalConstantHarmonic

namespace OAI

/-! # Actual centered and physically rescaled harmonic directions -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.centered_harmonic_direction_with_energy {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X) {R r M : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hM : 0 ≤ M)
    (u : SobolevSpace (hausdorff n X) hX.quadratic) (v : X → ℝ) (c : ℝ)
    (hu : IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p R) u)
    (hrep : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[
      (hausdorff n X).restrict (ball p R)] v)
    (hb : ∀ x ∈ ball p R, |v x-c| ≤ M*r) :
    ∃ w : SobolevSpace (hausdorff n X) hX.quadratic,
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p R) w ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic w =ᵐ[
        (hausdorff n X).restrict (ball p R)] (fun x => (v x-c)/r) ∧
      harmonicTargetNorm hX p R w ≤ M ∧
      ∀ q : SobolevSpace (hausdorff n X) hX.quadratic,
        localGamma (hausdorff n X) hX.quadratic w q =ᵐ[(hausdorff n X).restrict (ball p R)]
          fun x => r⁻¹*localGamma (hausdorff n X) hX.quadratic u q x := by
  let μ := hausdorff n X
  obtain ⟨d,_,hd⟩ := hX.local_constant_representative hn p R c
  let w := r⁻¹ • (u-d)
  have hdH := isSobolevHarmonicOn_of_local_constant μ hX.quadratic
    (ball p R) measurableSet_ball d c hd
  have hsub : IsSobolevHarmonicOn μ hX.quadratic (ball p R) (u-d) := by
    simpa only [neg_one_smul,sub_eq_add_neg] using
      hu.add μ hX.quadratic (hdH.smul μ hX.quadratic (-1))
  have hw : IsSobolevHarmonicOn μ hX.quadratic (ball p R) w :=
    hsub.smul μ hX.quadratic r⁻¹
  have hwrep : SobolevSpace.toLp μ hX.quadratic w =ᵐ[μ.restrict (ball p R)]
      (fun x => (v x-c)/r) := by
    have he : SobolevSpace.toLp μ hX.quadratic w =ᵐ[μ]
        fun x => r⁻¹*(SobolevSpace.toLp μ hX.quadratic u x-SobolevSpace.toLp μ hX.quadratic d x) := by
      dsimp only [w]
      rw [map_smul,map_sub]
      filter_upwards [Lp.coeFn_smul r⁻¹ (SobolevSpace.toLp μ hX.quadratic u-SobolevSpace.toLp μ hX.quadratic d),
        Lp.coeFn_sub (SobolevSpace.toLp μ hX.quadratic u) (SobolevSpace.toLp μ hX.quadratic d)]
        with x hs hx
      simp only [Pi.smul_apply,smul_eq_mul] at hs
      rw [hs,hx]
      rfl
    filter_upwards [ae_restrict_of_ae he,hrep,hd] with x hx hu hd
    rw [hx,hu,hd,div_eq_inv_mul]
  refine ⟨w,hw,hwrep,hX.harmonicTargetNorm_le_of_bound p hR hM w ?_,?_⟩
  · filter_upwards [hwrep,ae_restrict_mem measurableSet_ball] with x hx hball
    rw [hx,abs_div,abs_of_pos hr]
    exact (div_le_iff₀ hr).mpr (hb x hball)
  · intro q
    filter_upwards [hd,
      ae_restrict_of_ae (localGamma_smul_left μ hX.quadratic r⁻¹ (u-d) q),
      ae_restrict_of_ae (localGamma_sub_left μ hX.quadratic u d q),
      ae_restrict_of_ae (localGamma_zero_on_level μ hX.quadratic d q c)] with x hx hs hdq hz
    change localGamma μ hX.quadratic (r⁻¹ • (u-d)) q x = _
    rw [hs,hdq,hz hx,sub_zero]

theorem NoncollapsedRCD.centered_harmonic_direction {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X) {R r M : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hM : 0 ≤ M)
    (u : SobolevSpace (hausdorff n X) hX.quadratic) (v : X → ℝ) (c : ℝ)
    (hu : IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p R) u)
    (hrep : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[
      (hausdorff n X).restrict (ball p R)] v)
    (hb : ∀ x ∈ ball p R, |v x-c| ≤ M*r) :
    ∃ w : SobolevSpace (hausdorff n X) hX.quadratic,
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p R) w ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic w =ᵐ[
        (hausdorff n X).restrict (ball p R)] (fun x => (v x-c)/r) ∧
      harmonicTargetNorm hX p R w ≤ M := by
  obtain ⟨w,hw,hrep,hnorm,_⟩ :=
    hX.centered_harmonic_direction_with_energy hn p hR hr hM u v c hu hrep hb
  exact ⟨w,hw,hrep,hnorm⟩

end RegularPointCoordinates

end

end OAI
