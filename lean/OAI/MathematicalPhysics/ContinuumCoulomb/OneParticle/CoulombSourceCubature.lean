import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CompactCoulombSmooth
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CubeIntegral
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombFarCell

namespace OAI

/-! A compact orbital source can be integrated before the nuclear cell rule.
On cells separated from its support, the inverse-fifth-power error survives
integration with only the source's L1 mass as a factor. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem compact_coulomb_integrable {q : Position → ℝ} (hq : Continuous q)
    (hc : HasCompactSupport q) (y : Position) :
    Integrable (fun x => NeutralAtom.coulombKernel (y-x)*q x) := by
  have hi := hc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
    NeutralAtom.locallyIntegrable_coulombKernel hq y
  change Integrable (fun x => NeutralAtom.coulombKernel x*q (y-x)) at hi
  simpa only [sub_sub_cancel] using hi.comp_sub_left y

theorem compact_coulomb_eval_eq (q : Position → ℝ) (y : Position) :
    NeutralAtom.potentialOf q y = ∫ x, q x*Coulomb.coulombKernel (x-y) := by
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [NeutralAtom.coulombKernel,Coulomb.coulombKernel,norm_sub_rev,mul_comm]

theorem compact_coulomb_eval_integrable {q : Position → ℝ} (hq : Continuous q)
    (hc : HasCompactSupport q) (y : Position) :
    Integrable (fun x => q x*Coulomb.coulombKernel (x-y)) := by
  convert compact_coulomb_integrable hq hc y using 1
  funext x
  simp only [NeutralAtom.coulombKernel,Coulomb.coulombKernel,norm_sub_rev,mul_comm]

theorem compact_coulomb_cell_gauss {q : Position → ℝ} (hq : Continuous q)
    (hc : HasCompactSupport q) (b : Position) (h : ℝ) :
    positionCellGauss b h (NeutralAtom.potentialOf q) =
      ∫ x, q x*positionCellGauss b h (fun y => Coulomb.coulombKernel (x-y)) := by
  simp only [positionCellGauss_eq_node_sum,compact_coulomb_eval_eq]
  rw [← integral_finsetSum Finset.univ (fun v _ => compact_coulomb_eval_integrable hq hc _),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← Finset.mul_sum]
  ring

theorem compact_coulomb_cell_integral {q : Position → ℝ}
    (hq : ContDiff ℝ 4 q) (hc : HasCompactSupport q) (b : Position)
    {h r : ℝ} (hh : 0 ≤ h) (hr : 0 < r)
    (hsep : ∀ x, q x ≠ 0 → ∀ y ∈ positionCube b h, r ≤ ‖y-x‖) :
    Integrable (fun x => q x * positionCellIntegral b h (fun y => Coulomb.coulombKernel (x-y))) ∧
    positionCellIntegral b h (NeutralAtom.potentialOf q) =
      ∫ x, q x * positionCellIntegral b h (fun y => Coulomb.coulombKernel (x-y)) := by
  have hvol : IntegrableOn (fun _ : Position => (1:ℝ)) (positionCube b h) :=
    integrableOn_const ((positionCube_isCompact b hh).measure_lt_top (μ := volume)).ne
  have hqI : Integrable q := hq.continuous.integrable_of_hasCompactSupport hc
  have hmajor := (hqI.norm.mul_prod hvol).const_mul r⁻¹
  have hi : Integrable (fun p : Position × Position =>
      q p.1 * NeutralAtom.coulombKernel (p.2-p.1))
      (volume.prod (volume.restrict (positionCube b h))) := by
    apply hmajor.mono' (by
      exact (hq.continuous.measurable.comp measurable_fst |>.mul
        (NeutralAtom.measurable_coulombKernel.comp (measurable_snd.sub measurable_fst))).aestronglyMeasurable)
    have hp : ∀ᵐ p : Position × Position ∂(volume.prod (volume.restrict (positionCube b h))), p.2 ∈ positionCube b h :=
      (Measure.ae_prod_iff_ae_ae ((positionCube_isClosed b h).measurableSet.preimage measurable_snd)).mpr
        (Filter.Eventually.of_forall (fun _ => ae_restrict_mem (positionCube_isClosed b h).measurableSet))
    filter_upwards [hp] with p hp
    change ‖q p.1 * NeutralAtom.coulombKernel (p.2-p.1)‖ ≤ r⁻¹*(‖q p.1‖*1)
    by_cases hq0 : q p.1 = 0
    · simp [hq0]
    have hd := hsep p.1 hq0 p.2 hp
    rw [norm_mul,Real.norm_of_nonneg (NeutralAtom.coulombKernel_nonneg _),mul_one]
    have hk : NeutralAtom.coulombKernel (p.2-p.1) ≤ r⁻¹ :=
      inv_anti₀ hr hd
    exact (mul_le_mul_of_nonneg_left hk (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hinner (x : Position) :
      (∫ y in positionCube b h, q x*NeutralAtom.coulombKernel (y-x)) =
        q x*positionCellIntegral b h (fun y => Coulomb.coulombKernel (x-y)) := by
    rw [integral_const_mul]
    by_cases hqx : q x = 0
    · simp [hqx]
    have hk : IntegrableOn (fun y => Coulomb.coulombKernel (x-y)) (positionCube b h) := by
      apply (hvol.const_mul r⁻¹).mono' (by
        exact (Coulomb.coulombKernel_measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
      filter_upwards [ae_restrict_mem (positionCube_isClosed b h).measurableSet] with y hy
      change ‖Coulomb.coulombKernel (x-y)‖ ≤ r⁻¹*1
      rw [Real.norm_of_nonneg (Coulomb.coulombKernel_nonneg _),mul_one]
      apply inv_anti₀ hr
      simpa only [norm_sub_rev] using hsep x hqx y hy
    rw [positionCellIntegral_eq_setIntegral b hh _ hk]
    congr 1
    apply setIntegral_congr_fun (positionCube_isClosed b h).measurableSet
    intro y _
    simp only [NeutralAtom.coulombKernel,Coulomb.coulombKernel,norm_sub_rev]
  refine ⟨?_,?_⟩
  · exact hi.integral_prod_left.congr (Filter.Eventually.of_forall hinner)
  · rw [positionCellIntegral_eq_setIntegral b hh _
      ((compact_coulomb_C4 hq hc).continuous.continuousOn.integrableOn_compact
        (positionCube_isCompact b hh))]
    change (∫ y in positionCube b h, ∫ x, NeutralAtom.coulombKernel (y-x)*q x) = _
    simp_rw [mul_comm (NeutralAtom.coulombKernel _) (q _)]
    rw [← integral_integral_swap hi]
    exact integral_congr_ae (Filter.Eventually.of_forall hinner)

theorem compact_coulomb_cell_gauss_integrable {q : Position → ℝ} (hq : Continuous q)
    (hc : HasCompactSupport q) (b : Position) (h : ℝ) :
    Integrable (fun x => q x*positionCellGauss b h (fun y => Coulomb.coulombKernel (x-y))) := by
  have hi := (integrable_finsetSum Finset.univ (fun (v : Fin 3 → Fin 2) _ =>
    compact_coulomb_eval_integrable hq hc
      (cubePoint b (h/2) (gaussNode (v 0)) (gaussNode (v 1)) (gaussNode (v 2))))).const_mul (h^3/8)
  convert hi using 1
  funext x
  rw [positionCellGauss_eq_node_sum,← Finset.mul_sum]
  ring

theorem compact_coulomb_far_cell_error :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (q : Position → ℝ), ContDiff ℝ 4 q → HasCompactSupport q →
      ∀ (b : Position) (h r : ℝ), 0 ≤ h → 0 < r →
      (∀ x, q x ≠ 0 → ∀ y ∈ positionCube b h, r ≤ ‖y-x‖) →
      |positionCellGauss b h (NeutralAtom.potentialOf q)-
        positionCellIntegral b h (NeutralAtom.potentialOf q)| ≤
        (C*h^7/r^5)*(∫ x, ‖q x‖) := by
  obtain ⟨C,hC,herror⟩ := coulomb_far_cell_error
  refine ⟨C,hC,fun q hq hc b h r hh hr hsep => ?_⟩
  have hI := compact_coulomb_cell_integral hq hc b hh hr hsep
  have hQ := compact_coulomb_cell_gauss_integrable hq.continuous hc b h
  rw [compact_coulomb_cell_gauss hq.continuous hc,hI.2,← integral_sub hQ hI.1]
  have hb := norm_integral_le_of_norm_le
    (((hq.continuous.integrable_of_hasCompactSupport hc : Integrable q).norm).mul_const (C*h^7/r^5))
    (Filter.Eventually.of_forall (fun x => show
      ‖q x*positionCellGauss b h (fun y => Coulomb.coulombKernel (x-y))-
        q x*positionCellIntegral b h (fun y => Coulomb.coulombKernel (x-y))‖ ≤
        ‖q x‖*(C*h^7/r^5) from by
      by_cases hx : q x = 0
      · simp only [hx,zero_mul,sub_self,norm_zero,le_refl]
      rw [← mul_sub,norm_mul,Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply herror x b h r hh hr
      intro a ha d hd e he
      simpa only [norm_sub_rev] using hsep x hx
        (cubePoint b (h/2) a d e) (cubePoint_mem_positionCube b hh ha hd he)))
  simpa only [Real.norm_eq_abs,integral_mul_const,mul_comm] using hb

end ContinuumCoulomb

end

end OAI
