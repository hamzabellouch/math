import OAI.GroupTheory.PolycyclicRecognition.Geometry.HeightKernelRecognition
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RecognitionFromHeight

namespace OAI

/-! # Corrected-height recognition without the KMN input -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory ThompsonNonamenability
open scoped IsMulCommutative

instance height_quotient_commutative
    {G W : Type} [Group G] [AddCommGroup W] (τ : G →* Multiplicative W) :
    IsMulCommutative (G ⧸ τ.ker) := by
  let f : (G ⧸ τ.ker) →* Multiplicative W :=
    τ.range.subtype.comp (QuotientGroup.quotientKerEquivRange τ).toMonoidHom
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (QuotientGroup.quotientKerEquivRange τ).injective
  exact ⟨⟨fun a b => hf (by simp only [map_mul, mul_comm])⟩⟩

theorem height_quotient_finiteDimension
    {G W : Type} [Group G] [Group.FG G]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (τ : G →* Multiplicative W) :
    HasFiniteIntegralCohomologicalDimension (G ⧸ τ.ker) := by
  let f : (G ⧸ τ.ker) →* Multiplicative W :=
    τ.range.subtype.comp (QuotientGroup.quotientKerEquivRange τ).toMonoidHom
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (QuotientGroup.quotientKerEquivRange τ).injective
  let : IsAddTorsionFree W := IsAddTorsionFree.of_isTorsionFree ℝ W
  have ht : HasNoNontrivialTorsion (Multiplicative W) := by
    intro a n hn ha
    exact (pow_left_injective hn) (ha.trans (one_pow n).symm)
  obtain ⟨n, hn⟩ := nilpotent_poincareDuality_of_finitelyGenerated_torsionFree
    (ht.of_injective f hf)
  exact hn.finiteCohomologicalDimension _

theorem virtuallyPolycyclic_of_corrected_height_proved
    {P G X W : Type} [Group P] [Group G] [Group.FG P] [Group.FG G]
    [MetricSpace G] [IsIsometricSMul G G] [PseudoMetricSpace X] [DecidableEq X]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : GroupCoarseEquivalence P G) (hP : IsVirtuallyPolycyclic P)
    (M : InvariantMean G)
    (H : Subgroup G) [H.FiniteIndex] (τ : H →* Multiplicative W)
    (gromov : ∀ (J : Subgroup τ.ker) [DecidableEq J], GromovPolynomialGrowthInput J)
    (f : G → X) (π : X → W) (packing : PolynomialBoundedChainPacking π)
    (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : G) R).Finite)
    {K C K' C' D : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hK' : 0 ≤ K') (hD : 0 ≤ D)
    (hupper : ∀ x y, dist (f x) (f y) ≤ K * dist x y + C)
    (hlower : ∀ x y, dist x y ≤ K' * dist (f x) (f y) + C')
    (hheight : ∀ h : H, ‖(τ h).toAdd - π (f h)‖ ≤ D) :
    IsVirtuallyPolycyclic G := by
  classical
  obtain ⟨K₀, Γ, _, _, hΓ, ⟨eΓ⟩, n, hΓPD⟩ :=
    exists_coarse_poincareDuality_comparison_proved P G hP e
  let := hΓ
  have hG : TypeFPInfinity G :=
    fun i => liFinitenessInput Γ G eΓ i (hΓPD.typeFPInfinity Γ i)
  have hH : TypeFPInfinity H := fun i => (hG i).finiteIndex_subgroup H
  have hlocal : ∀ J : Subgroup H, J ≤ τ.ker → J.FG → Group.IsVirtuallyNilpotent J := by
    intro J hJ hfg
    let A := J.subgroupOf τ.ker
    let j := Subgroup.subgroupOfEquivOfLe hJ
    let : Group.FG A := @Group.fg_of_surjective _ _ _ _
      ((Group.fg_iff_subgroup_fg J).mpr hfg) j.symm.toMonoidHom j.symm.surjective
    let ι : A →* G := H.subtype.comp (τ.ker.subtype.comp A.subtype)
    have hι : Function.Injective ι :=
      Subtype.val_injective.comp (Subtype.val_injective.comp Subtype.val_injective)
    have hA : Group.IsVirtuallyNilpotent A := by
      apply virtuallyNilpotent_of_injective_boundedHeight (gromov A) ι hι f π packing
        hfinite hK hC hK' hD hupper hlower
      intro a
      have he := hheight a.val.val
      rw [a.val.property] at he
      change ‖(0 : W) - π (f (ι a))‖ ≤ D at he
      simpa only [zero_sub, norm_neg] using he
    exact virtuallyNilpotent_of_mulEquiv j hA
  have hpoly : IsVirtuallyPolycyclic H := hH.heightKernel_virtuallyPolycyclic
    (e.trans (finiteIndexCoarseEquivalence H).symm) hP (subgroupInvariantMean M H)
    τ.ker (height_quotient_finiteDimension τ) hlocal
  obtain ⟨V, hVi, hVpoly⟩ := hpoly
  let := hVi
  exact ⟨V.map H.subtype, ⟨by
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero hVi.index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := H))⟩,
    hVpoly.of_surjective (V.equivMapOfInjective H.subtype Subtype.val_injective).toMonoidHom
      (V.equivMapOfInjective H.subtype Subtype.val_injective).surjective⟩

end PolycyclicRecognition

end

end OAI
