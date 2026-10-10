import OAI.MeasureTheory.Falconer.Estimates.DescriptorMaskExceptional
import OAI.MeasureTheory.Falconer.Measures.ClassSupport
import OAI.MeasureTheory.Falconer.Radial.RadialSphereLaw

namespace OAI

/-! # Integrating a mask failure against the original opposite marginal -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor)
variable {d : ℕ}

noncomputable def descriptorFiberBad (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J : ℕ)
    (b : PolicyDescriptor) (S : Finset (Sphere d)) (G : Set (Space d × Space d)) :
    Set (Space d × Space d) :=
  G ∩ {z | descriptorMask Q ρ profile N σ J 0 b S z.1 (normalizeToSphere w₀ (z.2-z.1)) ≠ 1}

 theorem descriptorFiberBad_measurable (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J : ℕ)
    (b : PolicyDescriptor) (S : Finset (Sphere d))
    {G : Set (Space d × Space d)} (hG : MeasurableSet G) :
    MeasurableSet (descriptorFiberBad w₀ Q ρ profile N σ J b S G) := by
  apply hG.inter
  exact (measurableSet_eq_fun
    ((descriptorMask_measurable Q ρ profile N σ J 0 b S).comp
      (measurable_fst.prodMk ((normalizeToSphere_measurable w₀).comp
        (measurable_snd.sub measurable_fst)))) measurable_const).compl

namespace Regularization

 theorem uniform_source_mask_bad_mass {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (μ : Measure (Space d)) [IsProbabilityMeasure μ], ∀ B : ℕ,
      0 < B → (B:ℝ) ≤ σ*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^σ →
      ∀ p₀ ∈ regularizationLeaves Q μ N, ∀ b : PolicyDescriptor, descriptorValid N b →
      ∀ S : Finset (Sphere d),
        (∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ descriptorMaskRadius N σ b/2) →
      ∀ (ν : Measure (Space d)) [IsProbabilityMeasure ν], ∀ w₀ : Sphere d,
      ∀ G : Set (Space d × Space d), MeasurableSet G →
      (∀ᵐ x ∂sourceClass Q μ N B p₀, ∀ u : Space d, ∀ r : ℝ,
        ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
        originalRadialSphereLaw w₀ ν G x {w : Sphere d | dist (w:Space d) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^σ*r^((d:ℝ)/2))) →
      ((sourceClass Q μ N B p₀).prod ν)
        (descriptorFiberBad w₀ Q (sourceClass Q μ N B p₀)
          (fun u => sourceUnitProfile Q μ N B p₀ (u/N)) N σ J b S G) ≤
        ENNReal.ofReal (((2:ℝ)^N)^(-σ)) := by
  obtain ⟨N₀,h₀⟩ := uniform_descriptor_mask_exceptional (d := d) hσ hJ
  refine ⟨N₀,?_⟩
  intro N hN Q hQ μ _ B hB hwidth hlarge p₀ hp₀ b hb S hS ν _ w₀ G hG hcap
  let ρ := sourceClass Q μ N B p₀
  let profile := fun u => sourceUnitProfile Q μ N B p₀ (u/N)
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  let : IsProbabilityMeasure ρ := regularization_class_probability Q hside μ N B hp₀
  have hcarry : ∀ᵐ x ∂ρ, x ∈ Q.carrier := ae_iff.mpr (sourceClass_parent Q hside μ N B p₀)
  have hmass : ∀ᵐ x ∂ρ,
      ν {y | (x,y) ∈ descriptorFiberBad w₀ Q ρ profile N σ J b S G} ≤
        ENNReal.ofReal (((2:ℝ)^N)^(-σ)) := by
    filter_upwards [hcap,hcarry,ae_occupied_anchors Q ρ] with x hcx hx hocc
    obtain ⟨P,hP,hxp⟩ := Q.mem_descendant_at_depth (PlanarFalconer.descriptorAnchor b) hx
    have hlen := (mem_cubePaths _ _ _).mp hP
    let V := originalRadialSphereLaw w₀ ν G x
    have hv : V univ ≤ 1 := (originalRadialSphereLaw_mass_le w₀ ν G x).trans (by simp)
    have hh := h₀ N hN Q hQ μ B hB hwidth hlarge p₀ hp₀ b hb P hlen
      (hocc P hxp) V hv hcx S hS x hxp
    rw [originalRadialSphereLaw_apply w₀ ν G x _] at hh
    · exact hh
    · exact (measurableSet_eq_fun
        ((descriptorMask_measurable Q ρ profile N σ J 0 b S).comp
          (measurable_const.prodMk measurable_id)) measurable_const).compl
  rw [Measure.prod_apply (descriptorFiberBad_measurable w₀ Q ρ profile N σ J b S hG)]
  exact (lintegral_mono_ae hmass).trans_eq (by rw [lintegral_const,measure_univ,mul_one])

end Regularization
end Falconer

end OAI
