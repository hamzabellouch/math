import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.PairTensorCompression
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.WeightedSpinOrbitals

namespace OAI

/-! Spin selection rules for the actual Coulomb four-index integral. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def realPairIntegrand (f g h k : Position → ℝ) (σ τ κ χ : Fin 2)
    (z : (Fin 2 × (Fin 3 → ℝ)) × (Fin 2 × (Fin 3 → ℝ))) : ℂ :=
  flatPairCoulomb z.1 z.2*
    ((star (Coulomb.flatSpinOrbital (realSpinOrbital f σ) z.1)*
      Coulomb.flatSpinOrbital (realSpinOrbital h κ) z.1)*
    (star (Coulomb.flatSpinOrbital (realSpinOrbital g τ) z.2)*
      Coulomb.flatSpinOrbital (realSpinOrbital k χ) z.2))

private theorem realPairIntegrand_eq (f g h k : Position → ℝ) (σ τ κ χ s t : Fin 2)
    (x y : Fin 3 → ℝ) : realPairIntegrand f g h k σ τ κ χ ((s,x),(t,y)) =
      if s=σ ∧ s=κ ∧ t=τ ∧ t=χ then
        ((Coulomb.coulombKernel (WithLp.toLp 2 x-WithLp.toLp 2 y)*
          ((f (WithLp.toLp 2 x)*h (WithLp.toLp 2 x))*
            (g (WithLp.toLp 2 y)*k (WithLp.toLp 2 y))):ℝ):ℂ) else 0 := by
  by_cases h₁ : s=σ <;> by_cases h₂ : s=κ <;> by_cases h₃ : t=τ <;> by_cases h₄ : t=χ <;>
    simp_all [realPairIntegrand,flatPairCoulomb,Coulomb.flatSpinOrbital,realSpinOrbital,
      Complex.ofReal_mul]

private theorem realPairIntegrand_section_integrable (f g h k : Position → ℝ)
    (hI : Integrable (fun z : Position × Position => Coulomb.coulombKernel (z.1-z.2)*
      ((f z.1*h z.1)*(g z.2*k z.2))) (volume.prod volume)) (σ τ κ χ : Fin 2)
    (st : Fin 2 × Fin 2) :
    Integrable (fun z : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      realPairIntegrand f g h k σ τ κ χ ((st.1,z.1),(st.2,z.2))) (volume.prod volume) := by
  simp_rw [realPairIntegrand_eq]
  split_ifs
  · have hm : MeasurePreserving
        ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).prodCongr
          (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))) (volume.prod volume) (volume.prod volume) :=
      (PiLp.volume_preserving_toLp (Fin 3)).prod (PiLp.volume_preserving_toLp (Fin 3))
    exact hm.integrable_comp_of_integrable hI.ofReal
  · exact integrable_zero _ _ _

private theorem realPairIntegrand_regroup_integrable (f g h k : Position → ℝ)
    (hI : Integrable (fun z : Position × Position => Coulomb.coulombKernel (z.1-z.2)*
      ((f z.1*h z.1)*(g z.2*k z.2))) (volume.prod volume)) (σ τ κ χ : Fin 2) :
    Integrable (fun z : (Fin 2 × Fin 2) × ((Fin 3 → ℝ) × (Fin 3 → ℝ)) =>
      realPairIntegrand f g h k σ τ κ χ ((z.1.1,z.2.1),(z.1.2,z.2.2)))
      (Measure.count.prod (volume.prod volume)) :=
  Coulomb.integrable_finite_count_prod _ (realPairIntegrand_section_integrable f g h k hI σ τ κ χ)

theorem realSpin_coulomb_integrable (f g h k : Position → ℝ)
    (hI : Integrable (fun z : Position × Position => Coulomb.coulombKernel (z.1-z.2)*
      ((f z.1*h z.1)*(g z.2*k z.2))) (volume.prod volume)) (σ τ κ χ : Fin 2) :
    Integrable (realPairIntegrand f g h k σ τ κ χ)
      (Coulomb.spinSpaceMeasure.prod Coulomb.spinSpaceMeasure) := by
  have hm := Coulomb.pairRegroup_measurePreserving
    (Measure.count : Measure (Fin 2)) (volume : Measure (Fin 3 → ℝ))
    (Measure.count : Measure (Fin 2)) (volume : Measure (Fin 3 → ℝ))
  rw [Coulomb.count_prod_count] at hm
  exact hm.integrable_comp_of_integrable
    (realPairIntegrand_regroup_integrable f g h k hI σ τ κ χ)

theorem realSpin_coulomb_integral (f g h k : Position → ℝ)
    (hI : Integrable (fun z : Position × Position => Coulomb.coulombKernel (z.1-z.2)*
      ((f z.1*h z.1)*(g z.2*k z.2))) (volume.prod volume)) (σ τ κ χ : Fin 2) :
    (∫ z, realPairIntegrand f g h k σ τ κ χ z
      ∂(Coulomb.spinSpaceMeasure.prod Coulomb.spinSpaceMeasure)) =
      if σ=κ ∧ τ=χ then
        ((∫ z : Position × Position, Coulomb.coulombKernel (z.1-z.2)*
          ((f z.1*h z.1)*(g z.2*k z.2)) ∂(volume.prod volume):ℝ):ℂ) else 0 := by
  have hm := Coulomb.pairRegroup_measurePreserving
    (Measure.count : Measure (Fin 2)) (volume : Measure (Fin 3 → ℝ))
    (Measure.count : Measure (Fin 2)) (volume : Measure (Fin 3 → ℝ))
  rw [Coulomb.count_prod_count] at hm
  let F (z : (Fin 2 × Fin 2) × ((Fin 3 → ℝ) × (Fin 3 → ℝ))) :=
    realPairIntegrand f g h k σ τ κ χ ((z.1.1,z.2.1),(z.1.2,z.2.2))
  have he := hm.integral_comp' F
  change (∫ z, realPairIntegrand f g h k σ τ κ χ z
    ∂(Coulomb.spinSpaceMeasure.prod Coulomb.spinSpaceMeasure)) = _ at he
  rw [he,Coulomb.integral_finite_count_prod F
    (realPairIntegrand_section_integrable f g h k hI σ τ κ χ)]
  have hp : MeasurePreserving
      ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).prodCongr
        (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))) (volume.prod volume) (volume.prod volume) :=
    (PiLp.volume_preserving_toLp (Fin 3)).prod (PiLp.volume_preserving_toLp (Fin 3))
  have hsection (s t : Fin 2) :
      (∫ z : (Fin 3 → ℝ) × (Fin 3 → ℝ),
        realPairIntegrand f g h k σ τ κ χ ((s,z.1),(t,z.2)) ∂(volume.prod volume)) =
      if s=σ ∧ s=κ ∧ t=τ ∧ t=χ then
        ((∫ z : Position × Position, Coulomb.coulombKernel (z.1-z.2)*
          ((f z.1*h z.1)*(g z.2*k z.2)) ∂(volume.prod volume):ℝ):ℂ) else 0 := by
    simp_rw [realPairIntegrand_eq]
    split_ifs
    · exact (hp.integral_comp' (fun z : Position × Position =>
        Complex.ofReal (Coulomb.coulombKernel (z.1-z.2)*((f z.1*h z.1)*(g z.2*k z.2))))).trans
          integral_complex_ofReal
    · simp only [integral_zero]
  dsimp only [F]
  simp only [Fintype.sum_prod_type,hsection]
  fin_cases σ <;> fin_cases τ <;> fin_cases κ <;> fin_cases χ <;> norm_num

end ContinuumCoulomb

end

end OAI
