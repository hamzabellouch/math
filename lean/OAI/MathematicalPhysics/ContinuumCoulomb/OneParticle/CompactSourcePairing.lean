import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombSourceCubature
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.NuclearGridPotential

namespace OAI

/-! Fubini identities for nonnegative compact source densities and the
actual transported nuclear potential. No separation from a nuclear pole is
required for these identities. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem compact_source_transport_integrable {q : Position → ℝ}
    (hq : ContDiff ℝ 4 q) (hc : HasCompactSupport q) (hpos : ∀ y, 0 ≤ q y)
    {S : Set Position} (hS : IsCompact S) {G : Position → Position} (hG : Continuous G) :
    Integrable (fun p : Position × Position => q p.2*Coulomb.coulombKernel (p.2-G p.1))
      ((volume.restrict S).prod volume) := by
  have hm : Measurable (fun p : Position × Position => q p.2*Coulomb.coulombKernel (p.2-G p.1)) :=
    (hq.continuous.measurable.comp measurable_snd).mul
      (Coulomb.coulombKernel_measurable.comp (measurable_snd.sub (hG.measurable.comp measurable_fst)))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun x => compact_coulomb_eval_integrable hq.continuous hc (G x)),?_⟩
  have hi : IntegrableOn (fun x => NeutralAtom.potentialOf q (G x)) S :=
    ((compact_coulomb_C4 hq hc).continuous.comp hG).continuousOn.integrableOn_compact hS
  have he : (fun x => ∫ y, ‖q y*Coulomb.coulombKernel (y-G x)‖) =
      (fun x => NeutralAtom.potentialOf q (G x)) := by
    funext x
    rw [compact_coulomb_eval_eq]
    apply integral_congr_ae
    filter_upwards [] with y
    exact Real.norm_of_nonneg (mul_nonneg (hpos y) (Coulomb.coulombKernel_nonneg _))
  change Integrable (fun x => ∫ y, ‖q y*Coulomb.coulombKernel (y-G x)‖) (volume.restrict S)
  rw [he]
  exact hi

theorem compact_source_transport_pairing {q : Position → ℝ}
    (hq : ContDiff ℝ 4 q) (hc : HasCompactSupport q) (hpos : ∀ y, 0 ≤ q y)
    {S : Set Position} (hS : IsCompact S) {G : Position → Position} (hG : Continuous G) :
    (∫ x in S, NeutralAtom.potentialOf q (G x)) =
      ∫ y, q y*(∫ x in S, Coulomb.coulombKernel (y-G x)) := by
  have hi := compact_source_transport_integrable hq hc hpos hS hG
  simp_rw [compact_coulomb_eval_eq]
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards [] with y
  exact integral_const_mul _ _

theorem gridNuclearPotential_pairing {q : Position → ℝ}
    (hq : Continuous q) (hc : HasCompactSupport q)
    {ι : Type*} [Fintype ι] (index : ι → Fin 3 → ℤ)
    (G : Position → Position) (rho h : ℝ) :
    (∫ y, gridNuclearPotential index G rho h y*q y) =
      -rho*∑ i, positionCellGauss (gaussCellCenter h (index i)) h
        (fun x => NeutralAtom.potentialOf q (G x)) := by
  have hi (a : ι × (Fin 3 → Fin 2)) : Integrable (fun y =>
      Coulomb.coulombKernel (y-G (gaussLatticePoint h (gridGaussIndex index a)))*q y) := by
    convert compact_coulomb_eval_integrable hq hc (G (gaussLatticePoint h (gridGaussIndex index a))) using 1
    funext y
    ring
  calc
    _ = -(rho*h^3/8)*∑ a : ι × (Fin 3 → Fin 2),
        NeutralAtom.potentialOf q (G (gaussLatticePoint h (gridGaussIndex index a))) := by
      simp only [gridNuclearPotential,mul_assoc,Finset.sum_mul]
      rw [integral_const_mul,integral_finsetSum Finset.univ (fun a _ => hi a)]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      rw [compact_coulomb_eval_eq]
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = _ := by
      simp only [gaussCell_quadrature_lattice,Fintype.sum_prod_type,gridGaussIndex,← Finset.mul_sum]
      ring

end ContinuumCoulomb

end

end OAI
