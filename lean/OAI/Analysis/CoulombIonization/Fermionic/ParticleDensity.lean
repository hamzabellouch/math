import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.WeakDerivativeSmulL2
import OAI.Analysis.CoulombIonization.FormDomain.GradientVector

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombAtom.Pauli
open CoulombPauli CoulombPackets CoulombLT

def oneParticleDensity {N : ℕ} (ψ : FormVector (N+1))
    (hψ : ∀ s, MemLp (ψ.value s) 2) : Space → ℝ≥0∞ :=
  fermionDensity (toMany ψ hψ)

theorem form_lieb_thirring {N : ℕ} (ψ : FormVector (N+1))
    (hψ : FormAdmissible ψ) :
    (∫⁻ x, oneParticleDensity ψ hψ.1 x ^ (5/3:ℝ)) ≤
      ENNReal.ofReal (32*(N+1:ℝ) + (2048/3:ℝ)*
        (∑ s : Spins (N+1), ∑ i : Fin (N+1), ∑ a : Fin 3,
          ∫ x : Configuration (N+1), ‖ψ.gradient s i a x‖^2)) := by
  have hn : ‖toMany ψ hψ.1‖^2 = 1 :=
    (toMany_norm_sq ψ hψ.1).trans hψ.2.2.2.2.1
  have ha (i j : Fin (N+1)) (hij : i ≠ j) :
      permute (Equiv.swap i j) (toMany ψ hψ.1) = -toMany ψ hψ.1 := by
    rw [toMany_permute ψ hψ.1 (Equiv.swap i j) (hψ.2.2.2.1 _)]
    simp [Equiv.Perm.sign_swap hij]
  have hw (i : Fin (N+1)) (a : Fin 3) := form_hasFermionGradient ψ hψ i a
  simp only [EuclideanSpace.basisFun_apply] at hw
  have h := fermion_lieb_thirring (toMany ψ hψ.1) (gradientMany ψ hψ) hw hn ha
  simp only [gradientMany_norm_sq] at h
  have hs : (∑ s : Spins (N+1), ∑ i : Fin (N+1), ∑ a : Fin 3,
      ∫ x : Configuration (N+1), ‖ψ.gradient s i a x‖^2) =
      ∑ i : Fin (N+1), ∑ a : Fin 3, ∑ s : Spins (N+1),
        ∫ x : Configuration (N+1), ‖ψ.gradient s i a x‖^2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
  simpa only [oneParticleDensity,hs] using h
end CoulombAtom.Pauli

namespace CoulombLT
open CoulombPauli CoulombPackets
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma coordinateDensity_aemeasurable {N : ℕ}
    (ψ : fermionL2 (V := V) (N+1)) (i : Fin (N+1)) :
    AEMeasurable (fun x => ∑ s : Fin 2, ∫⁻ y,
      ENNReal.ofReal (‖splitFermion i ψ ((x,s),y)‖^2)
        ∂(configMeasure N (spinSpaceMeasure (V := V)))) volume := by
  have hm := ((Lp.memLp (splitFermion i ψ)).aestronglyMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal
  have h1 := hm.lintegral_prod_right'
  have h2 := h1.lintegral_prod_right'
  simpa only [lintegral_fintype,Measure.count_singleton,mul_one,Pi.pow_apply] using h2

lemma fermionDensity_aemeasurable {N : ℕ} (ψ : fermionL2 (V := V) (N+1)) :
    AEMeasurable (fermionDensity ψ) volume := by
  exact Finset.aemeasurable_fun_sum Finset.univ (fun i _ => coordinateDensity_aemeasurable ψ i)

lemma coordinate_density_weighted {N : ℕ} (ψ : fermionL2 (V := V) (N+1))
    (i : Fin (N+1)) (w : V → ℝ) (hw : Measurable w) :
    (∫⁻ x, ENNReal.ofReal (w x) * (∑ s : Fin 2, ∫⁻ y,
      ENNReal.ofReal (‖splitFermion i ψ ((x,s),y)‖^2)
        ∂(configMeasure N (spinSpaceMeasure (V := V))))) =
    ∫⁻ q, ENNReal.ofReal (w (q i).1) * ENNReal.ofReal (‖ψ q‖^2)
      ∂(configMeasure (N+1) (spinSpaceMeasure (V := V))) := by
  let ν := configMeasure N (spinSpaceMeasure (V := V))
  have hm : AEMeasurable (fun p : (V × Fin 2) × (Fin N → V × Fin 2) =>
      ENNReal.ofReal (w p.1.1) * ENNReal.ofReal (‖splitFermion i ψ p‖^2))
      ((spinSpaceMeasure (V := V)).prod ν) :=
    ((hw.comp (measurable_fst.comp measurable_fst)).ennreal_ofReal.aemeasurable).mul
      ((Lp.memLp (splitFermion i ψ)).aestronglyMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal
  have hp := splitAt_preserving (μ := spinSpaceMeasure (V := V)) i
  have ha := pull_ae (splitAt i).symm (hp.symm (splitAt i)) ψ
  calc
    _ = ∫⁻ x, ∫⁻ s : Fin 2, ∫⁻ y,
        ENNReal.ofReal (w x) * ENNReal.ofReal (‖splitFermion i ψ ((x,s),y)‖^2) ∂ν ∂Measure.count := by
      apply lintegral_congr
      intro x
      simp only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_fintype,Measure.count_singleton,mul_one,Finset.mul_sum]
      rfl
    _ = ∫⁻ p, ENNReal.ofReal (w p.1.1) * ENNReal.ofReal (‖splitFermion i ψ p‖^2)
        ∂((spinSpaceMeasure (V := V)).prod ν) := by
      rw [lintegral_prod _ hm,lintegral_prod _ hm.lintegral_prod_right']
    _ = ∫⁻ p, ENNReal.ofReal (w p.1.1) * ENNReal.ofReal (‖ψ ((splitAt i).symm p)‖^2)
        ∂((spinSpaceMeasure (V := V)).prod ν) := by
      apply lintegral_congr_ae
      filter_upwards [ha] with p hp
      rw [← hp]
      rfl
    _ = _ := by
      have he := (hp.symm (splitAt i)).lintegral_comp_emb
        (splitAt i).symm.measurableEmbedding
        (fun q => ENNReal.ofReal (w (q i).1) * ENNReal.ofReal (‖ψ q‖^2))
      have hs (p : (V × Fin 2) × (Fin N → V × Fin 2)) :
          (splitAt i).symm p i = p.1 := by
        exact congrArg Prod.fst ((splitAt i).apply_symm_apply p)
      simp_rw [hs] at he
      exact he

lemma density_weighted_lintegral {N : ℕ} (ψ : fermionL2 (V := V) (N+1))
    (w : V → ℝ) (hw : Measurable w) :
    (∫⁻ x, ENNReal.ofReal (w x) * fermionDensity ψ x) =
      ∑ i : Fin (N+1), ∫⁻ q, ENNReal.ofReal (w (q i).1) * ENNReal.ofReal (‖ψ q‖^2)
        ∂(configMeasure (N+1) (spinSpaceMeasure (V := V))) := by
  change (∫⁻ x, ENNReal.ofReal (w x) * ∑ i : Fin (N+1),
    ∑ s : Fin 2, ∫⁻ y, ENNReal.ofReal (‖splitFermion i ψ ((x,s),y)‖^2)
      ∂(configMeasure N (spinSpaceMeasure (V := V)))) = _
  conv_lhs => arg 2; ext x; rw [Finset.mul_sum]
  rw [lintegral_finsetSum' (f := fun i x => ENNReal.ofReal (w x) *
      (∑ s : Fin 2, ∫⁻ y, ENNReal.ofReal (‖splitFermion i ψ ((x,s),y)‖^2)
        ∂(configMeasure N (spinSpaceMeasure (V := V))))) Finset.univ (fun i _ =>
    hw.ennreal_ofReal.aemeasurable.mul (coordinateDensity_aemeasurable ψ i))]
  exact Finset.sum_congr rfl (fun i _ => coordinate_density_weighted ψ i w hw)
end CoulombLT

end

end OAI
