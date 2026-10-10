import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.Form
import OAI.Analysis.CoulombIonization.Fermionic.SlaterSymmetry

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

lemma pi_count_eq_count {ι β : Type*} [Fintype ι] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β] :
    (Measure.pi fun _ : ι => (Measure.count : Measure β)) = Measure.count := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.pi_singleton, Measure.count_singleton]
  simp only [Measure.count_singleton, Finset.prod_const_one]

lemma spinSpace_measurePreserving (n : ℕ) :
    MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow (Fin 2) Space (Fin n))
      (Measure.pi fun _ : Fin n => (Measure.count : Measure (Fin 2)).prod volume)
      ((Measure.count : Measure (Spins n)).prod volume) := by
  simpa only [pi_count_eq_count, ← volume_pi] using
    measurePreserving_arrowProdEquivProdArrow (Fin 2) Space (Fin n)
      (fun _ => (Measure.count : Measure (Fin 2))) (fun _ => (volume : Measure Space))

lemma spinSpace_integral {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : (Fin n → Fin 2 × Space) → E)
    (hF : Integrable F (Measure.pi fun _ : Fin n =>
      (Measure.count : Measure (Fin 2)).prod volume)) :
    (∫ z, F z ∂Measure.pi (fun _ : Fin n => (Measure.count : Measure (Fin 2)).prod volume)) =
      ∑ s : Spins n, ∫ x : Configuration n, F (fun i => (s i,x i)) := by
  have hp := (spinSpace_measurePreserving n).symm
  have hi := (hp.integrable_comp_emb
    (MeasurableEquiv.arrowProdEquivProdArrow (Fin 2) Space (Fin n)).symm.measurableEmbedding).2 hF
  rw [← hp.integral_comp' F]
  change Integrable (fun z : Spins n × Configuration n =>
    F (fun i => (z.1 i,z.2 i))) (Measure.count.prod volume) at hi
  change (∫ z : Spins n × Configuration n, F (fun i => (z.1 i,z.2 i))
    ∂Measure.count.prod volume) = _
  rw [integral_prod _ hi, integral_count]

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

abbrev slaterParticleMeasure : Measure SlaterParticle :=
  (Measure.count : Measure (Fin 2)).prod volume

lemma compact_spinSpace {f : SlaterParticle → ℂ}
    (hc : ∀ s, HasCompactSupport (fun x : Space => f (s,x))) : HasCompactSupport f := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_univ.prod (isCompact_iUnion hc))
  intro z hz
  exact ⟨Set.mem_univ _, Set.mem_iUnion.mpr ⟨z.1, subset_tsupport _ hz⟩⟩

lemma memLp_spinSpace {f : SlaterParticle → ℂ}
    (hf : ∀ s, Continuous (fun x : Space => f (s,x)))
    (hc : ∀ s, HasCompactSupport (fun x : Space => f (s,x))) :
    MemLp f 2 slaterParticleMeasure :=
  (continuous_prod_of_discrete_left.mpr hf).memLp_of_hasCompactSupport (compact_spinSpace hc)

lemma memLp_spatialOrbitalDerivative {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (a : Fin 3) (i : Fin n) :
    MemLp (spatialOrbitalDerivative φ a i) 2 slaterParticleMeasure :=
  memLp_spinSpace (fun s => smooth_derivative_continuous (hφ i s) _)
    (fun s => compact_derivative (hc i s) _)

lemma slaterForm_mass {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 slaterParticleMeasure)
    (ho : ∀ i k, (∫ z, conj (φ i z) * φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0) :
    formMass (slaterForm φ) = 1 := by
  have he := spinSpace_integral (fun z => ‖slater φ z‖^2)
    (memLp_slater hφ).norm.integrable_sq
  have hn := slater_norm_sq_integral hφ ho
  rw [he] at hn
  exact hn

theorem slaterForm_admissible {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z) * φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0) :
    FormAdmissible (slaterForm φ) :=
  (slaterForm_sobolevFermion hφ hc).admissible
    (slaterForm_mass (fun i => memLp_spinSpace (fun s => (hφ i s).continuous) (hc i)) ho)

theorem slaterForm_kinetic {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z) * φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0) :
    formKinetic (slaterForm φ) = (1/2:ℝ) * ∑ a : Fin 3, ∑ i : Fin n,
      ∫ z, ‖spatialOrbitalDerivative φ a i z‖^2 ∂slaterParticleMeasure := by
  have hl (i : Fin n) : MemLp (φ i) 2 slaterParticleMeasure :=
    memLp_spinSpace (fun s => (hφ i s).continuous) (hc i)
  have hd := memLp_spatialOrbitalDerivative hφ hc
  have he (a : Fin 3) (j : Fin n) := spinSpace_integral
    (fun z => ‖slaterCoordinate φ (spatialOrbitalDerivative φ a) j z‖^2)
    (memLp_slaterCoordinate hl (hd a) j).norm.integrable_sq
  unfold formKinetic
  congr 1
  simp only [slaterForm]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Spins n))) (t := (Finset.univ : Finset (Fin 3)))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = ∑ j : Fin n, ∫ z, ‖slaterCoordinate φ (spatialOrbitalDerivative φ a) j z‖^2
        ∂Measure.pi (fun _ : Fin n => slaterParticleMeasure) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (he a j).symm
    _ = _ := slaterCoordinate_sum_norm_sq_integral hl (hd a) ho

end CoulombAtom

end

end OAI
