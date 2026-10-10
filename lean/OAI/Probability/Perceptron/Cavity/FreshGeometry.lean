import Mathlib
import OAI.Probability.Perceptron.Variational.SynchronizedLimit
import OAI.Probability.Perceptron.Cavity.FreshGGUniqueness

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma compact_gg_spin_geometry (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hEx : ∀ e : Equiv.Perm ℕ, MeasurePreserving (compactRelabel (K:=CompactJointOverlap) e) (μ : Measure _) (μ : Measure _))
    (hGG : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
      (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect μ n i f g=0)
    (hR : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _), ∀ n, Matrix.PosSemidef (fun i j : Fin n => (Q i j).1.val))
    (hdiag : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _), ∀ i, (Q i i).1.val=1) :
    ∀ᵐ Q ∂(μ : Measure _), CompactSpinGeometry Q := by
  have hg : ∀ᵐ Q ∂compactRealLaw μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray Prod.fst Q)) :=
    (ae_map_iff compactArrayReal_measurable.aemeasurable (measurableSet_gram_arrays.preimage
      (scalarArray_measurable measurable_fst))).mpr hR
  have hu := scalarArray_ultrametric (compactRealLaw μ) (compactRealLaw_exchangeable μ hEx)
    (compactRealLaw_gg μ hGG) measurable_fst hg (compactRealLaw_diagonals μ).1
  have hbase : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _),
      min (Q 0 1).1.val (Q 0 2).1.val ≤ (Q 1 2).1.val :=
    (ae_map_iff compactArrayReal_measurable.aemeasurable (by measurability)).mp hu
  have hdistinct (i j k : ℕ) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
      ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _),
      min (Q i j).1.val (Q i k).1.val ≤ (Q j k).1.val := by
    let g : Fin 3 → ℕ := ![i,j,k]
    have hg : Function.Injective g := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [g]
    obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair (fun a : Fin 3 => a.val) g Fin.val_injective hg
    have h0 := he 0
    have h1 := he 1
    have h2 := he 2
    change e 0=i at h0
    change e 1=j at h1
    change e 2=k at h2
    have hh := (hEx e).quasiMeasurePreserving.ae hbase
    simpa only [compactRelabel,h0,h1,h2] using hh
  have hall : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _),
      ∀ i j k, i≠j → i≠k → j≠k → min (Q i j).1.val (Q i k).1.val ≤ (Q j k).1.val := by
    simp only [ae_all_iff]
    exact hdistinct
  filter_upwards [hR,hdiag,hall] with Q hQ hd hu
  have hs : ∀ i j, (Q i j).1.val=(Q j i).1.val :=
    gram_array_symmetric (fun i j => (Q i j).1.val) hQ
  refine ⟨hs,hd,?_⟩
  intro i j k
  by_cases hij : i=j
  · subst j
    exact min_le_right _ _
  by_cases hik : i=k
  · subst k
    rw [hs j i]
    exact min_le_left _ _
  by_cases hjk : j=k
  · subst k
    rw [hd j,min_self]
    exact (Q i j).1.property.2
  exact hu i j k hij hik hjk

lemma sourceGibbsArray_limit_spin_diagonal (k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : (n : ℕ) → Fin (n+1) → ℕ) (h : ℕ → Fin (k+1) → ℝ)
    (u : (n : ℕ) → Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℕ → ℝ≥0)
    (s : ℕ→ℕ) {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    ∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), ∀ i, (Q i i).1.val=1 := by
  rw [ae_all_iff]
  intro i
  have hc : IsClosed {Q : CompactArray CompactJointOverlap | (Q i i).1.val=1} :=
    isClosed_eq (by fun_prop) continuous_const
  apply (mem_ae_iff_prob_eq_one hc.measurableSet).mpr
  have hv := weak_limit_closed_full hlim hc
    (fun n => sourceGibbsArray_closed_full (s n) k f (p (s n)) (d (s n)) (h (s n)) (u (s n)) z (t (s n))
      hc (fun x => sourceJointArray_diagonal x i))
  simp only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hv,ENNReal.coe_one]

lemma source_contact_limit_spin_geometry (k : ℕ) (f : ℝ →ᵇ ℝ) (p d : ℕ → ℕ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (t : ℕ → ℝ≥0) (h : ℕ → Fin (k+1) → ℝ)
    (hh0 : ∀ n l, 0≤h n l) (hh : ∀ n, Monotone (h n))
    (u : (n : ℕ) → Fin (n+1) → ℝ)
    (hu : ∀ n, u n ∈ Icc (fun _ => 1) (fun _ => 2))
    (hmin : ∀ n, IsMinOn (fun v => quadraticBoxPenalty (sourcePenaltyWeight (n+1)) v-
      sourceExpectedPressure n k f (fun j => p j.val) (fun j => d j.val) (h n) z (t n) v)
      (Icc (fun _ : Fin (n+1) => 1) (fun _ => 2)) (u n))
    {H T : ℝ} (hH : 0≤H) (hhH : ∀ n, h n 0≤H) (ht : ∀ n, (t n:ℝ)≤T)
    (hcover : ∀ a b : ℕ, 1≤a+b → ∃ j, p j=a ∧ d j=b)
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ → ℕ} (hs : StrictMono s)
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f
      (fun a => p a.val) (fun a => d a.val) (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q := by
  apply compact_gg_spin_geometry ν
    (source_contact_limit_exchangeable k f (fun _ a => p a.val) (fun _ a => d a.val) h u z t s hlim)
    (source_contact_limit_joint_gg k f p d z hz hz0 hz1 t h hh0 hh u hu hmin hH hhH ht hs hlim hcover)
    (sourceGibbsArray_limit_gram k f (fun _ a => p a.val) (fun _ a => d a.val) h u z t s hlim).1
    (sourceGibbsArray_limit_spin_diagonal k f (fun _ a => p a.val) (fun _ a => d a.val) h u z t s hlim)

end SphericalPerceptronFreeEnergy
end

end OAI
