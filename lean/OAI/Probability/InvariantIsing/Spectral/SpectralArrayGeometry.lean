import OAI.Probability.InvariantIsing.Spectral.SpectralReplicaLaw
import OAI.Probability.IsingPerceptron.ArrayGeometry

namespace OAI

/-! Gram structure and replica symmetry for spectral arrays retaining common disorder. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology Matrix

namespace InvariantIsing

def permuteSpectralArray {m : ℕ} (e : ℕ → ℕ) (x : SpectralArray m) : SpectralArray m :=
  fun ij => x (e ij.1, e ij.2)

lemma continuous_permuteSpectralArray {m : ℕ} (e : ℕ → ℕ) :
    Continuous (permuteSpectralArray (m := m) e) := by
  unfold permuteSpectralArray
  fun_prop

lemma disorderReplicaLaw_map_reindex {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (e : ℕ → ℕ) (he : Function.Injective e) :
    (disorderReplicaLaw P ν hν).map (Prod.map id (fun σ i => σ (e i))) =
      disorderReplicaLaw P ν hν := by
  unfold disorderReplicaLaw
  rw [← Measure.compProd_map (by fun_prop)]
  congr 1
  apply Kernel.ext
  intro ω
  rw [Kernel.map_apply _ (by fun_prop)]
  change (Measure.infinitePi (fun _ : ℕ => ν ω)).map (fun σ i => σ (e i)) =
    Measure.infinitePi (fun _ : ℕ => ν ω)
  exact Measure.map_infinitePi_infinitePi_of_inj he

lemma spectralArrayLaw_map_reindex {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N)) (n : ℕ)
    (ν : Ω → Measure (Spin N × LabeledLeaf n)) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] (e : ℕ → ℕ) (he : Function.Injective e) :
    (spectralArrayLaw P U hU I n ν hν : Measure (SpectralArray (m + 1))).map
      (permuteSpectralArray e) = spectralArrayLaw P U hU I n ν hν := by
  change ((disorderReplicaLaw P ν hν).map (spectralReplicaArray U I n)).map _ = _
  rw [Measure.map_map (continuous_permuteSpectralArray e).measurable
    (measurable_spectralReplicaArray U hU I n)]
  have heq : permuteSpectralArray e ∘ spectralReplicaArray U I n =
      spectralReplicaArray U I n ∘ Prod.map id (fun σ i => σ (e i)) := rfl
  rw [heq, ← Measure.map_map (measurable_spectralReplicaArray U hU I n) (by fun_prop),
    disorderReplicaLaw_map_reindex P ν hν e he]
  rfl

lemma spectralArray_limit_reindex {m : ℕ} {L : ℕ → ProbabilityMeasure (SpectralArray m)}
    {Q : ProbabilityMeasure (SpectralArray m)} (hL : Tendsto L atTop (𝓝 Q))
    (e : ℕ → ℕ)
    (hE : ∀ k, (L k : Measure (SpectralArray m)).map (permuteSpectralArray e) = L k) :
    (Q : Measure (SpectralArray m)).map (permuteSpectralArray e) = Q := by
  have hc := (ProbabilityMeasure.continuous_map (continuous_permuteSpectralArray e)).tendsto Q
  have he : (fun k => (L k).map (permuteSpectralArray e)) = L := by
    funext k
    exact Subtype.ext (hE k)
  have ht := hc.comp hL
  change Tendsto (fun k => (L k).map (permuteSpectralArray e)) _ _ at ht
  rw [he] at ht
  have heq : Q.map (permuteSpectralArray e) = Q := tendsto_nhds_unique ht hL
  exact congrArg Subtype.val heq

lemma scalar_of_spectral_exchangeable {m : ℕ} {Q : ProbabilityMeasure (SpectralArray m)}
    (hE : ∀ e : Equiv.Perm ℕ,
      (Q : Measure (SpectralArray m)).map (permuteSpectralArray e) = Q)
    (f : SpectralEntry m → ℝ) (hf : Measurable f) :
    WeaklyExchangeable (fun x i j => f (x (i,j))) (Q : Measure (SpectralArray m)) := by
  intro e _
  have hm : Measurable (fun x : SpectralArray m => fun i j => f (x (i,j))) := by fun_prop
  refine ⟨hm.aemeasurable, (hm.comp (continuous_permuteSpectralArray e).measurable).aemeasurable, ?_⟩
  calc
    _ = ((Q : Measure (SpectralArray m)).map (permuteSpectralArray e)).map
        (fun x i j => f (x (i,j))) :=
      congrArg (Measure.map (fun x i j => f (x (i,j)))) (hE e).symm
    _ = _ := Measure.map_map hm (continuous_permuteSpectralArray e).measurable

def spectralCoordinateArray {m : ℕ} (a : Fin m) (x : SpectralArray m) : RealArray :=
  fun i j => x (i,j) a

lemma continuous_spectralCoordinateArray {m : ℕ} (a : Fin m) :
    Continuous (spectralCoordinateArray a) := by
  unfold spectralCoordinateArray
  fun_prop

def SpectralGram {m : ℕ} (x : SpectralArray m) : Prop :=
  ∀ a n, Matrix.PosSemidef (fun i j : Fin n => spectralCoordinateArray a x i j)

lemma isClosed_spectralGram (m : ℕ) : IsClosed {x : SpectralArray m | SpectralGram x} := by
  unfold SpectralGram
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun n =>
    (isClosed_setOf_posSemidef n).preimage (by unfold spectralCoordinateArray; fun_prop)

lemma spectralReplicaArray_gram {Ω : Type*} {N m : ℕ} (U : Ω → SpecialOrthogonal N)
    (I : Fin m → Finset (Fin N)) (n : ℕ)
    (p : Ω × (ℕ → Spin N × LabeledLeaf n)) : SpectralGram (spectralReplicaArray U I n p) := by
  intro a z
  refine Fin.lastCases ?_ (fun j => ?_) a
  · simpa only [spectralCoordinateArray, spectralReplicaArray, spectralJointEntry_tree] using
      treeOverlap_posSemidef n (fun i : Fin z => (p.2 i).2)
  · simpa only [spectralCoordinateArray, spectralReplicaArray, spectralJointEntry_spectral] using
      projectedOverlap_posSemidef (specialRotation (U p.1)) (I j) (fun i : Fin z => (p.2 i).1)

lemma spectralArrayLaw_gram {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N)) (n : ℕ)
    (ν : Ω → Measure (Spin N × LabeledLeaf n)) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] :
    ∀ᵐ x ∂(spectralArrayLaw P U hU I n ν hν : Measure (SpectralArray (m + 1))), SpectralGram x := by
  change ∀ᵐ x ∂(disorderReplicaLaw P ν hν).map (spectralReplicaArray U I n), SpectralGram x
  rw [ae_map_iff (measurable_spectralReplicaArray U hU I n).aemeasurable
    (isClosed_spectralGram (m + 1)).measurableSet]
  exact ae_of_all _ (spectralReplicaArray_gram U I n)

lemma spectralArray_limit_gram {m : ℕ} {L : ℕ → ProbabilityMeasure (SpectralArray m)}
    {Q : ProbabilityMeasure (SpectralArray m)} (hL : Tendsto L atTop (𝓝 Q))
    (hG : ∀ k, ∀ᵐ x ∂(L k : Measure (SpectralArray m)), SpectralGram x) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray m)), SpectralGram x :=
  ae_closed_of_weak_limit hL (isClosed_spectralGram m) hG

end InvariantIsing

end

end OAI
