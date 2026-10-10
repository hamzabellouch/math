import OAI.Probability.PosteriorReplicas.Gaussian.GaussianWishart
import OAI.Probability.PosteriorReplicas.Gaussian.ObservableGaussian
import OAI.Probability.PosteriorReplicas.Information.ReplicaFiniteKL

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

abbrev AuxSpace (d ℓ k : ℕ) := Rows d ℓ × Rows ℓ k

def auxLaw (d ℓ k : ℕ) : Measure (AuxSpace d ℓ k) :=
  (gaussianRows d ℓ).prod (gaussianRows ℓ k)

instance (d ℓ k : ℕ) : IsProbabilityMeasure (auxLaw d ℓ k) := by
  unfold auxLaw; infer_instance

def projectedTuple {d ℓ m : ℕ} (B : Rows d ℓ) (u : Tuple d m) : Tuple ℓ m :=
  fun i => WithLp.toLp 2 (labels B (u i))

@[fun_prop] lemma measurable_projectedTuple {d ℓ m : ℕ} :
    Measurable (fun z : Rows d ℓ × Tuple d m => projectedTuple z.1 z.2) := by
  unfold projectedTuple labels; fun_prop

lemma differences_projectedTuple {d ℓ m : ℕ} (B : Rows d ℓ) (u : Tuple d m) :
    differences (projectedTuple B u) = pairingColumns (differences u) B := by
  ext i j
  simp [differences,projectedTuple,pairingColumns,labels,inner_sub_left,real_inner_comm]

def observableRows {d ℓ k m : ℕ} (u : Tuple d m) (b : AuxSpace d ℓ k) : Rows d k :=
  rowMix (randomComplement (pairingColumns (differences u) b.1) b.2) b.1

@[fun_prop] lemma measurable_observableRows {d ℓ k m : ℕ} :
    Measurable (fun z : Tuple d m × AuxSpace d ℓ k => observableRows z.1 z.2) := by
  unfold observableRows; fun_prop

lemma observableRows_law {d ℓ k m : ℕ} {u : Tuple d m}
    (hu : LinearIndependent ℝ (differences u)) (hkm : k+m ≤ ℓ) :
    (auxLaw d ℓ k).map (observableRows u) = constrainedRows k u := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map hH (by fun_prop), auxLaw, lintegral_prod _ (by fun_prop)]
  change (∫⁻ B, ∫⁻ e, H (rowMix (randomComplement (pairingColumns (differences u) B) e) B) ∂gaussianRows ℓ k ∂gaussianRows d ℓ) = _
  have he := observable_gaussian_lintegral hu hkm (H := fun z => H z.2) (by fun_prop)
  dsimp only [Prod.snd] at he
  rw [he]
  simp only [lintegral_const, measure_univ, mul_one]
  rw [constrainedRows, lintegral_map hH (by fun_prop)]
  rfl

abbrev Observation (d ℓ k m : ℕ) := AuxSpace d ℓ k × Tuple ℓ m

def observe {d ℓ k m : ℕ} (z : EqualSpace d k m × AuxSpace d ℓ k) : Observation d ℓ k m :=
  (z.2,projectedTuple z.2.1 z.1.2.2)

@[fun_prop] lemma measurable_observe {d ℓ k m : ℕ} : Measurable (@observe d ℓ k m) := by
  unfold observe; fun_prop

def observableLikelihood {d ℓ k m : ℕ} (f : Vec d → ℝ≥0∞)
    (z : Observation d ℓ k m) : ℝ≥0∞ :=
  let C := randomComplement (differences z.2) z.1.2
  equalConstant k m * (wishartMoment ℓ m k)⁻¹ *
    (ENNReal.ofReal (affineVolume z.2))⁻¹^k *
      (projectedDensity .spherical f (rowMix C z.1.1)
        (fun i => ⟪C i,z.2 0⟫))⁻¹^m

@[fun_prop] lemma measurable_observableLikelihood {d ℓ k m : ℕ} {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) : Measurable (@observableLikelihood d ℓ k m f) := by
  unfold observableLikelihood; fun_prop

lemma observableLikelihood_observe {d ℓ k m : ℕ} (f : Vec d → ℝ≥0∞)
    (z : EqualSpace d k m × AuxSpace d ℓ k) :
    observableLikelihood f (observe z) = equalConstant k m * (wishartMoment ℓ m k)⁻¹ *
      (ENNReal.ofReal (gramVolume (pairingColumns (differences z.1.2.2) z.2.1)))⁻¹^k *
      (projectedDensity .spherical f (observableRows z.1.2.2 z.2)
        (labels (observableRows z.1.2.2 z.2) (z.1.2.2 0)))⁻¹^m := by
  unfold observableLikelihood observe
  simp only [differences_projectedTuple]
  have he : (fun i => ⟪randomComplement (pairingColumns (differences z.1.2.2) z.2.1) z.2.2 i,
      projectedTuple z.2.1 z.1.2.2 0⟫) =
      labels (observableRows z.1.2.2 z.2) (z.1.2.2 0) := by
    ext i
    unfold observableRows labels projectedTuple rowMix
    simp [sum_inner,inner_smul_left,PiLp.inner_apply,labels,mul_comm]
  rw [he]
  have hv : affineVolume (projectedTuple z.2.1 z.1.2.2) =
      gramVolume (pairingColumns (differences z.1.2.2) z.2.1) := by
    change gramVolume (differences (projectedTuple z.2.1 z.1.2.2)) = _
    rw [differences_projectedTuple]
  rw [hv]
  rfl

lemma observableLikelihood_fixed_lintegral {d ℓ k m : ℕ}
    (hk : 1 ≤ k) (hkm : k+m ≤ ℓ) {u : Tuple d m}
    (hu : LinearIndependent ℝ (differences u))
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) (A : Rows d k) (y : Labels k) :
    (∫⁻ b, observableLikelihood f (observe ((A,y,u),b)) ∂auxLaw d ℓ k) =
      ∫⁻ A, replicaDensity .spherical f (A,labels A (u 0),u) ∂constrainedRows k u := by
  simp_rw [observableLikelihood_observe]
  rw [auxLaw,lintegral_prod _ (by fun_prop)]
  have h := observable_gaussian_lintegral hu hkm
    (H := fun z : Rows ℓ m × Rows d k => equalConstant k m * (wishartMoment ℓ m k)⁻¹ *
      (ENNReal.ofReal (gramVolume z.1))⁻¹^k *
      (projectedDensity .spherical f z.2 (labels z.2 (u 0)))⁻¹^m) (by unfold labels; fun_prop)
  change _ = _ at h
  rw [show (∫⁻ B, ∫⁻ e, equalConstant k m * (wishartMoment ℓ m k)⁻¹ *
      (ENNReal.ofReal (gramVolume (pairingColumns (differences u) B)))⁻¹^k *
      (projectedDensity .spherical f (observableRows u (B,e))
        (labels (observableRows u (B,e)) (u 0)))⁻¹^m ∂gaussianRows ℓ k ∂gaussianRows d ℓ) = _ from h]
  simp_rw [lintegral_const_mul _ (show Measurable (fun A : Rows d k =>
    (projectedDensity .spherical f (fun i => (Submodule.span ℝ (range (differences u)))ᗮ.starProjection (A i))
      (labels (fun i => (Submodule.span ℝ (range (differences u)))ᗮ.starProjection (A i)) (u 0)))⁻¹^m) by unfold labels; fun_prop)]
  rw [lintegral_mul_const _ (by fun_prop),lintegral_const_mul _ (by fun_prop),pairingColumns_inverse_moment hu (by omega : m ≤ ℓ)]
  rw [constrainedRows,lintegral_map (by unfold replicaDensity labels; fun_prop) (by fun_prop)]
  unfold replicaDensity
  dsimp only
  rw [lintegral_const_mul _ (by unfold labels; fun_prop)]
  have hz := wishartMoment_pos (ℓ := ℓ) (m := m) (k := k) (by omega)
  have ht := wishartMoment_ne_top hk hkm
  have hc : equalConstant k m * (wishartMoment ℓ m k)⁻¹ *
      ((ENNReal.ofReal (gramVolume (differences u)))⁻¹^k * wishartMoment ℓ m k) =
      equalConstant k m * (ENNReal.ofReal (gramVolume (differences u)))⁻¹^k := by
    calc
      _ = (equalConstant k m * (ENNReal.ofReal (gramVolume (differences u)))⁻¹^k) *
          ((wishartMoment ℓ m k)⁻¹ * wishartMoment ℓ m k) := by ring
      _ = _ := by rw [ENNReal.inv_mul_cancel hz.ne' ht,mul_one]
  rw [hc]
  rfl

lemma equalReference_tuple {d k m : ℕ} (ν : Measure (Vec d)) [IsProbabilityMeasure ν] :
    (equalReference (k := k) (m := m) ν).map (fun z => z.2.2) = Measure.pi (fun _ => ν) := by
  rw [equalReference,Measure.map_map (by fun_prop) measurable_rightBasePoint]
  change ((Measure.pi (fun _ : Fin (m+1) => ν)).prod (gaussianRows d k)).map Prod.fst = _
  simp only [Measure.map_fst_prod,measure_univ,one_smul]

lemma observableLikelihood_lintegral {d ℓ k m : ℕ} (hd : k+m+2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k+m ≤ ℓ)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] :
    (∫⁻ z : EqualSpace d k m × AuxSpace d ℓ k, observableLikelihood f (observe z)
      ∂(equalReference ((sphereLaw d).withDensity f)).prod (auxLaw d ℓ k)) = 1 := by
  have : IsProbabilityMeasure ((BaseLaw.spherical.measure d).withDensity f) := by
    change IsProbabilityMeasure ((sphereLaw d).withDensity f); infer_instance
  have := replicaLaw_probability hd hk hm .spherical hf hLt hfL
  rw [lintegral_prod _ (by fun_prop)]
  have he : (fun z : EqualSpace d k m => ∫⁻ b, observableLikelihood f (observe (z,b)) ∂auxLaw d ℓ k) =ᵐ[
      equalReference ((sphereLaw d).withDensity f)]
      (fun z => ∫⁻ b, observableLikelihood f (observe ((0,0,z.2.2),b)) ∂auxLaw d ℓ k) := by
    exact ae_of_all _ (fun z => rfl)
  rw [lintegral_congr_ae he, ← lintegral_map (f := fun u : Tuple d m =>
    ∫⁻ b, observableLikelihood f (observe (((0 : Rows d k),0,u),b)) ∂auxLaw d ℓ k) (by fun_prop) (by fun_prop),
    equalReference_tuple]
  calc
    _ = ∫⁻ u : Tuple d m, ∫⁻ A, replicaDensity .spherical f (A,labels A (u 0),u)
        ∂constrainedRows k u ∂Measure.pi (fun _ => (sphereLaw d).withDensity f) := by
      apply lintegral_congr_ae
      filter_upwards [ae_tilt_tuple_full_rank (by omega : 3 ≤ d) (by omega : m < d)
        .spherical hf hLt hfL] with u hu
      exact observableLikelihood_fixed_lintegral hk hkm hu hf 0 0
    _ = ∫⁻ z : EqualSpace d k m, replicaDensity .spherical f z
        ∂equalReference ((sphereLaw d).withDensity f) := by
      rw [equalReference_lintegral _ (by fun_prop)]
      apply lintegral_congr_ae
      filter_upwards [ae_tilt_tuple_full_rank (by omega : 3 ≤ d) (by omega : m < d)
        .spherical hf hLt hfL] with u hu
      rw [constrainedRows_eq_residualRows hu,lintegral_map (by unfold labels; fun_prop) (by fun_prop)]
    _ = 1 := by
      change (∫⁻ z, replicaDensity .spherical f z ∂equalReference ((BaseLaw.spherical.measure d).withDensity f)) = 1
      have hh := measure_univ (μ := replicaLaw (k := k) (m := m) .spherical f)
      rw [replicaLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] at hh
      exact hh

lemma observableDensity_expected {d ℓ k m : ℕ} {u : Tuple d m}
    (hu : LinearIndependent ℝ (differences u)) (hkm : k+m ≤ ℓ)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ b, projectedDensity .spherical f (observableRows u b) (labels (observableRows u b) (u 0))
      ∂auxLaw d ℓ k) = ∫⁻ A, projectedDensity .spherical f (residualRows u A)
      (labels (residualRows u A) (u 0)) ∂gaussianRows d k := by
  rw [← lintegral_map (f := fun A : Rows d k => projectedDensity .spherical f A (labels A (u 0)))
    (by unfold labels; fun_prop) (by fun_prop),observableRows_law hu hkm,
    constrainedRows_eq_residualRows hu,lintegral_map (by unfold labels; fun_prop) (by fun_prop)]

end PosteriorReplicas
end

end OAI
