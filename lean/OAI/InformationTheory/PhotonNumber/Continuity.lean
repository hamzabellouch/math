import OAI.InformationTheory.PhotonNumber.BeamTrace

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace EntropyPhotonNumber
open TensorLp
def mixedVector {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρA ρB : State n)
    (ab : PairedIndex n) : JointFock n :=
  beamUnitary η hη (tensor (rootColumn ρA ab.1) (rootColumn ρB ab.2))

theorem mixedVector_norm {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρA ρB : State n) :
    HasSum (fun ab => ‖mixedVector η hη ρA ρB ab‖^2) 1 := by
  simpa only [mixedVector, LinearIsometryEquiv.norm_map, one_mul] using
    TraceEnsemble.hasSum_tensor_norm (rootColumn_norm ρA) (rootColumn_norm ρB)

def beamOutput {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρA ρB : State n) : State n where
  op := partialTrace (mixedVector η hη ρA ρB)
  positive := partialTrace_positive (mixedVector_norm η hη ρA ρB).summable
  trace_one := by
    simpa only [channelNumberBasis_apply, entry] using
      partialTrace_trace (mixedVector_norm η hη ρA ρB) (channelNumberBasis n)

theorem mixedVector_entry {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρA ρB : State n)
    (k l e : NumberIndex n) :
    inner ℂ (lp.single 2 (k,e) 1)
      (TraceEnsemble.operator (mixedVector η hη ρA ρB) (lp.single 2 (l,e) 1)) =
        outputBlock η ρA ρB k l e := by
  unfold mixedVector
  rw [TraceEnsemble.unitary_entry
    (TraceEnsemble.hasSum_tensor_norm (rootColumn_norm ρA) (rootColumn_norm ρB)).summable]
  rw [beam_symm_number, beam_symm_number]
  simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold outputBlock
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [TraceEnsemble.tensor_entry (rootColumn_norm ρA).summable (rootColumn_norm ρB).summable,
    rootColumn_operator, rootColumn_operator]
  simp only [entry, numberKet]
  ring

theorem beamOutput_spec {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρA ρB : State n) :
    IsBeamSplitterOutput η ρA ρB (beamOutput η hη ρA ρB) := by
  intro k l
  have h := partialTrace_entry (mixedVector_norm η hη ρA ρB).summable k l
  simpa only [mixedVector_entry, beamOutput, entry, numberKet] using h

end EntropyPhotonNumber

namespace BlockUnitary
variable {J : Type*} [Fintype J]

theorem finite_transform_norm_sq (U : J → J → ℝ)
    (hc : ∀ a b, ∑ k, U k a*U k b = if a=b then 1 else 0) (z : J → ℂ) :
    (∑ k, ‖∑ a, (U k a : ℂ)*z a‖^2) = ∑ a, ‖z a‖^2 := by
  classical
  let v : J → EuclideanSpace ℂ J := fun a => WithLp.toLp 2 (fun k => (U k a : ℂ))
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro a b
    change (∑ k, (U k b : ℂ)*star (U k a : ℂ)) = _
    simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← Complex.ofReal_sum, hc]
    by_cases hab : a=b
    · simp [hab]
    · simp [hab, Ne.symm hab]
  have hi := hv.inner_sum z z Finset.univ
  have he : (∑ a, z a • v a) = WithLp.toLp 2 (fun k => ∑ a, (U k a : ℂ)*z a) := by
    ext k
    simp [v, mul_comm]
  have hnorm : ‖∑ a, z a • v a‖^2 = ∑ a, ‖z a‖^2 := by
    calc
      _ = (inner ℂ (∑ a, z a • v a) (∑ a, z a • v a)).re :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
      _ = (∑ a, conj (z a)*z a).re := congrArg Complex.re hi
      _ = _ := by simp [Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]
  rw [he, EuclideanSpace.norm_sq_eq] at hnorm
  exact hnorm

variable {S : Type*} {I : S → Type*} [∀ s, Fintype (I s)]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem unitary_coordinate (b : HilbertBasis (Sigma I) ℂ E)
    (U : ∀ s, I s → I s → ℝ)
    (hcol : ∀ s a d, ∑ k, U s k a*U s k d = if a=d then 1 else 0)
    (hrow : ∀ s k l, ∑ a, U s k a*U s l a = if k=l then 1 else 0)
    (x : E) (s : S) (k : I s) :
    inner ℂ (b ⟨s,k⟩) (unitary b U hcol hrow x) =
      ∑ a, (U s k a : ℂ)* inner ℂ (b ⟨s,a⟩) x := by
  have hi := (unitary b U hcol hrow).inner_map_map
    ((unitary b U hcol hrow).symm (b ⟨s,k⟩)) x
  rw [LinearIsometryEquiv.apply_symm_apply, unitary_symm_apply_basis] at hi
  rw [hi]
  simp only [sum_inner, inner_smul_left, Complex.conj_ofReal]

theorem unitary_sector_mass (b : HilbertBasis (Sigma I) ℂ E)
    (U : ∀ s, I s → I s → ℝ)
    (hcol : ∀ s a d, ∑ k, U s k a*U s k d = if a=d then 1 else 0)
    (hrow : ∀ s k l, ∑ a, U s k a*U s l a = if k=l then 1 else 0)
    (x : E) (s : S) :
    (∑ k, ‖inner ℂ (b ⟨s,k⟩) (unitary b U hcol hrow x)‖^2) =
      ∑ k, ‖inner ℂ (b ⟨s,k⟩) x‖^2 := by
  simp only [unitary_coordinate]
  exact finite_transform_norm_sq (U s) (hcol s) _

theorem unitary_weighted_mass (b : HilbertBasis (Sigma I) ℂ E)
    (U : ∀ s, I s → I s → ℝ)
    (hcol : ∀ s a d, ∑ k, U s k a*U s k d = if a=d then 1 else 0)
    (hrow : ∀ s k l, ∑ a, U s k a*U s l a = if k=l then 1 else 0)
    (x : E) (w : S → ℝ≥0∞) :
    (∑' i : Sigma I, w i.1 * ENNReal.ofReal (‖inner ℂ (b i) (unitary b U hcol hrow x)‖^2)) =
      ∑' i : Sigma I, w i.1 * ENNReal.ofReal (‖inner ℂ (b i) x‖^2) := by
  rw [ENNReal.tsum_sigma', ENNReal.tsum_sigma']
  congr 1
  funext s
  simp only [tsum_fintype, ← Finset.mul_sum]
  congr 1
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),
    ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _), unitary_sector_mass]

end BlockUnitary

namespace TensorLp
variable {A B I : Type*}

def vectorMoment (w : A → ℝ≥0∞) (x : H A) : ℝ≥0∞ :=
  ∑' a, w a * ENNReal.ofReal (‖x a‖^2)

def matrixMoment [DecidableEq A] (w : A → ℝ≥0∞) (T : H A →L[ℂ] H A) : ℝ≥0∞ :=
  ∑' a, w a * ENNReal.ofReal (inner ℂ (lp.single 2 a 1) (T (lp.single 2 a 1))).re

theorem vectorMoment_one (x : H A) : vectorMoment (fun _ => 1) x = ENNReal.ofReal (‖x‖^2) := by
  simp only [vectorMoment, one_mul]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hasSum_square x).summable,
    (hasSum_square x).tsum_eq]

theorem matrixMoment_ensemble [DecidableEq A] {v : I → H A}
    (hv : Summable (fun i => ‖v i‖^2)) (w : A → ℝ≥0∞) :
    matrixMoment w (TraceEnsemble.operator v) = ∑' i, vectorMoment w (v i) := by
  have he (a : A) : ENNReal.ofReal
      (inner ℂ (lp.single 2 a 1) (TraceEnsemble.operator v (lp.single 2 a 1))).re =
      ∑' i, ENNReal.ofReal (‖v i a‖^2) := by
    have h : HasSum (fun i => ‖v i a‖^2)
        (inner ℂ (lp.single 2 a 1) (TraceEnsemble.operator v (lp.single 2 a 1))).re := by
      convert! TraceEnsemble.hasSum_quadratic hv (lp.single 2 a 1) using 1
      ext i
      simp only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
    rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) h.summable]
  simp only [matrixMoment, he, ← ENNReal.tsum_mul_left, vectorMoment]
  exact ENNReal.tsum_comm

theorem partialTrace_moment [DecidableEq A] {v : I → H (A × B)}
    (hv : Summable (fun i => ‖v i‖^2)) (w : A → ℝ≥0∞) :
    matrixMoment w (partialTrace v) = ∑' i, vectorMoment (fun ab : A × B => w ab.1) (v i) := by
  rw [partialTrace, matrixMoment_ensemble (hasSum_slice_family hv.hasSum).summable]
  simp only [vectorMoment, slice_apply]
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  congr 1
  funext i
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_prod]

theorem tensor_add_moment (w : A → ℝ≥0∞) (u : B → ℝ≥0∞) (x : H A) (y : H B) :
    vectorMoment (fun ab : A × B => w ab.1+u ab.2) (tensor x y) =
      vectorMoment w x * ENNReal.ofReal (‖y‖^2) +
      ENNReal.ofReal (‖x‖^2) * vectorMoment u y := by
  have hx : (∑' a, ENNReal.ofReal (‖x a‖^2)) = ENNReal.ofReal (‖x‖^2) := by
    simpa only [vectorMoment, one_mul] using vectorMoment_one x
  have hy : (∑' b, ENNReal.ofReal (‖y b‖^2)) = ENNReal.ofReal (‖y‖^2) := by
    simpa only [vectorMoment, one_mul] using vectorMoment_one y
  change (∑' ab : A × B, (w ab.1+u ab.2)*ENNReal.ofReal (‖x ab.1*y ab.2‖^2)) = _
  simp only [norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _),
    add_mul, ENNReal.tsum_add, ENNReal.tsum_prod']
  congr 1
  · simp only [← mul_assoc, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hy, vectorMoment]
  · simp only [mul_left_comm (u _) (ENNReal.ofReal _), ENNReal.tsum_mul_left,
      ENNReal.tsum_mul_right, hx, vectorMoment]

theorem ensemble_tensor_add_moment [DecidableEq A] [DecidableEq B]
    {v : I → H A} {J : Type*} {z : J → H B}
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hz : HasSum (fun j => ‖z j‖^2) 1)
    (w : A → ℝ≥0∞) (u : B → ℝ≥0∞) :
    (∑' ij : I × J, vectorMoment (fun ab : A × B => w ab.1+u ab.2) (tensor (v ij.1) (z ij.2))) =
      matrixMoment w (TraceEnsemble.operator v) + matrixMoment u (TraceEnsemble.operator z) := by
  have hv₁ : (∑' i, ENNReal.ofReal (‖v i‖^2)) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hv.summable, hv.tsum_eq]
    norm_num
  have hz₁ : (∑' j, ENNReal.ofReal (‖z j‖^2)) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hz.summable, hz.tsum_eq]
    norm_num
  simp only [tensor_add_moment, ENNReal.tsum_add, ENNReal.tsum_prod',
    ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hv₁, hz₁, one_mul, mul_one]
  rw [matrixMoment_ensemble hv.summable, matrixMoment_ensemble hz.summable]

end TensorLp

namespace EntropyPhotonNumber
open TensorLp FischerBeam

theorem beam_sector_weighted_mass {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (x : JointFock n) (w : NumberIndex n → ℝ≥0∞) :
    (∑' a : NumberSector n, w a.1 * ENNReal.ofReal
      (‖inner ℂ (jointSectorBasis n a) (beamUnitary η hη x)‖^2)) =
      ∑' a : NumberSector n, w a.1 * ENNReal.ofReal (‖inner ℂ (jointSectorBasis n a) x‖^2) := by
  unfold beamUnitary
  exact BlockUnitary.unitary_weighted_mass _ _ _ _ _ _

theorem beam_vector_moment {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (x : JointFock n) (w : NumberIndex n → ℝ≥0∞) :
    vectorMoment (fun ab : PairedIndex n => w (fun j => ab.1 j+ab.2 j)) (beamUnitary η hη x) =
      vectorMoment (fun ab : PairedIndex n => w (fun j => ab.1 j+ab.2 j)) x := by
  unfold vectorMoment
  rw [← (sectorEquiv n).tsum_eq (fun ab => w (fun j => ab.1 j+ab.2 j) *
    ENNReal.ofReal (‖beamUnitary η hη x ab‖^2)),
    ← (sectorEquiv n).tsum_eq (fun ab => w (fun j => ab.1 j+ab.2 j) *
    ENNReal.ofReal (‖x ab‖^2))]
  have he (a : NumberSector n) :
      (fun j => (sectorEquiv n a).1 j+(sectorEquiv n a).2 j) = a.1 := by
    funext j
    exact Nat.add_sub_of_le (Nat.le_of_lt_succ (a.2 j).isLt)
  simpa only [he, jointSectorBasis_apply, lp.inner_single_left, RCLike.inner_apply,
    map_one, one_mul, mul_one] using beam_sector_weighted_mass η hη x w

theorem beam_total_moment {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (x : JointFock n) :
    vectorMoment (fun ab : PairedIndex n => (totalNumber ab.1 : ℝ≥0∞)+totalNumber ab.2)
      (beamUnitary η hη x) =
      vectorMoment (fun ab : PairedIndex n => (totalNumber ab.1 : ℝ≥0∞)+totalNumber ab.2) x := by
  simpa only [totalNumber, Finset.sum_add_distrib, Nat.cast_add] using
    beam_vector_moment η hη x (fun k => (totalNumber k : ℝ≥0∞))

def energyMoment {n : ℕ} (ρ : State n) : ℝ≥0∞ :=
  matrixMoment (fun k => (totalNumber k : ℝ≥0∞)) ρ.op

theorem energyMoment_eq {n : ℕ} (ρ : State n) :
    energyMoment ρ = ∑' k, ENNReal.ofReal ((totalNumber k : ℝ)*(entry ρ.op k k).re) := by
  simp only [energyMoment, matrixMoment, entry, numberKet,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

theorem finiteEnergy_iff {n : ℕ} (ρ : State n) : FiniteEnergy ρ ↔ energyMoment ρ < ⊤ := by
  rw [energyMoment_eq]
  have hp (k : NumberIndex n) : 0 ≤ (totalNumber k : ℝ)*(entry ρ.op k k).re :=
    mul_nonneg (Nat.cast_nonneg _) (ρ.positive.re_inner_nonneg_right _)
  constructor
  · intro h
    exact h.tsum_ofReal_lt_top
  · intro h
    have hs := ENNReal.summable_toReal h.ne
    change Summable (fun k => (totalNumber k : ℝ)*(entry ρ.op k k).re)
    simpa only [ENNReal.toReal_ofReal (hp _)] using hs

theorem beamOutput_energy_le {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρA ρB : State n) :
    energyMoment (beamOutput η hη ρA ρB) ≤ energyMoment ρA + energyMoment ρB := by
  change matrixMoment _ (partialTrace (mixedVector η hη ρA ρB)) ≤ _
  rw [partialTrace_moment (mixedVector_norm η hη ρA ρB).summable]
  calc
    _ ≤ ∑' a, vectorMoment (fun ab : PairedIndex n =>
        (totalNumber ab.1 : ℝ≥0∞)+totalNumber ab.2) (mixedVector η hη ρA ρB a) := by
      apply ENNReal.tsum_le_tsum
      intro a
      apply ENNReal.tsum_le_tsum
      intro ab
      exact mul_le_mul' le_self_add le_rfl
    _ = ∑' a : PairedIndex n, vectorMoment (fun ab : PairedIndex n =>
        (totalNumber ab.1 : ℝ≥0∞)+totalNumber ab.2)
        (tensor (rootColumn ρA a.1) (rootColumn ρB a.2)) := by
      simp only [mixedVector, beam_total_moment]
    _ = energyMoment ρA + energyMoment ρB := by
      rw [ensemble_tensor_add_moment (rootColumn_norm ρA) (rootColumn_norm ρB)
        (fun k => (totalNumber k : ℝ≥0∞)) (fun k => (totalNumber k : ℝ≥0∞)),
        rootColumn_operator, rootColumn_operator]
      rfl

theorem beamOutput_finiteEnergy {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) {ρA ρB : State n}
    (hA : FiniteEnergy ρA) (hB : FiniteEnergy ρB) : FiniteEnergy (beamOutput η hη ρA ρB) := by
  apply (finiteEnergy_iff _).mpr
  exact (beamOutput_energy_le η hη ρA ρB).trans_lt
    (ENNReal.add_lt_top.mpr ⟨(finiteEnergy_iff ρA).mp hA, (finiteEnergy_iff ρB).mp hB⟩)

end EntropyPhotonNumber

namespace TensorLp
variable {A B : Type*}

theorem sum_slice_moment (w : A → ℝ≥0∞) (z : H (A × B)) :
    (∑' b, vectorMoment w (slice z b)) = vectorMoment (fun ab : A × B => w ab.1) z := by
  simp only [vectorMoment, slice_apply]
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_prod]

end TensorLp

namespace EntropyPhotonNumber
open TensorLp

def firstKraus {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (σ : State n)
    (eb : NumberIndex n × NumberIndex n) : Fock n →L[ℂ] Fock n :=
  sliceCLM eb.1 ∘L ((beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    tensorRight (rootColumn σ eb.2))

@[simp] theorem firstKraus_apply {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (σ : State n)
    (eb : NumberIndex n × NumberIndex n) (x : Fock n) :
    firstKraus η hη σ eb x = slice (beamUnitary η hη (tensor x (rootColumn σ eb.2))) eb.1 := rfl

theorem firstKraus_norm {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (σ : State n) (x : Fock n) :
    HasSum (fun eb => ‖firstKraus η hη σ eb x‖^2) (‖x‖^2) := by
  simp only [firstKraus_apply]
  apply hasSum_slice_family (v := fun b => beamUnitary η hη (tensor x (rootColumn σ b)))
  simpa only [LinearIsometryEquiv.norm_map, tensor_norm_sq, mul_one] using
    (rootColumn_norm σ).mul_left (‖x‖^2)

theorem firstKraus_energy {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (σ : State n) (x : Fock n) :
    (∑' eb, vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (firstKraus η hη σ eb x)) ≤
      vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) x +
        energyMoment σ * ENNReal.ofReal (‖x‖^2) := by
  have hn : (∑' b, ENNReal.ofReal (‖rootColumn σ b‖^2)) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (rootColumn_norm σ).summable,
      (rootColumn_norm σ).tsum_eq, ENNReal.ofReal_one]
  have he : (∑' b, vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (rootColumn σ b)) =
      energyMoment σ := by
    rw [← matrixMoment_ensemble (rootColumn_norm σ).summable, rootColumn_operator]
    rfl
  simp only [firstKraus_apply, ENNReal.tsum_prod']
  rw [ENNReal.tsum_comm]
  simp only [sum_slice_moment]
  calc
    _ ≤ ∑' b, vectorMoment (fun ab : NumberIndex n × NumberIndex n =>
        (totalNumber ab.1 : ℝ≥0∞)+totalNumber ab.2)
        (beamUnitary η hη (tensor x (rootColumn σ b))) := by
      apply ENNReal.tsum_le_tsum
      intro b
      apply ENNReal.tsum_le_tsum
      intro ab
      exact mul_le_mul' le_self_add le_rfl
    _ = _ := by
      simp only [beam_total_moment]
      simp_rw [tensor_add_moment (fun k : NumberIndex n => (totalNumber k : ℝ≥0∞))
        (fun k : NumberIndex n => (totalNumber k : ℝ≥0∞))]
      simp only [ENNReal.tsum_add,
        ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hn, he, mul_comm, one_mul]

def secondKraus {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρ : State n)
    (ea : NumberIndex n × NumberIndex n) : Fock n →L[ℂ] Fock n :=
  sliceCLM ea.1 ∘L ((beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    tensorLeft (rootColumn ρ ea.2))

@[simp] theorem secondKraus_apply {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρ : State n)
    (ea : NumberIndex n × NumberIndex n) (x : Fock n) :
    secondKraus η hη ρ ea x = slice (beamUnitary η hη (tensor (rootColumn ρ ea.2) x)) ea.1 := rfl

theorem secondKraus_norm {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρ : State n) (x : Fock n) :
    HasSum (fun ea => ‖secondKraus η hη ρ ea x‖^2) (‖x‖^2) := by
  simp only [secondKraus_apply]
  apply hasSum_slice_family (v := fun a => beamUnitary η hη (tensor (rootColumn ρ a) x))
  simpa only [LinearIsometryEquiv.norm_map, tensor_norm_sq, one_mul] using
    (rootColumn_norm ρ).mul_right (‖x‖^2)

theorem secondKraus_energy {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρ : State n) (x : Fock n) :
    (∑' ea, vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (secondKraus η hη ρ ea x)) ≤
      vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) x +
        energyMoment ρ * ENNReal.ofReal (‖x‖^2) := by
  have hn : (∑' a, ENNReal.ofReal (‖rootColumn ρ a‖^2)) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (rootColumn_norm ρ).summable,
      (rootColumn_norm ρ).tsum_eq, ENNReal.ofReal_one]
  have he : (∑' a, vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (rootColumn ρ a)) =
      energyMoment ρ := by
    rw [← matrixMoment_ensemble (rootColumn_norm ρ).summable, rootColumn_operator]
    rfl
  simp only [secondKraus_apply, ENNReal.tsum_prod']
  rw [ENNReal.tsum_comm]
  simp only [sum_slice_moment]
  calc
    _ ≤ ∑' a, vectorMoment (fun ab : NumberIndex n × NumberIndex n =>
        (totalNumber ab.1 : ℝ≥0∞)+totalNumber ab.2)
        (beamUnitary η hη (tensor (rootColumn ρ a) x)) := by
      apply ENNReal.tsum_le_tsum
      intro a
      apply ENNReal.tsum_le_tsum
      intro ab
      exact mul_le_mul' le_self_add le_rfl
    _ = _ := by
      simp only [beam_total_moment]
      simp_rw [tensor_add_moment (fun k : NumberIndex n => (totalNumber k : ℝ≥0∞))
        (fun k : NumberIndex n => (totalNumber k : ℝ≥0∞))]
      simp only [ENNReal.tsum_add,
        ENNReal.tsum_mul_right, hn, he, one_mul, add_comm]

def composeKraus {n : ℕ} {I J : Type*} (U : I → Fock n →L[ℂ] Fock n)
    (V : J → Fock n →L[ℂ] Fock n) (ij : I × J) : Fock n →L[ℂ] Fock n := U ij.1 ∘L V ij.2

theorem composeKraus_norm {n : ℕ} {I J : Type*} (U : I → Fock n →L[ℂ] Fock n)
    (V : J → Fock n →L[ℂ] Fock n)
    (hU : ∀ x, HasSum (fun i => ‖U i x‖^2) (‖x‖^2))
    (hV : ∀ x, HasSum (fun j => ‖V j x‖^2) (‖x‖^2)) (x : Fock n) :
    HasSum (fun ij => ‖composeKraus U V ij x‖^2) (‖x‖^2) := by
  change HasSum (fun ij : I × J => ‖U ij.1 (V ij.2 x)‖^2) (‖x‖^2)
  have hu (j : J) : (∑' i, ‖U i (V j x)‖^2) = ‖V j x‖^2 := (hU (V j x)).tsum_eq
  have hs : Summable (fun ji : J × I => ‖U ji.2 (V ji.1 x)‖^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    exact ⟨fun j => (hU (V j x)).summable, by simpa only [hu] using (hV x).summable⟩
  have ht : (∑' ji : J × I, ‖U ji.2 (V ji.1 x)‖^2) = ‖x‖^2 := by
    rw [hs.tsum_prod]
    simpa only [hu] using (hV x).tsum_eq
  have hsum : HasSum (fun ji : J × I => ‖U ji.2 (V ji.1 x)‖^2) (‖x‖^2) := ht ▸ hs.hasSum
  exact (Equiv.prodComm I J).hasSum_iff.mpr hsum

theorem composeKraus_energy {n : ℕ} {I J : Type*} (U : I → Fock n →L[ℂ] Fock n)
    (V : J → Fock n →L[ℂ] Fock n) {EU EV : ℝ≥0∞}
    (hV : ∀ x, HasSum (fun j => ‖V j x‖^2) (‖x‖^2))
    (hEU : ∀ x, (∑' i, vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (U i x)) ≤
      vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) x+EU*ENNReal.ofReal (‖x‖^2))
    (hEV : ∀ x, (∑' j, vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (V j x)) ≤
      vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) x+EV*ENNReal.ofReal (‖x‖^2))
    (x : Fock n) :
    (∑' ij, vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (composeKraus U V ij x)) ≤
      vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) x+(EU+EV)*ENNReal.ofReal (‖x‖^2) := by
  have hn : (∑' j, ENNReal.ofReal (‖V j x‖^2)) = ENNReal.ofReal (‖x‖^2) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hV x).summable, (hV x).tsum_eq]
  change (∑' ij : I × J, vectorMoment _ (U ij.1 (V ij.2 x))) ≤ _
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  calc
    _ ≤ ∑' j, (vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (V j x)+EU*ENNReal.ofReal (‖V j x‖^2)) :=
      ENNReal.tsum_le_tsum (fun j => hEU (V j x))
    _ = (∑' j, vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (V j x))+EU*ENNReal.ofReal (‖x‖^2) := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, hn]
    _ ≤ _ := by
      have hh := add_le_add_right (hEV x) (EU*ENNReal.ofReal (‖x‖^2))
      simpa only [add_mul, add_assoc, add_left_comm, add_comm] using hh

theorem state_ext {n : ℕ} {ρ σ : State n} (h : ρ.op = σ.op) : ρ = σ := by
  cases ρ; cases σ; cases h; rfl

theorem output_unique {n : ℕ} {η : ℝ} {ρA ρB ρC ρD : State n}
    (hC : IsBeamSplitterOutput η ρA ρB ρC) (hD : IsBeamSplitterOutput η ρA ρB ρD) :
    ρC = ρD := by
  apply state_ext
  exact entry_ext fun k l => (hC k l).unique (hD k l)

theorem output_eq {n : ℕ} {η : ℝ} (hη : η ∈ Set.Icc 0 1) {ρA ρB ρC : State n}
    (hC : IsBeamSplitterOutput η ρA ρB ρC) : ρC = beamOutput η hη ρA ρB :=
  output_unique hC (beamOutput_spec η hη ρA ρB)

end EntropyPhotonNumber

namespace TraceEnsemble
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J K : Type*}

omit [CompleteSpace E] in
theorem operator_reindex (e : I ≃ J) (v : J → E) : operator (fun i => v (e i)) = operator v := by
  exact e.tsum_eq (fun j => InnerProductSpace.rankOne ℂ (v j) (v j))

omit [CompleteSpace E] in
theorem kraus_hasSum {V : I → E →L[ℂ] E}
    (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    {v : J → E} {t : ℝ} (hv : HasSum (fun j => ‖v j‖^2) t) :
    HasSum (fun ij : I × J => ‖V ij.1 (v ij.2)‖^2) t := by
  have hu (j : J) : (∑' i, ‖V i (v j)‖^2) = ‖v j‖^2 := (hV (v j)).tsum_eq
  have hs : Summable (fun ji : J × I => ‖V ji.2 (v ji.1)‖^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    exact ⟨fun j => (hV (v j)).summable, by simpa only [hu] using hv.summable⟩
  have ht : (∑' ji : J × I, ‖V ji.2 (v ji.1)‖^2) = t := by
    rw [hs.tsum_prod]
    simpa only [hu] using hv.tsum_eq
  have hsum : HasSum (fun ji : J × I => ‖V ji.2 (v ji.1)‖^2) t := ht ▸ hs.hasSum
  exact (Equiv.prodComm I J).hasSum_iff.mpr hsum

end TraceEnsemble

namespace EntropyPhotonNumber
open TensorLp
theorem beam_ensemble {n : ℕ} {I J : Type*} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (ρ σ : State n) (v : I → Fock n) (w : J → Fock n)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1)
    (hev : TraceEnsemble.operator v = ρ.op) (hew : TraceEnsemble.operator w = σ.op) :
    partialTrace (fun ij : I × J => beamUnitary η hη (tensor (v ij.1) (w ij.2))) =
      (beamOutput η hη ρ σ).op := by
  have hn : Summable (fun ij : I × J => ‖beamUnitary η hη (tensor (v ij.1) (w ij.2))‖^2) := by
    simpa only [LinearIsometryEquiv.norm_map] using (TraceEnsemble.hasSum_tensor_norm hv hw).summable
  apply entry_ext
  intro k l
  have hh : HasSum (fun e => outputBlock η ρ σ k l e)
      (entry (partialTrace (fun ij : I × J => beamUnitary η hη (tensor (v ij.1) (w ij.2)))) k l) := by
    simpa only [entry, numberKet, beam_ensemble_entry η hη ρ σ v w hv hw hev hew] using
      partialTrace_entry hn k l
  exact hh.unique (beamOutput_spec η hη ρ σ k l)

theorem firstKraus_ensemble {n : ℕ} {I : Type*} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (ρ σ : State n) (v : I → Fock n) (hv : HasSum (fun i => ‖v i‖^2) 1)
    (hev : TraceEnsemble.operator v = ρ.op) :
    TraceEnsemble.operator (fun ei : (NumberIndex n × NumberIndex n) × I =>
      firstKraus η hη σ ei.1 (v ei.2)) = (beamOutput η hη ρ σ).op := by
  let e := (Equiv.prodAssoc (NumberIndex n) (NumberIndex n) I).trans
    (Equiv.prodCongr (Equiv.refl (NumberIndex n)) (Equiv.prodComm (NumberIndex n) I))
  have he := TraceEnsemble.operator_reindex e (fun z : NumberIndex n × (I × NumberIndex n) =>
    slice (beamUnitary η hη (tensor (v z.2.1) (rootColumn σ z.2.2))) z.1)
  change _ = partialTrace (fun ij : I × NumberIndex n => beamUnitary η hη (tensor (v ij.1) (rootColumn σ ij.2))) at he
  exact he.trans (beam_ensemble η hη ρ σ v (rootColumn σ) hv (rootColumn_norm σ) hev (rootColumn_operator σ))

theorem secondKraus_ensemble {n : ℕ} {I : Type*} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (ρ σ : State n) (v : I → Fock n) (hv : HasSum (fun i => ‖v i‖^2) 1)
    (hev : TraceEnsemble.operator v = σ.op) :
    TraceEnsemble.operator (fun ei : (NumberIndex n × NumberIndex n) × I =>
      secondKraus η hη ρ ei.1 (v ei.2)) = (beamOutput η hη ρ σ).op := by
  have he := TraceEnsemble.operator_reindex (Equiv.prodAssoc (NumberIndex n) (NumberIndex n) I)
    (fun z : NumberIndex n × (NumberIndex n × I) =>
      slice (beamUnitary η hη (tensor (rootColumn ρ z.2.1) (v z.2.2))) z.1)
  change _ = partialTrace (fun ij : NumberIndex n × I => beamUnitary η hη (tensor (rootColumn ρ ij.1) (v ij.2))) at he
  exact he.trans (beam_ensemble η hη ρ σ (rootColumn ρ) v (rootColumn_norm ρ) hv (rootColumn_operator ρ) hev)

theorem composeKraus_ensemble {n : ℕ} {I J K : Type*}
    (U : I → Fock n →L[ℂ] Fock n) (V : J → Fock n →L[ℂ] Fock n) (v : K → Fock n) :
    TraceEnsemble.operator (fun z : (I × J) × K => composeKraus U V z.1 (v z.2)) =
      TraceEnsemble.operator (fun z : I × (J × K) => U z.1 (V z.2.1 (v z.2.2))) := by
  unfold composeKraus
  exact TraceEnsemble.operator_reindex (Equiv.prodAssoc I J K)
    (fun z : I × (J × K) => U z.1 (V z.2.1 (v z.2.2)))

end EntropyPhotonNumber

namespace EnsembleL2
open scoped BigOperators ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def vector (v : I → E) (hv : Summable (fun i => ‖v i‖^2)) : lp (fun _ : I => E) 2 :=
  ⟨v, (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr
    (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hv)⟩
omit [InnerProductSpace ℂ E] in
@[simp] theorem vector_apply (v : I → E) (hv : Summable (fun i => ‖v i‖^2)) (i : I) : vector v hv i = v i := rfl

omit [InnerProductSpace ℂ E] in
theorem norm_sum (v : I → E) (hv : Summable (fun i => ‖v i‖^2)) :
    HasSum (fun i => ‖v i‖^2) (‖vector v hv‖^2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, vector_apply] using
    lp.hasSum_norm (p := 2) (by norm_num) (vector v hv)

theorem inner_sum (v w : I → E) (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun i => ‖w i‖^2)) :
    HasSum (fun i => inner ℂ (v i) (w i)) (inner ℂ (vector v hv) (vector w hw)) :=
  lp.hasSum_inner (𝕜 := ℂ) (vector v hv) (vector w hw)

theorem image_summable (v : I → E) (hv : Summable (fun i => ‖v i‖^2)) (T : E →L[ℂ] E) :
    Summable (fun i => ‖T (v i)‖^2) := by
  apply (hv.mul_left (‖T‖^2)).of_nonneg_of_le (fun _ => sq_nonneg _)
  intro i
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm (v i)) 2

theorem projection_bound (x a b : E) (hab : inner ℂ a b = 0)
    (hax : inner ℂ a x = inner ℂ a a) (hbx : inner ℂ b x = inner ℂ b b) :
    ‖a‖^2+‖b‖^2 ≤ ‖x‖^2 := by
  have hba : inner ℂ b a = 0 := by rw [← inner_conj_symm b a, hab, map_zero]
  have hxa : inner ℂ x a = inner ℂ a a := by
    rw [← inner_conj_symm x a, hax, inner_self_conj]
  have hxb : inner ℂ x b = inner ℂ b b := by
    rw [← inner_conj_symm x b, hbx, inner_self_conj]
  have hh : 0 ≤ (inner ℂ (x-a-b) (x-a-b)).re := inner_self_nonneg (𝕜 := ℂ) (x := x-a-b)
  simp only [inner_sub_left, inner_sub_right, hax, hbx, hxa, hxb, hab, hba] at hh
  simp only [Complex.sub_re, Complex.zero_re] at hh
  have hn (v : E) : (inner ℂ v v).re = ‖v‖^2 := by
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
  simp only [hn] at hh
  nlinarith

theorem projection_sums (x a b : I → E) (u v w : ℝ)
    (hx : HasSum (fun i => ‖x i‖^2) w) (ha : HasSum (fun i => ‖a i‖^2) u)
    (hb : HasSum (fun i => ‖b i‖^2) v)
    (hab : HasSum (fun i => inner ℂ (a i) (b i)) 0)
    (hax : HasSum (fun i => inner ℂ (a i) (x i)) (u : ℂ))
    (hbx : HasSum (fun i => inner ℂ (b i) (x i)) (v : ℂ)) : u+v ≤ w := by
  have hna := (norm_sum a ha.summable).unique ha
  have hnb := (norm_sum b hb.summable).unique hb
  have hnx := (norm_sum x hx.summable).unique hx
  have hh := projection_bound (vector x hx.summable) (vector a ha.summable) (vector b hb.summable)
    ((inner_sum a b ha.summable hb.summable).unique hab)
    (by rw [(inner_sum a x ha.summable hx.summable).unique hax, inner_self_eq_norm_sq_to_K]
        change (u:ℂ)=(‖vector a ha.summable‖:ℂ)^2
        rw [← Complex.ofReal_pow, hna])
    (by rw [(inner_sum b x hb.summable hx.summable).unique hbx, inner_self_eq_norm_sq_to_K]
        change (v:ℂ)=(‖vector b hb.summable‖:ℂ)^2
        rw [← Complex.ofReal_pow, hnb])
  rwa [hna, hnb, hnx] at hh

theorem fubini_inner (a z : I × J → E) (u : I → ℂ) (t : ℂ)
    (ha : Summable (fun ij => ‖a ij‖^2)) (hz : Summable (fun ij => ‖z ij‖^2))
    (hrow : ∀ i, HasSum (fun j => inner ℂ (a (i,j)) (z (i,j))) (u i))
    (hu : HasSum u t) : HasSum (fun ij => inner ℂ (a ij) (z ij)) t := by
  have hh := inner_sum a z ha hz
  exact (hh.prod_fiberwise hrow).unique hu ▸ hh

theorem fubini_inner_second (a z : I × J → E) (u : J → ℂ) (t : ℂ)
    (ha : Summable (fun ij => ‖a ij‖^2)) (hz : Summable (fun ij => ‖z ij‖^2))
    (hrow : ∀ j, HasSum (fun i => inner ℂ (a (i,j)) (z (i,j))) (u j))
    (hu : HasSum u t) : HasSum (fun ij => inner ℂ (a ij) (z ij)) t := by
  have hh := fubini_inner (fun ji : J × I => a (ji.2,ji.1))
    (fun ji : J × I => z (ji.2,ji.1)) u t
    ha.prod_symm hz.prod_symm hrow hu
  exact (Equiv.prodComm J I).hasSum_iff (f := fun ij => inner ℂ (a ij) (z ij)) |>.mp hh

theorem self_inner_hasSum (v : I → E) (hv : Summable (fun i => ‖v i‖^2)) :
    HasSum (fun i => inner ℂ (v i) (v i)) (((∑' i, ‖v i‖^2):ℝ):ℂ) := by
  have hh := hv.hasSum.mapL Complex.ofRealCLM
  have he (i : I) : inner ℂ (v i) (v i) = (((‖v i‖^2):ℝ):ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    change (‖v i‖:ℂ)^2=(((‖v i‖^2):ℝ):ℂ)
    rw [Complex.ofReal_pow]
  simpa only [he, Complex.ofRealCLM_apply] using hh

end EnsembleL2

namespace TensorLp
open scoped BigOperators ComplexConjugate
variable {A B I J : Type*}
theorem conditional_left_overlap (x : I → H A) (y : J → H B)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : HasSum (fun j => ‖y j‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B)) (S : H A →L[ℂ] H A)
    (hentry : ∀ u v, HasSum (fun j => inner ℂ (tensor u (y j)) (Z (tensor v (y j)))) (inner ℂ u (S v))) :
    HasSum (fun ij : I × J => inner ℂ (tensor (S (x ij.1)) (y ij.2))
      (Z (tensor (x ij.1) (y ij.2)))) (((∑' i, ‖S (x i)‖^2) : ℝ):ℂ) := by
  exact EnsembleL2.fubini_inner
    (fun ij : I × J => tensor (S (x ij.1)) (y ij.2))
    (fun ij : I × J => Z (tensor (x ij.1) (y ij.2)))
    (fun i => inner ℂ (S (x i)) (S (x i))) _
    (tensorFamily_summable (fun i => S (x i)) y (EnsembleL2.image_summable x hx S) hy.summable)
    (EnsembleL2.image_summable (fun ij : I × J => tensor (x ij.1) (y ij.2))
      (tensorFamily_summable x y hx hy.summable) Z)
    (fun i => hentry (S (x i)) (x i))
    (EnsembleL2.self_inner_hasSum (fun i => S (x i)) (EnsembleL2.image_summable x hx S))

theorem conditional_right_overlap (x : I → H A) (y : J → H B)
    (hx : HasSum (fun i => ‖x i‖^2) 1) (hy : Summable (fun j => ‖y j‖^2))
    (Z : H (A × B) →L[ℂ] H (A × B)) (T : H B →L[ℂ] H B)
    (hentry : ∀ u v, HasSum (fun i => inner ℂ (tensor (x i) u) (Z (tensor (x i) v))) (inner ℂ u (T v))) :
    HasSum (fun ij : I × J => inner ℂ (tensor (x ij.1) (T (y ij.2)))
      (Z (tensor (x ij.1) (y ij.2)))) (((∑' j, ‖T (y j)‖^2) : ℝ):ℂ) := by
  exact EnsembleL2.fubini_inner_second
    (fun ij : I × J => tensor (x ij.1) (T (y ij.2)))
    (fun ij : I × J => Z (tensor (x ij.1) (y ij.2)))
    (fun j => inner ℂ (T (y j)) (T (y j))) _
    (tensorFamily_summable x (fun j => T (y j)) hx.summable (EnsembleL2.image_summable y hy T))
    (EnsembleL2.image_summable (fun ij : I × J => tensor (x ij.1) (y ij.2))
      (tensorFamily_summable x y hx.summable hy) Z)
    (fun j => hentry (T (y j)) (y j))
    (EnsembleL2.self_inner_hasSum (fun j => T (y j)) (EnsembleL2.image_summable y hy T))

 theorem tensorFamily_norm (x : I → H A) (y : J → H B) (α β : ℝ)
    (hx : HasSum (fun i => ‖x i‖^2) α) (hy : HasSum (fun j => ‖y j‖^2) β) :
    HasSum (fun ij : I × J => ‖tensor (x ij.1) (y ij.2)‖^2) (α*β) := by
  have hs := hx.summable.mul_of_nonneg hy.summable (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  simpa only [tensor_norm_sq] using hx.mul hy hs

 theorem tensorFamily_orthogonal (x x' : I → H A) (y y' : J → H B)
    (hx : Summable (fun i => ‖x i‖^2)) (hx' : Summable (fun i => ‖x' i‖^2))
    (hy : Summable (fun j => ‖y j‖^2)) (hy' : Summable (fun j => ‖y' j‖^2))
    (hleft : HasSum (fun i => inner ℂ (x i) (x' i)) 0)
    (hright : HasSum (fun j => inner ℂ (y j) (y' j)) 0) :
    HasSum (fun ij : I × J => inner ℂ (tensor (x ij.1) (y ij.2)) (tensor (x' ij.1) (y' ij.2))) 0 := by
  have hs := (EnsembleL2.inner_sum
    (fun ij : I × J => tensor (x ij.1) (y ij.2))
    (fun ij : I × J => tensor (x' ij.1) (y' ij.2))
    (tensorFamily_summable x y hx hy) (tensorFamily_summable x' y' hx' hy')).summable
  simp only [inner_tensor] at hs
  simpa only [inner_tensor, zero_mul] using hleft.mul hright hs

theorem arithmetic_projection (x : I → H A) (y : J → H B)
    (hx : HasSum (fun i => ‖x i‖^2) 1) (hy : HasSum (fun j => ‖y j‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B))
    (S : H A →L[ℂ] H A) (T : H B →L[ℂ] H B)
    (hSentry : ∀ u v, HasSum (fun j => inner ℂ (tensor u (y j)) (Z (tensor v (y j)))) (inner ℂ u (S v)))
    (hTentry : ∀ u v, HasSum (fun i => inner ℂ (tensor (x i) u) (Z (tensor (x i) v))) (inner ℂ u (T v)))
    (hleft : HasSum (fun i => inner ℂ (x i) (S (x i))) 0)
    (hright : HasSum (fun j => inner ℂ (y j) (T (y j))) 0) :
    (∑' i, ‖S (x i)‖^2)+(∑' j, ‖T (y j)‖^2) ≤
      ∑' ij : I × J, ‖Z (tensor (x ij.1) (y ij.2))‖^2 := by
  have hS := EnsembleL2.image_summable x hx.summable S
  have hT := EnsembleL2.image_summable y hy.summable T
  let z := fun ij : I × J => Z (tensor (x ij.1) (y ij.2))
  let a := fun ij : I × J => tensor (S (x ij.1)) (y ij.2)
  let b := fun ij : I × J => tensor (x ij.1) (T (y ij.2))
  have hz : Summable (fun ij => ‖z ij‖^2) :=
    EnsembleL2.image_summable (fun ij : I × J => tensor (x ij.1) (y ij.2)) (tensorFamily_summable x y hx.summable hy.summable) Z
  have ha : HasSum (fun ij => ‖a ij‖^2) (∑' i, ‖S (x i)‖^2) := by
    exact mul_one (∑' i, ‖S (x i)‖^2) ▸ tensorFamily_norm (fun i => S (x i)) y _ 1 hS.hasSum hy
  have hb : HasSum (fun ij => ‖b ij‖^2) (∑' j, ‖T (y j)‖^2) := by
    exact one_mul (∑' j, ‖T (y j)‖^2) ▸ tensorFamily_norm x (fun j => T (y j)) 1 _ hx hT.hasSum
  have hcl : HasSum (fun i => inner ℂ (S (x i)) (x i)) 0 := by
    have hh := hleft.mapL Complex.conjCLE.toContinuousLinearMap
    change HasSum (fun i => conj (inner ℂ (x i) (S (x i)))) (conj 0) at hh
    simpa only [map_zero, inner_conj_symm] using hh
  have hab : HasSum (fun ij => inner ℂ (a ij) (b ij)) 0 :=
    tensorFamily_orthogonal (fun i => S (x i)) x y (fun j => T (y j)) hS hx.summable hy.summable hT hcl hright
  exact EnsembleL2.projection_sums z a b _ _ _ hz.hasSum ha hb hab
    (conditional_left_overlap x y hx.summable hy Z S hSentry) (conditional_right_overlap x y hx hy.summable Z T hTentry)
end TensorLp

namespace KrausBounded
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace E] [CompleteSpace H]

theorem dual_point_square (V : I → E →L[ℂ] H)
    (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (Z : H →L[ℂ] H) (x : E) :
    ‖dual V hV Z x‖^2 ≤ ∑' i, ‖Z (V i x)‖^2 := by
  have hn : ‖(analysis V hV).adjoint‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact analysis_norm V hV
  have ht : ‖dual V hV Z x‖ ≤ ‖acted V hV Z x‖ := by
    exact ((analysis V hV).adjoint.le_opNorm (acted V hV Z x)).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hn (norm_nonneg (acted V hV Z x)))
  have hs : HasSum (fun i => ‖Z (V i x)‖^2) (‖acted V hV Z x‖^2) := by
    convert! lp.hasSum_norm (p:=2) (by norm_num) (acted V hV Z x) using 1 <;> simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    rfl
  rw [hs.tsum_eq]
  exact pow_le_pow_left₀ (norm_nonneg _) ht 2
end KrausBounded

namespace EnsembleL2
open scoped BigOperators ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
def mean (v : I → E) (Z : E →L[ℂ] E) : ℂ := ∑' i, inner ℂ (v i) (Z (v i))
def center (v : I → E) (Z : E →L[ℂ] E) : E →L[ℂ] E := Z-mean v Z • ContinuousLinearMap.id ℂ E

omit [CompleteSpace E] in
theorem mean_hasSum (v : I → E) (hv : Summable (fun i => ‖v i‖^2)) (Z : E →L[ℂ] E) :
    HasSum (fun i => inner ℂ (v i) (Z (v i))) (mean v Z) :=
  (inner_sum v (fun i => Z (v i)) hv (image_summable v hv Z)).summable.hasSum

omit [CompleteSpace E] in
theorem center_mean (v : I → E) (hv : HasSum (fun i => ‖v i‖^2) 1) (Z : E →L[ℂ] E) :
    HasSum (fun i => inner ℂ (v i) (center v Z (v i))) 0 := by
  have hi : HasSum (fun i => inner ℂ (v i) (v i)) (1:ℂ) := by
    simpa only [hv.tsum_eq, Complex.ofReal_one] using self_inner_hasSum v hv.summable
  have hh := (mean_hasSum v hv.summable Z).sub (hi.mul_left (mean v Z))
  simpa only [center, sub_apply, smul_apply, inner_sub_right, inner_smul_right,
    ContinuousLinearMap.id_apply, mul_one, sub_self] using hh
end EnsembleL2

namespace TensorLp
open scoped BigOperators ComplexConjugate
variable {A B I J : Type*}

theorem conditionalLeft_mean (x : I → H A) (y : J → H B)
    (hx : HasSum (fun i => ‖x i‖^2) 1) (hy : HasSum (fun j => ‖y j‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B)) :
    HasSum (fun i => inner ℂ (x i) (conditionalLeft y hy Z (x i)))
      (EnsembleL2.mean (fun ij : I × J => tensor (x ij.1) (y ij.2)) Z) := by
  have hh := EnsembleL2.mean_hasSum (fun ij : I × J => tensor (x ij.1) (y ij.2))
    (tensorFamily_summable x y hx.summable hy.summable) Z
  exact hh.prod_fiberwise (fun i => conditionalLeft_entry y hy Z (x i) (x i))

theorem conditionalRight_mean (x : I → H A) (y : J → H B)
    (hx : HasSum (fun i => ‖x i‖^2) 1) (hy : HasSum (fun j => ‖y j‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B)) :
    HasSum (fun j => inner ℂ (y j) (conditionalRight x hx Z (y j)))
      (EnsembleL2.mean (fun ij : I × J => tensor (x ij.1) (y ij.2)) Z) := by
  have hh := EnsembleL2.mean_hasSum (fun ij : I × J => tensor (x ij.1) (y ij.2))
    (tensorFamily_summable x y hx.summable hy.summable) Z
  exact ((Equiv.prodComm J I).hasSum_iff.mpr hh).prod_fiberwise
    (fun j => conditionalRight_entry x hx Z (y j) (y j))

theorem centered_arithmetic_projection (x : I → H A) (y : J → H B)
    (hx : HasSum (fun i => ‖x i‖^2) 1) (hy : HasSum (fun j => ‖y j‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B)) :
    let T := EnsembleL2.center (fun ij : I × J => tensor (x ij.1) (y ij.2)) Z
    (∑' i, ‖conditionalLeft y hy T (x i)‖^2)+(∑' j, ‖conditionalRight x hx T (y j)‖^2) ≤
      ∑' ij : I × J, ‖T (tensor (x ij.1) (y ij.2))‖^2 := by
  dsimp only
  let T := EnsembleL2.center (fun ij : I × J => tensor (x ij.1) (y ij.2)) Z
  have hv : HasSum (fun ij : I × J => ‖tensor (x ij.1) (y ij.2)‖^2) 1 := by
    simpa only [one_mul] using tensorFamily_norm x y 1 1 hx hy
  have hm := EnsembleL2.center_mean (fun ij : I × J => tensor (x ij.1) (y ij.2)) hv Z
  have hz : EnsembleL2.mean (fun ij : I × J => tensor (x ij.1) (y ij.2)) T=0 := hm.tsum_eq
  apply arithmetic_projection x y hx hy T (conditionalLeft y hy T) (conditionalRight x hx T)
    (conditionalLeft_entry y hy T) (conditionalRight_entry x hx T)
  · exact hz ▸ conditionalLeft_mean x y hx hy T
  · exact hz ▸ conditionalRight_mean x y hx hy T
end TensorLp

namespace KrausBounded

section
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace E] [CompleteSpace H]

theorem dual_id (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2)) :
    dual V hV (ContinuousLinearMap.id ℂ H)=ContinuousLinearMap.id ℂ E := by
  have he : acted V hV (ContinuousLinearMap.id ℂ H)=analysis V hV := by
    ext x i
    rfl
  rw [dual, he]
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp
  intro x
  have hh : ‖analysis V hV x‖^2=‖x‖^2 := (wave_square V (fun y => (hV y).summable) x).trans (hV x).tsum_eq
  nlinarith [norm_nonneg (analysis V hV x), norm_nonneg x]
end

open scoped BigOperators ComplexConjugate
variable {E H K I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace E] [CompleteSpace H]

omit [CompleteSpace E] [CompleteSpace H] in
theorem family_hasSum (V : K → E →L[ℂ] H)
    (hV : ∀ x, HasSum (fun k => ‖V k x‖^2) (‖x‖^2))
    (v : I → E) (t : ℝ) (hv : HasSum (fun i => ‖v i‖^2) t) :
    HasSum (fun ik : I × K => ‖V ik.2 (v ik.1)‖^2) t := by
  have hs : Summable (fun ik : I × K => ‖V ik.2 (v ik.1)‖^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    refine ⟨fun i => (hV (v i)).summable, ?_⟩
    simpa only [(hV _).tsum_eq] using hv.summable
  have he : (∑' ik : I × K, ‖V ik.2 (v ik.1)‖^2)=t := by
    rw [hs.tsum_prod]
    simpa only [(hV _).tsum_eq] using hv.tsum_eq
  exact he ▸ hs.hasSum

theorem dual_output_mean (V : K → E →L[ℂ] H)
    (hV : ∀ x, HasSum (fun k => ‖V k x‖^2) (‖x‖^2))
    (v : I → E) (hv : Summable (fun i => ‖v i‖^2)) (Z : H →L[ℂ] H) :
    EnsembleL2.mean v (dual V hV Z)=EnsembleL2.mean (fun ik : I × K => V ik.2 (v ik.1)) Z := by
  have hw := family_hasSum V hV v _ hv.hasSum
  have hh := EnsembleL2.mean_hasSum (fun ik : I × K => V ik.2 (v ik.1)) hw.summable Z
  exact (EnsembleL2.mean_hasSum v hv (dual V hV Z)).unique
    (hh.prod_fiberwise (fun i => dual_entry V hV Z (v i) (v i)))

theorem dual_center (V : K → E →L[ℂ] H)
    (hV : ∀ x, HasSum (fun k => ‖V k x‖^2) (‖x‖^2))
    (v : I → E) (hv : Summable (fun i => ‖v i‖^2)) (Z : H →L[ℂ] H) :
    EnsembleL2.center v (dual V hV Z)=
      dual V hV (EnsembleL2.center (fun ik : I × K => V ik.2 (v ik.1)) Z) := by
  unfold EnsembleL2.center
  rw [dual_output_mean V hV v hv Z]
  simp only [sub_eq_add_neg, ← neg_smul, dual_add, dual_smul, dual_id]

theorem dual_variance (V : K → E →L[ℂ] H)
    (hV : ∀ x, HasSum (fun k => ‖V k x‖^2) (‖x‖^2))
    (v : I → E) (hv : Summable (fun i => ‖v i‖^2)) (Z : H →L[ℂ] H) :
    (∑' i, ‖EnsembleL2.center v (dual V hV Z) (v i)‖^2) ≤
      ∑' ik : I × K, ‖EnsembleL2.center (fun ik : I × K => V ik.2 (v ik.1)) Z (V ik.2 (v ik.1))‖^2 := by
  let T := EnsembleL2.center (fun ik : I × K => V ik.2 (v ik.1)) Z
  have hw := family_hasSum V hV v _ hv.hasSum
  have hs := EnsembleL2.image_summable (fun ik : I × K => V ik.2 (v ik.1)) hw.summable T
  rw [dual_center V hV v hv Z, hs.tsum_prod]
  exact Summable.tsum_le_tsum (fun i => dual_point_square V hV T (v i))
    (EnsembleL2.image_summable v hv (dual V hV T)) hs.prod
end KrausBounded

namespace TensorLp
open scoped BigOperators ComplexConjugate
variable {A B I J K E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem channel_arithmetic_projection (x : I → H A) (y : J → H B)
    (hx : HasSum (fun i => ‖x i‖^2) 1) (hy : HasSum (fun j => ‖y j‖^2) 1)
    (V : K → H (A × B) →L[ℂ] E)
    (hV : ∀ z, HasSum (fun k => ‖V k z‖^2) (‖z‖^2))
    (Z : E →L[ℂ] E) :
    let v := fun ij : I × J => tensor (x ij.1) (y ij.2)
    let T := EnsembleL2.center v (KrausBounded.dual V hV Z)
    (∑' i, ‖conditionalLeft y hy T (x i)‖^2)+(∑' j, ‖conditionalRight x hx T (y j)‖^2) ≤
      ∑' ik : (I × J) × K, ‖EnsembleL2.center (fun ik : (I × J) × K => V ik.2 (v ik.1)) Z (V ik.2 (v ik.1))‖^2 := by
  exact (centered_arithmetic_projection x y hx hy (KrausBounded.dual V hV Z)).trans
    (KrausBounded.dual_variance V hV (fun ij : I × J => tensor (x ij.1) (y ij.2))
      (tensorFamily_summable x y hx.summable hy.summable) Z)
end TensorLp

namespace KrausBounded
open scoped BigOperators ComplexConjugate
variable {E H F I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace E] [CompleteSpace H] [CompleteSpace F]

def composite (V : I → E →L[ℂ] H) (U : J → H →L[ℂ] F) (ij : I × J) : E →L[ℂ] F := U ij.2 ∘L V ij.1

omit [CompleteSpace E] [CompleteSpace H] [CompleteSpace F] in
theorem composite_norm (V : I → E →L[ℂ] H) (U : J → H →L[ℂ] F)
    (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (hU : ∀ x, HasSum (fun j => ‖U j x‖^2) (‖x‖^2)) (x : E) :
    HasSum (fun ij => ‖composite V U ij x‖^2) (‖x‖^2) :=
  family_hasSum U hU (fun i => V i x) _ (hV x)

theorem dual_composite (V : I → E →L[ℂ] H) (U : J → H →L[ℂ] F)
    (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (hU : ∀ x, HasSum (fun j => ‖U j x‖^2) (‖x‖^2)) (Z : F →L[ℂ] F) :
    dual (composite V U) (composite_norm V U hV hU) Z=dual V hV (dual U hU Z) := by
  ext y
  apply ext_inner_left ℂ
  intro x
  have hh := dual_entry (composite V U) (composite_norm V U hV hU) Z x y
  exact (hh.prod_fiberwise (fun i => dual_entry U hU Z (V i x) (V i y))).unique
    (dual_entry V hV (dual U hU Z) x y)

theorem dual_reindex {K : Type*} (e : K ≃ I) (V : I → E →L[ℂ] H)
    (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (hW : ∀ x, HasSum (fun k => ‖V (e k) x‖^2) (‖x‖^2)) (Z : H →L[ℂ] H) :
    dual (fun k => V (e k)) hW Z=dual V hV Z := by
  ext y
  apply ext_inner_left ℂ
  intro x
  exact (dual_entry _ hW Z x y).unique (e.hasSum_iff.mpr (dual_entry V hV Z x y))
end KrausBounded

namespace EntropyPhotonNumber
open TensorLp KrausBounded
open scoped BigOperators ComplexConjugate

def jointKraus {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (e : NumberIndex n) :
    H (NumberIndex n × NumberIndex n) →L[ℂ] Fock n :=
  sliceCLM e ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap

theorem jointKraus_norm {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (x : H (NumberIndex n × NumberIndex n)) :
    HasSum (fun e => ‖jointKraus η hη e x‖^2) (‖x‖^2) := by
  convert! hasSum_slice_norm_sq (beamUnitary η hη x) using 1
  exact (beamUnitary η hη).norm_map x |>.symm |> congrArg (fun t : ℝ => t^2)

def rawJointKraus {n : ℕ} (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (τ : State n) := composite (jointKraus η hη) (firstKraus θ hθ τ)

theorem rawJointKraus_norm {n : ℕ} (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (τ : State n) (x : H (NumberIndex n × NumberIndex n)) :
    HasSum (fun e => ‖rawJointKraus η θ hη hθ τ e x‖^2) (‖x‖^2) :=
  composite_norm _ _ (jointKraus_norm η hη) (firstKraus_norm θ hθ τ) x

def rawDual {n : ℕ} (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (τ : State n) (Z : Fock n →L[ℂ] Fock n) :=
  dual (rawJointKraus η θ hη hθ τ) (rawJointKraus_norm η θ hη hθ τ) Z

theorem physical_arithmetic_projection {n : ℕ} (η θ : ℝ)
    (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (ρ σ τ : State n)
    (Z : Fock n →L[ℂ] Fock n) :
    let x := rootColumn ρ
    let y := rootColumn σ
    let v := fun ij : NumberIndex n × NumberIndex n => tensor (x ij.1) (y ij.2)
    let T := EnsembleL2.center v (rawDual η θ hη hθ τ Z)
    let out := fun ik : (NumberIndex n × NumberIndex n) × (NumberIndex n × (NumberIndex n × NumberIndex n)) =>
      rawJointKraus η θ hη hθ τ ik.2 (v ik.1)
    (∑' i, ‖conditionalLeft y (rootColumn_norm σ) T (x i)‖^2)+
      (∑' j, ‖conditionalRight x (rootColumn_norm ρ) T (y j)‖^2) ≤
      ∑' ik, ‖EnsembleL2.center out Z (out ik)‖^2 :=
  channel_arithmetic_projection (rootColumn ρ) (rootColumn σ) (rootColumn_norm ρ)
    (rootColumn_norm σ) (rawJointKraus η θ hη hθ τ) (rawJointKraus_norm η θ hη hθ τ) Z

def fixedPortEquiv (n : ℕ) : ((NumberIndex n × NumberIndex n) × (NumberIndex n × NumberIndex n)) ≃
    NumberIndex n × (NumberIndex n × (NumberIndex n × NumberIndex n)) where
  toFun z := (z.2.2, (z.2.1,z.1))
  invFun z := (z.2.2,(z.2.1,z.1))
  left_inv _ := rfl
  right_inv _ := rfl

theorem rawDual_first_slice {n : ℕ} (η θ : ℝ)
    (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (σ τ : State n)
    (Z : Fock n →L[ℂ] Fock n) :
    conditionalLeft (rootColumn σ) (rootColumn_norm σ) (rawDual η θ hη hθ τ Z)=
      dual (composeKraus (firstKraus θ hθ τ) (firstKraus η hη σ))
        (composeKraus_norm _ _ (firstKraus_norm θ hθ τ) (firstKraus_norm η hη σ)) Z := by
  let V := fun j => tensorRight (A := NumberIndex n) (rootColumn σ j)
  let U := rawJointKraus η θ hη hθ τ
  have hh := dual_composite V U (rightFamily_norm _ (rootColumn_norm σ))
    (rawJointKraus_norm η θ hη hθ τ) Z
  change dual V _ (dual U _ Z)=_
  rw [← hh]
  have he : (fun k => composite V U (fixedPortEquiv n k))=
      composeKraus (firstKraus θ hθ τ) (firstKraus η hη σ) := by
    funext k
    ext z
    rfl
  have hr := dual_reindex (fixedPortEquiv n) (composite V U)
    (composite_norm V U (rightFamily_norm _ (rootColumn_norm σ)) (rawJointKraus_norm η θ hη hθ τ))
    (fun x => (fixedPortEquiv n).hasSum_iff.mpr
      (composite_norm V U (rightFamily_norm _ (rootColumn_norm σ)) (rawJointKraus_norm η θ hη hθ τ) x)) Z
  simpa only [he] using hr.symm

theorem rawDual_second_slice {n : ℕ} (η θ : ℝ)
    (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (ρ τ : State n)
    (Z : Fock n →L[ℂ] Fock n) :
    conditionalRight (rootColumn ρ) (rootColumn_norm ρ) (rawDual η θ hη hθ τ Z)=
      dual (composeKraus (firstKraus θ hθ τ) (secondKraus η hη ρ))
        (composeKraus_norm _ _ (firstKraus_norm θ hθ τ) (secondKraus_norm η hη ρ)) Z := by
  let V := fun j => tensorLeft (B := NumberIndex n) (rootColumn ρ j)
  let U := rawJointKraus η θ hη hθ τ
  have hh := dual_composite V U (leftFamily_norm _ (rootColumn_norm ρ))
    (rawJointKraus_norm η θ hη hθ τ) Z
  change dual V _ (dual U _ Z)=_
  rw [← hh]
  have he : (fun k => composite V U (fixedPortEquiv n k))=
      composeKraus (firstKraus θ hθ τ) (secondKraus η hη ρ) := by
    funext k
    ext z
    rfl
  have hr := dual_reindex (fixedPortEquiv n) (composite V U)
    (composite_norm V U (leftFamily_norm _ (rootColumn_norm ρ)) (rawJointKraus_norm η θ hη hθ τ))
    (fun x => (fixedPortEquiv n).hasSum_iff.mpr
      (composite_norm V U (leftFamily_norm _ (rootColumn_norm ρ)) (rawJointKraus_norm η θ hη hθ τ) x)) Z
  simpa only [he] using hr.symm
end EntropyPhotonNumber

end

end OAI
