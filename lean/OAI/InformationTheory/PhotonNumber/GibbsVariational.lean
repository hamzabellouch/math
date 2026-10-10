import OAI.InformationTheory.PhotonNumber.Entropy

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal

namespace QuantumTrace

section
open scoped BigOperators
open Filter Topology

theorem negMulLog_lt_crossEntropy {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hne : p ≠ q) :
    Real.negMulLog p < q - p + p * (-Real.log q) := by
  by_cases hz : p = 0
  · simp [hz, hq]
  have hneq : p/q ≠ 1 := by
    intro h
    exact hne ((div_eq_one_iff_eq hq.ne').mp h)
  have h := mul_lt_mul_of_pos_left
    (Real.negMulLog_lt_one_sub_self (div_nonneg hp hq.le) hneq) hq
  change q * (-(p / q) * Real.log (p / q)) < q * (1 - p / q) at h
  rw [Real.log_div hz hq.ne'] at h
  have hl : q * (-(p / q) * (Real.log p - Real.log q)) =
      -p * Real.log p + p * Real.log q := by field_simp; ring
  have hr : q * (1 - p / q) = q - p := by field_simp
  rw [hl, hr] at h
  dsimp [Real.negMulLog]
  linarith

structure StochasticOverlap (I J : Type*) where
  value : I → J → ℝ
  nonneg : ∀ i j, 0 ≤ value i j
  row : ∀ i, HasSum (value i) 1
  col : ∀ j, HasSum (fun i => value i j) 1

namespace StochasticOverlap
variable {I J : Type*} (a : StochasticOverlap I J)

theorem hasSum_row_product (p : I → ℝ) {s : ℝ} (hp : HasSum p s) :
    HasSum (fun ij : I × J => a.value ij.1 ij.2 * p ij.1) s := by
  have hs : Summable (fun ij : I × J => a.value ij.1 ij.2 * p ij.1) := by
    apply Summable.of_norm
    apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
    constructor
    · intro i
      simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (a.nonneg i _)] using
        (a.row i).summable.mul_right |p i|
    · simp_rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (a.nonneg _ _),
        tsum_mul_right, (a.row _).tsum_eq, one_mul]
      exact hp.summable.norm
  convert hs.hasSum using 1
  rw [hs.tsum_prod]
  simp only [tsum_mul_right, (a.row _).tsum_eq, one_mul, hp.tsum_eq]

def transpose : StochasticOverlap J I where
  value j i := a.value i j
  nonneg j i := a.nonneg i j
  row := a.col
  col := a.row

theorem hasSum_col_product (q : J → ℝ) {s : ℝ} (hq : HasSum q s) :
    HasSum (fun ij : I × J => a.value ij.1 ij.2 * q ij.2) s := by
  exact (Equiv.prodComm J I).hasSum_iff.mp (a.transpose.hasSum_row_product q hq)

theorem hasSum_prod_nonneg {v : I × J → ℝ} {c : I → ℝ} {s : ℝ}
    (hv : ∀ ij, 0 ≤ v ij) (hf : ∀ i, HasSum (fun j => v (i,j)) (c i))
    (hc : HasSum c s) : HasSum v s := by
  have hs : Summable v := (summable_prod_of_nonneg hv).mpr
    ⟨fun i => (hf i).summable, by simpa only [(hf _).tsum_eq] using hc.summable⟩
  convert hs.hasSum using 1
  rw [hs.tsum_prod]
  simp only [(hf _).tsum_eq, hc.tsum_eq]

def diagonal (p : I → ℝ) (j : J) : ℝ := ∑' i, a.value i j * p i

theorem hasSum_crossEntropy {p : I → ℝ} {q : J → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hp1 : HasSum p 1)
    (hq : ∀ j, 0 < q j) (hq1 : HasSum q 1)
    {C : ℝ} (hc : HasSum (fun j => a.diagonal p j * (-Real.log (q j))) C) :
    HasSum (fun ij : I × J => a.value ij.1 ij.2 * p ij.1 * (-Real.log (q ij.2))) C := by
  have hpairs := a.hasSum_row_product p hp1
  have hl (j : J) : 0 ≤ -Real.log (q j) := by
    apply neg_nonneg.mpr
    apply Real.log_nonpos (hq j).le
    rw [← hq1.tsum_eq]
    exact hq1.summable.le_tsum j (fun j _ => (hq j).le)
  apply (Equiv.prodComm J I).hasSum_iff.mp
  apply hasSum_prod_nonneg (c := fun j => a.diagonal p j * (-Real.log (q j)))
    (fun ji => mul_nonneg (mul_nonneg (a.nonneg _ _) (hp _)) (hl _)) _ hc
  intro j
  exact (hpairs.summable.prod_symm.prod_factor j).hasSum.mul_right _

theorem klein {p : I → ℝ} {q : J → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hp1 : HasSum p 1)
    (hq : ∀ j, 0 < q j) (hq1 : HasSum q 1)
    {H C : ℝ} (hh : HasSum (fun i => Real.negMulLog (p i)) H)
    (hc : HasSum (fun j => a.diagonal p j * (-Real.log (q j))) C) :
    H ≤ C ∧ (H = C → ∀ i j, a.value i j ≠ 0 → p i = q j) := by
  let d (ij : I × J) : ℝ := a.value ij.1 ij.2 *
    (q ij.2 - p ij.1 + p ij.1 * (-Real.log (q ij.2)) - Real.negMulLog (p ij.1))
  have hd (ij : I × J) : 0 ≤ d ij :=
    mul_nonneg (a.nonneg _ _) (sub_nonneg.mpr (negMulLog_le_crossEntropy (hp _) (hq _)))
  have hdSum : HasSum d (C-H) := by
    have h := (((a.hasSum_col_product q hq1).sub (a.hasSum_row_product p hp1)).add
      (a.hasSum_crossEntropy hp hp1 hq hq1 hc)).sub
      (a.hasSum_row_product (fun i => Real.negMulLog (p i)) hh)
    convert! h using 1
    · funext ij
      dsimp [d]
      ring
    · ring
  refine ⟨sub_nonneg.mp (hdSum.tsum_eq ▸ tsum_nonneg hd), ?_⟩
  intro he i j ha
  by_contra hne
  have hpos : 0 < d (i,j) := mul_pos (lt_of_le_of_ne (a.nonneg i j) (Ne.symm ha))
    (sub_pos.mpr (negMulLog_lt_crossEntropy (hp i) (hq j) hne))
  have hx := hdSum.summable.le_tsum (i,j) (fun ij _ => hd ij)
  rw [hdSum.tsum_eq, he, sub_self] at hx
  exact (not_lt_of_ge hx) hpos

end StochasticOverlap
end

section
open scoped BigOperators
variable {I J : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def basisOverlap (b : HilbertBasis I ℂ E) (c : HilbertBasis J ℂ E) :
    StochasticOverlap I J where
  value i j := ‖inner ℂ (c j) (b i)‖ ^ 2
  nonneg _ _ := sq_nonneg _
  row i := by
    simpa only [b.orthonormal.norm_eq_one, one_pow] using basis_hasSum_norm_sq c (b i)
  col j := by
    simpa only [norm_inner_symm, c.orthonormal.norm_eq_one, one_pow] using
      basis_hasSum_norm_sq b (c j)

theorem basisOverlap_diagonal (b : HilbertBasis I ℂ E) (c : HilbertBasis J ℂ E)
    (T : E →L[ℂ] E) (p : I → ℝ) (he : ∀ i, T (b i) = (p i : ℂ) • b i) (j : J) :
    (basisOverlap b c).diagonal p j = (inner ℂ (c j) (T (c j))).re := by
  have hh := hasSum_quadratic_eigenbasis b T p he (c j)
  simpa only [StochasticOverlap.diagonal, basisOverlap, norm_inner_symm, mul_comm] using hh.tsum_eq

theorem quantum_klein (b : HilbertBasis I ℂ E) (c : HilbertBasis J ℂ E)
    {T S : E →L[ℂ] E} (hs : S.IsSymmetric)
    {p : I → ℝ} {q : J → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : HasSum p 1)
    (hq : ∀ j, 0 < q j) (hq1 : HasSum q 1)
    (heT : ∀ i, T (b i) = (p i : ℂ) • b i)
    (heS : ∀ j, S (c j) = (q j : ℂ) • c j)
    {H C : ℝ} (hh : HasSum (fun i => Real.negMulLog (p i)) H)
    (hc : HasSum (fun j => (inner ℂ (c j) (T (c j))).re * (-Real.log (q j))) C) :
    H ≤ C ∧ (H = C → T = S) := by
  have hcc : HasSum (fun j => (basisOverlap b c).diagonal p j * (-Real.log (q j))) C := by
    simpa only [basisOverlap_diagonal b c T p heT] using hc
  obtain ⟨hle, heq⟩ := (basisOverlap b c).klein hp hp1 hq hq1 hh hcc
  refine ⟨hle, ?_⟩
  intro he
  have hcoef (i : I) (j : J) :
      (q j : ℂ) * inner ℂ (c j) (b i) = (p i : ℂ) * inner ℂ (c j) (b i) := by
    by_cases hz : inner ℂ (c j) (b i) = 0
    · simp [hz]
    · rw [heq he i j (by simpa only [basisOverlap, ne_eq, sq_eq_zero_iff,
          norm_eq_zero] using hz)]
  have hb (i : I) : T (b i) = S (b i) := by
    apply c.repr.injective
    apply lp.ext
    funext j
    simp only [c.repr_apply_apply, heT, inner_smul_right]
    have hsym : inner ℂ (S (c j)) (b i) = inner ℂ (c j) (S (b i)) := hs _ _
    rw [← hsym, heS, inner_smul_left]
    simpa only [Complex.conj_ofReal] using (hcoef i j).symm
  ext x
  have ht := T.hasSum (b.hasSum_repr x)
  have hu := S.hasSum (b.hasSum_repr x)
  apply ht.unique
  convert hu using 1
  funext i
  simp only [ContinuousLinearMap.map_smul, hb]

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

theorem hasSum_entropy_eigenvalues (a : HilbertBasis I ℂ E) (b : HilbertBasis J ℂ E)
    {T : E →L[ℂ] E} (hp : T.IsPositive)
    (ht : HasSum (fun i => (inner ℂ (a i) (T (a i))).re) 1)
    (p : J → ℝ) (he : ∀ j, T (b j) = (p j : ℂ) • b j) {S : ℝ}
    (hS : HasSum (fun i => (inner ℂ (a i) (entropyOperator T (a i))).re) S) :
    HasSum (fun j => Real.negMulLog (p j)) S := by
  have hh := hasSum_trace_basis a b (entropyOperator_positive hp (norm_le_trace a hp ht)) hS
  have hev (j : J) : (inner ℂ (b j) (entropyOperator T (b j))).re = Real.negMulLog (p j) := by
    rw [entropyOperator_apply_eigenvector hp.isSymmetric (he j), inner_smul_right,
      inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
    simp
  simpa only [hev] using hh

theorem spectral_gibbs_variational [Nonempty J] (a : HilbertBasis I ℂ E)
    (b : HilbertBasis J ℂ E) (u : J → ℝ)
    (hheat : Summable (fun j => Real.exp (-u j)))
    {T : E →L[ℂ] E} (hp : T.IsPositive)
    (ht : HasSum (fun i => (inner ℂ (a i) (T (a i))).re) 1)
    {S K : ℝ} (hS : HasSum (fun i => (inner ℂ (a i) (entropyOperator T (a i))).re) S)
    (hK : HasSum (fun j => u j*(inner ℂ (b j) (T (b j))).re) K) :
    -Real.log (heatPartition u) ≤ K-S ∧
      (K-S = -Real.log (heatPartition u) → T = spectralGibbs b u hheat) := by
  obtain ⟨L, c, p, hpp, hpt, heT⟩ := exists_positive_eigenbasis a hp ht
  have hSp := hasSum_entropy_eigenvalues a c hp ht p heT hS
  have ht' := hasSum_trace_basis a b hp ht
  have hcross : HasSum (fun j => (inner ℂ (b j) (T (b j))).re * (-Real.log (gibbsWeight u j)))
      (K+Real.log (heatPartition u)) := by
    have hh := hK.add (ht'.mul_right (Real.log (heatPartition u)))
    convert! hh using 1
    · funext j
      rw [log_gibbsWeight u hheat]
      ring
    · ring
  obtain ⟨hle, heq⟩ := quantum_klein c b (spectralGibbs_positive b u hheat).isSymmetric
    hpp hpt (gibbsWeight_pos u hheat) (gibbsWeight_hasSum u hheat)
    heT (spectralGibbs_eigen b u hheat) hSp hcross
  exact ⟨by linarith, fun hh => heq (by linarith)⟩

end

variable {J : Type*}

theorem spectral_gibbs_attains {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [Nonempty J] {I : Type*} (a : HilbertBasis I ℂ E)
    (b : HilbertBasis J ℂ E) (u : J → ℝ) (hu : ∀ j, 0 ≤ u j)
    (hheat : Summable (fun j => Real.exp (-u j)))
    (hhalf : Summable (fun j => Real.exp (-(1/2 : ℝ)*u j))) :
    let ω := spectralGibbs b u hheat
    Summable (fun j => u j*(inner ℂ (b j) (ω (b j))).re) ∧
      Summable (fun i => (inner ℂ (a i) (entropyOperator ω (a i))).re) ∧
      (∑' j, u j*(inner ℂ (b j) (ω (b j))).re) -
        (∑' i, (inner ℂ (a i) (entropyOperator ω (a i))).re) = -Real.log (heatPartition u) := by
  let ω := spectralGibbs b u hheat
  have he (j : J) : (inner ℂ (b j) (ω (b j))).re = gibbsWeight u j := by
    rw [show ω = spectralGibbs b u hheat from rfl, spectralGibbs_eigen,
      inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
    simp
  have hE : Summable (fun j => u j*gibbsWeight u j) := by
    have hh : Summable (fun j => Real.exp (-u j)*u j) := by
      apply Summable.of_nonneg_of_le (fun j => mul_nonneg (Real.exp_nonneg _) (hu j)) _
        (summable_polynomial_heat u hu hhalf)
      intro j
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      nlinarith [sq_nonneg (u j-1)]
    apply (hh.div_const (heatPartition u)).congr
    intro j
    dsimp [gibbsWeight]
    ring
  have hH : HasSum (fun j => Real.negMulLog (gibbsWeight u j))
      ((∑' j, u j*gibbsWeight u j)+Real.log (heatPartition u)) := by
    have hh := hE.hasSum.add ((gibbsWeight_hasSum u hheat).mul_right (Real.log (heatPartition u)))
    convert! hh using 1
    · funext j
      rw [show Real.negMulLog (gibbsWeight u j) = gibbsWeight u j * (-Real.log (gibbsWeight u j)) by
        rw [Real.negMulLog]; ring, log_gibbsWeight u hheat]
      ring
    · ring
  have hHb : HasSum (fun j => (inner ℂ (b j) (entropyOperator ω (b j))).re)
      ((∑' j, u j*gibbsWeight u j)+Real.log (heatPartition u)) := by
    convert! hH using 1
    funext j
    rw [entropyOperator_apply_eigenvector (spectralGibbs_positive b u hheat).isSymmetric
      (spectralGibbs_eigen b u hheat j), inner_smul_right, inner_self_eq_norm_sq_to_K,
      b.orthonormal.norm_eq_one]
    simp
  have hHa := hasSum_trace_basis b a
    (entropyOperator_positive (spectralGibbs_positive b u hheat)
      (norm_le_trace b (spectralGibbs_positive b u hheat) (spectralGibbs_trace_one b u hheat b))) hHb
  refine ⟨?_, hHa.summable, ?_⟩
  · change Summable (fun j => u j*(inner ℂ (b j) (ω (b j))).re)
    simpa only [he] using hE
  · change (∑' j, u j*(inner ℂ (b j) (ω (b j))).re) - _ = _
    simp only [he, hHa.tsum_eq]
    ring

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace

def crossEntropy {n : ℕ} {J : Type*} (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (σ : State n) : ℝ :=
  ∑' j, (-Real.log (p j))*(inner ℂ (b j) (σ.op (b j))).re

theorem entropy_hasSum {n : ℕ} (ρ : State n) (hρ : FiniteEnergy ρ) :
    HasSum (fun k => (inner ℂ (numberBasis n k) (entropyOperator ρ.op (numberBasis n k))).re)
      (entropy ρ) := by
  rw [entropy_eq_quantumTrace]
  have hh := (entropy_summable ρ hρ)
  simpa only [entropyOperator_eq_complex ρ.positive.isSymmetric, numberBasis_apply, entry]
    using hh.hasSum

theorem entropy_le_crossEntropy {n : ℕ} (ρ σ : State n) (hσ : FiniteEnergy σ)
    {J : Type*} (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (hc : Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (σ.op (b j))).re)) :
    entropy σ ≤ crossEntropy b p σ ∧
      (entropy σ = crossEntropy b p σ → σ = ρ) := by
  obtain ⟨I, a, q, hq, hqt, hqe⟩ := exists_positive_eigenbasis (numberBasis n)
    σ.positive (trace_one_numberBasis σ)
  have hS := hasSum_entropy_eigenvalues (numberBasis n) a σ.positive
    (trace_one_numberBasis σ) q hqe (entropy_hasSum σ hσ)
  have hC : HasSum (fun j => (inner ℂ (b j) (σ.op (b j))).re*(-Real.log (p j)))
      (crossEntropy b p σ) := by
    simpa only [crossEntropy, mul_comm] using hc.hasSum
  obtain ⟨hle, heq⟩ := quantum_klein a b ρ.positive.isSymmetric hq hqt hp hs hqe he hS hC
  exact ⟨hle, fun h => state_ext (heq h)⟩

theorem crossEntropy_self {n : ℕ} (ρ : State n) (hρ : FiniteEnergy ρ)
    {J : Type*} (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) :
    crossEntropy b p ρ = entropy ρ := by
  have h := hasSum_entropy_eigenvalues (numberBasis n) b ρ.positive
    (trace_one_numberBasis ρ) p he (entropy_hasSum ρ hρ)
  rw [crossEntropy, ← h.tsum_eq]
  congr 1
  funext j
  rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
  simp [Real.negMulLog]
  ring

theorem crossEntropy_finite {n : ℕ} (ρ σ : State n) (hσ : FiniteEnergy σ)
    {r κ : ℝ} (hr : 0 < r) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hle : (κ : ℂ) • (thermalState n r hr).op ≤ ρ.op)
    {J : Type*} (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) :
    Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (σ.op (b j))).re) := by
  have hp1 (j : J) : p j ≤ 1 := hs.tsum_eq ▸ hs.summable.le_tsum j (fun i _ => (hp i).le)
  have hw (j : J) : 0 ≤ -Real.log (p j) := neg_nonneg.mpr (Real.log_nonpos (hp j).le (hp1 j))
  apply (basisExpectation_finite_iff b _ hw σ.positive).mp
  have hh := negativeLog_expectation_le_thermal ρ σ hr hκ hκ1 hle b p hp hs he
  have hhE : basisExpectation (numberBasis n) (fun k => (totalNumber k : ℝ≥0∞)) σ.op =
      ENNReal.ofReal (energy σ) := by
    have hh := basisExpectation_ofReal (numberBasis n) (fun k => (totalNumber k : ℝ))
      (fun _ => Nat.cast_nonneg _) σ.positive (by
        simpa only [FiniteEnergy, numberBasis_apply, entry] using hσ)
    simpa only [ENNReal.ofReal_natCast, energy, numberBasis_apply, entry] using hh
  rw [hhE] at hh
  exact hh.trans_lt (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top⟩)

end EntropyPhotonNumber

namespace QuantumTrace
variable {n : ℕ} {J : Type*} [Nonempty J]

theorem spectralGibbs_seventh_moment
    (b : HilbertBasis J ℂ (SequenceHilbert (Fin n → ℕ))) (u : J → ℝ)
    (hu : ∀ j, 0 < u j) {k : ℝ} (hk : 0 < k)
    {B : SequenceHilbert (Fin n → ℕ) →L[ℂ] SequenceHilbert (Fin n → ℕ)}
    (hheat : Summable (fun j => Real.exp (-u j)))
    (hhalf : Summable (fun j => Real.exp (-(1/2 : ℝ)*u j)))
    (hreg : ∀ j, ∃ z : SequenceHilbert (Fin n → ℕ),
      (∀ i, z i = (rootNumberWeight i^7 : ℝ)*b j i) ∧
      ‖z‖ ≤ k⁻¹*(u j+‖B‖*Real.sqrt (u j/k))) :
    Summable (fun i => numberWeight i^7 *
      (inner ℂ (sequenceBasis _ i) (spectralGibbs b u hheat (sequenceBasis _ i))).re) := by
  choose z hz hzs using hreg
  have hn : Summable (fun j => Real.exp (-u j)*‖z j‖^2) :=
    gibbs_high_moment_summable u (fun j => (hu j).le) hk (norm_nonneg B)
      (fun j => ‖z j‖) (fun j => norm_nonneg _) hzs hhalf
  have hw : Summable (fun j => gibbsWeight u j*‖z j‖^2) := by
    apply (hn.div_const (heatPartition u)).congr
    intro j
    dsimp [gibbsWeight]
    ring
  apply weighted_number_moment b (spectralGibbs b u hheat) (gibbsWeight u)
    (fun j => (gibbsWeight_pos u hheat j).le) (spectralGibbs_eigen b u hheat)
    (fun i => numberWeight i^7) (fun i => pow_nonneg (by linarith [numberWeight_one_le i]) _)
    (fun j => ‖z j‖^2) _ hw
  intro j
  have heq : (fun i => ‖z j i‖^2) = (fun i => numberWeight i^7*‖b j i‖^2) := by
    funext i
    rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity [rootNumberWeight_one_le i]), mul_pow]
    congr 1
    rw [← pow_mul, show (7*2 : ℕ) = 2*7 from rfl, pow_mul, rootNumberWeight,
      Real.sq_sqrt (by linarith [numberWeight_one_le i])]
  rw [← heq]
  exact sequence_hasSum_norm_sq (z j)

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace
theorem exists_gibbs_state (n : ℕ) {k : ℝ} (hk : 0 < k)
    {B : Fock n →L[ℂ] Fock n} (hB : B.IsPositive) :
    ∃ (J : Type) (_ : Nonempty J) (b : HilbertBasis J ℂ (Fock n)) (u : J → ℝ)
      (hheat : Summable (fun j => Real.exp (-u j))) (ω : State n),
      (∀ j, 0 < u j) ∧
      (∀ j, gibbsInverse rootNumberWeight rootNumberWeight_one_le k B (b j) =
        (((u j)⁻¹ : ℝ) : ℂ) • b j) ∧
      (∀ t : ℝ, 0 < t → Summable (fun j => Real.exp (-t*u j))) ∧
      ω.op = spectralGibbs b u hheat ∧ Function.Injective ω.op ∧ FiniteMoment 7 ω := by
  classical
  obtain ⟨J,b,u,hu,he,hreg,hheat⟩ := gibbs_fock_spectral_regular n hk hB
  have hJ : Nonempty J := by
    by_contra h
    have : IsEmpty J := not_nonempty_iff.mp h
    have hh := (basis_hasSum_norm_sq b (numberKet (fun _ : Fin n => 0))).tsum_eq
    simp only [tsum_empty] at hh
    have hn : ‖numberKet (fun _ : Fin n => 0)‖ = 1 := by simp [numberKet]
    rw [hn, one_pow] at hh
    exact zero_ne_one hh
  let _ := hJ
  have ht : Summable (fun j => Real.exp (-u j)) := by simpa using hheat 1 (by norm_num)
  let T := spectralGibbs b u ht
  have hT : T.IsPositive := spectralGibbs_positive b u ht
  have hs : HasSum (fun i => (entry T i i).re) 1 := by
    simpa only [sequenceBasis_numberKet, entry] using
      spectralGibbs_trace_one b u ht (sequenceBasis (NumberIndex n))
  let ω : State n := ⟨T,hT,hs⟩
  refine ⟨J,hJ,b,u,ht,ω,hu,he,hheat,rfl,spectralGibbs_injective b u ht,?_⟩
  have hm := spectralGibbs_seventh_moment b u hu hk ht (hheat (1/2) (by norm_num))
    (B := B) (fun j => by obtain ⟨y,z,_,hz,_,hzs⟩ := hreg j; exact ⟨z,hz,hzs⟩)
  simpa only [FiniteMoment, numberWeight_eq, sequenceBasis_numberKet, entry] using hm

end

section
open QuantumTrace TraceEnsemble

theorem gibbs_slice_real_trace {n : ℕ} {J L K I : Type*}
    (c : HilbertBasis L ℂ (Fock n)) (u : L → ℝ) (hu : ∀ l, 0 < u l)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : HasSum p 1)
    (ρ : State n) (heρ : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (hm : FiniteMoment 4 ρ)
    (a : HilbertBasis K ℂ (Fock n)) (w : K → ℝ) (hw : ∀ j, 0 ≤ w j)
    (V : I → Fock n →L[ℂ] Fock n) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (σ : State n)
    (heσ : TraceEnsemble.operator (fun z : I × J => V z.1 (diagonalVector b p z.2)) = σ.op)
    (hc : Summable (fun j => w j*(inner ℂ (a j) (σ.op (a j))).re))
    {B : Fock n →L[ℂ] Fock n} (hB : B.IsPositive) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hform : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re =
      ENNReal.ofReal α*sliceMoment a (fun j => ENNReal.ofReal (w j)) V (energyInverse n x)+
      ENNReal.ofReal β*numberVectorMoment (energyInverse n x))
    {k : ℝ} (hk : 0 < k)
    (heK : ∀ l, gibbsInverse rootNumberWeight rootNumberWeight_one_le k B (c l) =
      (((u l)⁻¹ : ℝ) : ℂ) • c l) :
    HasSum (fun l => u l*(inner ℂ (c l) (ρ.op (c l))).re)
      (k*numberMoment 4 ρ + α*(∑' j, w j*(inner ℂ (a j) (σ.op (a j))).re) + β*energy ρ) := by
  obtain ⟨E,hE,he⟩ := gibbs_slice_trace c u hu b p hp hs ρ heρ hm a
    (fun j => ENNReal.ofReal (w j)) V hV σ heσ hB hform hk heK
  have hE0 : 0 ≤ E := hE.tsum_eq ▸ tsum_nonneg
    (fun j => mul_nonneg (hu j).le (ρ.positive.re_inner_nonneg_right _))
  have hc0 : 0 ≤ ∑' j, w j*(inner ℂ (a j) (σ.op (a j))).re :=
    tsum_nonneg (fun j => mul_nonneg (hw j) (σ.positive.re_inner_nonneg_right _))
  rw [basisExpectation_ofReal a w hw σ.positive hc,
    ← ENNReal.ofReal_mul hk.le, ← ENNReal.ofReal_mul hα, ← ENNReal.ofReal_mul hβ,
    ← ENNReal.ofReal_add (mul_nonneg hα hc0) (mul_nonneg hβ (energy_nonneg ρ)),
    ← ENNReal.ofReal_add (mul_nonneg hk.le (numberMoment_nonneg 4 ρ))
      (add_nonneg (mul_nonneg hα hc0) (mul_nonneg hβ (energy_nonneg ρ)))] at he
  have he' := (ENNReal.ofReal_eq_ofReal_iff hE0
    (add_nonneg (mul_nonneg hk.le (numberMoment_nonneg 4 ρ))
      (add_nonneg (mul_nonneg hα hc0) (mul_nonneg hβ (energy_nonneg ρ))))).mp he
  simpa only [he', add_assoc] using hE

def sliceFreeEnergy {n : ℕ} {K : Type*} (a : HilbertBasis K ℂ (Fock n)) (w : K → ℝ)
    (Φ : State n → State n) (k α β : ℝ) (ρ : State n) : ℝ :=
  k*numberMoment 4 ρ + α*(∑' j, w j*(inner ℂ (a j) ((Φ ρ).op (a j))).re) +
    β*energy ρ - entropy ρ

theorem sliced_gibbs_minimizer {n : ℕ} {K I : Type*}
    (a : HilbertBasis K ℂ (Fock n)) (w : K → ℝ) (hw : ∀ j, 0 ≤ w j)
    (V : I → Fock n →L[ℂ] Fock n) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (Φ : State n → State n)
    (hΦ : ∀ (J : Type) (v : J → Fock n) (ρ : State n),
      HasSum (fun j => ‖v j‖^2) 1 → operator v = ρ.op →
      operator (fun z : I × J => V z.1 (v z.2)) = (Φ ρ).op)
    (hc : ∀ ρ, FiniteMoment 4 ρ →
      Summable (fun j => w j*(inner ℂ (a j) ((Φ ρ).op (a j))).re))
    {B : Fock n →L[ℂ] Fock n} (hB : B.IsPositive) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hform : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re =
      ENNReal.ofReal α*sliceMoment a (fun j => ENNReal.ofReal (w j)) V (energyInverse n x)+
      ENNReal.ofReal β*numberVectorMoment (energyInverse n x))
    {k : ℝ} (hk : 0 < k) (ρ : State n) (hm : FiniteMoment 4 ρ)
    (hmin : ∀ σ, FiniteMoment 4 σ → sliceFreeEnergy a w Φ k α β ρ ≤ sliceFreeEnergy a w Φ k α β σ) :
    ∃ (J : Type) (_ : Nonempty J) (b : HilbertBasis J ℂ (Fock n)) (u : J → ℝ)
      (hheat : Summable (fun j => Real.exp (-u j))),
      (∀ j, 0 < u j) ∧
      (∀ j, gibbsInverse rootNumberWeight rootNumberWeight_one_le k B (b j) =
        (((u j)⁻¹ : ℝ) : ℂ) • b j) ∧
      ρ.op = spectralGibbs b u hheat ∧ Function.Injective ρ.op ∧ FiniteMoment 7 ρ := by
  classical
  obtain ⟨J,hJ,b,u,ht,ω,hu,he,hheat,hω,hinj,hmω⟩ := exists_gibbs_state n hk hB
  let _ := hJ
  have htrace (σ : State n) (hmσ : FiniteMoment 4 σ) :
      HasSum (fun j => u j*(inner ℂ (b j) (σ.op (b j))).re)
        (k*numberMoment 4 σ + α*(∑' j, w j*(inner ℂ (a j) ((Φ σ).op (a j))).re) + β*energy σ) := by
    obtain ⟨L,c,p,hp,hs,heσ⟩ := exists_positive_eigenbasis (numberBasis n)
      σ.positive (trace_one_numberBasis σ)
    have hv : HasSum (fun j => ‖diagonalVector c p j‖^2) 1 := by
      simpa only [diagonalVector_norm_sq c p hp] using hs
    exact gibbs_slice_real_trace b u hu c p hp hs σ heσ hmσ a w hw V hV (Φ σ)
      (hΦ L _ σ hv (diagonalVector_operator c p hp hs.summable σ.op heσ)) (hc σ hmσ)
      hB hα hβ hform hk he
  have hmω4 := finiteMoment_mono (by norm_num : 4 ≤ 7) hmω
  have htρ := htrace ρ hm
  have hVρ := spectral_gibbs_variational (numberBasis n) b u ht ρ.positive
    (trace_one_numberBasis ρ) (entropy_hasSum ρ (finiteMoment_finiteEnergy (by norm_num) hm)) htρ
  have hωatt := spectral_gibbs_attains (numberBasis n) b u (fun j => (hu j).le) ht
    (hheat (1/2) (by norm_num))
  have hSω : HasSum (fun i => (inner ℂ ((numberBasis n) i)
      (entropyOperator ω.op ((numberBasis n) i))).re) (entropy ω) :=
    entropy_hasSum ω (finiteMoment_finiteEnergy (by norm_num) hmω4)
  have hωeq : sliceFreeEnergy a w Φ k α β ω = -Real.log (heatPartition u) := by
    dsimp only at hωatt
    rw [← hω] at hωatt
    rw [(htrace ω hmω4).tsum_eq, hSω.tsum_eq] at hωatt
    exact hωatt.2.2
  have heq : sliceFreeEnergy a w Φ k α β ρ = -Real.log (heatPartition u) :=
    le_antisymm ((hmin ω hmω4).trans_eq hωeq) hVρ.1
  have hρop := hVρ.2 heq
  have hρω : ρ = ω := state_ext (hρop.trans hω.symm)
  exact ⟨J,hJ,b,u,ht,hu,he,hρop,by simpa only [hρω] using hinj,by simpa only [hρω] using hmω⟩

end

section
open QuantumTrace

theorem crossEntropy_mixture {n : ℕ} {J : Type*} (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (t : ℝ) (ht : t ∈ Set.Icc 0 1) (ρ σ : State n)
    (hρ : Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (ρ.op (b j))).re))
    (hσ : Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (σ.op (b j))).re)) :
    crossEntropy b p (mixture t ht ρ σ) = t*crossEntropy b p ρ+(1-t)*crossEntropy b p σ := by
  have hh := (hρ.hasSum.mul_left t).add (hσ.hasSum.mul_left (1-t))
  have hf (j : J) : (-Real.log (p j))*(inner ℂ (b j) ((mixture t ht ρ σ).op (b j))).re =
      t*((-Real.log (p j))*(inner ℂ (b j) (ρ.op (b j))).re)+
      (1-t)*((-Real.log (p j))*(inner ℂ (b j) (σ.op (b j))).re) := by
    simp only [mixture, add_apply, smul_apply, inner_add_right, inner_smul_right,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  unfold crossEntropy
  simpa only [hf] using hh.tsum_eq

theorem one_port_majorant {n : ℕ} {J : Type*}
    (Φ : State n → State n) (τ : State n) (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1)
    (c a β ζ : ℝ) (hc : 0 < c) (ha : 0 < a)
    (ρ : State n) (hmρ : FiniteMoment 4 ρ)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (Φ ρ) τ).op (b j) =
      (p j : ℂ) • b j)
    (hfinite : ∀ σ, FiniteMoment 4 σ → FiniteEnergy (Φ σ)) (hτ : FiniteEnergy τ)
    (hcross : ∀ σ, FiniteMoment 4 σ →
      Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) ((Φ σ).op (b j))).re))
    (hcτ : Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (τ.op (b j))).re))
    (hmin : ∀ σ, FiniteMoment 4 σ →
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (Φ ρ) τ)-a*entropy ρ+
        β*energy ρ+ζ*numberMoment 4 ρ ≤
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (Φ σ) τ)-a*entropy σ+
        β*energy σ+ζ*numberMoment 4 σ) :
    ∀ σ, FiniteMoment 4 σ →
      sliceFreeEnergy b (fun j => -Real.log (p j)) Φ (ζ/a) (c*(1-κ)/a) (β/a) ρ ≤
      sliceFreeEnergy b (fun j => -Real.log (p j)) Φ (ζ/a) (c*(1-κ)/a) (β/a) σ := by
  let ht : 1-κ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩
  let ρ0 := mixture (1-κ) ht (Φ ρ) τ
  have hself := crossEntropy_self ρ0 (mixture_finiteEnergy _ _ (hfinite ρ hmρ) hτ) b p he
  have hmixρ := crossEntropy_mixture b p (1-κ) ht (Φ ρ) τ (hcross ρ hmρ) hcτ
  intro σ hmσ
  have hmixσ := crossEntropy_mixture b p (1-κ) ht (Φ σ) τ (hcross σ hmσ) hcτ
  have hcσ : Summable (fun j => (-Real.log (p j))*(inner ℂ (b j)
      ((mixture (1-κ) ht (Φ σ) τ).op (b j))).re) := by
    convert! ((hcross σ hmσ).mul_left (1-κ)).add (hcτ.mul_left (1-(1-κ))) using 1
    funext j
    simp only [mixture, add_apply, smul_apply, inner_add_right, inner_smul_right,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have hmaj := (entropy_le_crossEntropy ρ0 (mixture (1-κ) ht (Φ σ) τ)
    (mixture_finiteEnergy _ _ (hfinite σ hmσ) hτ) b p hp hs he hcσ).1
  have hm := hmin σ hmσ
  have hρeq : c*entropy ρ0 = c*((1-κ)*crossEntropy b p (Φ ρ)+κ*crossEntropy b p τ) := by
    rw [← hself, hmixρ]
    congr 1
    ring
  have hσle : c*entropy (mixture (1-κ) ht (Φ σ) τ) ≤
      c*((1-κ)*crossEntropy b p (Φ σ)+κ*crossEntropy b p τ) := by
    have hh := mul_le_mul_of_nonneg_left hmaj hc.le
    rw [hmixσ] at hh
    simpa only [show 1-(1-κ) = κ by ring] using hh
  apply (mul_le_mul_iff_right₀ ha).mp
  have hscale (x : State n) :
      a*sliceFreeEnergy b (fun j => -Real.log (p j)) Φ (ζ/a) (c*(1-κ)/a) (β/a) x =
      ζ*numberMoment 4 x+c*(1-κ)*crossEntropy b p (Φ x)+β*energy x-a*entropy x := by
    dsimp [sliceFreeEnergy, crossEntropy]
    field_simp
  rw [hscale, hscale]
  change c*entropy ρ0-a*entropy ρ+β*energy ρ+ζ*numberMoment 4 ρ ≤ _ at hm
  rw [hρeq] at hm
  linarith

end

section
open QuantumTrace TensorLp

structure KrausFlow (n : ℕ) where
  I : Type
  V : I → Fock n →L[ℂ] Fock n
  norm : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2)
  F : ℝ
  nonneg : 0 ≤ F
  energy : ∀ x, (∑' i, vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (V i x)) ≤
    vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) x+ENNReal.ofReal F*ENNReal.ofReal (‖x‖^2)
  map : State n → State n
  ensemble : ∀ (J : Type) (v : J → Fock n) (ρ : State n),
    HasSum (fun j => ‖v j‖^2) 1 → TraceEnsemble.operator v = ρ.op →
    TraceEnsemble.operator (fun z : I × J => V z.1 (v z.2)) = (map ρ).op
  finiteEnergy : ∀ ρ, FiniteEnergy ρ → FiniteEnergy (map ρ)

theorem composedKraus_second_ensemble {n : ℕ} {J : Type*}
    (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (ρ σ τ : State n)
    (v : J → Fock n) (hv : HasSum (fun j => ‖v j‖^2) 1)
    (he : TraceEnsemble.operator v = σ.op) :
    TraceEnsemble.operator (fun z : ((NumberIndex n × NumberIndex n) ×
      (NumberIndex n × NumberIndex n)) × J =>
      composeKraus (firstKraus θ hθ τ) (secondKraus η hη ρ) z.1 (v z.2)) =
      (beamOutput θ hθ (beamOutput η hη ρ σ) τ).op := by
  have hV := TraceEnsemble.kraus_hasSum (secondKraus_norm η hη ρ) hv
  have heV := secondKraus_ensemble η hη ρ σ v hv he
  have heU := firstKraus_ensemble θ hθ (beamOutput η hη ρ σ) τ _ hV heV
  exact (composeKraus_ensemble (firstKraus θ hθ τ) (secondKraus η hη ρ) v).trans heU

namespace Regularization
variable {n : ℕ} (R : Regularization n)

def rawOutput (ρ σ : State n) : State n :=
  beamOutput (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2, sub_le_self _ R.hδ.1⟩
    (beamOutput R.η R.hη ρ σ) R.τD

def firstFlow (σ : State n) (hσ : FiniteEnergy σ) : KrausFlow n where
  I := (NumberIndex n × NumberIndex n) × (NumberIndex n × NumberIndex n)
  V := composeKraus (firstKraus (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2, sub_le_self _ R.hδ.1⟩ R.τD)
    (firstKraus R.η R.hη σ)
  norm := composeKraus_norm _ _ (firstKraus_norm _ _ _) (firstKraus_norm _ _ _)
  F := energy R.τD+energy σ
  nonneg := add_nonneg (energy_nonneg _) (energy_nonneg _)
  energy := by
    intro x
    have hh := composeKraus_energy
      (firstKraus (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2, sub_le_self _ R.hδ.1⟩ R.τD)
      (firstKraus R.η R.hη σ) (firstKraus_norm _ _ _) (firstKraus_energy _ _ _)
      (firstKraus_energy _ _ _) x
    simpa only [energyMoment_ofReal R.finiteD, energyMoment_ofReal hσ,
      ENNReal.ofReal_add (energy_nonneg R.τD) (energy_nonneg σ)] using hh
  map := fun ρ => R.rawOutput ρ σ
  ensemble := by
    intro J v ρ hv he
    exact composedKraus_first_ensemble _ _ _ _ ρ σ R.τD v hv he
  finiteEnergy := fun _ hρ => beamOutput_finiteEnergy _ _ (beamOutput_finiteEnergy _ _ hρ hσ) R.finiteD

def secondFlow (ρ : State n) (hρ : FiniteEnergy ρ) : KrausFlow n where
  I := (NumberIndex n × NumberIndex n) × (NumberIndex n × NumberIndex n)
  V := composeKraus (firstKraus (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2, sub_le_self _ R.hδ.1⟩ R.τD)
    (secondKraus R.η R.hη ρ)
  norm := composeKraus_norm _ _ (firstKraus_norm _ _ _) (secondKraus_norm _ _ _)
  F := energy R.τD+energy ρ
  nonneg := add_nonneg (energy_nonneg _) (energy_nonneg _)
  energy := by
    intro x
    have hh := composeKraus_energy
      (firstKraus (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2, sub_le_self _ R.hδ.1⟩ R.τD)
      (secondKraus R.η R.hη ρ) (secondKraus_norm _ _ _) (firstKraus_energy _ _ _)
      (secondKraus_energy _ _ _) x
    simpa only [energyMoment_ofReal R.finiteD, energyMoment_ofReal hρ,
      ENNReal.ofReal_add (energy_nonneg R.τD) (energy_nonneg ρ)] using hh
  map := fun σ => R.rawOutput ρ σ
  ensemble := by
    intro J v σ hv he
    exact composedKraus_second_ensemble _ _ _ _ ρ σ R.τD v hv he
  finiteEnergy := fun _ hσ => beamOutput_finiteEnergy _ _ (beamOutput_finiteEnergy _ _ hρ hσ) R.finiteD

end Regularization
end

section
open QuantumTrace
theorem flow_minimum_gibbs {n : ℕ} {J : Type*}
    (F : KrausFlow n) (τ : State n) {r : ℝ} (hr : 0 < r) (hτ : τ = thermalState n r hr)
    (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1) (hκ0 : 0 < κ)
    (c a β ζ : ℝ) (hc : 0 < c) (ha : 0 < a) (hβ : 0 ≤ β) (hζ : 0 < ζ)
    (ρ : State n) (hmρ : FiniteMoment 4 ρ)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ).op (b j) =
      (p j : ℂ) • b j)
    (hmin : ∀ σ, FiniteMoment 4 σ →
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ)-a*entropy ρ+
        β*energy ρ+ζ*numberMoment 4 ρ ≤
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map σ) τ)-a*entropy σ+
        β*energy σ+ζ*numberMoment 4 σ) :
    ∃ G : GibbsData n (ζ/a) ρ, ∀ x,
      ENNReal.ofReal (inner ℂ x (G.B x)).re =
        ENNReal.ofReal (c*(1-κ)/a)*
          sliceMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) F.V (energyInverse n x)+
        ENNReal.ofReal (β/a)*numberVectorMoment (energyInverse n x) := by
  let ht : 1-κ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩
  let ρ0 := mixture (1-κ) ht (F.map ρ) τ
  have hle : (κ : ℂ) • (thermalState n r hr).op ≤ ρ0.op := by
    rw [← hτ]
    exact mixture_replacement_le κ hκ (F.map ρ) τ
  have hf (σ : State n) (hm : FiniteMoment 4 σ) : FiniteEnergy (F.map σ) :=
    F.finiteEnergy σ (finiteMoment_finiteEnergy (by norm_num) hm)
  have hfτ : FiniteEnergy τ := by simpa only [hτ] using thermalState_finiteEnergy n r hr
  have hcross (σ : State n) (hm : FiniteMoment 4 σ) :
      Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) ((F.map σ).op (b j))).re) :=
    crossEntropy_finite ρ0 (F.map σ) (hf σ hm) hr hκ0 hκ.2 hle b p hp hs he
  have hcτ := crossEntropy_finite ρ0 τ hfτ hr hκ0 hκ.2 hle b p hp hs he
  have hα : 0 ≤ c*(1-κ)/a := div_nonneg (mul_nonneg hc.le (sub_nonneg.mpr hκ.2)) ha.le
  have hβ' : 0 ≤ β/a := div_nonneg hβ ha.le
  have hk : 0 < ζ/a := div_pos hζ ha
  have hw (j : J) : 0 ≤ -Real.log (p j) := neg_nonneg.mpr (Real.log_nonpos (hp j).le
    (hs.tsum_eq ▸ hs.summable.le_tsum j (fun i _ => (hp i).le)))
  obtain ⟨B,hB,hform⟩ := logarithmic_slice_representation ρ0 hr hκ0 hκ.2 hle b p hp hs he
    F.V F.F F.nonneg F.norm F.energy
  obtain ⟨C,hC,hCform⟩ := combined_form_representation b
    (fun j => ENNReal.ofReal (-Real.log (p j))) F.V hB hform hα hβ'
  have hm := one_port_majorant F.map τ κ hκ c a β ζ hc ha ρ hmρ b p hp hs he hf hfτ hcross hcτ hmin
  obtain ⟨L,hL,d,u,heat,hu,hinv,hop,hinj,hm7⟩ := sliced_gibbs_minimizer b
    (fun j => -Real.log (p j)) hw F.V F.norm F.map F.ensemble hcross hC hα hβ' hCform hk ρ hmρ hm
  let G : GibbsData n (ζ/a) ρ := ⟨C,hC,L,hL,d,u,hu,heat,hinv,hop,hinj,hm7⟩
  exact ⟨G,hCform⟩

namespace Regularization
variable {n : ℕ} (R : Regularization n)

theorem minimum_gibbs (ρ σ : State n) (hmρ : FiniteMoment 4 ρ) (hmσ : FiniteMoment 4 σ)
    {r : ℝ} (hr : 0 < r) (hτ : R.τ0 = thermalState n r hr) (hκ : 0 < R.κ)
    (hmin : ∀ ρ' σ', FiniteMoment 4 ρ' → FiniteMoment 4 σ' → R.objective ρ σ ≤ R.objective ρ' σ') :
    ∃ (J : Type) (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ),
      (∀ j, 0 < p j) ∧ HasSum p 1 ∧ (∀ j, (R.output ρ σ).op (b j) = (p j : ℂ) • b j) ∧
      ∃ (G1 : GibbsData n (R.ζ/R.a1) ρ) (G2 : GibbsData n (R.ζ/R.a2) σ),
        (∀ x, ENNReal.ofReal (inner ℂ x (G1.B x)).re =
          ENNReal.ofReal (R.c*(1-R.κ)/R.a1)*sliceMoment b (fun j => ENNReal.ofReal (-Real.log (p j)))
            (R.firstFlow σ (finiteMoment_finiteEnergy (by norm_num) hmσ)).V (energyInverse n x)+
          ENNReal.ofReal (R.b1/R.a1)*numberVectorMoment (energyInverse n x)) ∧
        (∀ x, ENNReal.ofReal (inner ℂ x (G2.B x)).re =
          ENNReal.ofReal (R.c*(1-R.κ)/R.a2)*sliceMoment b (fun j => ENNReal.ofReal (-Real.log (p j)))
            (R.secondFlow ρ (finiteMoment_finiteEnergy (by norm_num) hmρ)).V (energyInverse n x)+
          ENNReal.ofReal (R.b2/R.a2)*numberVectorMoment (energyInverse n x)) := by
  have hle : (R.κ : ℂ) • (thermalState n r hr).op ≤ (R.output ρ σ).op := by
    rw [← hτ]
    exact mixture_replacement_le R.κ R.hκ (R.rawOutput ρ σ) R.τ0
  obtain ⟨J,b,p,hp,hs,he⟩ := exists_faithful_eigenbasis_of_thermal_le (R.output ρ σ) hr hκ hle
  have hmin1 (ρ' : State n) (hmρ' : FiniteMoment 4 ρ') := hmin ρ' σ hmρ' hmσ
  have hmin2 (σ' : State n) (hmσ' : FiniteMoment 4 σ') := hmin ρ σ' hmρ hmσ'
  obtain ⟨G1,hG1⟩ := flow_minimum_gibbs
    (R.firstFlow σ (finiteMoment_finiteEnergy (by norm_num) hmσ)) R.τ0 hr hτ R.κ R.hκ hκ
    R.c R.a1 R.b1 R.ζ R.hc R.ha1 R.hb1.le R.hζ ρ hmρ b p hp hs he (by
      intro ρ' hmρ'
      have h := hmin1 ρ' hmρ'
      dsimp only [objective] at h
      change R.c*entropy (R.output ρ σ)-R.a1*entropy ρ+R.b1*energy ρ+R.ζ*numberMoment 4 ρ ≤
        R.c*entropy (R.output ρ' σ)-R.a1*entropy ρ'+R.b1*energy ρ'+R.ζ*numberMoment 4 ρ'
      linarith)
  obtain ⟨G2,hG2⟩ := flow_minimum_gibbs
    (R.secondFlow ρ (finiteMoment_finiteEnergy (by norm_num) hmρ)) R.τ0 hr hτ R.κ R.hκ hκ
    R.c R.a2 R.b2 R.ζ R.hc R.ha2 R.hb2.le R.hζ σ hmσ b p hp hs he (by
      intro σ' hmσ'
      have h := hmin2 σ' hmσ'
      dsimp only [objective] at h
      change R.c*entropy (R.output ρ σ)-R.a2*entropy σ+R.b2*energy σ+R.ζ*numberMoment 4 σ ≤
        R.c*entropy (R.output ρ σ')-R.a2*entropy σ'+R.b2*energy σ'+R.ζ*numberMoment 4 σ'
      linarith)
  exact ⟨J,b,p,hp,hs,he,G1,G2,hG1,hG2⟩

end Regularization
end

open QuantumTrace TraceEnsemble

namespace GibbsData
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)
theorem crossEntropy_hamiltonian {J : Type*}
    (a : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (F : KrausFlow n) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hk : 0 < k)
    (hform : ∀ x, ENNReal.ofReal (inner ℂ x (G.B x)).re =
      ENNReal.ofReal α*sliceMoment a (fun j => ENNReal.ofReal (-Real.log (p j))) F.V (energyInverse n x)+
      ENNReal.ofReal β*numberVectorMoment (energyInverse n x))
    (σ : State n) (hm : FiniteMoment 4 σ)
    (hc : Summable (fun j => (-Real.log (p j))*(inner ℂ (a j) ((F.map σ).op (a j))).re)) :
    HasSum (fun j => (-Real.log (gibbsWeight G.eigenval j))*(inner ℂ (G.basis j) (σ.op (G.basis j))).re)
      (k*numberMoment 4 σ+α*crossEntropy a p (F.map σ)+β*energy σ+Real.log (heatPartition G.eigenval)) := by
  let _ := G.nonempty
  obtain ⟨L,b,q,hq,hqt,he⟩ := exists_positive_eigenbasis (numberBasis n) σ.positive (trace_one_numberBasis σ)
  have hv : HasSum (fun j => ‖diagonalVector b q j‖^2) 1 := by
    simpa only [diagonalVector_norm_sq b q hq] using hqt
  have hw (j : J) : 0 ≤ -Real.log (p j) := neg_nonneg.mpr (Real.log_nonpos (hp j).le
    (hs.tsum_eq ▸ hs.summable.le_tsum j (fun i _ => (hp i).le)))
  have hK := gibbs_slice_real_trace G.basis G.eigenval G.positive_eigenval b q hq hqt σ he hm
    a (fun j => -Real.log (p j)) hw F.V F.norm (F.map σ)
    (F.ensemble L _ σ hv (diagonalVector_operator b q hq hqt.summable σ.op he)) hc
    G.positive hα hβ hform hk G.inverse_eigen
  have htr := hasSum_trace_basis (numberBasis n) G.basis σ.positive (trace_one_numberBasis σ)
  have hh := hK.add (htr.mul_left (Real.log (heatPartition G.eigenval)))
  convert! hh using 1
  · funext j
    rw [log_gibbsWeight G.eigenval G.heat]
    ring
  · simp only [mul_one, crossEntropy]

end GibbsData

def relativeEntropy {n : ℕ} {J : Type*} (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (σ : State n) : ℝ := crossEntropy b p σ-entropy σ

theorem flow_relative_entropy_identity {n : ℕ} {J : Type*}
    (F : KrausFlow n) (τ : State n) (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1)
    (c a β ζ : ℝ) (ha : 0 < a)
    (ρ : State n) (hmρ : FiniteMoment 4 ρ)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (G : GibbsData n (ζ/a) ρ)
    (he0 : ∀ j, (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ).op (b j) =
      (p j : ℂ) • b j)
    (hτ : FiniteEnergy τ)
    (hcross : ∀ σ, FiniteMoment 4 σ →
      Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) ((F.map σ).op (b j))).re))
    (hcτ : Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (τ.op (b j))).re))
    (hlog : ∀ σ, FiniteMoment 4 σ → crossEntropy G.basis (gibbsWeight G.eigenval) σ =
      (ζ/a)*numberMoment 4 σ+(c*(1-κ)/a)*crossEntropy b p (F.map σ)+(β/a)*energy σ+
        Real.log (heatPartition G.eigenval))
    (σ : State n) (hmσ : FiniteMoment 4 σ) :
    a*relativeEntropy G.basis (gibbsWeight G.eigenval) σ-
      c*relativeEntropy b p (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map σ) τ) =
      (c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map σ) τ)-
        a*entropy σ+β*energy σ+ζ*numberMoment 4 σ)-
      (c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ)-
        a*entropy ρ+β*energy ρ+ζ*numberMoment 4 ρ) := by
  let ht : 1-κ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩
  have hself := crossEntropy_self ρ (finiteMoment_finiteEnergy (by norm_num) hmρ)
    G.basis (gibbsWeight G.eigenval) G.eigen
  have hself0 := crossEntropy_self (mixture (1-κ) ht (F.map ρ) τ)
    (mixture_finiteEnergy _ _ (F.finiteEnergy _ (finiteMoment_finiteEnergy (by norm_num) hmρ)) hτ) b p he0
  rw [crossEntropy_mixture b p (1-κ) ht (F.map ρ) τ (hcross ρ hmρ) hcτ] at hself0
  rw [hlog ρ hmρ] at hself
  unfold relativeEntropy
  rw [hlog σ hmσ, crossEntropy_mixture b p (1-κ) ht (F.map σ) τ (hcross σ hmσ) hcτ]
  have hself' := congrArg (fun x => a*x) hself
  have hcancel (x : ℝ) : a*(x/a) = x := mul_div_cancel₀ x ha.ne'
  simp only [mul_add, ← mul_assoc, hcancel] at hself'
  field_simp [ha.ne']
  linear_combination hself' - c*hself0

end EntropyPhotonNumber

namespace TensorLp
variable {A B I J : Type*}

theorem tensor_mul_moment (w : A → ℝ≥0∞) (u : B → ℝ≥0∞) (x : H A) (y : H B) :
    vectorMoment (fun ab : A × B => w ab.1*u ab.2) (tensor x y) =
      vectorMoment w x*vectorMoment u y := by
  change (∑' ab : A × B, (w ab.1*u ab.2)*ENNReal.ofReal (‖x ab.1*y ab.2‖^2)) = _
  simp only [norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.tsum_prod']
  simp_rw [mul_mul_mul_comm (w _) (u _) (ENNReal.ofReal _) (ENNReal.ofReal _)]
  simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, vectorMoment]

theorem ensemble_tensor_mul_moment [DecidableEq A] [DecidableEq B]
    {v : I → H A} {z : J → H B}
    (hv : Summable (fun i => ‖v i‖^2)) (hz : Summable (fun j => ‖z j‖^2))
    (w : A → ℝ≥0∞) (u : B → ℝ≥0∞) :
    (∑' ij : I × J, vectorMoment (fun ab : A × B => w ab.1*u ab.2) (tensor (v ij.1) (z ij.2))) =
      matrixMoment w (TraceEnsemble.operator v)*matrixMoment u (TraceEnsemble.operator z) := by
  simp only [tensor_mul_moment, ENNReal.tsum_prod', ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  rw [matrixMoment_ensemble hv, matrixMoment_ensemble hz]

end TensorLp

namespace EntropyPhotonNumber
open TensorLp

def powerMoment {n : ℕ} (m : ℕ) (ρ : State n) : ℝ≥0∞ :=
  matrixMoment (fun k => (1+(totalNumber k : ℝ≥0∞))^m) ρ.op

theorem powerMoment_eq {n : ℕ} (m : ℕ) (ρ : State n) :
    powerMoment m ρ = ∑' k, ENNReal.ofReal ((1+(totalNumber k : ℝ))^m*(entry ρ.op k k).re) := by
  unfold powerMoment matrixMoment
  congr 1
  funext k
  rw [ENNReal.ofReal_mul (pow_nonneg (by positivity) _),
    ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_one, ENNReal.ofReal_natCast]
  rfl

theorem finiteMoment_iff {n : ℕ} (m : ℕ) (ρ : State n) :
    FiniteMoment m ρ ↔ powerMoment m ρ < ⊤ := by
  rw [powerMoment_eq]
  have hp (k : NumberIndex n) : 0 ≤ (1+(totalNumber k : ℝ))^m*(entry ρ.op k k).re :=
    mul_nonneg (pow_nonneg (by positivity) _) (ρ.positive.re_inner_nonneg_right _)
  constructor
  · intro h
    exact h.tsum_ofReal_lt_top
  · intro h
    have hs := ENNReal.summable_toReal h.ne
    change Summable (fun k => (1+(totalNumber k : ℝ))^m*(entry ρ.op k k).re)
    simpa only [ENNReal.toReal_ofReal (hp _)] using hs

theorem beamOutput_powerMoment_le {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (m : ℕ) (ρA ρB : State n) :
    powerMoment m (beamOutput η hη ρA ρB) ≤ powerMoment m ρA*powerMoment m ρB := by
  change matrixMoment _ (partialTrace (mixedVector η hη ρA ρB)) ≤ _
  rw [partialTrace_moment (mixedVector_norm η hη ρA ρB).summable]
  calc
    _ ≤ ∑' a, vectorMoment (fun ab : PairedIndex n =>
        (1+((totalNumber (fun j => ab.1 j+ab.2 j)) : ℝ≥0∞))^m) (mixedVector η hη ρA ρB a) := by
      apply ENNReal.tsum_le_tsum
      intro a
      apply ENNReal.tsum_le_tsum
      intro ab
      apply mul_le_mul' _ le_rfl
      apply pow_le_pow_left'
      simp only [totalNumber, Finset.sum_add_distrib, Nat.cast_add]
      exact add_le_add_right le_self_add 1
    _ = ∑' a : PairedIndex n, vectorMoment (fun ab : PairedIndex n =>
        (1+((totalNumber (fun j => ab.1 j+ab.2 j)) : ℝ≥0∞))^m)
        (tensor (rootColumn ρA a.1) (rootColumn ρB a.2)) := by
      congr 1
      funext a
      exact beam_vector_moment η hη _ (fun k => (1+(totalNumber k : ℝ≥0∞))^m)
    _ ≤ ∑' a : PairedIndex n, vectorMoment (fun ab : PairedIndex n =>
        (1+(totalNumber ab.1 : ℝ≥0∞))^m*(1+(totalNumber ab.2 : ℝ≥0∞))^m)
        (tensor (rootColumn ρA a.1) (rootColumn ρB a.2)) := by
      apply ENNReal.tsum_le_tsum
      intro a
      apply ENNReal.tsum_le_tsum
      intro ab
      apply mul_le_mul' _ le_rfl
      dsimp only
      rw [← mul_pow]
      apply pow_le_pow_left'
      simp only [totalNumber, Finset.sum_add_distrib, Nat.cast_add]
      rw [add_mul, one_mul, mul_add, mul_one]
      rw [← add_assoc]
      calc
        1+((∑ j, ab.1 j : ℕ):ℝ≥0∞)+(∑ j, ab.2 j : ℕ) ≤
          1+((∑ j, ab.1 j : ℕ):ℝ≥0∞)+(∑ j, ab.2 j : ℕ)+
            ((∑ j, ab.1 j : ℕ):ℝ≥0∞)*(∑ j, ab.2 j : ℕ) := le_self_add
        _ = _ := by ac_rfl
    _ = powerMoment m ρA*powerMoment m ρB := by
      rw [ensemble_tensor_mul_moment (rootColumn_norm ρA).summable (rootColumn_norm ρB).summable
        (fun k => (1+(totalNumber k : ℝ≥0∞))^m) (fun k => (1+(totalNumber k : ℝ≥0∞))^m),
        rootColumn_operator, rootColumn_operator]
      rfl

theorem beamOutput_finiteMoment {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) {m : ℕ} {ρA ρB : State n}
    (hA : FiniteMoment m ρA) (hB : FiniteMoment m ρB) : FiniteMoment m (beamOutput η hη ρA ρB) := by
  apply (finiteMoment_iff _ _).mpr
  exact (beamOutput_powerMoment_le η hη m ρA ρB).trans_lt
    (ENNReal.mul_lt_top ((finiteMoment_iff _ _).mp hA) ((finiteMoment_iff _ _).mp hB))

end EntropyPhotonNumber

end

end OAI
