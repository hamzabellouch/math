import Mathlib
import OAI.Geometry.SmoothYau.Estimates.TransportCorrection
import OAI.Geometry.SmoothYau.Geometry.WaveDerivSum

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def smoothPolynomialLaplacian (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (P : MvPolynomial σ ℂ) : (σ → ℝ) → ℂ :=
  fun x => (∑ i, ∑ j, g i j x * realPolyEval (pderiv i (pderiv j P)) x) +
    ∑ i, b i x * realPolyEval (pderiv i P) x

omit [DecidableEq σ] in
lemma contDiff_smoothPolynomialLaplacian (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (P : MvPolynomial σ ℂ) :
    ContDiff ℝ ∞ (smoothPolynomialLaplacian g b P) := by
  exact (ContDiff.sum (fun i _ => ContDiff.sum
    (fun j _ => (hg i j).mul (contDiff_realPolyEval _)))).add
      (ContDiff.sum (fun i _ => (hb i).mul (contDiff_realPolyEval _)))

lemma waveDeriv_realPolyEval_single (i : σ) (P : MvPolynomial σ ℂ) :
    waveDeriv (Pi.single i 1) (realPolyEval P) = realPolyEval (pderiv i P) := by
  funext x
  simp [waveDeriv, fderiv_realPolyEval, Pi.single_apply, apply_ite]

lemma smoothPolynomialLaplacian_eq_operator (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (P : MvPolynomial σ ℂ) :
    smoothPolynomialLaplacian g b P =
      waveCoordinateOperator (fun i => Pi.single i 1) g b (realPolyEval P) := by
  funext x
  simp only [waveCoordinateOperator, waveDeriv_realPolyEval_single,
    smoothPolynomialLaplacian]

def smoothPhaseTransportVector (g : σ → σ → (σ → ℝ) → ℂ)
    (S : MvPolynomial σ ℂ) (i : σ) : (σ → ℝ) → ℂ :=
  fun x => ∑ j, (g i j x + g j i x) * realPolyEval (pderiv j S) x

def smoothPhaseTransportScalar (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (S : MvPolynomial σ ℂ) : (σ → ℝ) → ℂ :=
  fun x => smoothPolynomialLaplacian g b S x + 2

omit [DecidableEq σ] in
lemma contDiff_smoothPhaseTransportVector (g : σ → σ → (σ → ℝ) → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (S : MvPolynomial σ ℂ) (i : σ) :
    ContDiff ℝ ∞ (smoothPhaseTransportVector g S i) :=
  ContDiff.sum (fun j _ => ((hg i j).add (hg j i)).mul (contDiff_realPolyEval _))

omit [DecidableEq σ] in
lemma contDiff_smoothPhaseTransportScalar (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (S : MvPolynomial σ ℂ) :
    ContDiff ℝ ∞ (smoothPhaseTransportScalar g b S) :=
  (contDiff_smoothPolynomialLaplacian g b hg hb S).add contDiff_const

lemma smoothPhaseTransportVector_zero (g : σ → σ → (σ → ℝ) → ℂ)
    (hg0 : ∀ i j, g i j 0 = if i = j then 1 else 0)
    (S : MvPolynomial σ ℂ) (z : σ → ℂ)
    (hS : ∀ i, constantCoeff (pderiv i S) = z i) (i : σ) :
    smoothPhaseTransportVector g S i 0 = 2 * z i := by
  simp only [smoothPhaseTransportVector, hg0, realPolyEval_at_zero, hS]
  simp [eq_comm, ite_add_ite, ite_mul, two_mul]
  ring

omit [DecidableEq σ] in
lemma sum_transport_product (G : σ → σ → ℂ) (s v : σ → ℂ) :
    (∑ i, (∑ j, (G i j + G j i) * s j) * v i) =
      (∑ i, ∑ j, G i j * v i * s j) + (∑ i, ∑ j, G i j * s i * v j) := by
  simp only [Finset.sum_mul, add_mul, Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · rw [Finset.sum_comm]

lemma smoothWaveTransport_eq_finite (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (S V : MvPolynomial σ ℂ) :
    smoothWaveTransport (smoothPhaseTransportVector g S)
      (smoothPhaseTransportScalar g b S) V =
    finiteWaveTransport (fun i => Pi.single i 1) g b (realPolyEval S) (realPolyEval V) := by
  funext x
  simp only [smoothWaveTransport, smoothPhaseTransportVector, smoothPhaseTransportScalar,
    finiteWaveTransport, waveGradientPair, waveDeriv_realPolyEval_single,
    ← smoothPolynomialLaplacian_eq_operator]
  rw [sum_transport_product]

def smoothTransportPolynomial (a : σ → (σ → ℝ) → ℂ)
    (b f : (σ → ℝ) → ℂ) (z : σ → ℂ) (c : ℂ) (N : ℕ) : MvPolynomial σ ℂ :=
  transportIter (fun i => realTaylorPolynomial (a i) N)
    (realTaylorPolynomial b N) (realTaylorPolynomial f N) z c N

lemma smoothTransportPolynomial_spec (a : σ → (σ → ℝ) → ℂ)
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) (b f : (σ → ℝ) → ℂ)
    (hb : ContDiff ℝ ∞ b) (hf : ContDiff ℝ ∞ f)
    (z : σ → ℂ) (hz : z ≠ 0) (ha0 : ∀ i, a i 0 = 2 * z i)
    (c : ℂ) (N : ℕ) :
    let V := smoothTransportPolynomial a b f z c N
    constantCoeff V = c ∧ V.totalDegree ≤ N ∧
      SmoothJetZero (smoothWaveTransport a b V + f) N := by
  dsimp only
  by_cases hN : N = 0
  · subst N
    exact ⟨by simp [smoothTransportPolynomial, transportIter],
      by simp [smoothTransportPolynomial, transportIter], SmoothJetZero.order_zero _⟩
  · have hA (i : σ) : constantCoeff (realTaylorPolynomial (a i) N) = 2 * z i :=
      (realTaylorPolynomial_constant (ha i) (Nat.pos_of_ne_zero hN)).trans (ha0 i)
    obtain ⟨hV, hR, hD⟩ := transportIter_spec
      (fun i => realTaylorPolynomial (a i) N) (realTaylorPolynomial b N)
      (realTaylorPolynomial f N) z hz hA c N
    exact ⟨hV, hD, smoothWaveTransport_jet a ha b f hb hf _ N hR⟩

def smoothPhasePolynomial (g : σ → σ → (σ → ℝ) → ℂ)
    (c : ℂ) (z : σ → ℂ) (Q : σ → σ → ℂ) (L : ℕ) : MvPolynomial σ ℂ :=
  eikonalIter (fun i j => realTaylorPolynomial (g i j) L) z
    (wavePhaseSeed c z Q) (L - 2)

lemma smoothPhasePolynomial_spec (g : σ → σ → (σ → ℝ) → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hg0 : ∀ i j, g i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ i j, fderiv ℝ (g i j) 0 = 0)
    (c : ℂ) (z : σ → ℂ) (Q : σ → σ → ℂ) (hz : z ≠ 0)
    (hQ : ∀ i j, Q i j = Q j i) (hnull : ∑ i, z i * z i = -1)
    (hQz : ∀ k, ∑ i, z i * Q k i = 0) (L : ℕ) (hL : 2 ≤ L) :
    let S := smoothPhasePolynomial g c z Q L
    VanishTo (S - wavePhaseSeed c z Q) 3 ∧
      (∀ i, constantCoeff (pderiv i S) = z i) ∧
      SmoothJetZero (smoothEikonalResidual g S) L ∧
      S.totalDegree ≤ max (wavePhaseSeed c z Q).totalDegree L := by
  let G := fun i j => realTaylorPolynomial (g i j) L
  have hG (i j : σ) : constantCoeff (G i j) = if i = j then 1 else 0 :=
    (realTaylorPolynomial_constant (hg i j) (by omega)).trans (hg0 i j)
  have hdG (i j l : σ) : constantCoeff (pderiv l (G i j)) = 0 := by
    rw [realTaylorPolynomial_linear (hg i j) (by omega), hdg0 i j]
    rfl
  obtain ⟨hS, hE, hdegree⟩ := eikonalIter_spec G z hz (wavePhaseSeed c z Q) hG
    (wavePhaseSeed_gradient c z Q)
    (wavePhaseSeed_eikonal G c z Q hG hdG hQ hnull hQz) (L - 2)
  have horder : L - 2 + 2 = L := by omega
  rw [horder] at hE hdegree
  refine ⟨hS, ?_, smoothEikonalResidual_jet g hg _ L hE, hdegree⟩
  intro i
  have hd := (hS.pderiv i).constantCoeff_eq_zero (by decide)
  simp only [map_sub, wavePhaseSeed_gradient] at hd
  exact sub_eq_zero.mp hd

def smoothWaveAmplitudes (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (S : MvPolynomial σ ℂ) (z : σ → ℂ)
    (K J : ℕ) : ℕ → MvPolynomial σ ℂ
  | 0 => smoothTransportPolynomial (smoothPhaseTransportVector g S)
      (smoothPhaseTransportScalar g b S) 0 z 1 (K + J)
  | j + 1 => smoothTransportPolynomial (smoothPhaseTransportVector g S)
      (smoothPhaseTransportScalar g b S)
      (smoothPolynomialLaplacian g b (smoothWaveAmplitudes g b S z K J j)) z 0
      (K + J - (j + 1))

lemma smoothWaveAmplitudes_zero_spec (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hg0 : ∀ i j, g i j 0 = if i = j then 1 else 0)
    (S : MvPolynomial σ ℂ) (z : σ → ℂ) (hz : z ≠ 0)
    (hS : ∀ i, constantCoeff (pderiv i S) = z i) (K J : ℕ) :
    let V := smoothWaveAmplitudes g b S z K J 0
    constantCoeff V = 1 ∧ V.totalDegree ≤ K + J ∧
      SmoothJetZero (smoothWaveTransport (smoothPhaseTransportVector g S)
        (smoothPhaseTransportScalar g b S) V) (K + J) := by
  dsimp only
  rw [smoothWaveAmplitudes]
  have h := smoothTransportPolynomial_spec (smoothPhaseTransportVector g S)
    (contDiff_smoothPhaseTransportVector g hg S) (smoothPhaseTransportScalar g b S) 0
    (contDiff_smoothPhaseTransportScalar g b hg hb S) contDiff_const z hz
    (smoothPhaseTransportVector_zero g hg0 S z hS) 1 (K + J)
  exact ⟨h.1, h.2.1, by simpa only [add_zero] using h.2.2⟩

lemma smoothWaveAmplitudes_succ_spec (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hg0 : ∀ i j, g i j 0 = if i = j then 1 else 0)
    (S : MvPolynomial σ ℂ) (z : σ → ℂ) (hz : z ≠ 0)
    (hS : ∀ i, constantCoeff (pderiv i S) = z i) (K J j : ℕ) :
    let V := smoothWaveAmplitudes g b S z K J
    constantCoeff (V (j+1)) = 0 ∧ (V (j+1)).totalDegree ≤ K + J - (j+1) ∧
      SmoothJetZero (smoothWaveTransport (smoothPhaseTransportVector g S)
        (smoothPhaseTransportScalar g b S) (V (j+1)) +
          smoothPolynomialLaplacian g b (V j)) (K + J - (j+1)) := by
  dsimp only
  conv_lhs => rw [smoothWaveAmplitudes]
  exact smoothTransportPolynomial_spec (smoothPhaseTransportVector g S)
    (contDiff_smoothPhaseTransportVector g hg S) (smoothPhaseTransportScalar g b S)
    (smoothPolynomialLaplacian g b (smoothWaveAmplitudes g b S z K J j))
    (contDiff_smoothPhaseTransportScalar g b hg hb S)
    (contDiff_smoothPolynomialLaplacian g b hg hb _) z hz
    (smoothPhaseTransportVector_zero g hg0 S z hS) 0 (K + J - (j+1))

lemma smoothWaveAmplitudes_spec (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hg0 : ∀ i j, g i j 0 = if i = j then 1 else 0)
    (S : MvPolynomial σ ℂ) (z : σ → ℂ) (hz : z ≠ 0)
    (hS : ∀ i, constantCoeff (pderiv i S) = z i) (K J : ℕ) :
    let V := smoothWaveAmplitudes g b S z K J
    (∀ j, constantCoeff (V j) = if j = 0 then 1 else 0) ∧
    (∀ j, (V j).totalDegree ≤ K + J - j) ∧
    SmoothJetZero (finiteWaveTransport (fun i => Pi.single i 1) g b
      (realPolyEval S) (realPolyEval (V 0))) (K + J) ∧
    (∀ j, SmoothJetZero (fun x => finiteWaveTransport (fun i => Pi.single i 1) g b
        (realPolyEval S) (realPolyEval (V (j+1))) x +
       waveCoordinateOperator (fun i => Pi.single i 1) g b (realPolyEval (V j)) x)
      (K + J - (j + 1))) := by
  dsimp only
  have h0 := smoothWaveAmplitudes_zero_spec g b hg hb hg0 S z hz hS K J
  have hs := smoothWaveAmplitudes_succ_spec g b hg hb hg0 S z hz hS K J
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    cases j with
    | zero => exact h0.1
    | succ j => exact (hs j).1
  · intro j
    cases j with
    | zero => exact h0.2.1
    | succ j => exact (hs j).2.1
  · rw [← smoothWaveTransport_eq_finite]
    exact h0.2.2
  · intro j
    rw [← smoothWaveTransport_eq_finite, ← smoothPolynomialLaplacian_eq_operator]
    exact (hs j).2.2



end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {X : Type*} [TopologicalSpace X]

omit [Fintype σ] in
lemma CoeffContinuous.C {c : X → ℂ} (hc : Continuous c) :
    CoeffContinuous (fun x => MvPolynomial.C (c x) : X → MvPolynomial σ ℂ) := by
  intro m
  simp only [coeff_C]
  split_ifs
  · exact hc
  · exact continuous_const

lemma multilinearPolynomial_coeffContinuous {n : ℕ}
    (B : X → (σ → ℝ) [×n]→L[ℝ] ℂ) (hB : Continuous B) :
    CoeffContinuous (fun x => multilinearPolynomial (B x)) := by
  apply CoeffContinuous.sum Finset.univ
  intro a _
  apply CoeffContinuous.mul _ (CoeffContinuous.const _)
  apply CoeffContinuous.C
  exact hB.eval continuous_const

lemma realTaylorPolynomial_coeffContinuous (f : X → (σ → ℝ) → ℂ) (N : ℕ)
    (hf : ∀ k < N, Continuous (fun p => iteratedFDeriv ℝ k (f p) 0)) :
    CoeffContinuous (fun p => realTaylorPolynomial (f p) N) := by
  apply CoeffContinuous.sum (Finset.range N)
  intro k hk
  exact (CoeffContinuous.const _).mul
    (multilinearPolynomial_coeffContinuous _ (hf k (Finset.mem_range.mp hk)))

def formalPolynomialLaplacian (G : σ → σ → MvPolynomial σ ℂ)
    (B : σ → MvPolynomial σ ℂ) (P : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  (∑ i, ∑ j, G i j * pderiv i (pderiv j P)) + ∑ i, B i * pderiv i P

def formalPhaseTransportVector (G : σ → σ → MvPolynomial σ ℂ)
    (S : MvPolynomial σ ℂ) (i : σ) : MvPolynomial σ ℂ :=
  ∑ j, (G i j + G j i) * pderiv j S

def formalPhaseTransportScalar (G : σ → σ → MvPolynomial σ ℂ)
    (B : σ → MvPolynomial σ ℂ) (S : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  formalPolynomialLaplacian G B S + 2

omit [DecidableEq σ] in
lemma formalPolynomialLaplacian_coeffContinuous
    (G : X → σ → σ → MvPolynomial σ ℂ) (B : X → σ → MvPolynomial σ ℂ)
    (hG : ∀ i j, CoeffContinuous (fun p => G p i j))
    (hB : ∀ i, CoeffContinuous (fun p => B p i))
    (P : X → MvPolynomial σ ℂ) (hP : CoeffContinuous P) :
    CoeffContinuous (fun p => formalPolynomialLaplacian (G p) (B p) (P p)) := by
  exact (CoeffContinuous.sum Finset.univ _ (fun i _ =>
    CoeffContinuous.sum Finset.univ _ (fun j _ => (hG i j).mul ((hP.pderiv j).pderiv i)))).add
      (CoeffContinuous.sum Finset.univ _ (fun i _ => (hB i).mul (hP.pderiv i)))

omit [DecidableEq σ] in
lemma formalPhaseTransportVector_coeffContinuous
    (G : X → σ → σ → MvPolynomial σ ℂ)
    (hG : ∀ i j, CoeffContinuous (fun p => G p i j))
    (P : X → MvPolynomial σ ℂ) (hP : CoeffContinuous P) (i : σ) :
    CoeffContinuous (fun p => formalPhaseTransportVector (G p) (P p) i) :=
  CoeffContinuous.sum Finset.univ _ (fun j _ => ((hG i j).add (hG j i)).mul (hP.pderiv j))

lemma formalPhaseTransportVector_constant (G : σ → σ → MvPolynomial σ ℂ)
    (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (S : MvPolynomial σ ℂ) (z : σ → ℂ)
    (hS : ∀ i, constantCoeff (pderiv i S) = z i) (i : σ) :
    constantCoeff (formalPhaseTransportVector G S i) = 2 * z i := by
  simp only [formalPhaseTransportVector, map_sum, map_mul, map_add, hG, hS]
  simp [eq_comm, ite_add_ite, ite_mul, two_mul]
  ring

omit [DecidableEq σ] in
lemma smoothPolynomialLaplacian_approx (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (G : σ → σ → MvPolynomial σ ℂ) (B : σ → MvPolynomial σ ℂ) (N : ℕ)
    (hG : ∀ i j, SmoothJetZero (g i j - realPolyEval (G i j)) N)
    (hB : ∀ i, SmoothJetZero (b i - realPolyEval (B i)) N) (P : MvPolynomial σ ℂ) :
    SmoothJetZero (smoothPolynomialLaplacian g b P -
      realPolyEval (formalPolynomialLaplacian G B P)) N := by
  let D := fun i j x => (g i j x - realPolyEval (G i j) x) *
    realPolyEval (pderiv i (pderiv j P)) x
  let F := fun i x => (b i x - realPolyEval (B i) x) * realPolyEval (pderiv i P) x
  have hd (i j : σ) : ContDiff ℝ ∞ (D i j) :=
    ((hg i j).sub (contDiff_realPolyEval _)).mul (contDiff_realPolyEval _)
  have hf (i : σ) : ContDiff ℝ ∞ (F i) :=
    ((hb i).sub (contDiff_realPolyEval _)).mul (contDiff_realPolyEval _)
  have hds (i : σ) : ContDiff ℝ ∞ (∑ j, D i j) := by
    simpa only [Finset.sum_fn] using ContDiff.sum (s := Finset.univ) (fun j _ => hd i j)
  have hdss : ContDiff ℝ ∞ (∑ i, ∑ j, D i j) := by
    simpa only [Finset.sum_fn] using ContDiff.sum (s := Finset.univ) (fun i _ => hds i)
  have hfs : ContDiff ℝ ∞ (∑ i, F i) := by
    simpa only [Finset.sum_fn] using ContDiff.sum (s := Finset.univ) (fun i _ => hf i)
  have heq : smoothPolynomialLaplacian g b P - realPolyEval (formalPolynomialLaplacian G B P) =
      (∑ i, ∑ j, D i j) + ∑ i, F i := by
    funext x
    simp only [smoothPolynomialLaplacian, formalPolynomialLaplacian, Pi.sub_apply,
      Pi.add_apply, Finset.sum_apply, realPolyEval, map_add, map_sum, map_mul, D, F,
      sub_mul, Finset.sum_sub_distrib]
    ring
  rw [heq]
  exact (SmoothJetZero.sum Finset.univ _ (fun i _ => hds i)
    (fun i _ => SmoothJetZero.sum Finset.univ _ (fun j _ => hd i j)
      (fun j _ => (hG i j).mul_right ((hg i j).sub (contDiff_realPolyEval _)) _
        (contDiff_realPolyEval _)))).add hdss hfs
    (SmoothJetZero.sum Finset.univ _ (fun i _ => hf i)
      (fun i _ => (hB i).mul_right ((hb i).sub (contDiff_realPolyEval _)) _
        (contDiff_realPolyEval _)))

omit [DecidableEq σ] in
lemma smoothPhaseTransportVector_approx (g : σ → σ → (σ → ℝ) → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (G : σ → σ → MvPolynomial σ ℂ) (N : ℕ)
    (hG : ∀ i j, SmoothJetZero (g i j - realPolyEval (G i j)) N)
    (S : MvPolynomial σ ℂ) (i : σ) :
    SmoothJetZero (smoothPhaseTransportVector g S i -
      realPolyEval (formalPhaseTransportVector G S i)) N := by
  let D := fun j x => ((g i j x - realPolyEval (G i j) x) +
    (g j i x - realPolyEval (G j i) x)) * realPolyEval (pderiv j S) x
  have hd (j : σ) : ContDiff ℝ ∞ (D j) :=
    (((hg i j).sub (contDiff_realPolyEval _)).add
      ((hg j i).sub (contDiff_realPolyEval _))).mul (contDiff_realPolyEval _)
  have heq : smoothPhaseTransportVector g S i - realPolyEval (formalPhaseTransportVector G S i) =
      ∑ j, D j := by
    funext x
    simp only [smoothPhaseTransportVector, formalPhaseTransportVector, Pi.sub_apply,
      Finset.sum_apply, realPolyEval, map_sum, map_mul, map_add, D]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  exact SmoothJetZero.sum Finset.univ _ (fun j _ => hd j) (fun j _ =>
    ((hG i j).add ((hg i j).sub (contDiff_realPolyEval _))
      ((hg j i).sub (contDiff_realPolyEval _)) (hG j i)).mul_right
        (((hg i j).sub (contDiff_realPolyEval _)).add
          ((hg j i).sub (contDiff_realPolyEval _))) _ (contDiff_realPolyEval _))

omit [DecidableEq σ] in
lemma smoothWaveTransport_jet_approx (a : σ → (σ → ℝ) → ℂ)
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) (b f : (σ → ℝ) → ℂ)
    (hb : ContDiff ℝ ∞ b) (hf : ContDiff ℝ ∞ f)
    (A : σ → MvPolynomial σ ℂ) (B F V : MvPolynomial σ ℂ) (N : ℕ)
    (hA : ∀ i, SmoothJetZero (a i - realPolyEval (A i)) N)
    (hB : SmoothJetZero (b - realPolyEval B) N)
    (hF : SmoothJetZero (f - realPolyEval F) N)
    (hR : VanishTo (waveTransport A B V + F) N) :
    SmoothJetZero (smoothWaveTransport a b V + f) N := by
  let D := fun i x => (a i x - realPolyEval (A i) x) * realPolyEval (pderiv i V) x
  let D₀ := fun x => (b x - realPolyEval B x) * realPolyEval V x
  have hD (i : σ) : ContDiff ℝ ∞ (D i) :=
    ((ha i).sub (contDiff_realPolyEval _)).mul (contDiff_realPolyEval _)
  have hD₀ : ContDiff ℝ ∞ D₀ :=
    (hb.sub (contDiff_realPolyEval _)).mul (contDiff_realPolyEval _)
  have hDs : ContDiff ℝ ∞ (∑ i, D i) := by
    simpa only [Finset.sum_fn] using (ContDiff.sum (s := Finset.univ) (fun i _ => hD i))
  have hj (i : σ) : SmoothJetZero (D i) N :=
    (hA i).mul_right ((ha i).sub (contDiff_realPolyEval _)) _ (contDiff_realPolyEval _)
  have hj₀ : SmoothJetZero D₀ N := hB.mul_right
      (hb.sub (contDiff_realPolyEval _)) _ (contDiff_realPolyEval _)
  have hjs : SmoothJetZero (∑ i, D i) N :=
    SmoothJetZero.sum Finset.univ _ (fun i _ => hD i) (fun i _ => hj i)
  have heq : smoothWaveTransport a b V + f =
      realPolyEval (waveTransport A B V + F) +
        ((∑ i, D i) + D₀ + (f - realPolyEval F)) := by
    funext x
    simp only [smoothWaveTransport, waveTransport, Pi.add_apply, Pi.sub_apply,
      Finset.sum_apply, realPolyEval, map_add, map_sum, map_mul, D, D₀]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [heq]
  exact hR.realPolyEval.add (contDiff_realPolyEval _)
    ((hDs.add hD₀).add (hf.sub (contDiff_realPolyEval _)))
    ((hjs.add hDs hD₀ hj₀).add (hDs.add hD₀) (hf.sub (contDiff_realPolyEval _)) hF)

def symbolWaveAmplitudes (G : σ → σ → MvPolynomial σ ℂ)
    (B : σ → MvPolynomial σ ℂ) (S : MvPolynomial σ ℂ) (z : σ → ℂ)
    (K J : ℕ) : ℕ → MvPolynomial σ ℂ
  | 0 => transportIter (formalPhaseTransportVector G S) (formalPhaseTransportScalar G B S) 0 z 1 (K+J)
  | j+1 => transportIter (formalPhaseTransportVector G S) (formalPhaseTransportScalar G B S)
      (formalPolynomialLaplacian G B (symbolWaveAmplitudes G B S z K J j)) z 0 (K+J-(j+1))

lemma symbolWaveAmplitudes_spec (G : σ → σ → MvPolynomial σ ℂ)
    (B : σ → MvPolynomial σ ℂ) (S : MvPolynomial σ ℂ) (z : σ → ℂ)
    (hz : z ≠ 0) (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hS : ∀ i, constantCoeff (pderiv i S) = z i) (K J : ℕ) :
    let V := symbolWaveAmplitudes G B S z K J
    (∀ j, constantCoeff (V j) = if j = 0 then 1 else 0) ∧
    (∀ j, (V j).totalDegree ≤ K+J-j) ∧
    VanishTo (waveTransport (formalPhaseTransportVector G S)
      (formalPhaseTransportScalar G B S) (V 0)) (K+J) ∧
    (∀ j, VanishTo (waveTransport (formalPhaseTransportVector G S)
      (formalPhaseTransportScalar G B S) (V (j+1)) + formalPolynomialLaplacian G B (V j))
      (K+J-(j+1))) := by
  dsimp only
  have hA := formalPhaseTransportVector_constant G hG S z hS
  have h0 := transportIter_spec (formalPhaseTransportVector G S)
    (formalPhaseTransportScalar G B S) 0 z hz hA 1 (K+J)
  have hj (j : ℕ) := transportIter_spec (formalPhaseTransportVector G S)
    (formalPhaseTransportScalar G B S)
    (formalPolynomialLaplacian G B (symbolWaveAmplitudes G B S z K J j)) z hz hA 0 (K+J-(j+1))
  exact ⟨fun j => by cases j with
    | zero => exact h0.1
    | succ j => exact (hj j).1,
    fun j => by cases j with
    | zero => exact h0.2.2
    | succ j => exact (hj j).2.2,
    by simpa only [add_zero, symbolWaveAmplitudes] using h0.2.1, fun j => (hj j).2.1⟩

omit [DecidableEq σ] in
lemma symbolWaveAmplitudes_coeffContinuous
    (G : X → σ → σ → MvPolynomial σ ℂ) (B : X → σ → MvPolynomial σ ℂ)
    (hG : ∀ i j, CoeffContinuous (fun p => G p i j))
    (hB : ∀ i, CoeffContinuous (fun p => B p i))
    (S : X → MvPolynomial σ ℂ) (hS : CoeffContinuous S) (z : X → σ → ℂ)
    (hz : ∀ i, Continuous (fun p => z p i)) (hz₀ : ∀ p, z p ≠ 0) (K J j : ℕ) :
    CoeffContinuous (fun p => symbolWaveAmplitudes (G p) (B p) (S p) (z p) K J j) := by
  have hA := formalPhaseTransportVector_coeffContinuous G hG S hS
  have hT : CoeffContinuous (fun p => formalPhaseTransportScalar (G p) (B p) (S p)) :=
    (formalPolynomialLaplacian_coeffContinuous G B hG hB S hS).add (CoeffContinuous.const _)
  induction j with
  | zero => exact transportIter_coeffContinuous _ hA _ _ hT (CoeffContinuous.const _) z hz hz₀ _ continuous_const _
  | succ j ih =>
    exact transportIter_coeffContinuous _ hA _ _ hT
      (formalPolynomialLaplacian_coeffContinuous G B hG hB _ ih) z hz hz₀ _ continuous_const _

lemma symbolWaveAmplitudes_genuine (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (G : σ → σ → MvPolynomial σ ℂ) (B : σ → MvPolynomial σ ℂ)
    (S : MvPolynomial σ ℂ) (z : σ → ℂ) (hz : z ≠ 0)
    (hG0 : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hS : ∀ i, constantCoeff (pderiv i S) = z i) (K J : ℕ)
    (hG : ∀ i j, SmoothJetZero (g i j - realPolyEval (G i j)) (K+J))
    (hB : ∀ i, SmoothJetZero (b i - realPolyEval (B i)) (K+J)) :
    let V := symbolWaveAmplitudes G B S z K J
    SmoothJetZero (finiteWaveTransport (fun i => Pi.single i 1) g b
      (realPolyEval S) (realPolyEval (V 0))) (K+J) ∧
    (∀ j, SmoothJetZero (fun x => finiteWaveTransport (fun i => Pi.single i 1) g b
      (realPolyEval S) (realPolyEval (V (j+1))) x +
        waveCoordinateOperator (fun i => Pi.single i 1) g b (realPolyEval (V j)) x)
      (K+J-(j+1))) := by
  let V := symbolWaveAmplitudes G B S z K J
  have hspec := symbolWaveAmplitudes_spec G B S z hz hG0 hS K J
  have hA := smoothPhaseTransportVector_approx g hg G (K+J) hG S
  have hT : SmoothJetZero (smoothPhaseTransportScalar g b S -
      realPolyEval (formalPhaseTransportScalar G B S)) (K+J) := by
    convert smoothPolynomialLaplacian_approx g b hg hb G B (K+J) hG hB S using 1
    funext x
    simp [smoothPhaseTransportScalar, formalPhaseTransportScalar, realPolyEval]
  constructor
  · rw [← smoothWaveTransport_eq_finite]
    have h := smoothWaveTransport_jet_approx (smoothPhaseTransportVector g S)
      (contDiff_smoothPhaseTransportVector g hg S) (smoothPhaseTransportScalar g b S) 0
      (contDiff_smoothPhaseTransportScalar g b hg hb S) contDiff_const
      (formalPhaseTransportVector G S) (formalPhaseTransportScalar G B S) 0 (V 0) (K+J)
      hA hT (by
        convert SmoothJetZero.zero (E := σ → ℝ) (F := ℂ) (K+J) using 1
        ext x; simp [realPolyEval])
      (by simpa only [add_zero] using hspec.2.2.1)
    simpa only [add_zero] using h
  · intro j
    rw [← smoothWaveTransport_eq_finite, ← smoothPolynomialLaplacian_eq_operator]
    exact smoothWaveTransport_jet_approx (smoothPhaseTransportVector g S)
      (contDiff_smoothPhaseTransportVector g hg S) (smoothPhaseTransportScalar g b S)
      (smoothPolynomialLaplacian g b (V j))
      (contDiff_smoothPhaseTransportScalar g b hg hb S)
      (contDiff_smoothPolynomialLaplacian g b hg hb _)
      (formalPhaseTransportVector G S) (formalPhaseTransportScalar G B S)
      (formalPolynomialLaplacian G B (V j)) (V (j+1)) (K+J-(j+1))
      (fun i => (hA i).mono (Nat.sub_le _ _)) (hT.mono (Nat.sub_le _ _))
      ((smoothPolynomialLaplacian_approx g b hg hb G B (K+J) hG hB _).mono (Nat.sub_le _ _))
      (hspec.2.2.2 j)

def uniformSmoothWaveAmplitudes (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (S : MvPolynomial σ ℂ) (z : σ → ℂ) (K J : ℕ) :=
  symbolWaveAmplitudes (fun i j => realTaylorPolynomial (g i j) (K+J))
    (fun i => realTaylorPolynomial (b i) (K+J)) S z K J

lemma uniformSmoothWaveAmplitudes_genuine (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hg0 : ∀ i j, g i j 0 = if i = j then 1 else 0)
    (S : MvPolynomial σ ℂ) (z : σ → ℂ) (hz : z ≠ 0)
    (hS : ∀ i, constantCoeff (pderiv i S) = z i) (K J : ℕ) (hKJ : 0 < K+J) :
    let V := uniformSmoothWaveAmplitudes g b S z K J
    (∀ j, constantCoeff (V j) = if j = 0 then 1 else 0) ∧
    (∀ j, (V j).totalDegree ≤ K+J-j) ∧
    SmoothJetZero (finiteWaveTransport (fun i => Pi.single i 1) g b
      (realPolyEval S) (realPolyEval (V 0))) (K+J) ∧
    (∀ j, SmoothJetZero (fun x => finiteWaveTransport (fun i => Pi.single i 1) g b
      (realPolyEval S) (realPolyEval (V (j+1))) x +
        waveCoordinateOperator (fun i => Pi.single i 1) g b (realPolyEval (V j)) x)
      (K+J-(j+1))) := by
  let G := fun i j => realTaylorPolynomial (g i j) (K+J)
  let B := fun i => realTaylorPolynomial (b i) (K+J)
  have hG0 (i j : σ) : constantCoeff (G i j) = if i = j then 1 else 0 :=
    (realTaylorPolynomial_constant (hg i j) hKJ).trans (hg0 i j)
  have hs := symbolWaveAmplitudes_spec G B S z hz hG0 hS K J
  have hgenuine := symbolWaveAmplitudes_genuine g b hg hb G B S z hz hG0 hS K J
    (fun i j => realTaylorPolynomial_remainder (hg i j) (K+J))
    (fun i => realTaylorPolynomial_remainder (hb i) (K+J))
  exact ⟨hs.1, hs.2.1, hgenuine⟩

lemma wavePhaseSeed_coeffContinuous (c : X → ℂ) (hc : Continuous c)
    (z : X → σ → ℂ) (hz : ∀ i, Continuous (fun p => z p i))
    (Q : X → σ → σ → ℂ) (hQ : ∀ i j, Continuous (fun p => Q p i j)) :
    CoeffContinuous (fun p => wavePhaseSeed (c p) (z p) (Q p)) := by
  exact ((CoeffContinuous.C hc).add
    (CoeffContinuous.sum Finset.univ _ (fun i _ => (CoeffContinuous.C (hz i)).mul
      (CoeffContinuous.const _)))).add
    ((CoeffContinuous.sum Finset.univ _ (fun i _ => CoeffContinuous.sum Finset.univ _
      (fun j _ => ((CoeffContinuous.C (hQ i j)).mul (CoeffContinuous.const _)).mul
        (CoeffContinuous.const _)))).smul continuous_const)

lemma smoothPhasePolynomial_coeffContinuous (g : X → σ → σ → (σ → ℝ) → ℂ)
    (c : X → ℂ) (hc : Continuous c) (z : X → σ → ℂ)
    (hz : ∀ i, Continuous (fun p => z p i)) (hz₀ : ∀ p, z p ≠ 0)
    (Q : X → σ → σ → ℂ) (hQ : ∀ i j, Continuous (fun p => Q p i j)) (L : ℕ)
    (hg : ∀ i j k, k < L → Continuous (fun p => iteratedFDeriv ℝ k (g p i j) 0)) :
    CoeffContinuous (fun p => smoothPhasePolynomial (g p) (c p) (z p) (Q p) L) :=
  eikonalIter_coeffContinuous _
    (fun i j => realTaylorPolynomial_coeffContinuous _ L (hg i j)) z hz hz₀ _
    (wavePhaseSeed_coeffContinuous c hc z hz Q hQ) (L-2)

lemma uniformSmoothWaveAmplitudes_coeffContinuous (g : X → σ → σ → (σ → ℝ) → ℂ)
    (b : X → σ → (σ → ℝ) → ℂ) (S : X → MvPolynomial σ ℂ) (hS : CoeffContinuous S)
    (z : X → σ → ℂ) (hz : ∀ i, Continuous (fun p => z p i)) (hz₀ : ∀ p, z p ≠ 0)
    (K J : ℕ)
    (hg : ∀ i j k, k < K+J → Continuous (fun p => iteratedFDeriv ℝ k (g p i j) 0))
    (hb : ∀ i k, k < K+J → Continuous (fun p => iteratedFDeriv ℝ k (b p i) 0)) (j : ℕ) :
    CoeffContinuous (fun p => uniformSmoothWaveAmplitudes (g p) (b p) (S p) (z p) K J j) :=
  symbolWaveAmplitudes_coeffContinuous _ _
    (fun i j => realTaylorPolynomial_coeffContinuous _ (K+J) (hg i j))
    (fun i => realTaylorPolynomial_coeffContinuous _ (K+J) (hb i)) S hS z hz hz₀ K J j

omit [DecidableEq σ] in
lemma wavePhaseSeed_degree (c : ℂ) (z : σ → ℂ) (Q : σ → σ → ℂ) :
    (wavePhaseSeed c z Q).totalDegree ≤ 2 := by
  unfold wavePhaseSeed
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · simp
    · apply totalDegree_finsetSum_le
      intro i _
      exact (totalDegree_mul _ _).trans (by simp)
  · apply (totalDegree_smul_le _ _).trans
    apply totalDegree_finsetSum_le
    intro i _
    apply totalDegree_finsetSum_le
    intro j _
    exact (totalDegree_mul _ _).trans (by
      have h := totalDegree_mul (C (Q i j)) (MvPolynomial.X i)
      simp only [totalDegree_C, totalDegree_X, zero_add] at h ⊢
      omega)

lemma smoothPhasePolynomial_degree (g : σ → σ → (σ → ℝ) → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hg0 : ∀ i j, g i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ i j, fderiv ℝ (g i j) 0 = 0)
    (c : ℂ) (z : σ → ℂ) (Q : σ → σ → ℂ) (hz : z ≠ 0)
    (hQ : ∀ i j, Q i j = Q j i) (hnull : ∑ i, z i * z i = -1)
    (hQz : ∀ k, ∑ i, z i * Q k i = 0) (L : ℕ) (hL : 2 ≤ L) :
    (smoothPhasePolynomial g c z Q L).totalDegree ≤ L :=
  (smoothPhasePolynomial_spec g hg hg0 hdg0 c z Q hz hQ hnull hQz L hL).2.2.2.trans
    (max_le ((wavePhaseSeed_degree c z Q).trans hL) le_rfl)


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def polynomialFiniteWave (S : MvPolynomial σ ℂ) (V : ℕ → MvPolynomial σ ℂ)
    (J : ℕ) (n : ℝ) (x : σ → ℝ) : ℂ :=
  Complex.exp ((n : ℂ) * realPolyEval S x) *
    ∑ j ∈ Finset.range (J+1), ((n : ℂ)⁻¹)^j * realPolyEval (V j) x

def polynomialWaveRemainder (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (S : MvPolynomial σ ℂ) (V : ℕ → MvPolynomial σ ℂ) :
    ℕ → (σ → ℝ) → ℂ
  | 0 => smoothWaveTransport (smoothPhaseTransportVector g S)
      (smoothPhaseTransportScalar g b S) (V 0)
  | j+1 => fun x => smoothWaveTransport (smoothPhaseTransportVector g S)
      (smoothPhaseTransportScalar g b S) (V (j+1)) x + smoothPolynomialLaplacian g b (V j) x

omit [DecidableEq σ] in
lemma contDiff_polynomialWaveRemainder (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (S : MvPolynomial σ ℂ)
    (V : ℕ → MvPolynomial σ ℂ) (j : ℕ) :
    ContDiff ℝ ∞ (polynomialWaveRemainder g b S V j) := by
  have ht (j : ℕ) := contDiff_smoothWaveTransport _
    (contDiff_smoothPhaseTransportVector g hg S) _
    (contDiff_smoothPhaseTransportScalar g b hg hb S) (V j)
  cases j with
  | zero => exact ht 0
  | succ j => exact (ht (j+1)).add (contDiff_smoothPolynomialLaplacian g b hg hb (V j))

lemma smoothEikonalResidual_eq_gradientPair (g : σ → σ → (σ → ℝ) → ℂ)
    (S : MvPolynomial σ ℂ) :
    smoothEikonalResidual g S = fun x =>
      1 + waveGradientPair (fun i => Pi.single i 1) g (realPolyEval S) (realPolyEval S) x := by
  funext x
  simp only [smoothEikonalResidual, waveGradientPair, waveDeriv_realPolyEval_single]

lemma polynomial_wave_residual_expansion (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (S : MvPolynomial σ ℂ) (V : ℕ → MvPolynomial σ ℂ)
    (J : ℕ) (n : ℝ) (hn : n ≠ 0) :
    (fun x => waveCoordinateOperator (fun i => Pi.single i 1) g b
        (polynomialFiniteWave S V J n) x + (n : ℂ)*((n : ℂ)+2)*polynomialFiniteWave S V J n x) =
      fun x => (n : ℂ)^2 * (∑ j ∈ Finset.range (J+1), ((n : ℂ)⁻¹)^j *
          (Complex.exp ((n : ℂ)*realPolyEval S x) * (smoothEikonalResidual g S x * realPolyEval (V j) x))) +
        (n : ℂ) * (∑ j ∈ Finset.range (J+1), ((n : ℂ)⁻¹)^j *
          (Complex.exp ((n : ℂ)*realPolyEval S x) * polynomialWaveRemainder g b S V j x)) +
        ((n : ℂ)⁻¹)^J * (Complex.exp ((n : ℂ)*realPolyEval S x) * smoothPolynomialLaplacian g b (V J) x) := by
  funext x
  have h := finite_wave_residual (fun i => Pi.single i 1) g b (realPolyEval S)
    (contDiff_realPolyEval _) (fun j => realPolyEval (V j)) (fun j => contDiff_realPolyEval _)
    (polynomialWaveRemainder g b S V)
    (by simp only [polynomialWaveRemainder, smoothWaveTransport_eq_finite])
    (fun j => by simp only [polynomialWaveRemainder, smoothWaveTransport_eq_finite,
      smoothPolynomialLaplacian_eq_operator]) (n : ℂ) (by exact_mod_cast hn) J x
  change _ = _ at h
  rw [show polynomialFiniteWave S V J n = fun y =>
    Complex.exp ((n : ℂ)*realPolyEval S y)*
      ∑ j ∈ Finset.range (J+1), ((n : ℂ)⁻¹)^j*realPolyEval (V j) y by rfl]
  rw [h, smoothEikonalResidual_eq_gradientPair, smoothPolynomialLaplacian_eq_operator]
  simp only [Finset.mul_sum, mul_add]
  apply congrArg₂ (·+·)
  · apply congrArg₂ (·+·)
    · apply Finset.sum_congr rfl
      intro j hj
      ring
    · apply Finset.sum_congr rfl
      intro j hj
      ring
  · ring

lemma generated_wave_remainders_vanish (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hg0 : ∀ i j, g i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ i j, fderiv ℝ (g i j) 0 = 0)
    (s : ℂ) (z : σ → ℂ) (Q : σ → σ → ℂ) (hz : z ≠ 0)
    (hQ : ∀ i j, Q i j = Q j i) (hnull : ∑ i, z i*z i = -1)
    (hQz : ∀ k, ∑ i, z i*Q k i = 0) (K J : ℕ) (hK : 1 ≤ K) :
    let S := smoothPhasePolynomial g s z Q (K+J+1)
    let V := uniformSmoothWaveAmplitudes g b S z K J
    (∀ j, SmoothJetZero (fun x => smoothEikonalResidual g S x * realPolyEval (V j) x) K) ∧
    (∀ j ≤ J, SmoothJetZero (polynomialWaveRemainder g b S V j) K) := by
  dsimp only
  let S := smoothPhasePolynomial g s z Q (K+J+1)
  let V := uniformSmoothWaveAmplitudes g b S z K J
  have hs := smoothPhasePolynomial_spec g hg hg0 hdg0 s z Q hz hQ hnull hQz (K+J+1) (by omega)
  have hv := uniformSmoothWaveAmplitudes_genuine g b hg hb hg0 S z hz hs.2.1 K J (by omega)
  constructor
  · intro j
    exact (hs.2.2.1.mono (by omega)).mul_right (contDiff_smoothEikonalResidual g hg S)
      (realPolyEval (V j)) (contDiff_realPolyEval _)
  · intro j hj
    cases j with
    | zero =>
      rw [polynomialWaveRemainder, smoothWaveTransport_eq_finite]
      exact hv.2.2.1.mono (by omega)
    | succ j =>
      simp only [polynomialWaveRemainder, smoothWaveTransport_eq_finite,
        smoothPolynomialLaplacian_eq_operator]
      exact (hv.2.2.2 j).mono (by omega)

end YauCounterexamples
end

end OAI
