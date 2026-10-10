import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.PolynomialFiniteWave
import OAI.Geometry.SmoothYau.Spectrum.NormIteratedFDerivConstMul

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
section UniformJetBounds
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def UniformJetBounds (f : X → E → ℂ) (K : Set X) (B : Set E) : Prop :=
  ∀ k : ℕ, ∃ C > 0, ∀ p ∈ K, ∀ x ∈ B, ‖iteratedFDeriv ℝ k (f p) x‖ ≤ C

lemma UniformJetBounds.mono {f : X → E → ℂ} {K K' : Set X} {B B' : Set E}
    (h : UniformJetBounds f K B) (hK : K' ⊆ K) (hB : B' ⊆ B) :
    UniformJetBounds f K' B' := by
  intro k
  obtain ⟨C,hC,h⟩ := h k
  exact ⟨C,hC,fun p hp x hx => h p (hK hp) x (hB hx)⟩

lemma UniformJetBounds.const (c : ℂ) (K : Set X) (B : Set E) :
    UniformJetBounds (fun _ _ => c) K B := by
  intro k
  refine ⟨‖c‖+1,by positivity,?_⟩
  intro p hp x hx
  cases k with
  | zero => simp
  | succ k => simp [iteratedFDeriv_succ_const]; positivity

lemma UniformJetBounds.add {f g : X → E → ℂ} {K : Set X} {B : Set E}
    (hf : ∀ p, ContDiff ℝ ∞ (f p)) (hg : ∀ p, ContDiff ℝ ∞ (g p))
    (hfB : UniformJetBounds f K B) (hgB : UniformJetBounds g K B) :
    UniformJetBounds (fun p x => f p x + g p x) K B := by
  intro k
  obtain ⟨C,hC,hCb⟩ := hfB k
  obtain ⟨D,hD,hDb⟩ := hgB k
  refine ⟨C+D,add_pos hC hD,?_⟩
  intro p hp x hx
  change ‖iteratedFDeriv ℝ k (f p + g p) x‖ ≤ _
  rw [iteratedFDeriv_add_apply ((hf p).of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))).contDiffAt
    ((hg p).of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hCb p hp x hx) (hDb p hp x hx))

lemma UniformJetBounds.sum {ι : Type*} (s : Finset ι) (f : ι → X → E → ℂ)
    {K : Set X} {B : Set E} (hf : ∀ i ∈ s, ∀ p, ContDiff ℝ ∞ (f i p))
    (hB : ∀ i ∈ s, UniformJetBounds (f i) K B) :
    UniformJetBounds (fun p x => ∑ i ∈ s, f i p x) K B := by
  classical
  intro k
  choose C hC hCb using fun i : s => hB i i.property k
  refine ⟨(∑ i : s, C i)+1,add_pos_of_nonneg_of_pos
    (Finset.sum_nonneg (fun i _ => (hC i).le)) zero_lt_one,?_⟩
  intro p hp x hx
  rw [iteratedFDeriv_fun_sum_apply (fun i hi =>
    ((hf i hi p).of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))).contDiffAt)]
  apply (norm_sum_le _ _).trans
  apply le_trans _ (le_add_of_nonneg_right zero_le_one)
  rw [← Finset.sum_attach]
  exact Finset.sum_le_sum (fun i _ => hCb i p hp x hx)

lemma UniformJetBounds.mul {f g : X → E → ℂ} {K : Set X} {B : Set E}
    (hf : ∀ p, ContDiff ℝ ∞ (f p)) (hg : ∀ p, ContDiff ℝ ∞ (g p))
    (hfB : UniformJetBounds f K B) (hgB : UniformJetBounds g K B) :
    UniformJetBounds (fun p x => f p x * g p x) K B := by
  intro k
  choose C hC hCb using hfB
  choose D hD hDb using hgB
  refine ⟨(∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) * C i * D (k-i))+1,
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i).le) (hD (k-i)).le)) zero_lt_one,?_⟩
  intro p hp x hx
  apply (norm_iteratedFDeriv_mul_le (hf p) (hg p) x
    (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))).trans
  apply le_trans _ (le_add_of_nonneg_right zero_le_one)
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (hCb i p hp x hx) (Nat.cast_nonneg _))
    (hDb (k-i) p hp x hx) (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (hC i).le)

lemma UniformJetBounds.common {f : X → E → ℂ} {K : Set X} {B : Set E}
    (h : UniformJetBounds f K B) (m : ℕ) :
    ∃ C ≥ 1, ∀ p ∈ K, ∀ x ∈ B, ∀ k ≤ m, ‖iteratedFDeriv ℝ k (f p) x‖ ≤ C := by
  choose C hC hCb using h
  refine ⟨1+∑ k ∈ Finset.range (m+1), C k,?_,?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ => (hC k).le))
  · intro p hp x hx k hk
    apply (hCb k p hp x hx).trans
    have hkB : C k ≤ ∑ i ∈ Finset.range (m+1), C i :=
      Finset.single_le_sum (fun i _ => (hC i).le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    exact hkB.trans (le_add_of_nonneg_left zero_le_one)

variable [TopologicalSpace X]
lemma uniformJetBounds_of_continuous_jets (f : X → E → ℂ)
    (hf : ∀ k, Continuous (fun q : X × E => iteratedFDeriv ℝ k (f q.1) q.2))
    {K : Set X} (hK : IsCompact K) {B : Set E} (hB : IsCompact B) :
    UniformJetBounds f K B := by
  intro k
  obtain ⟨C,hC⟩ := (hK.prod hB).exists_bound_of_continuousOn (hf k).continuousOn
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  exact fun p hp x hx => (hC (p,x) ⟨hp,hx⟩).trans (le_max_left _ _)
end UniformJetBounds

variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {X : Type*} [TopologicalSpace X]

omit [Fintype σ] in
lemma totalDegree_pderiv_le (i : σ) (P : MvPolynomial σ ℂ) :
    (pderiv i P).totalDegree ≤ P.totalDegree := by
  classical
  apply Finset.sup_le
  intro m hm
  have hc : P.coeff (m + Finsupp.single i 1) ≠ 0 := by
    have h := mem_support_iff.mp hm
    rw [coeff_pderiv] at h
    exact left_ne_zero_of_mul h
  have hb := le_totalDegree (mem_support_iff.mpr hc)
  have he : (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index (by simp) (by intros; rfl)]
    simp
  rw [he] at hb
  omega

omit [DecidableEq σ] in
lemma uniformJetBounds_realPolyEval (P : X → MvPolynomial σ ℂ)
    (hP : CoeffContinuous P) (N : ℕ) (hN : ∀ p, (P p).totalDegree ≤ N)
    {K : Set X} (hK : IsCompact K) {B : Set (σ → ℝ)} (hB : IsCompact B) :
    UniformJetBounds (fun p => realPolyEval (P p)) K B :=
  fun k => compact_uniform_polynomial_jets P hP N hN hK hB k

lemma uniformJetBounds_smoothPolynomialLaplacian
    (g : X → σ → σ → (σ → ℝ) → ℂ) (b : X → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (P : X → MvPolynomial σ ℂ) (hP : CoeffContinuous P) (N : ℕ)
    (hN : ∀ p, (P p).totalDegree ≤ N)
    {K : Set X} (hK : IsCompact K) {B : Set (σ → ℝ)} (hB : IsCompact B)
    (hgB : ∀ i j, UniformJetBounds (fun p => g p i j) K B)
    (hbB : ∀ i, UniformJetBounds (fun p => b p i) K B) :
    UniformJetBounds (fun p => smoothPolynomialLaplacian (g p) (b p) (P p)) K B := by
  apply UniformJetBounds.add
  · intro p
    exact ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
      (hg p i j).mul (contDiff_realPolyEval _)))
  · intro p
    exact ContDiff.sum (fun i _ => (hb p i).mul (contDiff_realPolyEval _))
  · apply UniformJetBounds.sum
    · intro i hi p
      exact ContDiff.sum (fun j _ => (hg p i j).mul (contDiff_realPolyEval _))
    · intro i hi
      apply UniformJetBounds.sum
      · intro j hj p; exact (hg p i j).mul (contDiff_realPolyEval _)
      · intro j hj
        exact (hgB i j).mul (fun p => hg p i j) (fun p => contDiff_realPolyEval _)
          (uniformJetBounds_realPolyEval _ ((hP.pderiv j).pderiv i) N
            (fun p => (totalDegree_pderiv_le _ _).trans
              ((totalDegree_pderiv_le _ _).trans (hN p))) hK hB)
  · apply UniformJetBounds.sum
    · intro i hi p; exact (hb p i).mul (contDiff_realPolyEval _)
    · intro i hi
      exact (hbB i).mul (fun p => hb p i) (fun p => contDiff_realPolyEval _)
        (uniformJetBounds_realPolyEval _ (hP.pderiv i) N
          (fun p => (totalDegree_pderiv_le _ _).trans (hN p)) hK hB)

lemma uniformJetBounds_smoothEikonalResidual
    (g : X → σ → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j))
    (S : X → MvPolynomial σ ℂ) (hS : CoeffContinuous S) (N : ℕ)
    (hN : ∀ p, (S p).totalDegree ≤ N)
    {K : Set X} (hK : IsCompact K) {B : Set (σ → ℝ)} (hB : IsCompact B)
    (hgB : ∀ i j, UniformJetBounds (fun p => g p i j) K B) :
    UniformJetBounds (fun p => smoothEikonalResidual (g p) (S p)) K B := by
  have hd (i : σ) := uniformJetBounds_realPolyEval _ (hS.pderiv i) N
    (fun p => (totalDegree_pderiv_le _ _).trans (hN p)) hK hB
  apply UniformJetBounds.add
  · intro p; exact contDiff_const
  · intro p
    exact ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
      ((hg p i j).mul (contDiff_realPolyEval _)).mul (contDiff_realPolyEval _)))
  · exact UniformJetBounds.const 1 K B
  · apply UniformJetBounds.sum
    · intro i hi p
      exact ContDiff.sum (fun j _ =>
        ((hg p i j).mul (contDiff_realPolyEval _)).mul (contDiff_realPolyEval _))
    · intro i hi
      apply UniformJetBounds.sum
      · intro j hj p
        exact ((hg p i j).mul (contDiff_realPolyEval _)).mul (contDiff_realPolyEval _)
      · intro j hj
        exact ((hgB i j).mul (fun p => hg p i j) (fun p => contDiff_realPolyEval _) (hd i)).mul
          (fun p => (hg p i j).mul (contDiff_realPolyEval _))
          (fun p => contDiff_realPolyEval _) (hd j)

lemma uniformJetBounds_smoothPhaseTransportVector
    (g : X → σ → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j))
    (S : X → MvPolynomial σ ℂ) (hS : CoeffContinuous S) (N : ℕ)
    (hN : ∀ p, (S p).totalDegree ≤ N)
    {K : Set X} (hK : IsCompact K) {B : Set (σ → ℝ)} (hB : IsCompact B)
    (hgB : ∀ i j, UniformJetBounds (fun p => g p i j) K B) (i : σ) :
    UniformJetBounds (fun p => smoothPhaseTransportVector (g p) (S p) i) K B := by
  apply UniformJetBounds.sum
  · intro j hj p
    exact ((hg p i j).add (hg p j i)).mul (contDiff_realPolyEval _)
  · intro j hj
    exact ((hgB i j).add (fun p => hg p i j) (fun p => hg p j i) (hgB j i)).mul
      (fun p => (hg p i j).add (hg p j i)) (fun p => contDiff_realPolyEval _)
      (uniformJetBounds_realPolyEval _ (hS.pderiv j) N
        (fun p => (totalDegree_pderiv_le _ _).trans (hN p)) hK hB)

lemma uniformJetBounds_smoothPhaseTransportScalar
    (g : X → σ → σ → (σ → ℝ) → ℂ) (b : X → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (S : X → MvPolynomial σ ℂ) (hS : CoeffContinuous S) (N : ℕ)
    (hN : ∀ p, (S p).totalDegree ≤ N)
    {K : Set X} (hK : IsCompact K) {B : Set (σ → ℝ)} (hB : IsCompact B)
    (hgB : ∀ i j, UniformJetBounds (fun p => g p i j) K B)
    (hbB : ∀ i, UniformJetBounds (fun p => b p i) K B) :
    UniformJetBounds (fun p => smoothPhaseTransportScalar (g p) (b p) (S p)) K B :=
  (uniformJetBounds_smoothPolynomialLaplacian g b hg hb S hS N hN hK hB hgB hbB).add
    (fun p => contDiff_smoothPolynomialLaplacian _ _ (hg p) (hb p) _) (fun _ => contDiff_const)
    (UniformJetBounds.const 2 K B)

lemma uniformJetBounds_smoothWaveTransport
    (a : X → σ → (σ → ℝ) → ℂ) (b : X → (σ → ℝ) → ℂ)
    (ha : ∀ p i, ContDiff ℝ ∞ (a p i)) (hb : ∀ p, ContDiff ℝ ∞ (b p))
    (P : X → MvPolynomial σ ℂ) (hP : CoeffContinuous P) (N : ℕ)
    (hN : ∀ p, (P p).totalDegree ≤ N)
    {K : Set X} (hK : IsCompact K) {B : Set (σ → ℝ)} (hB : IsCompact B)
    (haB : ∀ i, UniformJetBounds (fun p => a p i) K B)
    (hbB : UniformJetBounds b K B) :
    UniformJetBounds (fun p => smoothWaveTransport (a p) (b p) (P p)) K B := by
  apply UniformJetBounds.add
  · intro p
    exact ContDiff.sum (fun i _ => (ha p i).mul (contDiff_realPolyEval _))
  · intro p; exact (hb p).mul (contDiff_realPolyEval _)
  · apply UniformJetBounds.sum
    · intro i hi p; exact (ha p i).mul (contDiff_realPolyEval _)
    · intro i hi
      exact (haB i).mul (fun p => ha p i) (fun p => contDiff_realPolyEval _)
        (uniformJetBounds_realPolyEval _ (hP.pderiv i) N
          (fun p => (totalDegree_pderiv_le _ _).trans (hN p)) hK hB)
  · exact hbB.mul hb (fun p => contDiff_realPolyEval _)
      (uniformJetBounds_realPolyEval P hP N hN hK hB)

lemma uniformJetBounds_finiteWaveTransport
    (g : X → σ → σ → (σ → ℝ) → ℂ) (b : X → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (S V : X → MvPolynomial σ ℂ) (hS : CoeffContinuous S) (hV : CoeffContinuous V)
    (N M : ℕ) (hN : ∀ p, (S p).totalDegree ≤ N) (hM : ∀ p, (V p).totalDegree ≤ M)
    {K : Set X} (hK : IsCompact K) {B : Set (σ → ℝ)} (hB : IsCompact B)
    (hgB : ∀ i j, UniformJetBounds (fun p => g p i j) K B)
    (hbB : ∀ i, UniformJetBounds (fun p => b p i) K B) :
    UniformJetBounds (fun p => finiteWaveTransport (fun i => Pi.single i 1)
      (g p) (b p) (realPolyEval (S p)) (realPolyEval (V p))) K B := by
  simp only [← smoothWaveTransport_eq_finite]
  exact uniformJetBounds_smoothWaveTransport _ _
    (fun p i => contDiff_smoothPhaseTransportVector _ (hg p) _ i)
    (fun p => contDiff_smoothPhaseTransportScalar _ _ (hg p) (hb p) _)
    V hV M hM hK hB
    (uniformJetBounds_smoothPhaseTransportVector g hg S hS N hN hK hB hgB)
    (uniformJetBounds_smoothPhaseTransportScalar g b hg hb S hS N hN hK hB hgB hbB)

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {X : Type*}

lemma UniformJetBounds.finite_common (f : ℕ → X → E → ℂ) {P : Set X} {B : Set E}
    (h : ∀ j, UniformJetBounds (f j) P B) (J m : ℕ) :
    ∃ C ≥ 1, ∀ j ≤ J, ∀ p ∈ P, ∀ x ∈ B, ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k (f j p) x‖ ≤ C := by
  choose C hC hb using fun j => (h j).common m
  refine ⟨1+∑ j ∈ Finset.range (J+1), C j, ?_, ?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => zero_le_one.trans (hC j)))
  · intro j hj p hp x hx k hk
    apply (hb j p hp x hx k hk).trans
    apply le_trans (Finset.single_le_sum (fun i _ => zero_le_one.trans (hC i))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
    exact le_add_of_nonneg_left zero_le_one

variable {σ : Type*} [Fintype σ] [DecidableEq σ] [TopologicalSpace X]

lemma uniformJetBounds_polynomialWaveRemainder
    (g : X → σ → σ → (σ → ℝ) → ℂ) (b : X → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (S : X → MvPolynomial σ ℂ) (V : X → ℕ → MvPolynomial σ ℂ)
    (hS : CoeffContinuous S) (hV : ∀ j, CoeffContinuous (fun p => V p j))
    (N M : ℕ) (hN : ∀ p, (S p).totalDegree ≤ N) (hM : ∀ p j, (V p j).totalDegree ≤ M)
    {P : Set X} (hP : IsCompact P) {B : Set (σ → ℝ)} (hB : IsCompact B)
    (hgB : ∀ i j, UniformJetBounds (fun p => g p i j) P B)
    (hbB : ∀ i, UniformJetBounds (fun p => b p i) P B) (j : ℕ) :
    UniformJetBounds (fun p => polynomialWaveRemainder (g p) (b p) (S p) (V p) j) P B := by
  have ht (j : ℕ) := uniformJetBounds_finiteWaveTransport g b hg hb S (fun p => V p j)
    hS (hV j) N M hN (fun p => hM p j) hP hB hgB hbB
  simp only [← smoothWaveTransport_eq_finite] at ht
  cases j with
  | zero => exact ht 0
  | succ j =>
    exact (ht (j+1)).add
      (fun p => contDiff_smoothWaveTransport _ (contDiff_smoothPhaseTransportVector _ (hg p) _) _
        (contDiff_smoothPhaseTransportScalar _ _ (hg p) (hb p) _) _)
      (fun p => contDiff_smoothPolynomialLaplacian _ _ (hg p) (hb p) _)
      (uniformJetBounds_smoothPolynomialLaplacian g b hg hb (fun p => V p j)
        (hV j) M (fun p => hM p j) hP hB hgB hbB)

theorem generated_wave_uniform_jets
    (g : X → σ → σ → (σ → ℝ) → ℂ) (b : X → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (σ → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (σ → ℝ) => iteratedFDeriv ℝ k (b q.1 i) q.2))
    (s : X → ℂ) (hs : Continuous s) (z : X → σ → ℂ) (hz : ∀ i, Continuous (fun p => z p i))
    (hz₀ : ∀ p, z p ≠ 0) (Q : X → σ → σ → ℂ)
    (hQ : ∀ i j, Continuous (fun p => Q p i j)) (hsym : ∀ p i j, Q p i j = Q p j i)
    (hnull : ∀ p, ∑ i, z p i*z p i = -1) (hQz : ∀ p k, ∑ i, z p i*Q p k i = 0)
    (K J : ℕ) (hK : 1 ≤ K) {P : Set X} (hP : IsCompact P)
    {B : Set (σ → ℝ)} (hB : IsCompact B) :
    let S := fun p => smoothPhasePolynomial (g p) (s p) (z p) (Q p) (K+J+1)
    let V := fun p => uniformSmoothWaveAmplitudes (g p) (b p) (S p) (z p) K J
    UniformJetBounds (fun p => realPolyEval (S p)) P B ∧
    (∀ j, UniformJetBounds (fun p x => smoothEikonalResidual (g p) (S p) x * realPolyEval (V p j) x) P B) ∧
    (∀ j, UniformJetBounds (fun p => polynomialWaveRemainder (g p) (b p) (S p) (V p) j) P B) ∧
    (∀ j, UniformJetBounds (fun p => smoothPolynomialLaplacian (g p) (b p) (V p j)) P B) ∧
    (∀ j, UniformJetBounds (fun p => realPolyEval (V p j)) P B) := by
  dsimp only
  let S := fun p => smoothPhasePolynomial (g p) (s p) (z p) (Q p) (K+J+1)
  let V := fun p => uniformSmoothWaveAmplitudes (g p) (b p) (S p) (z p) K J
  have hgc0 (i j k) : Continuous (fun p => iteratedFDeriv ℝ k (g p i j) 0) :=
    (hgc i j k).comp (continuous_id.prodMk continuous_const)
  have hbc0 (i k) : Continuous (fun p => iteratedFDeriv ℝ k (b p i) 0) :=
    (hbc i k).comp (continuous_id.prodMk continuous_const)
  have hSc : CoeffContinuous S := smoothPhasePolynomial_coeffContinuous g s hs z hz hz₀ Q hQ
    (K+J+1) (fun i j k _ => hgc0 i j k)
  have hVc (j : ℕ) : CoeffContinuous (fun p => V p j) :=
    uniformSmoothWaveAmplitudes_coeffContinuous g b S hSc z hz hz₀ K J
      (fun i j k _ => hgc0 i j k) (fun i k _ => hbc0 i k) j
  have hSd (p) : (S p).totalDegree ≤ K+J+1 := smoothPhasePolynomial_degree (g p) (hg p)
    (hg0 p) (hdg0 p) (s p) (z p) (Q p) (hz₀ p) (hsym p) (hnull p) (hQz p) _ (by omega)
  have hVd (p j) : (V p j).totalDegree ≤ K+J := by
    have hS := smoothPhasePolynomial_spec (g p) (hg p) (hg0 p) (hdg0 p) (s p) (z p) (Q p)
      (hz₀ p) (hsym p) (hnull p) (hQz p) (K+J+1) (by omega)
    exact ((uniformSmoothWaveAmplitudes_genuine (g p) (b p) (hg p) (hb p) (hg0 p) (S p)
      (z p) (hz₀ p) hS.2.1 K J (by omega)).2.1 j).trans (Nat.sub_le _ _)
  have hgB (i j) := uniformJetBounds_of_continuous_jets (fun p => g p i j) (hgc i j) hP hB
  have hbB (i) := uniformJetBounds_of_continuous_jets (fun p => b p i) (hbc i) hP hB
  have hVB (j) := uniformJetBounds_realPolyEval (fun p => V p j) (hVc j) (K+J)
    (fun p => hVd p j) hP hB
  refine ⟨uniformJetBounds_realPolyEval S hSc (K+J+1) hSd hP hB, ?_, ?_, ?_, hVB⟩
  · intro j
    exact (uniformJetBounds_smoothEikonalResidual g hg S hSc (K+J+1) hSd hP hB hgB).mul
      (fun p => contDiff_smoothEikonalResidual _ (hg p) _) (fun p => contDiff_realPolyEval _) (hVB j)
  · exact uniformJetBounds_polynomialWaveRemainder g b hg hb S V hSc hVc (K+J+1) (K+J)
      hSd hVd hP hB hgB hbB
  · intro j
    exact uniformJetBounds_smoothPolynomialLaplacian g b hg hb (fun p => V p j)
      (hVc j) (K+J) (fun p => hVd p j) hP hB hgB hbB
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
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {X : Type*}

lemma norm_iteratedFDeriv_waveDeriv {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (v : E) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (waveDeriv v f) x‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ (k+1) f x‖ := by
  have h : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hb := norm_iteratedFDeriv_clm_apply_const (c := v) (x := x) h.contDiffAt
    (show (k : ℕ∞ω) ≤ ∞ by exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))
  change ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ f y v) x‖ ≤ _
  simpa only [norm_iteratedFDeriv_fderiv] using hb

lemma UniformJetBounds.waveDeriv {f : X → E → ℂ} {P : Set X} {B : Set E}
    (h : UniformJetBounds f P B) (hf : ∀ p, ContDiff ℝ ∞ (f p)) (v : E) :
    UniformJetBounds (fun p => waveDeriv v (f p)) P B := by
  intro k
  obtain ⟨C,hC,hb⟩ := h (k+1)
  refine ⟨1+‖v‖*C, by positivity, ?_⟩
  intro p hp x hx
  apply (norm_iteratedFDeriv_waveDeriv (hf p) v k x).trans
  exact (mul_le_mul_of_nonneg_left (hb p hp x hx) (norm_nonneg _)).trans
    (le_add_of_nonneg_left zero_le_one)

lemma UniformJetBounds.fixed (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (P : Set X) {B : Set E} (hB : IsCompact B) : UniformJetBounds (fun _ => f) P B := by
  intro k
  obtain ⟨C,hC⟩ := hB.exists_bound_of_continuousOn (hf.continuous_iteratedFDeriv
    (show (k : ℕ∞ω) ≤ ∞ by exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))).continuousOn
  exact ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun p hp x hx => (hC x hx).trans (le_max_left _ _)⟩

lemma SmoothJetZero.congr_eventually {f h : E → ℂ} {N : ℕ}
    (hf : SmoothJetZero f N) (he : h =ᶠ[𝓝 0] f) : SmoothJetZero h N := by
  intro k hk
  rw [(he.iteratedFDeriv (𝕜 := ℝ) k).self_of_nhds]
  exact hf k hk

variable {ι : Type*} [Fintype ι]

lemma contDiff_waveGradientPair (e : ι → E) (G : ι → ι → E → ℂ)
    (hG : ∀ i j, ContDiff ℝ ∞ (G i j)) (S V : E → ℂ)
    (hS : ContDiff ℝ ∞ S) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (waveGradientPair e G S V) :=
  ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    ((hG i j).mul (contDiff_waveDeriv (e i) S hS)).mul (contDiff_waveDeriv (e j) V hV)))

lemma contDiff_waveCoordinateOperator (e : ι → E) (G : ι → ι → E → ℂ)
    (b : ι → E → ℂ) (hG : ∀ i j, ContDiff ℝ ∞ (G i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (V : E → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (waveCoordinateOperator e G b V) :=
  (ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    (hG i j).mul (contDiff_waveDeriv (e i) _ (contDiff_waveDeriv (e j) V hV))))).add
      (ContDiff.sum (fun i _ => (hb i).mul (contDiff_waveDeriv (e i) V hV)))

lemma contDiff_finiteWaveTransport (e : ι → E) (G : ι → ι → E → ℂ)
    (b : ι → E → ℂ) (hG : ∀ i j, ContDiff ℝ ∞ (G i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (S V : E → ℂ)
    (hS : ContDiff ℝ ∞ S) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (finiteWaveTransport e G b S V) :=
  ((contDiff_waveGradientPair e G hG V S hV hS).add
    (contDiff_waveGradientPair e G hG S V hS hV)).add
      (((contDiff_waveCoordinateOperator e G b hG hb S hS).add contDiff_const).mul hV)

lemma UniformJetBounds.gradientPair (e : ι → E) (G : X → ι → ι → E → ℂ)
    (hG : ∀ p i j, ContDiff ℝ ∞ (G p i j)) (S V : X → E → ℂ)
    (hS : ∀ p, ContDiff ℝ ∞ (S p)) (hV : ∀ p, ContDiff ℝ ∞ (V p)) {P : Set X} {B : Set E}
    (hGb : ∀ i j, UniformJetBounds (fun p => G p i j) P B)
    (hSb : UniformJetBounds S P B) (hVb : UniformJetBounds V P B) :
    UniformJetBounds (fun p => waveGradientPair e (G p) (S p) (V p)) P B := by
  apply UniformJetBounds.sum
  · intro i hi p
    exact ContDiff.sum (fun j _ => ((hG p i j).mul
      (contDiff_waveDeriv _ _ (hS p))).mul (contDiff_waveDeriv _ _ (hV p)))
  · intro i hi
    apply UniformJetBounds.sum
    · intro j hj p
      exact ((hG p i j).mul (contDiff_waveDeriv _ _ (hS p))).mul (contDiff_waveDeriv _ _ (hV p))
    · intro j hj
      exact ((hGb i j).mul (fun p => hG p i j) (fun p => contDiff_waveDeriv _ _ (hS p))
        (hSb.waveDeriv hS (e i))).mul
        (fun p => (hG p i j).mul (contDiff_waveDeriv _ _ (hS p)))
        (fun p => contDiff_waveDeriv _ _ (hV p)) (hVb.waveDeriv hV (e j))

lemma UniformJetBounds.coordinateOperator (e : ι → E) (G : X → ι → ι → E → ℂ)
    (b : X → ι → E → ℂ) (hG : ∀ p i j, ContDiff ℝ ∞ (G p i j))
    (hb : ∀ p i, ContDiff ℝ ∞ (b p i)) (V : X → E → ℂ)
    (hV : ∀ p, ContDiff ℝ ∞ (V p)) {P : Set X} {B : Set E}
    (hGb : ∀ i j, UniformJetBounds (fun p => G p i j) P B)
    (hbb : ∀ i, UniformJetBounds (fun p => b p i) P B)
    (hVb : UniformJetBounds V P B) :
    UniformJetBounds (fun p => waveCoordinateOperator e (G p) (b p) (V p)) P B := by
  apply UniformJetBounds.add
  · intro p
    exact ContDiff.sum (fun i _ => ContDiff.sum (fun j _ => (hG p i j).mul
      (contDiff_waveDeriv _ _ (contDiff_waveDeriv _ _ (hV p)))))
  · intro p
    exact ContDiff.sum (fun i _ => (hb p i).mul (contDiff_waveDeriv _ _ (hV p)))
  · apply UniformJetBounds.sum
    · intro i hi p
      exact ContDiff.sum (fun j _ => (hG p i j).mul
        (contDiff_waveDeriv _ _ (contDiff_waveDeriv _ _ (hV p))))
    · intro i hi
      apply UniformJetBounds.sum
      · intro j hj p
        exact (hG p i j).mul (contDiff_waveDeriv _ _ (contDiff_waveDeriv _ _ (hV p)))
      · intro j hj
        exact (hGb i j).mul (fun p => hG p i j)
          (fun p => contDiff_waveDeriv _ _ (contDiff_waveDeriv _ _ (hV p)))
          ((hVb.waveDeriv hV (e j)).waveDeriv (fun p => contDiff_waveDeriv _ _ (hV p)) (e i))
  · apply UniformJetBounds.sum
    · intro i hi p
      exact (hb p i).mul (contDiff_waveDeriv _ _ (hV p))
    · intro i hi
      exact (hbb i).mul (fun p => hb p i) (fun p => contDiff_waveDeriv _ _ (hV p)) (hVb.waveDeriv hV (e i))

lemma UniformJetBounds.transport (e : ι → E) (G : X → ι → ι → E → ℂ)
    (b : X → ι → E → ℂ) (hG : ∀ p i j, ContDiff ℝ ∞ (G p i j))
    (hb : ∀ p i, ContDiff ℝ ∞ (b p i)) (S V : X → E → ℂ)
    (hS : ∀ p, ContDiff ℝ ∞ (S p)) (hV : ∀ p, ContDiff ℝ ∞ (V p)) {P : Set X} {B : Set E}
    (hGb : ∀ i j, UniformJetBounds (fun p => G p i j) P B)
    (hbb : ∀ i, UniformJetBounds (fun p => b p i) P B)
    (hSb : UniformJetBounds S P B) (hVb : UniformJetBounds V P B) :
    UniformJetBounds (fun p => finiteWaveTransport e (G p) (b p) (S p) (V p)) P B := by
  have hpair (p) := (contDiff_waveGradientPair e (G p) (hG p) (V p) (S p) (hV p) (hS p)).add
    (contDiff_waveGradientPair e (G p) (hG p) (S p) (V p) (hS p) (hV p))
  have hlap (p) := contDiff_waveCoordinateOperator e (G p) (b p) (hG p) (hb p) (S p) (hS p)
  exact ((UniformJetBounds.gradientPair e G hG V S hV hS hGb hVb hSb).add
    (fun p => contDiff_waveGradientPair e (G p) (hG p) (V p) (S p) (hV p) (hS p))
    (fun p => contDiff_waveGradientPair e (G p) (hG p) (S p) (V p) (hS p) (hV p))
    (UniformJetBounds.gradientPair e G hG S V hS hV hGb hSb hVb)).add hpair
    (fun p => ((hlap p).add contDiff_const).mul (hV p))
    (((UniformJetBounds.coordinateOperator e G b hG hb S hS hGb hbb hSb).add hlap
      (fun _ => contDiff_const) (UniformJetBounds.const 2 P B)).mul
      (fun p => (hlap p).add contDiff_const) hV hVb)
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
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def smoothFiniteWave (S : E → ℂ) (V : ℕ → E → ℂ) (J : ℕ) (n : ℝ) (x : E) : ℂ :=
  Complex.exp ((n : ℂ)*S x) * ∑ j ∈ Finset.range (J+1), ((n : ℂ)⁻¹)^j * V j x

def smoothWaveRemainder (e : ι → E) (g : ι → ι → E → ℂ) (b : ι → E → ℂ)
    (S : E → ℂ) (V : ℕ → E → ℂ) : ℕ → E → ℂ
  | 0 => finiteWaveTransport e g b S (V 0)
  | j+1 => fun x => finiteWaveTransport e g b S (V (j+1)) x + waveCoordinateOperator e g b (V j) x

def smoothWaveEikonal (e : ι → E) (g : ι → ι → E → ℂ) (S : E → ℂ) (x : E) : ℂ :=
  1 + waveGradientPair e g S S x

lemma contDiff_smoothWaveEikonal (e : ι → E) (g : ι → ι → E → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (S : E → ℂ) (hS : ContDiff ℝ ∞ S) :
    ContDiff ℝ ∞ (smoothWaveEikonal e g S) :=
  contDiff_const.add (contDiff_waveGradientPair e g hg S S hS hS)

lemma contDiff_smoothWaveRemainder (e : ι → E) (g : ι → ι → E → ℂ) (b : ι → E → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (S : E → ℂ) (V : ℕ → E → ℂ) (hS : ContDiff ℝ ∞ S) (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (j : ℕ) : ContDiff ℝ ∞ (smoothWaveRemainder e g b S V j) := by
  cases j with
  | zero => exact contDiff_finiteWaveTransport e g b hg hb S (V 0) hS (hV 0)
  | succ j =>
    exact (contDiff_finiteWaveTransport e g b hg hb S (V (j+1)) hS (hV (j+1))).add
      (contDiff_waveCoordinateOperator e g b hg hb (V j) (hV j))

lemma smooth_wave_residual_expansion (e : ι → E) (g : ι → ι → E → ℂ) (b : ι → E → ℂ)
    (S : E → ℂ) (V : ℕ → E → ℂ) (hS : ContDiff ℝ ∞ S) (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (J : ℕ) (n : ℝ) (hn : n ≠ 0) :
    (fun x => waveCoordinateOperator e g b (smoothFiniteWave S V J n) x +
      (n : ℂ)*((n : ℂ)+2)*smoothFiniteWave S V J n x) =
    fun x => (n : ℂ)^2 * (∑ j ∈ Finset.range (J+1), ((n : ℂ)⁻¹)^j *
      (Complex.exp ((n : ℂ)*S x) * (smoothWaveEikonal e g S x * V j x))) +
      (n : ℂ) * (∑ j ∈ Finset.range (J+1), ((n : ℂ)⁻¹)^j *
        (Complex.exp ((n : ℂ)*S x) * smoothWaveRemainder e g b S V j x)) +
      ((n : ℂ)⁻¹)^J * (Complex.exp ((n : ℂ)*S x) * waveCoordinateOperator e g b (V J) x) := by
  funext x
  have h := finite_wave_residual e g b S hS V hV (smoothWaveRemainder e g b S V)
    rfl (fun j => rfl) (n : ℂ) (by exact_mod_cast hn) J x
  unfold smoothFiniteWave
  rw [h]
  simp only [smoothWaveEikonal, Finset.mul_sum, mul_add]
  apply congrArg₂ (·+·)
  · apply congrArg₂ (·+·)
    · apply Finset.sum_congr rfl
      intro j hj
      ring
    · apply Finset.sum_congr rfl
      intro j hj
      ring
  · ring

lemma waveDeriv_congr_eventually {f h : E → ℂ} {x : E} (he : f =ᶠ[𝓝 x] h) (v : E) :
    waveDeriv v f =ᶠ[𝓝 x] waveDeriv v h := by
  filter_upwards [he.fderiv (𝕜 := ℝ)] with y hy
  exact congrArg (fun L : E →L[ℝ] ℂ => L v) hy

lemma waveGradientPair_congr_eventually (e : ι → E) (g : ι → ι → E → ℂ)
    {S T V W : E → ℂ} {x : E} (hS : S =ᶠ[𝓝 x] T) (hV : V =ᶠ[𝓝 x] W) :
    waveGradientPair e g S V =ᶠ[𝓝 x] waveGradientPair e g T W := by
  have hs : ∀ᶠ y in 𝓝 x, ∀ i, waveDeriv (e i) S y = waveDeriv (e i) T y :=
    eventually_all.mpr (fun i => waveDeriv_congr_eventually hS (e i))
  have hv : ∀ᶠ y in 𝓝 x, ∀ i, waveDeriv (e i) V y = waveDeriv (e i) W y :=
    eventually_all.mpr (fun i => waveDeriv_congr_eventually hV (e i))
  filter_upwards [hs,hv] with y hsy hvy
  simp only [waveGradientPair,hsy,hvy]

lemma waveCoordinateOperator_congr_eventually (e : ι → E) (g : ι → ι → E → ℂ)
    (b : ι → E → ℂ) {V W : E → ℂ} {x : E} (hV : V =ᶠ[𝓝 x] W) :
    waveCoordinateOperator e g b V =ᶠ[𝓝 x] waveCoordinateOperator e g b W := by
  have hv : ∀ᶠ y in 𝓝 x, ∀ i, waveDeriv (e i) V y = waveDeriv (e i) W y :=
    eventually_all.mpr (fun i => waveDeriv_congr_eventually hV (e i))
  have hvv : ∀ᶠ y in 𝓝 x, ∀ i j,
      waveDeriv (e i) (waveDeriv (e j) V) y = waveDeriv (e i) (waveDeriv (e j) W) y :=
    eventually_all.mpr (fun i => eventually_all.mpr (fun j =>
      waveDeriv_congr_eventually (waveDeriv_congr_eventually hV (e j)) (e i)))
  filter_upwards [hv,hvv] with y hvy hvvy
  simp only [waveCoordinateOperator,hvy,hvvy]

lemma finiteWaveTransport_congr_eventually (e : ι → E) (g : ι → ι → E → ℂ)
    (b : ι → E → ℂ) {S T V W : E → ℂ} {x : E}
    (hS : S =ᶠ[𝓝 x] T) (hV : V =ᶠ[𝓝 x] W) :
    finiteWaveTransport e g b S V =ᶠ[𝓝 x] finiteWaveTransport e g b T W := by
  filter_upwards [waveGradientPair_congr_eventually e g hV hS,
    waveGradientPair_congr_eventually e g hS hV,
    waveCoordinateOperator_congr_eventually e g b hS,hV] with y h₁ h₂ h₃ h₄
  simp only [finiteWaveTransport,h₁,h₂,h₃,h₄]

lemma smoothWaveRemainder_congr_eventually (e : ι → E) (g : ι → ι → E → ℂ)
    (b : ι → E → ℂ) (S : E → ℂ) {V W : ℕ → E → ℂ} {x : E}
    (hV : ∀ j, V j =ᶠ[𝓝 x] W j) (j : ℕ) :
    smoothWaveRemainder e g b S V j =ᶠ[𝓝 x] smoothWaveRemainder e g b S W j := by
  cases j with
  | zero => exact finiteWaveTransport_congr_eventually e g b EventuallyEq.rfl (hV 0)
  | succ j =>
    exact (finiteWaveTransport_congr_eventually e g b EventuallyEq.rfl (hV (j+1))).add
      (waveCoordinateOperator_congr_eventually e g b (hV j))
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
open Set Filter
open scoped Topology ContDiff
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {X : Type*}

omit [DecidableEq σ] in
theorem smooth_wave_uniform_residual_bound
    (e : σ → (σ → ℝ)) (g : X → σ → σ → (σ → ℝ) → ℂ) (b : X → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (S : X → (σ → ℝ) → ℂ) (V : X → ℕ → (σ → ℝ) → ℂ)
    (hSsmooth : ∀ p, ContDiff ℝ ∞ (S p)) (hVsmooth : ∀ p j, ContDiff ℝ ∞ (V p j))
    (m D J : ℕ) (hJ : D+m+1 ≤ J) (r c : ℝ) (hr : r ≤ 1) (hc : 0 < c)
    (P : Set X)
    (hS : UniformJetBounds (fun p => S p) P (Metric.ball 0 r))
    (hF : ∀ j, UniformJetBounds (fun p x => smoothWaveEikonal e (g p) (S p) x * V p j x)
      P (Metric.ball 0 r))
    (hR : ∀ j, UniformJetBounds (fun p => smoothWaveRemainder e (g p) (b p) (S p) (V p) j)
      P (Metric.ball 0 r))
    (hL : UniformJetBounds (fun p => waveCoordinateOperator e (g p) (b p) (V p J)) P (Metric.ball 0 r))
    (hFzero : ∀ p ∈ P, ∀ j ≤ J, SmoothJetZero
      (fun x => smoothWaveEikonal e (g p) (S p) x * V p j x) (2*D+3*m+6))
    (hRzero : ∀ p ∈ P, ∀ j ≤ J, SmoothJetZero
      (smoothWaveRemainder e (g p) (b p) (S p) (V p) j) (2*D+3*m+6)) :
    ∃ C > 0, ∀ p ∈ P, ∀ n : ℝ, 1 ≤ n → ∀ x ∈ Metric.ball (0 : σ → ℝ) r,
      ∀ φ : ℝ, n*((S p x).re-φ) ≤ Real.sqrt n*‖x‖-c*n*‖x‖^2 →
      ∀ k ≤ m, ‖iteratedFDeriv ℝ k (fun y =>
        waveCoordinateOperator e (g p) (b p) (smoothFiniteWave (S p) (V p) J n) y +
         (n : ℂ)*((n : ℂ)+2)*smoothFiniteWave (S p) (V p) J n y) x‖ ≤
        C*(n^(D+1))⁻¹*Real.exp (n*φ) := by
  obtain ⟨CS,hCS,hSb⟩ := hS.common m
  obtain ⟨CF,hCF,hFb⟩ := UniformJetBounds.finite_common _ hF J (2*D+3*m+6)
  obtain ⟨CR,hCR,hRb⟩ := UniformJetBounds.finite_common _ hR J (2*D+3*m+6)
  obtain ⟨CL,hCL,hLb⟩ := hL.common m
  let A := max CF (max CR CL)
  have hFA : CF ≤ A := le_max_left _ _
  have hRA : CR ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hLA : CL ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  have hA : 0 ≤ A := zero_le_one.trans (hCF.trans hFA)
  let Ck := fun k => 2*(J+1 : ℕ) *
      (expJetConstant k CS*A*((2*(k+(D+3))).factorial : ℝ)*Real.exp c⁻¹) +
        expJetConstant k CS*A*Real.exp c⁻¹
  have hCk (k : ℕ) : 0 ≤ Ck k := by
    dsimp [Ck]
    have he := expJetConstant_nonneg k (zero_le_one.trans hCS)
    positivity
  let C := 1+∑ k ∈ Finset.range (m+1), Ck k
  have hC : 0 < C := by
    dsimp [C]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun k _ => hCk k))
  refine ⟨C,hC,?_⟩
  intro p hp n hn x hx φ hphase k hk
  have hCkC : Ck k ≤ C := (Finset.single_le_sum (fun i _ => hCk i)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))).trans (le_add_of_nonneg_left zero_le_one)
  have horder : 2*D+3*k+6 ≤ 2*D+3*m+6 := by omega
  have hbound := finite_scheduled_residual_bound (S p)
    (fun j x => smoothWaveEikonal e (g p) (S p) x * V p j x)
    (smoothWaveRemainder e (g p) (b p) (S p) (V p))
    (waveCoordinateOperator e (g p) (b p) (V p J))
    (hSsmooth p) (fun j => (contDiff_smoothWaveEikonal e _ (hg p) _ (hSsmooth p)).mul (hVsmooth p j))
    (contDiff_smoothWaveRemainder e _ _ (hg p) (hb p) _ _ (hSsmooth p) (hVsmooth p))
    (contDiff_waveCoordinateOperator e _ _ (hg p) (hb p) _ (hVsmooth p J))
    k D J (by omega) x CS A n φ c r hCS hA hn hc hr hx
    (fun i hi hik => hSb p hp x hx i (hik.trans hk))
    (fun j hj => (hFzero p hp j hj).mono horder)
    (fun j hj => (hRzero p hp j hj).mono horder)
    (fun j hj y hy => (hFb j hj p hp y hy _ horder).trans hFA)
    (fun j hj y hy => (hRb j hj p hp y hy _ horder).trans hRA)
    (fun i hi => (hLb p hp x hx i (hi.trans hk)).trans hLA) hphase
  rw [smooth_wave_residual_expansion e _ _ _ _ (hSsmooth p) (hVsmooth p) _ n (ne_of_gt (zero_lt_one.trans_le hn))]
  apply hbound.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCkC (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hn) _)))
    (Real.exp_pos _).le

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
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {X : Type*}

lemma smoothWaveEikonal_realPolyEval (g : σ → σ → (σ → ℝ) → ℂ) (S : MvPolynomial σ ℂ) :
    smoothWaveEikonal (fun i => Pi.single i 1) g (realPolyEval S) = smoothEikonalResidual g S :=
  (smoothEikonalResidual_eq_gradientPair g S).symm

lemma smoothWaveRemainder_realPolyEval (g : σ → σ → (σ → ℝ) → ℂ) (b : σ → (σ → ℝ) → ℂ)
    (S : MvPolynomial σ ℂ) (V : ℕ → MvPolynomial σ ℂ) (j : ℕ) :
    smoothWaveRemainder (fun i => Pi.single i 1) g b (realPolyEval S) (fun j => realPolyEval (V j)) j =
      polynomialWaveRemainder g b S V j := by
  cases j with
  | zero => exact (smoothWaveTransport_eq_finite g b S (V 0)).symm
  | succ j =>
    simp only [smoothWaveRemainder,polynomialWaveRemainder,
      smoothWaveTransport_eq_finite,smoothPolynomialLaplacian_eq_operator]

lemma cutoff_polynomial_remainders_vanish
    (g : σ → σ → (σ → ℝ) → ℂ) (b : σ → (σ → ℝ) → ℂ)
    (S : MvPolynomial σ ℂ) (V : ℕ → MvPolynomial σ ℂ)
    (ζ : (σ → ℝ) → ℂ) (hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (K : ℕ)
    (hF : ∀ j, SmoothJetZero (fun x => smoothEikonalResidual g S x * realPolyEval (V j) x) K)
    (J : ℕ) (hR : ∀ j ≤ J, SmoothJetZero (polynomialWaveRemainder g b S V j) K) :
    (∀ j, SmoothJetZero (fun x => smoothWaveEikonal (fun i => Pi.single i 1) g (realPolyEval S) x *
      (ζ x * realPolyEval (V j) x)) K) ∧
    (∀ j ≤ J, SmoothJetZero (smoothWaveRemainder (fun i => Pi.single i 1) g b (realPolyEval S)
      (fun j x => ζ x * realPolyEval (V j) x) j) K) := by
  have hV (j) : (fun x => ζ x * realPolyEval (V j) x) =ᶠ[𝓝 0] realPolyEval (V j) := by
    filter_upwards [hζ] with x hx
    simp only [hx,one_mul]
  constructor
  · intro j
    apply (hF j).congr_eventually
    rw [smoothWaveEikonal_realPolyEval]
    exact EventuallyEq.rfl.mul (hV j)
  · intro j hj
    apply (hR j hj).congr_eventually
    rw [← smoothWaveRemainder_realPolyEval]
    exact smoothWaveRemainder_congr_eventually _ _ _ _ hV j

omit [DecidableEq σ] in
lemma uniformJetBounds_smoothWaveEikonal
    (e : σ → (σ → ℝ)) (g : X → σ → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (S : X → (σ → ℝ) → ℂ)
    (hS : ∀ p, ContDiff ℝ ∞ (S p)) {P : Set X} {B : Set (σ → ℝ)}
    (hgB : ∀ i j, UniformJetBounds (fun p => g p i j) P B)
    (hSB : UniformJetBounds S P B) :
    UniformJetBounds (fun p => smoothWaveEikonal e (g p) (S p)) P B :=
  (UniformJetBounds.const 1 P B).add (fun _ => contDiff_const)
    (fun p => contDiff_waveGradientPair e (g p) (hg p) (S p) (S p) (hS p) (hS p))
    (UniformJetBounds.gradientPair e g hg S S hS hS hgB hSB hSB)

omit [DecidableEq σ] in
lemma uniformJetBounds_smoothWaveRemainder
    (e : σ → (σ → ℝ)) (g : X → σ → σ → (σ → ℝ) → ℂ) (b : X → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (S : X → (σ → ℝ) → ℂ) (V : X → ℕ → (σ → ℝ) → ℂ)
    (hS : ∀ p, ContDiff ℝ ∞ (S p)) (hV : ∀ p j, ContDiff ℝ ∞ (V p j))
    {P : Set X} {B : Set (σ → ℝ)}
    (hgB : ∀ i j, UniformJetBounds (fun p => g p i j) P B)
    (hbB : ∀ i, UniformJetBounds (fun p => b p i) P B)
    (hSB : UniformJetBounds S P B) (hVB : ∀ j, UniformJetBounds (fun p => V p j) P B) (j : ℕ) :
    UniformJetBounds (fun p => smoothWaveRemainder e (g p) (b p) (S p) (V p) j) P B := by
  cases j with
  | zero =>
    exact UniformJetBounds.transport e g b hg hb S (fun p => V p 0) hS
      (fun p => hV p 0) hgB hbB hSB (hVB 0)
  | succ j =>
    exact (UniformJetBounds.transport e g b hg hb S (fun p => V p (j+1)) hS
      (fun p => hV p (j+1)) hgB hbB hSB (hVB (j+1))).add
      (fun p => contDiff_finiteWaveTransport e (g p) (b p) (hg p) (hb p) (S p) (V p (j+1)) (hS p) (hV p (j+1)))
      (fun p => contDiff_waveCoordinateOperator e (g p) (b p) (hg p) (hb p) (V p j) (hV p j))
      (UniformJetBounds.coordinateOperator e g b hg hb (fun p => V p j) (fun p => hV p j) hgB hbB (hVB j))

theorem cutoff_polynomial_wave_residual_bound
    (g : X → σ → σ → (σ → ℝ) → ℂ) (b : X → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (S : X → MvPolynomial σ ℂ) (V : X → ℕ → MvPolynomial σ ℂ)
    (ζ : (σ → ℝ) → ℂ) (hζ : ContDiff ℝ ∞ ζ) (hζ₀ : ζ =ᶠ[𝓝 0] fun _ => 1)
    (m D J : ℕ) (hJ : D+m+1 ≤ J) (r c : ℝ) (hr : r ≤ 1) (hc : 0 < c)
    (P : Set X)
    (hgB : ∀ i j, UniformJetBounds (fun p => g p i j) P (Metric.ball 0 r))
    (hbB : ∀ i, UniformJetBounds (fun p => b p i) P (Metric.ball 0 r))
    (hSB : UniformJetBounds (fun p => realPolyEval (S p)) P (Metric.ball 0 r))
    (hVB : ∀ j, UniformJetBounds (fun p => realPolyEval (V p j)) P (Metric.ball 0 r))
    (hFzero : ∀ p ∈ P, ∀ j, SmoothJetZero
      (fun x => smoothEikonalResidual (g p) (S p) x * realPolyEval (V p j) x) (2*D+3*m+6))
    (hRzero : ∀ p ∈ P, ∀ j ≤ J, SmoothJetZero
      (polynomialWaveRemainder (g p) (b p) (S p) (V p) j) (2*D+3*m+6)) :
    ∃ C > 0, ∀ p ∈ P, ∀ n : ℝ, 1 ≤ n → ∀ x ∈ Metric.ball (0 : σ → ℝ) r,
      ∀ φ : ℝ, n*((realPolyEval (S p) x).re-φ) ≤ Real.sqrt n*‖x‖-c*n*‖x‖^2 →
      ∀ k ≤ m, ‖iteratedFDeriv ℝ k (fun y =>
        waveCoordinateOperator (fun i => Pi.single i 1) (g p) (b p)
          (smoothFiniteWave (realPolyEval (S p)) (fun j x => ζ x * realPolyEval (V p j) x) J n) y +
         (n : ℂ)*((n : ℂ)+2)*smoothFiniteWave (realPolyEval (S p))
          (fun j x => ζ x * realPolyEval (V p j) x) J n y) x‖ ≤
        C*(n^(D+1))⁻¹*Real.exp (n*φ) := by
  let W := fun p j x => ζ x * realPolyEval (V p j) x
  have hW (p j) : ContDiff ℝ ∞ (W p j) := hζ.mul (contDiff_realPolyEval _)
  have hζB : UniformJetBounds (fun _ : X => ζ) P (Metric.ball 0 r) :=
    (UniformJetBounds.fixed ζ hζ P (isCompact_closedBall 0 r)).mono subset_rfl Metric.ball_subset_closedBall
  have hWB (j) : UniformJetBounds (fun p => W p j) P (Metric.ball 0 r) :=
    hζB.mul (fun _ => hζ) (fun _ => contDiff_realPolyEval _) (hVB j)
  have hE := uniformJetBounds_smoothWaveEikonal (fun i => Pi.single i 1) g hg
    (fun p => realPolyEval (S p)) (fun _ => contDiff_realPolyEval _) hgB hSB
  apply smooth_wave_uniform_residual_bound (fun i => Pi.single i 1) g b hg hb
    (fun p => realPolyEval (S p)) W (fun _ => contDiff_realPolyEval _) hW m D J hJ r c hr hc P hSB
  · intro j
    exact hE.mul (fun p => contDiff_smoothWaveEikonal _ _ (hg p) _ (contDiff_realPolyEval _))
      (fun p => hW p j) (hWB j)
  · exact uniformJetBounds_smoothWaveRemainder _ g b hg hb _ W (fun _ => contDiff_realPolyEval _) hW hgB hbB hSB hWB
  · exact UniformJetBounds.coordinateOperator _ g b hg hb (fun p => W p J) (fun p => hW p J) hgB hbB (hWB J)
  · intro p hp j hj
    exact (cutoff_polynomial_remainders_vanish (g p) (b p) (S p) (V p) ζ hζ₀ _
      (hFzero p hp) J (hRzero p hp)).1 j
  · intro p hp j hj
    exact (cutoff_polynomial_remainders_vanish (g p) (b p) (S p) (V p) ζ hζ₀ _
      (hFzero p hp) J (hRzero p hp)).2 j hj
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
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : Type*}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma smoothFiniteWave_eq_sum (S : E → ℂ) (V : ℕ → E → ℂ) (J : ℕ) (n : ℝ) :
    smoothFiniteWave S V J n = fun x => ∑ j ∈ Finset.range (J+1),
      ((n : ℂ)⁻¹)^j * (Complex.exp ((n : ℂ)*S x)*V j x) := by
  funext x
  simp only [smoothFiniteWave,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma smoothFiniteWave_cutoff (S : E → ℂ) (V : ℕ → E → ℂ) (ζ : E → ℂ) (J : ℕ) (n : ℝ) :
    smoothFiniteWave S (fun j x => ζ x * V j x) J n = fun x => ζ x * smoothFiniteWave S V J n x := by
  funext x
  simp only [smoothFiniteWave,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma smoothFiniteWave_cutoff_support (S : E → ℂ) (V : ℕ → E → ℂ) (ζ : E → ℂ) (J : ℕ) (n : ℝ) :
    Function.support (smoothFiniteWave S (fun j x => ζ x * V j x) J n) ⊆ Function.support ζ := by
  rw [smoothFiniteWave_cutoff]
  exact Function.support_mul_subset_left _ _

omit [NormedSpace ℝ E] in
lemma smoothFiniteWave_cutoff_compact (S : E → ℂ) (V : ℕ → E → ℂ) (ζ : E → ℂ)
    (hζ : HasCompactSupport ζ) (J : ℕ) (n : ℝ) :
    HasCompactSupport (smoothFiniteWave S (fun j x => ζ x * V j x) J n) :=
  hζ.mono (smoothFiniteWave_cutoff_support S V ζ J n)

theorem smooth_finite_wave_uniform_derivatives (S : X → E → ℂ) (V : X → ℕ → E → ℂ)
    (hS : ∀ p, ContDiff ℝ ∞ (S p)) (hV : ∀ p j, ContDiff ℝ ∞ (V p j))
    (m J : ℕ) {P : Set X} {B : Set E}
    (hSB : UniformJetBounds S P B) (hVB : ∀ j, UniformJetBounds (fun p => V p j) P B)
    (c : ℝ) (hc : 0 < c) :
    ∃ C > 0, ∀ p ∈ P, ∀ n : ℝ, 1 ≤ n → ∀ x ∈ B, ∀ φ : ℝ,
      n*((S p x).re-φ) ≤ Real.sqrt n*‖x‖-c*n*‖x‖^2 → ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k (smoothFiniteWave (S p) (V p) J n) x‖ ≤ C*n^k*Real.exp (n*φ) := by
  obtain ⟨CS,hCS,hSb⟩ := hSB.common m
  obtain ⟨CV,hCV,hVb⟩ := UniformJetBounds.finite_common _ hVB J m
  let Ck := fun k => (J+1 : ℕ)*expJetConstant k CS*CV*Real.exp c⁻¹
  have hCk (k) : 0 ≤ Ck k := by
    dsimp [Ck]
    have he := expJetConstant_nonneg k (zero_le_one.trans hCS)
    positivity
  let C := 1+∑ k ∈ Finset.range (m+1), Ck k
  have hC : 0 < C := by
    dsimp [C]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun k _ => hCk k)
  refine ⟨C,hC,?_⟩
  intro p hp n hn x hx φ hphase k hk
  have hCkC : Ck k ≤ C := (Finset.single_le_sum (fun i _ => hCk i)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))).trans (le_add_of_nonneg_left zero_le_one)
  have he : ∀ j, ContDiff ℝ ∞ (fun y => Complex.exp ((n : ℂ)*S p y)*V p j y) := fun j =>
    (Complex.contDiff_exp.comp (contDiff_const.mul (hS p))).mul (hV p j)
  have hec := expJetConstant_nonneg k (zero_le_one.trans hCS)
  rw [smoothFiniteWave_eq_sum]
  apply (norm_iteratedFDeriv_weighted_sum _ he J k x _ (inverse_frequency_norm_le_one hn)
    (expJetConstant k CS*CV*Real.exp c⁻¹*n^k*Real.exp (n*φ)) (by positivity)
    (fun j hj => bounded_wave_term (S p) (V p j) (hS p) (hV p j) k x CS CV n φ c hCS
      (zero_le_one.trans hCV) hn hc
      (fun i hi hik => hSb p hp x hx i (hik.trans hk))
      (fun i hi => hVb j hj p hp x hx i (hi.trans hk)) hphase)).trans
  calc
    _ = Ck k*n^k*Real.exp (n*φ) := by dsimp [Ck]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCkC (pow_nonneg (zero_le_one.trans hn) _)) (Real.exp_pos _).le

end YauCounterexamples
end

end OAI
