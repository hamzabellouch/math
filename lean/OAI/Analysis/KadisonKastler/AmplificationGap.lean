import OAI.Analysis.KadisonKastler.FiniteBlockCompression
import OAI.Analysis.KadisonKastler.WeakCPLimits

namespace OAI

/-! # Passing matrix approximants to the infinite amplification

Finite compressions have norm at most one. Weak operator compactness gives
a single limiting approximant in the target amplification, retaining the
same error at every coefficient and therefore in operator norm.
-/

namespace KadisonKastler

open Filter
open scoped BigOperators CStarAlgebra Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

local instance amplificationGapOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : PartialOrder (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrder _
local instance amplificationGapStarOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : StarOrderedRing (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrderedRing _

/-- Uniform finite matrix approximation implies approximation in the
actual countable amplification, with no loss of constant. -/
theorem exists_amplified_approx_of_matrix_approx
    (M N : VonNeumannAlgebra E) {r : ℝ} (hr : 0 ≤ r)
    (hnear : ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)),
      (∀ i j, X i j ∈ M) → ‖X‖ ≤ 1 →
      ∃ Y : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E),
        (∀ i j, Y i j ∈ N) ∧ ‖Y‖ ≤ 1 ∧ ‖X - Y‖ ≤ r)
    (T : H →L[ℂ] H) (hT : T ∈ unitBall (F.amplifiedAlgebra M)) :
    ∃ S ∈ unitBall (F.amplifiedAlgebra N), ‖T - S‖ ≤ r := by
  have hex (n : ℕ) := hnear n (F.finiteCompression n T)
    (fun i j => (F.mem_amplifiedAlgebra_iff M T).mp hT.1 i j)
    ((F.norm_finiteCompression_le n T).trans hT.2)
  choose Y hYN hYn hclose using hex
  let a (n : ℕ) := F.finiteBlock (Y n)
  have ha (n : ℕ) : a n ∈ F.amplifiedAlgebra N :=
    F.finiteBlock_mem_amplifiedAlgebra N (Y n) (hYN n)
  have han (n : ℕ) : ‖a n‖ ≤ 1 := (F.norm_finiteBlock (Y n)).le.trans (hYn n)
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨S, hSn, hlim⟩ := Generator.Tracial.exists_weak_operator_ultralimit ω a 1
    zero_le_one han
  have hSN : S ∈ F.amplifiedAlgebra N :=
    Generator.Tracial.weak_operator_limit_mem (F.amplifiedAlgebra N)
      (fun n => ⟨a n, ha n⟩) S hlim
  refine ⟨S, ⟨hSN, hSn⟩, ?_⟩
  let D (n : ℕ) := F.finiteBlock (F.finiteCompression n T) - a n
  have hDn (n : ℕ) : ‖D n‖ ≤ r := by
    have he : D n = F.finiteBlock (F.finiteCompression n T - Y n) := by
      exact (map_sub (F.finiteBlockHom n) _ _).symm
    rw [he, F.norm_finiteBlock]
    exact hclose n
  apply norm_le_of_weak_limit (l := (ω : Filter ℕ)) D (T - S) hr hDn
  intro x y
  have hleft := (F.finiteBlock_compression_tendsto T x y).mono_left hω
  simpa only [D, sub_apply, inner_sub_right] using hleft.sub (hlim x y)

/-- Common countable matrix units in the original pair make every matrix
approximation available with its original ordinary tolerance. -/
theorem kkDistance_amplifiedAlgebra_le_of_common_matrix_units
    (M N : VonNeumannAlgebra E) (D : Submodule ℂ E) [CompleteSpace D]
    (G : FullMatrixCorner D)
    (hM : ∀ i j, G.entry i j ∈ M) (hN : ∀ i j, G.entry i j ∈ N) :
    kkDistance (F.amplifiedAlgebra M) (F.amplifiedAlgebra N) ≤ kkDistance M N := by
  have happ (P Q : VonNeumannAlgebra E)
      (hP : ∀ i j, G.entry i j ∈ P) (hQ : ∀ i j, G.entry i j ∈ Q)
      {r : ℝ} (hr : kkDistance P Q < r) (n : ℕ)
      (X : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E))
      (hX : ∀ i j, X i j ∈ P) (hn : ‖X‖ ≤ 1) :
      ∃ Y : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E),
        (∀ i j, Y i j ∈ Q) ∧ ‖Y‖ ≤ 1 ∧ ‖X - Y‖ ≤ r := by
    cases n with
    | zero =>
      have hx : X = 0 := by
        apply Matrix.ext
        intro i
        exact Fin.elim0 i
      have hz : ‖(0 : CStarMatrix (Fin 0) (Fin 0) (E →L[ℂ] E))‖ = 0 := by
        rw [← F.norm_finiteBlock]
        simp [finiteBlock]
      refine ⟨0, ?_, by rw [hz]; exact zero_le_one, ?_⟩
      · intro i
        exact Fin.elim0 i
      · rw [hx, sub_self, hz]
        exact (kkDistance_nonneg P Q).trans hr.le
    | succ n =>
      obtain ⟨Y, hY, hYn, hXY⟩ := (G.finiteCuntz (n + 1)).exists_matrix_unitBall_approx
        P Q (G.finiteCuntz_mem _ P hP) (G.finiteCuntz_mem _ Q hQ) hr X hX hn
      exact ⟨Y, hY, hYn, hXY.le⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  have hr : 0 ≤ kkDistance M N + ε := add_nonneg (kkDistance_nonneg M N) hε.le
  apply Metric.hausdorffDist_le_of_mem_dist hr
  · intro T hT
    obtain ⟨S, hS, hn⟩ := F.exists_amplified_approx_of_matrix_approx M N hr
      (happ M N hM hN (lt_add_of_pos_right _ hε)) T hT
    exact ⟨S, hS, by simpa only [dist_eq_norm] using hn⟩
  · intro T hT
    obtain ⟨S, hS, hn⟩ := F.exists_amplified_approx_of_matrix_approx N M hr
      (happ N M hN hM (by rw [kkDistance_comm]; exact lt_add_of_pos_right _ hε)) T hT
    exact ⟨S, hS, by simpa only [dist_eq_norm] using hn⟩

end FullMatrixCorner

end

end KadisonKastler

end OAI
