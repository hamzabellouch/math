import OAI.NumberTheory.DukePrimeDegree.Entropy.CompactSmallObservations
import OAI.NumberTheory.DukePrimeDegree.Dynamics.CentralizerContraction
import OAI.NumberTheory.DukePrimeDegree.Entropy.DiagonalEntropy

namespace OAI

/-! # Consistent small lifts of compact future itineraries

On an orbit staying in a compact set, sufficiently fine finite observations
force the small relative lifts to evolve by diagonal conjugation. Boundedness
then excludes every expanding matrix entry.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma small_future_lifts_conjugate {n : ℕ} (a : G n) (x y : X n)
    {L r : ℝ} (hL : 1 ≤ L) (hr : 0 < r)
    (hexpand : (MulAut.conj a⁻¹) '' matrixBall n r ⊆ matrixBall n (L*r))
    (hinj : ∀ k : ℕ, Set.InjOn
      (fun g => rightAction ((fun z => rightAction z a)^[k+1] x) g)
        (matrixBall n (L*r)))
    (g : ℕ → G n) (hg : ∀ k, g k ∈ matrixBall n r)
    (hlift : ∀ k, rightAction ((fun z => rightAction z a)^[k] x) (g k) =
      (fun z => rightAction z a)^[k] y) :
    ∀ k, g k = (MulAut.conj a⁻¹)^[k] (g 0) := by
  have hstep (k : ℕ) : g (k+1) = MulAut.conj a⁻¹ (g k) := by
    apply hinj k
    · exact matrixBall_mono (le_mul_of_one_le_left hr.le hL) (hg (k+1))
    · exact hexpand ⟨g k,hg k,rfl⟩
    · change rightAction ((fun z => rightAction z a)^[k+1] x) (g (k+1)) =
        rightAction ((fun z => rightAction z a)^[k+1] x) (MulAut.conj a⁻¹ (g k))
      rw [hlift (k+1),Function.iterate_succ_apply',←hlift k,
        rightAction_conjugation]
      rw [Function.iterate_succ_apply']
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [hstep,Function.iterate_succ_apply',ih]

theorem exists_observation_with_bounded_future_lift {n : ℕ}
    (K : Set (X n)) (hK : IsCompact K)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) :
    ∃ (N : ℕ) (Q : X n → Fin N), Measurable Q ∧
      ∀ x y, (∀ k : ℕ,
          (fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x ∈ K) →
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
            Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ g : G n, rightAction x g=y ∧
          ∀ i j, ell j < ell i → g.val i j=0 := by
  obtain ⟨R,hR,hRinj⟩ := compact_uniform_chart_injective K hK
  have hn : ∑ i, -ell i=0 := by simp only [Finset.sum_neg_distrib,hell,neg_zero]
  obtain ⟨L,hL,hexpand⟩ := diagonal_conjugation_expansion (fun i => -ell i) hn
  have hparam : diagonalOneParameter (fun i => -ell i) hn (-1) =
      diagonalOneParameter ell hell 1 := by
    simpa only [neg_neg] using diagonalOneParameter_neg_weights ell hell (-1)
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let r : ℝ := R/L
  have hr : 0 < r := div_pos hR hLp
  have hLr : L*r=R := by dsimp [r]; field_simp
  obtain ⟨N,Q,hQ,hsmall⟩ := exists_finite_observation_small_lifts K hK
    (matrixBall n r) ((matrixBall_isOpen n r).mem_nhds (one_mem_matrixBall n hr))
  refine ⟨N,Q,hQ,?_⟩
  intro x y hx hxy
  let a := diagonalOneParameter ell hell (-1)
  let T : X n → X n := fun z => rightAction z a
  choose g hg hlift using fun k => hsmall (T^[k] x) (hx k) (T^[k] y) (hxy k)
  have hex : (MulAut.conj a⁻¹) '' matrixBall n r ⊆ matrixBall n (L*r) := by
    have ha : diagonalOneParameter (fun i => -ell i) hn (-1) = a⁻¹ :=
      hparam.trans (by dsimp [a]; rw [diagonalOneParameter_neg,inv_inv])
    exact ha ▸ hexpand r hr
  have hconj := small_future_lifts_conjugate a x y hL hr hex
    (fun k => by rw [hLr]; exact hRinj _ (hx (k+1))) g hg hlift
  refine ⟨g 0,by simpa only [Function.iterate_zero,Function.id_def] using hlift 0,?_⟩
  intro i j hij
  apply conjugation_expanding_entry_eq_zero ell hell (g 0)
    tendsto_natCast_atTop_atTop (r+1) _ hij
  apply Eventually.of_forall
  intro k p q
  have hp : a^k=diagonalOneParameter ell hell (-(k:ℝ)) := by
    dsimp [a]
    rw [diagonalOneParameter_neg,inv_pow,←diagonalOneParameter_nat,diagonalOneParameter_neg]
  have he : diagonalOneParameter ell hell (k:ℝ)*g 0*
      diagonalOneParameter ell hell (-(k:ℝ))=g k := by
    calc
      _ = (MulAut.conj a⁻¹)^[k] (g 0) := by
        rw [conjugation_iterate,hp,←diagonalOneParameter_neg,neg_neg]
      _ = g k := (hconj k).symm
  rw [he]
  have hb := hg k p q
  change |(g k).val p q-(1 : Matrix (Fin n) (Fin n) ℝ) p q| < r at hb
  have hone : |(1 : Matrix (Fin n) (Fin n) ℝ) p q| ≤ 1 := by
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  calc
    |(g k).val p q| = |((g k).val p q-(1 : Matrix (Fin n) (Fin n) ℝ) p q)+
        (1 : Matrix (Fin n) (Fin n) ℝ) p q| := by congr 1; ring
    _ ≤ |(g k).val p q-(1 : Matrix (Fin n) (Fin n) ℝ) p q|+
        |(1 : Matrix (Fin n) (Fin n) ℝ) p q| := abs_add_le _ _
    _ ≤ r+1 := by linarith

theorem exists_observation_with_upper_triangular_future_lift {n : ℕ}
    (K : Set (X n)) (hK : IsCompact K)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (hmono : StrictMono ell) :
    ∃ (N : ℕ) (Q : X n → Fin N), Measurable Q ∧
      ∀ x y, (∀ k : ℕ,
          (fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x ∈ K) →
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
            Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ g : G n, rightAction x g=y ∧ ∀ i j, j < i → g.val i j=0 := by
  obtain ⟨N,Q,hQ,h⟩ := exists_observation_with_bounded_future_lift K hK ell hell
  refine ⟨N,Q,hQ,?_⟩
  intro x y hx hxy
  obtain ⟨g,hg,hzero⟩ := h x y hx hxy
  exact ⟨g,hg,fun i j hij => hzero i j (hmono hij)⟩

end DukePrimeDegree

end

end OAI
