import OAI.NumberTheory.DukePrimeDegree.Entropy.CompactFutureLifts
import Mathlib.Topology.Compactness.Lindelof

namespace OAI

/-! # Countable future observations with locally controlled lifts

The observation cells adapt to the local injectivity radius both before
and after one diagonal step. Two valid injectivity balls are nested, so
successive relative lifts agree even when their radii differ. No compact
orbit assumption or finite-entropy hypothesis is required for the
resulting countable observation.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

private theorem exists_local_lift_control {n : ℕ} (a : G n)
    {L : ℝ} (hL : 1 ≤ L) (x : X n) :
    ∃ (U : Set (X n)) (r : ℝ), IsOpen U ∧ x ∈ U ∧ 0 < r ∧ r ≤ 1 ∧
      (∀ z ∈ U, Set.InjOn (fun g => rightAction z g) (matrixBall n r)) ∧
      (∀ z ∈ U, Set.InjOn (fun g => rightAction (rightAction z a) g)
        (matrixBall n (L*r))) ∧
      ∀ z ∈ U, ∀ y ∈ U, ∃ g ∈ matrixBall n r, rightAction z g=y := by
  obtain ⟨U,hU,hx,R,hR,hUi⟩ := local_uniform_chart_injective x
  obtain ⟨V,hV,hTx,S,hS,hVi⟩ := local_uniform_chart_injective (rightAction x a)
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let r := min 1 (min R (S/L))
  have hr : 0 < r := lt_min zero_lt_one (lt_min hR (div_pos hS hLp))
  have hrR : r ≤ R := (min_le_right _ _).trans (min_le_left _ _)
  have hrS : L*r ≤ S := by
    have hh : r ≤ S/L := (min_le_right _ _).trans (min_le_right _ _)
    nlinarith [(le_div_iff₀ hLp).mp hh]
  obtain ⟨W,hW,hxW,hsmall⟩ := exists_open_small_relative_lifts x (matrixBall n r)
    ((matrixBall_isOpen n r).mem_nhds (one_mem_matrixBall n hr))
  refine ⟨U ∩ ((fun z => rightAction z a) ⁻¹' V) ∩ W,r,
    (hU.inter (hV.preimage (continuous_rightAction a))).inter hW,
    ⟨⟨hx,hTx⟩,hxW⟩,hr,min_le_left _ _,?_,?_,?_⟩
  · intro z hz
    exact (hUi z hz.1.1).mono (matrixBall_mono hrR)
  · intro z hz
    exact (hVi _ hz.1.2).mono (matrixBall_mono hrS)
  · intro z hz y hy
    exact hsmall z hz.2 y hy.2

lemma variable_future_lifts_conjugate {n : ℕ} (a : G n) (x y : X n)
    (L : ℝ) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k)
    (hexpand : ∀ s, 0 < s →
      (MulAut.conj a⁻¹) '' matrixBall n s ⊆ matrixBall n (L*s))
    (hinj : ∀ k : ℕ, Set.InjOn
      (fun g => rightAction ((fun z => rightAction z a)^[k] x) g)
        (matrixBall n (r k)))
    (hnext : ∀ k : ℕ, Set.InjOn
      (fun g => rightAction ((fun z => rightAction z a)^[k+1] x) g)
        (matrixBall n (L*r k)))
    (g : ℕ → G n) (hg : ∀ k, g k ∈ matrixBall n (r k))
    (hlift : ∀ k, rightAction ((fun z => rightAction z a)^[k] x) (g k) =
      (fun z => rightAction z a)^[k] y) :
    ∀ k, g k = (MulAut.conj a⁻¹)^[k] (g 0) := by
  have hstep (k : ℕ) : g (k+1) = MulAut.conj a⁻¹ (g k) := by
    have he : rightAction ((fun z => rightAction z a)^[k+1] x) (g (k+1)) =
        rightAction ((fun z => rightAction z a)^[k+1] x) (MulAut.conj a⁻¹ (g k)) := by
      rw [hlift (k+1),Function.iterate_succ_apply',←hlift k,rightAction_conjugation,
        Function.iterate_succ_apply']
    have hc := hexpand (r k) (hr k) ⟨g k,hg k,rfl⟩
    rcases le_total (r (k+1)) (L*r k) with h | h
    · exact hnext k (matrixBall_mono h (hg (k+1))) hc he
    · exact hinj (k+1) (hg (k+1)) (matrixBall_mono h hc) he
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [hstep,Function.iterate_succ_apply',ih]

theorem exists_countable_observation_with_triangular_future_lifts {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) :
    ∃ Q : X n → ℕ, Measurable Q ∧
      ∀ x y, (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
            Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ g : G n, rightAction x g=y ∧ ∀ i j, ell j < ell i → g.val i j=0 := by
  classical
  let a := diagonalOneParameter ell hell (-1)
  let T : X n → X n := fun z => rightAction z a
  have hn : ∑ i, -ell i=0 := by simp only [Finset.sum_neg_distrib,hell,neg_zero]
  obtain ⟨L,hL,hexpand⟩ := diagonal_conjugation_expansion (fun i => -ell i) hn
  have hparam : diagonalOneParameter (fun i => -ell i) hn (-1) = a⁻¹ := by
    calc
      _ = diagonalOneParameter ell hell 1 := by
        simpa only [neg_neg] using diagonalOneParameter_neg_weights ell hell (-1)
      _ = _ := by dsimp [a]; rw [diagonalOneParameter_neg,inv_inv]
  have hex (s : ℝ) (hs : 0 < s) :
      (MulAut.conj a⁻¹) '' matrixBall n s ⊆ matrixBall n (L*s) :=
    hparam ▸ hexpand s hs
  choose U r hU hxU hr hr1 hinj hnext hsmall using exists_local_lift_control a hL
  obtain ⟨f,hf⟩ := isLindelof_univ.indexed_countable_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x,hxU x⟩)
  have hcov (x : X n) : ∃ k, x ∈ U (f k) := mem_iUnion.mp (hf (mem_univ x))
  let Q : X n → ℕ := fun x => Nat.find (hcov x)
  have hQ : Measurable Q := measurable_find hcov (fun k => (hU (f k)).measurableSet)
  have hmem (x : X n) : x ∈ U (f (Q x)) := Nat.find_spec (hcov x)
  refine ⟨Q,hQ,?_⟩
  intro x y hxy
  let R : ℕ → ℝ := fun k => r (f (Q (T^[k] x)))
  have hRm (k : ℕ) : T^[k] x ∈ U (f (Q (T^[k] x))) := hmem _
  have hRy (k : ℕ) : T^[k] y ∈ U (f (Q (T^[k] x))) := by
    rw [←hxy k]
    exact hmem _
  choose g hg hlift using fun k => hsmall _ _ (hRm k) _ (hRy k)
  have hconj := variable_future_lifts_conjugate a x y L R
    (fun k => hr _) hex
    (fun k => hinj _ _ (hRm k))
    (fun k => by
      simpa only [Function.iterate_succ_apply'] using hnext _ _ (hRm k))
    g hg hlift
  refine ⟨g 0,by simpa only [Function.iterate_zero,Function.id_def] using hlift 0,?_⟩
  intro i j hij
  apply conjugation_expanding_entry_eq_zero ell hell (g 0)
    tendsto_natCast_atTop_atTop 2 _ hij
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
  change |(g k).val p q-(1 : Matrix (Fin n) (Fin n) ℝ) p q| < R k at hb
  have hRone : R k ≤ 1 := hr1 _
  have hone : |(1 : Matrix (Fin n) (Fin n) ℝ) p q| ≤ 1 := by
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  have htriangle := abs_add_le ((g k).val p q-(1 : Matrix (Fin n) (Fin n) ℝ) p q)
    ((1 : Matrix (Fin n) (Fin n) ℝ) p q)
  rw [sub_add_cancel] at htriangle
  linarith

end DukePrimeDegree

end

end OAI
