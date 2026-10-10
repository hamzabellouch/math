import OAI.NumberTheory.DukePrimeDegree.Entropy.CompactFutureLifts

namespace OAI

/-! # A measurable chart height with bounded diagonal increments

Local quotient injectivity is encoded on a geometric sequence of radii.
The least admissible index is measurable and changes by at most one under
a fixed diagonal translation. This supplies chart-size control without
an integrability assumption on the height itself.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

def LocalInjectivityAt {n : ℕ} (r : ℝ) (x : X n) : Prop :=
  ∃ U : Set (X n), IsOpen U ∧ x ∈ U ∧
    ∀ y ∈ U, Set.InjOn (fun g => rightAction y g) (matrixBall n r)

lemma LocalInjectivityAt.mono {n : ℕ} {r s : ℝ} {x : X n}
    (h : LocalInjectivityAt r x) (hs : s ≤ r) : LocalInjectivityAt s x := by
  obtain ⟨U,hU,hx,hi⟩ := h
  exact ⟨U,hU,hx,fun y hy => (hi y hy).mono (matrixBall_mono hs)⟩

lemma isOpen_localInjectivityAt {n : ℕ} (r : ℝ) :
    IsOpen {x : X n | LocalInjectivityAt r x} := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨U,hU,hx,hi⟩
  apply Filter.mem_of_superset (hU.mem_nhds hx)
  exact fun y hy => ⟨U,hU,hy,hi⟩

lemma localInjectivityAt_translate {n : ℕ} (a : G n) {κ r : ℝ}
    (hexpand : (MulAut.conj a) '' matrixBall n (r/κ) ⊆ matrixBall n r)
    {x : X n} (hx : LocalInjectivityAt r x) :
    LocalInjectivityAt (r/κ) (rightAction x a) := by
  obtain ⟨U,hU,hx,hi⟩ := hx
  refine ⟨(rightActionHomeomorph a) '' U,
    (rightActionHomeomorph a).isOpenMap U hU,⟨x,hx,rfl⟩,?_⟩
  rintro _ ⟨z,hz,rfl⟩ u hu v hv heq
  apply (MulAut.conj a).injective
  apply hi z hz (hexpand ⟨u,hu,rfl⟩) (hexpand ⟨v,hv,rfl⟩)
  have H := congrArg (fun w => rightAction w a⁻¹) heq
  change rightAction (rightAction (rightAction z a) u) a⁻¹ =
    rightAction (rightAction (rightAction z a) v) a⁻¹ at H
  simpa only [rightAction_mul,MulAut.conj_apply,mul_assoc] using H

theorem exists_local_injectivity_height {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) :
    ∃ (κ : ℝ) (H : X n → ℕ), 1 < κ ∧ Measurable H ∧
      (∀ x, LocalInjectivityAt ((κ⁻¹)^(H x)) x) ∧
      ∀ x, H (rightAction x (diagonalOneParameter ell hell (-1))) ≤ H x+1 ∧
        H x ≤ H (rightAction x (diagonalOneParameter ell hell (-1)))+1 := by
  classical
  let a := diagonalOneParameter ell hell (-1)
  obtain ⟨L,hL,hexpand⟩ := diagonal_conjugation_expansion ell hell
  have hn : ∑ i, -ell i=0 := by simp only [Finset.sum_neg_distrib,hell,neg_zero]
  obtain ⟨M,hM,hexpandInv⟩ := diagonal_conjugation_expansion (fun i => -ell i) hn
  have hparam : diagonalOneParameter (fun i => -ell i) hn (-1) = a⁻¹ := by
    calc
      _ = diagonalOneParameter ell hell 1 := by
        simpa only [neg_neg] using diagonalOneParameter_neg_weights ell hell (-1)
      _ = _ := by dsimp [a]; rw [diagonalOneParameter_neg,inv_inv]
  let κ : ℝ := max 2 (max L M)
  have hκ : 1 < κ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hκp : 0 < κ := zero_lt_one.trans hκ
  have hLκ : L ≤ κ := (le_max_left _ _).trans (le_max_right _ _)
  have hMκ : M ≤ κ := (le_max_right _ _).trans (le_max_right _ _)
  have hc (r : ℝ) (hr : 0 < r) :
      (MulAut.conj a) '' matrixBall n (r/κ) ⊆ matrixBall n r := by
    exact (hexpand (r/κ) (div_pos hr hκp)).trans (matrixBall_mono (by
      have hh := mul_le_mul_of_nonneg_right hLκ (div_nonneg hr.le hκp.le)
      rw [mul_div_cancel₀ _ hκp.ne'] at hh
      exact hh))
  have hci (r : ℝ) (hr : 0 < r) :
      (MulAut.conj a⁻¹) '' matrixBall n (r/κ) ⊆ matrixBall n r := by
    have he : (MulAut.conj a⁻¹) '' matrixBall n (r/κ) ⊆ matrixBall n (M*(r/κ)) :=
      hparam ▸ hexpandInv (r/κ) (div_pos hr hκp)
    exact he.trans (matrixBall_mono (by
      have hh := mul_le_mul_of_nonneg_right hMκ (div_nonneg hr.le hκp.le)
      rw [mul_div_cancel₀ _ hκp.ne'] at hh
      exact hh))
  have hinv : 0 < κ⁻¹ := inv_pos.mpr hκp
  have hinv1 : κ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hκ
  have hexists (x : X n) : ∃ k : ℕ, LocalInjectivityAt ((κ⁻¹)^k) x := by
    obtain ⟨U,hU,hx,r,hr,hi⟩ := local_uniform_chart_injective x
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hinv.le hinv1
    obtain ⟨k,hk⟩ := ((ht.eventually (gt_mem_nhds hr))).exists
    exact ⟨k,LocalInjectivityAt.mono ⟨U,hU,hx,hi⟩ hk.le⟩
  let H : X n → ℕ := fun x => Nat.find (hexists x)
  have hH (x : X n) : LocalInjectivityAt ((κ⁻¹)^(H x)) x := Nat.find_spec (hexists x)
  have hHm : Measurable H := measurable_find hexists
    (fun k => (isOpen_localInjectivityAt ((κ⁻¹)^k)).measurableSet)
  have hstep (b : G n)
      (hb : ∀ r, 0 < r → (MulAut.conj b) '' matrixBall n (r/κ) ⊆ matrixBall n r)
      (x : X n) : H (rightAction x b) ≤ H x+1 := by
    apply Nat.find_min'
    have ht := localInjectivityAt_translate b (hb _ (pow_pos hinv (H x))) (hH x)
    simpa only [pow_succ,div_eq_mul_inv] using ht
  refine ⟨κ,H,hκ,hHm,hH,?_⟩
  intro x
  refine ⟨hstep a hc x,?_⟩
  simpa only [rightAction_mul,mul_inv_cancel,rightAction_one] using
    hstep a⁻¹ hci (rightAction x a)

end DukePrimeDegree

end

end OAI
