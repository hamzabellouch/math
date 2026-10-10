import OAI.NumberTheory.DukePrimeDegree.Entropy.AdaptiveFutureLifts
import OAI.NumberTheory.DukePrimeDegree.Geometry.QuotientLogProper
import Mathlib.Data.Nat.Pairing

namespace OAI

/-! # Future observations finite on each compact height range

Compact height levels provide finite chart covers. Encoding their level
and chart labels gives one countable observation with controlled future
lifts, while its restriction to every bounded height range is finite.
No finite Shannon entropy of the countable observation is asserted.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_finite_level_triangular_observation {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (H : X n → ℕ) (hH : Measurable H)
    (hcompact : ∀ m, IsCompact {x | H x ≤ m}) :
    ∃ Q : X n → ℕ, Measurable Q ∧
      (∀ m, (Q '' {x | H x ≤ m}).Finite) ∧
      ∀ x y, (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
            Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ g : G n, rightAction x g=y ∧ ∀ i j, ell j < ell i → g.val i j=0 := by
  classical
  let a := diagonalOneParameter ell hell (-1)
  let T : X n → X n := fun x => rightAction x a
  let K : ℕ → Set (X n) := fun m => {x | H x ≤ m}
  have hn : ∑ i, -ell i=0 := by simp only [Finset.sum_neg_distrib,hell,neg_zero]
  obtain ⟨L,hL,hexpand⟩ := diagonal_conjugation_expansion (fun i => -ell i) hn
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hparam : diagonalOneParameter (fun i => -ell i) hn (-1) = a⁻¹ := by
    calc
      _ = diagonalOneParameter ell hell 1 := by
        simpa only [neg_neg] using diagonalOneParameter_neg_weights ell hell (-1)
      _ = _ := by dsimp [a]; rw [diagonalOneParameter_neg,inv_inv]
  have hex (s : ℝ) (hs : 0 < s) :
      (MulAut.conj a⁻¹) '' matrixBall n s ⊆ matrixBall n (L*s) :=
    hparam ▸ hexpand s hs
  choose R hR hRi using fun m => compact_uniform_chart_injective
    (K m ∪ T '' K m) ((hcompact m).union ((hcompact m).image (continuous_rightAction a)))
  let r : ℕ → ℝ := fun m => min 1 (R m/L)
  have hr (m : ℕ) : 0 < r m := lt_min zero_lt_one (div_pos (hR m) hLp)
  have hr1 (m : ℕ) : r m ≤ 1 := min_le_left _ _
  have hLr (m : ℕ) : L*r m ≤ R m := by
    have hh := (le_div_iff₀ hLp).mp (min_le_right 1 (R m/L))
    simpa only [mul_comm] using hh
  have hrR (m : ℕ) : r m ≤ R m :=
    (le_mul_of_one_le_left (hr m).le hL).trans (hLr m)
  choose N P hP hsmall using fun m => exists_finite_observation_small_lifts (K m)
    (hcompact m) (matrixBall n (r m))
    ((matrixBall_isOpen n (r m)).mem_nhds (one_mem_matrixBall n (hr m)))
  let Q : X n → ℕ := fun x => Nat.pair (H x) (P (H x) x).val
  have hQ : Measurable Q := by
    have hvar : Measurable (fun p : ℕ × X n => (P p.1 p.2).val) :=
      measurable_from_prod_countable_right fun m =>
        (measurable_of_finite (fun u : Fin (N m) => u.val)).comp (hP m)
    exact (measurable_of_countable (fun p : ℕ × ℕ => Nat.pair p.1 p.2)).comp
      (hH.prodMk (hvar.comp (hH.prodMk measurable_id)))
  have heq {x y : X n} (h : Q y=Q x) : H y=H x ∧ P (H x) y=P (H x) x := by
    have hp : H y=H x ∧ (P (H y) y).val=(P (H x) x).val := Nat.pair_eq_pair.mp h
    refine ⟨hp.1,?_⟩
    apply Fin.ext
    have hv := hp.2
    rw [hp.1] at hv
    exact hv
  refine ⟨Q,hQ,?_,?_⟩
  · intro m
    have hlevel (k : ℕ) : (Q '' {x | H x=k}).Finite := by
      apply ((Set.finite_range (fun p : Fin (N k) => Nat.pair k p.val))).subset
      rintro _ ⟨x,hx,rfl⟩
      change H x=k at hx
      subst k
      exact ⟨P (H x) x,rfl⟩
    apply (Set.Finite.biUnion (Finset.finite_toSet (Finset.range (m+1)))
      (fun k _ => hlevel k)).subset
    rintro _ ⟨x,hx,rfl⟩
    exact mem_iUnion₂.mpr ⟨H x,by simpa using Nat.lt_succ_of_le hx,
      mem_image_of_mem Q rfl⟩
  · intro x y hxy
    let s : ℕ → ℝ := fun k => r (H (T^[k] x))
    have hx (k : ℕ) : T^[k] x ∈ K (H (T^[k] x)) := by
      change H (T^[k] x) ≤ H (T^[k] x)
      exact le_rfl
    choose g hg hlift using fun k => hsmall (H (T^[k] x)) (T^[k] x) (hx k)
      (T^[k] y) (heq (hxy k)).2
    have hconj := variable_future_lifts_conjugate a x y L s (fun k => hr _) hex
      (fun k => (hRi _ _ (Or.inl (hx k))).mono (matrixBall_mono (hrR _)))
      (fun k => by
        apply (hRi _ _ (Or.inr ⟨T^[k] x,hx k,?_⟩)).mono (matrixBall_mono (hLr _))
        exact (Function.iterate_succ_apply' T k x).symm)
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
    change |(g k).val p q-(1 : Matrix (Fin n) (Fin n) ℝ) p q| < s k at hb
    have hone : |(1 : Matrix (Fin n) (Fin n) ℝ) p q| ≤ 1 := by
      simp only [Matrix.one_apply]
      split_ifs <;> norm_num
    have htriangle := abs_add_le ((g k).val p q-(1 : Matrix (Fin n) (Fin n) ℝ) p q)
      ((1 : Matrix (Fin n) (Fin n) ℝ) p q)
    rw [sub_add_cancel] at htriangle
    have hs : s k ≤ 1 := hr1 _
    linarith

/-- A countable geometric observation whose compact levels are finite and
whose level height grows sublinearly along almost every diagonal orbit. -/
theorem exists_tempered_finite_level_observation (d : ℕ)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0) :
    ∃ (H Q : X (d+1) → ℕ), Measurable H ∧ Measurable Q ∧
      (∀ m, IsCompact {x | H x ≤ m}) ∧
      (∀ m, (Q '' {x | H x ≤ m}).Finite) ∧
      (∀ᵐ x ∂μ, Tendsto (fun k : ℕ =>
        (H ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x) : ℝ)/
          (k:ℝ)) atTop (𝓝 0)) ∧
      ∀ x y, (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
            Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ g : G (d+1), rightAction x g=y ∧ ∀ i j, ell j < ell i → g.val i j=0 := by
  have hT : MeasurePreserving
      (fun x => rightAction x (diagonalOneParameter ell hell (-1))) μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  obtain ⟨H,hH,hK,hsub⟩ := exists_tempered_compact_exhaustion μ _ hT
  obtain ⟨Q,hQ,hfinite,htri⟩ := exists_finite_level_triangular_observation ell hell H hH hK
  exact ⟨H,Q,hH,hQ,hK,hfinite,hsub,htri⟩

end DukePrimeDegree

end

end OAI
