import OAI.Combinatorics.SparsestCut.Model

namespace OAI

universe u1 u2

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut

namespace FiniteDuality

variable {E : Type u1} {K : Type u2} [Fintype E] [Fintype K]

def packingCone (A : E → K → ℝ) (w : K → ℝ) : Set ((E → ℝ) × ℝ) :=
  {y | ∃ t : K → ℝ, (∀ k, 0 ≤ t k) ∧
      (∀ e, ∑ k, A e k * t k ≤ y.1 e) ∧ y.2 ≤ ∑ k, w k * t k}

lemma packingCone_closed (A : E → K → ℝ) (w : K → ℝ)
    (hA : ∀ e k, 0 ≤ A e k) (hcol : ∀ k, 0 < ∑ e, A e k) :
    IsClosed (packingCone A w) := by
  classical
  apply isSeqClosed_iff_isClosed.mp
  intro y b hy hyb
  choose t ht0 htA htw using hy
  have hsum : Tendsto (fun n => ∑ e, (y n).1 e) atTop (𝓝 (∑ e, b.1 e)) :=
    tendsto_finsetSum _ (fun e he => (tendsto_pi_nhds.mp hyb.fst_nhds) e)
  obtain ⟨B, hB⟩ := hsum.bddAbove_range
  have hbound (n : ℕ) (k : K) : t n k ≤ B / (∑ e, A e k) := by
    apply (le_div_iff₀ (hcol k)).mpr
    calc
      t n k * ∑ e, A e k = ∑ e, A e k * t n k := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
      _ ≤ ∑ e, ∑ j, A e j * t n j := by
        apply Finset.sum_le_sum
        intro e he
        exact Finset.single_le_sum (fun j hj => mul_nonneg (hA e j) (ht0 n j))
          (Finset.mem_univ k)
      _ ≤ ∑ e, (y n).1 e := Finset.sum_le_sum (fun e he => htA n e)
      _ ≤ B := hB (Set.mem_range_self n)
  obtain ⟨u, hu, φ, hφ, htend⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : K → ℝ) (fun k => B / (∑ e, A e k)))).tendsto_subseq
      (fun n => ⟨ht0 n, hbound n⟩)
  refine ⟨u, hu.1, ?_, ?_⟩
  · intro e
    apply le_of_tendsto_of_tendsto
      (tendsto_finsetSum _ (fun k hk =>
        tendsto_const_nhds.mul ((tendsto_pi_nhds.mp htend) k)))
      (((tendsto_pi_nhds.mp hyb.fst_nhds) e).comp hφ.tendsto_atTop)
    exact Eventually.of_forall (fun n => htA (φ n) e)
  · apply le_of_tendsto_of_tendsto (hyb.snd_nhds.comp hφ.tendsto_atTop)
      (tendsto_finsetSum _ (fun k hk =>
        tendsto_const_nhds.mul ((tendsto_pi_nhds.mp htend) k)))
    exact Eventually.of_forall (fun n => htw (φ n))

noncomputable def packingProperCone (A : E → K → ℝ) (w : K → ℝ)
    (hA : ∀ e k, 0 ≤ A e k) (hcol : ∀ k, 0 < ∑ e, A e k) :
    ProperCone ℝ ((E → ℝ) × ℝ) where
  carrier := packingCone A w
  zero_mem' := by
    refine ⟨0, by simp, ?_, ?_⟩ <;> simp
  add_mem' := by
    rintro x y ⟨s, hs0, hsA, hsw⟩ ⟨t, ht0, htA, htw⟩
    refine ⟨s+t, fun k => add_nonneg (hs0 k) (ht0 k), ?_, ?_⟩
    · intro e
      simpa [mul_add, Finset.sum_add_distrib] using add_le_add (hsA e) (htA e)
    · simpa [mul_add, Finset.sum_add_distrib] using add_le_add hsw htw
  smul_mem' := by
    rintro ⟨a, ha⟩ x ⟨t, ht0, htA, htw⟩
    refine ⟨a • t, fun k => mul_nonneg ha (ht0 k), ?_, ?_⟩
    · intro e
      change (∑ k, A e k * (a * t k)) ≤ a * x.1 e
      simpa [← Finset.mul_sum, mul_left_comm] using
        mul_le_mul_of_nonneg_left (htA e) ha
    · change a * x.2 ≤ ∑ k, w k * (a * t k)
      simpa [← Finset.mul_sum, mul_left_comm] using
        mul_le_mul_of_nonneg_left htw ha
  isClosed' := packingCone_closed A w hA hcol

lemma dual_functional (f : ((E → ℝ) × ℝ) →L[ℝ] ℝ) :
    ∃ c : E → ℝ, ∃ q : ℝ, ∀ x : (E → ℝ) × ℝ,
      f x = (∑ e, c e * x.1 e) + q * x.2 := by
  classical
  refine ⟨fun e => f (Pi.single e 1, 0), f (0, 1), ?_⟩
  rintro ⟨x,y⟩
  have heq : (x,y) = (∑ e, x e • (Pi.single e 1, (0 : ℝ))) + y • (0, (1 : ℝ)) := by
    ext e <;> simp [Prod.fst_sum, Prod.snd_sum, ← Pi.single_smul,
      Finset.univ_sum_single]
  calc
    f (x,y) = f ((∑ e, x e • (Pi.single e 1, (0 : ℝ))) + y • (0, (1 : ℝ))) :=
      congrArg f heq
    _ = (∑ e, f (Pi.single e 1, 0) * x e) + f (0, 1) * y := by
      simp only [map_add, map_sum, map_smul, smul_eq_mul, mul_comm]

theorem packing_duality_strict (A : E → K → ℝ) (w : K → ℝ)
    (hA : ∀ e k, 0 ≤ A e k) (hcol : ∀ k, 0 < ∑ e, A e k)
    (d : E → ℝ) (hd : ∀ e, 0 ≤ d e) {β : ℝ} (hβ : 0 < β)
    (hbound : ∀ t : K → ℝ, (∀ k, 0 ≤ t k) →
      (∀ e, ∑ k, A e k * t k ≤ d e) → (∑ k, w k * t k) < β) :
    ∃ c : E → ℝ, (∀ e, 0 ≤ c e) ∧
      (∀ k, w k ≤ ∑ e, A e k * c e) ∧ (∑ e, c e * d e) < β := by
  classical
  let C := packingProperCone A w hA hcol
  have hnot : (d,β) ∉ C := by
    rintro ⟨t, ht0, htA, htw⟩
    exact (hbound t ht0 htA).not_ge htw
  obtain ⟨f, hf, hfb⟩ := C.hyperplane_separation_point hnot
  obtain ⟨c,q,hform⟩ := dual_functional f
  have hc (e : E) : 0 ≤ c e := by
    have hx : (Pi.single e 1, (0 : ℝ)) ∈ C := by
      refine ⟨0, by simp, ?_, ?_⟩
      · intro j; simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
        simp [Pi.single_apply]; split_ifs <;> norm_num
      · simp
    simpa [hform, Pi.single_apply, mul_ite] using hf _ hx
  have hq : q < 0 := by
    rw [hform] at hfb
    have hcd : 0 ≤ ∑ e, c e * d e :=
      Finset.sum_nonneg (fun e he => mul_nonneg (hc e) (hd e))
    nlinarith
  have hcoldual (k : K) : 0 ≤ (∑ e, c e * A e k) + q * w k := by
    have hx : ((fun e => A e k), w k) ∈ C := by
      refine ⟨Pi.single k 1, ?_, ?_, ?_⟩
      · intro j; simp [Pi.single_apply]; split_ifs <;> norm_num
      · intro e; simp [Pi.single_apply, mul_ite]
      · simp [Pi.single_apply, mul_ite]
    simpa [hform, Pi.single_apply, mul_ite] using hf _ hx
  refine ⟨fun e => c e / (-q), fun e => div_nonneg (hc e) (neg_pos.mpr hq).le, ?_, ?_⟩
  · intro k
    simp only [← mul_div_assoc, ← Finset.sum_div]
    apply (le_div_iff₀ (neg_pos.mpr hq)).mpr
    have := hcoldual k
    have hsum : (∑ e, A e k * c e) = ∑ e, c e * A e k := by
      apply Finset.sum_congr rfl; intros; ring
    rw [hsum]
    nlinarith
  · simp only [div_mul_eq_mul_div, ← Finset.sum_div]
    apply (div_lt_iff₀ (neg_pos.mpr hq)).mpr
    rw [hform] at hfb
    nlinarith

omit [Fintype K] in

lemma cap_covering (A : E → K → ℝ) (w : K → ℝ)
    (hA : ∀ e k, A e k = 0 ∨ A e k = 1) {W : ℝ} (hW : 0 ≤ W)
    (hw : ∀ k, w k ≤ W) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e)
    (hcover : ∀ k, w k ≤ ∑ e, A e k * c e) :
    ∀ k, w k ≤ ∑ e, A e k * min (c e) W := by
  classical
  intro k
  by_cases hb : ∃ e, A e k = 1 ∧ W < c e
  · obtain ⟨e, he, hce⟩ := hb
    calc
      w k ≤ W := hw k
      _ = A e k * min (c e) W := by rw [he, min_eq_right hce.le]; ring
      _ ≤ ∑ j, A j k * min (c j) W :=
        Finset.single_le_sum (fun j hj => mul_nonneg
          (show 0 ≤ A j k from by rcases hA j k with h | h <;> rw [h] ; norm_num)
          (le_min (hc j) hW)) (Finset.mem_univ e)
  · convert hcover k using 1
    apply Finset.sum_congr rfl
    intro e he
    rcases hA e k with hz | ho
    · simp [hz]
    · have hcW : c e ≤ W := le_of_not_gt (fun h => hb ⟨e, ho, h⟩)
      rw [min_eq_left hcW]

theorem packing_duality (A : E → K → ℝ) (w : K → ℝ)
    (hA : ∀ e k, A e k = 0 ∨ A e k = 1) (hcol : ∀ k, 0 < ∑ e, A e k)
    (d : E → ℝ) (hd : ∀ e, 0 ≤ d e) {β W : ℝ} (hβ : 0 ≤ β) (hW : 0 ≤ W)
    (hw : ∀ k, w k ≤ W)
    (hbound : ∀ t : K → ℝ, (∀ k, 0 ≤ t k) →
      (∀ e, ∑ k, A e k * t k ≤ d e) → (∑ k, w k * t k) ≤ β) :
    ∃ c : E → ℝ, (∀ e, 0 ≤ c e) ∧
      (∀ k, w k ≤ ∑ e, A e k * c e) ∧ (∑ e, c e * d e) ≤ β := by
  classical
  have hA0 : ∀ e k, 0 ≤ A e k := by
    intro e k; rcases hA e k with h | h <;> rw [h] ; norm_num
  let T : Set (E → ℝ) := Icc 0 (fun _ => W) ∩ {c | ∀ k, w k ≤ ∑ e, A e k * c e}
  have hTc : IsCompact T := by
    refine isCompact_Icc.inter_right ?_
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro k
    apply isClosed_le continuous_const
    exact continuous_finsetSum _ (fun e he => continuous_const.mul (continuous_apply e))
  have hcapped : ∀ γ, β < γ → ∃ c ∈ T, (∑ e, c e * d e) < γ := by
    intro γ hγ
    obtain ⟨c, hc0, hcA, hcd⟩ := packing_duality_strict A w hA0 hcol d hd
      (hβ.trans_lt hγ) (fun t ht htA => (hbound t ht htA).trans_lt hγ)
    refine ⟨fun e => min (c e) W, ⟨⟨?_, ?_⟩, cap_covering A w hA hW hw c hc0 hcA⟩, ?_⟩
    · exact fun e => le_min (hc0 e) hW
    · exact fun e => min_le_right _ _
    · exact lt_of_le_of_lt (Finset.sum_le_sum (fun e he =>
        mul_le_mul_of_nonneg_right (min_le_left _ _) (hd e))) hcd
  obtain ⟨c0, hc0, _⟩ := hcapped (β+1) (by linarith)
  have hobj : Continuous (fun c : E → ℝ => ∑ e, c e * d e) :=
    continuous_finsetSum _ (fun e he => (continuous_apply e).mul continuous_const)
  obtain ⟨c, hc, hmin⟩ := hTc.exists_isMinOn ⟨c0,hc0⟩ hobj.continuousOn
  refine ⟨c, hc.1.1, hc.2, ?_⟩
  by_contra! hstrict
  obtain ⟨c', hc', hlt⟩ := hcapped (∑ e, c e * d e) hstrict
  exact hlt.not_ge (hmin hc')

end FiniteDuality

end UniformSparsestCut

end

end OAI
