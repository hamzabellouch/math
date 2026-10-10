import OAI.Combinatorics.SparsestCut.CutSums

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut

section SemimetricBounds

variable {n : ℕ}

def IsSemimetric (d : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ d i j) ∧ (∀ i j, d i j = d j i) ∧
    (∀ i, d i i = 0) ∧ (∀ i j k, d i k ≤ d i j + d j k)

lemma NegativeType.semimetric {d : Fin n → Fin n → ℝ} (hd : NegativeType d) :
    IsSemimetric d := by
  obtain ⟨x,hx⟩ := hd.1
  refine ⟨fun i j => by rw [hx]; positivity, ?_, ?_, hd.2⟩
  · intro i j; rw [hx, hx, norm_sub_rev]
  · intro i; simp [hx]

lemma NegativeType.scale {d : Fin n → Fin n → ℝ} (hd : NegativeType d)
    {a : ℝ} (ha : 0 ≤ a) : NegativeType (fun i j => a * d i j) := by
  obtain ⟨x,hx⟩ := hd.1
  refine ⟨⟨fun i => Real.sqrt a • x i, ?_⟩, ?_⟩
  · intro i j
    change a * d i j = _
    rw [← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg a), Real.sq_sqrt ha, hx]
  · intro i j k
    simpa [mul_add] using mul_le_mul_of_nonneg_left (hd.2 i j k) ha

lemma cutDist_negativeType (B : Finset (Fin n)) (hn : 0 < n) : NegativeType (cutDist B) := by
  classical
  let i0 : Fin n := ⟨0,hn⟩
  refine ⟨⟨fun i => EuclideanSpace.single i0 (cutIndicator B i), ?_⟩,
    cutDist_triangle B⟩
  intro i j
  change cutDist B i j = ‖PiLp.single (β := fun _ : Fin n => ℝ) 2 i0 (cutIndicator B i) -
    PiLp.single (β := fun _ : Fin n => ℝ) 2 i0 (cutIndicator B j)‖ ^ 2
  rw [← PiLp.single_sub]
  change cutDist B i j = ‖EuclideanSpace.single i0
    (cutIndicator B i - cutIndicator B j)‖ ^ 2
  rw [PiLp.norm_single, Real.norm_eq_abs]
  change cutDist B i j = cutDist B i j ^ 2
  rcases cutDist_binary B i j with h | h <;> rw [h] <;> norm_num

lemma cut_nonempty (hn : 2 ≤ n) : Nonempty (Cut n) := by
  classical
  let i : Fin n := ⟨0,by omega⟩
  refine ⟨⟨{i}, Finset.singleton_nonempty i, ?_⟩⟩
  intro he
  have hh := congrArg Finset.card he
  simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at hh
  omega

lemma feasible_nonempty (hn : 2 ≤ n) : ∃ d : Fin n → Fin n → ℝ, Feasible d := by
  classical
  obtain ⟨B⟩ := cut_nonempty hn
  refine ⟨fun i j => (cutDemand B.1)⁻¹ * cutDist B.1 i j, ?_, ?_⟩
  · exact (cutDist_negativeType B.1 (by omega)).scale (inv_nonneg.mpr (cutDemand_pos B).le)
  · rw [pairSum_smul, pairSum_cut, inv_mul_cancel₀ (cutDemand_pos B).ne']

lemma normalized_pair_le_one {d : Fin n → Fin n → ℝ} (hd : IsSemimetric d)
    (hD : pairSum d = 1) (i j : Fin n) : d i j ≤ 1 := by
  rcases lt_trichotomy i j with h | h | h
  · simpa [hD] using le_pairSum hd.1 h
  · subst j; rw [hd.2.2.1]; norm_num
  · rw [hd.2.1 i j]; simpa [hD] using le_pairSum hd.1 h

lemma continuous_pairSum : Continuous (pairSum (n := n)) := by
  unfold pairSum
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro j hj
  split_ifs
  · exact (continuous_apply j).comp (continuous_apply i)
  · exact continuous_const

lemma semimetric_closed : IsClosed {d : Fin n → Fin n → ℝ | IsSemimetric d} := by
  unfold IsSemimetric
  simp only [ofPred_and, ofPred_forall]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
  · apply isClosed_iInter; intro i; apply isClosed_iInter; intro j
    exact isClosed_le continuous_const ((continuous_apply j).comp (continuous_apply i))
  · apply isClosed_iInter; intro i; apply isClosed_iInter; intro j
    exact isClosed_eq ((continuous_apply j).comp (continuous_apply i))
      ((continuous_apply i).comp (continuous_apply j))
  · apply isClosed_iInter; intro i
    exact isClosed_eq ((continuous_apply i).comp (continuous_apply i)) continuous_const
  · apply isClosed_iInter; intro i; apply isClosed_iInter; intro j
    apply isClosed_iInter; intro k
    exact isClosed_le (by fun_prop) (by fun_prop)

lemma normalized_semimetric_compact :
    IsCompact {d : Fin n → Fin n → ℝ | IsSemimetric d ∧ pairSum d = 1} := by
  have hclosed : IsClosed {d : Fin n → Fin n → ℝ | IsSemimetric d ∧ pairSum d = 1} :=
    semimetric_closed.inter (isClosed_eq continuous_pairSum continuous_const)
  apply (isCompact_Icc : IsCompact (Icc (0 : Fin n → Fin n → ℝ) (fun _ _ => 1))).of_isClosed_subset hclosed
  intro d hd
  exact ⟨hd.1.1, normalized_pair_le_one hd.1 hd.2⟩

lemma objective_nonneg (C : Capacity n) {d : Fin n → Fin n → ℝ} (hd : IsSemimetric d) :
    0 ≤ pairSum (fun i j => C.cap i j * d i j) :=
  pairSum_nonneg (fun i j => mul_nonneg (C.nonneg i j) (hd.1 i j))

lemma objective_pos_of_cuts (C : Capacity n)
    (hC : ∀ B : Cut n, cutDemand B.1 ≤ ∑ i ∈ B.1, ∑ j ∈ B.1ᶜ, C.cap i j)
    {d : Fin n → Fin n → ℝ} (hd : IsSemimetric d) (hD : pairSum d = 1) :
    0 < pairSum (fun i j => C.cap i j * d i j) := by
  classical
  have hnonneg := objective_nonneg C hd
  by_contra! hnot
  have hzero := le_antisymm hnot hnonneg
  have hp (i j : Fin n) : C.cap i j * d i j = 0 := by
    have h0 : 0 ≤ C.cap i j * d i j := mul_nonneg (C.nonneg i j) (hd.1 i j)
    rcases lt_trichotomy i j with h | h | h
    · have hh := le_pairSum (fun i j => mul_nonneg (C.nonneg i j) (hd.1 i j)) h
      rw [hzero] at hh
      exact le_antisymm hh h0
    · subst j; simp [C.diagonal]
    · rw [C.symm i j, hd.2.1 i j]
      have hh := le_pairSum (fun i j => mul_nonneg (C.nonneg i j) (hd.1 i j)) h
      rw [hzero] at hh
      exact le_antisymm hh (mul_nonneg (C.nonneg _ _) (hd.1 _ _))
  have hd0 : ∀ i j, d i j = 0 := by
    intro i j
    let B : Finset (Fin n) := Finset.univ.filter (fun k => d i k = 0)
    have hi : i ∈ B := by simp [B, hd.2.2.1]
    have hBall : B = Finset.univ := by
      by_contra hne
      let B' : Cut n := ⟨B, ⟨i,hi⟩, hne⟩
      have hjump (u : Fin n) (hu : u ∈ B) (v : Fin n) (hv : v ∈ Bᶜ) : C.cap u v = 0 := by
        have hu0 : d i u = 0 := (Finset.mem_filter.mp hu).2
        have hv0 : d i v ≠ 0 := by simpa [B] using hv
        have hduv : d u v ≠ 0 := by
          intro huv
          have ht := hd.2.2.2 i u v
          rw [hu0,huv] at ht
          exact hv0 (le_antisymm (by simpa using ht) (hd.1 i v))
        exact (mul_eq_zero.mp (hp u v)).resolve_right hduv
      have hsum : (∑ u ∈ B, ∑ v ∈ Bᶜ, C.cap u v) = 0 := by
        apply Finset.sum_eq_zero
        intro u hu
        exact Finset.sum_eq_zero (fun v hv => hjump u hu v hv)
      have hh := hC B'
      change cutDemand B ≤ _ at hh
      rw [hsum] at hh
      exact (cutDemand_pos B').not_ge hh
    have hj : j ∈ B := by rw [hBall]; exact Finset.mem_univ j
    exact (Finset.mem_filter.mp hj).2
  simp [pairSum,hd0] at hD

lemma glValue_pos_of_cuts (C : Capacity n) (hn : 2 ≤ n)
    (hC : ∀ B : Cut n, cutDemand B.1 ≤ ∑ i ∈ B.1, ∑ j ∈ B.1ᶜ, C.cap i j) :
    0 < glValue C := by
  obtain ⟨d0,hd0⟩ := feasible_nonempty hn
  have hobj : Continuous (fun d : Fin n → Fin n → ℝ => pairSum (fun i j => C.cap i j * d i j)) := by
    apply continuous_pairSum.comp
    apply continuous_pi; intro i; apply continuous_pi; intro j
    exact continuous_const.mul ((continuous_apply j).comp (continuous_apply i))
  obtain ⟨d,hd,hmin⟩ := normalized_semimetric_compact.exists_isMinOn
    ⟨d0,hd0.1.semimetric,hd0.2⟩ hobj.continuousOn
  apply (objective_pos_of_cuts C hC hd.1 hd.2).trans_le
  apply le_csInf
  · exact ⟨_,d0,hd0,rfl⟩
  · rintro b ⟨d',hd',rfl⟩
    exact hmin ⟨hd'.1.semimetric,hd'.2⟩

lemma OPT_ge_one_of_cuts (C : Capacity n) (hn : 2 ≤ n)
    (hC : ∀ B : Cut n, cutDemand B.1 ≤ ∑ i ∈ B.1, ∑ j ∈ B.1ᶜ, C.cap i j) :
    1 ≤ OPT C := by
  obtain ⟨B0⟩ := cut_nonempty hn
  apply le_csInf
  · exact ⟨_,B0.1,B0.2.1,B0.2.2,rfl⟩
  · rintro b ⟨B,hB,hB',rfl⟩
    unfold cutRatio
    rw [← cutDemand_eq]
    exact (one_le_div (cutDemand_pos ⟨B,hB,hB'⟩)).mpr (hC ⟨B,hB,hB'⟩)

end SemimetricBounds

end UniformSparsestCut

end

end OAI
