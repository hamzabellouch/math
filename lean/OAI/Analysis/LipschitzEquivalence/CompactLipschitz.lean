import OAI.Analysis.LipschitzEquivalence.ShrinkingCutoffs

namespace OAI

universe uM uI

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.LocalLipschitz
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]

theorem disjoint_sum_lipschitz (f : I → M → ℝ) {C : ℝ≥0}
    (hf : ∀ i, LipschitzWith C (f i))
    (hdis : ∀ x i j, f i x ≠ 0 → f j x ≠ 0 → i = j) :
    LipschitzWith (2*C) (fun x => ∑ i, f i x) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hi =>
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Finset.sum_of_isEmpty,dist_self]
    positivity
  | inr hi =>
    have hex (x : M) : ∃ i : I, ∀ j : I, j ≠ i → f j x = 0 := by
      by_cases hx : ∃ i, f i x ≠ 0
      · obtain ⟨i,hi⟩ := hx
        refine ⟨i,fun j hji => ?_⟩
        by_contra hj
        exact hji (hdis x j i hj hi)
      · push Not at hx
        exact ⟨Classical.choice hi,fun j _ => hx j⟩
    choose a ha using hex
    have heval (x : M) : ∑ i, f i x = f (a x) x := by
      apply Finset.sum_eq_single (a x)
      · intro b hb hba
        exact ha x b hba
      · simp
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [heval,heval,Real.dist_eq]
    by_cases hxy : a x = a y
    · have h := (hf (a x)).dist_le_mul x y
      rw [Real.dist_eq,hxy] at h
      rw [hxy]
      calc
        _ ≤ (C : ℝ) * dist x y := h
        _ ≤ (2*C : ℝ≥0) * dist x y := by
          simp only [NNReal.coe_mul, NNReal.coe_ofNat]
          nlinarith [C.coe_nonneg, dist_nonneg (x := x) (y := y)]
    · have hx := (hf (a x)).dist_le_mul x y
      have hy := (hf (a y)).dist_le_mul x y
      rw [ha y (a x) hxy,Real.dist_eq,sub_zero] at hx
      rw [ha x (a y) (Ne.symm hxy),Real.dist_eq,zero_sub,abs_neg] at hy
      calc
        _ ≤ |f (a x) x|+|f (a y) y| := abs_sub _ _
        _ ≤ (2*C : ℝ≥0) * dist x y := by
          simp only [NNReal.coe_mul,NNReal.coe_ofNat]
          linarith

theorem compact_eventual_lipschitz (R : ℕ → M → ℝ) {K : Set M} (hK : IsCompact K)
    {C : ℝ≥0} (hC : 0 < C)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ K, |R i x| < ε)
    (hloc : ∀ p ∈ K, ∃ V : Set M, IsOpen V ∧ p ∈ V ∧
      ∀ᶠ i in atTop, LipschitzOnWith C (R i) (K ∩ V)) :
    ∀ᶠ i in atTop, LipschitzOnWith C (R i) K := by
  classical
  choose V hV hpV hlocV using fun p : K => hloc p.1 p.2
  have hcover : K ⊆ ⋃ p : K, V p := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x,hx⟩,hpV ⟨x,hx⟩⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover V hV hcover
  have hcover' : K ⊆ ⋃ p : s, V p.1 := by
    intro x hx
    obtain ⟨p,hp,hxp⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Set.mem_iUnion.mpr ⟨⟨p,hp⟩,hxp⟩
  obtain ⟨δ,hδ,hLeb⟩ := lebesgue_number_lemma_of_metric hK (fun p : s => hV p.1) hcover'
  have hall : ∀ᶠ i in atTop, ∀ p : s, LipschitzOnWith C (R i) (K ∩ V p.1) :=
    Filter.eventually_all.mpr (fun p => hlocV p.1)
  have hC' : 0 < (C : ℝ) := hC
  have hsml := hsmall ((C : ℝ)*δ/2) (by positivity)
  filter_upwards [hall,hsml] with i hi hsi
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  by_cases hxy : dist x y < δ
  · obtain ⟨p,hp⟩ := hLeb x hx
    exact (hi p).dist_le_mul x ⟨hx,hp (Metric.mem_ball_self hδ)⟩ y
      ⟨hy,hp (by simpa only [Metric.mem_ball,dist_comm] using hxy)⟩
  · have htri := abs_sub (R i x) (R i y)
    have hxsmall := hsi x hx
    have hysmall := hsi y hy
    rw [Real.dist_eq]
    have hd : δ ≤ dist x y := le_of_not_gt hxy
    nlinarith [mul_le_mul_of_nonneg_left hd hC'.le]
end LipschitzCounterexample.LocalLipschitz

namespace LipschitzCounterexample.LocalLipschitz
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]

def weightedRemainder (d : M → ℝ) (z : I → M) (φ : I → M → ℝ) (x : M) : ℝ :=
  d x - ∑ j, (d x-d (z j))*φ j x

omit [MetricSpace M] in
theorem weightedRemainder_sub (d : M → ℝ) (z : I → M) (φ : I → M → ℝ) (x y : M) :
    weightedRemainder d z φ x-weightedRemainder d z φ y =
      (1-∑ j,φ j x)*(d x-d y)+∑ j,(φ j x-φ j y)*(d (z j)-d y) := by
  simp only [weightedRemainder, sub_mul, mul_sub, one_mul, Finset.sum_sub_distrib,
    Finset.sum_mul]
  have h₁ : ∑ j, d x * φ j x = ∑ j, φ j x * d x := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have h₂ : ∑ j, d y * φ j y = ∑ j, φ j y * d y := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have h₃ : ∑ j, d (z j) * φ j x = ∑ j, φ j x * d (z j) := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have h₄ : ∑ j, d (z j) * φ j y = ∑ j, φ j y * d (z j) := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [h₁,h₂,h₃,h₄]
  ring

theorem weightedRemainder_lipschitzOn (d : M → ℝ) (z : I → M) (φ : I → M → ℝ)
    {K O : Set M} {A B ε : ℝ≥0}
    (hd : LipschitzOnWith A d O) (hφ : ∀ j, LipschitzWith B (φ j))
    (hsum : ∀ x, (∑ j,φ j x) ∈ Icc (0 : ℝ) 1)
    (hsmall : ∀ x ∈ K, |d x| ≤ ε) (hzsmall : ∀ j, |d (z j)| ≤ ε) :
    LipschitzOnWith (A+2*Fintype.card I*B*ε) (weightedRemainder d z φ) (K ∩ O) := by
  classical
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq,weightedRemainder_sub]
  have hxφ : |1-∑ j,φ j x| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hsum x).2)]
    linarith [(hsum x).1]
  have hfirst : |(1-∑ j,φ j x)*(d x-d y)| ≤ (A : ℝ)*dist x y := by
    rw [abs_mul]
    calc
      _ ≤ 1*|d x-d y| := mul_le_mul_of_nonneg_right hxφ (abs_nonneg _)
      _ ≤ (A : ℝ)*dist x y := by simpa only [one_mul,Real.dist_eq] using hd.dist_le_mul x hx.2 y hy.2
  have hterm (j : I) : |(φ j x-φ j y)*(d (z j)-d y)| ≤
      (B : ℝ)*dist x y*(2*(ε : ℝ)) := by
    rw [abs_mul]
    have hl := (hφ j).dist_le_mul x y
    rw [Real.dist_eq] at hl
    exact mul_le_mul hl ((abs_sub _ _).trans (by linarith [hzsmall j,hsmall y hy.1]))
      (abs_nonneg _) (by positivity)
  have hsecond : |∑ j,(φ j x-φ j y)*(d (z j)-d y)| ≤
      (Fintype.card I : ℝ)*((B : ℝ)*dist x y*(2*(ε : ℝ))) := by
    calc
      _ ≤ ∑ j,|(φ j x-φ j y)*(d (z j)-d y)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : I, (B : ℝ)*dist x y*(2*(ε : ℝ)) := Finset.sum_le_sum (fun j _ => hterm j)
      _ = _ := by simp
  refine (abs_add_le _ _).trans ?_
  simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat]
  nlinarith
end LipschitzCounterexample.LocalLipschitz

namespace LipschitzCounterexample.LocalGeometry
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]

theorem exists_disjoint_balls (z : I → M) (hz : Function.Injective z) :
    ∃ r : ℝ, 0 < r ∧ Pairwise (fun j k => Disjoint (Metric.ball (z j) r) (Metric.ball (z k) r)) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hi => exact ⟨1,by norm_num,fun j => isEmptyElim j⟩
  | inr hi =>
    let d : I × I → ℝ := fun p => if p.1 = p.2 then 1 else dist (z p.1) (z p.2)/3
    have hd (p : I × I) : 0 < d p := by
      dsimp [d]
      split_ifs with hp
      · norm_num
      · exact div_pos (dist_pos.mpr (fun h => hp (hz h))) (by norm_num)
    let r : ℝ := Finset.univ.inf' Finset.univ_nonempty d
    have hr : 0 < r := (Finset.lt_inf'_iff _).mpr (fun p _ => hd p)
    refine ⟨r,hr,?_⟩
    intro j k hjk
    have hrd : r ≤ dist (z j) (z k)/3 := by
      have ht : r ≤ d (j,k) := Finset.inf'_le _ (Finset.mem_univ (j,k))
      simpa only [d,ite_eq_right hjk] using ht
    apply Set.disjoint_left.mpr
    intro x hx hy
    have ht := dist_triangle (z j) x (z k)
    rw [dist_comm (z j) x] at ht
    change dist x (z j) < r at hx
    change dist x (z k) < r at hy
    linarith
end LipschitzCounterexample.LocalGeometry

end

end OAI
