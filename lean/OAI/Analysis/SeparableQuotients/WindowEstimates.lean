import OAI.Analysis.SeparableQuotients.PathRigidity

namespace OAI

noncomputable section

namespace SeparableQuotient.SeriesTails
open Filter
open scoped Topology Classical

noncomputable def tail (a : ℕ → ℝ) (N : ℕ) : ℝ := ∑' k, a (k+N)

lemma tendsto_tail (a : ℕ → ℝ) : Tendsto (tail a) atTop (𝓝 0) :=
  tendsto_sum_nat_add a

lemma tail_nonneg (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (N : ℕ) : 0 ≤ tail a N :=
  tsum_nonneg (fun _ => ha _)

lemma sum_le_tail {ι : Type*} (a : ℕ → ℝ) (ha : Summable a) (hn : ∀ n, 0 ≤ a n)
    (s : Finset ι) (w : ι → ℕ) (hi : Set.InjOn w s) (N : ℕ) (hN : ∀ i ∈ s, N ≤ w i) :
    ∑ i ∈ s, a (w i) ≤ tail a N := by
  have hinj : Set.InjOn (fun i => w i - N) s := by
    intro i hi' j hj' hij
    apply hi hi' hj'
    have h1 := hN i hi'
    have h2 := hN j hj'
    change w i - N = w j - N at hij
    omega
  calc
    ∑ i ∈ s, a (w i) = ∑ i ∈ s, a ((w i-N)+N) := by
      exact Finset.sum_congr rfl (fun i hi => by rw [Nat.sub_add_cancel (hN i hi)])
    _ = ∑ k ∈ s.image (fun i => w i-N), a (k+N) := by
      symm
      apply Finset.sum_image
      exact hinj
    _ ≤ tail a N := ((summable_nat_add_iff N).mpr ha).sum_le_tsum _ (fun _ _ => hn _)

end SeparableQuotient.SeriesTails

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

lemma evaluateArray_finite (x : Γ →₀ ℝ) (g : Array) :
    norming.evaluateArray (norming.includeFinite x) g = ∑ a ∈ x.support, (g a : ℝ) * x a := by
  rw [norming.evaluateArray_eq]
  simp only [norming.coordinate_includeFinite]
  have h1 : ∑ a ∈ g.support, (g a : ℝ) * x a =
      ∑ a ∈ g.support ∪ x.support, (g a : ℝ) * x a := by
    apply Finset.sum_subset Finset.subset_union_left
    intro a _ ha
    simp [Finsupp.notMem_support_iff.mp ha]
  have h2 : ∑ a ∈ x.support, (g a : ℝ) * x a =
      ∑ a ∈ g.support ∪ x.support, (g a : ℝ) * x a := by
    apply Finset.sum_subset Finset.subset_union_right
    intro a _ ha
    simp [Finsupp.notMem_support_iff.mp ha]
  exact h1.trans h2.symm

noncomputable def vectorL1 (x : Γ →₀ ℝ) : ℝ := ∑ a ∈ x.support, |x a|

lemma vectorL1_nonneg (x : Γ →₀ ℝ) : 0 ≤ vectorL1 x :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma typeI_eval_le_l1 {f : Family} (e : TypeI f)
    (hm : ∀ j, e.child j ∈ f.norming) (x : Γ →₀ ℝ) :
    |norming.evaluateArray (norming.includeFinite x) e.value| ≤
      vectorL1 x * (1 / (f.m e.weight : ℝ)) := by
  rw [evaluateArray_finite]
  calc
    |∑ a ∈ x.support, (e.value a : ℝ) * x a| ≤ ∑ a ∈ x.support, |(e.value a : ℝ) * x a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ x.support, |x a| * (1 / (f.m e.weight : ℝ)) := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left (e.coefficient_bound
        (fun j a => full_coefficient_bound _ (f.norming_subset_full (hm j)) a) a) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; rfl

lemma path_piece_zero_of_earlier_hit {f : Family} (P : LegalFinitePath f)
    (x y : Γ →₀ ℝ) (hs : ∀ a ∈ x.support, ∀ b ∈ y.support, a < b)
    (J T : ℕ) (δ : ℝ) (hδ : 0 < δ) (hh : WindowHit P x J T δ)
    (i : Fin P.val.length) (hi : P.val.raw.weight i < J) :
    norming.evaluateArray (norming.includeFinite y) (P.val.raw.piece i) = 0 := by
  obtain ⟨j, hj, _, a, ha, ha'⟩ := hh.anchor hδ
  have hij : i < j := P.val.valid.weight_strict.lt_iff_lt.mp (hi.trans_le hj)
  rw [evaluateArray_finite]
  apply Finset.sum_eq_zero
  intro b hb
  have hz : P.val.raw.piece i b = 0 := by
    by_contra hn
    have hba := P.val.valid.successive i j hij j.isLt b
      (Finsupp.mem_support_iff.mpr hn) a ha'
    exact (lt_asymm hba (hs a ha b hb))
  simp only [hz, Rat.cast_zero, zero_mul]

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.Norming
open scoped Classical

lemma Family.theta_summable (f : Family) : Summable f.theta := by
  apply (summable_nat_add_iff 1).mp
  simpa only [Family.theta, Nat.add_sub_cancel] using (Parameters.hasSum_theta f.s_ge_two).summable

lemma Family.m_inv_summable (f : Family) : Summable (fun j => 1 / (f.m j : ℝ)) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [Family.m, Nat.add_sub_cancel] using f.reciprocal_summable

end SeparableQuotient.Norming

namespace SeparableQuotient.SeriesTails
open scoped Classical

lemma sum_outside_window_bound {ι : Type*} (s : Finset ι) (w : ι → ℕ) (v : ι → ℝ)
    (hi : Set.InjOn w s) (B J T : ℕ) (hBJ : B ≤ J) (hJT : J ≤ T)
    (a b : ℕ → ℝ) (ha : Summable a) (hb : Summable b)
    (han : ∀ n, 0 ≤ a n) (hbn : ∀ n, 0 ≤ b n)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hz : ∀ i ∈ s, w i < B → v i = 0)
    (hl : ∀ i ∈ s, B ≤ w i → w i < J → |v i| ≤ A * a (w i))
    (hh : ∀ i ∈ s, T < w i → |v i| ≤ C * b (w i)) :
    |(∑ i ∈ s, v i) - ∑ i ∈ s, if J ≤ w i ∧ w i ≤ T then v i else 0| ≤
      A * tail a B + C * tail b (T+1) := by
  let lo := s.filter (fun i => B ≤ w i ∧ w i < J)
  let hi' := s.filter (fun i => T < w i)
  have heq : (∑ i ∈ s, v i) - (∑ i ∈ s, if J ≤ w i ∧ w i ≤ T then v i else 0) =
      (∑ i ∈ lo, v i) + ∑ i ∈ hi', v i := by
    rw [← Finset.sum_sub_distrib]
    simp only [lo, hi', Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i his
    by_cases h1 : w i < B
    · have h2 : ¬ (J ≤ w i ∧ w i ≤ T) := by omega
      have h3 : ¬ (B ≤ w i ∧ w i < J) := by omega
      have h4 : ¬ T < w i := by omega
      simp only [hz i his h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, sub_self, add_zero]
    · by_cases h2 : w i < J
      · have h3 : ¬ (J ≤ w i ∧ w i ≤ T) := by omega
        have h4 : B ≤ w i ∧ w i < J := by omega
        have h5 : ¬ T < w i := by omega
        simp only [ite_eq_right h3, ite_eq_left h4, ite_eq_right h5, sub_zero, add_zero]
      · by_cases h3 : w i ≤ T
        · have h4 : J ≤ w i ∧ w i ≤ T := by omega
          have h5 : ¬ (B ≤ w i ∧ w i < J) := by omega
          have h6 : ¬ T < w i := by omega
          simp only [ite_eq_left h4, ite_eq_right h5, ite_eq_right h6, sub_self, add_zero]
        · have h4 : ¬ (J ≤ w i ∧ w i ≤ T) := by omega
          have h5 : ¬ (B ≤ w i ∧ w i < J) := by omega
          have h6 : T < w i := by omega
          simp only [ite_eq_right h4, ite_eq_right h5, ite_eq_left h6, sub_zero, zero_add]
  have hlo : |∑ i ∈ lo, v i| ≤ A * tail a B := by
    calc
      _ ≤ ∑ i ∈ lo, |v i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ lo, A * a (w i) := Finset.sum_le_sum (fun i his =>
        hl i (Finset.mem_filter.mp his).1 (Finset.mem_filter.mp his).2.1 (Finset.mem_filter.mp his).2.2)
      _ = A * ∑ i ∈ lo, a (w i) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_le_tail a ha han lo w
        (hi.mono (Finset.filter_subset _ _)) B (fun i his => (Finset.mem_filter.mp his).2.1)) hA
  have hhi : |∑ i ∈ hi', v i| ≤ C * tail b (T+1) := by
    calc
      _ ≤ ∑ i ∈ hi', |v i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ hi', C * b (w i) := Finset.sum_le_sum (fun i his =>
        hh i (Finset.mem_filter.mp his).1 (Finset.mem_filter.mp his).2)
      _ = C * ∑ i ∈ hi', b (w i) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_le_tail b hb hbn hi' w
        (hi.mono (Finset.filter_subset _ _)) (T+1) (fun i his => (Finset.mem_filter.mp his).2)) hC
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hlo hhi)

end SeparableQuotient.SeriesTails

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

lemma finitePathFunctional_apply {f : Family} (P : LegalFinitePath f) (x : E) :
    finitePathFunctional P.val P.property x = norming.evaluateArray x P.val.value := by
  exact (norming.evaluateArray_eq_functional x ⟨P.val.value, finitePath_mem_full P.val P.property⟩).symm

lemma window_error_bound {f : Family} (P : LegalFinitePath f)
    (x y : Γ →₀ ℝ) (hs : ∀ a ∈ x.support, ∀ b ∈ y.support, a < b)
    (B S J T : ℕ) (hBJ : B ≤ J) (hJT : J ≤ T)
    (δ A : ℝ) (hδ : 0 < δ) (hA : 0 ≤ A) (hh : WindowHit P x B S δ)
    (hl : ∀ e : TypeI f, (∀ j, e.child j ∈ f.norming) → e.weight < J →
      |norming.evaluateArray (norming.includeFinite y) e.value| ≤ A * f.theta e.weight) :
    |finitePathFunctional P.val P.property (norming.includeFinite y) -
      norming.evaluateArray (norming.includeFinite y) (P.val.window J T)| ≤
      A * tail f.theta B + vectorL1 y * tail (fun j => 1 / (f.m j : ℝ)) (T+1) := by
  rw [finitePathFunctional_apply]
  simp only [FinitePath.value, FinitePath.window, map_sum, apply_ite, map_zero]
  apply sum_outside_window_bound Finset.univ (fun i : Fin P.val.length => P.val.raw.weight i)
    _ P.val.valid.weight_strict.injective.injOn B J T hBJ hJT f.theta
    (fun j => 1 / (f.m j : ℝ)) f.theta_summable f.m_inv_summable f.theta_nonneg
    (fun _ => by positivity) A (vectorL1 y) hA (vectorL1_nonneg y)
  · exact fun i _ hi => path_piece_zero_of_earlier_hit P x y hs B S δ hδ hh i hi
  · intro i _ _ hi
    rw [← P.val.weight_eq i] at hi
    simpa only [P.val.value_eq, P.val.weight_eq] using hl (P.val.piece i) (P.property i) hi
  · intro i _ _
    rw [← P.val.value_eq i, ← P.val.weight_eq i]
    exact typeI_eval_le_l1 (P.val.piece i) (P.property i) y

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.CoverRecurrence
open Filter
open scoped Classical Topology

/-- Uniformly finite covers of all initial segments give a single sequence of
covering objects which eventually hits every member of an infinite fixed set.
No compactness of the covering objects themselves is assumed. -/
lemma recurrent_of_covers {Λ : Type*} (Hit : Λ → ℕ → Prop) (D : ℕ)
    (hcover : ∀ n, ∃ R : Finset Λ, R.card ≤ D ∧ ∀ i ≤ n, ∃ P ∈ R, Hit P i) :
    ∃ (P : ℕ → Λ) (W : Set ℕ), W.Infinite ∧ ∀ i ∈ W, ∀ᶠ n in atTop, Hit (P n) i := by
  choose R hR hhit using hcover
  have hfunc (n : ℕ) : ∃ P : Fin (D+1) → Λ, ∀ i ≤ n, ∃ b, Hit (P b) i := by
    obtain ⟨p₀, hp₀, _⟩ := hhit n 0 (Nat.zero_le _)
    let e : Fin (R n).card ≃ R n := (R n).equivFin.symm
    let P : Fin (D+1) → Λ := fun b => if hb : b.val < (R n).card then (e ⟨b, hb⟩).val else p₀
    refine ⟨P, fun i hi => ?_⟩
    obtain ⟨p, hp, hh⟩ := hhit n i hi
    let j := e.symm ⟨p, hp⟩
    let b : Fin (D+1) := ⟨j.val, j.isLt.trans_le ((hR n).trans (Nat.le_succ D))⟩
    refine ⟨b, ?_⟩
    have hb : b.val < (R n).card := j.isLt
    change Hit (P b) i
    rw [show P b = p from by
      dsimp only [P]
      rw [dite_eq_left hb]
      change (e (e.symm ⟨p, hp⟩)).val = p
      rw [e.apply_symm_apply]]
    exact hh
  choose P hP using hfunc
  let c : ℕ → ℕ → Fin (D+1) := fun n i => if hi : i ≤ n then (hP n i hi).choose else 0
  have hc (n i : ℕ) (hi : i ≤ n) : Hit (P n (c n i)) i := by
    simpa only [c, dite_eq_left hi] using (hP n i hi).choose_spec
  obtain ⟨l, _, φ, hφ, hl⟩ := isCompact_univ.tendsto_subseq
    (x := c) (fun _ => Set.mem_univ _)
  obtain ⟨b, hb⟩ := Finite.exists_infinite_fiber l
  refine ⟨fun n => P (φ n) b, {i | l i = b}, Set.infinite_coe_iff.mp hb, fun i hi => ?_⟩
  have he : ∀ᶠ n in atTop, c (φ n) i = l i := by
    simpa only [nhds_discrete, tendsto_pure, Function.comp_apply] using (tendsto_pi_nhds.mp hl i)
  filter_upwards [he, eventually_ge_atTop i] with n hn hin
  have hh := hc (φ n) i (hin.trans (hφ.id_le n))
  rwa [hn, hi] at hh

end SeparableQuotient.CoverRecurrence

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

/-- Pathwise nullity excludes four recurrent hits by reconstruction of a limiting infinite path. -/
lemma not_all_four_hits {f : Family} (x : ℕ → Γ →₀ ℝ) (J T : ℕ → ℕ)
    (hJT : ∀ i, J i ≤ T i)
    (horder : ∀ i j, i < j → T i < J j)
    (hs : ∀ i j, i < j → ∀ a ∈ (x i).support, ∀ b ∈ (x j).support, a < b)
    (hcoh : ∀ i j, i < j → ∀ a ∈ (x i).support, ∀ b ∈ (x i).support,
      rho (min a b) (max a b) ≤ J j)
    (M A δ : ℝ) (hM : ∀ i, ‖norming.includeFinite (x i)‖ ≤ M) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hlow : ∀ i (e : TypeI f), (∀ j, e.child j ∈ f.norming) → e.weight < J i →
      |norming.evaluateArray (norming.includeFinite (x i)) e.value| ≤ A * f.theta e.weight)
    (htail : Tendsto (fun i => vectorL1 (x i) * tail (fun j => 1 / (f.m j : ℝ)) (T i+1)) atTop (𝓝 0))
    (hnull : ∀ Q : InfinitePath f, Tendsto (fun i => pathFunctional Q (norming.includeFinite (x i))) atTop (𝓝 0)) :
    ¬ (∀ w v t k : ℕ, w < v → v < t → t < k →
      ∃ P : LegalFinitePath f, WindowHit P (x w) (J w) (T w) δ ∧
        WindowHit P (x v) (J v) (T v) δ ∧ WindowHit P (x t) (J t) (T t) δ ∧
        WindowHit P (x k) (J k) (T k) δ) := by
  intro hall
  obtain ⟨D, hD⟩ := finite_window_covers x J T horder hcoh M δ hM hδ hall
  obtain ⟨P, W, hW, hP⟩ := CoverRecurrence.recurrent_of_covers
    (fun P i => WindowHit P (x i) (J i) (T i) δ) D hD
  have hJ : StrictMono J := fun i j hij => (hJT i).trans_lt (horder i j hij)
  have hwin (B : ℕ) : ∃ T' : ℕ, ∃ s : Finset Γ, ∀ᶠ n in atTop,
      ∃ i < (P n).val.length, B < (P n).val.raw.weight i ∧ (P n).val.raw.weight i ≤ T' ∧
        ∃ a ∈ s, a ∈ ((P n).val.raw.piece i).support := by
    obtain ⟨i, hi, hBi⟩ := hW.exists_gt B
    refine ⟨T i, (x i).support, (hP i hi).mono fun n hn => ?_⟩
    obtain ⟨j, hj, hj', a, ha, ha'⟩ := hn.anchor hδ
    exact ⟨j, j.isLt, hBi.trans_le ((hJ.id_le i).trans hj), hj', a, ha, ha'⟩
  obtain ⟨φ, Q, hφ, hQ⟩ := path_of_recurrent_windows (fun n => (P n).val)
    (fun n => (P n).property) hwin
  have hlim (i : ℕ) := stabilized_path_tendsto (fun n => (P (φ n)).val)
    (fun n => (P (φ n)).property) Q
    (fun j => (hQ j).mono fun _ hn => ⟨hn.1, hn.2.1, hn.2.2.1⟩) (norming.includeFinite (x i))
  have ht : Tendsto (fun i => A * tail f.theta (J i)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using tendsto_const_nhds.mul ((tendsto_tail f.theta).comp hJ.tendsto_atTop)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (by linarith : (0:ℝ) < δ/4)))
  obtain ⟨w₀, hw₀, hNw₀⟩ := hW.exists_gt N₀
  have hsmall : A * tail f.theta (J w₀) < δ/4 := hN₀ _ hNw₀.le
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (htail.eventually (gt_mem_nhds (by linarith : (0:ℝ) < δ/4)))
  have hn : Tendsto (fun i => |pathFunctional Q (norming.includeFinite (x i))|) atTop (𝓝 0) := by
    simpa only [abs_zero] using (hnull Q).abs
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hn.eventually (gt_mem_nhds (by linarith : (0:ℝ) < δ/2)))
  obtain ⟨i, hi, hBig⟩ := hW.exists_gt (max w₀ (max N₁ N₂))
  have hwi : w₀ < i := (le_max_left _ _).trans_lt hBig
  have hN1i : N₁ ≤ i := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hBig.le
  have hN2i : N₂ ≤ i := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hBig.le
  have hbound : ∀ᶠ n in atTop,
      δ/2 ≤ |finitePathFunctional (P (φ n)).val (P (φ n)).property (norming.includeFinite (x i))| := by
    filter_upwards [(hP w₀ hw₀).filter_mono hφ.tendsto_atTop, (hP i hi).filter_mono hφ.tendsto_atTop] with n hn₀ hni
    have he := window_error_bound (P (φ n)) (x w₀) (x i) (hs w₀ i hwi)
      (J w₀) (T w₀) (J i) (T i) (hJ.monotone hwi.le) (hJT i) δ A hδ hA hn₀ (hlow i)
    have ht' := hN₁ i hN1i
    have ha := abs_sub_abs_le_abs_sub
      (norming.evaluateArray (norming.includeFinite (x i)) ((P (φ n)).val.window (J i) (T i)))
      (finitePathFunctional (P (φ n)).val (P (φ n)).property (norming.includeFinite (x i)))
    rw [abs_sub_comm] at ha
    change δ < |norming.evaluateArray (norming.includeFinite (x i)) ((P (φ n)).val.window (J i) (T i))| at hni
    linarith
  have hge : δ/2 ≤ |pathFunctional Q (norming.includeFinite (x i))| :=
    ge_of_tendsto (hlim i).abs hbound
  exact (not_lt_of_ge hge) (hN₂ i hN2i)

end SeparableQuotient.ActualSpace

end

end OAI
