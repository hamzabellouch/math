import OAI.Analysis.AncientFlat.Regularity.CompactHolder

namespace OAI
noncomputable section
open Set Filter
namespace ParabolicInterior
open ParabolicLocalization
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedSpace ℝ E] in
lemma compact_local_holder (α : ℝ) (hα : 0≤α) (K : Set (V × ℝ)) (hK : IsCompact K)
    (f : V × ℝ → E)
    (hf : ∀ p∈K, ∃ U : Set (V × ℝ), IsOpen U ∧ p∈U ∧
      ∃ C : ℝ, 0≤C ∧ HolderBound α U f C) :
    ∃ C : ℝ, 0≤C ∧ HolderBound α K f C := by
  classical
  choose U hU hp C hC hB using fun p : K => hf p p.property
  have hcover : K⊆⋃ p : K, U p := by
    intro p hp'
    exact mem_iUnion.mpr ⟨⟨p,hp'⟩,hp ⟨p,hp'⟩⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U hU hcover
  let W : {p : K // p∈s} → Set (V × ℝ) := fun p => U p.val
  have hW : K⊆⋃ p, W p := by
    intro p hp'
    obtain ⟨q,hq⟩ := mem_iUnion.mp (hs hp')
    obtain ⟨hq',hpq⟩ := mem_iUnion.mp hq
    exact mem_iUnion.mpr ⟨⟨q,hq'⟩,hpq⟩
  obtain ⟨δ,hδ,hδcover⟩ := lebesgue_number_lemma_of_metric hK (fun p : {p : K // p∈s} => hU p.val) hW
  let B := ∑ p∈s, C p
  have hB0 : 0≤B := Finset.sum_nonneg fun p _ => hC p
  have hCB (p : K) (hp' : p∈s) : C p≤B := Finset.single_le_sum (fun q _ => hC q) hp'
  have hb (p) (hp' : p∈K) : ‖f p‖≤B := by
    obtain ⟨q,hq⟩ := mem_iUnion.mp (hW hp')
    exact ((hB q.val).1 p hq).trans (hCB q.val q.property)
  let d := min δ 1
  have hd : 0<d := lt_min hδ zero_lt_one
  have hdp : 0<d^α := Real.rpow_pos_of_pos hd _
  let A := B+2*B/d^α
  have hA : 0≤A := by dsimp [A]; positivity
  refine ⟨A,hA,fun p hp' => (hb p hp').trans (by dsimp [A]; exact le_add_of_nonneg_right (div_nonneg (by positivity) hdp.le)),?_⟩
  intro p hp' q hq'
  by_cases hn : pdist p q<d
  · obtain ⟨i,hi⟩ := hδcover p hp'
    have hpU : p∈W i := hi (Metric.mem_ball_self hδ)
    have hqU : q∈W i := hi (by
      rw [Metric.mem_ball,dist_eq_norm, norm_sub_rev]
      exact (norm_pair_sub_le_pdist p q (hn.le.trans (min_le_right _ _))).trans_lt
        (hn.trans_le (min_le_left _ _)))
    exact ((hB i.val).2 p hpU q hqU).trans
      (mul_le_mul_of_nonneg_right ((hCB i.val i.property).trans (by dsimp [A]; exact le_add_of_nonneg_right (div_nonneg (by positivity) hdp.le)))
        (Real.rpow_nonneg (pdist_nonneg _ _) _))
  · have hdq : d^α≤pdist p q^α := Real.rpow_le_rpow hd.le (not_lt.mp hn) hα
    have hfar : 2*B≤(2*B/d^α)*pdist p q^α := by
      calc
        _ = (2*B/d^α)*d^α := (div_mul_cancel₀ _ hdp.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hdq (by positivity)
    exact ((norm_sub_le _ _).trans (by linarith [hb p hp',hb q hq'])).trans
      (hfar.trans (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) (Real.rpow_nonneg (pdist_nonneg _ _) _)))
end ParabolicInterior

end

end OAI
