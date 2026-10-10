import OAI.Probability.GammaPassage.CrossingEvents

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Grid Set Finset MeasureTheory ProbabilityTheory

theorem pathIn_append (p : Vertex) (ds es : List Step) (S : Set Vertex)
    (hd : PathIn p ds S) (he : PathIn (p+displacement ds) es S) :
    PathIn p (ds++es) S := by
  intro i hi
  by_cases hid : i ≤ ds.length
  · simpa only [List.take_append, Nat.sub_eq_zero_of_le hid, List.take_zero,
      List.append_nil] using hd i hid
  · have hle : ds.length ≤ i := by omega
    have hie : i-ds.length ≤ es.length := by simp only [List.length_append] at hi; omega
    have hh := he (i-ds.length) hie
    simpa only [List.take_append, List.take_of_length_le hle, displacement_append,
      add_assoc] using hh

lemma vertical_straight_subset (X lo hi y : ℤ) (d : Step) (n : ℕ)
    (hd : d=.north ∨ d=.south)
    (hy : lo ≤ y ∧ y ≤ hi)
    (hz : lo ≤ y+(n : ℤ)*d.delta.2 ∧ y+(n : ℤ)*d.delta.2 ≤ hi) :
    (Finset.range n).image (straightEdge (X,y) d) ⊆ verticalIntervalEdges X lo hi := by
  intro e he
  obtain ⟨i,hi',rfl⟩ := Finset.mem_image.mp he
  have hi'' := Finset.mem_range.mp hi'
  rcases hd with rfl | rfl
  · refine Finset.mem_image.mpr ⟨y+i,Finset.mem_Ico.mpr ?_,?_⟩
    · simp only [Step.delta] at hz
      constructor <;> omega
    · simp [straightEdge,Step.edge,Step.delta]
  · refine Finset.mem_image.mpr ⟨y-(i : ℤ)-1,Finset.mem_Ico.mpr ?_,?_⟩
    · simp only [Step.delta] at hz
      constructor <;> omega
    · simp [straightEdge,Step.edge,Step.delta,Prod.ext_iff]
      omega

lemma vertical_straight_in (X lo hi y : ℤ) (d : Step) (n : ℕ)
    (hd : d=.north ∨ d=.south)
    (hy : lo ≤ y ∧ y ≤ hi)
    (hz : lo ≤ y+(n : ℤ)*d.delta.2 ∧ y+(n : ℤ)*d.delta.2 ≤ hi) :
    PathIn (X,y) (List.replicate n d) {p | p.1=X ∧ lo ≤ p.2 ∧ p.2 ≤ hi} := by
  intro i hi'
  have hi'' : i ≤ n := by simpa using hi'
  have htake : (List.replicate n d).take i = List.replicate i d := by
    simp [List.take_replicate,Nat.min_eq_left hi'']
  rw [htake]
  simp only [displacement,List.map_replicate,List.sum_replicate]
  rcases hd with rfl | rfl <;>
    simp [Step.delta,Prod.smul_mk] at hz ⊢ <;> omega

/-- Both traversal directions use the same internal-edge sum, with each
edge charged exactly once on the straight attachment path. -/
theorem vertical_interval_all_pairs (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (X lo hi : ℤ) (p q : Vertex) (hp : p.1=X ∧ lo ≤ p.2 ∧ p.2 ≤ hi)
    (hq : q.1=X ∧ lo ≤ q.2 ∧ q.2 ≤ hi) :
    ∃ ds, p+displacement ds=q ∧
      pathCost w p ds ≤ ∑ e ∈ verticalIntervalEdges X lo hi,w e ∧
      PathIn p ds {z | z.1=X ∧ lo ≤ z.2 ∧ z.2 ≤ hi} := by
  have hp' : p=(X,p.2) := Prod.ext hp.1 rfl
  have hq' : q=(X,q.2) := Prod.ext hq.1 rfl
  let ds := vertical (q.2-p.2)
  refine ⟨ds,?_,?_,?_⟩
  · simp [ds,displacement_vertical,Prod.ext_iff,hp.1,hq.1]
  · by_cases hle : p.2 ≤ q.2
    · have hn : (((q.2-p.2).toNat : ℕ) : ℤ)=q.2-p.2 := Int.toNat_of_nonneg (by omega)
      rw [show ds=List.replicate (q.2-p.2).toNat Step.north by simp [ds,vertical,hle],
        hp',pathCost_replicate_edgeSet]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · apply vertical_straight_subset X lo hi p.2 .north _ (Or.inl rfl) hp.2
        have hcancel : p.2 + (q.2-p.2) = q.2 := by omega
        simpa only [Step.delta,mul_one,hn,hcancel] using hq.2
      · intro e _ _; exact hw e
    · have hn : (((-(q.2-p.2)).toNat : ℕ) : ℤ)=p.2-q.2 := by omega
      rw [show ds=List.replicate (-(q.2-p.2)).toNat Step.south by simp [ds,vertical,hle],
        hp',pathCost_replicate_edgeSet]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · apply vertical_straight_subset X lo hi p.2 .south _ (Or.inr rfl) hp.2
        simpa [Step.delta,neg_sub,Int.toNat_of_nonneg (show 0 ≤ p.2-q.2 by omega)] using hq.2
      · intro e _ _; exact hw e
  · rw [hp']
    by_cases hle : p.2 ≤ q.2
    · have hn : (((q.2-p.2).toNat : ℕ) : ℤ)=q.2-p.2 := Int.toNat_of_nonneg (by omega)
      rw [show ds=List.replicate (q.2-p.2).toNat Step.north by simp [ds,vertical,hle]]
      apply vertical_straight_in X lo hi p.2 .north _ (Or.inl rfl) hp.2
      have hcancel : p.2 + (q.2-p.2) = q.2 := by omega
      simpa only [Step.delta,mul_one,hn,hcancel] using hq.2
    · have hn : (((-(q.2-p.2)).toNat : ℕ) : ℤ)=p.2-q.2 := by omega
      rw [show ds=List.replicate (-(q.2-p.2)).toNat Step.south by simp [ds,vertical,hle]]
      apply vertical_straight_in X lo hi p.2 .south _ (Or.inr rfl) hp.2
      simpa [Step.delta,neg_sub,Int.toNat_of_nonneg (show 0 ≤ p.2-q.2 by omega)] using hq.2

lemma transverse_interval_all_pairs (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b : ℝ) (X : ℤ) (lo hi : ℝ) (p q : Vertex)
    (hp : p.1=X ∧ lo ≤ transverse b p ∧ transverse b p ≤ hi)
    (hq : q.1=X ∧ lo ≤ transverse b q ∧ transverse b q ≤ hi) :
    ∃ ds, p+displacement ds=q ∧
      pathCost w p ds ≤ ∑ e ∈ transverseIntervalEdges b X lo hi,w e ∧
      PathIn p ds {z | z.1=X ∧ lo ≤ transverse b z ∧ transverse b z ≤ hi} := by
  have conv (z : Vertex) (hz : z.1=X) :
      (lo ≤ transverse b z ∧ transverse b z ≤ hi) ↔
      (⌈lo+b*X⌉ ≤ z.2 ∧ z.2 ≤ ⌊hi+b*X⌋) := by
    rw [Int.ceil_le,Int.le_floor]
    simp only [transverse,hz]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  obtain ⟨ds,hd,hc,hin⟩ := vertical_interval_all_pairs w hw X ⌈lo+b*X⌉ ⌊hi+b*X⌋ p q
    ⟨hp.1,(conv p hp.1).mp hp.2⟩ ⟨hq.1,(conv q hq.1).mp hq.2⟩
  refine ⟨ds,hd,hc,?_⟩
  intro i hi'
  have hz := hin i hi'
  exact ⟨hz.1,(conv _ hz.1).mpr hz.2⟩

end GammaFPP.CrossingBridge

end OAI
