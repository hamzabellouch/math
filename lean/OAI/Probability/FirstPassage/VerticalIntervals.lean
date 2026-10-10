import OAI.Probability.FirstPassage.LocalizedEvents
import OAI.Probability.FirstPassage.PathConcatenation

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def verticalIntervalEdges (X lo hi : ℤ) : Finset Edge :=
  (Finset.Ico lo hi).image (fun y => ((X,y),true))

lemma verticalIntervalEdges_card (X lo hi : ℤ) :
    (verticalIntervalEdges X lo hi).card=(hi-lo).toNat := by
  rw [verticalIntervalEdges,Finset.card_image_of_injective]
  · exact Int.card_Ico lo hi
  · intro a b hab
    exact congrArg (fun e : Edge => e.1.2) hab

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
        simpa only [Step.delta,mul_one,hn,add_sub_cancel] using hq.2
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
      simpa only [Step.delta,mul_one,hn,add_sub_cancel] using hq.2
    · have hn : (((-(q.2-p.2)).toNat : ℕ) : ℤ)=p.2-q.2 := by omega
      rw [show ds=List.replicate (-(q.2-p.2)).toNat Step.south by simp [ds,vertical,hle]]
      apply vertical_straight_in X lo hi p.2 .south _ (Or.inr rfl) hp.2
      simpa [Step.delta,neg_sub,Int.toNat_of_nonneg (show 0 ≤ p.2-q.2 by omega)] using hq.2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

lemma costly_edge_set_probability_real (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (a : ℝ) :
    P.real {ω | a ≤ ∑ e ∈ S, τ e ω} ≤ (2 : ℝ)^S.card*Real.exp (-a/2) := by
  have he := ENNReal.toReal_mono
    (show (2 : ℝ≥0∞)^S.card/ENNReal.ofReal (Real.exp (a/2)) ≠ ⊤ from
      ENNReal.div_ne_top (by simp) (by positivity)) (costly_edge_set_probability h S a)
  simp only [ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] at he
  change P.real _ ≤ _ at he
  rw [show -a/2=-(a/2) by ring,Real.exp_neg]
  simpa only [div_eq_mul_inv] using he

theorem grid_vertical_cost_tail (henv : ExponentialEnvironment P τ)
    (X lo hi : ℤ) (a : ℝ)
    (hcard : ((verticalIntervalEdges X lo hi).card : ℝ) ≤ 50*a) :
    P.real {ω | 100*a < ∑ e ∈ verticalIntervalEdges X lo hi,τ e ω} ≤
      Real.exp (-(50*(1-Real.log 2))*a) := by
  let _ := henv.probability
  apply (measureReal_mono (show {ω | 100*a < ∑ e ∈ verticalIntervalEdges X lo hi,τ e ω} ⊆
    {ω | 100*a ≤ ∑ e ∈ verticalIntervalEdges X lo hi,τ e ω} from by
      intro ω hω
      change 100*a ≤ _
      exact le_of_lt hω)).trans
  apply (costly_edge_set_probability_real henv _ (100*a)).trans
  rw [show (2 : ℝ)^(verticalIntervalEdges X lo hi).card =
      Real.exp ((verticalIntervalEdges X lo hi).card*Real.log 2) by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 2)],← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hcard (show 0 ≤ Real.log 2 by positivity)
  nlinarith

end PlanarFPP

end OAI
