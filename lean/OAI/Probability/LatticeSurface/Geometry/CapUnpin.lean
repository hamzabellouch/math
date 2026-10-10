import Mathlib
import OAI.Probability.LatticeSurface.Convexity.BoundedBase
import OAI.Probability.LatticeSurface.Geometry.CapReflection

namespace OAI

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

def unpinIndex (pins : Set V) (x : V) (hx : x ∈ pins) :
    Free (pins \ {x}) ≃ Option (Free pins) where
  toFun y := if hy : (y : V) = x then none else some ⟨y, fun hp => y.2 ⟨hp,hy⟩⟩
  invFun o := match o with
    | none => ⟨x, by simp⟩
    | some y => ⟨y, fun hp => y.2 hp.1⟩
  left_inv := by
    intro y
    by_cases hy : (y : V) = x
    · simp only [dite_eq_left hy]
      exact Subtype.ext hy.symm
    · simp only [dite_eq_right hy]
  right_inv := by
    intro o
    cases o with
    | none => simp
    | some y =>
      have hn : (y : V) ≠ x := fun hh => y.2 (hh ▸ hx)
      simp [hn]

def splitUnpin (pins : Set V) (x : V) (hx : x ∈ pins) :
    (Free (pins \ {x}) → ℝ) ≃ᵐ ((Free pins → ℝ) × ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Option (Free pins) => ℝ) (unpinIndex pins x hx)).trans
    (MeasurableEquiv.piOptionEquivProd (fun _ => ℝ))

lemma preserving_splitUnpin [Fintype V] (pins : Set V) (x : V) (hx : x ∈ pins) :
    MeasurePreserving (splitUnpin pins x hx) :=
  preserving_piOptionReal.comp (volume_measurePreserving_piCongrLeft _ (unpinIndex pins x hx))

lemma insert_restore (pins : Set V) (x : V) (hx : x ∈ pins) (b : V → ℝ)
    (h : Free pins → ℝ) (t : ℝ) (y : V) :
    restore (pins \ {x}) b ((splitUnpin pins x hx).symm (h,t)) y =
      if y = x then t else restore pins b h y := by
  by_cases hy : y = x
  · subst y
    simp [restore, splitUnpin, MeasurableEquiv.piCongrLeft, unpinIndex,
      MeasurableEquiv.piOptionEquivProd]
    rfl
  · by_cases hyp : y ∈ pins
    · have hn : y ∈ pins \ {x} := ⟨hyp,hy⟩
      simp [restore, hn, hy, hyp]
    · have hn : y ∉ pins \ {x} := fun hh => hyp hh.1
      simp [restore, hn, hy, hyp, splitUnpin, MeasurableEquiv.piCongrLeft,
        unpinIndex, MeasurableEquiv.piOptionEquivProd]
      rfl

lemma insert_feasible [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (pins : Set V) (x : V) (hx : x ∈ pins) (b : V → ℝ)
    (h : Free pins → ℝ) (hf : h ∈ below G pins b (b x) (G.neighborFinset x))
    (t : ℝ) (ht : t ∈ Icc (b x-1) (b x)) :
    (splitUnpin pins x hx).symm (h,t) ∈ conditionalBody G (pins \ {x}) b := by
  intro y z hyz
  rw [insert_restore pins x hx b, insert_restore pins x hx b]
  have hval : restore pins b h x = b x := by simp [restore, hx]
  by_cases hy : y = x <;> by_cases hz : z = x
  · exact False.elim (hyz.ne (hy.trans hz.symm))
  · simp only [ite_eq_left hy, ite_eq_right hz]
    subst y
    have hn : z ∈ G.neighborFinset x := by simpa using hyz
    have hu := hf.2 z hn
    have hl := (abs_le.mp (hf.1 x z hyz)).2
    rw [hval] at hl
    exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · simp only [ite_eq_right hy, ite_eq_left hz]
    subst z
    have hn : y ∈ G.neighborFinset x := by simpa using hyz.symm
    have hu := hf.2 y hn
    have hl := (abs_le.mp (hf.1 x y hyz.symm)).2
    rw [hval] at hl
    exact abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · simpa only [ite_eq_right hy, ite_eq_right hz] using hf.1 y z hyz

theorem volume_release_max_pin [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (pins : Set V) (x : V) (hx : x ∈ pins) (b : V → ℝ)
    (hb : ∀ y ∈ pins, b y ≤ b x) :
    volume (conditionalBody G pins b) ≤
      2 ^ G.degree x * volume (conditionalBody G (pins \ {x}) b) := by
  let B := below G pins b (b x) (G.neighborFinset x)
  let K := conditionalBody G (pins \ {x}) b
  have hK : MeasurableSet K := (closed_conditionalBody G _ b).measurableSet
  have he := (preserving_splitUnpin pins x hx).symm (splitUnpin pins x hx)
  have hvol : volume B ≤ volume K := by
    have hsub : B ×ˢ Icc (b x-1) (b x) ⊆ (splitUnpin pins x hx).symm ⁻¹' K := by
      rintro ⟨h,t⟩ ⟨hh,ht⟩
      exact insert_feasible G pins x hx b h hh t ht
    have hm := measure_mono (μ := (volume : Measure ((Free pins → ℝ) × ℝ))) hsub
    rw [he.measure_preimage hK.nullMeasurableSet] at hm
    have hI : volume (Icc (b x-1) (b x)) = 1 := by
      rw [Real.volume_Icc, show b x-(b x-1) = 1 by ring, ENNReal.ofReal_one]
    change ((volume : Measure (Free pins → ℝ)).prod (volume : Measure ℝ))
      (B ×ˢ Icc (b x-1) (b x)) ≤ volume K at hm
    rw [Measure.prod_prod, hI, mul_one] at hm
    exact hm
  calc
    volume (conditionalBody G pins b) ≤ 2 ^ (G.neighborFinset x).card * volume B :=
      volume_one_sided G pins b (b x) hb _
    _ = 2 ^ G.degree x * volume B := by rw [SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ _ := mul_le_mul_right hvol _

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

lemma restore_neg {V : Type*} (pins : Set V) (b : V → ℝ) (h : Free pins → ℝ) (x : V) :
    restore pins (fun y => -b y) (-h) x = -restore pins b h x := by
  by_cases hx : x ∈ pins <;> simp [restore, hx]

lemma body_neg_preimage {V : Type*} (G : SimpleGraph V) (pins : Set V) (b : V → ℝ) :
    conditionalBody G pins (fun y => -b y) = Neg.neg ⁻¹' conditionalBody G pins b := by
  ext h
  have hh : ∀ x, restore pins b (-h) x = -restore pins (fun y => -b y) h x := by
    intro x
    simpa only [neg_neg] using restore_neg pins (fun y => -b y) h x
  simp only [conditionalBody, mem_preimage, mem_ofPred_eq, hh, neg_sub_neg, abs_sub_comm]

lemma volume_body_neg {V : Type*} [Fintype V]
    (G : SimpleGraph V) (pins : Set V) (b : V → ℝ) :
    volume (conditionalBody G pins (fun y => -b y)) = volume (conditionalBody G pins b) := by
  rw [body_neg_preimage]
  exact (Measure.measurePreserving_neg volume).measure_preimage
    (closed_conditionalBody G pins b).measurableSet.nullMeasurableSet

theorem volume_release_min_pin {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (pins : Set V) (x : V) (hx : x ∈ pins) (b : V → ℝ)
    (hb : ∀ y ∈ pins, b x ≤ b y) :
    volume (conditionalBody G pins b) ≤
      2 ^ G.degree x * volume (conditionalBody G (pins \ {x}) b) := by
  have hh := volume_release_max_pin G pins x hx (fun y => -b y)
    (fun y hy => neg_le_neg (hb y hy))
  rw [volume_body_neg G pins b, volume_body_neg G (pins \ {x}) b] at hh
  exact hh

theorem volume_release_extreme_pin {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (pins : Set V) (x : V) (hx : x ∈ pins) (b : V → ℝ)
    (hb : (∀ y ∈ pins, b y ≤ b x) ∨ (∀ y ∈ pins, b x ≤ b y)) :
    volume (conditionalBody G pins b) ≤
      2 ^ G.degree x * volume (conditionalBody G (pins \ {x}) b) := by
  rcases hb with hb | hb
  · exact volume_release_max_pin G pins x hx b hb
  · exact volume_release_min_pin G pins x hx b hb

end ExtremalEdges

end

end OAI
