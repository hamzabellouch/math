import Mathlib
import OAI.Probability.LatticeSurface.Convexity.BoundedBase
import OAI.Probability.LatticeSurface.Convexity.BrunnMinkowski
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
import OAI.Probability.LatticeSurface.Dynamics.DisplacementInequality
import OAI.Probability.LatticeSurface.Geometry.CapCentral
import OAI.Probability.LatticeSurface.Geometry.CapCompact
import OAI.Probability.LatticeSurface.Geometry.CapContract
import OAI.Probability.LatticeSurface.Geometry.CapCoordinates
import OAI.Probability.LatticeSurface.Geometry.CapReflection
import OAI.Probability.LatticeSurface.Geometry.CapSplit
import OAI.Probability.LatticeSurface.Geometry.CapUnpin
import OAI.Probability.LatticeSurface.Geometry.CapWeld

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace FacetVolume

end FacetVolume

namespace ExtremalEdges

open scoped ENNReal

end ExtremalEdges

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

def gradientBody (G : SimpleGraph V) (pins : Set V) (W : Finset V) (r : V → V) :
    Set ((Free (pins ∪ (W : Set V)) → ℝ) × (W → ℝ)) :=
  {p | ∀ x y, G.Adj x y → |fromGradients pins W r p x-fromGradients pins W r p y| ≤ 1}

lemma gradientBody_preimage [Fintype V] (G : SimpleGraph V) (pins : Set V)
    (W : Finset V) (hwp : ∀ w ∈ W, w ∉ pins) (r : V → V) :
    gradientBody G pins W r = (gradientCoords pins W hwp r).symm ⁻¹'
      conditionalBody G pins (fun _ => 0) := by
  ext p
  simp only [gradientBody, conditionalBody, Set.mem_preimage, Set.mem_ofPred_eq, gradient_restore]

lemma compact_gradientBody [Fintype V] (G : SimpleGraph V) (hc : G.Connected)
    (pins : Set V) (hp : pins.Nonempty) (W : Finset V)
    (hwp : ∀ w ∈ W, w ∉ pins) (r : V → V) :
    IsCompact (gradientBody G pins W r) := by
  rw [gradientBody_preimage G pins W hwp r, ← MeasurableEquiv.image_eq_preimage_symm]
  exact (compact_zeroBody G hc pins hp).image (continuous_gradientCoords pins W hwp r)

lemma convex_gradientBody (G : SimpleGraph V) (pins : Set V) (W : Finset V) (r : V → V) :
    Convex ℝ (gradientBody G pins W r) := by
  intro p hp q hq s t hs ht hst x y hxy
  simp only [fromGradients_comb]
  calc
    |s * fromGradients pins W r p x+t * fromGradients pins W r q x-
        (s * fromGradients pins W r p y+t * fromGradients pins W r q y)| =
      |s * (fromGradients pins W r p x-fromGradients pins W r p y)+
        t * (fromGradients pins W r q x-fromGradients pins W r q y)| := by congr 1; ring
    _ ≤ |s * (fromGradients pins W r p x-fromGradients pins W r p y)|+
        |t * (fromGradients pins W r q x-fromGradients pins W r q y)| := abs_add_le _ _
    _ ≤ s*1+t*1 := by
      rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
      gcongr
      exacts [hp x y hxy,hq x y hxy]
    _ = 1 := by linarith

lemma neg_gradientBody (G : SimpleGraph V) (pins : Set V) (W : Finset V) (r : V → V)
    {p : (Free (pins ∪ (W : Set V)) → ℝ) × (W → ℝ)} (hp : p ∈ gradientBody G pins W r) :
    -p ∈ gradientBody G pins W r := by
  intro x y hxy
  simpa only [fromGradients_neg, neg_sub_neg, abs_sub_comm] using hp x y hxy

lemma central_gradientBody (G : SimpleGraph V) (pins : Set V) (W : Finset V) (r : V → V) :
    productSlice (gradientBody G pins W r) 0 =
      conditionalBody (G.map (collapse W r)) (pins ∪ (W : Set V)) (fun _ => 0) := by
  ext h
  simp only [productSlice, gradientBody, conditionalBody, Set.mem_ofPred_eq,
    fromGradients_zero, graph_constraint_map]

def capsInterval (u : ℝ) : Set ℝ := Icc (-1) (u-1) ∪ Icc (1-u) 1

lemma measurable_capsInterval (u : ℝ) : MeasurableSet (capsInterval u) :=
  measurableSet_Icc.union measurableSet_Icc

lemma mem_capsInterval {u t : ℝ} (hl : 1-u ≤ |t|) (hh : |t| ≤ 1) : t ∈ capsInterval u := by
  rcases le_total 0 t with ht | ht
  · right
    rw [abs_of_nonneg ht] at hl hh
    exact ⟨hl,hh⟩
  · left
    rw [abs_of_nonpos ht] at hl hh
    constructor <;> linarith

lemma volume_capsInterval (u : ℝ) (hu : 0 ≤ u) :
    volume (capsInterval u) ≤ ENNReal.ofReal (2*u) := by
  calc
    volume (capsInterval u) ≤ volume (Icc (-1:ℝ) (u-1))+volume (Icc (1-u) 1) := measure_union_le _ _
    _ = ENNReal.ofReal u+ENNReal.ofReal u := by simp [Real.volume_Icc]
    _ = ENNReal.ofReal (2*u) := by rw [← ENNReal.ofReal_add hu hu]; congr 1; ring

theorem star_cap_volume [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (pins : Set V) (hp : pins.Nonempty)
    (W : Finset V) (r : V → V) (D : ℕ)
    (hwp : ∀ w ∈ W, w ∉ pins) (hr : ∀ w ∈ W, r w ∉ W)
    (hd : ∀ w ∈ W, G.degree w ≤ D) (he : ∀ w ∈ W, G.Adj w (r w))
    (u : ℝ) (hu : 0 ≤ u) :
    volume {h : Free pins → ℝ | h ∈ conditionalBody G pins (fun _ => 0) ∧
      ∀ w ∈ W, 1-u ≤ |restore pins (fun _ => 0) h w-restore pins (fun _ => 0) h (r w)|} ≤
      (ENNReal.ofReal (2*u))^W.card * (2^D)^W.card *
        volume (conditionalBody G pins (fun _ => 0)) := by
  let S : Set (W → ℝ) := Set.pi Set.univ (fun _ => capsInterval u)
  have hS : MeasurableSet S := MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurable_capsInterval u)
  have hvolS : volume S ≤ (ENNReal.ofReal (2*u))^W.card := by
    rw [show volume S = ∏ _ : W, volume (capsInterval u) from volume_pi_pi _]
    calc
      (∏ _ : W, volume (capsInterval u)) ≤ ∏ _ : W, ENNReal.ofReal (2*u) :=
        Finset.prod_le_prod (fun _ _ => volume_capsInterval u hu)
      _ = _ := by simp
  let K := gradientBody G pins W r
  have hk : IsCompact K := compact_gradientBody G hc pins hp W hwp r
  have hb := product_small_set_bound hk (convex_gradientBody G pins W r)
    (fun _ h => neg_gradientBody G pins W r h) S hS
  have hsub : {h : Free pins → ℝ | h ∈ conditionalBody G pins (fun _ => 0) ∧
      ∀ w ∈ W, 1-u ≤ |restore pins (fun _ => 0) h w-restore pins (fun _ => 0) h (r w)|} ⊆
        (gradientCoords pins W hwp r) ⁻¹' (K ∩ Prod.snd ⁻¹' S) := by
    intro h hh
    constructor
    · change (gradientCoords pins W hwp r) h ∈ gradientBody G pins W r
      rw [gradientBody_preimage G pins W hwp r]
      simpa using hh.1
    · intro w hw
      rw [gradientCoords_difference pins W hwp r hr h w]
      exact mem_capsInterval (hh.2 w w.2) (hh.1 w (r w) (he w w.2))
  calc
    _ ≤ volume ((gradientCoords pins W hwp r) ⁻¹' (K ∩ Prod.snd ⁻¹' S)) := measure_mono hsub
    _ = volume (K ∩ Prod.snd ⁻¹' S) := (preserving_gradientCoords pins W hwp r).measure_preimage
      (hk.measurableSet.inter (hS.preimage measurable_snd)).nullMeasurableSet
    _ ≤ volume S * volume (productSlice K 0) := hb
    _ ≤ (ENNReal.ofReal (2*u))^W.card * ((2^D)^W.card *
        volume (conditionalBody G pins (fun _ => 0))) := by
      apply mul_le_mul' hvolS
      rw [show productSlice K 0 = _ from central_gradientBody G pins W r]
      exact volume_collapsed_body_le G pins W r D hwp hr hd
    _ = _ := by ring

end ExtremalEdges

end
end

end OAI
