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
import OAI.Probability.LatticeSurface.Geometry.CapMatching
import OAI.Probability.LatticeSurface.Geometry.CapOrient
import OAI.Probability.LatticeSurface.Geometry.CapReflection
import OAI.Probability.LatticeSurface.Geometry.CapSmall
import OAI.Probability.LatticeSurface.Geometry.CapSplit
import OAI.Probability.LatticeSurface.Geometry.CapUnpin
import OAI.Probability.LatticeSurface.Geometry.CapWeld
import OAI.Probability.LatticeSurface.Moments.ControlledGradients

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

end ExtremalEdges

noncomputable section

namespace ExtremalEdges

open Finset

variable {V I : Type*} [Fintype V] [Fintype I]

attribute [local instance] Classical.propDecidable

local instance gradientWindowsFiniteDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

local instance gradientWindowsIndexDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

variable {V I : Type*} [Fintype V] [Fintype I]

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

theorem star_window_volume (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (pins : Set V) (hp : pins.Nonempty)
    (W : Finset V) (r : V → V) (D : ℕ)
    (hwp : ∀ w ∈ W, w ∉ pins) (hr : ∀ w ∈ W, r w ∉ W)
    (hd : ∀ w ∈ W, G.degree w ≤ D)
    (S : W → Set ℝ) (hS : ∀ w, MeasurableSet (S w)) :
    volume {h : Free pins → ℝ | h ∈ conditionalBody G pins (fun _ => 0) ∧
      ∀ w : W, restore pins (fun _ => 0) h w-restore pins (fun _ => 0) h (r w) ∈ S w} ≤
      (∏ w : W, volume (S w)) * (2^D)^W.card *
        volume (conditionalBody G pins (fun _ => 0)) := by
  let T := Set.pi Set.univ S
  have hT : MeasurableSet T := MeasurableSet.pi (Set.to_countable _) (fun w _ => hS w)
  let K := gradientBody G pins W r
  have hk : IsCompact K := compact_gradientBody G hc pins hp W hwp r
  have hb := product_small_set_bound hk (convex_gradientBody G pins W r)
    (fun _ h => neg_gradientBody G pins W r h) T hT
  have hsub : {h : Free pins → ℝ | h ∈ conditionalBody G pins (fun _ => 0) ∧
      ∀ w : W, restore pins (fun _ => 0) h w-restore pins (fun _ => 0) h (r w) ∈ S w} ⊆
        (gradientCoords pins W hwp r) ⁻¹' (K ∩ Prod.snd ⁻¹' T) := by
    intro h hh
    constructor
    · change (gradientCoords pins W hwp r) h ∈ gradientBody G pins W r
      rw [gradientBody_preimage G pins W hwp r]
      simpa using hh.1
    · intro w hw
      rw [gradientCoords_difference pins W hwp r hr h w]
      exact hh.2 w
  calc
    _ ≤ volume ((gradientCoords pins W hwp r) ⁻¹' (K ∩ Prod.snd ⁻¹' T)) := measure_mono hsub
    _ = volume (K ∩ Prod.snd ⁻¹' T) := (preserving_gradientCoords pins W hwp r).measure_preimage
      (hk.measurableSet.inter (hT.preimage measurable_snd)).nullMeasurableSet
    _ ≤ volume T * volume (productSlice K 0) := hb
    _ ≤ (∏ w : W, volume (S w)) * ((2^D)^W.card *
        volume (conditionalBody G pins (fun _ => 0))) := by
      rw [show volume T = _ from volume_pi_pi S, show productSlice K 0 = _ from central_gradientBody G pins W r]
      exact mul_le_mul' le_rfl (volume_collapsed_body_le G pins W r D hwp hr hd)
    _ = _ := by ring

lemma star_near_zero_volume (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (pins : Set V) (hp : pins.Nonempty)
    (W : Finset V) (r : V → V) (D : ℕ)
    (hwp : ∀ w ∈ W, w ∉ pins) (hr : ∀ w ∈ W, r w ∉ W)
    (hd : ∀ w ∈ W, G.degree w ≤ D) (u : ℝ) (_hu : 0 ≤ u) :
    volume {h : Free pins → ℝ | h ∈ conditionalBody G pins (fun _ => 0) ∧
      ∀ w ∈ W, |restore pins (fun _ => 0) h w-restore pins (fun _ => 0) h (r w)| ≤ u} ≤
      (ENNReal.ofReal (2*u))^W.card * (2^D)^W.card *
        volume (conditionalBody G pins (fun _ => 0)) := by
  have hh := star_window_volume G hc pins hp W r D hwp hr hd
    (fun _ => Set.Icc (-u) u) (fun _ => measurableSet_Icc)
  simpa only [Set.mem_Icc, ← abs_le, Subtype.forall, Real.volume_Icc,
    sub_neg_eq_add, show u+u=2*u by ring, Finset.prod_const, Finset.card_univ,
    Fintype.card_coe] using hh

def nearZero {j : ℕ} (G : SimpleGraph V) (pins : Set V)
    (e : Fin j → V × V) (u : ℝ) : Set (Free pins → ℝ) :=
  body G pins ∩ {h | ∀ i, |height pins h (e i).1-height pins h (e i).2| ≤ u}

theorem near_zero_gradients (D : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (_hc : G.Connected) (_hd : ∀ x, G.degree x ≤ D)
      (pins : Set V) (_hp : pins.Nonempty) (j : ℕ) (e : Fin j → V × V)
      (_he : ∀ i, G.Adj (e i).1 (e i).2)
      (_hi : ∀ i k, i ≠ k → e i ≠ e k ∧ e i ≠ ((e k).2, (e k).1))
      (_hfree : ∀ i, ¬ ((e i).1 ∈ pins ∧ (e i).2 ∈ pins))
      (u : ℝ), 0 < u →
      (volume (nearZero G pins e u)).toReal / (volume (body G pins)).toReal ≤
        (C*u) ^ ((j : ℝ)/C) := by
  let C : ℝ := 2^(D+1)+4*D+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hCD : (4*D : ℝ) ≤ C := by dsimp [C]; linarith [pow_pos (by norm_num : (0:ℝ) < 2) (D+1)]
  have hCB : (2:ℝ)^(D+1) ≤ C := by dsimp [C]; linarith [Nat.cast_nonneg (α := ℝ) D]
  refine ⟨C,hC,?_⟩
  intro V _ G _ hc hd pins hp j e he hi hfree u hu
  classical
  have hBfin : volume (body G pins) ≠ ⊤ := (compact_zeroBody G hc pins hp).measure_ne_top
  have hBpos : 0 < (volume (body G pins)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (volume_zeroBody_pos G pins)) hBfin
  have hcaple : volume (nearZero G pins e u) ≤ volume (body G pins) := measure_mono Set.inter_subset_left
  have hratio : (volume (nearZero G pins e u)).toReal / (volume (body G pins)).toReal ≤ 1 := by
    apply (div_le_iff₀ hBpos).mpr
    simpa using ENNReal.toReal_mono hBfin hcaple
  by_cases hlarge : 1 ≤ C*u
  · exact hratio.trans (Real.one_le_rpow hlarge (div_nonneg (Nat.cast_nonneg j) hC.le))
  have hCu : C*u < 1 := lt_of_not_ge hlarge
  have hCup : 0 < C*u := mul_pos hC hu
  have hei : Function.Injective e := by
    intro i k hik
    by_contra hh
    exact (hi i k hh).1 hik
  obtain ⟨M,hM,hsize⟩ := large_matching G D hd e he hei
  obtain ⟨W,r,hcard,hwp,hr,hwr⟩ := orient_matching e pins (fun i => (he i).ne) hfree M hM
  have her : ∀ w ∈ W, G.Adj w (r w) := by
    intro w hw
    obtain ⟨i,_,hh | hh⟩ := hwr w hw
    · rw [hh.2,hh.1]; exact he i
    · rw [hh.2,hh.1]; exact (he i).symm
  have hsub : nearZero G pins e u ⊆ {h : Free pins → ℝ |
      h ∈ conditionalBody G pins (fun _ => 0) ∧ ∀ w ∈ W,
        |restore pins (fun _ => 0) h w-restore pins (fun _ => 0) h (r w)| ≤ u} := by
    intro h hh
    refine ⟨hh.1,?_⟩
    intro w hw
    obtain ⟨i,_,ht | ht⟩ := hwr w hw
    · rw [ht.2,ht.1]
      simpa only [height_restore] using hh.2 i
    · rw [ht.2,ht.1]
      simpa only [height_restore,abs_sub_comm] using hh.2 i
  have hvol := (measure_mono hsub).trans
    (star_near_zero_volume G hc pins hp W r D hwp hr (fun w _ => hd w) u hu.le)
  have hfinite : (ENNReal.ofReal (2*u))^W.card*(2^D)^W.card*
      volume (conditionalBody G pins (fun _ => 0)) ≠ ⊤ := by finiteness
  have hreal := ENNReal.toReal_mono hfinite hvol
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (show 0 ≤ 2*u by positivity), ENNReal.toReal_ofNat] at hreal
  have hpown : (volume (nearZero G pins e u)).toReal / (volume (body G pins)).toReal ≤
      ((2:ℝ)^(D+1)*u)^W.card := by
    apply (div_le_iff₀ hBpos).mpr
    have hcst : (2*u)^W.card*((2:ℝ)^D)^W.card = ((2:ℝ)^(D+1)*u)^W.card := by
      rw [← mul_pow]
      congr 1
      rw [pow_succ]
      ring
    simpa only [hcst,body_conditional] using hreal
  have hsz : (j : ℝ) ≤ (W.card : ℝ)*(4*D) := by
    rw [hcard]
    have hszn : j ≤ M.card*(4*D) := by simpa using hsize
    exact_mod_cast hszn
  have hexp : (j : ℝ)/C ≤ W.card := by
    apply (div_le_iff₀ hC).mpr
    exact hsz.trans (mul_le_mul_of_nonneg_left hCD (Nat.cast_nonneg _))
  calc
    (volume (nearZero G pins e u)).toReal / (volume (body G pins)).toReal ≤
        ((2:ℝ)^(D+1)*u)^W.card := hpown
    _ ≤ (C*u)^W.card := pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hCB hu.le) _
    _ = (C*u)^(W.card : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (C*u)^((j:ℝ)/C) := Real.rpow_le_rpow_of_exponent_ge hCup hCu.le hexp

end ExtremalEdges

end
end
end

end OAI
