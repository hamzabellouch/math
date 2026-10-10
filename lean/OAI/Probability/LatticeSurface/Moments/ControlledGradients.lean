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

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace ExtremalEdges

open Finset

variable {V I : Type*} [Fintype V] [Fintype I]

attribute [local instance] Classical.propDecidable

local instance controlledGradientsMatchingDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

local instance controlledGradientsCapDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

variable {V I : Type*} [Fintype V] [Fintype I]

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

def height {V : Type*} (pins : Set V) (h : Free pins → ℝ) (x : V) : ℝ :=
  if hx : x ∈ pins then 0 else h ⟨x, hx⟩

def body {V : Type*} (G : SimpleGraph V) (pins : Set V) : Set (Free pins → ℝ) :=
  {h | ∀ x y, G.Adj x y → |height pins h x - height pins h y| ≤ 1}

def cap {V : Type*} {j : ℕ} (G : SimpleGraph V) (pins : Set V)
    (e : Fin j → V × V) (u : ℝ) : Set (Free pins → ℝ) :=
  body G pins ∩ {h | ∀ i, 1-u ≤ |height pins h (e i).1 - height pins h (e i).2|}

lemma height_restore {V : Type*} (pins : Set V) (h : Free pins → ℝ) (x : V) :
    height pins h x = restore pins (fun _ => 0) h x := rfl

lemma body_conditional {V : Type*} (G : SimpleGraph V) (pins : Set V) :
    body G pins = conditionalBody G pins (fun _ => 0) := rfl

theorem controlled_gradients (D : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (_hc : G.Connected) (_hd : ∀ x, G.degree x ≤ D)
      (pins : Set V) (_hp : pins.Nonempty) (j : ℕ) (e : Fin j → V × V)
      (_he : ∀ i, G.Adj (e i).1 (e i).2)
      (_hi : ∀ i k, i ≠ k → e i ≠ e k ∧ e i ≠ ((e k).2, (e k).1))
      (u : ℝ), 0 < u → u ≤ 1/8 →
      (volume (cap G pins e u)).toReal / (volume (body G pins)).toReal ≤
        (C*u) ^ ((j : ℝ)/C) := by
  let C : ℝ := 2^(D+1)+4*D+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hCD : (4*D : ℝ) ≤ C := by dsimp [C]; linarith [pow_pos (by norm_num : (0:ℝ) < 2) (D+1)]
  have hCB : (2:ℝ)^(D+1) ≤ C := by dsimp [C]; linarith [Nat.cast_nonneg (α := ℝ) D]
  refine ⟨C,hC,?_⟩
  intro V _ G _ hc hd pins hp j e he hi u hu hu8
  classical
  have hBfin : volume (body G pins) ≠ ⊤ := (compact_zeroBody G hc pins hp).measure_ne_top
  have hBpos : 0 < (volume (body G pins)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (volume_zeroBody_pos G pins)) hBfin
  have hcaple : volume (cap G pins e u) ≤ volume (body G pins) := measure_mono Set.inter_subset_left
  have hratio : (volume (cap G pins e u)).toReal / (volume (body G pins)).toReal ≤ 1 := by
    apply (div_le_iff₀ hBpos).mpr
    simpa using ENNReal.toReal_mono hBfin hcaple
  by_cases hlarge : 1 ≤ C*u
  · exact hratio.trans (Real.one_le_rpow hlarge (div_nonneg (Nat.cast_nonneg j) hC.le))
  have hCu : C*u < 1 := lt_of_not_ge hlarge
  have hCup : 0 < C*u := mul_pos hC hu
  by_cases hfree : ∀ i, ¬ ((e i).1 ∈ pins ∧ (e i).2 ∈ pins)
  · have hei : Function.Injective e := by
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
    have hsub : cap G pins e u ⊆ {h : Free pins → ℝ |
        h ∈ conditionalBody G pins (fun _ => 0) ∧ ∀ w ∈ W,
          1-u ≤ |restore pins (fun _ => 0) h w-restore pins (fun _ => 0) h (r w)|} := by
      intro h hh
      refine ⟨hh.1,?_⟩
      intro w hw
      obtain ⟨i,_,ht | ht⟩ := hwr w hw
      · rw [ht.2,ht.1]
        simpa only [height_restore] using hh.2 i
      · rw [ht.2,ht.1]
        simpa only [height_restore,abs_sub_comm] using hh.2 i
    have hvol := (measure_mono hsub).trans
      (star_cap_volume G hc pins hp W r D hwp hr (fun w _ => hd w) her u hu.le)
    have hfinite : (ENNReal.ofReal (2*u))^W.card*(2^D)^W.card*
        volume (conditionalBody G pins (fun _ => 0)) ≠ ⊤ := by finiteness
    have hreal := ENNReal.toReal_mono hfinite hvol
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (show 0 ≤ 2*u by positivity), ENNReal.toReal_ofNat] at hreal
    have hpown : (volume (cap G pins e u)).toReal / (volume (body G pins)).toReal ≤
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
      (volume (cap G pins e u)).toReal / (volume (body G pins)).toReal ≤
          ((2:ℝ)^(D+1)*u)^W.card := hpown
      _ ≤ (C*u)^W.card := pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hCB hu.le) _
      _ = (C*u)^(W.card : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (C*u)^((j:ℝ)/C) := Real.rpow_le_rpow_of_exponent_ge hCup hCu.le hexp
  · push Not at hfree
    obtain ⟨i,hip,hjp⟩ := hfree
    have hempty : cap G pins e u = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro h hh
      have ht := hh.2 i
      simp only [height, dite_eq_left hip, dite_eq_left hjp, sub_self, abs_zero] at ht
      linarith
    rw [hempty,measure_empty,ENNReal.toReal_zero,zero_div]
    exact Real.rpow_nonneg hCup.le _

end ExtremalEdges

end

end OAI
