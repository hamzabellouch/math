import Mathlib
import OAI.Analysis.HardSphere.Bridges.AffineVolume

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

def jointSegmentHit (t : ℝ) (y : Point) (s w : Time) (c : C(Time,Point)) (r C : ℝ) : Set (Point×Noise) :=
  {p | p.2∈segmentHit t y p.1 s w c r C}

lemma jointSegmentHit_closed (t : ℝ) (y : Point) (s w : Time) (c : C(Time,Point)) (r C : ℝ) :
    IsClosed (jointSegmentHit t y s w c r C) := by
  let E : Set ((Point×Noise)×Time) := {p | (p.2:ℝ)≤(w:ℝ) ∧
    ‖leg t y p.1.1 p.1.2 (suffixTime s p.2)-c p.2‖≤r}
  have hE : IsClosed E := by
    apply IsClosed.inter
    · exact isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const
    · have hn : Continuous (fun p : (Point×Noise)×Time ↦ ‖leg t y p.1.1 p.1.2 (suffixTime s p.2)-c p.2‖) := by
        change Continuous (fun p : (Point×Noise)×Time ↦ ‖(fun j ↦
          (1-(suffixTime s p.2:ℝ))*y j+(suffixTime s p.2:ℝ)*p.1.1 j+
          Real.sqrt (2*t)*p.1.2 j (suffixTime s p.2))-c p.2‖)
        apply Continuous.norm
        apply Continuous.sub
        · apply continuous_pi
          intro j
          fun_prop
        · exact c.continuous.comp continuous_snd
      exact isClosed_le hn continuous_const
  have hp := isClosedMap_fst_of_compactSpace E hE
  have hc : IsClosed {p : Point×Noise | ‖leg t y p.1 p.2 s-p.1‖≤C} := by
    apply isClosed_le _ continuous_const
    change Continuous (fun p : Point×Noise ↦ ‖(fun j ↦ (1-(s:ℝ))*y j+(s:ℝ)*p.1 j+
      Real.sqrt (2*t)*p.2 j s)-p.1‖)
    fun_prop
  convert hc.inter hp using 1
  ext p
  simp only [jointSegmentHit,segmentHit,mem_ofPred_eq,Set.mem_inter_iff,mem_image,E]
  constructor
  · rintro ⟨h,q,hq,hh⟩
    exact ⟨h,⟨(p,q),⟨hq,hh⟩,rfl⟩⟩
  · rintro ⟨h,⟨⟨p',q⟩,⟨hq,hh⟩,hp⟩⟩
    dsimp at hp
    subst p'
    exact ⟨h,q,hq,hh⟩

lemma uniformSegmentHit_measurable (t : ℝ) (y : Point) (s w : Time) (c : C(Time,Point)) (r : ℝ)
    {B : Set Point} (hB : MeasurableSet B) : MeasurableSet (uniformSegmentHit t y s w c r B) := by
  let E : Set ((Noise×Point)×Time) := {p | (p.2:ℝ)≤(w:ℝ) ∧
    ‖leg t y p.1.2 p.1.1 (suffixTime s p.2)-c p.2‖≤r}
  have hE : IsClosed E := by
    apply IsClosed.inter
    · exact isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const
    · have hn : Continuous (fun p : (Noise×Point)×Time ↦ ‖leg t y p.1.2 p.1.1 (suffixTime s p.2)-c p.2‖) := by
        change Continuous (fun p : (Noise×Point)×Time ↦ ‖(fun j ↦
          (1-(suffixTime s p.2:ℝ))*y j+(suffixTime s p.2:ℝ)*p.1.2 j+
          Real.sqrt (2*t)*p.1.1 j (suffixTime s p.2))-c p.2‖)
        apply Continuous.norm
        apply Continuous.sub
        · apply continuous_pi
          intro j
          fun_prop
        · exact c.continuous.comp continuous_snd
      exact isClosed_le hn continuous_const
  have hp := (isClosedMap_fst_of_compactSpace E hE).measurableSet
  convert (hB.preimage measurable_snd).inter hp using 1
  ext p
  simp only [uniformSegmentHit,mem_ofPred_eq,Set.mem_inter_iff,mem_image,E,mem_preimage]
  constructor
  · rintro ⟨h,q,hq,hh⟩
    exact ⟨h,⟨(p,q),⟨hq,hh⟩,rfl⟩⟩
  · rintro ⟨h,⟨⟨p',q⟩,⟨hq,hh⟩,hp⟩⟩
    dsimp at hp
    subst p'
    exact ⟨h,q,hq,hh⟩

end HardSphere.Bridge

end

noncomputable section
open Set
open scoped BigOperators
namespace HardSphere.Bridge

lemma inverse_sqrt_step {x h : ℝ} (hx : 0<x) (hh : 0<h) :
    h / ((x+h)*Real.sqrt (x+h)) ≤ 2*(1/Real.sqrt x-1/Real.sqrt (x+h)) := by
  have hX := Real.sqrt_pos.2 hx
  have hY := Real.sqrt_pos.2 (add_pos hx hh)
  have hXY := Real.sqrt_le_sqrt (le_add_of_nonneg_right hh.le : x≤x+h)
  have hxx := Real.sq_sqrt hx.le
  have hyy := Real.sq_sqrt (add_pos hx hh).le
  apply (div_le_iff₀ (mul_pos (add_pos hx hh) hY)).mpr
  field_simp
  have he : 2*(x+h)*(Real.sqrt (x+h)-Real.sqrt x)-h*Real.sqrt x=
      (Real.sqrt (x+h)-Real.sqrt x)^2*(2*Real.sqrt (x+h)+Real.sqrt x) := by
    calc
      _ = 2*(Real.sqrt (x+h))^2*(Real.sqrt (x+h)-Real.sqrt x)-
        ((Real.sqrt (x+h))^2-(Real.sqrt x)^2)*Real.sqrt x := by rw [hxx,hyy]; ring
      _ = _ := by ring
  have hp : 0 ≤ (Real.sqrt (x+h)-Real.sqrt x)^2*(2*Real.sqrt (x+h)+Real.sqrt x) := by positivity
  linarith

lemma singular_sum (n : ℕ) {x h : ℝ} (hx : 0<x) (hh : 0<h) :
    (∑k∈Finset.range n, h/((x+(k+1)*h)*Real.sqrt (x+(k+1)*h))) ≤
      2*(1/Real.sqrt x-1/Real.sqrt (x+n*h)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hp : 0<x+n*h := add_pos_of_pos_of_nonneg hx (by positivity)
    have hstep := inverse_sqrt_step hp hh
    have he : x+(n:ℝ)*h+h=x+((n:ℝ)+1)*h := by ring
    rw [he] at hstep
    push_cast
    exact (add_le_add ih hstep).trans_eq (by ring)

lemma singular_sum_bound (n : ℕ) {x h : ℝ} (hx : 0<x) (hh : 0<h) :
    (∑k∈Finset.range n, 1/((x+(k+1)*h)*Real.sqrt (x+(k+1)*h))) ≤
      2/(h*Real.sqrt x) := by
  have hs := singular_sum n hx hh
  have he : (∑k∈Finset.range n,h/((x+(k+1)*h)*Real.sqrt (x+(k+1)*h)))=
      h*(∑k∈Finset.range n,1/((x+(k+1)*h)*Real.sqrt (x+(k+1)*h))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he] at hs
  have hs' : h*(∑k∈Finset.range n,1/((x+(k+1)*h)*Real.sqrt (x+(k+1)*h))) ≤ 2/Real.sqrt x := by
    apply hs.trans
    have hp : 0≤1/Real.sqrt (x+(n:ℝ)*h) := by positivity
    calc
      _ ≤ 2*(1/Real.sqrt x) := by linarith
      _ = _ := by ring
  rw [show 2/(h*Real.sqrt x)=(2/Real.sqrt x)/h by ring]
  apply (le_div_iff₀ hh).mpr
  simpa only [mul_comm] using hs'

end HardSphere.Bridge

end

end OAI
