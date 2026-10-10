import Mathlib
import OAI.Combinatorics.UniformKServer.Epochs
import OAI.Combinatorics.UniformKServer.DomainTransport
import OAI.Combinatorics.UniformKServer.SideParameters
import OAI.Combinatorics.UniformKServer.SideStability

namespace OAI

                                   
section

/-! Actual side-domain update with the exact held height/offset parameters.
 The source leaves fixed absolute constants flexible; W=11, C'=28 apply in
 the eventual b≤4, θ≤1 parameter interval. Empty side domains are included. -/
noncomputable section
namespace UniformKServer.AdaptiveSide
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

structure Config (ι : Type*) where
  active : Finset ι
  A : ℝ
  a : active → ℝ
  ell : ℝ
  cw : ℝ
  b : ℝ

def theta (p : Config ι) : ι → ℝ := DomainTransport.extend p.active
  (fun i => SideParameters.slack p.ell p.cw p.A (p.a i))
def offset (p : Config ι) : ι → ℝ := DomainTransport.extend p.active
  (fun i => SideParameters.offset p.A (p.a i))

def valid (p : Config ι) : Prop := 1 ≤ p.ell ∧ 0 < p.cw ∧ 0 < p.b ∧ p.b ≤ 4 ∧
  (∀ i, 0 < p.a i ∧ p.a i ≤ p.A) ∧
  (∀ i, SideParameters.slack p.ell p.cw p.A (p.a i) ≤ 1)

def potential (p : Config ι) (B : ι → ℝ) (D : ℝ) (w : ι → ℝ) : ℝ :=
  SideTracker.potential p.b 28 D (theta p) (offset p) B w

def slope (p : Config ι) : ℝ := 2000*(p.ell/p.cw+1)

omit [Fintype ι] in
theorem theta_pos {p : Config ι} (hp : valid p) (i : p.active) : 0 < theta p i := by
  rw [theta,DomainTransport.extend_apply]
  exact SideParameters.slack_pos (by linarith [hp.1]) hp.2.1
    (hp.2.2.2.2.1 i).1 (hp.2.2.2.2.1 i).2

omit [Fintype ι] in
theorem offset_pos {p : Config ι} (hp : valid p) (i : p.active) : 0 < offset p i := by
  rw [offset,DomainTransport.extend_apply]
  exact SideParameters.offset_pos (hp.2.2.2.2.1 i).1 (hp.2.2.2.2.1 i).2

omit [Fintype ι] in
theorem theta_le {p : Config ι} (hp : valid p) (i : p.active) : theta p i ≤ 1 := by
  rw [theta,DomainTransport.extend_apply]
  exact hp.2.2.2.2.2 i

omit [Fintype ι] in
theorem slope_nonneg {p : Config ι} (hp : valid p) : 0 ≤ slope p := by
  have hq : 0 ≤ p.ell/p.cw := div_nonneg (by linarith [hp.1]) hp.2.1.le
  unfold slope
  positivity

theorem coordinate_zero (b θ z B D : ℝ) : SideTracker.coordinate b θ z 28 B D 0=0 := by
  simp [SideTracker.coordinate]

theorem restrict_potential {p : Config ι} (B w : ι → ℝ) (D : ℝ)
    (hw : DomainTransport.Supported p.active w) :
    potential p B D w = SideTracker.potential p.b 28 D (fun i : p.active => theta p i)
      (fun i => offset p i) (fun i => B i) (fun i => w i) := by
  exact (DomainTransport.potential_restrict
    (fun i => SideTracker.coordinate p.b (theta p i) (offset p i) 28 (B i) D)
    hw (fun _ _ => coordinate_zero ..)).symm

theorem restrict_domain {I : Finset ι} {w : ι → ℝ}
    (hw : DomainTransport.domain I 11 w) : SideTracker.domain 11 (fun i : I => w i) := by
  refine ⟨fun i => hw.1 i,?_⟩
  rw [DomainTransport.sum_restrict hw.2.1]
  exact hw.2.2

theorem extend_domain {I : Finset ι} {w : I → ℝ} (hw : SideTracker.domain 11 w) :
    DomainTransport.domain I 11 (DomainTransport.extend I w) := by
  refine ⟨?_,DomainTransport.extend_supported I w,?_⟩
  · intro i
    unfold DomainTransport.extend
    split_ifs with hi
    · exact hw.1 ⟨i,hi⟩
    · rfl
  · rw [DomainTransport.extend_sum]
    exact hw.2

theorem update {p : Config ι} (hp : valid p) (B w₀ : ι → ℝ) (D S : ℝ)
    (hD : 0 ≤ D) (hB : ∀ i, 0 ≤ B i) (hs : DomainTransport.Supported p.active B)
    (hS : (∑ i, B i) ≤ S) (hw₀ : DomainTransport.domain p.active 11 w₀) :
    ∃ w, DomainTransport.domain p.active 11 w ∧
      (∀ i, D*w i ≤ (p.b+theta p i)*B i) ∧
      (S ≤ 2*D → ∀ i, p.b*B i-theta p i*offset p i*D ≤ D*w i) ∧
      D*SideTracker.movement w w₀ ≤ potential p B D w₀-potential p B D w := by
  obtain ⟨w,hw,hf,hl,hm⟩ := SideTracker.side_update p.b 28 D 11 5 S
    (fun i : p.active => theta p i) (fun i => offset p i) (fun i => B i) (fun i => w₀ i)
    hp.2.2.1 hD (by norm_num) (by norm_num) (theta_pos hp) (offset_pos hp)
    (fun i => hB i) (by rw [DomainTransport.sum_restrict hs]; exact hS)
    (fun i => by linarith [hp.2.2.2.1,theta_le hp i])
    (fun i => by linarith [hp.2.2.2.1,theta_le hp i]) (restrict_domain hw₀)
  refine ⟨DomainTransport.extend p.active w,extend_domain hw,?_,?_,?_⟩
  · intro i
    by_cases hi : i ∈ p.active
    · simpa only [DomainTransport.extend,hi,dite_true] using hf ⟨i,hi⟩
    · rw [hs i hi,DomainTransport.extend_supported p.active w i hi,mul_zero,mul_zero]
  · intro hSD i
    by_cases hi : i ∈ p.active
    · simpa only [DomainTransport.extend,hi,dite_true] using hl hSD ⟨i,hi⟩
    · rw [hs i hi,DomainTransport.extend_supported p.active w i hi]
      simp [theta,DomainTransport.extend,hi]
  · rw [restrict_potential B w₀ D hw₀.2.1,
      restrict_potential B (DomainTransport.extend p.active w) D (DomainTransport.extend_supported _ _)]
    have he : (fun i : p.active => DomainTransport.extend p.active w i)=w := by
      funext i
      exact DomainTransport.extend_apply _ _ _
    rw [he]
    change D*SimplexTracker.movement (DomainTransport.extend p.active w) w₀ ≤ _
    rw [DomainTransport.movement_extend p.active w hw₀.2.1]
    exact hm

omit [Fintype ι] in
theorem parameter_bounds {p : Config ι} (hp : valid p) (i : p.active) {s : ℝ}
    (hs : 0 ≤ s) (hsW : s ≤ 11) :
    1/theta p i ≤ p.ell/p.cw ∧
      Real.log (1+s/offset p i)/theta p i ≤ 13*(p.ell/p.cw) ∧
      p.b+theta p i/2 ≤ 5 := by
  have hθ := theta_le hp i
  refine ⟨?_,?_,by linarith [hp.2.2.2.1]⟩
  · rw [theta,DomainTransport.extend_apply]
    exact SideParameters.inverse_slack (by linarith [hp.1]) hp.2.1
      (hp.2.2.2.2.1 i).1 (hp.2.2.2.2.1 i).2
  · rw [theta,offset,DomainTransport.extend_apply,DomainTransport.extend_apply]
    have h := SideParameters.logarithm_over_slack (by linarith [hp.1] : 0 < p.ell) hp.2.1
      (hp.2.2.2.2.1 i).1 (hp.2.2.2.2.1 i).2 hs hsW
    norm_num at h
    simpa only [mul_div_assoc] using h

omit [Fintype ι] in
theorem coordinate_bound {p : Config ι} (hp : valid p) (i : p.active) {w B D : ℝ}
    (hw : 0 ≤ w) (hwW : w ≤ 11) :
    |SideTracker.coordinate p.b (theta p i) (offset p i) 28 B D w| ≤
      slope p*(|D| *w+|B|) := by
  obtain ⟨hT,hJ,hQ⟩ := parameter_bounds hp i hw hwW
  have h := SideStability.coordinate_bound hp.2.2.1.le (theta_pos hp i) (offset_pos hp i)
    hw hT hJ hQ 28 B D
  rw [abs_of_pos (by norm_num : (0:ℝ)<28)] at h
  refine h.trans ?_
  have hq : 0 ≤ p.ell/p.cw := div_nonneg (by linarith [hp.1]) hp.2.1.le
  have hD := abs_nonneg D
  have hB := abs_nonneg B
  have hDw := mul_nonneg hD hw
  unfold slope
  nlinarith

theorem coordinate_le_sum {I : Finset ι} {w : ι → ℝ}
    (hw : DomainTransport.domain I 11 w) (i : ι) : w i ≤ 11 :=
  (single_le_sum (s:=univ) (f:=w) (fun j _ => hw.1 j) (mem_univ i)).trans hw.2.2

theorem input_bound {p : Config ι} (hp : valid p) (B B' w : ι → ℝ) (D D' : ℝ)
    (hw : DomainTransport.domain p.active 11 w) :
    |potential p B D w-potential p B' D' w| ≤
      slope p*((∑ i, |B i-B' i|)+|D-D'|) := by
  rw [restrict_potential B w D hw.2.1,restrict_potential B' w D' hw.2.1]
  have hq : 0 ≤ p.ell/p.cw := div_nonneg (by linarith [hp.1]) hp.2.1.le
  have hb (i : p.active) := parameter_bounds hp i (hw.1 i) (coordinate_le_sum hw i)
  have h := SideStability.input_bound p.b 28 D D' (p.ell/p.cw) (13*(p.ell/p.cw)) 5 11
    (fun i : p.active => theta p i) (fun i => offset p i) (fun i => B i)
    (fun i => B' i) (fun i => w i) hp.2.2.1.le (theta_pos hp) (offset_pos hp)
    (restrict_domain hw) (fun i => (hb i).1) (fun i => (hb i).2.1)
    (fun i => (hb i).2.2) (by linarith)
  rw [abs_of_pos (by norm_num : (0:ℝ)<28)] at h
  have hsum : (∑ i : p.active, |B i-B' i|) ≤ ∑ i, |B i-B' i| := by
    rw [sum_coe_sort p.active (fun i : ι => |B i-B' i|)]
    exact sum_le_univ_sum_of_nonneg (fun i => abs_nonneg (B i-B' i))
  have hn : 0 ≤ ∑ i, |B i-B' i| := sum_nonneg fun _ _ => abs_nonneg _
  have hd := abs_nonneg (D-D')
  refine h.trans ?_
  unfold slope
  nlinarith [mul_le_mul_of_nonneg_left hsum hq, mul_nonneg hq hn, mul_nonneg hq hd]

omit [Fintype ι] in
theorem theta_nonneg {p : Config ι} (hp : valid p) (i : ι) : 0 ≤ theta p i := by
  by_cases hi : i ∈ p.active
  · exact (theta_pos hp ⟨i,hi⟩).le
  · rw [theta,DomainTransport.extend_supported _ _ i hi]

theorem prepare {p q : Config ι} (hp : valid p) (B w₀ : ι → ℝ) (D : ℝ)
    (hD : 0 ≤ D) (hB : ∀ i, 0 ≤ B i)
    (hpB : DomainTransport.Supported p.active B) (hqB : DomainTransport.Supported q.active B)
    (hw₀ : DomainTransport.domain p.active 11 w₀) :
    ∃ w b, DomainTransport.domain p.active 11 w ∧ DomainTransport.domain q.active 11 b ∧
      (∀ i, D*b i ≤ (p.b+theta p i)*B i) ∧
      D*SideTracker.movement w w₀ ≤ potential p B D w₀-potential p B D w ∧
      D*SideTracker.movement b w=0 ∧ potential p B D b=potential p B D w := by
  obtain ⟨w,hw,hf,_,hm⟩ := update hp B w₀ D (∑ i, B i) hD hB hpB le_rfl hw₀
  obtain ⟨hb,hfree,he⟩ := DomainTransport.prepared_side hw hD hqB
    (fun i _ => hf i)
  refine ⟨w,DomainTransport.delete q.active w,hw,hb,?_,hm,hfree,he⟩
  intro i
  unfold DomainTransport.delete
  split_ifs with hi
  · exact hf i
  · rw [hqB i hi,mul_zero,mul_zero]

theorem triangle (a b c : ι → ℝ) :
    SideTracker.movement a c ≤ SideTracker.movement a b+SideTracker.movement b c := by
  unfold SideTracker.movement
  rw [←sum_add_distrib]
  exact sum_le_sum fun i _ => abs_sub_le (a i) (b i) (c i)

/-- Actual two-minimizer nonswitch operation. Parameter change is left as the
 exact prepared difference for the following size-charge lemma, not an assumed
 movement estimate. Both minimizations use the new nonnegative D. -/
theorem step {p q : Config ι} (hp : valid p) (hq : valid q)
    (Bstar Bnew w₀ : ι → ℝ) (D S : ℝ) (hD : 0 ≤ D)
    (hB : ∀ i, 0 ≤ Bstar i) (hBn : ∀ i, 0 ≤ Bnew i)
    (hS : (∑ i, Bnew i) ≤ S)
    (hpB : DomainTransport.Supported p.active Bstar)
    (hqB : DomainTransport.Supported q.active Bstar)
    (hqN : DomainTransport.Supported q.active Bnew)
    (hw₀ : DomainTransport.domain p.active 11 w₀) :
    ∃ w b, DomainTransport.domain q.active 11 w ∧ DomainTransport.domain q.active 11 b ∧
      (∀ i, D*w i ≤ (q.b+theta q i)*Bnew i) ∧
      (S ≤ 2*D → ∀ i, q.b*Bnew i-theta q i*offset q i*D ≤ D*w i) ∧
      (∀ i, D*b i ≤ (p.b+theta p i)*Bstar i) ∧
      D*SideTracker.movement w w₀ ≤ potential p Bstar D w₀-potential q Bnew D w+
        (potential q Bstar D b-potential p Bstar D b)+slope q*(∑ i, |Bnew i-Bstar i|) := by
  obtain ⟨w₁,b,hw₁,hb,hf,hm,hfree,he⟩ := prepare hp Bstar w₀ D hD hB hpB hqB hw₀
  obtain ⟨w,hw,hu,hl,hmn⟩ := update hq Bnew b D S hD hBn hqN hS hb
  refine ⟨w,b,hw,hb,hu,hl,hf,?_⟩
  have ht := mul_le_mul_of_nonneg_left (triangle w b w₀) hD
  have hp' := mul_le_mul_of_nonneg_left (triangle b w₁ w₀) hD
  rw [mul_add,hfree,zero_add] at hp'
  have hi := input_bound hq Bnew Bstar b D D hb
  rw [sub_self,abs_zero,add_zero] at hi
  have hi' := (le_abs_self _).trans hi
  rw [←he] at hm
  nlinarith

end UniformKServer.AdaptiveSide

end


end

end OAI
