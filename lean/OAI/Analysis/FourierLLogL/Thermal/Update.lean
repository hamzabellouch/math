import OAI.Analysis.FourierLLogL.Thermal.Stretch
import OAI.Analysis.FourierLLogL.Thermal.Flat

/-! # Update records and validity -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Thermal
open Law Node Real Period Compress.Params

variable {M l j : ℕ}
open scoped Classical

/-- Data determining an update. -/
structure Update (j M : ℕ) (p : Node) where
  ix : ℕ
  V : Law (Grid (snapGrid j p M))
  x : Grid (snapGrid j p M)
  v : Grid (snapGrid j p M) → Grid M → ℂ
  scale : ℝ
  credit : ℝ
  regular : Bool

variable {p : Node}

namespace Update
def adjust (u : Update j M p) : Form M := averageCost (snap_le _ _) u.V u.x
def changeForm (u : Update j M p) : Form M :=
    u.scale • u.adjust
def next (u : Update j M p) (A : Form M) : Form M := A+place p M+u.changeForm
def app (u : Update j M p) (y z : Grid M) : ℂ :=
    ply (snap_le _ _) u.V (fun i => u.v i z) y

/-- At a regular attempt membership uses the *specified* old-channel conditional mean,
never a sample. -/
def tiltMean (u : Update j M p) (A : Form M) (y : Grid M) : ℂ :=
    (channel A y).Cx (u.app y)
def take (u : Update j M p) (A : Form M) (y : Grid M) : Prop :=
    if u.regular then beta u.ix /2 ≤ ‖u.tiltMean A y‖ else True
def chances (u : Update j M p) (P : Law (Grid M)) (A : Form M) := P.prob (u.take A)
def encoded (u : Update j M p) (C : ℝ) := kappa j (codeWeight C) u.ix
def bill (u : Update j M p) := if u.regular then u.credit else 0

structure Good (u : Update j M p) (C : ℝ) (A : Form M) (P : Law (Grid M)) : Prop where
  ix_ok : u.ix ≤ testIx j
  duration : eps * u.encoded C ≤ u.credit
  reserves : height j/H j ^2 ≤ u.credit ∧ u.credit ≤ reserve C * height j
  high : height j * H j ^200 ≤ u.scale
  unit : ∀ i z, ‖u.v i z‖ ≤ 1
  positive : 0 ≤ u.changeForm
  plate : flat (H j) (plateErr j) (A+place p M) u.changeForm
  cost : F (u.next A) - F (A+place p M) ≤ 400 * u.credit
  energy : (label (u.next A)).Ex (form u.adjust) ≤ 400 * u.credit/u.scale
  bias : beta u.ix / 2 ≤ u.chances P A
  cheap : u.regular = false → u.credit = eps * u.encoded C
  evidence : u.regular → u.credit / 4 ≤
    levelCost (snap_le _ _) (tilde (H j) A p) u.V (sLen j)
  gap_est : ∀ r : ℝ, 0 ≤ r → r ≤ sepRad j/2 → gap (u.next A) (r+stepRad C j) - gap A r ≤
    if u.regular then 402*u.credit else -(u.encoded C/2)

lemma chance_bias {u : Update j M p} {A : Form M} {P : Law (Grid M)}
    {w : Finset (Grid (snapGrid j p M))} {B : Bool}
    (hQ : supported w u.V)
    (hB : biases P p A (snap_le _ _) w B u.v (beta u.ix)) :
    beta u.ix /2 ≤ u.chances P A := by
  classical
  let T := u.tiltMean A
  have ht (x) : ‖T x‖ ≤ 1 :=
    norm_Cx_unit _ _ (fun y => ply_unit _ _ _ (fun i => hB.1 i y) _)
  have he := moments_bias _ hB u.V hQ
  change beta u.ix ≤ (P.withNext (channel A)).Ex (fun i => if i.1 ∈ (p.child B).block M then (u.app i.1 i.2).re else 0) at he
  rw [conditional_if_ex P (channel A) (fun x => x∈(child p B).block M) (fun x z => (u.app x z).re)] at he
  let b := beta u.ix
  have hU : b ≤ P.Ex (fun x => ‖T x‖) := by
    apply he.trans
    refine Ex_mono _ fun x => ?_
    split_ifs
    · rw [← re_Cx (channel A x) (u.app x)]
      exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
    · positivity
  unfold chances prob
  have hs := P.Ex_mono (f:=fun x => ‖T x‖)
    (g:=fun x => (if u.take A x then 1 else 0)+b/2) (fun x => by
      by_cases H : u.take A x
      · rw [ite_eq_left H]; have hi : 0 ≤ b := (beta_pos _).le
        linarith [ht x]
      · rw [ite_eq_right H,zero_add]
        by_contra! he
        apply H
        unfold take; split
        · exact he.le
        trivial)
  rw [Ex_add,Ex_const] at hs
  change b/2 ≤ _
  linarith

end Update

lemma paid_tighten (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ j : ℕ in atTop, ∀ M : ℕ, ∀ p : Node, ∀ A : Form M, Press C j p A →
        F (tilde (H j) A p)-F (A+place p M) ≤ height j/H j^4 := by
  filter_upwards [stiff_budget C hC] with j hh M p A H1
  obtain ⟨hq,n,q,hp,hG,hN,hF⟩ := H1
  have hp' := H_ge j
  have hd := d_pos j
  have ht : 0 ≤ plateErr j := by unfold plateErr; apply div_nonneg hd.le; exact pow_nonneg (H_pos j).le _
  apply (tilde_tight hG hp' hq).trans
  apply le_trans _ hh; gcongr

lemma make_update (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ j : ℕ in atTop, ∀ M : ℕ, ∀ A : Form M, ∀ p : Node,
      p.lev < M → Press C j p A →
      ∀ (a : Grid M → ℝ), 0 ≤ a → (∀ x, a x ≤ exp (height j)) → exp (-height j) ≤ p.avg a →
      ∀ (P : Law (Grid M)) (α : ℝ), PieceLaw p a P → 0 < α → p.avg a ≤ 2*α →
      ∀ i : ℕ, i ≤ testIx j →
        request A j p a α (side i) (kappa j (codeWeight C) i) →
        ∃ u : Update j M p, u.ix = i ∧ u.Good C A P := by
  filter_upwards [obtain_compressed C hC, flat_selection (reserve C) (reserve_ge hC),
    paid_tighten C hC,kappa_scales (codeWeight C) (code_ge hC),step_gap C hC]
    with j hC' hflat hT hL h
  intro M A p hp H' a ha he hm P α hP hα hm' i hi hI
  obtain ⟨w,x,B,v,V,t,h0,h1,h2,h3,h4,h5,h6,h7,h8⟩ :=
    hC' M A p hp H' a ha he hm P α hP hα hm' i hi hI
  let d := height j
  let L := long j
  let k := kappa j (codeWeight C) i
  let hZ := H j
  let E := averageCost (snap_le (M:=M) j p) V x
  let S := place p M
  let R := A+S
  let Q := tilde hZ A p
  have Hq : p.ok M := H'.fits
  have HH : 0 ≤ A := by obtain ⟨_,_,_,h,_⟩ := H'.cap; exact h.nonneg
  have HE : 0 ≤ E := averageCost_pos _ _ _
  have Hh : 1 ≤ hZ := H_ge _
  have Hp : 0 < hZ := H_pos _
  have HQ : R ≤ Q := tilde_le Hh HH p
  have hd : 0 < d := d_pos j
  have ht : d/hZ^2 ≤ t := (hL i hi).1.trans h0
  have htp : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hi : F (R+L • E)- F R ≤ 400*t := by
    have hh := F_mono (add_le_add_left HQ (L • E))
    have hi : F Q-F R ≤ d/hZ^4 := hT _ p A H'
    change F (Q+L • E)-F Q ≤ 350*t at h7
    have hE : d/hZ^4 ≤ d/hZ^2 := by gcongr; norm_num
    linarith
  obtain ⟨c,hc,hc',hb,hb',hb''⟩ := hflat M R E
    (add_nonneg HH (place_valid _ _)) HE t h1 hi
  let D := c • E; let N := R+D
  have HC : 0 < c := lt_of_lt_of_le (mul_pos hd (by positivity)) hc
  have HD : 0 ≤ D := smul_nonneg HC.le HE
  have Hstep (r : ℝ) (hr : 0 ≤ r) (hr' : r ≤ sepRad j/2) :
      gap N (r+stepRad C j) - gap A r ≤ 402*t ∧
        (evenly w V → t=eps*k → gap N (r+stepRad C j)-gap A r ≤ -(k/2)) := by
    obtain ⟨H1,H2⟩ := h M _ (snap_le _ _) p Hq A N HH (le_add_of_nonneg_right HD)
        x V c t r ht h1 hc hb'' hb' hr hr'
    exact ⟨H1,fun hh ht => H2 w k h2 h4 hh h6 ht⟩
  rcases h8 with ⟨Hc,Hv⟩ | HR
  · let u : Update j M p := ⟨i,V,x,v,c,t,false⟩
    refine ⟨u,rfl,?_⟩
    refine ⟨?_,h0,⟨ht,h1⟩,hc,h5.1,HD,hb,hb',hb'',u.chance_bias h3 h5,fun _ => Hc,?_,?_⟩
    · change i ≤ _
      assumption
    · simp [u]
    intro r hr hr'
    exact (Hstep r hr hr').2 Hv Hc
  let u : Update j M p := ⟨i,V,x,v,c,t,true⟩
  refine ⟨u,rfl,?_⟩
  refine ⟨?_,h0,⟨ht,h1⟩,hc,h5.1,HD,hb,hb',hb'',u.chance_bias h3 h5,?_,fun _ => HR,?_⟩
  · change i ≤ _
    assumption
  · simp [u]
  intro r hr hr'; exact (Hstep r hr hr').1

end FourierLLogL.Dyadic.Thermal

end OAI
