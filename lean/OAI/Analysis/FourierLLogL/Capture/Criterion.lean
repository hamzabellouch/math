import OAI.Analysis.FourierLLogL.Capture.Mask
import OAI.Analysis.FourierLLogL.Plateau.Local

/-! # Criteria and their polarized tests -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Capture
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread

variable {M J j : ℕ} {s : Scene M}
open scoped Classical

def optic (s : Scene M) (b : Bool) := if b then s.fund.mood else 0
def energy (s : Scene M) (u : Grid M) := energyZ s.here s.wage s.norm s.fund.mood u
def scalar (s : Scene M) (u : Grid M) :=
    ∑ i : Grid M, (↑(wt s.here s.wage s.norm i):ℂ)*chi u i
def magnitude (main : Bool) (s : Scene M) (u : Grid M) :=
    if main then energy s u else ‖scalar s u‖

def strength (main : Bool) (b : ℝ) := if main then b^2 else b

def intense (main : Bool) (s : Scene M) (r : ℝ) (i : Grid M) :=
    ∃ b, strength main r ≤ magnitude main (s.smaller b) i

def amp (i : ℕ) (b : Bool) := strength b (side i)

lemma strength_bounds (b : Bool) {r : ℝ} (hr : 0 < r) (h : r ≤ 1) :
    0 < strength b r ∧ strength b r ≤ r ∧ r^2 ≤ strength b r := by
  have he : r^2 ≤ r := by nlinarith
  cases b <;> simp only [strength, Bool.false_eq_true,↓reduceIte] <;> exact ⟨by positivity,by linarith,by linarith⟩

lemma amp_pos (i : ℕ) (b : Bool) : 0 < amp i b :=
  (strength_bounds b (side_pos i) (side_le i)).1

lemma amp_hi (i : ℕ) (b : Bool) : amp i b ≤ 1 :=
    (strength_bounds b (side_pos i) (side_le i)).2.1.trans (side_le i)

lemma gate_amp (i : ℕ) (b : Bool) :
    gateWidth b i = amp i b /128 := rfl

lemma intent_main (s : Scene M) (r : ℝ) (i : Grid M) :
    intense true s r i ↔ high s.here s.wage s.norm s.fund.mood r i := by
  rfl

lemma scalar_series (s : Scene M) (A : Form M) (u : Grid M) :
    scalar s u = ∑ z, fz s.here s.wage s.norm A u z := by
  unfold fz scalar
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i hi => ?_
  unfold omegaObs; simp_rw [Complex.ofReal_mul,mul_right_comm
    ((wt s.here s.wage s.norm i):ℂ) _ (chi u i)]
  rw [← Finset.mul_sum,← Complex.ofReal_sum,(channel A i).total]; simp

lemma strong_sum (s : Scene M) (b : Bool) (x : Grid M)
    (ha : 0 ≤ s.wage) (hb : 0 < s.norm) :
    magnitude b s x ≤ ∑ z, ‖fz s.here s.wage s.norm (optic s b) x z‖ := by
  cases b
  · change ‖scalar s x‖ ≤ _
    rw [scalar_series s (optic s false)]; exact norm_sum_le _ _
  · exact energyZ_le s.here ha hb.le _ _

def tracker (s : Scene M) (main : Bool) := s.actor.withNext (channel (optic s main))

def aim {p : Node} (b : Bool) (y : Grid M) : ℝ := if y∈(child p b).block M then 1 else 0
private lemma aim_identity (s : Scene M) (b : Bool) (i : Grid M) (main : Bool)
    (v : Grid M → ℂ) (hp : s.here.valid) (hh : s.here.lev < M)
    (ha : 0 ≤ s.wage) (hb : 0 < s.norm) (hm : 0 < s.mass) :
    let q := s.smaller b
    ∑ z, (v z*fz q.here q.wage q.norm (optic q main) i z).re =
      (2*s.mass/s.norm)*(tracker s main).Ex (fun w =>
        aim (p:=s.here) b w.1*(v w.2*chi i w.1).re) := by
  classical
  intro q
  let A := optic s main
  let L := channel A; let P := s.actor
  let H := fun y : Grid M => aim (p:=s.here) b y
  let c := 2*s.mass/s.norm
  have HE (z : Grid M) :
      (v z*fz q.here q.wage q.norm (optic q main) i z).re =
        ∑ y, c * (P y * (L y z * (H y*(v z*chi i y).re))) := by
    unfold fz; rw [Finset.mul_sum,Complex.re_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    have Hi : omegaObs q.here q.wage q.norm (optic q main) y z =
        c*H y*P y*L y z := by
      unfold omegaObs
      change wt (s.here.child b) s.wage s.norm y*L y z = _
      unfold H Procedure.Capture.aim c P
      rw [actor_def ⟨hp,hh.le⟩ ha hm y,wt_half hp hh]
      split_ifs
      · unfold mass wt; unfold mass at hm; field_simp
      · simp
    rw [Hi,mul_left_comm,Complex.re_ofReal_mul]; ring
  unfold tracker; rw [Ex_withNext]; simp only [HE,← Finset.mul_sum,Ex]
  congr 1
  rw [Finset.sum_comm]
  dsimp only [c,P,H,A,L]
  simp_rw [Finset.mul_sum]

lemma criterion_bias (s : Scene M) (main : Bool) (k : ℕ) (x : Grid M)
    (hp : s.here.valid) (hh : s.here.lev < M) (ha : 0 ≤ s.wage)
    (hx : 0 < s.norm) (hm : 0 < s.mass) (he : intense main s (side k) x) :
    ∃ b : Bool, ∃ f : Grid M → ℂ, (∀ z, ‖f z‖ ≤ 1) ∧
      amp k main /2 ≤ (s.mass/s.norm)*(tracker s main).Ex (fun w =>
        aim (p:=s.here) b w.1 * (f w.2*chi x w.1).re) := by
  obtain ⟨b,hL⟩ := he
  let q := s.smaller b
  let v := fun z => fz q.here q.wage q.norm (optic q main) x z
  let f := fun z => polar (v z)
  have HH := aim_identity s b x main f hp hh ha hx hm
  have He (z : Grid M) : (f z*v z).re=‖v z‖ := polar_identity _
  have H : amp k main ≤ ∑ z, ‖v z‖ := hL.trans (strong_sum q main x ha hx)
  refine ⟨b,f,fun z => polar_unit _,?_⟩
  change ∑ z,(f z*v z).re = _ at HH
  simp_rw [He,mul_div_assoc] at HH
  nlinarith

private lemma test_one (g z : ℂ) (hg : ‖g‖ ≤ 1) (hz : ‖z‖ = 1) :
    |(g*z).re| ≤ 1 := (Complex.abs_re_le_norm _).trans
      (by rw [norm_mul,hz,mul_one]; exact hg)

lemma expensive_intent {s : Scene M} (main : Bool) {k : ℕ} {x : Grid M}
    (hp : s.here.valid) (hh : s.here.lev < M) (ha : 0 ≤ s.wage)
    (hx : 0 < s.norm) (hm : 0 < s.mass) (he : intense main s (side k) x) :
    amp k main /2 ≤ s.mass/s.norm := by
  obtain ⟨b,f,hf,hb⟩ := criterion_bias _ _ _ _ hp hh ha hx hm he
  apply hb.trans
  apply mul_le_of_le_one_right (by positivity)
  refine le_trans (Ex_mono _ (g:=fun _ => 1) fun i => ?_) (Ex_const _ _).le
  unfold aim; split_ifs
  · rw [one_mul]; exact (le_abs_self _).trans (test_one _ _ (hf _) (norm_chi _ _))
  norm_num

lemma edge_prob {s : Scene M} {i : ℕ} (hm : 0 < s.mass) (hn : 0 < s.norm)
    (hp : s.here.ok M) (h : 0 ≤ s.wage) :
    s.mass/s.norm * s.actor.prob (fun x => lanes s.here i M ∧ flanked s.here i x)
      = edgeW s i := by
  classical
  rw [prob_eq,edgeW]
  by_cases hh : lanes s.here i M
  · simp only [hh,ite_true,true_and]; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    split_ifs with H
    · rw [actor_def hp h hm]
      unfold wt mass; unfold mass at hm
      field_simp
    exact mul_zero _
  simp [hh]

/-- Mask of sufficient precision is a biased test under the post law -/
theorem masked_bias {s : Scene M} {i : ℕ} (main : Bool) (x : Grid M)
    (hp : s.here.valid) (he : s.here.lev < M)
    (ha : 0 ≤ s.wage) (hn : 0 < s.norm) (hm : 0 < s.mass) (hM : s.mass ≤ 2*s.norm)
    (h : intense main s (side i) x)
    (hB : ¬ hazard s main i) (r : ℕ) (hr : side r ≤ amp i main /128) :
    ∃ g : Grid M → ℂ, (∀ z, ‖g z‖ ≤ 1) ∧ ∃ f : Grid M → ℝ,
      limitR f (band s.here i r) ∧ (∀ y, 0 ≤ f y ∧ f y ≤ 1) ∧
      expU (fun y => if y∈s.here.block M then 0 else f y) ≤ s.here.len*side r ∧
      amp i main /8 ≤ (tracker s main).Ex (fun y => f y.1*(g y.2*chi x y.1).re) := by
  obtain ⟨b,g,hg,hG⟩ := criterion_bias s main i x hp he ha hn hm h
  obtain ⟨f,hf,hN,hE,hP⟩ := make_mask (M:=M) s.here hp he b i r
  let p := s.here
  let a := amp i main; let v := s.mass/s.norm
  let P := tracker s main
  let w (y : Grid M × Grid M) := (g y.2*chi x y.1).re
  let G (y : Grid M) := lanes p i M ∧ flanked p i y
  let F (y : Grid M × Grid M) := f y.1*w y
  have Hq : v*P.prob (fun y => G y.1) ≤ a/128 := by
    rw [← prob_send P Prod.fst G,show P.send Prod.fst=s.actor from send_fst_withNext _ _]
    rw [edge_prob hm hn ⟨hp,he.le⟩ ha]
    exact le_of_not_ge hB
  have Hw (i) : |w i| ≤ 1 := test_one _ _ (hg _) (norm_chi _ _)
  have H : v * P.Ex (fun i => aim (p:=p) b i.1*w i) ≤
      v* (P.Ex F + P.prob (fun i => G i.1) + side r) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← Ex_const P (side r)]; unfold prob
    rw [← Ex_add,← Ex_add]
    apply Ex_mono_mem; rintro ⟨y,z⟩ h
    have h0 : y∈p.block M := by
      have hh : 0 < s.actor y := pos_of_mul_pos_left h ((channel (optic s main) y).nonneg z)
      exact piece_support ⟨hp,he.le⟩ (actor_def ⟨hp,he.le⟩ ha hm) _ hh
    change aim (p:=p) b y*w (y,z) ≤ f y*w (y,z)+(@ite ℝ (G y) (Classical.propDecidable _) 1 0)+side r
    have hi := abs_le.mp (Hw (y,z))
    have hi' := hN y
    split_ifs with H
    · unfold aim; split_ifs <;> nlinarith [side_pos r]
    have He : |aim (p:=p) b y-f y| ≤ side r := hE y h0 H
    have hY := (mul_le_mul He (Hw (y,z)) (abs_nonneg _) (side_pos r).le)
    rw [← abs_mul,mul_one] at hY
    have hx := (abs_le.mp hY).2
    linarith
  refine ⟨g,hg,f,hf,hN,hP,?_⟩
  have hv : v ≤ 2 := (div_le_iff₀ hn).mpr hM
  have hp' : 0 < v := by unfold v; positivity
  change a/2 ≤ _ at hG
  change _ ≤ v * P.Ex (fun i => aim (p:=p) b i.1*w i) at hG
  have HH : 0 < a := amp_pos _ _
  change a/8 ≤ P.Ex F
  change side r ≤ a/128 at hr
  nlinarith

end FourierLLogL.Dyadic.Procedure.Capture

end OAI
