import OAI.Analysis.FourierLLogL.Thermal.Spatial
import OAI.Analysis.FourierLLogL.Dyadic.Node

/-! # Thermal certificates and tightening -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate Real
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Thermal
open Node Law Period Real

variable {M : ℕ}

def place (p : Node) (M : ℕ) := S M p.invlen

lemma place_valid (p : Node) (M : ℕ) : 0 ≤ place p M := S_nonneg _ _

lemma loc_scale {p : Node} (hp : p.lev ≤ M) : invlen p ≤ 2^M := pow_le_pow_right₀ (by norm_num) hp

lemma place_internal {p : Node} {x y : Grid M} (hx : x ∈ p.block M) (hy : y ∈ p.block M) :
    form (place p M) (x-y) ≤ 32 := by
  have hi := diam_block hx hy
  have hh := (diam_le_diff _ _).trans hi
  unfold place; rw [form_S]
  calc
    _ ≤ p.invlen^2 * (32 * Dyadic.diam (x-y)^2) := by gcongr; exact (cost_diam _).2
    _ ≤ p.invlen^2 * (32 * p.len^2) := by gcongr; exact diam_nonneg _
    _ = 32 := by rw [rinv]; field_simp [p.len_pos.ne']

/-- A plate distributes the free energy cost over a long range of factors. -/
def flat (h err : ℝ) (A D : Form M) : Prop :=
    F (A+(h^140 : ℝ) • D)-F (A+(2⁻¹:ℝ) • D) ≤ err

/-- certificate of a main form. n is the addition count and p the latest interval. -/
structure Certified (h err : ℝ) (n : ℕ) (p : Node) (A : Form M) : Prop where
  fits : p.ok M
  nonneg : 0 ≤ A
  prev : (p=root ∧ A=0) ∨ place p M ≤ A
  tighten : F ((h^130:ℝ) • A) - F A ≤ n*(err + 1000*h)
  energy : (label A).Ex (form A) ≤ n*(2*err+100)

variable {h err : ℝ}
lemma certified_start (M : ℕ) : Certified h err 0 root (0:Form M) := by
  refine ⟨root_ok _,le_rfl,Or.inl ⟨rfl,rfl⟩,by simp,?_⟩
  rw [show form (0:Form M) = fun _ => 0 from funext form_zero,Ex_const]
  simp

lemma certified_add {A D : Form M} {p q : Node} {n : ℕ} (H : Certified h err n p A)
    (hh : 1 ≤ h) (hq : q.ok M)
    (hd : 0 ≤ D) (hF : flat h err (A+place q M) D) :
    Certified h err (n+1) q ((A+place q M)+D) := by
  let B := place q M
  let U := A+B+D
  let w := h^130
  have hp : 0 < h := by linarith
  have hw : 1 ≤ w := one_le_pow₀ hh
  have hB : 0 ≤ B := place_valid _ _
  have hA := H.nonneg
  have hAB := add_nonneg hA hB
  have hAU : A ≤ U := by
    apply le_trans (le_add_of_nonneg_right hB) (le_add_of_nonneg_right hd)
  have hBU : B ≤ U := by
    apply le_trans (le_add_of_nonneg_left hA) (le_add_of_nonneg_right hd)
  refine ⟨hq, hA.trans hAU, Or.inr hBU, ?_, ?_⟩
  ·
    let D' := w • D-D
    have hw' {E : Form M} (h : 0 ≤ E) : E ≤ w • E := by
      intro x
      exact le_mul_of_one_le_left (h x) hw
    have hD' : 0 ≤ D' := sub_nonneg.mpr (hw' hd)
    let V := w • A + w • B + D
    have heq : w • U = V+D' := by unfold U V D'; rw [smul_add,smul_add]; abel
    have h1 : U ≤ V := add_le_add_left (add_le_add (hw' hA) (hw' hB)) _
    have h2 : F (V+D')-F V ≤ err := by
      apply le_trans (F_increment (hA.trans hAU) h1 hD')
      have hh1 : U+D' ≤ A+B+(h^140:ℝ) • D := by
        have hP : w ≤ h^140 := pow_le_pow_right₀ hh (by omega)
        unfold U D'
        rw [show A+B+D+(w • D-D) = A+B+w • D by abel]
        refine add_le_add_right ?_ _
        intro x; exact mul_le_mul_of_nonneg_right hP (hd x)
      have hh2 : A+B + (2⁻¹:ℝ) • D ≤ U := by
        refine add_le_add_right ?_ _
        intro x; change 2⁻¹*D x ≤ D x; have hx := hd x; change 0 ≤ D x at hx; norm_num; linarith
      exact le_trans (sub_le_sub (F_mono hh1) (F_mono hh2)) hF
    let W := w • A+B+D
    have h3 : F W-F U ≤ F (w • A)-F A := by
      have ht := F_increment hA hAU (sub_nonneg.mpr (hw' hA))
      rw [show A+(w • A - A) = w • A by abel, show U+(w • A-A)=W by unfold U W; abel] at ht
      exact ht
    have h4 : F V-F W ≤ F (w • B)- F B := by
      have hBW : B ≤ W := le_trans hBU (add_le_add_left (add_le_add_left (hw' hA) _) _)
      have ht := F_increment hB hBW (sub_nonneg.mpr (hw' hB))
      rw [show B+(w • B - B) = w • B by abel, show W+(w • B-B)=V by unfold V W; abel] at ht
      exact ht
    have h5 : F (w • B) - F B ≤ 1000*h := by
      have he : w • B = S M (h^65 * q.invlen) := by
        rw [show w = (h^65)^2 by unfold w; rw [← pow_mul]]; unfold B place; rw [scale_S]
      have hs := one_le_pow₀ hh (n:=65)
      have hc := q.invlen_ge
      have hp' := q.invlen_pos
      rw [he]
      have H1 := F_S_upper M _ (one_le_mul_of_one_le_of_one_le hs hc)
      have H2 := F_S_lower _ hp' (loc_scale hq.2)
      rw [log_mul (by positivity) hp'.ne',log_pow] at H1
      unfold B place; push_cast at *
      linarith [Real.log_le_sub_one_of_pos hp]
    have H6 := H.tighten
    change F (w • U) - F U ≤ _
    change F (w • A)-F A ≤ _ at H6
    rw [heq]
    push_cast; linarith

  let L := (2⁻¹:ℝ) • D
  have heq : U = A+B+L+L := by
    unfold L U
    rw [add_assoc (A+B) _ _,← add_smul]
    norm_num
  have h1 : F U-F (A+B+L) ≤ err := by
    have he : D ≤ h^140 • D := fun x => le_mul_of_one_le_left (hd x) (one_le_pow₀ hh)
    exact (sub_le_sub_right (F_mono (add_le_add_right he (A+B))) _).trans hF
  have hG : (label U).Ex (form D) ≤ 2*err := by
    have hh1 := mean_energy (A+B+L) L
    rw [← heq] at hh1
    have h2 (x : Grid M) : form L x = 2⁻¹ * form D x := form_smul _ _ _
    rw [funext h2,Ex_lmul] at hh1
    norm_num at hh1; linarith
  have hG' : (label U).Ex (form B) ≤ 100 :=
    S_energy q.invlen q.invlen_ge (loc_scale hq.2) U hBU
  change (label U).Ex (form U) ≤ _
  have h3 (x : Grid M) : form U x = form A x+form B x+form D x := by
    unfold U; rw [form_add,form_add]
  rw [funext h3,Ex_add,Ex_add]
  have hh1 := form_energy_mono hA hAU hA
  have hh2 := H.energy
  push_cast; linarith

/-- tightening used by compression and evidence posterior bounds. -/
def tilde (h : ℝ) (A : Form M) (p : Node) : Form M :=
  h^130 • A + S M (1000*p.invlen)

lemma tilde_le {h : ℝ} (hh : 1 ≤ h) {A : Form M} (hA : 0 ≤ A) (p : Node) :
    A+place p M ≤ tilde h A p := by
  apply add_le_add _ (S_mono p.invlen_pos.le (by linarith [p.invlen_pos]))
  intro i; exact le_mul_of_one_le_left (hA i) (one_le_pow₀ hh)

lemma tilde_tight {n : ℕ} {A : Form M} {p q : Node} (H : Certified h err n p A)
    (hh : 1 ≤ h) (hq : q.ok M) :
    F (tilde h A q)-F (A + place q M) ≤ n*(err+1000*h)+2000 := by
  let B := place q M
  let A' := h^130 • A
  let B' := S M (1000*q.invlen)
  have hA := H.nonneg
  have hB : 0 ≤ B := place_valid _ _
  have hA' : A ≤ A' := fun i => le_mul_of_one_le_left (hA i) (one_le_pow₀ hh)
  have hB' : B ≤ B' := S_mono q.invlen_pos.le (by linarith [q.invlen_pos])
  have hX := F_increment hA hA' hB
  have hY := F_increment hB hB' (hA.trans hA')
  have hc := q.invlen_ge
  have hc' := q.invlen_pos
  have hZ : F B'-F B ≤ 2000 := by
    have h1 := F_S_upper M (1000*q.invlen) (by linarith)
    have h2 := F_S_lower _ hc' (loc_scale hq.2)
    rw [log_mul (by norm_num) hc'.ne'] at h1
    unfold B B' place
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1000)]
  have HH := H.tighten
  rw [add_comm B _,add_comm B' _] at hY
  change F A'-_ ≤ _ at HH
  change F (A'+B')-F (A+B) ≤ _
  linarith

lemma space_increment {n : ℕ} {A : Form M} {p q' : Node} (H : Certified h err n p A)
    (h : q'.below p) (hq : q'.ok M) :
    F (A+place q' M)-F A ≤ log q'.invlen - log p.invlen + 3000 := by
  let B := place q' M
  have hh := scale_below h
  have hn := q'.invlen_ge
  have hp := q'.invlen_pos
  have hz := p.invlen_pos
  rcases H.prev with ⟨he,h'⟩|he
  · rw [h',he,F_zero,zero_add,invlen_top,log_one]
    unfold place
    linarith [F_S_upper M _ hn]
  let r := p.invlen/20
  let s := arc M r
  have hr : 0 < r := by unfold r; positivity
  have hs : r ≤ s.card := arc_card_lo _ _ hr.le (by
    unfold r; linarith [loc_scale H.fits.2])
  have hB := place_valid q' M
  let L := (1/120:ℝ)
  have hl : 0 < L := by unfold L; norm_num
  have hx1 (i : Grid M) (hi : i ∈ s) :
      q A 0 * (L/q'.invlen) ≤ q A i * q B (-i) := by
    have hx := (mem_arc _ _).mp hi
    have h1 := cred_short _ p.invlen_ge (loc_scale H.fits.2) _ he i hx
    have h2 := q_short _ hn (loc_scale hq.2) i (by unfold r at hx; linarith)
    calc
      _ = (exp (-F A)*(1/2))*((1/60)/q'.invlen) := by rw [F_origin]; unfold L; ring
      _ ≤ (exp (-F A)*cred A i)* q B i :=
        mul_le_mul (by gcongr) h2 (by positivity) (mul_nonneg
          (Real.exp_nonneg _) (cred_nonneg H.nonneg _))
      _ = _ := by rw [← q_express, q_even _ _]
  have HX :
      q A 0 * ((p.invlen / q'.invlen) / 2400) ≤ q (A+B) 0 := by
    have ha := q_origin_pos A
    rw [q_add]; simp_rw [zero_sub]
    calc
      _ = r * (q A 0 * (L/q'.invlen)) := by unfold r L; ring
      _ ≤ ↑s.card*(q A 0 * (L/q'.invlen)) := by gcongr
      _ = _ := (show ∑ _i ∈ s, (q A 0 * (L/q'.invlen)) = _ by simp).symm
      _ ≤ ∑ i ∈ s, q A i * q B (-i) := Finset.sum_le_sum hx1
      _ ≤ ∑ i, q A i * q B (-i) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => mul_nonneg (q_nonneg H.nonneg _) (q_nonneg hB _))
  have hhA := q_origin_pos A
  have Hl := log_le_log (by positivity) HX
  rw [log_mul (by positivity) (by positivity),log_div (by positivity) (by norm_num),
    log_div (by positivity) (by positivity)] at Hl
  change F (A+B)-_ ≤ _
  unfold F
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2400)]

end FourierLLogL.Dyadic.Thermal

end OAI
