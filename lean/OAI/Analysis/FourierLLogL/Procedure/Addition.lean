import OAI.Analysis.FourierLLogL.Procedure.Deficit
import OAI.Analysis.FourierLLogL.Thermal.Posterior
/-! # Cost of revealing the new main observation -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure
open Law Node Real Period Compress.Params Thermal Fund Scene Fork
variable {M J j : ℕ} {s : Scene M}
open scoped Classical

private def measureRate (p : Node) (A : Form M) (z v : Grid M) :=
    side M * (boltz A (z-v)* boltz (place p M) (start p M-v))

private lemma weight_pos' (p : Node) (A : Form M) (z v : Grid M) :
    0 < measureRate p A z v :=
  mul_pos (side_pos _) (mul_pos (boltz_pos _ _) (boltz_pos _ _))

private lemma rate_sum_pos (p : Node) (A : Form M) (z : Grid M) :
    0 < ∑ v, measureRate p A z v :=
  Finset.sum_pos (fun _ _ => weight_pos' _ _ _ _) Finset.univ_nonempty

private lemma rate_sum_le (p : Node) (A : Form M) (hA : 0 ≤ A) (z : Grid M) :
    ∑ v, measureRate p A z v ≤ exp (-F (A+place p M)) := by
  let s : Profile M := [(A,z), (place p M,start p M)]
  have ht : mixForm s=A+place p M := by simp [s,mixForm]
  have hV (x : Grid M) : measureRate p A z x = side M*tune s x := by
    unfold s measureRate; rw [tune_cons,tune_cons]
    simp [tune,sumE]
  have H := profile_envelope (s:=s) (by
    intro i hi
    simp only [s,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with h|h <;> (subst i; first | exact hA | exact place_valid _ _)) 0
  simp_rw [hV,← Finset.mul_sum]
  unfold fc at H
  simp only [ht,neg_zero,chi_zero_left,mul_one,expU_real,Complex.norm_real,Real.norm_eq_abs] at H
  change expU (fun x => tune s x) ≤ _
  rw [F_origin]; exact (le_abs_self _).trans H

private def matchLabel (p : Node) (A : Form M) (z : Grid M) : Law (Grid M) :=
    proportional _ (fun i => (weight_pos' p A z i).le) (rate_sum_pos p A z)

private lemma match_pos (p : Node) (A : Form M) (z v : Grid M) :
    0 < matchLabel p A z v :=
  div_pos (weight_pos' _ _ _ _) (rate_sum_pos _ _ _)

private lemma KL_bound (p : Node) (A B : Form M) (hA : 0 ≤ A) (h : A+place p M ≤ B)
    (x z : Grid M) :
    let q := matchLabel p A
    (channel B x).kl (q z) ≤ F B-F (A+place p M) +
      (channel B x).Ex (fun y => form A (z-y) + form (place p M) (start p M-y)) := by
  intro q
  have hB : 0 ≤ B := (add_nonneg hA (place_valid _ _)).trans h
  rw [kl_ex]
  conv_rhs => lhs; rw [← Ex_const (channel B x) (F B-F (A+place p M))]
  rw [← Ex_add]; apply Ex_mono; intro i
  let S := place p M; let t := start p M
  change log (channel B x i)-log (measureRate p A z i/∑ v, measureRate p A z v) ≤
    F B-F (A+S) + (form A (z-i)+form S (t-i))
  have H := log_le_log (rate_sum_pos p A z) (rate_sum_le p A hA z)
  rw [log_exp] at H
  rw [ch_K,K_eq,log_mul (side_pos _).ne' (exp_pos _).ne',log_exp,
    Real.log_div (weight_pos' _ _ _ _).ne' (rate_sum_pos _ _ _).ne',
    measureRate, log_mul (side_pos _).ne' (mul_pos (boltz_pos _ _) (boltz_pos _ _)).ne',
    log_mul (boltz_pos _ _).ne' (boltz_pos _ _).ne',boltz,boltz,log_exp,log_exp]
  change _ ≤ -F (A+S) at H
  unfold S t at *
  linarith [form_nonneg hB (i-x)]

theorem added_deficit (s : Scene M) (p : Node) (A B : Form M)
    (hp : s.here.ok M) (he : s.here=p) (hh : 0 ≤ s.wage) (hm : 0 < s.mass)
    (hA : 0 ≤ A) (hB : A+place p M ≤ B) :
    deficit s (channel B) ≤ deficit s (channel A)+
      (F B-F (A+place p M)+4*(label A).Ex (form A)+264) := by
  subst p
  let q := s.here; let S := place q M
  let k := channel A; let v := channel B
  let T := matchLabel q A
  let P := s.actor; let H := P.withNext k
  let x := F B-F (A+S)
  let l := (label A).Ex (form A)
  let y := x+4*l+264
  have hi : H.Ex (fun z => (v z.1).kl (T z.2)) ≤ y := by
    unfold H; rw [Ex_withNext]
    have hhA : 0 ≤ S := place_valid q _
    have hx : S ≤ B := le_trans (le_add_of_nonneg_left hA) hB
    have hv : A ≤ B := le_trans (le_add_of_nonneg_right hhA) hB
    let m := q.start M
    have hm' (i) (hi : 0 < P i) :
        (k i).Ex (fun z => (v i).kl (T z)) ≤ y := by
      have he : i∈s.here.block M := piece_support hp (actor_def hp hh hm) _ hi
      have hE := place_internal (start_mem hp.1 hp.2) he
      have hh (z w : Grid M) : form A (z-w)+form S (m-w) ≤
          2*(form A (z-i)+form S (m-i))+ 2*(form A (i-w)+form S (i-w)) := by
        have h1 := form_triangle hA (z-i) (i-w)
        have h2 := form_triangle hhA (m-i) (i-w)
        rw [sub_add_sub_cancel] at h1 h2
        linarith
      have hG (v : Form M) (A : Form M) :
          (channel A i).Ex (fun y => form v (i-y)) = (label A).Ex (form v) := by
        have h1 (y : Grid M) : form v (i-y) = form v (y-i) := by
          rw [show i-y= -(y-i) by ring, form_even _ _]
        simp_rw [h1]; exact ch_noise _ _ _
      have Hta (z : Grid M) :
          (v i).kl (T z) ≤ x+2*(form A (z-i)+form S (m-i))+
            2*(l+100) := by
        have hi := KL_bound q A B hA hB i z
        apply hi.trans
        have he := (v i).Ex_mono (hh z)
        rw [Ex_add _ (f:=fun _ => 2*(form A (z-i)+form S (m-i))), Ex_const,Ex_lmul,Ex_add (f:=fun w => form A (i-w))] at he
        unfold v at he
        rw [hG,hG] at he
        have h1 := S_energy q.invlen q.invlen_ge (loc_scale hp.2) B hx
        have h2 := form_energy_mono hA hv hA
        unfold x l m S q place at *
        linarith
      apply le_trans ((k i).Ex_mono Hta); unfold k
      rw [Ex_add,Ex_add,Ex_lmul,Ex_add,Ex_const,Ex_const,Ex_const,ch_noise A (form A)]
      unfold y x S m l q at *; linarith
    exact (P.Ex_mono_mem hm').trans (P.Ex_const y).le
  have he := (replace_signal P k v T (match_pos q A)).trans hi
  unfold deficit; change levels s-P.privateH v ≤ levels s-P.privateH k+y
  linarith

lemma priced_change :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ s : Scene M, ∀ f : Grid M → ℝ,
    ∀ u : Update j M s.here, Safe s j J f → Safe (s.win u) j J f → 0 < (s.win u).mass →
      u.Good capA s.fund.mood s.actor →
      let A := s.fund.mood
      deficit (s.win u) (channel (u.next A)) ≤ deficit (s.win u) (channel A) + 500*u.credit := by
  filter_upwards [h_large 10,stiff_budget capA cap_ok] with j hp hx M J s f u hs hS hm hU
  intro A
  have H := added_deficit (win s u) s.here A (u.next A) hS.within rfl hS.positive hm
      hs.capital.effects.nonneg (le_add_of_nonneg_right hU.positive)
  have hh := hs.capital.effects.energy
  let a := Thermal.H j
  let d := height j
  have he : 1 ≤ a := H_ge _
  have ht : 0 ≤ plateErr j := by unfold plateErr; exact div_nonneg (d_pos _).le (pow_nonneg (H_pos _).le _)
  have hy := hU.reserves.1
  have hX := hs.capital.under
  apply H.trans
  have H : 4*(label A).Ex (form A)+264 ≤ 100*u.credit := by
    have hw :
        (label A).Ex (form A) ≤ 2*(capA*a*(plateErr j + 1000*a)) := by
      apply le_trans hh
      calc
        _ ≤ (capA*a)*(2*(plateErr j+1000*a)) := by gcongr <;> linarith
        _ = _ := by ring
    change capA*a*(plateErr j + 1000*a)+2000 ≤ d/a^4 at hx
    have hZ : d/a^4 ≤ u.credit := by
      apply le_trans _ hy; unfold d a
      gcongr <;> first | exact (d_pos j).le | exact H_ge j | omega
    have h0 : 0 ≤ capA*a*(plateErr j + 1000*a) :=
      mul_nonneg (mul_nonneg (le_trans zero_le_one cap_ok) (by linarith)) (by linarith)
    linarith
  linarith [hU.cost]

end FourierLLogL.Dyadic.Procedure

end OAI
