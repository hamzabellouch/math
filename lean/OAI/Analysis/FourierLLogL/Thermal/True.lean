import OAI.Analysis.FourierLLogL.Thermal.Reference
import OAI.Analysis.FourierLLogL.Finite.Tail

/-! # True-law estimates used to supervise all attempts -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Thermal
open Law Node Real Period Compress.Params

namespace Update
variable {p : Node} {j M : ℕ}

/-- Failure of loudness only. -/
def quiet (u : Update j M p) (x : Clutch j M) :=
    ∀ i, ‖app u x.1 (x.2 i)‖ < beta u.ix/4

lemma consistent_triangle {A : Form M} (u : Update j M p) (hA : 0 ≤ A) {x : Clutch j M}
    {y z : Grid M} (h : form A (z-y) ≤ cushion j)
    (h' : ∀ i, form A (x.2 i-y) ≤ cushion j)
    (H : ¬ u.quiet x) : u.alarm A z x := by
  unfold quiet at H
  push Not at H
  obtain ⟨i,hi⟩ := H
  refine ⟨i,?_,hi⟩
  unfold consistent
  have he := form_triangle hA (x.2 i-y) (-(z-y))
  rw [form_even _ _,show x.2 i-y+ -(z-y)=x.2 i-z by ring] at he
  linarith [h' i]

private lemma diff_cost (u : Update j M p) (hv : ∀ i z, ‖u.v i z‖ ≤ 1) (x z d : Grid M) :
    (‖u.app x z‖- ‖u.app (x+d) z‖)^2 ≤ 2*form u.adjust d := by
  let P := u.V; let r := raise (snap_le (M:=M) j p); let f := fun i => u.v i z
  let c := chi (r u.x) d
  have hn (x : Grid M) : u.app x z = P.Cx (fun i => f i * chi (r i) x) := rfl
  have he (i : Grid (snapGrid j p M)) : c*chi (r (i-u.x)) d = chi (r i) d := by
    unfold c; rw [← chi_add',← map_add]
    congr 2; ring
  let F (i : Grid (snapGrid j p M)) := f i * chi (r i) x * c *
      (1-chi (r (i-u.x)) d)
  have HQ : c*u.app x z-u.app (x+d) z=P.Cx F := by
    simp_rw [hn,← Cx_lmul,Cx,← Finset.sum_sub_distrib,chi_add _ x]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← he]; unfold F; ring
  have hi (i) : ‖F i‖ ≤ ‖1-chi (r (i-u.x)) d‖ := by
    unfold F c; simp_rw [norm_mul,norm_chi,mul_one]
    exact mul_le_of_le_one_left (by positivity) (hv _ z)
  have H := abs_norm_sub_norm_le (c*u.app x z) (u.app (x+d) z)
  rw [HQ,norm_mul,show ‖c‖=1 from norm_chi _ _,one_mul] at H
  calc
    _ ≤ ‖P.Cx F‖^2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) H _
    _ ≤ _ := sq_Cx_norm P F
    _ ≤ P.Ex fun i => ‖1-chi (r (i-u.x)) d‖^2 := Ex_mono P (fun i => by gcongr; exact hi i)
    _ = _ := by simp_rw [norm_phase_sq, Ex_lmul, adjust,average_form]; rfl

open scoped Classical

lemma quiet_scale (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ j : ℕ in atTop, ∀ M : ℕ, ∀ p : Node, ∀ P : Law (Grid M),
      ∀ (A : Form M) (u : Update j M p), u.Good C A P → u.regular → ∀ x : Grid M,
        u.take A x → (fresh A (u.next A) j x).prob (quiet u) ≤ 2/H j^40 := by
  filter_upwards [h_large (10^16*reserve C)] with j hh M p P A u hu hr x hx
  let b := beta u.ix; let a := H j; let d := height j; let D := reserve C
  let V := u.next A
  let L := clones j
  have hL : (L:ℝ) = a^120 := clones_eq j
  have hb : 0 < b := beta_pos _
  have hI : 1 ≤ a := H_ge _
  have ha : 0 < a := H_pos _
  have hD : 1 ≤ D := reserve_ge hC
  change 10^16*D ≤ a at hh
  have he : (1/6400)/a^32 ≤ b := (main_bounds _ hu.ix_ok).1
  let T := channel A x
  let G := channel V x

  let bad (i) : Prop := ‖u.app x i‖ < 3*b/8
  have hi : 1/a^33 ≤ 1-T.prob bad := by
    unfold take at hx
    rw [ite_eq_left hr] at hx
    have hu' := hx.trans (Cx_norm T _)
    have hE := lowerTail T (fun x => ¬ bad x) (3*b/8) 1 (fun i => ‖u.app x i‖)
      (fun i _ => by
        have HE : ‖u.app x i‖ ≤ 1 := ply_unit _ _ _ (fun j => hu.unit j _) _
        linarith)
      (fun i hi => (show ‖u.app x i‖ < 3*b/8 from Classical.byContradiction (p:=bad i) hi).le)
    rw [prob_compl] at hE
    apply le_trans (b:=b/8) _ (by change b/2 ≤ _ at hu'; linarith)
    apply le_trans (b:= ((1/6400)/a^32)/8) ?_ (by linarith)
    field_simp
    nlinarith
  have hf : (T.prob bad)^L ≤ 1/a^40 := by
    let t := T.prob bad
    have he' := bernoulli_trial (prob_nonneg T bad) (prob_le_one T bad) L
    rw [hL] at he'
    change a^120*t^L*(1-t) ≤ _ at he'
    have ht : 0 ≤ t^L := pow_nonneg (prob_nonneg _ _) _
    change t^L ≤ _
    have he : a^120*t^L * (1/a^33) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hi (mul_nonneg (pow_nonneg ha.le 120) ht)).trans he'
    have hZZ : a^40 ≤ a^87 := pow_le_pow_right₀ hI (by omega)
    rw [show a^120*t^L*(1/a^33)=a^87*t^L by
      rw [show a^120=a^87*a^33 by ring]; field_simp] at he
    apply (le_div_iff₀ (by positivity : 0 < a^40)).mpr
    nlinarith

  let other (z : Grid M) := (b/8)^2 ≤ 2*form u.adjust (z-x)
  have hM : G.prob other ≤ 1/a^40 := by
    have hp := upperTail G other (fun z => 2*form u.adjust (z-x)) (fun i =>
      mul_nonneg (by norm_num) (form_nonneg (averageCost_pos _ _ _) _)) ((b/8)^2) (fun i hi => hi)
    rw [Ex_lmul, show G.Ex (fun z => form u.adjust (z-x)) =
      (label V).Ex (form u.adjust) from ch_noise _ _ _] at hp
    have hc := hu.high
    have HE : (b/8)^2*G.prob other ≤ 800*D/a^200 := by
      apply hp.trans
      have HT : 0 < d*a^200 := mul_pos (d_pos j) (pow_pos ha 200)
      apply le_trans (b:=2*(400*u.credit/u.scale)) (mul_le_mul_of_nonneg_left hu.energy (by norm_num))
      calc
        _ ≤ 2*(400*(D*d)/(d*a^200)) := by
          have H₁ : d*a^200 ≤ u.scale := hu.high
          have H₂ : u.credit ≤ D*d := hu.reserves.2
          have hx : 0 < d := d_pos _
          gcongr
        _ = _ := by have hx : 0 < d := d_pos _; field_simp; norm_num
    apply le_of_mul_le_mul_left _ (show 0 < (b/8)^2 by positivity)
    calc
      _ ≤ _ := HE
      _ ≤ (((1/6400)/a^32)/8)^2 * (1/a^40) := by
          have Ht : a ≤ a^96 := by
            have := pow_le_pow_right₀ hI (show 1 ≤ 96 by omega); simpa using this
          field_simp
          nlinarith
      _ ≤ _ := by gcongr
  let Q := fresh A V j x
  have heQ : Q.prob (quiet u) ≤ G.prob other + (T.prob bad)^L := by
    let S : Law (Fin L → Grid M) := pack fun _ => T
    have HH (y z : Grid M) (hy : ¬ other y) (hz : ¬ bad z) : b/4 ≤ ‖u.app y z‖ := by
      have HE := diff_cost u hu.unit x z (y-x)
      rw [show x+(y-x)=y by ring] at HE
      unfold other bad b at *; nlinarith
    calc
      Q.prob (quiet u) ≤ Q.prob (fun xz => other xz.1 ∨ ∀ i, bad (xz.2 i)) :=
        prob_mono Q _ _ fun x hx => by
          by_contra! H
          obtain ⟨i,hi⟩ := H.2
          exact (hx i).not_ge (HH _ _ H.1 hi)
      _ ≤ Q.prob (fun x => other x.1) + Q.prob (fun x => ∀ i, bad (x.2 i)) := Q.prob_union _ _
      _ = _ := by
        rw [← prob_send Q Prod.fst other, ← prob_send Q Prod.snd (fun x => ∀ i, bad (x i))]
        unfold Q fresh
        rw [send_fst_tensorP,send_snd_tensorP]; congr 1
        exact independent T bad L
  change Q.prob _ ≤ 2/a^40
  apply heQ.trans; rw [show 2/a^40=1/a^40+1/a^40 by ring]; linarith

end Update
end FourierLLogL.Dyadic.Thermal

end OAI
