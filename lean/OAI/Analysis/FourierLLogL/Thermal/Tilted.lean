import OAI.Analysis.FourierLLogL.Thermal.Power
import OAI.Analysis.FourierLLogL.Thermal.Product

/-! # Bounding a characteristic-function power -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Thermal
open Law Node Real Period

variable {M l : ℕ}
open scoped Classical

lemma prob_translate (v : Grid M → Prop) (t : Grid M) :
    (uniform _).prob (fun z => v (z-t)) = (uniform _).prob v := by
  unfold prob
  simp_rw [← expU_ex, show ∀ z, z-t = -t+z from fun z => by ring]
  rw [expU_translate (fun z => if v z then (1:ℝ) else 0)]

/-- label cutoff by reference radius -/
def dome (p : Node) (M : ℕ) (s : ℝ) (z : Grid M) :=
    Dyadic.diam (z-start p M) ≤ s / p.invlen

lemma dome_prob (p : Node) (hp : p.ok M) (s : ℝ) (hs : 1 ≤ s) :
    (uniform _).prob (dome p M s) ≤ 4*s/p.invlen := by
  have hr := p.invlen_pos
  have he : (uniform _).prob (dome p M s) ≤ 2*(s/p.invlen + side M) := by
    unfold dome
    rw [prob_translate (fun z => Dyadic.diam z ≤ s/p.invlen)]
    exact arc_length _ _ (by apply div_nonneg <;> linarith)
  have hi : side M ≤ 1/p.invlen := by
    rw [side_pow_two,one_div]
    exact (inv_le_inv₀ (by positivity) hr).mpr (loc_scale hp.2)
  apply le_trans he
  have hx := (le_div_iff₀ hr).mp hi
  field_simp; linarith

lemma prob_as_ex {α : Type} [Fintype α] (P : Law α) (p : α → Prop) [DecidablePred p] :
    P.prob p = P.Ex (fun x => if p x then 1 else 0) := by
  rw [prob_eq]; unfold Ex; simp

lemma ch_dome_bound {p p' : Node} (hv : p.below p') {n : ℕ} {h err : ℝ} {A : Form M}
    (H : Certified h err n p' A) (x : Grid M) (hx : x∈p.block M) (s : ℝ) (hs : 0 < s) :
    (channel A x).prob (fun z => ¬dome p' M s z) ≤ 264/(8*s^2) := by
  let C := channel A x


  have hi : C.Ex (fun z => (8*s^2)*(if ¬dome p' M s z then 1 else 0)) ≤ 264 :=
    le_trans (C.Ex_mono (g:=fun z => form (place p' M) (z-p'.start M)) fun z => by
      unfold dome; split_ifs with Hh
      · rw [mul_zero]
        exact form_nonneg (place_valid _ _) _
      · have hp := p'.invlen_pos
        rw [not_le] at Hh
        rw [mul_one,place,form_S]
        apply le_trans (b:=p'.invlen^2*(8*(Dyadic.diam (z-start p' M))^2))
        · rw [div_lt_iff₀ hp] at Hh
          have hh := pow_le_pow_left₀ hs.le Hh.le 2
          nlinarith
        · exact mul_le_mul_of_nonneg_left (cost_diam _).1 (sq_nonneg _)) (local_channel_energy H x (block_of_below hv _ hx))
  rw [Ex_lmul,mul_comm] at hi
  apply (le_div_iff₀ (by positivity : 0 < 8*s^2)).mpr
  have HH : C.prob (fun x => ¬ dome p' M s x) =
      C.Ex (fun z => if ¬dome p' M s z then 1 else 0) := by
    refine @prob_as_ex _ _ _ _ (fun z => instDecidableNot)
  rw [show (channel A x) = C from rfl,HH]; exact hi

/-- factorization for the two center-shifted weights used in the unconditional cap -/
private lemma two_envelope {A B C : Form M} (hA : 0 ≤ A) (hB : 0 ≤ B) (hh : A+B ≤ C)
    (i j s : Grid M) :
    ‖expU (fun y => (↑(boltz A (i-y)*boltz B (j-y)):ℂ)*chi s y)‖ ≤ exp (-F (A+B))*cred C s := by
  let f := fun b : Bool => if b then B else A
  let v := fun b : Bool => if b then j else i
  have H := envelope Finset.univ f (fun i _ => by cases i; exact hA; exact hB) v (-s)
  simp only [Fintype.prod_bool,Fintype.sum_bool,f,v,Bool.false_eq_true,↓reduceIte,q_even _ _] at H
  rw [add_comm] at H
  have HE := q_compare (add_nonneg hA hB) (le_refl (A+B)) hh s
  apply le_trans ?_ HE
  rw [expU_coeff (fun y => (↑(boltz A (i-y)*boltz B (j-y)):ℂ)) s]
  apply le_trans _ H
  push_cast; simp_rw [mul_comm ((boltz A _):ℂ)]
  exact le_rfl

lemma moments_bias {p : Node} {P : Law (Grid M)} (hl : l ≤ M)
    {B : Bool} {A : Form M} {s : Finset (Grid l)} {v : Grid l → Grid M → ℂ}
    {β : ℝ} (hG : biases P p A hl s B v β) (Q : Law (Grid l)) (hQ : ∀ x, 0 < Q x → x∈s) :
    let U := P.withNext (channel A)
    β ≤ U.Ex (fun xz => if xz.1∈(p.child B).block M then
        (ply hl Q (fun i => v i xz.2) xz.1).re else 0) := by
  intro U
  let D (i : Grid l) (x : Grid M × Grid M) :=
    if x.1∈(p.child B).block M then (v i x.2*chi (raise hl i) x.1).re else 0
  have H (i : Grid l) (hi : 0 < Q i) : β ≤ U.Ex (D i) := by
    unfold U D; rw [conditional_if_ex P (channel A) (fun x => x∈(p.child B).block M)
      (fun x z => (v i z*chi (raise hl i) x).re)]
    exact hG.2 _ (hQ _ hi)
  calc
    _ = Q.Ex (fun _ => β) := (Q.Ex_const _).symm
    _ ≤ Q.Ex (fun i => U.Ex (D i)) := Q.Ex_mono_mem H
    _ = _ := by
      rw [Ex_swap Q U]
      refine congrArg U.Ex (funext fun x => ?_)
      unfold D
      split_ifs with hh
      · rw [ply,re_Cx]
      rw [Ex_const]

private lemma ex_pow_bound {α : Type} [Fintype α]
    (P : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (T : ℕ) :
    P.Ex f ^ T ≤ P.Ex (fun i => f i ^ T) := by
  have H := (convexOn_pow (𝕜:=ℝ) T).map_sum_le (t:=Finset.univ)
    (p:=f) (w:=fun i => P i) (fun x _ => P.nonneg x) P.total (fun i _ => hf i)
  exact H

lemma uniform_level_cost {p p' : Node} {a : Grid M → ℝ} (hp : p.ok M) (hv : p.below p')
    {n : ℕ} {h err : ℝ} {A A' : Form M} (H : Certified h err n p' A)
    (HH : A+place p M ≤ A')
    {P : Law (Grid M)} (ht : PieceLaw p a P) (hl : l ≤ M) {s : Finset (Grid l)}
    {d : ℝ} (h1 : ∀ x, a x ≤ exp d) (hm : exp (-d) ≤ p.avg a) {B : Bool}
    {v : Grid l → Grid M → ℂ} {β : ℝ} (h0 : 0 < β) (hb : β ≤ 1)
    (HG : biases P p A hl s B v β) (Q : Law (Grid l)) (hQ : ∀ x, 0 < Q x → x∈s) (T : ℕ)
    (hT : 0 < T) :
    levelCost hl A' Q T ≤ 2*d + F A - log p'.invlen + 5000 - log β +
        2*T*(1-log β) := by
  classical
  let R := p.invlen
  let R' := p'.invlen
  let E := levelCost hl A' Q T
  let K := place p M
  let fp := F (A+K)
  have hpR : 0 < R := p.invlen_pos
  have hpR' : 0 < R' := p'.invlen_pos
  let L := channel A
  let U := P.withNext L
  let a0 := 1000/β
  have ha : 1 ≤ a0 := (le_div_iff₀ h0).mpr (by linarith)
  let D := dome p' M a0
  have hD : U.prob (fun xz => ¬ D xz.2) ≤ β/2 := by
    unfold prob; dsimp only [U]; rw [Ex_withNext]
    rw [← Ex_const P (β/2)]
    refine Ex_mono_mem _ fun x hx => ?_
    have hH := ch_dome_bound hv H x (piece_support hp ht x hx) a0 (by linarith)
    apply le_trans (show (L x).prob _ ≤ _ from hH)
    unfold a0; field_simp; nlinarith
  let W (x z : Grid M) := ply hl Q (fun i => v i z) x
  have HW (x z : Grid M) : ‖W x z‖≤1 := ply_unit _ _ _ (fun i => HG.1 i z) _
  let f (xz : Grid M × Grid M) := if D xz.2 then ‖W xz.1 xz.2‖ else 0
  have hf (xz) : 0 ≤ f xz := by unfold f; split_ifs <;> positivity
  have he : β/2 ≤ U.Ex f := by
    let V := fun xz : Grid M × Grid M => if ¬ D xz.2 then (1 : ℝ) else 0
    have hG' : β ≤ U.Ex fun xz => f xz+V xz := by
      apply le_trans (moments_bias hl HG Q hQ)
      refine Ex_mono _ fun xz => ?_
      unfold f V
      change (if _ then (W _ _).re else _) ≤ _
      have hh := HW xz.1 xz.2
      have hh' := Complex.abs_re_le_norm (W xz.1 xz.2)
      by_cases hh0 : D xz.2 <;> simp only [hh0,ite_true, ite_false,not_false_eq_true, not_true,add_zero,zero_add] <;>
        split_ifs <;> first | positivity | linarith [(abs_le.mp hh').2]
    have hD' : U.Ex V ≤ β/2 := by
      rw [@prob_as_ex _ _ _ _ (fun z => instDecidableNot)] at hD
      exact hD
    rw [Ex_add] at hG'; linarith
  let N := 2*T
  have he1 : (β/2)^N ≤ U.Ex (fun i => f i ^ N) :=
      (pow_le_pow_left₀ (by positivity) he N).trans (ex_pow_bound _ _ hf _)
  let V (z y : Grid M) := boltz A (z-y)*boltz K (p.start M-y)
  have hV (z) : expU (fun y => V z y * ‖W y z‖^N) ≤ exp (-fp) * exp (-E) := by
    unfold E
    rw [heat_exp]
    exact weighted_envelope T hl A' Q _ (fun x => HG.1 x z) _ _
      (fun s => two_envelope H.nonneg (place_valid _ _) HH _ _ _)
  let c := R*exp (2*d+F A+32)
  have hc : 0 ≤ c := by unfold c; positivity
  let b := side M
  have hbb : 0 < b := side_pos _
  have hpoint (x z : Grid M) : U (x,z) ≤ b*c*b*V z x := by
    have Hx := piece_density ht h1 hm x
    rw [dice_apply hp] at Hx
    have h1 : 0 < V z x := mul_pos (boltz_pos _ _) (boltz_pos _ _)
    by_cases h : x∈p.block M
    · rw [ite_eq_left h,← rinv] at Hx
      have HE := place_internal (start_mem hp.1 hp.2) h
      have hi : 1 ≤ exp 32 * boltz K (p.start M-x) := by
        unfold boltz; rw [← exp_add]
        apply Real.one_le_exp _; unfold K; linarith
      calc
        _ = P x * (b*(exp (F A)*boltz A (z-x))) := by
          unfold U L b
          rw [withNext_apply,ch_K,K_eq,boltz,← exp_add]; congr 4
        _ ≤ (exp (2*d)*(b*R)) * (b*(exp (F A)*boltz A (z-x))) :=
          mul_le_mul_of_nonneg_right Hx (by have := boltz_pos A (z-x); positivity)
        _ ≤ (exp (2*d)*(b*R)) * (b*(exp (F A)*boltz A (z-x))) *
            (exp 32*boltz K (p.start M-x)) :=
          le_mul_of_one_le_right (by have := boltz_pos A (z-x); positivity) hi
        _ = _ := by unfold c V; rw [exp_add,exp_add]; ring
    · rw [ite_eq_right h,mul_zero] at Hx
      unfold U; rw [withNext_apply,Hx.antisymm (P.nonneg _),zero_mul]
      positivity
  have HUB (z : Grid M) : ∑ x : Grid M, U (x,z)*f (x,z)^N ≤
      (if D z then b else 0) * (c*(exp (-fp)*exp (-E))) := by
    split_ifs with HHz
    · calc
        _ ≤ ∑ x : Grid M, b*c*b*V z x*‖W x z‖^N := Finset.sum_le_sum fun x _ => by
          simp only [f,HHz,ite_true]
          exact mul_le_mul_of_nonneg_right (hpoint x z) (by positivity)
        _ = b*c*expU (fun x => V z x*‖W x z‖^N) := by
          unfold b expU; simp only [smul_eq_mul,Finset.mul_sum,mul_assoc]
        _ ≤ _ := by
          rw [← mul_assoc b c]; exact mul_le_mul_of_nonneg_left (hV z) (by positivity)
    · have HH : N ≠ 0 := by unfold N; omega
      simp [f,HHz,HH]
  have HM :
      (β/2)^N ≤ 4*a0/R' * (c*(exp (-fp)*exp (-E))) := calc
    _ ≤ U.Ex (fun i => f i ^ N) := he1
    _ = ∑ z, ∑ x : Grid M, U (x,z)*f (x,z)^N := by unfold Ex; rw [Fintype.sum_prod_type,Finset.sum_comm]
    _ ≤ ∑ z, (if D z then b else 0) * (c*(exp (-fp)*exp (-E))) := Finset.sum_le_sum (fun z _ => HUB z)
    _ = (uniform _).prob D * (c*(exp (-fp)*exp (-E))) := by
      rw [prob_eq]; simp_rw [uniform_side,← Finset.sum_mul]; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right (dome_prob p' H.fits a0 ha) (by positivity)
  have hrel : log R - 12 ≤ fp := (F_S_lower _ p.invlen_pos (loc_scale hp.2)).trans
    (F_mono (le_add_of_nonneg_left H.nonneg))
  have hlog := log_le_log (by positivity) HM
  unfold a0 c N at hlog
  rw [show 4*(1000/β)=(4000:ℝ)/β by ring] at hlog
  have hc' : 0 < R * exp (2*d + F A + 32) := by positivity
  rw [log_pow,Real.log_div h0.ne' (by norm_num)] at hlog
  rw [Real.log_mul (by positivity) (by positivity),Real.log_div (by positivity) hpR'.ne',
    Real.log_div (by norm_num) h0.ne', Real.log_mul hc'.ne' (by positivity),
    Real.log_mul hpR.ne' (by positivity),Real.log_mul (by positivity) (by positivity)] at hlog
  push_cast at hlog
  simp_rw [log_exp] at hlog
  change E ≤ 2*d + F A - log R' + 5000-log β+_

  nlinarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4000),log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2),
    Nat.cast_nonneg (α:=ℝ) T]

end FourierLLogL.Dyadic.Thermal

end OAI
