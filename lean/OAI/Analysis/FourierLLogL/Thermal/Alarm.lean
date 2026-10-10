import OAI.Analysis.FourierLLogL.Thermal.Posterior

/-! # Probability cost of clone evidence under the comparison model -/
open Set Function Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Thermal
open Law Node Real Period Compress.Params

variable {M j : ℕ}
open scoped Classical

def cushion (j : ℕ) := height j/H j^100
def clones (j : ℕ) := slow j ^120

abbrev Clutch (j M : ℕ) := Grid M × (Fin (clones j) → Grid M)

def fresh (A B : Form M) (j : ℕ) (y : Grid M) : Law (Clutch j M) :=
    (channel B y).tensorP (pack (fun _ => channel A y))

namespace Update
variable {p : Node}

def consistent (_u : Update j M p) (A : Form M) (z z' : Grid M) : Prop :=
    form A (z'-z) ≤ 4*cushion j

def single (u : Update j M p) (A : Form M) (z : Grid M) (v z' : Grid M) : Prop :=
    u.consistent A z z' ∧ beta u.ix /4 ≤ ‖u.app v z'‖

def alarm (u : Update j M p) (A : Form M) (z : Grid M) (x : Clutch j M) : Prop :=
    ∃ i, u.single A z x.1 (x.2 i)


def alarmQ (u : Update j M p) (A : Form M) (z y : Grid M) :=
    (fresh A (u.next A) j y).prob (u.alarm A z)

def singleQ (u : Update j M p) (A : Form M) (z y : Grid M) :=
    (channel (u.next A) y).Ex fun v => (channel A y).prob (u.single A z v)

lemma alarm_le (u : Update j M p) (A : Form M) (z y : Grid M) :
    alarmQ u A z y ≤ clones j * singleQ u A z y := by
  classical
  let T := clones j
  let L := fresh A (u.next A) j y
  let F (i : Fin T) (w : Clutch j M) : ℝ := if u.single A z w.1 (w.2 i) then 1 else 0
  have hi (i : Fin T) : L.Ex (F i) = u.singleQ A z y := by
    unfold L fresh F singleQ prob; rw [Ex_tensorP]
    refine congrArg _ (funext fun v => ?_)
    let f (z' : Grid M) := if u.single A z v z' then (1:ℝ) else 0
    exact Ex_pack_proj (fun _ => channel A y) i f
  unfold alarmQ prob; apply le_trans (b:=L.Ex (fun w => ∑ i, F i w))
  · apply Ex_mono
    intro w
    split_ifs with H
    · obtain ⟨i,hi⟩ := H
      have HE := Finset.single_le_sum (f:=fun i => F i w) (fun i _ => by
        unfold F; split_ifs <;> norm_num) (Finset.mem_univ i)
      rwa [show F i w=1 from ite_eq_left hi] at HE
    exact Finset.sum_nonneg fun i _ => by unfold F; split_ifs <;> norm_num
  rw [Ex_finset_sum]
  simp_rw [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin,nsmul_eq_mul]
  exact le_rfl

lemma shift_app (u : Update j M p) (x y z : Grid M) :
    u.app (x+y) z = ply (snap_le (M:=M) j p) u.V
      (fun i => u.v i z * chi (raise (snap_le (M:=M) j p) i) y) x := by
  unfold app ply
  refine congrArg _ ?_; funext i
  rw [chi_add]; ring

private lemma one_moment {A : Form M} {p : Node} (hp : p.ok M) (hA : 0 ≤ A)
    {P : Law (Grid M)} {C : ℝ} (u : Update j M p) (HG : u.Good C A P) (HR : u.regular)
    (s : Profile M) (hS : ∀ i∈s, 0 ≤ i.1)
    (HH : A+place p M + mixForm s ≤ tilde (H j) A p)
    (z' d : Grid M) :
    expU (fun y => prefixE s p y * boltz A (z'-y) * ‖u.app (y+d) z'‖^(2*sLen j)) ≤
      exp (32 -F (A+place p M)-u.credit/4) := by
  let t := p.start M
  let B := place p M; let U := A+B; let V := tilde (H j) A p
  let W : Profile M := (B,t)::(A,z')::s
  have he (y : Grid M) : prefixE s p y * boltz A (z'-y) ≤ exp 32 * tune W y := by
    unfold prefixE; split_ifs with hi
    · have H : form B (t-y) ≤ 32 := place_internal (start_mem hp.1 hp.2) hi
      have HH : 1 ≤ exp 32 * boltz B (t-y) := by unfold boltz; rw [← exp_add]; apply one_le_exp; linarith
      unfold W; rw [tune_cons,tune_cons]
      have hx : 0 ≤ tune s y * boltz A (z'-y) := mul_nonneg (tune_pos _ _).le (boltz_pos _ _).le
      apply le_trans (le_mul_of_one_le_left hx HH)
      exact le_of_eq (by ring)
    · rw [zero_mul]
      exact mul_nonneg (exp_nonneg _) (tune_pos _ _).le
  let f (i) := u.v i z' * chi (raise (snap_le (M:=M) j p) i) d
  have hf (i) : ‖f i‖ ≤ 1 := by
    unfold f; rw [norm_mul,norm_chi,mul_one]; exact HG.unit _ _
  have hi (i : Grid M) : ‖expU (fun y => (↑(tune W y):ℂ)*chi i y)‖ ≤ exp (-F U)*cred V i := by
    have HB := place_valid p M
    rw [expU_coeff (fun y => (↑(tune W y):ℂ))]
    apply le_trans (profile_envelope (s:=W) ?_ _)
    · rw [q_even _ _]
      have Heq : mixForm W = U+mixForm s := by unfold W U; rw [mix_cons,mix_cons]; abel
      rw [Heq]
      exact q_compare (add_nonneg hA HB) (le_add_of_nonneg_right (mix_nonneg hS)) HH _
    intro z hz
    simp only [W,List.mem_cons] at hz
    rcases hz with hh|hh|hh <;>
      first | exact hS z hh | (subst z; first | exact HB | exact hA)
  have hN := weighted_envelope (sLen j) (snap_le _ _) V u.V f hf (tune W) _ hi
  let T := sLen j
  calc
    _ ≤ exp 32 * expU (fun y => tune W y * ‖u.app (y+d) z'‖^(2*T)) := by
      rw [expU_ex,expU_ex,← Ex_lmul]; apply Ex_mono; intro x
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (he x) (by positivity)
    _ = exp 32 * expU (fun y => tune W y * ‖ply (snap_le _ _) u.V f y‖^(2*T)) := by
      simp only [shift_app]; rfl
    _ ≤ exp 32*(exp (-F U)*HeatM (snap_le _ _) V u.V T) :=
      mul_le_mul_of_nonneg_left hN (exp_nonneg _)
    _ ≤ _ := by
      rw [← heat_exp,← exp_add,← exp_add]; apply exp_monotone
      have H : u.credit/4 ≤ levelCost (snap_le _ _) V u.V T := HG.evidence HR
      unfold U B; linarith

private lemma consistent_length (u : Update j M p) (z : Grid M) (A : Form M) :
    (uniform (Grid M)).prob (u.consistent A z) ≤ exp (4*cushion j-F A) := by
  unfold consistent
  rw [prob_translate (fun w => form A w ≤ 4*cushion j)]
  unfold prob
  let f := 4*cushion j
  have hi : (uniform _).Ex (fun w => exp (-f)*(if form A w ≤ 4*cushion j then 1 else 0)) ≤
      q A 0 := by
    rw [q_origin,expU_ex]; refine Ex_mono _ fun i => ?_
    split_ifs with H
    · rw [mul_one]; exact exp_monotone (neg_le_neg H)
    rw [mul_zero]; exact (boltz_pos _ _).le
  rw [Ex_lmul,← F_origin] at hi

  refine le_of_mul_le_mul_left ?_ (exp_pos (-f))
  rw [← exp_add]
  rw [show -f+(4*cushion j-F A)=-F A by unfold f; ring]
  simpa only using hi

theorem one_clone_tail {A : Form M} {p : Node} (hp : p.ok M) (hA : 0 ≤ A)
    {P : Law (Grid M)} {C : ℝ} (u : Update j M p) (HG : u.Good C A P) (HR : u.regular)
    (s : Profile M) (hS : ∀ i∈s, 0 ≤ i.1)
    (HH : A+place p M + mixForm s ≤ tilde (H j) A p) (z : Grid M) :
    (beta u.ix/4)^(2*sLen j) * expU (fun y => prefixE s p y * singleQ u A z y) ≤
      exp (32 - F (A+place p M)-u.credit/4+4*cushion j) := by
  let f := prefixE s p
  let L := label (u.next A)
  let V := uniform (Grid M)
  let b := beta u.ix/4
  let N := 2*sLen j
  let M0 := fun y d => u.single A z (y+d)
  let S := fun z' : Grid M => if u.consistent A z z' then (1:ℝ) else 0
  have he (y : Grid M) : b^N * (f y*singleQ u A z y) ≤ exp (F A) *
      L.Ex (fun d => V.Ex fun z' => S z' * (f y * boltz A (z'-y) * ‖u.app (y+d) z'‖^N)) := by
    unfold singleQ; rw [ch_ex]
    have hc (y z : Grid M) : channel A y z = exp (F A) * (V z * boltz A (z-y)) := by
      rw [ch_K,K_eq,boltz,show V z = side M from uniform_side z,
        sub_eq_add_neg,exp_add]
      ring
    rw [← mul_assoc]
    change (b^N*f y)*L.Ex _ ≤ _
    simp_rw [← Ex_lmul L]
    refine Ex_mono _ fun d => ?_
    unfold prob Ex
    rw [Finset.mul_sum,Finset.mul_sum]
    refine Finset.sum_le_sum fun z' _ => ?_
    have hp := prefixE_nonneg s p y
    change 0 ≤ f y at hp
    dsimp
    split_ifs with H
    · unfold S; obtain ⟨h1,h2⟩ := H
      simp only [ite_eq_left h1,mul_one,one_mul]
      have hf : b^N ≤ ‖u.app (y+d) z'‖^N :=
        pow_le_pow_left₀ (by have := beta_pos u.ix; positivity) h2 _
      convert mul_le_mul_of_nonneg_left hf
        (mul_nonneg hp ((channel A y).nonneg z')) using 1 <;>
        (simp only [hc]; ring)
    rw [mul_zero,mul_zero]
    unfold S
    split_ifs <;> (have := V.nonneg z'; have := boltz_pos A (z'-y); positivity)
  let E := 32-F (A+place p M)-u.credit/4
  have hm (d z' : Grid M) :
      V.Ex (fun y => f y * boltz A (z'-y) * ‖u.app (y+d) z'‖^N) ≤ exp E := by
    unfold V; rw [←expU_ex]
    exact one_moment hp hA u HG HR s hS HH z' d
  rw [expU_ex]; change b^N * V.Ex (fun y => f y * u.singleQ A z y) ≤ _
  rw [← Ex_lmul]
  apply le_trans (V.Ex_mono he)
  rw [Ex_lmul,Ex_swap V L]
  have hiD (d : Grid M) :
      V.Ex (fun y => V.Ex fun z' => S z' * (f y * boltz A (z'-y) * ‖u.app (y+d) z'‖^N))
        ≤ exp (4*cushion j-F A)*exp E := by
    rw [Ex_swap V V]; simp_rw [Ex_lmul]
    apply le_trans (b:=V.Ex fun z' => S z'*exp E)
    · exact V.Ex_mono fun z' => mul_le_mul_of_nonneg_left (hm d z') (by unfold S; split_ifs <;> norm_num)
    rw [Ex_mul]
    have hC : V.Ex S = V.prob _ := rfl
    exact mul_le_mul_of_nonneg_right (hC.le.trans (consistent_length u z A)) (exp_nonneg E)
  calc
    _ ≤ exp (F A)*L.Ex (fun _ => exp (4*cushion j-F A)*exp E) :=
      mul_le_mul_of_nonneg_left (L.Ex_mono hiD) (exp_nonneg _)
    _ = _ := by rw [Ex_const,←exp_add,←exp_add]; unfold E; congr 1; ring

end Update
end FourierLLogL.Dyadic.Thermal

end OAI
