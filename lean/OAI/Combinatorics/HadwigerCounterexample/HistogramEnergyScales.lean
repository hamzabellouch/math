import OAI.Combinatorics.HadwigerCounterexample.RepeatedQueryEnergy
import OAI.Combinatorics.HadwigerCounterexample.TemplateTypicality

namespace OAI

/-! # Histogram Energy Scales -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Filter
open scoped BigOperators Topology
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]

theorem log_thrift (r : ℝ) (hr : 0≤r) :
    ∀ᶠ l : ℕ in atTop,r * Real.log ((l:ℝ)+1)≤(l:ℝ) := by
  have h2 := Real.log_pos (x:=2) (by norm_num)
  let a := (1:ℝ)/(log 2*(r+1))
  have hr' : 0<r+1 := by linarith
  have ha : 0<a := by positivity
  filter_upwards [bp_poly_dom_nat ha 2 1,eventually_ge_atTop 1] with l hl hl'
  have hi : 1 ≤ (l:ℝ) := by exact_mod_cast hl'
  simp only [pow_one] at hl
  have he := Real.log_le_log (x:=(l:ℝ)+1) (by positivity)
    (le_trans (show (l:ℝ)+1≤2*l by linarith) hl.le)
  rw [log_bp] at he
  have ht : (r+1)*(a*l*log 2)=l := by unfold a; field_simp
  have hx := mul_le_mul_of_nonneg_left he hr'.le
  rw [ht] at hx
  have hz : 0≤ log ((l:ℝ)+1) := Real.log_nonneg (by linarith)
  linarith

theorem div_grows (d : ℕ) (hd : 0<d) :
    Tendsto (fun n : ℕ => n / d) atTop atTop := tendsto_atTop.mpr fun b =>
  (eventually_ge_atTop (b*d)).mono fun _ h => (Nat.le_div_iff_mul_le hd).mpr h

structure TollBar (M : ℕ) (C : ℝ) (I J G : Type) [Fintype I] [Fintype J]
    [Fintype G] [DecidableEq G] (g : Route J G) (n l : ℕ)
    (r u E V : ℝ) : Prop where
  pos : 0<l
  frame : ∀ i : G, 2*num (Port (tied g (Fin l)) i)-↑(M*n) ≤ -1
  peak : peakExpense (Fin l) J 1+ (-(↑(M*n):ℝ)/2+2*u) ≤0
  cap :
    bp (C*(M*n:ℕ))*( (4:ℝ)^Fintype.card G *bp (num (Fin l)*num J*num J) *
      (num (Fin l × J)+1)) ≤ bp (E*l)
  charge :
    r*log ((l:ℝ)+1)+(E*l + bp (num (Fin l)*num I - n)*u*l+1)*log 2 ≤
      l*V

set_option maxHeartbeats 800000 in
theorem toll_calendar (M : ℕ) (hM : 1≤M) (C : ℝ) (hC : 0≤C)
    (I J G : Type) [Fintype I] [Fintype J]
    [Fintype G] [DecidableEq G] (g : Route J G) :
    ∃ (s : ℕ) (E V : ℝ), 0<s ∧ 0≤E ∧
    ∀ r u : ℝ, 0≤r→0≤u →
      ∀ᶠ n : ℕ in atTop,TollBar M C I J G g n (n / s) r u E V := by
  classical
  let a := num I; let b := num J
  let d := 2*((1+2*b)*b)
  have ha : 0≤a := Nat.cast_nonneg _
  have hb : 0≤b := Nat.cast_nonneg _
  have hd : 0 ≤ d := by positivity
  obtain ⟨s,hs⟩ := exists_nat_gt (1+4*(a+b+d))
  have hs' : 0<s := by exact_mod_cast (show (0:ℝ)<s from by linarith)
  have hi : (1:ℝ)≤M := by exact_mod_cast hM
  let E := C*(M*2*s)+b*b+1
  have hM' : (0:ℝ)≤M := by positivity
  have hE : 0 ≤ E := by positivity
  let V := 1+(E+2)*log 2
  refine ⟨s,E,V,hs',hE,fun r u hr hu => ?_⟩
  have ht := div_grows s hs'
  let B := (4:ℝ)^Fintype.card G
  filter_upwards [ht.eventually (eventually_ge_atTop 1),
    ht.eventually (bp_poly_dom_nat (a:=1) (by norm_num) (B*(b+1)) 1),ht.eventually
    (log_thrift r hr),ht.eventually ((tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
      (eventually_ge_atTop (max 2 (8*u)))),pay_nat (a:=1/2) u (b:=0) (by norm_num)]
    with n hl hG hr hpeak hU
  let l := n/s
  have hl' : 1≤(l:ℝ) := by exact_mod_cast hl
  have hsl : (s:ℝ)*l ≤ n := by
    rw [mul_comm]; exact_mod_cast Nat.div_mul_le_self n s
  have hnl : (n:ℝ) ≤ 2*s*l := by
    have h := Nat.lt_mul_div_succ n hs'
    change n<s*(l+1) at h
    have h1 : (n:ℝ)≤s*((l:ℝ)+1) := by exact_mod_cast h.le
    nlinarith only [h1,mul_le_mul_of_nonneg_left hl' (Nat.cast_nonneg (α:=ℝ) s)]
  have hx : (n:ℝ) ≤ ↑(M*n) := by
    exact_mod_cast (show n ≤ M*n from by nlinarith)
  change max 2 (8*u)≤ (l:ℝ) at hpeak
  have hh1 := mul_le_mul_of_nonneg_right hs.le (Nat.cast_nonneg l : 0≤(l:ℝ))
  have hq :
      num (Fin l)=(l:ℝ) ∧ num (Fin l × J)=(l:ℝ)*b := by simp [num,b]
  constructor
  · exact hl
  · intro i
    change 2*num (Port (tied g (Fin l)) i)-↑(M*n) ≤ -1
    have hg := port_limit (tied g (Fin l)) i
    rw [hq.2] at hg
    nlinarith only [hg,hx,hsl,hl',hh1,
      mul_nonneg ha (Nat.cast_nonneg l : 0≤(l:ℝ)),
      mul_nonneg hb (Nat.cast_nonneg l : 0≤(l:ℝ)),
      mul_nonneg hd (Nat.cast_nonneg l : 0≤(l:ℝ))]
  · have he : peakExpense (Fin l) J 1=d*l := by unfold peakExpense d b; rw [hq.1]; norm_num; ring
    change peakExpense (Fin l) J 1+ _ ≤ _
    rw [he]
    nlinarith only [hh1,hsl,hx, (max_le_iff.mp hpeak).2,
      mul_nonneg ha (Nat.cast_nonneg l : 0≤(l:ℝ)),
      mul_nonneg hb (Nat.cast_nonneg l : 0≤(l:ℝ)),
      mul_nonneg hd (Nat.cast_nonneg l : 0≤(l:ℝ)), Nat.cast_nonneg (α:=ℝ) l]
  · change bp _ * (B *bp (num (Fin l)*b*b) * (num (Fin l×J)+1)) ≤ bp (E*l)
    have hg : B*(num (Fin l×J)+1) ≤ bp l := by
      change B*(b+1)*(l:ℝ)^1 < bp (1*l) at hG
      simp only [hq.2]; rw [pow_one,one_mul] at hG
      refine le_trans ?_ hG.le
      exact (mul_le_mul_of_nonneg_left (show (l:ℝ)*b+1≤(b+1)*l by linarith only [hl'])
        (by positivity)).trans_eq (Eq.symm (mul_assoc _ _ _))
    have he : C*(↑(M*n):ℝ) ≤ C*(M*2*s)*l := by
      rw [Nat.cast_mul]
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnl hM') hC).trans_eq (by ring)
    rw [show E*l=C*(M*2*s)*l+num (Fin l)*b*b+l by rw [hq.1]; unfold E; ring,bp_add,bp_add]
    let D := num (Fin l)*b*b
    calc bp _*_ = (bp (C*↑(M*n))*bp D)*(B*(num (Fin l×J)+1)) := by unfold D; ring
         _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (bp_le he) (bp_pos D).le) hg
           (by unfold B num; positivity) (mul_nonneg (bp_pos _).le (bp_pos D).le)

  · change r*log ((l:ℝ)+1)+_ ≤ (l:ℝ)*V
    have hz : bp (num (Fin l)*num I-n)*u≤1 := by
      have he : (l:ℝ)*a-n≤ -(1/2:ℝ)*n := by
        nlinarith only [hh1,hsl,mul_nonneg hb (Nat.cast_nonneg l : 0≤(l:ℝ)),
          mul_nonneg hd (Nat.cast_nonneg l : 0≤(l:ℝ)),Nat.cast_nonneg (α:=ℝ) l]
      rw [hq.1,mul_comm (bp _) u]
      exact (mul_le_mul_of_nonneg_left (bp_le he) hu).trans (by simpa using hU)
    have hh :
        (E*l+bp (num (Fin l)*num I-n)*u*l+1)*log 2 ≤ ((E+2)*l)*log 2 :=
      mul_le_mul_of_nonneg_right (by
        have hmul := mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg l : 0≤(l:ℝ))
        linarith only [hl',hmul]) (Real.log_pos (x:=2) (by norm_num)).le
    change r*log ((l:ℝ)+1)≤l at hr
    exact (add_le_add hr hh).trans_eq (by unfold V; ring)

end HadwigerCounterexample

end

end OAI
