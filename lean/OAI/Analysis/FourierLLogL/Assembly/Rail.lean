import OAI.Analysis.FourierLLogL.Assembly.Phase
/-! # The uniform output path -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Paths
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical


namespace Troupe

lemma blend (l : Path M) {E : Type*} [AddCommMonoid E] (f g : Beat M → E) :
    subtotal (fun b => f b+g b) l = subtotal f l + subtotal g l := by
  induction l with
  | nil => change 0=0+(0:E); simp
  | cons b l ih => simp only [subtotal_cons,ih]; ac_rfl
lemma subtC (l : Path M) (f : Beat M → ℂ) (c : ℂ) :
    subtotal (fun b => c*f b) l=c*subtotal f l := by
  induction l with
  | nil => change 0=c*0; simp
  | cons b l ih => rw [subtotal_cons,subtotal_cons,ih,mul_add]
lemma subtR (l : Path M) (f : Beat M → ℝ) (c : ℝ) :
    subtotal (fun b => c*f b) l=c*subtotal f l := by
  induction l with
  | nil => change 0=c*0; simp
  | cons b l ih => rw [subtotal_cons,subtotal_cons,ih,mul_add]
lemma subt_constant (l : Path M) (c : ℝ) :
    subtotal (fun _ => c) l = c*l.length := by
  induction l with
  | nil => simp [subtotal]
  | cons b l ih => rw [subtotal_cons,List.length_cons,ih]; push_cast; ring
lemma subt_neg (l : Path M) (f g : Beat M → ℂ) :
    subtotal f l-subtotal g l=subtotal (fun b => f b-g b) l := by
  induction l with
  | nil => simp [subtotal]
  | cons b l ih => rw [subtotal_cons,subtotal_cons,subtotal_cons,← ih]; abel
lemma subt_norm (l : Path M) (f : Beat M → ℂ) :
    ‖subtotal f l‖ ≤ subtotal (fun b => ‖f b‖) l := by
  induction l with
  | nil => change ‖(0:ℂ)‖ ≤ 0; simp
  | cons b l ih => exact (norm_add_le (f b) _).trans (add_le_add_right ih _)

lemma trip_attend {x : Grid M} {l : Path M} (h : Trip x s l) :
    ∀ b∈l, Ideal b.pre b.post ∧ x∈b.post.here.block M ∧ |blow x b|=1 ∧
      b.post.here.below s.here ∧ dye b.post=dye s := by
  induction l generalizing s with
  | nil => simp
  | cons b l ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl|hz
    · refine ⟨h.2.1,?_,trip_final h,?_,?_⟩
      · exact block_of_below (child_below _ _) _ (trip_head h.2.2).2
      · rw [h.2.1.lower.here,h.1]; exact below_refl _
      rw [dye,h.2.1.lower.fund,h.1]; rfl
    obtain ⟨hp,hj,hi,h₁,h₂⟩ := ih h.2.2 z hz
    refine ⟨hp,hj,hi,?_,?_⟩
    · rw [← h.1,← h.2.1.lower.here]; exact below_trans h₁ (child_below _ _)
    change dye z.post=dye b.post at h₂; rw [h₂,dye,h.2.1.lower.fund,h.1]; rfl

def spaceRent (b : Beat M) := b.post.here.len
lemma length_fee {x : Grid M} {l : Path M} (h : Trip x s l) :
    subtotal spaceRent l ≤ 2*s.here.len := by
  induction l generalizing s with
  | nil => change 0 ≤ 2*_; exact mul_nonneg (by norm_num) s.here.len_pos.le
  | cons b l ih =>
    have H := ih h.2.2
    rw [show (winds b).here.len=b.post.here.len/2 from child_len _ b.bit] at H
    rw [←h.1,←h.2.1.lower.here]
    change b.post.here.len+subtotal spaceRent l ≤ _
    linarith

def aired (m : Beat M → Prop) (x u : Grid M) (b : Beat M) :=
    if m b then proceeds x u b else 0

lemma rail_fee {x : Grid M} (u v : Grid M) (μ : Beat M → Prop) (p l r : Path M)
    (h : Trip x s (p++(l++r))) :
    ‖subtotal (aired μ x u) l-chi (u-v) x*subtotal (aired μ x v) l‖ ≤
      64*s.here.len*rad (u-v) := by
  rw [← subtC,subt_neg]
  let F (b : Beat M) := aired μ x u b-chi (u-v) x * aired μ x v b
  apply (subt_norm l F).trans
  have ht := trip_cut h
  obtain ⟨hs,w,hk⟩ := ht
  obtain ⟨hL,t,hT⟩ := trip_cut hk
  have HH : subtotal (fun b => ‖F b‖) l ≤ subtotal (fun b => 32*rad (u-v)*spaceRent b) l := by
    suffices HX : ∀ l s, Trip x s l → subtotal (fun b => ‖F b‖) l ≤
        subtotal (fun b => 32*rad (u-v)*spaceRent b) l from HX _ w hL
    intro l; induction l with
    | nil => intro s h; exact le_rfl
    | cons b l ih =>
      intro s H
      rw [subtotal_cons,subtotal_cons]
      apply add_le_add _ (ih (winds b) H.2.2)
      unfold F aired; split_ifs
      · rw [proceeds,proceeds,mul_left_comm,← mul_sub,norm_scaleC,trip_final H,one_mul]
        have HC := (trip_attend H b List.mem_cons_self)
        exact (gain_point H.2.1.climb u v x HC.2.1).trans (le_of_eq (by unfold spaceRent; ring))
      · simp; exact mul_nonneg (mul_nonneg (by norm_num) (rad_nonneg _)) b.post.here.len_pos.le
  apply HH.trans
  rw [subtR]
  have hp' : subtotal spaceRent l ≤ 2*s.here.len := by
    have HH := length_fee h
    simp_rw [subtotal_app] at HH
    linarith [trip_nonneg hs (f:=spaceRent) (fun b _ => b.post.here.len_pos.le),
      trip_nonneg hT (f:=spaceRent) (fun b _ => b.post.here.len_pos.le)]
  nlinarith [rad_nonneg (u-v)]

lemma straight_fee {x : Grid M} (u : Grid M) (l : Path M)
    (h : Trip x s l) :
    ‖subtotal (proceeds x u) l‖ ≤ 4*l.length := by
  induction l generalizing s with
  | nil => change ‖(0:ℂ)‖ ≤ 4*(↑([]:Path M).length:ℝ); simp
  | cons b l ih =>
    rw [subtotal_cons,List.length_cons]; push_cast
    apply (norm_add_le _ _).trans
    have he := h.2.1.climb
    rw [proceeds,norm_scaleC,trip_final h,one_mul]
    linarith [(gain_norm he u).trans he.fit.lift,ih h.2.2]

lemma decode_track (l : Path M) (x v k : Grid M) {s : Scene M}
    (h : Trip x s l) :
    let w := subtotal (duties x v) l
    ∑ z,chi k z*w z=(cred (dye s) k:ℂ)*subtotal (proceeds x (v+k)) l := by
  induction l generalizing s with
  | nil => simp [subtotal]
  | cons b l ih =>
    have H := gain_decode b.post v k
    let C : ℂ := cred (dye b.post) k
    have HH := ih h.2.2
    intro w
    have hr : dye b.post=dye s := (trip_attend h b List.mem_cons_self).2.2.2.2
    rw [←hr]
    let t := duties x v b; let u := subtotal (duties x v) l
    have hw (z) : w z=t z+u z := rfl
    simp_rw [hw,mul_add,Finset.sum_add_distrib]
    rw [subtotal_cons,mul_add]
    congr 1
    · unfold t duties; simp_rw [mul_left_comm (chi k _),←Finset.mul_sum]
      rw [H]; unfold proceeds; ring

lemma below_decode (u v k x : Grid M) (A : Form M) (p l r : Path M)
    (h : Trip x s (p++(l++r))) (hx : A=dye s)
    (hh : delta A k ≤ 1) :
    ‖subtotal (proceeds x u) l‖ ≤
      2*Beam.yieldW (subtotal (duties x v) l)+64*s.here.len*rad (u-v-k) := by
  obtain ⟨_,q,h₁⟩ := trip_cut h
  obtain ⟨hp,d,h₂⟩ := trip_cut h₁
  let a := v+k
  let f := subtotal (proceeds x a) l; let W := subtotal (duties x v) l
  have HI : ‖f‖ ≤ 2*Beam.yieldW W := by
    by_cases ht : l=[]
    · unfold f W; rw [ht,subtotal_nil,subtotal_nil,norm_zero,Beam.yield_zero]; norm_num
    have hz := decode_track l x v k hp
    have HV : dye q=A := by
      obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil _ ht
      have hT : b∈p++(l++r) := by simp [hb]
      rw [← (trip_attend hp b hb).2.2.2.2, (trip_attend h b hT).2.2.2.2,hx]
    change ∑ z,chi k z*W z=(cred (dye q) k:ℂ)*f at hz
    rw [HV] at hz
    have hC : 1/2 ≤ cred A k := by
      nlinarith [delta_sq A k,show 0 ≤ delta A k from sqrt_nonneg _]
    have H : ‖(↑(cred A k):ℂ)*f‖ ≤ Beam.yieldW W := by
      rw [← hz]
      exact (norm_sum_le _ _).trans (by simp only [norm_mul,norm_chi,one_mul]; exact le_rfl)
    rw [norm_scaleC,abs_of_nonneg (by linarith)] at H
    nlinarith [norm_nonneg f]
  have he := rail_fee u a (fun _ => True) p l r h
  have hA (v) : aired (fun _ => True) x v=proceeds x v := by funext b; simp [aired]
  rw [hA,hA] at he
  let f' := subtotal (proceeds x u) l
  have HH : ‖f'‖ ≤ ‖f'-chi (u-a) x*f‖ + ‖f‖ := by
    have H := norm_add_le (f'-chi (u-a) x*f) (chi (u-a) x*f)
    rwa [sub_add_cancel,norm_mul,norm_chi,one_mul] at H
  rw [show u-v-k=u-a by unfold a; ring]
  change ‖f'-chi (u-a) x*f‖ ≤ _ at he
  change ‖f'‖ ≤ 2*Beam.yieldW W+_
  linarith

end Troupe


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
