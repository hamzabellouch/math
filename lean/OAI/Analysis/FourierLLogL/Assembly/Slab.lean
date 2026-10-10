import OAI.Analysis.FourierLLogL.Assembly.Rail
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

/-- Depth of a sequence (no missing jumps within plateau) -/
def matrix (n : ℕ) : Path M → Prop
| [] => True
| b::l => depthB b=n ∧ matrix (n+1) l

lemma matrix_trip {x : Grid M} (l : Path M) (h : Trip x s l) :
    matrix s.here.lev l := by
  induction l generalizing s with
  | nil => exact True.intro
  | cons b l ih =>
    have He : depthB b=s.here.lev := by unfold depthB; rw [h.2.1.lower.here,h.1]
    have HH := ih h.2.2
    rw [depth_next,He] at HH; exact ⟨He,HH⟩

lemma matrix_cut (l : Path M) (n : ℕ) (k : ℕ) (h : matrix n l) :
    ∃ p q : Path M, l=p++q ∧ matrix (n+p.length) q ∧
      (∀ b∈p, depthB b < k) ∧ (∀ b∈q, k ≤ depthB b) ∧
      n+p.length = min (max n k) (n+l.length) := by
  induction l generalizing n with
  | nil => refine ⟨[],[],rfl,True.intro,?_⟩; simp
  | cons b l ih =>
    obtain ⟨hp,hq,hh,hE,h₁,h₂,h₃⟩ := ih _ h.2
    have HI : depthB b=n := h.1
    by_cases hv : n < k
    · refine ⟨b::hp,hq, by rw [hh]; rfl,?_,?_,h₂,?_⟩
      · rw [List.length_cons,show n+(List.length hp+1)=n+1+List.length hp by omega]
        exact hE
      · intro x hx; rcases List.mem_cons.mp hx with rfl|hx
        · omega
        exact h₁ _ hx
      · simp only [List.length_cons]
        omega
    · have H : hp.length=0 := by omega
      have hL : hp=[] := List.eq_nil_of_length_eq_zero H
      rw [hL,List.nil_append] at hh; cases hh
      refine ⟨[],b::l,rfl,h,fun b hb => ?_,fun z hz => ?_,?_⟩
      · simp at hb
      · rcases List.mem_cons.mp hz with rfl|hz; omega
        exact h₂ _ hz
      · simp; omega

lemma slab_on (l : Path M) (n : ℕ) (h : matrix n l) (a k : ℕ) :
    ∃ p q r : Path M, l=p++q++r ∧
      (∀ b∈p, ¬betweenS a k b) ∧ (∀ b∈r, ¬betweenS a k b) ∧
      q.length ≤ k := by
  obtain ⟨p,s,H,h₁,h₂,h₃,h₄⟩ := matrix_cut l n a h
  obtain ⟨q,r,hr,hx,hp,he,hk⟩ := matrix_cut s _ (a+k) h₁
  refine ⟨p,q,r,by rw [H,hr,List.append_assoc],fun b hi hh => ?_,fun b hi hh => ?_,?_⟩
  exact (h₂ b hi).not_ge hh.1
  exact hh.2.not_ge (he b hi)
  have ht₁ : l.length=p.length+s.length := by rw [H,List.length_append]
  have ht₂ : s.length=q.length+r.length := by rw [hr,List.length_append]
  omega

/-- quality trip coupons that cover all high nonbad jumps before activation. -/
def shades (m : Grade → ℕ) (u : Grid M) (l : Path M) (j : ℕ) :=
    ∀ g : Grade, ∀ p q : Path M, l=p++q → stall u g j l p →
      ∀ b∈p, snag g u b → betweenS (m g) (billWait g j l) b

lemma sheds {s : Scene M} {l : Path M} (h : Cast j J f s l) (u : Grid M) :
    ∃ m : Grade → ℕ, shades m u l j := by
  choose m hm using fun g => bound_stage (u:=u) l h g
  exact ⟨m,hm⟩

def stripe (a : Grade → ℕ) (g : Grade) (j : ℕ) (l : Path M) (b : Beat M) :=
    if betweenS (a g) (billWait g j l) b then (1:ℝ) else 0

lemma stripe_pos (a : Grade → ℕ) (g : Grade) (j : ℕ) (l : Path M) (b : Beat M) :
    0 ≤ stripe a g j l b := by unfold stripe; split <;> norm_num

lemma stripe_bill (a : Grade → ℕ) (g : Grade) (j : ℕ) (l : Path M) (x : Grid M)
    {s : Scene M} (h : Trip x s l) : subtotal (stripe a g j l) l ≤ billWait g j l := by
  let f := stripe a g j l
  obtain ⟨v,w,p,hl,hv,hp,hw⟩ := slab_on l _ (matrix_trip l h) (a g) (billWait g j l)
  have HF (m : Path M) (hi : ∀ b∈m, ¬ betweenS (a g) (billWait g j l) b) :
      subtotal f m=0 := by
    induction m with
    | nil => rfl
    | cons b r ih =>
      have HH : f b=0 := ite_eq_right (hi b List.mem_cons_self)
      rw [subtotal_cons,HH,ih fun y hy => hi y (List.mem_cons_of_mem _ hy),zero_add]
  have HX (m : Path M) :
      subtotal f m ≤ m.length := by
    induction m with
    | nil => simp [subtotal]
    | cons b r ih =>
      have he : f b≤ 1 := by unfold f stripe; split <;> norm_num
      rw [subtotal_cons, List.length_cons]; push_cast; linarith
  change subtotal f l ≤ _
  nth_rw 1 [hl]
  rw [subtotal_app,subtotal_app,HF v hv,HF p hp,zero_add,add_zero]
  apply (HX w).trans
  exact_mod_cast hw


lemma trim_cost (g : Beat M → ℝ) (hg : ∀ b, Ideal b.pre b.post → 0 ≤ g b)
    {x : Grid M} (l p r : Path M) (h : Trip x s (p++(l++r))) :
    subtotal g l ≤ subtotal g (p++(l++r)) := by
  rw [subtotal_app,subtotal_app]
  obtain ⟨ha,q,hq⟩ := trip_cut h
  obtain ⟨hc,t,ht⟩ := trip_cut hq
  linarith [trip_nonneg ht hg,trip_nonneg ha hg]

lemma trip_depth_limit {l : Path M} {s : Scene M} (h : Cast j J f s l) :
    s.here.lev+l.length ≤ J := by
  induction l generalizing s with
  | nil => exact (show s.Safe j J f from h).depth_ok
  | cons b l ih =>
    obtain ⟨rfl,⟨t,ht⟩,hh⟩ := h
    have hi := ih hh
    rw [List.length_cons]
    have hX := ht.2.1.1.here
    rw [depth_next,depthB,hX] at hi
    omega

end Troupe


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
