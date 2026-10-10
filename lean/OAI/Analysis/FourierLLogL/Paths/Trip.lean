import OAI.Analysis.FourierLLogL.Snapshot.Activate
/-! # The uniform output path -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Paths
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical


abbrev Path (M : ℕ) := List (Beat M)

def winds (b : Beat M) := b.post.smaller b.bit
def curl (b : Bool) : ℝ := if b=true then -1 else 1

lemma curl_unit (b : Bool) : |curl b|=1 := by cases b <;> norm_num [curl]
lemma curl_sq (b : Bool) : (curl b)^2=1 := by cases b <;> norm_num [curl]
lemma fair_av (f : Bool→ℝ) : (uniform Bool).Ex f = (f false+f true)/2 := by
  simp only [Ex,Fintype.sum_bool,uniform_apply,Fintype.card_bool,Nat.cast_ofNat]
  ring

structure Fit (s : Scene M) : Prop where
  ready : ReadyAt s
  pos : 0 < s.norm
  lift : share s ≤ 4

structure Climb (s : Scene M) : Prop where
  fit : Fit s
  deep : s.here.lev < M
  tight : share s ≤ 2

structure Ideal (pre post : Scene M) : Prop where
  fit : Fit pre
  climb : Climb post
  lower : Less pre post

lemma jump_ideal {k} (h : Following j J f (.ran s q k))
    (hq : share s ≤ 4) : Ideal s q := by
  obtain ⟨ha,hb,hc,hd,he,hk⟩ := h
  obtain ⟨hz,hH⟩ := share_small hd
  refine ⟨⟨⟨ha.within,ha.positive⟩,hb.1.flat ▸ hz,hq⟩,?_,hb.1⟩
  exact ⟨⟨⟨hc.within,hc.positive⟩,hz,hH.trans (by norm_num)⟩,(rooted _ (hk false)).within.2,hH⟩

lemma Climb.child {q : Scene M} (h : Climb q) (b) : Fit (q.smaller b) :=
  let hx := h.fit.ready
  ⟨⟨q.here.child_ok hx.1.1 h.deep b,hx.2⟩,h.fit.pos,
    share_child q hx.1.1 h.deep hx.2 h.fit.pos h.tight b⟩

lemma Ideal.kill_eq {B : Beat M} (h : Ideal B.pre B.post) :
    killed B = share B.pre-share B.post := by
  rw [killed,sub_div]; unfold share; rw [h.lower.flat]
lemma Ideal.kill_nonneg {B : Beat M} (h : Ideal B.pre B.post) :
    0 ≤ killed B := div_nonneg (sub_nonneg.mpr
      (h.lower.mass_le h.fit.ready.2 h.fit.ready.1)) h.fit.pos.le

/-- deterministic integrity along a plateau list. -/
def Trip (x : Grid M) (s : Scene M) : Path M → Prop
  | [] => Fit s ∧ x∈s.here.block M
  | b::l =>
    b.pre=s ∧ Ideal b.pre b.post ∧ Trip x (winds b) l

lemma trip_head {x : Grid M} {l : Path M} (h : Trip x s l) :
    Fit s ∧ x∈s.here.block M := by
  induction l generalizing s with
  | nil => exact h
  | cons b l ih =>
    obtain ⟨rfl,ha,hb⟩ := h
    refine ⟨ha.fit,?_⟩
    have hi := (ih hb).2
    rw [← ha.lower.here]
    exact block_of_below (child_below _ _) _ hi

lemma stream_child {s q : Scene M} {x : Grid M} (h : Less s q) (hx : x∈s.here.block M) :
    x ∈ (q.smaller ((step q).bit x)).here.block M := by
  change x ∈ (child q.here _).block M
  let b (x : Grid M) := decide (x∈q.here.R.block M)
  change x ∈ (child q.here (b x)).block M
  by_cases HH : x∈q.here.R.block M
  · rw [show b x=true from decide_eq_true HH]; exact HH
  · rw [show b x=false from decide_eq_false HH]
    rw [← h.here,block_union] at hx
    exact hx.resolve_right HH

lemma trip_stream {x : Grid M} (t : Thread M s) (h : t.Following j J f)
    (hf : Fit s) (hx : x∈s.here.block M) : Trip x s (stream t x) := by
  induction t with
  | blank => exact ⟨hf,hx⟩
  | ran s q k ih =>
    have H := jump_ideal h hf.lift
    let b := (step q).bit x
    exact ⟨rfl,H,ih b (h.2.2.2.2.2 b) (H.climb.child b) (stream_child H.lower hx)⟩

lemma trip_cut {x : Grid M} {l r : Path M} (h : Trip x s (l++r)) :
    Trip x s l ∧ ∃ s, Trip x s r := by
  induction l generalizing s with
  | nil => exact ⟨trip_head h,⟨_,h⟩⟩
  | cons b l ih =>
    obtain ⟨rfl,hh,hk⟩ := h
    obtain ⟨h₁,h₂⟩ := ih hk
    exact ⟨⟨rfl,hh,h₁⟩,h₂⟩

lemma heav_bit (p : Node) (b : Bool) (x : Grid M) (h : x∈(p.child b).block M) :
    p.Hi (pos x)=curl b := by cases b; exact p.Hi_L h; exact p.Hi_R h

lemma Gi_half (p : Node) (b : Bool) (x : Grid M) (h : x∈(p.child b).block M) :
    p.Gi (pos x)=curl b * (p.child b).Hi (pos x) := by
  rw [Gi_eq]
  have H := Set.disjoint_left.mp (p.block_separate M)
  cases b
  · rw [p.R.Hi_out (show x ∉ p.R.block M from H h)]
    change _=1*p.L.Hi (pos x); ring
  · rw [p.L.Hi_out (show x∉ p.L.block M from fun H' => H H' h)]
    change _= -1*p.R.Hi (pos x); ring

def blow (x : Grid M) (b : Beat M) := b.post.here.Gi (pos x)

lemma trip_delay {x : Grid M} {c d : Beat M} {l : Path M}
    (h : Trip x s (c::d::l)) : blow x c=curl c.bit*curl d.bit := by
  have hx := (trip_head h.2.2).2
  obtain ⟨ha,hb,hH,hd,he⟩ := h
  have hE : (c.post.here.child c.bit)=d.post.here := by
    change (winds c).here=_
    rw [← hH,hd.lower.here]
  unfold blow; rw [Gi_half _ _ _ hx,hE]
  rw [heav_bit _ _ _ (trip_head he).2]

lemma trip_final {x : Grid M} {b : Beat M} {l : Path M}
    (h : Trip x s (b::l)) : |blow x b|=1 := by
  have hx := (trip_head h.2.2).2
  unfold blow; rw [Gi_half _ _ _ hx,abs_mul,curl_unit,one_mul]
  let p := (winds b).here
  change x ∈ p.block M at hx
  change |p.Hi (pos x)|=1
  rw [block_union] at hx
  rcases hx with hx|hx
  · rw [p.Hi_L hx]; norm_num
  · rw [p.Hi_R hx]; norm_num

def subtotal {E : Type*} [AddMonoid E] (f : Beat M→E) (l : Path M) := (l.map f).sum

lemma subtotal_nil {E : Type*} [AddMonoid E] (f : Beat M→E) : subtotal f [] = 0 := rfl
lemma subtotal_cons {E : Type*} [AddMonoid E] (f : Beat M→E) (b : Beat M) (l : Path M) :
    subtotal f (b::l)=f b+subtotal f l := rfl
lemma subtotal_app {E : Type*} [AddMonoid E] (f : Beat M→E) (l r : Path M) :
    subtotal f (l++r)=subtotal f l+subtotal f r := by simp only [subtotal, List.map_append,List.sum_append]

lemma trip_subtotal {x : Grid M} {f g : Beat M → ℝ} {l : Path M}
    (h : Trip x s l) (hp : ∀ b, Ideal b.pre b.post → f b ≤ g b) :
    subtotal f l ≤ subtotal g l := by
  induction l generalizing s with
  | nil => simp only [subtotal_nil,le_refl]
  | cons b l ih => exact add_le_add (hp b h.2.1) (ih h.2.2)
lemma trip_nonneg {x : Grid M} {f : Beat M → ℝ} {l : Path M}
    (h : Trip x s l) (hp : ∀ b, Ideal b.pre b.post → 0 ≤ f b) :
    0 ≤ subtotal f l := by
  induction l generalizing s with
  | nil => exact le_rfl
  | cons b l ih => exact add_nonneg (hp _ h.2.1) (ih h.2.2)

def fullKills (l : Path M) := subtotal killed l

lemma trip_K {x : Grid M} {l : Path M} (h : Trip x s l) : 0 ≤ fullKills l :=
    trip_nonneg h (fun _ H => H.kill_nonneg)


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
