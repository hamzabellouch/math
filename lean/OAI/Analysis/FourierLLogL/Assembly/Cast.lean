import OAI.Analysis.FourierLLogL.Assembly.Receipt
/-! # The uniform output path -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Paths
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical


namespace CastShow
open Troupe

def tailE (s : Scene M) (J : ℕ) (x u : Grid M) :=
  ∑ n ∈ Finset.Ico s.here.lev J, ∑ k ∈ Finset.range (2^n),
    FinJump ⟨n,k⟩ (finMod s.wage u) x

private lemma lone (s : Scene M) (p : Node) (hv : p.valid) (x u : Grid M) (h : x∈p.block M) :
    ∑ k∈Finset.range (2^p.lev), FinJump ⟨p.lev,k⟩ (finMod s.wage u) x = FinJump p (finMod s.wage u) x := by
  rw [Finset.sum_eq_single p.ix]
  · intro b hb hh
    rw [FinJump, Gi_out _ (show pos x∉ Node.cells ⟨p.lev,b⟩ from by
      intro H
      exact Set.disjoint_left.mp (cells_dis hh) H h),zero_smul]
  intro H; exact (H (Finset.mem_range.mpr hv)).elim

lemma tail_move {s : Scene M} (x u : Grid M) (hh : s.here.valid)
    (hp : s.here.lev < J) (h : x∈s.here.block M) (b : Bool) :
    tailE s J x u=FinJump s.here (finMod s.wage u) x+tailE (s.smaller b) J x u := by
  unfold tailE
  let f (n) := ∑ k∈Finset.range (2^n),FinJump ⟨n,k⟩ (finMod s.wage u) x
  let n := s.here.lev
  have he : Finset.Ico s.here.lev J=insert n (Finset.Ico (n+1) J) := by
    ext i; simp only [Finset.mem_insert,Finset.mem_Ico,n]; omega
  rw [he,Finset.sum_insert (by simp),lone s s.here hh x u h]
  cases b <;> rfl

lemma tail_attempt {s : Scene M} (v : Update j M s.here) (x u : Grid M) (J : ℕ) :
    tailE s J x u=tailE (s.lose v) J x u + tailE (s.win v) J x u := by
  let f := finMod s.wage u; let g := finMod (s.lose v).wage u
  let w := finMod (s.win v).wage u
  have H : f=g+w := by
    funext i
    unfold f g w lose win finMod; simp only [Pi.add_apply]
    by_cases HH : v.take s.fund.mood i
    all_goals simp [HH]
  have HV (p : Node) :
      FinJump p (finMod s.wage u) x=FinJump p g x+FinJump p w x := by
    unfold FinJump
    have Hx (x : Grid M) : finMod s.wage u x=g x+w x := congrFun H x
    simp_rw [Hx,smul_add,avg_sum,Finset.sum_add_distrib,smul_add]
  unfold tailE; simp_rw [HV,Finset.sum_add_distrib]; rfl

lemma tail_fail (s : Scene M) (u x : Grid M) (h : Safe s j J f)
    (hp : finGood (cutoff j) J f x) (hh : x∈s.here.block M)
    (ht : ¬s.openHere j J f) :
    tailE s J x u=0 := by
  by_cases hb : s.here.lev < J
  · have hx := hp s.here h.within.1 hb hh
    have he : s.mass=0 := le_antisymm (le_of_not_gt (fun hv => ht ⟨hb,hx,hv⟩)) h.mass_lower
    have H (i) (hf : i∈s.here.block M) : s.wage i=0 := by
      have HE := mass_actor (s:=s) h.within h.positive i
      rw [he,zero_mul] at HE
      exact (mul_eq_zero.mp HE.symm).resolve_left ((dice_positive h.within).2 hf).ne'
    unfold tailE; apply Finset.sum_eq_zero; intro n hn
    apply Finset.sum_eq_zero; intro k hk
    let p := Node.mk n k
    by_cases hm : x∈p.block M
    · have HI (y : Grid M) (hy : y∈p.block M) : finMod s.wage u y=0 := by
        unfold finMod; rw [H y]; simp
        have hf := coarse_const (Finset.mem_Ico.mp hn).1 (q:=p) (p:=s.here) (x:=pos x) (y:=pos y) hm hy
        exact hf.mp hh
      rw [FinJump,avg_sum]
      rw [Finset.sum_eq_zero (fun i hi => by rw [HI _ ((mem_group _ _).1 hi),smul_zero])]
      simp
    · rw [FinJump, Gi_out p hm,zero_smul]
  · unfold tailE; simp [Finset.Ico_eq_empty hb]

lemma FinJump_align (s : Scene M) (hv : s.here.valid) (hm : s.here.lev < M)
    (he : 0 < s.norm) (u x : Grid M) :
    FinJump s.here (finMod s.wage u) x=
      (s.norm:ℂ)*proceeds x u (Thread.Beat.mk s s ((step s).bit x)) := by
  let p := s.here; let f := finMod s.wage u
  let g (y : Grid M) := p.Hi (pos y) • f y
  have H (b : Bool) :
      (p.child b).avg g=((curl b:ℝ)*s.norm:ℝ)*scalar (s.smaller b) u := by
    rw [avg_cx (child_ok p hv hm b)]
    unfold Cx scalar; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    let q := p.child b
    by_cases hh : i∈q.block M
    · change (q.dice M i:ℂ)*g i=(((curl b*s.norm:ℝ):ℝ):ℂ)*((↑(wt q s.wage s.norm i):ℂ)*_)
      unfold g p wt
      rw [heav_bit _ _ _ hh,Complex.real_smul]
      have HR : (s.norm:ℂ) ≠ 0 := by exact_mod_cast he.ne'
      unfold f finMod
      push_cast; field_simp
    have hx : q.dice M i=0 := by rw [dice_apply (child_ok p hv hm b),ite_eq_right hh]
    have hi : wt (s.smaller b).here (s.smaller b).wage (s.smaller b).norm i=0 := by
      unfold wt; rw [show (s.smaller b).here=q from rfl,hx]; simp
    rw [hx,hi]; simp
  rw [FinJump, Complex.real_smul]
  have hi : p.avg g=(s.norm:ℂ)*gain s u := by
    rw [avg_split_complex]
    rw [show p.L=p.child false from rfl,show p.R=p.child true from rfl,H,H]
    unfold gain; simp only [curl,Bool.false_eq_true,↓reduceIte]; push_cast
    ring
  change (p.Gi (pos x):ℂ)*p.avg g=_*((p.Gi (pos x):ℂ)*_)
  rw [hi]; ring

/-- Payment from the already open plateau, without its children plateaus. -/
def ordinary (u x : Grid M) (t : Play j M s) :=
    (s.norm:ℂ)*subtotal (proceeds x u) ((project t).stream x)

def summons (u x : Grid M) {s : Scene M} (t : Play j M s) : ℂ := match t with
| .rest _ => 0
| .ticket _ t => ordinary u x t + summons u x t
| .freeze _ t => summons u x t
| .attempt _ _ l r => summons u x l+summons u x r
| .jump s l r => if (step s).bit x then summons u x r else summons u x l

lemma ordinary_jump (s : Scene M) (l : Play j M (s.smaller false)) (r : Play j M (s.smaller true)) (u x : Grid M) :
    let b := (step s).bit x
    ordinary u x (.jump s l r)=(s.norm:ℂ)*proceeds x u ⟨s,s,b⟩+
      if b=true then ordinary u x r else ordinary u x l := by
  intro b
  unfold ordinary b
  simp only [project,stream,subtotal_cons]
  cases (step s).bit x <;>
    simp only [smaller,Bool.false_eq_true,↓reduceIte,mul_add]

/-- common bit selection is correct for the shifted Haar step -/
lemma stage_shift (s : Scene M) (t : Play j M s) (u x : Grid M)
    (h : t.Follows J f) (hp : x∈ s.here.block M)
    (hh : finGood (cutoff j) J f x) : tailE s J x u=ordinary u x t+summons u x t := by
  induction t with
  | rest s =>
    rw [tail_fail s u x h.1 hh hp h.2]
    unfold ordinary; simp [project,stream,subtotal,summons]
  | ticket s t ih =>
    have HH := ih h.2.2.2.2 hp
    change tailE s.reset _ _ _ = _
    rw [HH]
    simp [ordinary,project,stream,subtotal,summons]
  | freeze s t ih =>
    have H := ih h.2.2.2 hp
    change tailE s.out _ _ _ = _
    rw [H]
    simp [ordinary,project,stream,subtotal,summons,out]
  | attempt s v l r il ir =>
    rw [tail_attempt v x u J, il h.2.2.2.2.1 hp, ir h.2.2.2.2.2 hp]
    rw [show ordinary u x (.attempt s v l r) = ordinary u x l by
      unfold ordinary; rw [project]
      cases project l <;> rfl]
    rw [summons]
    rw [show ordinary u x r=0 by unfold ordinary; rw [show (s.win v).norm=0 from rfl]; simp]; ring
  | jump s l r il ir =>
    obtain ⟨ha,hb,hc,hd,he⟩ := h
    let b := (step s).bit x
    have hM : s.here.lev < M := (Play.first hd).within.2
    have hs := share_small hb
    have Hm := FinJump_align s ha.within.1 hM hs.1 u x
    have HE := stream_child (less_self _) hp
    rw [tail_move x u ha.within.1 hb.1.1 hp b,Hm]
    change x ∈ (s.smaller b).here.block M at HE
    unfold b at *
    rcases HA : (step s).bit x
    · rw [ordinary_jump s l r u x, summons,HA,ite_eq_right (by simp)]
      rw [HA] at HE
      rw [il hd HE]; simp only [Bool.false_eq_true,↓reduceIte,add_assoc]
    · rw [ordinary_jump s l r u x, summons,HA,ite_eq_left rfl]
      rw [HA] at HE
      rw [ir he HE]; simp only [↓reduceIte,add_assoc]

end CastShow


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
