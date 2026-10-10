import OAI.Combinatorics.HadwigerCounterexample.SurrogateQueryScores

namespace OAI

/-! # Surrogate Product Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
variable {p:Shape} {n N K r:ℕ} {A:Type} [Fintype A]
open Template
namespace StatusAnalysis

omit [Fintype A] in
theorem cottonError (s : Finset A) (p q : Wgt A) (ε:ℝ)
    (hp : ∀ x,|p x|≤1) (hq : ∀ x,|q x|≤1)
    (hh : ∀ x,|p x-q x|≤ε) :
    |(∏ x∈s,p x) - (∏ x∈s,q x)|≤s.card*ε := by
  classical
  have ht (s : Finset A) : |∏ i∈s, q i| ≤1 := by
    rw [Finset.abs_prod]
    refine (Finset.prod_le_prod₀ (g:=fun _=>1) (fun i _=>abs_nonneg _) (fun i _=>hq i)).trans_eq (by simp)
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s h ih =>
    let Q:= ∏ i∈s,q i
    let P:= ∏ i∈s,p i
    rw [Finset.prod_insert h,Finset.prod_insert h,Finset.card_insert_of_notMem h]
    have he : p x*P-q x*Q=p x*(P-Q)+(p x-q x)*Q:=by ring
    push_cast; rw [he]
    have hf : |p x*(P-Q)|≤ (s.card:ℝ)*ε := by rw [abs_mul]; exact
      (mul_le_mul (hp _) ih (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    have hg : |(p x-q x)*Q|≤ ε := by
      rw [abs_mul]
      exact (mul_le_mul (hh x) (ht s) (abs_nonneg Q) ((abs_nonneg _).trans (hh x))).trans_eq (mul_one _)
    refine ((abs_add_le _ _).trans (add_le_add hf hg)).trans_eq (by ring)

def pigments {q : Template p A} (z : A→F) (Y : Silhouette p N r) (F : Paint q N) :=
   ∀ i:A, ∃ H : Fin r → Prop,∀ x,F.flies i x ↔ H (Y (q.t i) (z i) x)

namespace Quill
variable {q : Format} {d : Rates} {b : Bool} (w : Quill p q d b)
  (t : Tagging p (Messenger q)) (z : Messenger q→F)
  (o : UnitType p n N) (m:Mixer p n)

def suede (s:Charts p n d) (f : Paint (w.pen t) N) (i : Messenger q) (x : Knobs p.g n) :=
  w.stencil t z o s m i x*
    ind (f.flies i ((w.allure t z i).face (onSide o (parcel b i)) x))

def insidePaint (s : Charts p n d) (Y:Silhouette p N r) (f : Paint (w.pen t) N)
    (i : Messenger q) : Wgt (AtomKey (p:=p) (t i) N) :=
  fun x=> ind (f.flies i x) * seraph w t z o m s Y i x

theorem suedeFloor (s f i x) :
    |w.suede t z o m s f i x| ≤ 1 := by
  unfold suede
  rw [abs_mul,abs_of_nonneg (ind_nonneg _)]
  exact (mul_le_mul (w.stencil_floor t z o s m i x) (ind_le_one _) (ind_nonneg _) zero_le_one).trans_eq
    (one_mul _)

theorem paintFloor (s Y) (f:Paint (w.pen t) N) (i x)
    (hw : IsLaw (w.policies t z n i)) :
    |insidePaint w t z o m s (r:=r) Y f i x|≤1 := by
  unfold insidePaint; have hh:= w.seraphFloor t z o m s Y i hw x
  rw [abs_mul,abs_of_nonneg (ind_nonneg _),abs_of_nonneg hh.1]
  exact (mul_le_mul (ind_le_one _) hh.2 hh.1 zero_le_one).trans_eq (one_mul _)

set_option maxHeartbeats 700000 in
theorem surrogate_close (s :Charts p n d) (Y:Silhouette p N r) (f: Paint (w.pen t) N)
    (hf : pigments z Y f) (i:Messenger q) (hw:IsLaw (w.policies t z n i))
    {ε:ℝ} (h : (w.allure t z i).close Y (onSide o (parcel b i)) ε) :
    |avg (lawOmega p N (t i) (z i)) (w.insidePaint t z o m s Y f i)-
      avg (w.policies t z n i) (w.suede t z o m s f i)|≤ε := by
  classical
  let l:=w.allure t z i; let I:=parcel b i
  obtain ⟨H,hf⟩:=hf i
  let u (x : Fin r) (a:Magazine p (d I)) := ind (H x)*ind (a=w.amp i)
  have hu x i : |u x i|≤1 := by unfold u; rw [←ind_and,abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _
  have hh:= l.close_expect Y I o m (s I) hw u hu h
  let Ω:= lawOmega p N l.l l.q
  let E x:= avg (l.reflected Y I o m (s I) x) (u x)
  have he : avg (l.reference Y) E=avg Ω (insidePaint w t z o m s Y f i) := by
    unfold Appearance.reference
    rw [mapW_avg]; refine avg_congr fun k _=>?_
    have hx : f.flies i k ↔ H (Y l.l l.q k) := hf k
    let G:= l.reflected Y I o m (s I) (Y l.l l.q k)
    change avg G _=ind (f.flies i k)* G (w.amp i)
    rw [hx]; unfold u; rw [avg_mul']; change _*pr _ _=_; rw [pr_point']
  have hc (x:Knobs p.g n) :
      u (l.showTag Y (onSide o I) x) (l.profile I o m (s I) x)=w.suede t z o m s f i x := by
    let k : AtomKey (p:=p) ((w.pen t).t i) N := l.face (onSide o I) x
    change ind (H (Y ((w.pen t).t i) (z i) k)) *
      ind (l.profile I o m (s I) x=w.amp i) =
      ind (l.profile I o m (s I) x=w.amp i) * ind (f.flies i k)
    rw [hf]; exact mul_comm _ _
  change |avg (l.reference Y) E- _| ≤ _ at hh
  rw [he] at hh; simp_rw [hc] at hh; exact hh

set_option maxHeartbeats 800000 in
theorem score_sheen (s : Charts p n d) (Y:Silhouette p N r)
    (f : Paint (w.pen t) N) :
    w.sheen t z o m s Y f.cost=
    f.coeff*((w.pen t).kappa * avg (lawNu p N t z) (prodW (w.insidePaint t z o m s Y f))) := by
  classical
  let cost : Wgt (Keys (p:=p) t N) := f.cost
  let flies : ∀ i : Messenger q, AtomKey (p:=p) (t i) N → Prop := f.flies
  change w.sheen t z o m s Y cost = _
  rw [sheen_sun]
  let v:= w.pen t
  let h x := prodW (w.insidePaint t z o m s Y f) x
  let F := w.seraph t z o m s Y
  have hf (x: Keys (p:=p) t N) : cost x * prodW F x = f.coeff*h x := by
    change f.coeff * (∏ i : Messenger q, ind (flies i (x i))) *
      (∏ i : Messenger q, F i (x i)) =
      f.coeff * (∏ i : Messenger q, ind (flies i (x i)) * F i (x i))
    rw [Finset.prod_mul_distrib, mul_assoc]
  change v.kappa * avg _ _=_
  let μ:=lawNu p N t z
  calc
    _ = v.kappa * (f.coeff * avg μ h) := congrArg (fun x=>v.kappa*x) ((avg_congr (w:=μ)
      (fun i _=>hf i)).trans (avg_mul' ..))
    _ = _ := mul_left_comm _ _ _

set_option maxHeartbeats 800000 in
theorem score_prowl (s : Charts p n d) (f : Paint (w.pen t) N)
    (hh : ∀ i,frameLaw m (onSide o i)) (hg : 2≤p.g) (hj : 1≤p.j) :
    w.prowl s t z m o f.cost=
      f.coeff*avg (prodW (w.policies t z n)) (fun x => ind ((w.pen t).performs w.script m o x)*
        prodW (w.suede t z o m s f) x) := by
  classical
  let cost : Wgt (Keys (p:=p) t N) := f.cost
  change w.prowl s t z m o cost = _
  rw [prowl_astonish]
  let v:=w.pen t; let x:=w.policies t z n
  let μ:=prodW x
  let Q (y:Inputs p n (Messenger q)):= v.resultKey o y
  have heq := astonish_val v z f.cost w.script m x (w.stencil t z o s m) o
  change astonish v z f.cost w.script m x (w.stencil t z o s m) o=_
  rw [heq, ← avg_mul']; apply avg_congr
  intro y hy
  have he (i:Messenger q) : dialed p (v.t i) (v.f i) (y i)=z i := by
    have hf i : x i (y i) ≠ 0 := (Finset.prod_ne_zero_iff.mp hy _ (mem_univ i))
    exact (onW_ne (hf i)).1
  let a:= w.stencil t z o s m
  let W i:= ind (f.flies i ((w.allure t z i).face (onSide o (parcel b i)) (y i)))
  have hq : f.cost (Q y)= f.coeff*(∏ i,W i) := rfl
  change ind (v.earns w.script m z o y)* f.cost (Q y)*prodW a y=_
  have hs : (v.performs w.script m o y) ↔ v.earns w.script m z o y :=
    v.performs_own w.script m o y hh hg hj z he
  have hx : prodW (w.suede t z o m s f) y=prodW a y* (∏ i,W i) := by
    change (∏ i, a i (y i) * W i) = (∏ i, a i (y i)) * (∏ i,W i)
    rw [Finset.prod_mul_distrib]
  rw [hs,hq,hx]; ring

end Quill
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
