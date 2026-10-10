import OAI.Analysis.FourierLLogL.Paths.Launch
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
open Plot

def depthB (b : Beat M) := b.post.here.lev

lemma depth_next (b : Beat M) : (winds b).here.lev=depthB b+1 := by
  unfold winds depthB smaller
  cases b.bit <;> rfl

def muted (u : Grid M) (p : Plot) (c : Board M) (j : ℕ) : Path M → Prop
| [] => True
| b::l => ¬ p.catches b.post c j u ∧ muted u p (turn p c b.post) j l

lemma mute_cat (u : Grid M) (p : Plot) (c : Board M) (j : ℕ) (l r : Path M) :
    muted u p c j (l++r) ↔ muted u p c j l ∧ muted u p (quarrel p c l) j r := by
  induction l generalizing c with
  | nil => simp [muted,quarrel]
  | cons b l ih =>
    change (_∧muted u p (p.turn c b.post) j (l++r)) ↔ (_∧_)∧_
    rw [ih]; simp only [and_assoc]; rfl

lemma first_on (u : Grid M) (p : Plot) (c : Board M) (j : ℕ) (l : Path M) :
    muted u p c j l ∨ ∃ a b r,l=a++b::r ∧ muted u p c j a ∧
      p.catches b.post (quarrel p c a) j u := by
  induction l generalizing c with
  | nil => exact Or.inl True.intro
  | cons b l ih =>
    by_cases h : p.catches b.post c j u
    · exact Or.inr ⟨[],b,l,rfl,True.intro,h⟩
    rcases ih (turn p c b.post) with H|⟨a,d,r,H,h1,h2⟩
    · exact Or.inl ⟨h,H⟩
    exact Or.inr ⟨b::a,d,r,by rw [H]; rfl,⟨h,h1⟩,h2⟩

private lemma close_persists {A B : Finset (Grid M)} (h : A ⊆ B) (n : ℕ)
    {x : Grid M} (hv : enclosed A n x) : enclosed B n x := by
  classical
  obtain ⟨f,hf,rfl⟩ := hv
  let k (x : Grid M) := if x∈A then f x else 0
  refine ⟨k,fun i hi => ?_,?_⟩
  · unfold k; split_ifs with hh; exact hf _ hh; simp
  · have H : ∑ i∈A,k i • i=∑ i∈B,k i • i := Finset.sum_subset h (fun i _ h => by simp [k,h])
    rw [← H]; exact Finset.sum_congr rfl fun _ hx => by simp [k,hx]

private lemma reach_persists {A B : Finset (Grid M)} (h : A ⊆ B) (r t : ℝ)
    {x : Grid M} (hh : r ≤ t) (hv : atReach A r x) :
    atReach B t x := by
  obtain ⟨i,hi,hE⟩ := hv
  exact ⟨i,close_persists h 1 hi,hE.trans hh⟩

/-- snag only denotes a nonbad high depth. -/
def snag (g : Grade) (x : Grid M) (b : Beat M) :=
    intense g.main b.post (side g.i) x ∧ ¬ hazard b.post g.main g.i

def ink (s : Scene M) (g : Grade) (j : ℕ) := spotLimit s j g.i g.main

lemma mute_distance (u : Grid M) (p : Plot)
    (c : Board M) (s : Scene M) (l r : Path M)
    (h : Cast j J f s (l++r)) (he : Comes c s j J f) (hh : muted u p c j l)
    (k : ℝ) (hp : atReach c.chart.items k u) :
    ∀ b∈l, snag (grade p) u b →
      s.here.lev ≤ depthB b ∧ ink b.post (grade p) j < k := by
  induction l generalizing s c with
  | nil => simp
  | cons b l ih =>
    intro z hz hx
    obtain ⟨rfl,⟨t,ht⟩,h₁⟩ := h
    have hC := zoom_spec _ he.valid p.ix p.main ht
    let d := turn p c b.post
    have HR : atReach d.chart.items k u := reach_persists hC.extend k k le_rfl hp
    have hi : b.post.here=b.pre.here := ht.2.1.1.here
    rcases List.mem_cons.mp hz with rfl|hz
    · refine ⟨le_of_eq (congrArg Node.lev hi.symm),lt_of_not_ge fun H => ?_⟩
      exact hh.1 ⟨hx.1,reach_persists hC.extend k _ H hp⟩
    obtain ⟨ha,hb⟩ := ih d (winds b) h₁ (comes_down p ht he b.bit) hh.2 HR z hz hx
    rw [depth_next] at ha; change b.pre.here.lev ≤ _
      ∧ _
    rw [← hi]; exact ⟨le_trans (Nat.le_add_right (depthB b) 1) ha,hb⟩

def volumeAt (p : Plot) (s : Scene M) (c : Board M) :=
    localSize s.here p.ix c.chart

def betweenS (a H : ℕ) (b : Beat M) :=
    a ≤ depthB b ∧ depthB b < a+H

lemma screen_time (u : Grid M) (p : Plot)
    (c : Board M) (s : Scene M) (L : Path M)
    (h : Cast j J f s L) (he : Comes c s j J f) (hp : volumeAt p s c)
    (hv : oiled p c L) :
    ∃ a : ℕ, ∀ l r : Path M, L=l++r → muted u p c j l →
      ∀ b∈l, snag (grade p) u b → betweenS a (latency p j) b := by
  induction L generalizing c s with
  | nil =>
    refine ⟨0,?_⟩; intro l r hh hp b hb; cases l
    · cases hb
    · cases hh
  | cons b L ih =>
    have hi := oily_cons p h he hv
    obtain ⟨rfl,⟨t,ht⟩,h₁⟩ := h
    have hC := zoom_spec _ he.valid p.ix p.main ht
    have hH := ht.2.1.1.here
    let d := turn p c b.post; let s := b.post
    have HC : localSize s.here p.ix d.chart := hC.expands (hH.symm ▸ hp)
    by_cases hx : snag (grade p) u b
    · let I := horizon s.here p.ix d.chart.size
      have heq : d.chart=(now p c b.post) := rfl
      have HB : atReach d.chart.items I u := by
        have HE := hC.awake hx.2 u hx.1
        change atReach d.chart.items (d.chart.wide+speed s.here p.ix d.chart.size) u at HE
        apply reach_persists (Finset.Subset.refl _) _ _ ?_ HE
        unfold localSize at HC
        unfold I horizon; nlinarith
      refine ⟨depthB b,?_⟩
      intro l r hL hh z hz hZ
      cases l with
      | nil => cases hz
      | cons w l =>
        change b::L=w::(l++r) at hL; cases hL
        rcases List.mem_cons.mp hz with rfl|hz
        · unfold betweenS latency; omega
        obtain ⟨ha,hb⟩ := mute_distance u p d (winds b) l r h₁ hi.2.2 hh.2 I HB z hz hZ
        refine ⟨?_, lt_of_not_ge (fun H => ?_)⟩
        · rw [depth_next] at ha; omega
        have Hx' := waiting p j s.here z.post.here H d.chart.size hi.1
        exact hb.not_ge Hx'
    · have HV : volumeAt p (winds b) d := by
        unfold volumeAt localSize; unfold localSize at HC
        apply HC.trans
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply speed_le _ le_rfl
        rw [depth_next]; exact Nat.le_add_right _ _
      obtain ⟨a,ha⟩ := ih d _ h₁ hi.2.2 HV hi.2.1
      refine ⟨a,?_⟩
      intro l r hL hh z hz hZ
      cases l with
      | nil => cases hz
      | cons w l =>
        change b::L=w::(l++r) at hL
        have hw := List.cons.inj hL
        cases hw.1
        rcases List.mem_cons.mp hz with rfl|hz
        · exact (hx hZ).elim
        exact ha l r (List.cons.inj hL).2 hh.2 z hz hZ

def stall (u : Grid M) (g : Grade) (j : ℕ) (L : Path M) (l : Path M) :=
    muted u (heroPlot g L) (vacant M) j l
def billWait (g : Grade) (j : ℕ) (L : Path M) :=
    latency (heroPlot g L) j
lemma bound_stage {u : Grid M} {s : Scene M} (L : Path M)
    (h : Cast j J f s L) (g : Grade) :
    ∃ a : ℕ, ∀ l r : Path M, L=l++r → stall u g j L l →
      ∀ b∈l, snag g u b → betweenS a (billWait g j L) b :=
  screen_time u (heroPlot g L) (vacant M) s L h (vacant_comes s)
    (by simp [volumeAt,vacant,classic,Chart.size,localSize]) (oil_hero g L)

end Troupe


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
