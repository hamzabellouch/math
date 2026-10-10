import OAI.Combinatorics.HadwigerCounterexample.PredictedDualEvaluation

namespace OAI

/-! # Prediction Extraction -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Function Submodule LinearMap Module Finset
open scoped BigOperators
namespace StatusAnalysis
namespace DualAnalysis
variable {p:Shape} {r n:ℕ} {A B: Rates}
    {u:Terrain p r} {s:Gazette p r A} {t:Gazette p r B}
open PredictionClass Club Guild

structure countStory (p:Shape) (K:ℕ) (η δ ε β :ℝ) (u:Terrain p r) : Prop where
  h : origami p r u δ
  hb : 0≤β
  he : 0≤ ε
  ht : 0≤η
  bill : playbook p K * η ≤ ε
  high : 6*ε < 1/2*β

structure Stirrings (p:Shape) (r:ℕ) (u:Terrain p r) (s:Gazette p r A) (t:Gazette p r B)
    (p0:DualCoefficients A B) (S T:Stalls p) (ε:ℝ) : Prop where

  recollect (i:Grid): ∃ f:Pulsar p r,praise u s i.1 (S i.1) (leftChime p0 i) f (3*ε) ∧
      praise u t i.2 (T i.2) (rightChime p0 i) f (3*ε)
theorem counter_bill {δ ε β η:ℝ} (q: DualCoefficients A B)
    {K:ℕ} (h:countStory p K η δ ε β u)
    (hs:reports p r u s β δ) (ht:reports p r u t β δ)
    (P Q:Stalls p) (S:Straps (Label p.b)) (i:Grid)
    (he:q.law (chapter (stellar u s t η P Q) S))
    (ha:A i.1≤K^2) (hb:B i.2≤K^2):
    counsel u s t i (outstraps P S true i.1) (outstraps Q S false i.2)
      (leftChime q i) (rightChime q i) ε := by
  intro x hx hp hq
  apply (charge_counter h.h hs ht P Q S q he h.ht x i hx hp hq).trans
  exact (mul_le_mul_of_nonneg_right (booklet_cap p K _ _ ha hb) h.ht).trans h.bill

theorem tells {δ ε β η:ℝ} (q: DualCoefficients A B) {K:ℕ}
    (h:countStory p K η δ ε β u)
    (hs:reports p r u s β δ) (ht:reports p r u t β δ)
    (P Q:Stalls p) (S:Straps (Label p.b))
    (he:q.law (chapter (stellar u s t η P Q) S))
    (ha:∀ i,A i≤K^2) (hb:∀ i,B i≤K^2)
    (h1 : ∀ i, (outstraps P S true i).card<Fintype.card (Label p.b))
    (h2 : ∀ i, (outstraps Q S false i).card<Fintype.card (Label p.b))
    (hg:3≤p.g) :
    Stirrings p r u s t q (outstraps P S true) (outstraps Q S false) ε := by
  constructor
  intro i
  refine paeans u s t h.h hs ht i _ _ (h1 _) (h2 _) hg _ _ ε h.he
    (counter_bill q h hs ht _ _ _ i he (ha _) (hb _))

abbrev Dict (p : Shape) (r:ℕ) := Nodes → F → F→ Pulsar p r
def anthology (p : Shape) (r : ℕ) (u:Terrain p r) (s:Gazette p r A)
    (d:Dict p r) (L:ℕ) (ε:ℝ) :=
    ∀ (B: Stalls p) (i:Nodes), (B i).card ≤ L →
      ∀ (f:Pulsar p r) (a:RhymeSet (A i)), praise u s i (B i) a f ε →
        ∀ l q, pr (u l q) (fun x=> f l q x ≠ d i a.bit a.gamma l q x) ≤ 2*ε

set_option maxHeartbeats 800000 in
theorem build_anthology {δ ε β:ℝ} (P : Terrain p r) (s : Gazette p r A)
    (hp:origami p r P δ) (hs:reports p r P s β δ)
    (he:ε+ε<1/2*β) (hβ:0≤β) (hg:3≤p.g)
    (L:ℕ) (hL:2*L<Fintype.card (Label p.b)):
    ∃ d:Dict p r,anthology p r P s d L ε := by
  classical
  choose f hf using show ∀ (i:Nodes) (b k:F),∃ f:Pulsar p r,∀ (v: Pulsar p r) (A_:Finset (Label p.b))
    (a:RhymeSet (A i)), A_.card ≤ L → a.bit=b → a.gamma=k → praise P s i A_ a v ε →
       ∀ l q,pr (P l q) (fun x=> v l q x≠ f l q x) ≤2*ε from by
    intro i b k; let Q (v : Pulsar p r) :=
       ∃ (A' : Finset (Label p.b)) (a:RhymeSet (A i)),
         A'.card≤ L ∧ a.bit=b ∧ a.gamma=k ∧ praise P s i A' a v ε
    by_cases h:∃ v,Q v
    · obtain ⟨x,S,a0,hx,hy,hk,h⟩:= h
      refine ⟨x,fun v T a hc ha ht hz l q=>?_⟩
      obtain ⟨_,_,hg⟩:=unison hg hp hs i a a0 v x T S
        ((card_union_le ..).trans_lt (by rw [two_mul] at hL; linarith only [hL,hc,hx]))
        hz h (ha.trans hy.symm) he hβ
      specialize hg l q
      rw [ht,hk] at hg
      simpa only [ne_eq,add_left_inj,two_mul] using hg
    exact ⟨0,fun v t a h1 h2 h3 h4=>(h ⟨v,t,a,h1,h2,h3,h4⟩).elim⟩
  exact ⟨f,fun B i hi w a h=> hf i _ _ w (B i) a hi rfl rfl h⟩

def Pulsar.shift (g:Pulsar p r) (a:F): Pulsar p r := fun l q x => g l q x+a*q

abbrev Snip := F×F×F
abbrev Memo := Nodes × (Nodes→Snip)
theorem memo_card : Fintype.card Memo=128 := by simp [Memo,Nodes,Snip,F];

def Memo.words (d:Dict p r) (i:Memo) : Nodes→ Pulsar p r :=
   fun j=> let h:=i.2 j; (d i.1 h.1 h.2.1).shift h.2.2

private theorem praise_tidy (d : Dict p r) (u:Terrain p r) (s:Gazette p r A)
    (t:Gazette p r B)
    {ε β δ:ℝ} (hs:reports p r u s β δ) (h:origami p r u δ) (L:ℕ)
    (S T:Stalls p) (i j:Nodes) (a:RhymeSet (A i)) (b:RhymeSet (B j))
    (f:Pulsar p r) (ha:a.bit=1) (hq:anthology p r u t d L ε)
    (hh:(T j).card ≤ L)
    (hA:praise u s i (S i) a f ε) (hB:praise u t j (T j) b f ε):
    praise u s i (S i) (yokeSet a.coal (1+a.headBit)) ((d j b.bit b.gamma).shift a.gamma) (3*ε) := by
  intro x hx hg
  let g:= d j b.bit b.gamma
  have hz : shot u s i x a g ≤ 3*ε :=
    ((shot_switch u s i x a f g (h.1 _ _) (hs.law _ _ hg)).trans (add_le_add (hA x hx hg)
      (hq T j hh f b hB _ _))).trans_eq (by ring)
  let y := yokeSet a.coal (1+a.headBit)
  have he (j k) :
      y.soot x k≠ g.shift a.gamma x.l x.q j ↔ a.soot x k≠g x.l x.q j := by
    have hh : a.soot x k=y.soot x k+a.gamma*x.q := by
      unfold y RhymeSet.soot RhymeSet.read yokeSet; rw [ha]
      simp only [zero_mul,add_zero,←add_assoc,char_two,zero_add]
    rw [hh]
    unfold Pulsar.shift
    have hx : g x.l x.q j=(g x.l x.q j+a.gamma*x.q)+a.gamma*x.q :=
      Eq.symm (by rw [add_assoc,char_two,add_zero])
    apply not_congr
    constructor
    · intro h; rw [h,←hx]
    intro h; exact add_right_cancel (h.trans hx)
  change shot u s i x y (g.shift a.gamma) ≤_
  unfold shot; simp_rw [he]; exact hz

def announced (u:Terrain p r) (s:Gazette p r A) (d:Dict p r) (L:ℕ) (ε:ℝ) :=
   ∃ i:Memo,∃ (v:styles A) (a:Party) (S:Stalls p),∀ j,
       (S j).card≤L ∧ praise u s j (S j) (yokeSet (v j) (a j)) (Memo.words d i j) ε

set_option maxHeartbeats 900000 in
theorem quotes (d e:Dict p r)
    {ε β δ:ℝ} (hs:reports p r u s β δ) (ht:reports p r u t β δ) (h:origami p r u δ)
    (z:DualCoefficients A B) (hh:z.left ≠0 ∨ z.right≠0)
    (P Q:Stalls p) (hc:Stirrings p r u s t z P Q ε)
    (L:ℕ) (hA:anthology p r u s d L (3*ε)) (hB:anthology p r u t e L (3*ε))
    (hp:∀ i,(P i).card≤L)(hq:∀ i,(Q i).card≤L):
    announced u s e L (3*(3*ε)) ∨ announced u t d L (3*(3*ε)) := by
  classical
  choose f ha hb using hc.recollect
  have he (s: Quota) (h:s≠0): ∃ i:Nodes,s i=1 := by
    by_contra! hf; exact h (funext (fun i=> (bit_cases _).resolve_right (hf i)))
  rcases hh with h1|h1
  · obtain ⟨i,hi⟩:= he z.left h1
    let S j:= leftChime z (j,i); let T j:= rightChime z (j,i)
    let m : Memo:=(i,fun j=>((T j).bit,(T j).gamma,(S j).gamma))
    refine Or.inl ⟨m,fun j=>(S j).coal, fun j=>1+(S j).headBit,P, fun j=>⟨hp j,?_⟩⟩
    exact praise_tidy e u s t hs h L P Q j i (S j) (T j) (f (j,i)) hi hB (hq i)
      (ha (j,i)) (hb (j,i))
  obtain ⟨i,hi⟩:= he z.right h1
  let S j:= rightChime z (i,j); let T j:=leftChime z (i,j)
  let m : Memo:=(i,fun j=> ((T j).bit,(T j).gamma,(S j).gamma))
  refine Or.inr ⟨m,fun j=>(S j).coal,fun j=>1+(S j).headBit,Q,fun j=>⟨hq j,?_⟩⟩
  exact praise_tidy d u t s ht h L Q P j i (S j) (T j) (f (i,j)) hi hA (hp i) (hb (i,j)) (ha (i,j))

end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
