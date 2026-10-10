import OAI.Combinatorics.HadwigerCounterexample.FiniteOptionLabels

namespace OAI

/-! # Binary Status Comparison -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Filter Function Submodule Module LinearMap
open scoped BigOperators
variable {A B J H : Type} [Fintype A] [Fintype B] [Fintype J]

theorem disagreement_bound (w : Wgt A) (hw : ∀ x,0 ≤ w x) (f g h:A→ H) :
    pr w (fun i=> f i≠ h i) ≤ pr w (fun i=>f i≠ g i) + pr w (fun i=>g i≠h i) :=
  let p (i:A) := f i≠g i∨g i≠h i
  ((pr_mono hw fun i h=>show p i from Classical.byContradiction (fun hi => h (Eq.trans
    (not_not.mp (mt Or.inl hi)) (not_not.mp (mt Or.inr hi))))).trans (pr_or_le hw))

def majority (w : Wgt A) (f : A→F) :=
    if 1/2≤ pr w (fun i=>f i=0) then (0:F) else 1

theorem majority_bound (w : Wgt A) (hw:IsLaw w) (f : A→F) :
    1/2 ≤ pr w (fun i=> f i= majority w f) := by
  classical
  unfold majority
  split
  next h => exact h
  next h =>
    have hi i : f i=1 ↔ ¬f i=0 :=
      ⟨fun hh=>by rw [hh]; exact one_ne_zero,fun hh=>(bit_cases _).resolve_left hh⟩
    simp_rw [hi,pr_not,hw.total]
    exact le_of_lt (by linarith only [h])

theorem majority_charge (p:Wgt A) (q:Wgt B) (hp:IsLaw p) (hq:IsLaw q)
    (f:A→F) (g:B→F) :
    pr p (fun i=> f i≠majority q g)≤2 * pr (pairW p q) (fun i=> f i.1≠g i.2) := by
  classical
  let Q i:= g i=majority q g; let P i:= f i≠majority q g
  let v:= pairW p q
  have hm (z:A×B) (h:P z.1∧Q z.2): f z.1≠g z.2 := h.2 ▸ h.1
  have hh : pr p P*pr q Q ≤ pr v (fun i=>f i.1≠g i.2) :=
    (pairW_pr ..).symm.le.trans (pr_mono (pairW_law hp hq).nz hm)
  have hx:=majority_bound q hq g
  have hh' := mul_le_mul_of_nonneg_left hx (pr_nonneg (p:=P) hp.nz)
  change _* (1/2) ≤ _*pr q Q at hh'
  change pr p P≤2*pr v _
  linarith only [hh,hh']

theorem reflect_cost (p:Wgt A) (q:Wgt B) (hp:IsLaw p) (hq:IsLaw q)
    (f:A→H) (g:B→H) (k:H) :
    pr q (fun i=>g i≠k)≤ pr (pairW p q) (fun i=>f i.1≠g i.2)+pr p (fun i=>f i≠k) := by
  let w:=pairW p q
  let t i:= g i≠k; let s i:= f i≠k
  have hi : pr q t=pr w (fun i=> t i.2) := by simpa [hp.total] using
    (pairW_pr p q (fun _=>True) t).symm
  have hj : pr p s=pr w (fun i=>s i.1) := by simpa [hq.total] using
    (pairW_pr p q s (fun _=>True)).symm
  let P (i:A×B):= f i.1 ≠ g i.2
  rw [hi,hj]
  have hh (i:A×B) (h:t i.2): P i∨ s i.1 := by
    by_cases he:P i
    · exact Or.inl he
    exact Or.inr (fun hc=> h ((not_not.mp he).symm.trans hc))
  exact (pr_mono (pairW_law hp hq).nz hh).trans (pr_or_le (pairW_law hp hq).nz)

namespace StatusAnalysis
namespace DualAnalysis
variable {p:Shape} {d e: Rates} {r K:ℕ}
abbrev Pulsar (p:Shape) (r:ℕ):= Tag p.g → F → Fin r→F
variable (u:Terrain p r) (s:Gazette p r d) (t:Gazette p r e)

def shot (i:Nodes) (x:Appearance p) (a:RhymeSet (d i)) (f:Pulsar p r) :=
  avg (u x.l x.q) (fun j=>pr (s i x j) (fun v=> a.soot x v ≠f x.l x.q j))
def praise (u:Terrain p r) (s:Gazette p r d) (i:Nodes)
    (A:Finset (Label p.b)) (a:RhymeSet (d i)) (f:Pulsar p r) (ε:ℝ) :=
   ∀ x:Appearance p,x.s∉A →x.apt → shot u s i x a f≤ε
def counsel (i:Grid) (A B:Finset (Label p.b))
    (a : RhymeSet (d i.1)) (b : RhymeSet (e i.2)) (ε :ℝ) :=
   ∀ x:Zodiac p,x.common → x.s true∉A →x.s false∉ B →charge u x s t i a b≤ε

def amazes (p:Shape) (z:Label p.b) (l: Tag p.g) (q:F):Appearance p:=⟨l,z,Flavor.full,q⟩
def amends (p:Shape) (x y:Appearance p): Zodiac p :=
  {l:=x.l
   q:=x.q
   s i:=if i then x.s else y.s
   f i:=if i then x.f else y.f}
theorem amendsB (x y: Appearance p)(h:x.l=y.l)(ht:x.q=y.q):
    (amends p x y).aspect false=y := by cases x; cases y; simp_all [amends,Zodiac.aspect]

theorem splitCounsel (i:Grid) (A B:Finset (Label p.b))
    (a : RhymeSet (d i.1)) (b : RhymeSet (e i.2)) (ε :ℝ)
    (h:counsel u s t i A B a b ε) (x y:Appearance p)
    (hx:x.s∉A) (hy:y.s∉B) (he:x.apt) (hf:y.apt) (hg:x.l=y.l) (hk:x.q=y.q) :
    avg (u x.l x.q) (fun j=>pr (pairW (s i.1 x j) (t i.2 y j)) (fun k=>a.soot x k.1 ≠
      b.soot y k.2))≤ε := by
  classical
  let Z:=amends p x y
  have hQ : Z.aspect false=y := amendsB _ _ hg hk
  have hP : Z.aspect true=x := rfl
  have hm : Z.common := by intro i;cases i; rw [hQ];exact hf; rw [hP];exact he
  have hi:= h Z hm hx hy
  unfold charge circlet pr couplePage at hi
  rw [mixW_avg,hQ,hP] at hi
  exact hi

set_option maxHeartbeats 800000 in
theorem paeans {β δ:ℝ} (hu:origami p r u δ)(hs:reports p r u s β δ)(ht:reports p r u t β δ)
    (i:Grid) (A B:Finset (Label p.b)) (hx:A.card<Fintype.card (Label p.b))
    (hy:B.card<Fintype.card (Label p.b)) (hg:3≤p.g)
    (a : RhymeSet (d i.1)) (b : RhymeSet (e i.2)) (ε:ℝ) (he:0≤ε)
    (h:counsel u s t i A B a b ε) :
    ∃ f:Pulsar p r, praise u s i.1 A a f (3*ε) ∧ praise u t i.2 B b f (3*ε) := by
  classical
  obtain ⟨x,hx⟩:=any_label A hx
  obtain ⟨y,hy⟩:=any_label B hy
  let Z:= amazes p y
  let f l q j:= majority (t i.2 (Z l q) j) (b.soot (Z l q))
  have hl:praise u s i.1 A a f (2*ε) := by
    intro z hz hhq
    let w:= Z z.l z.q
    have ht' := generic_apt p hg w rfl
    have hh := splitCounsel u s t i A B a b ε h z w hz hy hhq ht' rfl rfl
    refine le_trans (avg_mono (hu.1 z.l z.q).nz (fun j=> majority_charge (s i.1 z j) (t i.2 w j)
      (hs.law _ _ hhq _) (ht.law _ _ ht' _) (a.soot z) (b.soot w))) ?_
    rw [avg_mul']
    exact mul_le_mul_of_nonneg_left hh (by norm_num)
  refine ⟨f,fun w hw hx=>(hl _ hw hx).trans (by linarith only [he]), fun w hw hv=>?_⟩
  let z:=amazes p x w.l w.q
  have hf : z.apt:=generic_apt _ hg _ rfl
  have hx0:= splitCounsel u s t i A B a b ε h z w hx hw hf hv rfl rfl
  have hl0:=hl z hx hf
  let W:=u w.l w.q
  have heq j:= reflect_cost (s i.1 z j) (t i.2 w j) (hs.law _ _ hf j) (ht.law _ _ hv j)
    (a.soot z) (b.soot w) (f w.l w.q j)
  apply (avg_mono (hu.1 w.l w.q).nz heq).trans
  rw [avg_add]; exact (add_le_add hx0 hl0).trans_eq (by ring)
end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
