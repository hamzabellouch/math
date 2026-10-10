import OAI.Combinatorics.HadwigerCounterexample.SimultaneousProjection

namespace OAI

/-! # Conditional Large Set Hits -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix LinearMap Function
open scoped BigOperators Topology
open Template
variable {p:Shape} {M n N K r s0:ℕ}
namespace StatusAnalysis
namespace Quill
variable {q:Format} {d:Rates} {b:Bool} (w:Quill p q d b) (t : Tagging p (Messenger q))
    (z:Messenger q→F) (m:Mixer p n)

def prelim (K:ℕ) (s:Charts p n d) (i:Messenger q) :=
   d (parcel b i)≤ K^2 ∧ Injective (s (parcel b i)) ∧
   ∀ x,totalRank (s (parcel b i) x)≤ K

def sameInk (i:Messenger q) (v: Magazine p (d (parcel b i))) :=
  Appearance.nearly p (w.amp i).1 (w.amp i).2.1 v

structure steady (K:ℕ) (s:Charts p n d) (o: UnitType p n N) : Prop where
  frame : PreparationParameters.frameSide p m o
  steadyAxes (i:Messenger q) : prelim (b:=b) K s i
  enough i : (w.amp i).1.diagO=(w.amp i).2.1.1
  sufficesP i :
    let j:= parcel b i; let x:=w.allure t z i
    carried (w.policies t z n i) (fun y=> w.sameInk i (x.profile j o m (s j) y) →
      x.profile j o m (s j) y=w.amp i)

set_option maxHeartbeats 800000 in
theorem thinGlaze (Y : Silhouette p N r) (o : UnitType p n N) (i : Messenger q)
    (s : Charts p n d) (k:AtomKey (p:=p) (t i) N)
    {δ : ℝ} (hd:0<δ)
    (hw:w.moral t z) (hp : w.steady t z m K s o)
    (he : gauze p δ δ Y m K o) (ht : 1≤p.r) (hn : 2*p.r≤n) :
    let x:=w.allure t z i
    δ ≤ x.reference Y (Y (t i) (z i) k) →
    basebeta p K/2 ≤ w.seraph t z o m s Y i k := by
  classical
  intro x h
  let j:=parcel b i
  let z':= w.amp i; let a:=Y (t i) (z i) k
  let μ:=x.reflected Y j o m (s j) a
  have hx : x.apt := w.allure_apt t z hw i
  have hm : IsLaw μ:= x.reflectedLaw Y (Appearance.witLaw hx ht hn) _ _ _ _ _
  obtain ⟨h1,h2,h3⟩:=hp.steadyAxes i
  have hh := x.demonstrates Y o (m:=m) (s j) K j a δ hd z'.1 z'.2.1.2 (hw.2.2 i)
    (hw.2.1 i) ht hn h (he _) h1 h2 h3
  have hq (y) (h:μ y≠0) (hz:w.sameInk i y): y=w.amp i := by
    let P := fun x=>w.sameInk i x → x=w.amp i
    have hb : carried μ P:= x.reflection_exact Y j o m (s j) a P (hp.sufficesP i)
    exact (show P y from not_not.mp fun hi=>h (hb y hi)) hz
  have h4 : (z'.1.diagO,z'.2.1.2)=z'.2.1 := Prod.ext (hp.enough i) rfl
  rw [h4] at hh
  exact hh.trans ((pr_on_mono hm.nz hq).trans_eq (pr_point' ..))

theorem tinyCell_loss (Y:Silhouette p N r) {δ:ℝ} (hd:0≤δ) (i : Messenger q)
    (hN: 2*num (Messenger q×Toast p)-(N:ℝ)≤ -1)
    (hh:2*num (Toast p)-(N:ℝ)≤ -1) :
    let x:= w.allure t z i
    let μ:=lawNu p N t z
    pr μ (fun y=> x.reference Y (Y (t i) (z i) (y i)) < δ) ≤
      r*δ+2*netFact (trayPort p t)*bp (-(N:ℝ)/2) := by
  classical
  intro a μ
  let I:=Messenger q
  let Ω:=fun i=> lawOmega p N (t i) (z i)
  let S:=fun y=>a.reference Y (Y (t i) (z i) y)<δ
  let f : ∀ i:Messenger q,Wgt (AtomKey (p:=p) (t i) N) := fun j=>
    if h:j=i then h ▸ (fun x : AtomKey (p:=p) (t i) N=> ind (S x)) else fun _=>1
  have hi : f i=fun x=>ind (S x) := by unfold f; simp
  have hf j (h:j≠i) : f j=fun _ => 1 := by unfold f; simp [h]
  have hg j x : |f j x| ≤ 1 := by
    by_cases h:j=i
    · subst j; rw [hi]; exact (abs_of_nonneg (ind_nonneg _)).le.trans (ind_le_one _)
    rw [hf j h]; simp
  have he x : prodW f x= ind (S (x i)) := by
    unfold prodW; rw [Finset.prod_eq_single i _ (by simp),hi]
    intro b _ hb; rw [hf _ hb]
  have hR :
      ∏ i,avg (Ω i) (f i) = pr (Ω i) S := by
    rw [Finset.prod_eq_single i _ (by simp),hi]; rfl
    intro b _ hb; rw [hf _ hb,(omegaLaw _ _ _ hh).avg_const]
  let L:=2*netFact (trayPort p t)*bp (-(N:ℝ)/2)
  have hM : pr μ (fun x=> S (x i)) ≤ pr (Ω i) S+L := by
    have hm := reference_product t z f hg hN
    change |avg μ (prodW f)-∏ i,avg (Ω i) (f i)|≤L at hm
    rw [show prodW f=(fun x=>ind (S (x i))) from funext he,hR] at hm
    exact sub_le_iff_le_add'.mp ((abs_le.mp hm).2)
  have hZ : pr (Ω i) S ≤ r*δ := by
    let Q:=fun x=> a.reference Y x < δ
    rw [show pr (Ω i) S= pr (a.reference Y) Q from (mapW_pr (Ω i) (Y (t i) (z i)) Q).symm]
    exact haze_small _ δ hd
  exact hM.trans (add_le_add_left hZ _)

end Quill
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
