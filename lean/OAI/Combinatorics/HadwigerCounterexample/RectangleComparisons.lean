import OAI.Combinatorics.HadwigerCounterexample.SurrogateProductBounds

namespace OAI

/-! # Rectangle Comparisons -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
variable {p:Shape} {n N r : ℕ}
open Template
namespace StatusAnalysis

private theorem warm_bound {u v : ℝ} (h : |u|≤1) {r:ℝ}
    (hv : |v|≤r) : |u*v|≤r := by
  rw [abs_mul]; exact (mul_le_mul h hv (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

namespace Quill
variable {q : Format} {d : Rates} {b : Bool}
    (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)
    (m : Mixer p n)

structure mirrorSpan (s:ℕ) (ε : ℝ) (Y:Silhouette p N r) (o:UnitType p n N) : Prop where
  law : ∀ i,IsLaw (w.policies t z n i)
  frame : ∀ i,frameLaw m (onSide o i)
  close : ∀ i,(w.allure t z i).close Y (onSide o (parcel b i)) ε
  ready : ∀ u:Messenger q → Wgt (Knobs p.g n),(∀ i x, |u i x|≤1) →
    let v:=w.pen t; let x:=w.policies t z n
    |avg (prodW x) (fun y=>ind (v.performs w.script m o y)*prodW u y)-v.kappa*∏ i:Messenger q,
      avg (x i) (u i)|≤ ε
  reference : ∀ f:∀ i:Messenger q,Wgt (AtomKey (p:=p) (t i) N),(∀ i x,|f i x|≤1) →
     |avg (lawNu p N t z) (prodW f) - ∏ i:Messenger q,avg (lawOmega p N (t i) (z i)) (f i)| ≤ ε

set_option maxHeartbeats 800000 in
theorem paint_agree (Y:Silhouette p N r) (o: UnitType p n N) (s : Charts p n d)
    (f:Paint (w.pen t) N) (hF : pigments z Y f)
    (hg : 2≤p.g) (hj : 1≤p.j) (hc : |f.coeff|≤1) {u ℓ}
    (he : w.mirrorSpan t z m ℓ u Y o) :
    |w.prowl s t z m o f.cost-w.sheen t z o m s Y f.cost|≤(2+num (Messenger q))*u := by
  classical
  let A:= w.suede t z o m s f; let x:= w.policies t z n
  let V:= w.pen t
  let B:= w.insidePaint t z o m s Y f
  let Q:= avg (prodW x) (fun y=>ind (V.performs w.script m o y)*prodW A y)
  let E:=avg (lawNu p N t z) (prodW B)
  have hb i y := paintFloor w t z o m s Y f i y (he.law _)
  have ha := suedeFloor w t z o m s f
  let h := he.law
  let P i := avg (x i) (A i); let R i:= avg (lawOmega p N (t i) (z i)) (B i)
  have hm : |Q-V.kappa*(∏ i,P i)|≤u := he.ready A ha
  have hf : |E-∏ i,R i|≤u := he.reference B hb
  have hP i : |P i|≤1 := by
    exact (abs_avg_le (h i).nz).trans ((avg_mono (h i).nz (ha i)).trans_eq ((h i).avg_const _))
  have hR i : |R i|≤1 := by
    have hv : SubLaw (lawOmega p N (t i) (z i)) := unifOn_sub _
    exact (abs_avg_le hv.nz).trans (hv.avg_le zero_le_one (hb i))
  have hh : |(∏ i, P i)-(∏ i, R i)|≤num (Messenger q)*u :=
    cottonError _ _ _ _ hP hR (fun i =>(abs_sub_comm ..).trans_le
      (surrogate_close w t z o m s Y f hF _ (h _) (he.close _)))
  have hK : |V.kappa|≤1 := by rw [abs_of_pos V.kappa_pos]; exact w.kappaTop t
  rw [score_prowl w t z o m s f he.frame hg hj,score_sheen w t z o m,←mul_sub]
  apply warm_bound hc
  have hh' : |V.kappa*(∏ i,P i)-V.kappa*E|≤num (Messenger q)*u+u := by
    rw [←mul_sub]; exact warm_bound hK ((abs_sub_le (∏ i,P i) (∏ i,R i) E).trans (add_le_add hh
      ((abs_sub_comm ..).trans_le hf)))
  exact ((abs_sub_le Q _ (V.kappa*E)).trans (add_le_add hm hh')).trans_eq (by ring)

set_option maxHeartbeats 800000 in
theorem paint_set (Y:Silhouette p N r) (o: UnitType p n N) (s : Charts p n d)
    {r' : ℕ}
    (f:Fin r' → Paint (w.pen t) N) (hF : ∀ i,pigments z Y (f i))
    (hg : 2≤p.g) (hj : 1≤p.j) (hc : ∀ i,|(f i).coeff|≤1) {u ℓ}
    (he : w.mirrorSpan t z m ℓ u Y o) :
    |w.prowl s t z m o (mural (w.pen t) f)-w.sheen t z o m s Y (mural (w.pen t) f)|≤
       r' * ((2+num (Messenger q))*u) := by
  classical
  let F i : Wgt (Keys (p:=p) t N) := (f i).cost
  let R := show Wgt (Keys (p:=p) t N) from mural (w.pen t) f
  have hf x : R x=∑ i:Fin r', F i x := rfl
  change |w.prowl _ _ _ _ _ R-w.sheen _ _ _ _ _ _ R|≤_
  have hh :
      w.prowl s t z m o R=∑ i:Fin r',w.prowl s t z m o (F i) := by
    let key : Inputs p n (Messenger q) → Keys (p:=p) t N := (w.pen t).resultKey o
    change avg ((w.pen t).state z n) (fun x => ind (w.deposit t z m o s x) * R (key x)) =
      ∑ i : Fin r', avg ((w.pen t).state z n)
        (fun x => ind (w.deposit t z m o s x) * F i (key x))
    simp_rw [hf, Finset.mul_sum,avg_sum]
  have ht :
      w.sheen t z o m s Y R=∑ i:Fin r',w.sheen t z o m s Y (F i) := by
    unfold sheen; simp_rw [hf,Finset.mul_sum,avg_sum]
  rw [hh,ht,←Finset.sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  exact (Finset.sum_le_sum fun i _=> paint_agree w t z m Y o s (f i) (hF i) hg hj (hc i)
    he).trans_eq (by simp)

structure witnessPaint (ε:ℝ) (W T : Wgt (Keys (p:=p) t N))
    (o : UnitType p n N) : Prop where
  shadow : ∀ f : (w.pen t).Localist N,(∀ i j, |f i j|≤1) →
    |avg (lawNu p N t z) (fun x=>(W x-T x)*prodW f x)|≤ε
  tested : ¬ exceeds (w.pen t) z (W-T) w.script m (w.policies t z n) ε o

set_option maxHeartbeats 800000 in
theorem bare_bridge (Y : Silhouette p N r) (o:UnitType p n N) (s:Charts p n d)
    {r' : ℕ}
    (f:Fin r' → Paint (w.pen t) N) (hF : ∀ i,pigments z Y (f i))
    (hg : 2≤p.g) (hj : 1≤p.j) (hc : ∀ i,|(f i).coeff|≤1) {u ℓ ε}
    (he : w.mirrorSpan t z m ℓ u Y o) (W : Wgt (Keys (p:=p) t N))
    (hw : w.witnessPaint t z m ε W (mural (w.pen t) f) o) :
    |w.prowl s t z m o W-w.sheen t z o m s Y W|≤ 2*ε +r'*((2+num (Messenger q))*u) := by
  classical
  let A:=w.pen t
  let T:= show Wgt (Keys (p:=p) t N) from mural A f
  let x:=w.prowl s t z m o; let y:= w.sheen t z o m s Y
  have h1 : |x W-x T|≤ε := by
    have hz : x W-x T=x (W-T) := by
      let key : Inputs p n (Messenger q) → Keys (p:=p) t N := A.resultKey o
      change avg (A.state z n) (fun x => ind (w.deposit t z m o s x) * W (key x)) -
        avg (A.state z n) (fun x => ind (w.deposit t z m o s x) * T (key x)) =
        avg (A.state z n) (fun x => ind (w.deposit t z m o s x) * (W-T) (key x))
      rw [←avg_sub]
      simp only [Pi.sub_apply,mul_sub]
    rw [hz]
    change |w.prowl _ _ _ _ _ _|≤_
    rw [prowl_astonish]
    exact le_of_not_gt (fun h=> hw.tested ⟨_, stencil_floor w t z o s m,h⟩)
  have h2 : |y W-y T|≤ε := by
    unfold y; rw [sheen_sun,sheen_sun,←mul_sub,←avg_sub]
    let B:= w.seraph t z o m s Y
    have hF (i j): |B i j|≤1 := by
      have hh:= w.seraphFloor t z o m s Y i (he.law i) j; rw [abs_of_nonneg (show 0≤B i j
        from hh.1)]; exact hh.2
    simp_rw [←sub_mul]; exact warm_bound (show |A.kappa|≤1 from (abs_of_pos A.kappa_pos).trans_le
      (w.kappaTop t)) (hw.shadow B hF)
  have h3 := paint_set w t z m Y o s f hF hg hj hc he
  exact (abs_sub_le (x W) (x T) (y W)).trans ((add_le_add h1
    ((abs_sub_le (x T) (y T) (y W)).trans (add_le_add h3 ((abs_sub_comm ..).trans_le h2)))).trans_eq
      (by ring))

end Quill
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
