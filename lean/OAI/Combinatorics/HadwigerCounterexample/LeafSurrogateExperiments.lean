import OAI.Combinatorics.HadwigerCounterexample.SurrogateAggregation

namespace OAI

/-! # Leaf Surrogate Experiments -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Function Finset Filter
open scoped BigOperators Topology
namespace StatusAnalysis
variable {p : Shape} {n N K s M : ℕ}
  {w : LeafMixture p n N} {q : Format} {d e : Rates}

namespace Station
variable (t : Station p n N K w) (x : Typus p q d e)
  (m : Mixer p n) (μ : Wgt (UnitType p n N)) (k : Fin (2^deckMax p K))
variable (Y : Silhouette p N s) (i j : w.T)

def stageLeft :=
  x.qA.showcase x.t x.z (partW μ i.val) (t.frontPage x m i j k) m (t.cAxes i d) Y
def stageRight :=
  x.qB.showcase x.t x.z (partW μ j.val) (t.backPage x m i j k) m (t.cAxes j e) Y
def stagePlane :=
  dip (lawNu p N x.t x.z) (t.stageLeft x m μ k Y i j) (t.stageRight x m μ k Y i j)

def twilight (o : UnitType p n N × UnitType p n N) :=
    ind (t.frontPage x m i j k o.1 ∧ t.backPage x m i j k o.2)*
      x.constellation o.1 o.2 (t.cAxes i d) (t.cAxes j e) m Y

def eclipse :=
  avg (pairW (partW μ i.val) (partW μ j.val)) (t.twilight x m k Y i j)

def stratum :=
  let v:=portionW μ w.T
  avg (pairW v v) (fun i=>t.eclipse x m μ k Y i.1 i.2)

set_option maxHeartbeats 900000 in
theorem eclipse_beam
    (hv : ∀ i∈w.T,IsLaw (partW μ i))
    (ha : ∀ i,IsLaw (x.qA.policies x.t x.z n i)) (hb : ∀ i,IsLaw (x.qB.policies x.t x.z n i))
    (hN : 2*num (Messenger q × Toast p)-(N:ℝ)≤ -1) :
    t.eclipse x m μ k Y i j - t.stagePlane x m μ k Y i j ≤
      2*netFact (trayPort p x.t)*bp (-(N:ℝ)/2) := by
  classical
  let X:=UnitType p n N
  let u:=partW μ i.val; let v:= partW μ j.val; let hK:=pairW u v
  have h := show IsLaw hK from pairW_law (hv _ i.property) (hv _ j.property)
  let U := t.frontPage x m i j k; let V := t.backPage x m i j k
  let Q o:=ind (U o)
  let R o:=ind (V o)
  let F o:= x.qA.mirror x.t x.z o m (t.cAxes i d) Y
  let G o:= x.qB.mirror x.t x.z o m (t.cAxes j e) Y
  let A:= lawNu p N x.t x.z
  have he : t.stagePlane x m μ k Y i j=
      avg hK (fun o=> Q o.1*R o.2*dip A (F o.1) (G o.2)) := by
    unfold stagePlane stageLeft stageRight Quill.showcase dip
    change avg A (fun i=>avg u (fun x=>Q x*F x i)*avg v (fun x=>R x*G x i))=_
    have hx (i:Keys (p:=p) x.t N) : avg u (fun x=>Q x*F x i)*avg v (fun x=>R x*G x i)=
        avg hK (fun o=> Q o.1*F o.1 i*(R o.2*G o.2 i)) := (pairW_separate ..).symm
    simp_rw [hx]; rw [avg_avg]
    apply avg_congr; intro o _
    rw [←avg_mul']; exact avg_congr fun i _=> by ring
  let C:= 2*netFact (trayPort p x.t)*bp (-(N:ℝ)/2)
  rw [he]; unfold eclipse; rw [← avg_sub]
  refine h.avg_le fun o=> ?_
  have ht := x.shine_match o.1 o.2 (t.cAxes i d) (t.cAxes j e) m Y ha hb hN
  unfold twilight; rw [ind_and]
  have hU := Q o.1; have hV:= R o.2
  let Z:= x.constellation o.1 o.2 (t.cAxes i d) (t.cAxes j e) m Y
  let L:= Z-dip A (F o.1) (G o.2)
  change Q o.1*R o.2* Z-Q o.1*R o.2*_≤ C
  by_cases hh : U o.1∧V o.2
  · have hf : Q o.1*R o.2=1 := by unfold Q R; rw [←ind_and,ind_one hh]
    rw [hf,one_mul,one_mul]; exact (abs_le.mp ht).2
  have hf : Q o.1*R o.2=0 := by unfold Q R; rw [←ind_and,ind_zero hh]
  rw [hf,zero_mul,zero_mul,sub_zero]; exact (abs_nonneg L).trans ht

end Station

variable {I : Type} [Fintype I]
theorem skylineMean (w : Wgt I) (f g c : Wgt I) (ε : ℝ) (he:0≤ε) (hw:IsLaw w)
    (h : avg w c≤ (ε/2)^2) (hc : ∀ i,g i^2≤c i)
    (hg:∀ i,f i - g i ≤ ε/2) : avg w f ≤ ε := by
  have h1 := (mean_sq _ hw g).trans ((avg_mono hw.nz hc).trans h)
  have h2 : avg w f-avg w g≤ ε/2 := by rw [←avg_sub]; exact hw.avg_le hg
  nlinarith only [he,h1,h2]
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
