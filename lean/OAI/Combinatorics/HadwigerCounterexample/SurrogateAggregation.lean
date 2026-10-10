import OAI.Combinatorics.HadwigerCounterexample.UniformSideComparisons
import OAI.Combinatorics.HadwigerCounterexample.ProjectedSurrogates

namespace OAI

/-! # Surrogate Aggregation -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Filter Function
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
variable {p : Shape} {n N K M r : ℕ}
variable {q:Format} {d e : Rates} {b:Bool}

namespace Quill
variable (w:Quill p q d b) (t: Tagging p (Messenger q))
  (z : Messenger q→F) (μ:Wgt (UnitType p n N)) (P:UnitType p n N→Prop)
  (m:Mixer p n) (s:Charts p n d) (Y: Silhouette p N r)
def showcase := fun x=> avg μ (fun i=> ind (P i)*w.mirror t z i m s Y x)

theorem bower_case (hw:IsLaw μ) (h:∀ i,IsLaw (w.policies t z n i)) :
    bower (w.showcase t z μ P m s Y) := by
  let f i := w.mirror t z i m s Y
  have he i x := mirror_floor w t z i m s Y h x
  constructor
  · intro i; exact avg_nonneg hw.nz fun j=>mul_nonneg (ind_nonneg _) (he j i).1
  intro i; exact hw.avg_le fun j=>(mul_le_mul (ind_le_one (P j)) (he j i).2 (he j i).1
    zero_le_one).trans_eq (one_mul _)
def displayMass := fun x=>lawNu p N t z x*w.showcase t z μ P m s Y x

theorem display_mean (W : Wgt (Keys (p:=p) t N)) :
    avg (w.displayMass t z μ P m s Y) W=avg μ (fun o=>ind (P o)*w.sheen t z o m s Y W) := by
  unfold sheen displayMass showcase
  simp only [avg,mul_assoc]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _ => by ring

set_option maxHeartbeats 900000 in
theorem display_test (H : Keys (p:=p) t N→ Prop)
    (hw:IsLaw μ) (h:∀ i,IsLaw (w.policies t z n i)) (hn:IsLaw (lawNu p N t z))
    (Z : UnitType p n N→Prop)
    {ε : ℝ} (he:0≤ε)
    (hg : ∀ x,P x → |w.prowl s t z m x (fun x=>ind (H x))-w.sheen t z x m s Y
      (fun x=>ind (H x))| > ε → Z x) :
    |pr (w.displayMass t z μ P m s Y) H- pr (w.sales t z μ P m s) H| ≤ ε+2*pr μ Z := by
  classical
  let W := fun x=>ind (H x)
  let f x:=w.prowl s t z m x W; let g x:=w.sheen t z x m s Y W
  have heq x :
      |ind (P x)*g x-ind (P x)*f x|≤ ε+ 2*ind (Z x) := by
    rw [←mul_sub,abs_mul,abs_of_nonneg (ind_nonneg _)]
    have hh (x): |ind (Z x)|≤1:=by rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _
    by_cases hP:P x
    · rw [ind_one hP,one_mul]
      by_cases h0 : Z x
      · have hh (x'): |W x'|≤1 := by unfold W; rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _
        have h1 : |f x|≤1 := by
          let F:=w.pen t
          have hv : IsLaw (F.state z n):=prodW_law h
          unfold f prowl; refine (abs_avg_le hv.nz).trans (hv.avg_le fun j=>?_)
          rw [abs_mul,abs_of_nonneg (ind_nonneg _)]
          exact (mul_le_mul (ind_le_one _) (hh _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
        have h2 : |g x|≤1 := by
          unfold g sheen; refine (abs_avg_le hn.nz).trans (hn.avg_le fun j=>?_)
          have hm:=mirror_floor w t z x m s Y h j
          rw [abs_mul,abs_of_nonneg hm.1]
          exact (mul_le_mul hm.2 (hh _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
        rw [ind_one h0]
        have hi := abs_sub (g x) (f x)
        linarith only [hi,h1,h2,he]
      rw [ind_zero h0,abs_sub_comm,mul_zero,add_zero]
      exact le_of_not_gt (fun h=> h0 (hg x hP h))
    rw [ind_zero hP,zero_mul]
    exact add_nonneg he (mul_nonneg (by norm_num) (ind_nonneg _))
  unfold pr; rw [sales_mean,display_mean,← avg_sub]
  exact (abs_avg_le hw.nz).trans ((avg_mono hw.nz heq).trans_eq (by rw [avg_add,
    avg_mul',hw.avg_const]))

end Quill

namespace Typus
variable (w: Typus p q d e) (o o' : UnitType p n N) (s:Charts p n d) (t:Charts p n e)
    (m : Mixer p n) (Y:Silhouette p N r)

/-- Per-position beta status overlap at fixed orientation pair. -/
def chimera (i:Messenger q) :=
    let l:=w.t i; let z:=w.z i
    let f:=w.qA.seraph w.t w.z o m s Y i; let g:=w.qB.seraph w.t w.z o' m t Y i
    dip (lawOmega p N l z) f g
def momus := (w.qA.pen w.t).kappa*(w.qB.pen w.t).kappa
def constellation := w.momus*(∏ i:Messenger q, w.chimera o o' s t m Y i)

set_option maxHeartbeats 900000 in
theorem shine_match (ha:∀ i,IsLaw (w.qA.policies w.t w.z n i))
    (hb:∀ i,IsLaw (w.qB.policies w.t w.z n i))
    (hN: 2*num ((Messenger q)×Toast p)-(N:ℝ)≤ -1) :
    let L:=w.qA.mirror w.t w.z o m s Y
    let R:=w.qB.mirror w.t w.z o' m t Y
    |w.constellation o o' s t m Y - dip (lawNu p N w.t w.z) L R| ≤
      2*netFact (trayPort p w.t) * bp (-(N:ℝ)/2) := by
  classical
  intro L R
  let μ:= lawNu p N w.t w.z
  let Z:=w.momus
  let A:=w.qA.seraph w.t w.z o m s Y; let B:=w.qB.seraph w.t w.z o' m t Y
  let C (i:Messenger q):=fun z=> A i z*B i z
  have hh : dip μ L R=Z*avg μ (prodW C) := by
    unfold dip; rw [←avg_mul']; refine avg_congr fun i hi=>?_
    unfold L R Z Quill.mirror momus prodW C
    rw [Finset.prod_mul_distrib]; unfold A B; ring
  have hC (i: Messenger q) (j): |C i j|≤1 := by
    have hm:= w.qA.seraphFloor w.t w.z o m s Y i (ha i) j
    have hn:= w.qB.seraphFloor w.t w.z o' m t Y i (hb i) j
    unfold C A B; rw [abs_mul,abs_of_nonneg hm.1,abs_of_nonneg hn.1]
    exact (mul_le_mul hm.2 hn.2 hn.1 zero_le_one).trans_eq (one_mul _)
  have hf := reference_product w.t w.z C hC hN
  change |Z*_ - dip μ L R|≤ _
  rw [hh,abs_sub_comm,←mul_sub,abs_mul]
  have hZ : |Z|≤1:= by
    unfold Z momus
    rw [abs_mul,abs_of_pos (kappa_pos _),abs_of_pos (kappa_pos _)]
    exact (mul_le_mul (w.qA.kappaTop _) (w.qB.kappaTop _) (kappa_pos _).le zero_le_one).trans_eq
      (one_mul _)
  exact (mul_le_mul hZ hf (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
end Typus
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
