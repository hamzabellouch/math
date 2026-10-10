import OAI.Combinatorics.HadwigerCounterexample.StatusCharts

namespace OAI

/-! # Explicit Status Equations -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Finset Function
open scoped BigOperators
namespace StatusAnalysis
variable {d e : Rates} {p : Shape} {n N : ℕ} {q : Format}

set_option maxHeartbeats 600000 in
theorem speak_val (u : ∀ i,Suite d e i) :
    speak d e u = ((fun i=>want _ _ (u i)),
      (fun j:Bool=> ∑ i:Bool,couple _ (u (i,j)).2.1),
      (fun i:Bool=> ∑ j:Bool,couple _ (u (i,j)).2.2)) := by
  unfold speak; rw [LinearMap.sum_apply]
  apply Prod.ext
  · rw [Prod.fst_sum]
    exact Finset.univ_sum_single (fun i=>want _ _ (u i))
  apply Prod.ext
  · rw [Prod.snd_sum,Prod.fst_sum]
    funext i
    rw [Finset.sum_apply]
    change (∑ j:Grid,(Pi.single j.2 (couple _ (u j).2.1) : Quota) i)=_
    rw [Fintype.sum_prod_type]; cases i <;> simp [Nodes,Pi.single_apply]
  rw [Prod.snd_sum,Prod.snd_sum]
  funext i
  rw [Finset.sum_apply]
  change (∑ j:Grid,(Pi.single j.1 (couple _ (u j).2.2) : Quota) i)=_
  rw [Fintype.sum_prod_type]; cases i <;> simp [Nodes,Pi.single_apply]

def funds {b : Bool} (x : Amounts p q d b) (i : Grid) :
    Whole (d (sendId b i)) :=
  ∑ k: Fin (q i),(x (⟨i,k⟩ : Messenger q)).2
def fullq (z : Messenger q → F) (i : Grid) := ∑ k:Fin (q i),z ⟨i,k⟩

theorem sendSum_by (u : Messenger q → F) (a : Amounts p q d true) (b : Amounts p q e false)
    (i : Grid) :
    sendSum u a b i=(fullq u i, (funds a i : Whole (d i.1)), (funds b i : Whole (e i.2))) := by
  unfold sendSum
  apply Prod.ext
  · rw [Prod.fst_sum]; rfl
  apply Prod.ext
  · rw [Prod.snd_sum,Prod.fst_sum]; rfl
  rw [Prod.snd_sum,Prod.snd_sum]; rfl

def still (b : Bool) (a : Amounts p q d b) (v : Charts p n d) (M : Cross p n) :=
  (∀ i:Grid,(funds a i).1.2= targetMark p v M (sendId b i) (sendId (!b) i))∧
    ∀ j:Bool,couple _ (funds a (transit b (true,j))) =
      couple _ (funds a (transit b (false,j)))

def rhyme {b : Bool} (a : Amounts p q d b) (x : Amounts p q e (!b)) :=
  ∀ i:Grid,(funds a i).1.1+(funds x i).1.1=1

set_option maxHeartbeats 800000 in
theorem spoken (v : Charts p n d) (w : Charts p n e) (M : Cross p n) (z : Messenger q→ F)
    (a : Amounts p q d true) (b : Amounts p q e false) :
    speak _ _ (sendSum z a b)=(hailing p v w M,0) ↔
      (∀ i,fullq z i=1)∧rhyme a b∧ still true a v M∧ still false b w (reciprocal p M) := by
  classical
  let f i:=funds a i; let g i:= funds b i
  let h1 i := couple (d (sendId true i)) (f i)
  let h2 i := couple (e (sendId false i)) (g i)
  rw [speak_val]
  simp_rw [sendSum_by]
  have h (x y:F) : x+y=0↔ x=y := by rw [← ZModModule.sub_eq_add,sub_eq_zero]
  constructor
  · intro ht
    have hh := congrArg Prod.fst ht
    have hx := congrArg Prod.fst (congrArg Prod.snd ht)
    have hy := congrArg Prod.snd (congrArg Prod.snd ht)
    refine ⟨fun i=>congrArg Prod.fst (congr_fun hh i),fun i=>congrArg (fun x=>x.2.1)
      (congr_fun hh i),⟨fun i=>congrArg (fun x=>x.2.2.1) (congr_fun hh i),fun i=>?_⟩,
      fun i=>congrArg (fun x=>x.2.2.2) (congr_fun hh i),fun i=>?_⟩
    · have ht:=congr_fun hx i
      change ∑ j:Bool,h1 (j,i)=0 at ht; rw [Fintype.sum_bool,h] at ht; exact ht
    have ht:=congr_fun hy i; change ∑ j:Bool,h2 (i,j)=0 at ht; rw [Fintype.sum_bool,h] at ht
    exact ht
  rintro ⟨ht,hv,⟨hF,hA⟩,hG,hB⟩
  apply Prod.ext
  · funext i; exact Prod.ext (ht i) (Prod.ext (hv i) (Prod.ext (hF i) (hG i)))
  apply Prod.ext
  · funext i; change ∑ j:Bool,h1 (j,i)=0
    rw [Fintype.sum_bool,h]; exact hA i
  funext i; change ∑ j:Bool,h2 (i,j)=0
  rw [Fintype.sum_bool,h]; exact hB i
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
