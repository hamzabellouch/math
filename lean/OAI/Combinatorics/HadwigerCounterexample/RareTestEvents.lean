import OAI.Combinatorics.HadwigerCounterexample.CompatibleOptionRealization

namespace OAI

/-! # Rare Test Events -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix LinearMap Module Function
open scoped BigOperators Topology
variable {p:Shape} {n N K M : ℕ}
namespace StatusAnalysis

def singles : Format:=fun _=>1
def volume1 : Volumes:=fun _=>1
theorem singles_vol : singles=toFormat volume1 := rfl
theorem singles_card : Fintype.card (Messenger singles)=4 := by
  decide
theorem singles_short : ∀ i,1≤singles i ∧ singles i≤7 :=by simp [singles]
theorem funds_one {b : Bool} {d : Rates} (f: Fabric p singles d b) (i:Grid) :
    funds f.amp i=(f.amp ⟨i,(0:Fin 1)⟩).2 := by
  unfold funds
  let : Unique (Fin (singles i)) := (show Unique (Fin 1) from inferInstance)
  exact Fintype.sum_unique _

theorem fourPens (s:Plan p n) (K:ℕ) (H : Stalls p) (h:booths p K s H)
    (ht : 2*frameBills p.g K+4 ≤Fintype.card (Label p.b)) :
    ∃ z:Messenger singles→Label p.b, Injective z ∧ ∀ i j, z i∉ H j := by
  classical
  let F:=H true ∪ H false; let T:=Fᶜ
  have hp : F.card≤ 2* frameBills p.g K :=
    (Finset.card_union_le _ _).trans ((add_le_add (h.1 _) (h.1 _)).trans_eq (two_mul _).symm)
  have he : Fintype.card (Messenger singles) ≤ Fintype.card (↑T:Type) := by
    rw [Fintype.card_coe,singles_card]; unfold T; rw [Finset.card_compl]; omega
  obtain ⟨i,hi⟩: ∃ i : Messenger singles → ↑T,Injective i := by

    obtain ⟨g⟩:=Function.Embedding.nonempty_of_card_le he
    exact ⟨g,g.injective⟩
  refine ⟨fun x=>(i x).val,Subtype.val_injective.comp hi,fun x b=>?_⟩
  have hh:(i x).val∉F:=Finset.mem_compl.mp (i x).property
  intro hx; cases b
  · exact hh (Finset.mem_union_right _ hx)
  exact hh (Finset.mem_union_left _ hx)

variable {d:Rates}
def coordSpec (m:BMark p n N) (o:UnitType p n N) (s:Charts p n d)
    (w:∀ i:Nodes,Cell (d i)) := ∀ i,s i (w i)= m o i

def beacon (p:Shape) (s:Charts p n d) (w:∀ i:Nodes,Cell (d i)) (b:Bool)
    (T: Cross p n) (z : Digest p.g) : Amounts p singles d b :=
   fun k =>
     let i:=parcel b k
     let j:= parcel (!b) k
     let x:=targetMark p s T i j
     (z,(z.diagO,x), z.diagO+dotProduct x (w i))

set_option maxHeartbeats 800000 in
theorem stillBeacon (m:BMark p n N) (o:UnitType p n N) (s:Charts p n d)
    (w:∀ i:Nodes,Cell (d i)) (b:Bool) (T:Cross p n) (z:Digest p.g)
    (h:coordSpec m o s w) (hT:∀ i,cardTone m o T i= glint p (m o)) :
    still b (beacon p s w b T z) s T := by
  classical
  let f:Amounts p singles d b:= beacon p s w b T z
  have hf (i): funds f i=(f ⟨i,(0:Fin 1)⟩).2 := by
    unfold funds; let : Unique (Fin (singles i)) := (show Unique (Fin 1) from inferInstance); exact Fintype.sum_unique _
  change (∀ i, _ ) ∧ _
  constructor
  · intro i
    change (funds f i).1.2=_
    rw [hf]
    rfl
  intro i
  have hh t q : couple _ (funds f (transit b (t,q))) =
      contract p T t q (m o t)+role p n (m o t) := by
    rw [hf]
    let k : Messenger singles:=⟨transit b (t,q),(0:Fin 1)⟩
    let a:= targetMark p s T (parcel b k) (parcel (!b) k)
    change z.diagO+(z.diagO+dotProduct a (w _))=_
    rw [← add_assoc,char_two,zero_add]; unfold a targetMark
    rw [← roll_project]
    have he (i t): (contract p T i t+role p n) (s i (w i))=contract p T i t (m o i)+role p n (m o i) :=
      by rw [h]; rfl
    rw [he]; cases b <;> rfl
  change couple _ (funds f _) = couple _ (funds f _)
  simp_rw [hh]
  have ht:= hT i
  unfold glint cardTone at ht; rw [Fintype.sum_bool,Fintype.sum_bool] at ht
  apply sub_eq_zero.mp
  rw [ZModModule.sub_eq_add]
  rw [add_add_add_comm,ht,char_two]

set_option maxHeartbeats 700000 in
theorem steadyBeacon {plan : Plan p n} (m:BMark p n N) (o:UnitType p n N) (s:Charts p n d)
    (w:∀ i:Nodes,Cell (d i)) (b:Bool) (T:Cross p n)
    (q:Quill p singles d b) (t:Tagging p (Messenger singles))
    (g: Mixer p n) (z:Digest p.g) (K:ℕ)
    (hd:∀ i,d i≤K^2)
    (ha:q.amp=beacon p s w b T z)
    (hk:planRank plan≤K)
    (hs:charted s plan)
    (h:coordSpec m o s w)
    (hF : PreparationParameters.frameSide p g o)
    (hg : exactInk p g m o) :
    q.steady t (fun _=>1) g K s o := by
  classical
  refine ⟨hF,fun i=> ⟨hd _,(hs _).2,fun y=>?_⟩,fun i=>by rw [ha];rfl, fun i v hv => ?_⟩
  · refine (effective_rank (i:=parcel b i) ?_).trans hk
    rw [← (hs _).1]; exact mem_range_self _ _
  · let l:= q.allure t (fun _=>1) i; let j:=parcel b i
    let V:= l.profile j o g (s j) v
    have ht : V.1 = (q.amp i).1 ∧ V.2.1=(q.amp i).2.1 → V=q.amp i := by
      rintro ⟨h1,h2⟩
      apply Prod.ext h1 (Prod.ext h2 _)
      rw [ha] at h2 ⊢
      let a:= useAtom p l.l l.s l.f v
      let k:=targetMark p s T j (parcel (!b) i)
      have heq : V.2.2 = z.diagO + dotProduct k (w j) := by
        have he := exactInner g m o hg j a
        have hx : a∈Xspace p n:= mem_useAtom ..
        have hg' : role p n a=z.diagO := congrArg Prod.fst h2
        have hk : roll (s j) (Tsym g a)=k := congrArg Prod.snd h2
        change innerP p o j a=_
        rw [he hx, grad_val,hg',T_swap, ←h,roll_project,hk]
      exact heq
    exact (hv ht).elim

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
