import OAI.Combinatorics.HadwigerCounterexample.PairedEventBounds

namespace OAI

/-! # Compatible Option Realization -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function Module LinearMap
open scoped BigOperators
variable {p:Shape} {n N M K s0:ℕ}
namespace StatusAnalysis

variable {q:Format} {d e: Rates} {b:Bool}
abbrev Stalls (p:Shape) := Bool→Finset (Label p.b)

def booths (p:Shape) (K:ℕ) (s: Plan p n) (H:Stalls p) :=
   (∀ i,(H i).card≤frameBills p.g K) ∧
   ∀ i j, protectedBy p (sPin s j i) (qorth K) (H i)
theorem buildBooths (K:ℕ) (s:Plan p n) (h:planRank s≤K)
    (hj:(K+1)*qorth K≤p.j+1) :
    ∃ H,booths p K s H := by
  classical
  choose H hH hG using fun i : Bool=> pin_protection s i K (qorth K) h hj
  exact ⟨H,hH,hG⟩

theorem shelter (K :ℕ) (S:Pin p n N) (t : Quill p q d b) (z : Tagging p (Messenger q)) (H:Stalls p)
    (h:booths p K S.sp H) (hp : Injective t.sel)
    (ht:∀ i:Messenger q,t.sel i∉H (parcel b i))
    (hg : ∀ i,1≤q i ∧ q i≤7) : t.penSpace z S K := by
  intro x i
  let v:=(t.pen z).draw x
  refine ⟨H i,h.2 i,fun j hj=>?_,?_,hp.injOn⟩
  · have he : parcel b j=i := Finset.mem_filter.mp hj|>.2
    rw [←he]; exact ht j
  exact (Volley.here_card v (shots_ok b v rfl hg) i).trans (by unfold qorth; omega)

theorem sizedCharts (K:ℕ) (w:LeafMixture p n N) (t:Station p n N K w) (ht:t.bank)
    (i:w.T) (h:planRank (w.pin i.val).sp≤K) :
    ∃ d:Stakes K,charted (t.cAxes i (toRates d)) (w.pin i.val).sp := by
  let s:=(w.pin i.val).sp
  let d (i:Nodes):= dim (effective s i)
  have hd i : d i < K^2+1 := Nat.lt_of_le_of_lt
    ((effective_dim s i).trans (by gcongr)) (Nat.lt_succ_self _)
  exact ⟨fun i=>⟨d i,hd i⟩,ht.1 i⟩

structure Fabric (p:Shape) (q:Format) (d:Rates) (b:Bool) where
  sel : Messenger q → Label p.b
  flav : Messenger q → Flavor p.g
  amp : Amounts p q d b

namespace Fabric
variable (w:Fabric p q d b) (t:Tagging p (Messenger q))
def hang (s:Script p (Messenger q)) : Quill p q d b :=
  ⟨w.sel,w.flav,w.amp,s⟩
def up (w:Fabric p q d b) (t:Tagging p (Messenger q)) (z: Messenger q→F) :=
    (w.hang 0).moral t z

end Fabric

variable {i j:Bool} {L:ℕ}
set_option maxHeartbeats 1200000 in
theorem optionVia (q:Format) (d e : Rates) (s t:Pin p n N) (T:Cross p n) (K:ℕ)
    (ha: tableInj s.sp t.sp T) (hb : tableInj t.sp s.sp (reciprocal p T))
    (p':Tagging p (Messenger q)) (x:Charts p n d) (y:Charts p n e)
    (hx:charted x s.sp) (hy:charted y t.sp)
    (f:Fabric p q d true) (g:Fabric p q e false)
    (hs h:Stalls p) (hm:booths p K s.sp hs) (hu : booths p K t.sp h)
    (hf:∀ i,f.sel i∉ hs (parcel true i)) (hg:∀ i,g.sel i∉ h (parcel false i))
    (z:Messenger q→F) (hF:f.up p' z)(hG:g.up p' z)
    (hj : 1≤p.J) (h2: 2≤p.g) (h₀:∀ i,1≤q i∧q i≤7)
    (he:speak _ _ (sendSum z f.amp g.amp)=(hailing p x y T,0)) :
    ∃ (a b:Script p (Messenger q)),Typus.chances ⟨p',z,f.hang a,g.hang b⟩ x y s t T K := by
  obtain ⟨hQ,hR,hL,hS⟩:= (spoken x y T z f.amp g.amp).mp he
  obtain ⟨a,ha'⟩:= proclaim_script true f.amp g.amp p' y (reciprocal p T) hR (fun i=>(h₀ i).1)
    hS h2 hj
  have hh : rhyme g.amp f.amp := fun i=> (add_comm ..).trans (hR i)
  obtain ⟨b,hb'⟩:= proclaim_script false g.amp f.amp p' x T hh (fun i=>(h₀ i).1)
    hL h2 hj
  exact ⟨a,b, ⟨h₀,hF,hG,hQ,hR,ha',hb'⟩,⟨hx,shelter K s (f.hang a) p' hs hm hF.1 hf h₀,hL,ha⟩,
    ⟨hy,shelter K t (g.hang b) p' h hu hG.1 hg h₀,hS,hb⟩⟩

def berthTicket (a b:Pin p n N) (T: Cross p n)
    (x:UnitType p n N × UnitType p n N) :=
    tableInj a.sp b.sp T ∧ tableInj b.sp a.sp (reciprocal p T)
      ∧ fitsTable a.sp b.sp T (actual p x.1 x.2)

theorem issueTicket (x y:UnitType p n N) (w : LeafMixture p n N) (t:Station p n N K w)
    (i j:w.T) (ha:apart w.T)
    (hx:x∈i.val) (hy:y∈j.val) (ht:t.bank)
    (he : secureAt p w.rooting (x,y)) :
    ∃ k, berthTicket (w.pin i.val) (w.pin j.val) (t.mails i j k) (x,y) := by
  obtain ⟨k,hk⟩:=ht.2 i j (actual p x y)
  obtain ⟨h1,h2⟩:=he
  let a:= w.pin i.val; let b:= w.pin j.val
  have hh : w.rooting x=a.sp:= congrArg Pin.sp (LeafMixture.poller_eq w ha i.property hx)
  have hg : w.rooting y=b.sp:= congrArg Pin.sp (LeafMixture.poller_eq w ha j.property hy)
  change tableInj (w.rooting x) (w.rooting y) (actual p x y) at h1
  change tableInj (w.rooting y) (w.rooting x) (actual p y x) at h2
  rw [hh,hg] at h1 h2
  rw [← reciprocal_actual] at h2
  exact ⟨k, fits_inj hk h1,fits_inj (fits_recip hk) h2,hk⟩

theorem berth_flags (a b:Pin p n N) (T:Cross p n) {x:UnitType p n N × UnitType p n N}
    (h:berthTicket a b T x) (ha:a.agree x.1) (hb:b.agree x.2) :
    tableFlag a b T x.1 ∧ tableFlag b a (reciprocal p T) x.2 := by
  have hg:=fits_recip h.2.2; rw [reciprocal_actual] at hg
  exact ⟨fits_flag T _ a b x.1 h.2.2 (flag_actual _ _ hb),
         fits_flag _ _ b a x.2 hg (flag_actual _ _ ha)⟩

def cardTone (m:BMark p n N) (x:UnitType p n N) (T:Cross p n) (j:Bool) : F :=
   ∑ i:Bool,contract p T i j (m x i)

theorem actualTone (m:BMark p n N) (a b : UnitType p n N) (j:Bool) :
    cardTone m a (actual p a b) j = tone p b (unary j) (delta m a) := by
  rw [lone]
  unfold cardTone delta
  rw [map_add,Fintype.sum_bool]
  simp_rw [contract_actual]; rfl
theorem fitsTone {w v: Plan p n} {T U:Cross p n}
    (m:BMark p n N) (x:UnitType p n N)
    (h:fitsTable w v T U) (hx:∀ i,m x i∈effective w i) (j) :
    cardTone m x T j=cardTone m x U j :=
    Finset.sum_congr rfl (fun i _=>fits_contract h i j _ (hx i))
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
