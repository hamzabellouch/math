import OAI.Combinatorics.HadwigerCounterexample.RelationMismatchBounds

namespace OAI

/-! # Finite Option Labels -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Finset Function Submodule LinearMap
open scoped BigOperators Topology
open Template
variable {p:Shape} {N n r K : ℕ}
namespace StatusAnalysis
namespace DualAnalysis
open Club Guild
variable {d e: Rates}
    {u:Terrain p r} {s:Gazette p r d} {t:Gazette p r e}
    {β η δ:ℝ}

abbrev Engagement (p:Shape) (q : Format) (d e:Rates) :=
  (i : Messenger q) → Scriptum p d e i.1

set_option maxHeartbeats 800000 in
theorem invite (p: Shape) (u:Terrain p r) (s:Gazette p r d) (t:Gazette p r e)
    (A B:Stalls p) (η:ℝ)
    (v: ∀ i,Suite d e i) (H:Straps (Label p.b)) (f:Bags (Scriptum p d e))
    (hf : Parade (stellar u s t η A B) H v f Finset.univ) :
    let C:=stellar u s t η A B
    ∃ (q : Volumes) (g:Engagement p (toFormat q) d e),
      (∀ i,1 ≤ toFormat q i ∧ toFormat q i ≤7) ∧
      (∀ i:Messenger (toFormat q),(C i.1).valid (g i)) ∧
      (∀ b:Bool,Injective (fun i:Messenger (toFormat q)=>(g i).1.s b)) ∧
      ∀ i,∑ j:Fin (toFormat q i),(C i).writes (g ⟨i,j⟩)=v i := by
  classical
  intro C
  have he i:= hf.batch i (mem_univ _)
  let q (i:Grid):Fin 8:= ⟨(f i).card,Nat.lt_succ_of_le (he i).2.2.2⟩
  let Q:=toFormat q
  let E (i:Grid): Fin (Q i)≃(↑(f i) : Type) := (Fintype.equivFinOfCardEq (Fintype.card_coe _)).symm
  let g:Engagement p Q d e:=fun i=>(E _ i.2).val
  have hG (i) : g i∈ f i.1:=(E i.1 i.2).property
  refine ⟨q,g,fun i=>(he i).2.2,fun i=>((he _).1.1 _ (hG i)).1,fun b i j h=>?_,
    fun i=>?_⟩
  · rcases i with ⟨i,x⟩;rcases j with ⟨j,y⟩
    by_cases hi:i=j
    · subst j
      have ht : g ⟨i,x⟩=g ⟨i,y⟩:=
        (he i).1.2 b (hG ⟨i,x⟩) (hG ⟨i,y⟩) h
      rw [show x=y from (E i).injective (Subtype.ext ht)]
    exact (hf.mixed i j (mem_univ _) (mem_univ _) hi _ (hG ⟨i,x⟩) _ (hG ⟨j,y⟩) b h).elim
  calc _ = ∑ x:↑(f i), (C i).writes x.val := Equiv.sum_comp (E i) (fun x=>(C i).writes x.val)
       _ = _ := (Finset.sum_coe_sort (f i) _).trans (he i).2.1

variable (p:Shape)
namespace Engagement

def tags {q:Format} (f:Engagement p q d e) :=
   fun i:Messenger q=> (f i).1.l
def bits {q:Format} (f:Engagement p q d e) :=
   fun i:Messenger q=> (f i).1.q
def genre0 {q:Format} (f:Engagement p q d e): Fabric p q d true :=
  {sel i:= (f i).1.s true
   flav i:= (f i).1.f true
   amp i:= (f i).2.1}
def genre1 {q:Format} (f:Engagement p q d e): Fabric p q e false :=
  {sel i:= (f i).1.s false
   flav i:= (f i).1.f false
   amp i:= (f i).2.2}
def binding {q:Format} (f:Engagement p q d e) (a b:Script p (Messenger q)) :
    Typus p q d e :=
  ⟨tags p f,bits p f,(genre0 p f).hang a,(genre1 p f).hang b⟩

set_option maxHeartbeats 900000 in
theorem solicit {q:Format} (g:Engagement p q d e) (a b:Script p (Messenger q))
    (Y : Silhouette p N r) (X:Charts p n d) (Z:Charts p n e) (m:Mixer p n)
    (o o':UnitType p n N) (i:Messenger q) :
    (g.binding p a b).chimera o o' X Z m Y i=
    let H:= g i
    circlet (wisp p Y) (wake p Y m o X) (wake p Y m o' Z) H.1 i.1 H.2 := by
  classical
  let H:=g i
  let μ:= lawOmega p N H.1.l H.1.q
  let u:= Y H.1.l H.1.q
  let F:=couplePage (wake p Y m o X) (wake p Y m o' Z) H.1 i.1
  change _=avg (mapW μ u) (fun i =>F i H.2)
  rw [mapW_avg]
  rfl
end Engagement

set_option maxHeartbeats 1200000 in
theorem processions (K:ℕ) {u:Terrain p r} {s:Gazette p r d} {t:Gazette p r e} (A:Stalls p) (B:Stalls p) (a b:Pin p n N)
    (X:Charts p n d) (W:Charts p n e) (T:Cross p n)
    (hA:charted X a.sp) (hB:charted W b.sp) (ha:tableInj a.sp b.sp T) (hb:tableInj b.sp a.sp
      (reciprocal p T))
    (x y:Stalls p) (hX:booths p K a.sp x) (hY:booths p K b.sp y) (hx: x ≤ A) (hy: y ≤ B)
    (hg:2≤p.g) (hp:1≤p.J)
    (H:Straps (Label p.b))
    (ht : ∀ i:Grid,(stellar u s t η A B i).travels H 100 (view _ _)
       (chapter (stellar u s t η A B) H i))
    (hv:scorecard (chapter (stellar u s t η A B) H) (hailing p X W T)) :
    ∃ (q:Volumes) (g:Engagement p (toFormat q) d e) (s0 t0:Script p (Messenger (toFormat q))),
       (g.binding p s0 t0).chances X W a b T K ∧ ∀ i:Messenger (toFormat q),
       η≤circlet u s t (g i).1 i.1 (g i).2 := by
  classical
  obtain ⟨v,hv,hp0⟩:=hv
  let C:=stellar u s t η A B
  obtain ⟨g,hg'⟩:= full_parade C H ht hv
  obtain ⟨q,g,hI,hG,hS,hQ⟩:=invite p u s t A B η v H g hg'
  let z:=g.tags p; let w:=g.bits p; let F0:=g.genre0 p; let F1:=g.genre1 p
  have hM : F0.up z w ∧ F1.up z w := by
    constructor
    · exact ⟨hS true,fun i=> (hG i).2.2.2.1.2.1,fun i=> (hG i).2.2.2.1.1⟩
    exact ⟨hS false,fun i=> (hG i).2.2.2.2.1.2.1,fun i=>(hG i).2.2.2.2.1.1⟩
  obtain ⟨P,Q,hP⟩:= optionVia (toFormat q) d e a b T K ha hb z X W hA hB F0 F1 x y hX hY
    (fun i h=> (hG i).1 (hx _ h)) (fun i h=> (hG i).2.1 (hy _ h)) w hM.1 hM.2 hp hg hI
    (by
      have he : sendSum w F0.amp F1.amp = v := funext (fun i=>hQ i)
      rw [he]; exact hp0)
  exact ⟨q,g,P,Q,hP,fun i=>(hG i).2.2.2.2.2⟩

end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
