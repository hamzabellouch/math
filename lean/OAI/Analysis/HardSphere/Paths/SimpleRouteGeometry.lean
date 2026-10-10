import Mathlib
import OAI.Analysis.HardSphere.Conditioning.SlotMultiplicity
import OAI.Analysis.HardSphere.Allocation.PhysicalRouteGeometry
import OAI.Analysis.HardSphere.Allocation.RouteCenters

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K} {J : Type*}

def simpleRouteVertices (p : SimplePath x y) (n : ℕ) : Fin (n+2)→Fin 3→Fin K :=
  fun i ↦ siteIndex (p.val.getVert i.val)

lemma simpleRouteVertices_zero (p : SimplePath x y) (n : ℕ) :
    simpleRouteVertices p n 0=siteIndex x := by simp [simpleRouteVertices]
lemma simpleRouteVertices_last (p : SimplePath x y) (n : ℕ) (hn : n+1=p.val.length) :
    simpleRouteVertices p n (Fin.last (n+1))=siteIndex y := by
  simp only [simpleRouteVertices,Fin.val_last,hn,SimpleGraph.Walk.getVert_length]

omit [NeZero K] in
lemma simpleRouteVertices_adjacent (p : SimplePath x y) (n : ℕ) (hn : n+1=p.val.length)
    (i : Fin (n+1)) :
    (torusNearestGraph K).Adj (p.val.getVert i.castSucc.val) (p.val.getVert i.succ.val) :=
  p.val.adj_getVert_succ (by simpa only [Fin.val_castSucc, ←hn] using i.isLt)

lemma simpleRouteVertices_distance {L : Length} (hL : L.val=(K:ℝ))
    (p : SimplePath x y) (n : ℕ) (hn : n+1=p.val.length) :
    ∀i:Fin (n+1),torusDistance L (gridCenter L (simpleRouteVertices p n i.castSucc))
      (gridCenter L (simpleRouteVertices p n i.succ))≤1 :=
  fun i ↦ adjacent_center_distance hL (simpleRouteVertices_adjacent p n hn i)

def simpleRouteSteps {L : Length} (hL : L.val=(K:ℝ))
    (p : SimplePath x y) (n : ℕ) (hn : n+1=p.val.length) : Fin (n+1)→Fin 7 :=
  fun i ↦ (adjacent_routeCellPeriod hL (simpleRouteVertices_adjacent p n hn i)).choose

lemma simpleRouteSteps_period {L : Length} (hL : L.val=(K:ℝ))
    (p : SimplePath x y) (n : ℕ) (hn : n+1=p.val.length) :
    ∀ i : Fin (n+1), projectPoint L (routeCellPeriod (simpleRouteVertices p n i.succ)
      (simpleRouteVertices p n i.castSucc) (simpleRouteSteps hL p n hn i))=0 :=
  fun i ↦ (adjacent_routeCellPeriod hL (simpleRouteVertices_adjacent p n hn i)).choose_spec

lemma gridSite_slotCenter {home : J→Fin 3→Fin K} (w : DiscreteTorus K) :
    (fun i ↦ gridSite (slotCenter home (siteIndex w) i))=
      extendedAnchor (fun j ↦ gridSite (home j)) w := by
  funext i
  cases i with
  | none => exact indexSite_siteIndex w
  | some j => rfl

lemma routeSlots_reparam {d e : ℕ} (f : Fin d↪J) (h : e=d) :
    routeSlots ((finCongr h).toEmbedding.trans f)=routeSlots f := by
  subst e
  rfl

lemma simpleRouteSlots {n : ℕ} (p : SimplePath x y) (hn : n+1=p.val.length)
    (home : J→Fin 3→Fin K) (f : Fin (n+1)↪J)
    (hf : ∀i,home (f i)=simpleRouteVertices p n i.castSucc) :
    ∃ pick : Fin p.val.length→J, ∃ H : ∀i,gridSite (home (pick i))=pathVertexEmbedding p i.castSucc,
      routeSlots f=routeSlots (departureEmbedding p (fun j ↦ gridSite (home j)) pick H) := by
  let pick : Fin p.val.length→J := fun i ↦ f (Fin.cast hn.symm i)
  have hp : ∀i,gridSite (home (pick i))=pathVertexEmbedding p i.castSucc := by
    intro i
    dsimp only [pick]
    rw [hf]
    exact indexSite_siteIndex _
  refine ⟨pick,hp,?_⟩
  have he : departureEmbedding p (fun j ↦ gridSite (home j)) pick hp=
      (finCongr hn.symm).toEmbedding.trans f := by ext i; rfl
  rw [he,routeSlots_reparam]

lemma simpleRoute_near_first {n l : ℕ} (p q : SimplePath x y)
    (hn : n+1=p.val.length) (hl : l+1=q.val.length)
    (home : J→Fin 3→Fin K) (f : Fin (n+1)↪J) (g : Fin (l+1)↪J)
    (hf : ∀i,home (f i)=simpleRouteVertices p n i.castSucc)
    (hg : ∀i,home (g i)=simpleRouteVertices q l i.castSucc) (R : ℕ) :
    (nearSlots (torusNear K R) (fun i ↦ gridSite (slotCenter home (siteIndex y) i))
      (routeSlots f) (routeSlots g)).card≤ simpleEncounter R p q := by
  obtain ⟨pick,hpick,hp⟩ := simpleRouteSlots p hn home f hf
  obtain ⟨choose,hchoose,hq⟩ := simpleRouteSlots q hl home g hg
  rw [gridSite_slotCenter,hp,hq]
  exact simple_nearSlots_bound R p q _ pick choose hpick hchoose

lemma simpleRoute_near_second {n l : ℕ} (p q : SimplePath x y)
    (hn : n+1=p.val.length) (hl : l+1=q.val.length)
    (home : J→Fin 3→Fin K) (f : Fin (n+1)↪J) (g : Fin (l+1)↪J)
    (hf : ∀i,home (f i)=simpleRouteVertices p n i.castSucc)
    (hg : ∀i,home (g i)=simpleRouteVertices q l i.castSucc) (R : ℕ) :
    (nearSlots (torusNear K R) (fun i ↦ gridSite (slotCenter home (siteIndex x) i))
      (routeSlots f) (routeSlots g)).card≤2*simpleEncounter R p q := by
  obtain ⟨pick,hpick,hp⟩ := simpleRouteSlots p hn home f hf
  obtain ⟨choose,hchoose,hq⟩ := simpleRouteSlots q hl home g hg
  rw [gridSite_slotCenter,hp,hq]
  exact second_primary_nearSlots_bound R p q _ pick choose hpick hchoose

end HardSphere.Groups
end
end

end OAI
