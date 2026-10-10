import Mathlib
import OAI.Geometry.HyperbolicGroups.PathLocalToGlobal
import OAI.Geometry.HyperbolicGroups.FinitePolyhedronEdgePaths

namespace OAI

noncomputable section

open Set
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V] [DecidableEq V] (K : AbstractSimplicialComplex V)

namespace EdgeChain
variable {K}
def append {a b c : V} : EdgeChain K a b → EdgeChain K b c → EdgeChain K a c
  | .nil _, q => q
  | .cons h p, q => .cons h (append p q)

def path {a b : V} : EdgeChain K a b → Path (vertex K a) (vertex K b)
  | .nil _ => .refl _
  | .cons h p => (edgePath K h).trans p.path

abbrev pathClass {a b : V} (p : EdgeChain K a b) :
    Path.Homotopic.Quotient (vertex K a) (vertex K b) := .mk p.path

@[simp] lemma pathClass_nil (a : V) : pathClass (.nil a : EdgeChain K a a) = .refl _ := rfl
@[simp] lemma pathClass_cons {a b c : V} (h : {a,b} ∈ K.faces) (p : EdgeChain K b c) :
    pathClass (.cons h p) = (Path.Homotopic.Quotient.mk (edgePath K h)).trans p.pathClass := rfl

@[simp] lemma pathClass_append {a b c : V} (p : EdgeChain K a b) (q : EdgeChain K b c) :
    (p.append q).pathClass = p.pathClass.trans q.pathClass := by
  induction p with
  | nil _ => simp [append]
  | cons h p ih => simp only [append,pathClass_cons,ih,Path.Homotopic.Quotient.trans_assoc]
end EdgeChain

/-- Normal form with one radial segment at each endpoint. -/
def EdgeTame {x y : Carrier K} (p : Path.Homotopic.Quotient x y) : Prop :=
  ∃ (a b : V) (ha : x ∈ openStar K a) (hb : y ∈ openStar K b) (c : EdgeChain K a b),
    p = (Path.Homotopic.Quotient.mk (starPath K a x ha)).symm.trans
      (c.pathClass.trans (Path.Homotopic.Quotient.mk (starPath K b y hb)))

lemma edgeTame_of_star {x y : Carrier K} (v : V) (p : Path x y)
    (hp : ∀ t, p t ∈ openStar K v) : EdgeTame K (.mk p) := by
  have hx : x ∈ openStar K v := p.source ▸ hp 0
  have hy : y ∈ openStar K v := p.target ▸ hp 1
  refine ⟨v,v,hx,hy,.nil v,?_⟩
  simp only [EdgeChain.pathClass_nil,Path.Homotopic.Quotient.refl_trans,
    ←Path.Homotopic.Quotient.mk_symm,←Path.Homotopic.Quotient.mk_trans]
  apply Path.Homotopic.Quotient.eq.mpr
  apply homotopic_in_star K v p _ hp
  intro t
  have ht := mem_range_self (f := (starPath K v x hx).symm.trans (starPath K v y hy)) t
  rw [Path.trans_range] at ht
  rcases ht with ⟨u,heq⟩|⟨u,heq⟩
  · rw [←heq]; exact starPath_mem K v x hx (unitInterval.symm u)
  · rw [←heq]; exact starPath_mem K v y hy u

lemma edgeTame_refl (x : Carrier K) : EdgeTame K (.refl x) := by
  obtain ⟨v,hv⟩ := exists_positive K x
  exact edgeTame_of_star K v (.refl x) (fun _ => hv)

lemma edgeTame_trans {x y z : Carrier K} {p : Path.Homotopic.Quotient x y}
    {q : Path.Homotopic.Quotient y z} (hp : EdgeTame K p) (hq : EdgeTame K q) :
    EdgeTame K (p.trans q) := by
  obtain ⟨a,b,ha,hb,c,rfl⟩ := hp
  obtain ⟨d,e,hd,he,f,rfl⟩ := hq
  refine ⟨a,e,ha,he,c.append (.cons (commonStar_edge K y hb hd) f),?_⟩
  have hbridge := Path.Homotopic.Quotient.eq.mpr (radial_bridge K y hb hd)
  change (Path.Homotopic.Quotient.mk (starPath K b y hb)).trans
    (Path.Homotopic.Quotient.mk (starPath K d y hd)).symm = _ at hbridge
  simp only [EdgeChain.pathClass_append,EdgeChain.pathClass_cons,
    Path.Homotopic.Quotient.trans_assoc]
  rw [←hbridge]
  simp only [Path.Homotopic.Quotient.trans_assoc]

theorem all_paths_edgeTame {x y : Carrier K} (p : Path x y) : EdgeTame K (.mk p) :=
  PathLocalToGlobal.of_open_cover (fun _ _ => EdgeTame K) (openStar K)
    (openStar_isOpen K) (exists_positive K) (edgeTame_refl K)
    (fun hp hq => edgeTame_trans K hp hq)
    (fun index {_ _} path hypothesis => edgeTame_of_star K index path hypothesis) p

lemma vertex_in_openStar {a b : V} (h : vertex K a ∈ openStar K b) : a = b := by
  by_contra hn
  have he : b ≠ a := Ne.symm hn
  change 0 < (vertex K a).val b at h
  simp [vertex,he] at h

@[simp] lemma starPath_self (a : V) (h : vertex K a ∈ openStar K a) :
    starPath K a (vertex K a) h = Path.refl (vertex K a) := by
  apply Path.ext
  funext t
  apply Subtype.ext
  exact AffineMap.lineMap_same_apply _ _

/-- Every actual continuous path between vertices has a finite edge-chain
representative, with the same endpoints and in its actual homotopy class. -/
theorem edgePath_representative {a b : V} (p : Path (vertex K a) (vertex K b)) :
    ∃ c : EdgeChain K a b, p.Homotopic c.path := by
  obtain ⟨x,y,hx,hy,c,hc⟩ := all_paths_edgeTame K p
  have ha := vertex_in_openStar K hx
  have hb := vertex_in_openStar K hy
  subst x; subst y
  refine ⟨c,Path.Homotopic.Quotient.eq.mp ?_⟩
  have hr : (Path.Homotopic.Quotient.refl (vertex K a)).symm = .refl _ := rfl
  simpa only [starPath_self, Path.Homotopic.Quotient.mk_refl, hr,
    Path.Homotopic.Quotient.refl_trans,Path.Homotopic.Quotient.trans_refl] using hc

end HyperbolicObstruction.FinitePolyhedron
end

end OAI
