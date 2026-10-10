import OAI.Combinatorics.PortMatching.Basic

namespace OAI

/-! Perfect-matching-preserving port-path degree reduction for finite simple graphs. -/

noncomputable section
namespace Matching205
namespace Reverse
universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma unique_missing {r : ℕ} (hr : 0 < r) (f : Fin (r-1) → Fin r)
    (hf : Function.Injective f) : ∃! p, ∀ q, f q ≠ p := by
  classical
  let s := Finset.univ.image f
  have hs : s.card = r-1 := by
    dsimp [s]
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  have hc : (Finset.univ \ s).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ s), Finset.card_univ,
      Fintype.card_fin, hs]
    omega
  have h := Finset.card_eq_one_iff_existsUnique.mp hc
  simpa [s, Finset.mem_sdiff, Finset.mem_image] using h

variable {G}
def mate {M : (graph G).Subgraph} (hM : M.IsPerfectMatching) (x : Vertex G) : Vertex G :=
  (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM x).choose
lemma mate_adj {M : (graph G).Subgraph} (hM : M.IsPerfectMatching) (x : Vertex G) :
    M.Adj x (mate hM x) :=
  (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM x).choose_spec.1
lemma mate_eq {M : (graph G).Subgraph} (hM : M.IsPerfectMatching)
    {x y : Vertex G} (h : M.Adj x y) : mate hM x = y :=
  hM.1.eq_of_adj_left (mate_adj hM x) h
lemma mate_involutive {M : (graph G).Subgraph} (hM : M.IsPerfectMatching) :
    Function.Involutive (mate hM) := fun x => mate_eq hM (mate_adj hM x).symm

variable (G)
def evenPosition (hpos : ∀ v, 0 < arity G v) (v : V) (j : Fin (arity G v)) : Vertex G :=
  ⟨v, ⟨2*j.val, by have := j.isLt; have := hpos v; omega⟩⟩
def nonport (v : V) (q : Fin (arity G v-1)) : Vertex G :=
  ⟨v, ⟨2*q.val+1, by have := q.isLt; omega⟩⟩
lemma evenPosition_injective (hpos : ∀ v, 0 < arity G v) (v : V) :
    Function.Injective (evenPosition G hpos v) := by
  intro i j h
  have h' := congrArg (fun x : Vertex G => x.2.val) h
  apply Fin.ext
  dsimp [evenPosition] at h'
  omega
lemma nonport_injective (v : V) : Function.Injective (nonport G v) := by
  intro i j h
  have h' := congrArg (fun x : Vertex G => x.2.val) h
  apply Fin.ext
  dsimp [nonport] at h'
  omega
lemma port_eq_evenPosition (hpos : ∀ v, 0 < arity G v) (v : V)
    (w : G.neighborSet v) :
    port G v w = evenPosition G hpos v (Fintype.equivFin _ w) := rfl

lemma nonport_not_external (v : V) (q : Fin (arity G v-1)) (y : Vertex G) :
    ¬ External G (nonport G v q) y := by
  rintro ⟨h, hx, _⟩
  have hx' := congrArg (fun x : Vertex G => x.2.val) hx
  dsimp [nonport, port] at hx'
  omega

lemma internal_nonport_even (hpos : ∀ v, 0 < arity G v) (v : V)
    (q : Fin (arity G v-1)) {y : Vertex G}
    (h : Internal G (nonport G v q) y) :
    ∃ j, y = evenPosition G hpos v j := by
  rcases y with ⟨w,i⟩
  have hw : v = w := h.1
  subst w
  have hi := i.isLt
  have hn := h.2
  dsimp [nonport] at hn
  have he : i.val % 2 = 0 := by omega
  let j : Fin (arity G v) := ⟨i.val / 2, by omega⟩
  refine ⟨j, ?_⟩
  congr 1
  apply Fin.ext
  dsimp [evenPosition, j]
  omega

lemma internal_even_nonport (hpos : ∀ v, 0 < arity G v) (v : V)
    (j : Fin (arity G v)) {y : Vertex G}
    (h : Internal G (evenPosition G hpos v j) y) :
    ∃ q, y = nonport G v q := by
  rcases y with ⟨w,i⟩
  have hw : v = w := h.1
  subst w
  have hi := i.isLt
  have hn := h.2
  dsimp [evenPosition] at hn
  have he : i.val % 2 = 1 := by omega
  let q : Fin (arity G v-1) := ⟨i.val / 2, by omega⟩
  refine ⟨q, ?_⟩
  congr 1
  apply Fin.ext
  dsimp [nonport, q]
  omega

lemma mate_nonport_even (hpos : ∀ v, 0 < arity G v)
    {M : (graph G).Subgraph} (hM : M.IsPerfectMatching)
    (v : V) (q : Fin (arity G v-1)) :
    ∃ j, mate hM (nonport G v q) = evenPosition G hpos v j := by
  have h := M.adj_sub (mate_adj hM (nonport G v q))
  change Internal G _ _ ∨ External G _ _ at h
  rcases h with h | h
  · exact internal_nonport_even G hpos v q h
  · exact (nonport_not_external G v q _ h).elim

def pairedPort (hpos : ∀ v, 0 < arity G v)
    {M : (graph G).Subgraph} (hM : M.IsPerfectMatching)
    (v : V) (q : Fin (arity G v-1)) : Fin (arity G v) :=
  (mate_nonport_even G hpos hM v q).choose
lemma pairedPort_spec (hpos : ∀ v, 0 < arity G v)
    {M : (graph G).Subgraph} (hM : M.IsPerfectMatching)
    (v : V) (q : Fin (arity G v-1)) :
    mate hM (nonport G v q) = evenPosition G hpos v (pairedPort G hpos hM v q) :=
  (mate_nonport_even G hpos hM v q).choose_spec
lemma pairedPort_injective (hpos : ∀ v, 0 < arity G v)
    {M : (graph G).Subgraph} (hM : M.IsPerfectMatching) (v : V) :
    Function.Injective (pairedPort G hpos hM v) := by
  intro i j h
  apply nonport_injective G v
  apply (mate_involutive hM).injective
  rw [pairedPort_spec G hpos hM, pairedPort_spec G hpos hM, h]

lemma external_iff_missing (hpos : ∀ v, 0 < arity G v)
    {M : (graph G).Subgraph} (hM : M.IsPerfectMatching)
    (v : V) (j : Fin (arity G v)) :
    External G (evenPosition G hpos v j) (mate hM (evenPosition G hpos v j)) ↔
      ∀ q, pairedPort G hpos hM v q ≠ j := by
  constructor
  · intro he q hq
    have hp := pairedPort_spec G hpos hM v q
    rw [hq] at hp
    have hm := congrArg (mate hM) hp
    rw [mate_involutive hM] at hm
    obtain ⟨ha, _, _⟩ := he
    rw [← hm] at ha
    exact G.irrefl ha
  · intro hj
    have h := M.adj_sub (mate_adj hM (evenPosition G hpos v j))
    change Internal G _ _ ∨ External G _ _ at h
    rcases h with hi | he
    · obtain ⟨q, hq⟩ := internal_even_nonport G hpos v j hi
      have hm := congrArg (mate hM) hq
      rw [mate_involutive hM, pairedPort_spec G hpos hM] at hm
      exact (hj q ((evenPosition_injective G hpos v hm).symm)).elim
    · exact he

theorem unique_external_port (hpos : ∀ v, 0 < arity G v)
    {M : (graph G).Subgraph} (hM : M.IsPerfectMatching) (v : V) :
    ∃! j : Fin (arity G v),
      External G (evenPosition G hpos v j) (mate hM (evenPosition G hpos v j)) := by
  have h := unique_missing (hpos v) (pairedPort G hpos hM v)
    (pairedPort_injective G hpos hM v)
  simpa only [external_iff_missing] using h

end Reverse

universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem decode_isPerfectMatching (hpos : ∀ v, 0 < arity G v)
    {M : (graph G).Subgraph} (hM : M.IsPerfectMatching) :
    (decode G M).IsPerfectMatching := by
  classical
  apply SimpleGraph.Subgraph.isPerfectMatching_iff.mpr
  intro v
  obtain ⟨j, hj, hu⟩ := Reverse.unique_external_port G hpos hM v
  obtain ⟨ha, hx, hy⟩ := hj
  let y := Reverse.mate hM (Reverse.evenPosition G hpos v j)
  have ha' : G.Adj v y.1 := ha
  have hdec : (decode G M).Adj v y.1 := by
    refine ⟨ha', ?_⟩
    have hm := Reverse.mate_adj hM (Reverse.evenPosition G hpos v j)
    exact (congrArg₂ (fun a b : Vertex G => M.Adj a b) hx hy).mp hm
  refine ⟨y.1, hdec, ?_⟩
  intro w hw
  obtain ⟨haw, hmw⟩ := hw
  let k : Fin (arity G v) := Fintype.equivFin _ ⟨w, haw⟩
  have hport : port G v ⟨w, haw⟩ = Reverse.evenPosition G hpos v k := rfl
  have hmate : Reverse.mate hM (Reverse.evenPosition G hpos v k) =
      port G w ⟨v, haw.symm⟩ := by
    rw [← hport]
    exact Reverse.mate_eq hM hmw
  have hk : External G (Reverse.evenPosition G hpos v k)
      (Reverse.mate hM (Reverse.evenPosition G hpos v k)) := by
    rw [hmate, ← hport]
    exact ⟨haw, rfl, rfl⟩
  have hkj : k = j := hu k hk
  have heq : port G v ⟨w, haw⟩ = port G v ⟨y.1, ha'⟩ := by
    rw [hport, hkj]
    exact hx
  have hi := congrArg (fun x : Vertex G => x.2.val) heq
  dsimp [port] at hi
  have hf : Fintype.equivFin (G.neighborSet v) ⟨w, haw⟩ =
      Fintype.equivFin (G.neighborSet v) ⟨y.1, ha'⟩ := by
    apply Fin.ext
    omega
  exact congrArg Subtype.val ((Fintype.equivFin _).injective hf)

end Matching205

end

end OAI
