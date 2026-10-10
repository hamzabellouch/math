import OAI.Combinatorics.ContingencyTables.Transport.EdmondsKarpDistance
import OAI.Combinatorics.ContingencyTables.Transport.PathAugmentation

namespace OAI

/-! # Label monotonicity and critical arcs of a shortest augmentation -/
namespace ContingencyTables.EdmondsKarpAugmentation
open PublishedEdmondsKarp PathAugmentation EdmondsKarpDistance
open scoped Classical
noncomputable section
variable {n k : ℕ}

lemma reverse_count_zero (p : Fin (k+1)→Fin n) (hp : Function.Injective p) (i : Fin k) :
    arcCount p (p i.succ) (p i.castSucc)=0 := by
  apply arcCount_eq_zero
  rintro ⟨j,hj,hi⟩
  have h1 := congrArg Fin.val (hp hj)
  have h2 := congrArg Fin.val (hp hi)
  simp only [Fin.val_castSucc,Fin.val_succ] at h1 h2
  omega

lemma update_decrease (f : Flow n) (p : Fin (k+1)→Fin n) (a : ℤ) (ha : 0 ≤ a)
    (u v : Fin n) (h : update f p a u v < f u v) :
    ∃ i : Fin k,p i.castSucc=v ∧ p i.succ=u := by
  by_contra hn
  have hz : arcCount p v u=0 := arcCount_eq_zero p v u hn
  have hc := arcCount_nonneg p u v
  have hprod := mul_nonneg ha hc
  simp only [update,hz,sub_zero] at h
  omega

lemma update_new_edge (c : Capacity n) (f : Flow n) (p : Fin (k+1)→Fin n)
    (a : ℤ) (ha : 0 ≤ a) (u v : Fin n)
    (h : 0 < (c u v:ℤ)-update f p a u v) :
    0 < (c u v:ℤ)-f u v ∨ ∃ i : Fin k,p i.castSucc=v ∧ p i.succ=u := by
  by_cases hold : 0 < (c u v:ℤ)-f u v
  · exact Or.inl hold
  · exact Or.inr (update_decrease f p a ha u v (by omega))

lemma update_saturates (c : Capacity n) (f : Flow n) (p : Fin (k+1)→Fin n)
    (hp : Function.Injective p) (a : ℤ) (i : Fin k)
    (ha : a=(c (p i.castSucc) (p i.succ):ℤ)-f (p i.castSucc) (p i.succ)) :
    update f p a (p i.castSucc) (p i.succ)=c (p i.castSucc) (p i.succ) := by
  rw [update,arcCount_eq_one p hp i,reverse_count_zero p hp i]
  omega

/-- All old distance labels remain valid lower potentials for the new
residual graph, including arcs created by cancellation of flow. -/
theorem labels_monotone {c : Capacity n} {s t : Fin n} {f g : Flow n}
    (h : ShortestAugmentation c s t f g) (v : Fin n) : label c f s v ≤ label c g s v := by
  obtain ⟨k,p,a,hp,hshort,ha,_,_,hg⟩ := h
  have he : g=update f p a := funext (fun u => funext (hg u))
  apply potential_le_distance (ResidualSearch.edge c g) s (label c f s)
    (label_source c f s) (label_le c f s)
  intro u v huv
  have hres : 0 < (c u v:ℤ)-g u v := of_decide_eq_true huv
  rw [he] at hres
  rcases update_new_edge c f p a ha.le u v hres with hold|⟨i,hi,hj⟩
  · exact label_edge hold
  · have h1 := label_path hp hshort i.castSucc
    have h2 := label_path hp hshort i.succ
    rw [hi] at h1
    rw [hj] at h2
    simp only [Fin.val_castSucc,Fin.val_succ] at h1 h2
    omega

/-- A decrease of flow on (u,v) means the augmentation used (v,u).
Consequently u was one distance layer beyond v. -/
theorem decrease_labels {c : Capacity n} {s t : Fin n} {f g : Flow n}
    (h : ShortestAugmentation c s t f g) (u v : Fin n) (hdec : g u v < f u v) :
    label c f s u=label c f s v+1 := by
  obtain ⟨k,p,a,hp,hshort,ha,_,_,hg⟩ := h
  have he : g=update f p a := funext (fun u => funext (hg u))
  rw [he] at hdec
  obtain ⟨i,hi,hj⟩ := update_decrease f p a ha.le u v hdec
  have h1 := label_path hp hshort i.castSucc
  have h2 := label_path hp hshort i.succ
  rw [hi] at h1
  rw [hj] at h2
  simp only [Fin.val_castSucc,Fin.val_succ] at h1 h2
  omega

/-- Each augmentation has an arc which was residual, becomes saturated,
and points from one finite distance layer to the next. -/
theorem critical_arc {c : Capacity n} {s t : Fin n} {f g : Flow n}
    (h : ShortestAugmentation c s t f g) :
    ∃ u v : Fin n,f u v < (c u v:ℤ) ∧ g u v=(c u v:ℤ) ∧
      label c f s v=label c f s u+1 ∧ label c f s u < n := by
  obtain ⟨k,p,a,hp,hshort,ha,_,⟨i,hsat⟩,hg⟩ := h
  have he : g=update f p a := funext (fun u => funext (hg u))
  refine ⟨p i.castSucc,p i.succ,?_,?_,?_,?_⟩
  · have hr := hp.2.2.2 i
    omega
  · rw [he]
    exact update_saturates c f p hp.2.2.1 a i hsat
  · rw [label_path hp hshort i.castSucc,label_path hp hshort i.succ]
    rfl
  · exact label_path_lt hp hshort i.castSucc

end
end ContingencyTables.EdmondsKarpAugmentation

end OAI
