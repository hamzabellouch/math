import Mathlib

namespace OAI

section
section
section
noncomputable section
namespace CannonCycleOrder
open Set SimpleGraph

def next {n:ℕ} (hn:0<n) (i:Fin n) : Fin n :=
  if h:i.val+1<n then ⟨i.val+1,h⟩ else ⟨0,hn⟩

lemma next_surjective {n:ℕ} (hn:0<n) : Function.Surjective (next hn) := by
  intro i
  by_cases hi:i.val=0
  · refine ⟨⟨n-1,by omega⟩,?_⟩
    apply Fin.ext
    simp only [next]
    split_ifs with h <;> dsimp <;> omega
  · refine ⟨⟨i.val-1,by omega⟩,?_⟩
    apply Fin.ext
    simp only [next]
    split_ifs with h <;> dsimp <;> omega

lemma next_ne {n:ℕ} (hn:0<n) (hn2:2≤n) (i:Fin n) : next hn i≠i := by
  intro he
  have hh:=congrArg Fin.val he
  simp only [next] at hh
  split_ifs at hh <;> dsimp at hh <;> omega

lemma next_mod {n:ℕ} (hn:0<n) (i:Fin n) : (next hn i).val=(i.val+1)%n := by
  simp only [next]
  split_ifs with h
  · exact (Nat.mod_eq_of_lt h).symm
  · dsimp
    have he:i.val+1=n := by omega
    simp [he]

def bipartite {E A:Type*} (R:E→A→Prop) : SimpleGraph (E⊕A) where
  Adj
    | .inl e,.inr a => R e a
    | .inr a,.inl e => R e a
    | _,_ => False
  symm := ⟨by intro x y h; cases x <;> cases y <;> exact h⟩
  loopless := ⟨by intro x; cases x <;> exact id⟩

def tag {E A:Type*} : E⊕A→ℕ | .inl _ => 0 | .inr _ => 1

lemma walk_tag {E A:Type*} {R:E→A→Prop} {e:E} {z:E⊕A}
    (p:(bipartite R).Walk (.inl e) z) : ∀ k≤p.length,tag (p.getVert k)=k%2 := by
  intro k
  induction k with
  | zero => intro _; simp [tag]
  | succ k ih =>
    intro hk
    have hr := ih (by omega)
    have ha := p.adj_getVert_succ (i:=k) (by omega)
    have hstep : tag (p.getVert (k+1))+tag (p.getVert k)=1 := by
      cases h0:p.getVert k <;> cases h1:p.getVert (k+1) <;>
        simp_all [bipartite,tag]
    rw [hr] at hstep
    omega

theorem exists_order {E A:Type*} [Finite E] [Finite A] (R:E→A→Prop)
    (hc:(bipartite R).IsCycles) (hp:(bipartite R).Preconnected)
    (hne:∃ e a,R e a) :
    ∃ n:ℕ,∃ hn:0<n,∃ e:Fin n≃E,∃ a:Fin n≃A,
      2≤n ∧ (∀ i,R (e i) (a i)) ∧ (∀ i,R (e (next hn i)) (a i)) := by
  classical
  obtain ⟨e₀,a₀,he₀⟩ := hne
  let G := bipartite R
  obtain ⟨p,hpc,hcover⟩ := hc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c:=G.connectedComponentMk (.inl e₀)) (by rfl)
    (show (G.neighborSet (.inl e₀)).Nonempty from ⟨.inr a₀,he₀⟩)
  have hsupp (z:E⊕A) : z∈p.support := by
    rw [←p.mem_verts_toSubgraph,hcover]
    change G.connectedComponentMk z=G.connectedComponentMk (.inl e₀)
    exact ConnectedComponent.sound (hp z (.inl e₀))
  have hpar := walk_tag p
  have heven : p.length%2=0 := by
    have hh := hpar p.length le_rfl
    simpa only [p.getVert_length,tag] using hh.symm
  let n := p.length/2
  have hlen : p.length=2*n := by omega
  have hn : 0<n := by have hh:=hpc.three_le_length; omega
  have hs (z:E⊕A) : ∃ k<p.length,p.getVert k=z := by
    obtain ⟨k,hk,hkl⟩ := Walk.mem_support_iff_exists_getVert.mp (hsupp z)
    by_cases h:k<p.length
    · exact ⟨k,h,hk⟩
    · have he:k=p.length := by omega
      exact ⟨0,by omega,by simpa [he] using hk⟩
  have exE (i:Fin n) : ∃ e:E,p.getVert (2*i.val)=.inl e := by
    have hh := hpar (2*i.val) (by omega)
    cases hv:p.getVert (2*i.val) with
    | inl e => exact ⟨e,rfl⟩
    | inr a => simp [hv,tag] at hh
  have exA (i:Fin n) : ∃ a:A,p.getVert (2*i.val+1)=.inr a := by
    have hh := hpar (2*i.val+1) (by omega)
    cases hv:p.getVert (2*i.val+1) with
    | inl e => simp [hv,tag] at hh
    | inr a => exact ⟨a,rfl⟩
  choose e he using exE
  choose a ha using exA
  have hein : Function.Injective e := by
    intro i j hij
    have hh := hpc.getVert_injOn' (by change 2*i.val≤p.length-1; omega)
      (by change 2*j.val≤p.length-1; omega) ((he i).trans ((congrArg Sum.inl hij).trans (he j).symm))
    apply Fin.ext; omega
  have hain : Function.Injective a := by
    intro i j hij
    have hh := hpc.getVert_injOn' (by change 2*i.val+1≤p.length-1; omega)
      (by change 2*j.val+1≤p.length-1; omega) ((ha i).trans ((congrArg Sum.inr hij).trans (ha j).symm))
    apply Fin.ext; omega
  have hesur : Function.Surjective e := by
    intro v
    obtain ⟨k,hk,hv⟩ := hs (.inl v)
    have hm := hpar k (by omega)
    simp only [hv,tag] at hm
    let i:Fin n := ⟨k/2,by omega⟩
    have heq:2*i.val=k := by dsimp [i]; omega
    exact ⟨i,Sum.inl.inj ((he i).symm.trans (by simpa only [heq] using hv))⟩
  have hasur : Function.Surjective a := by
    intro v
    obtain ⟨k,hk,hv⟩ := hs (.inr v)
    have hm := hpar k (by omega)
    simp only [hv,tag] at hm
    let i:Fin n := ⟨k/2,by omega⟩
    have heq:2*i.val+1=k := by dsimp [i]; omega
    exact ⟨i,Sum.inr.inj ((ha i).symm.trans (by simpa only [heq] using hv))⟩
  have hnext (i:Fin n) : p.getVert (2*i.val+2)=.inl (e (next hn i)) := by
    unfold next
    split_ifs with h
    · convert he ⟨i.val+1,h⟩ using 1
    · have hi:2*i.val+2=p.length := by omega
      rw [hi,p.getVert_length]
      simpa using (he ⟨0,hn⟩)
  refine ⟨n,hn,Equiv.ofBijective e ⟨hein,hesur⟩,Equiv.ofBijective a ⟨hain,hasur⟩,by have hh:=hpc.three_le_length; omega,?_,?_⟩
  · intro i
    have hh := p.adj_getVert_succ (i:=2*i.val) (by omega)
    rw [he i,ha i] at hh
    exact hh
  · intro i
    have hh := p.adj_getVert_succ (i:=2*i.val+1) (by omega)
    have heq:2*i.val+1+1=2*i.val+2 := by omega
    rw [heq,ha i,hnext i] at hh
    exact hh
end CannonCycleOrder

end
end
end
end

end OAI
