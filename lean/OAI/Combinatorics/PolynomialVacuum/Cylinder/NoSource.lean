import OAI.Combinatorics.PolynomialVacuum.Cylinder.OpenCurrent

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

 
def SupportedAt (D : Finset (Vertex M)) (q : Edge M →₀ ℤ) : Prop :=
  ∀g : Germ M,g.1∉D → (reverseGerm g).1∉D → orientedFlow q g=0

namespace OpenIce
variable (D : Finset (Vertex M)) (q : Edge M →₀ ℤ) (hq : ∀v∈D,LocalIce q v)

theorem enter_of_neg (v : activeInside D q) (k : Fin 3) (h : orientedFlow q (v.val,k)= -1) :
    enter D q hq v=k := by
  rw [at_slot D q hq v k] at h
  split_ifs at h <;> omega

theorem exit_of_pos (v : activeInside D q) (k : Fin 3) (h : orientedFlow q (v.val,k)=1) :
    exit D q hq v=k := by
  rw [at_slot D q hq v k] at h
  split_ifs at h <;> omega

 

theorem no_source_no_exit
    (hs : ∀a : activeInside D q,¬(network D q hq).Source a)
    (a : activeInside D q) : neighbor a.val (exit D q hq a)∈activeInside D q := by
  have hin : ∀v : activeInside D q,neighbor v.val (enter D q hq v)∈activeInside D q := by
    intro v
    by_contra h
    exact hs v h
  let prev (v : activeInside D q) : activeInside D q:=⟨neighbor v.val (enter D q hq v),hin v⟩
  have hp : ∀v,(network D q hq).next (prev v)=some v := by
    intro v
    apply ((network D q hq).next_some (prev v) v).mpr
    have he : exit D q hq (prev v)=enter D q hq v := by
      apply exit_of_pos D q hq
      change orientedFlow q (reverseGerm (v.val,enter D q hq v))=1
      rw [orientedFlow_reverse,at_enter D q hq]
      norm_num
    change neighbor (neighbor v.val (enter D q hq v)) (exit D q hq (prev v))=v.val
    rw [he,neighbor_neighbor]
  have hi : Function.Injective prev := by
    intro u v huv
    have hh:=(hp u).symm.trans ((congrArg (network D q hq).next huv).trans (hp v))
    exact Option.some.inj hh
  obtain ⟨v,hv⟩:=Finite.surjective_of_injective hi a
  have hvn :=hp v
  rw [hv] at hvn
  have he :=((network D q hq).next_some a v).mp hvn
  change neighbor a.val (exit D q hq a)=v.val at he
  rw [he]
  exact v.property

theorem no_source_outside_zero (hsupp : SupportedAt D q)
    (hs : ∀a : activeInside D q,¬(network D q hq).Source a)
    (v : Vertex M) (hv : v∉D) : ∀k,orientedFlow q (v,k)=0 := by
  intro k
  by_contra hk
  have hn : neighbor v k∈D := by
    by_contra hn
    exact hk (hsupp (v,k) hv hn)
  have ha : neighbor v k∈activeInside D q := by
    apply Finset.mem_inter.mpr ⟨?_,hn⟩
    apply (mem_activeSites q _).mpr
    refine ⟨k,?_⟩
    change orientedFlow q (reverseGerm (v,k))≠0
    simpa only [orientedFlow_reverse,neg_ne_zero] using hk
  let a : activeInside D q:=⟨neighbor v k,ha⟩
  have him : neighbor a.val k=v := neighbor_neighbor v k
  have hnk : orientedFlow q (a.val,k)≠0 := by
    change orientedFlow q (reverseGerm (v,k))≠0
    simpa only [orientedFlow_reverse,neg_ne_zero] using hk
  rw [at_slot D q hq a k] at hnk
  have hc : k=exit D q hq a ∨ k=enter D q hq a := by
    by_contra hh
    simp only [not_or] at hh
    simp [hh.1,hh.2] at hnk
  rcases hc with he | he
  · have hx := no_source_no_exit D q hq hs a
    rw [← he,him] at hx
    exact hv (Finset.mem_inter.mp hx).2
  · apply hs a
    change neighbor a.val (enter D q hq a)∉activeInside D q
    rw [← he,him]
    intro hh
    exact hv (Finset.mem_inter.mp hh).2

theorem no_source_global_ice (hsupp : SupportedAt D q)
    (hs : ∀a : activeInside D q,¬(network D q hq).Source a) : ∀v,LocalIce q v := by
  intro v
  by_cases hv : v∈D
  · exact hq v hv
  · exact Or.inl (no_source_outside_zero D q hq hsupp hs v hv)

theorem no_source_active_subset (hsupp : SupportedAt D q)
    (hs : ∀a : activeInside D q,¬(network D q hq).Source a) : activeSites q⊆D := by
  intro v hv
  by_contra hn
  obtain ⟨k,hk⟩:=(mem_activeSites q v).mp hv
  exact hk (no_source_outside_zero D q hq hsupp hs v hn k)

end OpenIce
end PolynomialVacuumCylinder

end OAI
