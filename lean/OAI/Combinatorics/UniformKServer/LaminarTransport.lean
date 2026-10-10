import Mathlib
import OAI.Combinatorics.UniformKServer.Epochs

namespace OAI

                                       
section

                                                                              
                                                                           
                                            
noncomputable section
namespace UniformKServer.LaminarTransport
open Finset
open scoped Classical
variable {I V E : Type*} [Fintype I] [Fintype E] [DecidableEq V]

def bit (C : Finset V) (x : V) : ℝ := if x∈C then 1 else 0
def cross (C : Finset V) (x y : V) : ℝ := |bit C x-bit C y|
def mass (C : Finset V) (a : I→V) : ℝ := ∑ i,bit C (a i)
def crossings (C : Finset V) (a b : I→V) (π : Equiv.Perm I) : ℝ :=
  ∑ i,cross C (a i) (b (π i))
def objective (C : E→Finset V) (a b : I→V) (π : Equiv.Perm I) : ℝ :=
  ∑ e,crossings (C e) a b π

def Laminar (C : E→Finset V) : Prop :=
  ∀ e f, C e⊆C f ∨ C f⊆C e ∨ Disjoint (C e) (C f)

theorem cross_swap_le {C B : Finset V} {x y u v : V}
    (hl : C⊆B ∨ B⊆C ∨ Disjoint C B)
    (hx : x∈C) (hy : y∉C) (hu : u∉C) (hv : v∈C) :
    cross B x v+cross B u y ≤ cross B x y+cross B u v := by
  rcases hl with h|h|h
  · have hxb := h hx
    have hvb := h hv
    by_cases hyb : y∈B <;> by_cases hub : u∈B <;>
      simp [cross,bit,hxb,hvb,hyb,hub]
  · have hyb : y∉B := fun h' => hy (h h')
    have hub : u∉B := fun h' => hu (h h')
    by_cases hxb : x∈B <;> by_cases hvb : v∈B <;>
      simp [cross,bit,hxb,hvb,hyb,hub]
  · have hxb : x∉B := fun h' => disjoint_left.mp h hx h'
    have hvb : v∉B := fun h' => disjoint_left.mp h hv h'
    by_cases hyb : y∈B <;> by_cases hub : u∈B <;>
      simp [cross,bit,hxb,hvb,hyb,hub]

theorem sum_swap (f : I→I→ℝ) (i j : I) (hij : i≠j) :
    (∑ u,f u (Equiv.swap i j u)) = (∑ u,f u u)+
      (f i j-f i i)+(f j i-f j j) := by
  classical
  have hp : ∀ u, f u (Equiv.swap i j u)=f u u+
      (if u=i then f i j-f i i else 0)+(if u=j then f j i-f j j else 0) := by
    intro u
    by_cases hi : u=i
    · subst u
      simp [hij]
    by_cases hj : u=j
    · subst u
      simp [Ne.symm hij]
    simp [Equiv.swap_apply_of_ne_of_ne hi hj,hi,hj]
  simp_rw [hp]
  simp only [sum_add_distrib]
  simp

theorem crossings_swap (C : Finset V) (a b : I→V) (π : Equiv.Perm I)
    (i j : I) (hij : i≠j) :
    crossings C a b ((Equiv.swap i j).trans π)=crossings C a b π+
      (cross C (a i) (b (π j))-cross C (a i) (b (π i)))+
      (cross C (a j) (b (π i))-cross C (a j) (b (π j))) := by
  exact sum_swap (fun u v=>cross C (a u) (b (π v))) i j hij

theorem no_opposite (C : E→Finset V) (a b : I→V) (hl : Laminar C)
    (π : Equiv.Perm I) (hπ : ∀ σ,objective C a b π≤objective C a b σ)
    (e : E) (i j : I) (hi : a i∈C e) (hbi : b (π i)∉C e)
    (hj : a j∉C e) (hbj : b (π j)∈C e) : False := by
  classical
  have hij : i≠j := by intro h; subst j; exact hj hi
  let σ := (Equiv.swap i j).trans π
  have hall : ∀ f,crossings (C f) a b σ≤crossings (C f) a b π := by
    intro f
    rw [crossings_swap _ _ _ _ _ _ hij]
    have h := cross_swap_le (hl e f) hi hbi hj hbj
    linarith
  have he : crossings (C e) a b σ<crossings (C e) a b π := by
    rw [crossings_swap _ _ _ _ _ _ hij]
    simp only [cross,bit,ite_eq_left hi,ite_eq_right hbi,ite_eq_right hj,ite_eq_left hbj]
    norm_num
  have hs : objective C a b σ<objective C a b π :=
    sum_lt_sum (fun f _=>hall f) ⟨e,mem_univ e,he⟩
  exact (not_lt_of_ge (hπ σ)) hs

theorem cut_identity (C : Finset V) (a b : I→V) (π : Equiv.Perm I)
    (hno : ∀ i j,a i∈C → b (π i)∉C → a j∉C → b (π j)∈C → False) :
    crossings C a b π=|mass C a-mass C b| := by
  have hm : (∑ i,bit C (b (π i)))=∑ i,bit C (b i) := Equiv.sum_comp π (fun i=>bit C (b i))
  have hs : (∑ i,(bit C (a i)-bit C (b (π i))))=mass C a-mass C b := by
    rw [sum_sub_distrib,hm]
    rfl
  by_cases ho : ∃ i,a i∈C ∧ b (π i)∉C
  · obtain ⟨i,hi,hbi⟩ := ho
    have hp : ∀ j,0≤bit C (a j)-bit C (b (π j)) := by
      intro j
      by_cases hj : a j∈C <;> by_cases hbj : b (π j)∈C
      · simp [bit,hj,hbj]
      · simp [bit,hj,hbj]
      · exact (hno i j hi hbi hj hbj).elim
      · simp [bit,hj,hbj]
    change (∑ j,|bit C (a j)-bit C (b (π j))|)=_
    simp_rw [abs_of_nonneg (hp _)]
    rw [hs,abs_of_nonneg (by rw [←hs]; exact sum_nonneg (fun j _=>hp j))]
  · have hp : ∀ j,bit C (a j)-bit C (b (π j))≤0 := by
      intro j
      by_cases hj : a j∈C <;> by_cases hbj : b (π j)∈C
      · simp [bit,hj,hbj]
      · exact (ho ⟨j,hj,hbj⟩).elim
      · simp [bit,hj,hbj]
      · simp [bit,hj,hbj]
    change (∑ j,|bit C (a j)-bit C (b (π j))|)=_
    simp_rw [abs_of_nonpos (hp _)]
    rw [sum_neg_distrib,hs,abs_of_nonpos (by rw [←hs]; exact sum_nonpos (fun j _=>hp j))]

theorem matching_exists (C : E→Finset V) (a b : I→V) (hl : Laminar C) :
    ∃ π : Equiv.Perm I,∀ e,crossings (C e) a b π=|mass (C e) a-mass (C e) b| := by
  classical
  obtain ⟨π,_,hπ⟩ := exists_min_image univ (objective C a b) (univ_nonempty : (univ : Finset (Equiv.Perm I)).Nonempty)
  refine ⟨π,fun e=>cut_identity (C e) a b π ?_⟩
  intro i j hi hbi hj hbj
  exact no_opposite C a b hl π (fun σ=>hπ σ (mem_univ σ)) e i j hi hbi hj hbj

end UniformKServer.LaminarTransport

end


end

end OAI
