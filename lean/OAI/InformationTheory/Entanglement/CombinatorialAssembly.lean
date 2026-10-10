import OAI.InformationTheory.Entanglement.CombinatorialLocal
import OAI.InformationTheory.Entanglement.MultiTensor

namespace OAI

noncomputable section
open scoped BigOperators
open Matrix
namespace FiniteConstruction
open ChannelCompletion

def P (i : Label) : Mat OutputCoordinate :=
  multiTensor (fun S => localProjection S i.1 (i.2 S))
lemma P_hermitian (i : Label) : (P i).IsHermitian :=
  multiTensor_hermitian _ (fun _ => localProjection_hermitian _ _ _)
lemma P_real (i : Label) (a b : OutputCoordinate) : star (P i a b)=P i a b := by
  simp only [P,multiTensor,star_prod]
  simp_rw [localProjection_real]
lemma P_idempotent (i : Label) : P i*P i=P i :=
  multiTensor_idempotent _ (fun _ => localProjection_idempotent _ _ _)
lemma P_orthogonal (i j : Label) (hq : i.1=j.1) (hij : i ≠ j) : P i*P j=0 := by
  obtain ⟨q,a⟩ := i
  obtain ⟨r,b⟩ := j
  dsimp only at hq
  subst r
  exact multiTensor_orthogonal _ (fun S => localProjection_orthogonal S q) a b
    (by intro he; subst b; exact hij rfl)
lemma P_complete (q : Question) : ∑ i : Label with i.1=q, P i=1 := by
  rw [Finset.sum_filter,Fintype.sum_prod_type]
  dsimp only
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [P]
  exact multiTensor_complete (fun S : Eight => fun a : Outcome => localProjection S q a)
    (fun S => localProjection_complete S q)
lemma P_commute (i j : Label) (hc : ProjectionCriterion.correlation u i.1 j.1 ≠ 0) :
    P i*P j=P j*P i :=
  multiTensor_commute _ _ (fun S => localProjection_commute S i.1 j.1 (i.2 S) (j.2 S) hc)
lemma P_overlap_product (i j : Label) :
    Matrix.trace (P i*P j)=∏ S, Matrix.trace
      (localProjection S i.1 (i.2 S)*localProjection S j.1 (j.2 S)) :=
  multiTensor_trace_mul _ _
lemma P_clique (J : Finset Label)
    (hJ : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → 0 < (Matrix.trace (P i*P j)).re) : J.card ≤ κ := by
  have hinj : Set.InjOn Prod.fst (J : Set Label) := by
    intro i hi j hj hq
    by_contra he
    have hz := P_orthogonal i j hq he
    have hh := hJ i hi j hj he
    rw [hz,Matrix.trace_zero,Complex.zero_re] at hh
    exact (lt_irrefl _ hh)
  have hcard := Finset.card_image_of_injOn hinj
  rw [← hcard]
  apply no_orthogonal_eight_bound
  intro hC
  obtain ⟨T,hT,cT,pT⟩ := hC
  let S : Eight := ⟨T,cT⟩
  have hS : OrthogonalEight S := pT
  have hf : ∀ t : Fin 6, ∃ i : Label, i ∈ J ∧ i.1=six S t := by
    intro t
    exact Finset.mem_image.mp (hT (six_mem S t))
  choose f hf hfst using hf
  obtain ⟨t,v,htv,hz⟩ := parity_zero_product (fun t => (f t).2 S)
  have hfv : f t ≠ f v := by
    intro he
    have hq := congrArg Prod.fst he
    rw [hfst,hfst] at hq
    exact htv (six_injective S hq)
  have hzero : P (f t)*P (f v)=0 := by
    unfold P
    rw [multiTensor_mul]
    apply multiTensor_zero_of _ S
    rw [hfst,hfst,localProjection_six S hS,localProjection_six S hS]
    exact hz
  have hh := hJ (f t) (hf t) (f v) (hf v) hfv
  rw [hzero,Matrix.trace_zero,Complex.zero_re] at hh
  exact lt_irrefl _ hh

def data : ProjectionCriterion.Data Question Coordinate OutputCoordinate Label where
  question := Prod.fst
  u := u
  unit := question_unit
  P := P
  hermitian := P_hermitian
  idempotent := P_idempotent
  orthogonal := P_orthogonal
  complete := P_complete
  commute := P_commute
  κ := κ
  gap := by rw [question_card,coordinate_card]; exact strict_gap
  clique := fun J hJ => by exact_mod_cast P_clique J hJ

end FiniteConstruction

end

end OAI
