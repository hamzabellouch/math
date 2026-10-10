import Mathlib
import OAI.Probability.ParisiFinite.PhysicalGate

namespace OAI

/-! Masked Disorder. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open MeasureTheory ProbabilityTheory Filter

namespace SKQAOA.Locality

variable {n : ℕ}

def maskedDisorder (J : Disorder n) (E : Finset (Edge n)) : Disorder n :=
  fun e => if e ∈ E then J e else 0

def maskedCost (J : Disorder n) (E : Finset (Edge n)) : Operator n :=
  cost n (maskedDisorder J E)

@[simp] theorem maskedCost_univ (J : Disorder n) : maskedCost J Finset.univ=cost n J := by
  unfold maskedCost
  congr 1
  funext e
  exact ite_eq_left (Finset.mem_univ e)

@[simp] theorem maskedCost_empty (J : Disorder n) : maskedCost J ∅=0 := by
  simp [maskedCost,maskedDisorder,cost]

theorem maskedCost_sum (J : Disorder n) (E : Finset (Edge n)) :
    maskedCost J E = ((Real.sqrt (n : ℝ))⁻¹ : ℂ) •
      ∑e∈E, (J e : ℂ) • (pauliZ e.1.1*pauliZ e.1.2) := by
  simp [maskedCost,cost,maskedDisorder,ite_smul]

theorem maskedCost_hermitian (J : Disorder n) (E : Finset (Edge n)) :
    (maskedCost J E).IsHermitian := cost_hermitian _ _

theorem maskedCost_commute (J K : Disorder n) (E F : Finset (Edge n)) :
    Commute (maskedCost J E) (maskedCost K F) := by
  simp only [maskedCost,cost_eq_diagonal]
  exact Matrix.commute_diagonal _ _

def touches (S : Finset (Fin n)) (e : Edge n) : Prop := e.1.1 ∈ S ∨ e.1.2 ∈ S

instance (S : Finset (Fin n)) (e : Edge n) : Decidable (touches S e) :=
  inferInstanceAs (Decidable (_ ∨ _))

def activeEdges (E : Finset (Edge n)) (S : Finset (Fin n)) : Finset (Edge n) :=
  E.filter (touches S)

def inactiveEdges (E : Finset (Edge n)) (S : Finset (Fin n)) : Finset (Edge n) :=
  E.filter (fun e => ¬touches S e)

def neighborhood (E : Finset (Edge n)) (S : Finset (Fin n)) : Finset (Fin n) :=
  S ∪ (activeEdges E S).biUnion (fun e => {e.1.1,e.1.2})

theorem subset_neighborhood (E : Finset (Edge n)) (S : Finset (Fin n)) :
    S ⊆ neighborhood E S := Finset.subset_union_left

theorem active_endpoints {E : Finset (Edge n)} {S : Finset (Fin n)} {e : Edge n}
    (he : e∈activeEdges E S) :
    e.1.1∈neighborhood E S ∧ e.1.2∈neighborhood E S := by
  constructor <;> apply Finset.mem_union.mpr <;> right <;>
    apply Finset.mem_biUnion.mpr <;> exact ⟨e,he,by simp⟩

theorem maskedCost_active_supported (J : Disorder n) (E : Finset (Edge n))
    (S : Finset (Fin n)) : IsSupported (neighborhood E S) (maskedCost J (activeEdges E S)) := by
  rw [maskedCost_sum]
  apply IsSupported.smul
  apply supported_finsetSum
  intro e he
  exact ((supported_pauliZ (active_endpoints he).1).mul
    (supported_pauliZ (active_endpoints he).2)).smul _

theorem commute_maskedCost_inactive {S : Finset (Fin n)} {A : Operator n}
    (hA : IsSupported S A) (J : Disorder n) (E : Finset (Edge n)) :
    Commute A (maskedCost J (inactiveEdges E S)) := by
  rw [maskedCost_sum]
  apply Commute.smul_right
  apply Commute.sum_right
  intro e he
  have ht : ¬touches S e := (Finset.mem_filter.mp he).2
  exact ((hA e.1.1 (fun h => ht (Or.inl h))).2.mul_right
    (hA e.1.2 (fun h => ht (Or.inr h))).2).smul_right _

theorem maskedCost_split (J : Disorder n) (E : Finset (Edge n)) (S : Finset (Fin n)) :
    maskedCost J E = maskedCost J (inactiveEdges E S)+maskedCost J (activeEdges E S) := by
  simp only [maskedCost_sum,←smul_add]
  congr 1
  rw [add_comm]
  exact (Finset.sum_filter_add_sum_filter_not E (touches S) _).symm

theorem evolution_add_of_commute (t : ℝ) {A B : Operator n} (h : Commute A B) :
    evolution t (A+B)=evolution t A*evolution t B := by
  unfold evolution
  rw [smul_add]
  exact Matrix.exp_add_of_commute _ _ ((h.smul_left _).smul_right _)

theorem unitary_conjugate_eq_self (U A : Operator n) (hU : U∈unitary (Operator n))
    (h : Commute A U) : Uᴴ*A*U=A := by
  have hl : Uᴴ*U=1 := Unitary.star_mul_self_of_mem hU
  rw [mul_assoc,h.eq,←mul_assoc,hl,one_mul]

 

theorem cost_conjugate_local {S : Finset (Fin n)} {A : Operator n}
    (hA : IsSupported S A) (J : Disorder n) (E : Finset (Edge n)) (t : ℝ) :
    (evolution t (maskedCost J E))ᴴ*A*evolution t (maskedCost J E) =
      (evolution t (maskedCost J (activeEdges E S)))ᴴ*A*
        evolution t (maskedCost J (activeEdges E S)) := by
  have hc := maskedCost_commute J J (inactiveEdges E S) (activeEdges E S)
  have hu := evolution_unitary t _ (maskedCost_hermitian J (inactiveEdges E S))
  have ha : Commute A (evolution t (maskedCost J (inactiveEdges E S))) :=
    ((commute_maskedCost_inactive hA J E).smul_right _).exp_right
  conv_lhs => rw [maskedCost_split J E S, evolution_add_of_commute t hc]
  rw [Matrix.conjTranspose_mul]
  calc
    _ = (evolution t (maskedCost J (activeEdges E S)))ᴴ *
        ((evolution t (maskedCost J (inactiveEdges E S)))ᴴ*A*
          evolution t (maskedCost J (inactiveEdges E S))) *
        evolution t (maskedCost J (activeEdges E S)) := by noncomm_ring
    _ = _ := by rw [unitary_conjugate_eq_self _ _ hu ha]

 
theorem IsSupported.cost_conjugate {S : Finset (Fin n)} {A : Operator n}
    (hA : IsSupported S A) (J : Disorder n) (E : Finset (Edge n)) (t : ℝ) :
    IsSupported (neighborhood E S)
      ((evolution t (maskedCost J E))ᴴ*A*evolution t (maskedCost J E)) := by
  rw [cost_conjugate_local hA]
  exact (((maskedCost_active_supported J E S).evolve t).adjoint.mul
    (hA.mono (subset_neighborhood E S))).mul
      ((maskedCost_active_supported J E S).evolve t)

end SKQAOA.Locality

 

open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open MeasureTheory ProbabilityTheory Filter

namespace SKQAOA.Locality

variable {n : ℕ}

theorem activeEdges_mono {E F : Finset (Edge n)} {S T : Finset (Fin n)}
    (hEF : E⊆F) (hST : S⊆T) : activeEdges E S⊆activeEdges F T := by
  intro e he
  rcases Finset.mem_filter.mp he with ⟨he,ht⟩
  refine Finset.mem_filter.mpr ⟨hEF he,?_⟩
  exact ht.elim (fun h => Or.inl (hST h)) (fun h => Or.inr (hST h))

theorem neighborhood_mono {E F : Finset (Edge n)} {S T : Finset (Fin n)}
    (hEF : E⊆F) (hST : S⊆T) : neighborhood E S⊆neighborhood F T := by
  apply Finset.union_subset_union hST
  intro i hi
  rcases Finset.mem_biUnion.mp hi with ⟨e,he,hi⟩
  exact Finset.mem_biUnion.mpr ⟨e,activeEdges_mono hEF hST he,hi⟩

 

def relevantEdges (E : Finset (Edge n)) :
    List PointedTree.Gate → Finset (Fin n) → Finset (Edge n)
  | [], _ => ∅
  | .mixer _ :: w, S => relevantEdges E w S
  | .cost _ :: w, S => activeEdges E S ∪ relevantEdges E w (neighborhood E S)

theorem relevantEdges_subset (E : Finset (Edge n)) (w : List PointedTree.Gate)
    (S : Finset (Fin n)) : relevantEdges E w S⊆E := by
  induction w generalizing S with
  | nil => exact Finset.empty_subset E
  | cons g w ih =>
    cases g with
    | mixer t => exact ih S
    | cost t => exact Finset.union_subset (Finset.filter_subset _ _) (ih _)

theorem relevantEdges_mono {E F : Finset (Edge n)} {S T : Finset (Fin n)}
    (hEF : E⊆F) (hST : S⊆T) (w : List PointedTree.Gate) :
    relevantEdges E w S⊆relevantEdges F w T := by
  induction w generalizing S T with
  | nil => exact Finset.Subset.refl _
  | cons g w ih =>
    cases g with
    | mixer t => exact ih hST
    | cost t =>
      exact Finset.union_subset_union (activeEdges_mono hEF hST)
        (ih (neighborhood_mono hEF hST))

 
def wordConjugate (J : Disorder n) (E : Finset (Edge n))
    (w : List PointedTree.Gate) (A : Operator n) : Operator n :=
  (physicalWord n (maskedDisorder J E) w)ᴴ*A*physicalWord n (maskedDisorder J E) w

@[simp] theorem wordConjugate_nil (J : Disorder n) (E : Finset (Edge n))
    (A : Operator n) : wordConjugate J E [] A=A := by simp [wordConjugate]

theorem wordConjugate_cons (J : Disorder n) (E : Finset (Edge n))
    (g : PointedTree.Gate) (w : List PointedTree.Gate) (A : Operator n) :
    wordConjugate J E (g::w) A = wordConjugate J E w
      ((physicalGate n (maskedDisorder J E) g)ᴴ*A*physicalGate n (maskedDisorder J E) g) := by
  simp only [wordConjugate,physicalWord_cons,Matrix.conjTranspose_mul]
  noncomm_ring

@[simp] theorem wordConjugate_cost (J : Disorder n) (E : Finset (Edge n))
    (t : ℝ) (w : List PointedTree.Gate) (A : Operator n) :
    wordConjugate J E (.cost t::w) A = wordConjugate J E w
      ((evolution t (maskedCost J E))ᴴ*A*evolution t (maskedCost J E)) :=
  wordConjugate_cons J E _ w A

@[simp] theorem wordConjugate_mixer (J : Disorder n) (E : Finset (Edge n))
    (t : ℝ) (w : List PointedTree.Gate) (A : Operator n) :
    wordConjugate J E (.mixer t::w) A = wordConjugate J E w
      ((evolution t (mixer n))ᴴ*A*evolution t (mixer n)) :=
  wordConjugate_cons J E _ w A

 
theorem wordConjugate_eq_of_relevant_subset (J : Disorder n)
    {E F : Finset (Edge n)} (hFE : F⊆E) (w : List PointedTree.Gate)
    {S : Finset (Fin n)} {A : Operator n} (hA : IsSupported S A)
    (hrel : relevantEdges E w S⊆F) :
    wordConjugate J E w A=wordConjugate J F w A := by
  induction w generalizing S A with
  | nil => simp
  | cons g w ih =>
    cases g with
    | mixer t =>
      simp only [wordConjugate_mixer]
      exact ih (hA.mixer_conjugate t) hrel
    | cost t =>
      have ha : activeEdges E S⊆F := Finset.union_subset_iff.mp hrel |>.1
      have hr : relevantEdges E w (neighborhood E S)⊆F :=
        Finset.union_subset_iff.mp hrel |>.2
      have heq : activeEdges E S=activeEdges F S := by
        apply Finset.Subset.antisymm
        · intro e he
          exact Finset.mem_filter.mpr ⟨ha he,(Finset.mem_filter.mp he).2⟩
        · exact activeEdges_mono hFE (Finset.Subset.refl _)
      have heqA : (evolution t (maskedCost J E))ᴴ*A*evolution t (maskedCost J E) =
          (evolution t (maskedCost J F))ᴴ*A*evolution t (maskedCost J F) := by
        rw [cost_conjugate_local hA J E,cost_conjugate_local hA J F,heq]
      simp only [wordConjugate_cost]
      rw [←heqA]
      exact ih (hA.cost_conjugate J E t) hr

 

theorem wordConjugate_insert_irrelevant (J : Disorder n)
    {H M : Finset (Edge n)} {e : Edge n} (he : e∈H) (hM : M⊆H)
    (w : List PointedTree.Gate) {S : Finset (Fin n)} {A : Operator n}
    (hA : IsSupported S A) (hirr : e∉relevantEdges H w S) :
    wordConjugate J (insert e M) w A=wordConjugate J M w A := by
  apply wordConjugate_eq_of_relevant_subset J (Finset.subset_insert _ _) w hA
  intro f hf
  have hf' := relevantEdges_subset (insert e M) w S hf
  rcases Finset.mem_insert.mp hf' with rfl|hf'
  · exact False.elim (hirr (relevantEdges_mono (Finset.insert_subset he hM)
      (Finset.Subset.refl S) w hf))
  · exact hf'

end SKQAOA.Locality

 

open scoped BigOperators

namespace FiniteEdgeExpansion

variable {E R A : Type*} [DecidableEq E] [CommRing R]

 
def mixedDifference (S : Finset E) (F : Finset E → R) : R :=
  ∑ T ∈ S.powerset, (-1 : R)^T.card * F (S \ T)

@[simp] theorem mixedDifference_empty (F : Finset E → R) :
    mixedDifference ∅ F = F ∅ := by simp [mixedDifference]

 

theorem mixedDifference_insert (S : Finset E) (e : E) (he : e ∉ S)
    (F : Finset E → R) :
    mixedDifference (insert e S) F =
      mixedDifference S (fun T => F (insert e T)) - mixedDifference S F := by
  unfold mixedDifference
  rw [Finset.sum_powerset_insert he]
  have heT (T : Finset E) (hT : T ∈ S.powerset) : e ∉ T := by
    intro h
    exact he (Finset.mem_powerset.mp hT h)
  have hfirst (T : Finset E) (hT : T ∈ S.powerset) :
      insert e S \ T = insert e (S \ T) := by
    ext x
    by_cases hx : x=e <;> simp [hx, heT T hT]
  have hsecond (T : Finset E) (hT : T ∈ S.powerset) :
      insert e S \ insert e T = S \ T := by
    ext x
    by_cases hx : x=e <;> simp [hx,he]
  have h₁ : (∑ T ∈ S.powerset, (-1:R)^T.card * F (insert e S \ T)) =
      ∑ T ∈ S.powerset, (-1:R)^T.card * F (insert e (S \ T)) := by
    apply Finset.sum_congr rfl
    intro T hT
    rw [hfirst T hT]
  have h₂ : (∑ T ∈ S.powerset, (-1:R)^(insert e T).card * F (insert e S \ insert e T)) =
      -(∑ T ∈ S.powerset, (-1:R)^T.card * F (S \ T)) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro T hT
    rw [Finset.card_insert_of_notMem (heT T hT), hsecond T hT, pow_succ]
    ring
  rw [h₁,h₂]
  ring

theorem mixedDifference_eq_zero_of_irrelevant {S : Finset E} {e : E}
    (he : e ∈ S) (F : Finset E → R)
    (hF : ∀ T ⊆ S.erase e, F (insert e T) = F T) :
    mixedDifference S F = 0 := by
  rw [←Finset.insert_erase he, mixedDifference_insert _ _ (Finset.notMem_erase e S)]
  have h : mixedDifference (S.erase e) (fun T => F (insert e T)) =
      mixedDifference (S.erase e) F := by
    apply Finset.sum_congr rfl
    intro T hT
    dsimp only
    rw [hF _ (Finset.sdiff_subset)]
  rw [h,sub_self]

 
theorem reconstruction (H : Finset E) (F : Finset E → R) :
    (∑ S ∈ H.powerset, mixedDifference S F)=F H := by
  induction H using Finset.induction_on generalizing F with
  | empty => simp
  | @insert e H he ih =>
    rw [Finset.sum_powerset_insert he]
    have hs : (∑S ∈ H.powerset, mixedDifference (insert e S) F) =
        (∑S ∈ H.powerset, mixedDifference S (fun T => F (insert e T))) -
          ∑S ∈ H.powerset, mixedDifference S F := by
      rw [←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro S hS
      exact mixedDifference_insert S e
        (fun h => he (Finset.mem_powerset.mp hS h)) F
    rw [hs,ih,ih]
    ring

variable [Fintype A]

def partition (q : A → R) (I : A → E → R) (S : Finset E) : R :=
  ∑ a, q a * ∏ e ∈ S, I a e

def coefficient (q : A → R) (I : A → E → R) (S : Finset E) : R :=
  ∑ a, q a * ∏ e ∈ S, (I a e - 1)

 

omit [DecidableEq E] in
theorem partition_expansion (q : A → R) (I : A → E → R) (S : Finset E) :
    partition q I S = ∑ T ∈ S.powerset, coefficient q I T := by
  unfold partition coefficient
  have hp (a : A) : (∏ e ∈ S, I a e) =
      ∑ T ∈ S.powerset, ∏ e ∈ T, (I a e-1) := by
    simpa using (Finset.prod_one_add (f := fun e => I a e-1) S)
  simp_rw [hp,Finset.mul_sum]
  exact Finset.sum_comm

 

theorem coefficient_eq_mixedDifference (q : A → R) (I : A → E → R) (S : Finset E) :
    coefficient q I S = mixedDifference S (partition q I) := by
  unfold coefficient mixedDifference partition
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hp := Finset.prod_sub (fun e => I a e) (fun _ : E => (1:R)) S
  simp only [Finset.prod_const_one,mul_one] at hp
  rw [hp,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  ring

theorem coefficient_eq_zero_of_irrelevant (q : A → R) (I : A → E → R)
    {S : Finset E} {e : E} (he : e ∈ S)
    (hF : ∀ T ⊆ S.erase e, partition q I (insert e T) = partition q I T) :
    coefficient q I S = 0 := by
  rw [coefficient_eq_mixedDifference]
  exact mixedDifference_eq_zero_of_irrelevant he _ hF

end FiniteEdgeExpansion

 

open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open MeasureTheory ProbabilityTheory Filter

namespace SKQAOA.Locality

variable {n : ℕ}

 
def annealedObservable (μ : Measure (Disorder n)) (a : Disorder n → ℂ)
    (B : Finset (Edge n)) (w : List PointedTree.Gate) (A : Disorder n → Operator n)
    (E : Finset (Edge n)) : ℂ :=
  ∫J, a J * quad ((physicalWord n (maskedDisorder J (E∪B)) w).mulVec (plus n)) (A J) ∂μ

 

theorem annealed_mixedDifference_eq_zero (μ : Measure (Disorder n)) (a : Disorder n → ℂ)
    (B : Finset (Edge n)) (w : List PointedTree.Gate) (A : Disorder n → Operator n)
    (S : Finset (Fin n)) (hA : ∀J, IsSupported S (A J))
    {H : Finset (Edge n)} {e : Edge n} (he : e∈H)
    (hirr : e∉relevantEdges (H∪B) w S) :
    FiniteEdgeExpansion.mixedDifference H (annealedObservable μ a B w A)=0 := by
  apply FiniteEdgeExpansion.mixedDifference_eq_zero_of_irrelevant he
  intro M hM
  apply integral_congr_ae
  filter_upwards [] with J
  congr 1
  rw [quad_mulVec,quad_mulVec]
  change quad (plus n) (wordConjugate J (insert e M∪B) w (A J)) =
    quad (plus n) (wordConjugate J (M∪B) w (A J))
  rw [Finset.insert_union]
  congr 1
  exact wordConjugate_insert_irrelevant J (Finset.mem_union_left B he)
    (Finset.union_subset_union (hM.trans (Finset.erase_subset e H)) (Finset.Subset.refl B))
    w (hA J) hirr

 
def averagedMarkedWord (r : Edge n) (w : List PointedTree.Gate)
    (E : Finset (Edge n)) : ℂ :=
  annealedObservable (disorderLaw n) (fun J => (J r:ℂ)) {r} w
    (fun _ => pauliZ r.1.1*pauliZ r.1.2) E

 

theorem marked_cluster_eq_zero (r : Edge n) (w : List PointedTree.Gate)
    {H : Finset (Edge n)} {e : Edge n} (he : e∈H)
    (hirr : e∉relevantEdges (H∪{r}) w {r.1.1,r.1.2}) :
    FiniteEdgeExpansion.mixedDifference H (averagedMarkedWord r w)=0 := by
  apply annealed_mixedDifference_eq_zero (disorderLaw n) (fun J => (J r:ℂ))
    {r} w (fun _ => pauliZ r.1.1*pauliZ r.1.2) {r.1.1,r.1.2} _ he hirr
  intro J
  exact (supported_pauliZ (by simp)).mul (supported_pauliZ (by simp))

end SKQAOA.Locality

 

open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter

namespace SKQAOA

 
def qaoaWord : (p : ℕ) → (Fin p → ℝ) → (Fin p → ℝ) → List PointedTree.Gate
  | 0, _, _ => []
  | p+1, γ, β => .mixer (β (Fin.last p)) :: .cost (γ (Fin.last p)) ::
      qaoaWord p (fun i => γ i.castSucc) (fun i => β i.castSucc)

@[simp] theorem physicalWord_qaoaWord (n p : ℕ) (J : Disorder n) (γ β : Fin p → ℝ) :
    physicalWord n J (qaoaWord p γ β)=circuit J p γ β := by
  induction p with
  | zero => rfl
  | succ p ih => simp only [qaoaWord,physicalWord,physicalGate,ih,circuit,mul_assoc]

namespace SiteHistories

instance bitsInhabited : (p : ℕ) → Inhabited (Bits p)
  | 0 => inferInstanceAs (Inhabited Unit)
  | p+1 => @instInhabitedProd Bool (Bits p) inferInstance (bitsInhabited p)

def maskPhase (n p : ℕ) (γ : Fin p → ℝ) (a b : History n p)
    (E : Finset (Edge n)) (e : Edge n) : ℂ :=
  if e∈E then pairedPhase n p γ a b e else 0

lemma masked_phase_sum (n p : ℕ) (J : Disorder n) (γ : Fin p → ℝ)
    (a b : History n p) (E : Finset (Edge n)) :
    (∑e, pairedPhase n p γ a b e*(Locality.maskedDisorder J E e:ℂ))=
      ∑e, maskPhase n p γ a b E e*(J e:ℂ) := by
  apply Finset.sum_congr rfl
  intro e he
  simp only [Locality.maskedDisorder,maskPhase]
  split_ifs <;> simp

lemma coord_masked_history (n p : ℕ) (J : Disorder n) (γ β : Fin p → ℝ)
    (σ : Configuration n) (r : Edge n) (E : Finset (Edge n)) :
    (J r:ℂ)*(star (qaoaState n p (Locality.maskedDisorder J E) γ β σ)*
      qaoaState n p (Locality.maskedDisorder J E) γ β σ)=
      ∑a:History n p, ∑b:History n p, pairedMix n p β σ a b *
        ((J r:ℂ)*Complex.exp (∑e,maskPhase n p γ a b E e*(J e:ℂ))) := by
  rw [qaoaState_pair_history]
  simp only [Finset.mul_sum,masked_phase_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

lemma integral_coord_masked (n p : ℕ) (γ β : Fin p → ℝ)
    (σ : Configuration n) (r : Edge n) (E : Finset (Edge n)) :
    (∫J:Disorder n, (J r:ℂ)*
      (star (qaoaState n p (Locality.maskedDisorder J E) γ β σ)*
        qaoaState n p (Locality.maskedDisorder J E) γ β σ) ∂disorderLaw n)=
      ∑a:History n p, ∑b:History n p, pairedMix n p β σ a b *
        maskPhase n p γ a b E r * Complex.exp (∑e,(maskPhase n p γ a b E e)^2/2) := by
  simp_rw [coord_masked_history]
  have hx (a b : History n p) : Integrable (fun J : Disorder n => pairedMix n p β σ a b *
      ((J r:ℂ)*Complex.exp (∑e, maskPhase n p γ a b E e*(J e:ℂ)))) (disorderLaw n) :=
    (GaussianFourier.integrable_coord_exp_sum (maskPhase n p γ a b E) r).const_mul _
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hx a b))]
  apply Finset.sum_congr rfl
  intro a ha
  rw [integral_finsetSum _ (fun b _ => hx a b)]
  apply Finset.sum_congr rfl
  intro b hb
  rw [integral_const_mul]
  change _ * (∫J:Disorder n, _ ∂GaussianFourier.law (Edge n))=_
  rw [GaussianFourier.integral_coord_exp_sum,mul_assoc]

lemma integrable_coord_masked (n p : ℕ) (γ β : Fin p → ℝ)
    (σ : Configuration n) (r : Edge n) (E : Finset (Edge n)) :
    Integrable (fun J:Disorder n => (J r:ℂ)*
      (star (qaoaState n p (Locality.maskedDisorder J E) γ β σ)*
        qaoaState n p (Locality.maskedDisorder J E) γ β σ)) (disorderLaw n) := by
  simp_rw [coord_masked_history]
  exact integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ =>
    (GaussianFourier.integrable_coord_exp_sum (maskPhase n p γ a b E) r).const_mul _))

lemma quad_ZZ (n : ℕ) (ψ : State n) (r : Edge n) :
    quad ψ (pauliZ r.1.1*pauliZ r.1.2)=
      ∑σ:Configuration n,(spin σ r.1.1:ℂ)*(spin σ r.1.2:ℂ)*(star (ψ σ)*ψ σ) := by
  simp only [pauliZ,Matrix.diagonal_mul_diagonal,quad,Matrix.mulVec_diagonal,
    dotProduct,Pi.star_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  ring

 
theorem averagedMarkedWord_history (n p : ℕ) (γ β : Fin p → ℝ)
    (r : Edge n) (E : Finset (Edge n)) :
    Locality.averagedMarkedWord r (qaoaWord p γ β) E=
      ∑σ:Configuration n, ∑a:History n p, ∑b:History n p,
        (spin σ r.1.1:ℂ)*(spin σ r.1.2:ℂ)*pairedMix n p β σ a b *
          pairedPhase n p γ a b r *
            Complex.exp (∑e, (maskPhase n p γ a b (E∪{r}) e)^2/2) := by
  unfold Locality.averagedMarkedWord Locality.annealedObservable
  simp only [physicalWord_qaoaWord]
  change (∫J:Disorder n, (J r:ℂ)*quad
    (qaoaState n p (Locality.maskedDisorder J (E∪{r})) γ β)
    (pauliZ r.1.1*pauliZ r.1.2) ∂disorderLaw n)=_
  simp only [quad_ZZ,Finset.mul_sum]
  have hi (σ : Configuration n) :=
    (integrable_coord_masked n p γ β σ r (E∪{r})).const_mul
      ((spin σ r.1.1:ℂ)*(spin σ r.1.2:ℂ))
  have rearr (J : Disorder n) (σ : Configuration n) :
      (J r:ℂ)*((spin σ r.1.1:ℂ)*(spin σ r.1.2:ℂ)*
        (star (qaoaState n p (Locality.maskedDisorder J (E∪{r})) γ β σ)*
          qaoaState n p (Locality.maskedDisorder J (E∪{r})) γ β σ))=
      ((spin σ r.1.1:ℂ)*(spin σ r.1.2:ℂ))*((J r:ℂ)*
        (star (qaoaState n p (Locality.maskedDisorder J (E∪{r})) γ β σ)*
          qaoaState n p (Locality.maskedDisorder J (E∪{r})) γ β σ)) := by ring
  simp_rw [rearr]
  rw [integral_finsetSum _ (fun σ _ => hi σ)]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [integral_const_mul,integral_coord_masked]
  simp only [Finset.mul_sum,maskPhase,Finset.mem_union,Finset.mem_singleton,
    or_true,ite_true]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

end SiteHistories
end SKQAOA

 

open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter

namespace SKQAOA.SiteHistories

variable {n : ℕ}

 
def rootFactor (p : ℕ) (γ : Fin p → ℝ) (r : Edge n) (a : Fin n → Site p) : ℂ :=
  (bitSpin (a r.1.1).1:ℂ)*(bitSpin (a r.1.2).1:ℂ)*Complex.I*
    ((Real.sqrt (n:ℝ))⁻¹:ℂ)*(delta p γ (a r.1.1) (a r.1.2):ℂ)*
      (edgeKernel n p γ (a r.1.1) (a r.1.2):ℂ)

 
def factor (p : ℕ) (γ : Fin p → ℝ) (r : Edge n)
    (a : Fin n → Site p) (e : Edge n) : ℂ :=
  if e=r then 1 else (edgeKernel n p γ (a e.1.1) (a e.1.2):ℂ)

def partition (p : ℕ) (γ β : Fin p → ℝ) (r : Edge n) (E : Finset (Edge n)) : ℂ :=
  FiniteHistory.expectation (weight p β) (fun a => rootFactor p γ r a * ∏e∈E,factor p γ r a e)

def cluster (p : ℕ) (γ β : Fin p → ℝ) (r : Edge n) (H : Finset (Edge n)) : ℂ :=
  FiniteHistory.expectation (weight p β)
    (fun a => rootFactor p γ r a * ∏e∈H,(factor p γ r a e-1))

lemma exp_maskPhase_sq (p : ℕ) (γ : Fin p → ℝ)
    (h : Configuration n × History n p × History n p) (E : Finset (Edge n)) :
    Complex.exp (∑e,(maskPhase n p γ h.2.1 h.2.2 E e)^2/2)=
      ∏e∈E,(edgeKernel n p γ (trajectoriesEquiv n p h e.1.1)
        (trajectoriesEquiv n p h e.1.2):ℂ) := by
  rw [Complex.exp_sum]
  have he (e : Edge n) : Complex.exp ((maskPhase n p γ h.2.1 h.2.2 E e)^2/2)=
      if e∈E then (edgeKernel n p γ (trajectoriesEquiv n p h e.1.1)
        (trajectoriesEquiv n p h e.1.2):ℂ) else 1 := by
    by_cases he : e∈E
    · simp only [maskPhase,he,ite_true,exp_pairedPhase_sq]
    · simp [maskPhase,he]
  simp_rw [he]
  rw [Finset.prod_ite_mem,Finset.univ_inter]

lemma prod_union_root {A : Type*} [DecidableEq A] (E : Finset A) (r : A) (f : A → ℂ) :
    (∏e∈E∪{r},f e)=f r*∏e∈E,if e=r then 1 else f e := by
  induction E using Finset.induction_on with
  | empty => simp
  | @insert e E he ih =>
    by_cases her : e=r
    · subst e
      rw [Finset.insert_union,Finset.insert_eq_of_mem (by simp),
        Finset.prod_insert he,ite_eq_left rfl,one_mul]
      exact ih
    · rw [Finset.insert_union,Finset.prod_insert (by simpa [her] using he),
        Finset.prod_insert he,ite_eq_right her,ih]
      ring

 

theorem partition_eq_marked (p : ℕ) (γ β : Fin p → ℝ) (r : Edge n)
    (E : Finset (Edge n)) :
    partition p γ β r E=Locality.averagedMarkedWord r (qaoaWord p γ β) E := by
  rw [averagedMarkedWord_history]
  have hs := (trajectoriesEquiv n p).sum_comp (fun a =>
    (∏i,weight p β (a i))*(rootFactor p γ r a*∏e∈E,factor p γ r a e))
  rw [Fintype.sum_prod_type] at hs
  simp_rw [Fintype.sum_prod_type] at hs
  unfold partition FiniteHistory.expectation
  rw [←hs]
  apply Finset.sum_congr rfl
  intro σ hσ
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [pairedMix_factor,pairedPhase_local n p γ (σ,a,b) r,
    exp_maskPhase_sq p γ (σ,a,b),prod_union_root]
  simp only [rootFactor,factor,trajectoriesEquiv_apply]
  change (∏i, weight p β (σ i,atVertex n p a i,atVertex n p b i))*
    ((spin σ r.1.1:ℂ)*(spin σ r.1.2:ℂ)*Complex.I*((Real.sqrt (n:ℝ))⁻¹:ℂ)*
      (delta p γ (σ r.1.1,atVertex n p a r.1.1,atVertex n p b r.1.1)
        (σ r.1.2,atVertex n p a r.1.2,atVertex n p b r.1.2):ℂ)*
      (edgeKernel n p γ (σ r.1.1,atVertex n p a r.1.1,atVertex n p b r.1.1)
        (σ r.1.2,atVertex n p a r.1.2,atVertex n p b r.1.2):ℂ)*
          ∏e∈E,factor p γ r (trajectoriesEquiv n p (σ,a,b)) e)=_
  ac_rfl

theorem cluster_eq_mixedDifference (p : ℕ) (γ β : Fin p → ℝ) (r : Edge n)
    (H : Finset (Edge n)) :
    cluster p γ β r H=FiniteEdgeExpansion.mixedDifference H
      (Locality.averagedMarkedWord r (qaoaWord p γ β)) := by
  have hp (E : Finset (Edge n)) :
      FiniteEdgeExpansion.partition (fun a : Fin n → Site p =>
        (∏i,weight p β (a i))*rootFactor p γ r a) (factor p γ r) E=
          partition p γ β r E := by
    simp only [FiniteEdgeExpansion.partition,partition,FiniteHistory.expectation,mul_assoc]
  have hc : cluster p γ β r H=FiniteEdgeExpansion.coefficient
      (fun a : Fin n → Site p => (∏i,weight p β (a i))*rootFactor p γ r a)
        (factor p γ r) H := by
    simp only [FiniteEdgeExpansion.coefficient,cluster,FiniteHistory.expectation,mul_assoc]
  rw [hc,FiniteEdgeExpansion.coefficient_eq_mixedDifference]
  congr 1
  funext E
  rw [hp,partition_eq_marked]

 
theorem cluster_eq_zero (p : ℕ) (γ β : Fin p → ℝ) (r : Edge n)
    {H : Finset (Edge n)} {e : Edge n} (he : e∈H)
    (hirr : e∉Locality.relevantEdges (H∪{r}) (qaoaWord p γ β) {r.1.1,r.1.2}) :
    cluster p γ β r H=0 := by
  rw [cluster_eq_mixedDifference]
  exact Locality.marked_cluster_eq_zero r _ he hirr

 
theorem marked_eq_sum_clusters (p : ℕ) (γ β : Fin p → ℝ) (r : Edge n)
    (E : Finset (Edge n)) :
    Locality.averagedMarkedWord r (qaoaWord p γ β) E=
      ∑H∈E.powerset,cluster p γ β r H := by
  simp_rw [cluster_eq_mixedDifference]
  exact (FiniteEdgeExpansion.reconstruction E _).symm

end SKQAOA.SiteHistories

end

end OAI
