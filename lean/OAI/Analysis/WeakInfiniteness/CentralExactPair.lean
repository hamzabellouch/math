import Mathlib
import OAI.Analysis.WeakInfiniteness.CentralizationEstimates
import OAI.Analysis.WeakInfiniteness.CuntzPairCorrection

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

universe u

variable (A : Type u) [CStarAlgebra A]

def LocalCentralExactCuntzPair : Prop :=
  ∀ (E : Finset A) (ε : ℝ),0<ε → ∃ r s : A,
    star r*r=1 ∧ star s*s=1 ∧ star r*s=0 ∧
    ∀ a ∈ E,‖a*r-r*a‖<ε ∧ ‖a*s-s*a‖<ε

variable {A}

lemma norm_commutator_perturbation_le (a r s : A) :
    ‖a*r-r*a‖≤‖a*s-s*a‖+2*‖a‖*‖r-s‖ := by
  have he : a*r-r*a=(a*s-s*a)+(a*(r-s)-(r-s)*a) := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖a*s-s*a‖+‖a*(r-s)-(r-s)*a‖ := norm_add_le _ _
    _ ≤ ‖a*s-s*a‖+(‖a*(r-s)‖+‖(r-s)*a‖) := by gcongr; exact norm_sub_le _ _
    _ ≤ ‖a*s-s*a‖+(‖a‖*‖r-s‖+‖r-s‖*‖a‖) := by gcongr <;> exact norm_mul_le _ _
    _ = _ := by ring

variable [PartialOrder A] [StarOrderedRing A]

lemma LocalCentralCuntzPair.exact_unital (h : LocalCentralCuntzPair A) :
    LocalCentralExactCuntzPair A := by
  classical
  intro E ε hε
  let M : ℝ := 1+∑ a ∈ E,‖a‖
  have hM : 0<M := by dsimp only [M]; positivity
  have haM (a : A) (ha : a∈E) : ‖a‖≤M := by
    have hs := Finset.single_le_sum (f := fun b : A => ‖b‖) (fun _ _ => norm_nonneg _) ha
    dsimp only [M]
    linarith
  let η : ℝ := ε/(4*M+4)
  have hη : 0<η := div_pos hε (by linarith)
  have hηε : (4*M+4)*η=ε := mul_div_cancel₀ _ (by linarith)
  obtain ⟨δ,hδ,hcorr⟩ := exists_cuntzPair_near (A := A) η hη
  let κ := min δ (ε/2)
  have hκ : 0<κ := lt_min hδ (by positivity)
  obtain ⟨s,t,hs,ht,hF⟩ := h (insert 1 E) κ hκ
  have h1 := hF 1 (Finset.mem_insert_self _ _)
  obtain ⟨r,q,hr,hq,hrq,hrs,hqt⟩ := hcorr s t hs ht
    (by simpa using lt_of_lt_of_le h1.2.2.1 (min_le_left δ (ε/2)))
    (by simpa using lt_of_lt_of_le h1.2.2.2.1 (min_le_left δ (ε/2)))
    (by simpa using lt_of_lt_of_le h1.2.2.2.2 (min_le_left δ (ε/2)))
  refine ⟨r,q,hr,hq,hrq,?_⟩
  intro a ha
  have ha' := hF a (Finset.mem_insert_of_mem ha)
  have hsr : ‖a*s-s*a‖<ε/2 := lt_of_lt_of_le ha'.1 (min_le_right δ (ε/2))
  have htq : ‖a*t-t*a‖<ε/2 := lt_of_lt_of_le ha'.2.1 (min_le_right δ (ε/2))
  have hbound (v w : A) (hw : ‖a*w-w*a‖<ε/2) (hvw : ‖v-w‖<η) : ‖a*v-v*a‖<ε := by
    have hn := norm_commutator_perturbation_le a v w
    have hb : 2*‖a‖*‖v-w‖≤2*M*η := by
      gcongr
      exact haM a ha
    have hη0 : 0≤η := hη.le
    nlinarith
  exact ⟨hbound r s hsr hrs,hbound q t htq hqt⟩

lemma ContractiveIdentityDiagonalization.centralExactCuntzPair
    (h : ContractiveIdentityDiagonalization A) : LocalCentralExactCuntzPair A :=
  h.localCentralCuntzPair.exact_unital

end

end WeakPureInfiniteness
end

end OAI
