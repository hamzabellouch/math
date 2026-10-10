import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.StableFiniteness.Definitions
import OAI.Analysis.Kaplansky.Quotient.ClosedStarQuotient

namespace OAI

noncomputable section

namespace KaplanskyConsequences
open Topology
open scoped CStarAlgebra
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

private def ProperClosedIdeal (S : NonUnitalStarSubalgebra ℂ A) : Prop :=
  (∀ a b : A, b ∈ S → a*b ∈ S) ∧ (∀ a b : A, a ∈ S → a*b ∈ S) ∧
    IsClosed (S : Set A) ∧ (1:A) ∉ S

lemma maximal_closedStarIdeal_exists [Nontrivial A] :
    ∃ I : ClosedStarIdeal A, (1:A) ∉ I.toNonUnitalStarSubalgebra ∧
      ∀ J : ClosedStarIdeal A, I.toNonUnitalStarSubalgebra ≤ J.toNonUnitalStarSubalgebra →
        (1:A) ∉ J.toNonUnitalStarSubalgebra →
        J.toNonUnitalStarSubalgebra ≤ I.toNonUnitalStarSubalgebra := by
  let s := {S : NonUnitalStarSubalgebra ℂ A | ProperClosedIdeal S}
  have hchain : ∀ c ⊆ s, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub := by
    intro c hcs hc y hy
    have : Nonempty c := ⟨⟨y,hy⟩⟩
    have hd : Directed (· ≤ ·) (fun i : c => i.val) := by
      intro i j
      rcases hc.total i.property j.property with h | h
      · exact ⟨j,h,le_rfl⟩
      · exact ⟨i,le_rfl,h⟩
    let U : NonUnitalStarSubalgebra ℂ A := ⨆ i : c, i.val
    have hU : (U : Set A) = ⋃ i : c, (i.val : Set A) :=
      NonUnitalStarSubalgebra.coe_iSup_of_directed hd
    have hleft (a b : A) (hb : b ∈ U) : a*b ∈ U := by
      change b ∈ (U : Set A) at hb
      change a*b ∈ (U : Set A)
      rw [hU] at hb ⊢
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hb
      exact Set.mem_iUnion.mpr ⟨i,(hcs i.property).1 a b hi⟩
    have hright (a b : A) (ha : a ∈ U) : a*b ∈ U := by
      change a ∈ (U : Set A) at ha
      change a*b ∈ (U : Set A)
      rw [hU] at ha ⊢
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp ha
      exact Set.mem_iUnion.mpr ⟨i,(hcs i.property).2.1 a b hi⟩
    have hnonunits : (U : Set A) ⊆ {a : A | ¬ IsUnit a} := by
      intro a ha
      rw [hU] at ha
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp ha
      rintro ⟨v,rfl⟩
      have hone := (hcs i.property).2.1 (v:A) (↑(v⁻¹)) hi
      simp only [Units.mul_inv] at hone
      exact (hcs i.property).2.2.2 hone
    have hclosure : closure (U : Set A) ⊆ {a : A | ¬ IsUnit a} :=
      closure_minimal hnonunits Units.isOpen.isClosed_compl
    refine ⟨U.topologicalClosure,?_,?_⟩
    · refine ⟨?_,?_,U.isClosed_topologicalClosure,?_⟩
      · intro a b hb
        exact map_mem_closure (continuous_const.mul continuous_id) hb (fun b hb => hleft a b hb)
      · intro a b ha
        exact map_mem_closure (f:=fun x : A => x*b) (show Continuous (fun x : A => x*b) from continuous_id.mul continuous_const) ha (fun x hx => hright x b hx)
      · intro h1
        exact hclosure h1 isUnit_one
    · intro z hz
      exact (le_iSup (fun i : c => i.val) ⟨z,hz⟩).trans U.le_topologicalClosure
  have hbot : (⊥ : NonUnitalStarSubalgebra ℂ A) ∈ s := by
    refine ⟨?_,?_,?_,?_⟩
    · intro a b hb
      rw [NonUnitalStarAlgebra.mem_bot] at hb ⊢
      rw [hb,mul_zero]
    · intro a b ha
      rw [NonUnitalStarAlgebra.mem_bot] at ha ⊢
      rw [ha,zero_mul]
    · simp
    · simpa only [NonUnitalStarAlgebra.mem_bot] using (one_ne_zero : (1:A) ≠ 0)
  obtain ⟨M,_,hM,hmax⟩ := zorn_le_nonempty₀ s hchain ⊥ hbot
  let I : ClosedStarIdeal A := ⟨M,hM.1,hM.2.1,hM.2.2.1⟩
  refine ⟨I,hM.2.2.2,?_⟩
  intro J hij hj
  exact hmax ⟨J.mul_mem_left,J.mul_mem_right,J.closed,hj⟩ hij

namespace ClosedStarIdeal

def comap (I : ClosedStarIdeal B) (f : A →⋆ₐ[ℂ] B) : ClosedStarIdeal A where
  __ := I.toNonUnitalStarSubalgebra.comap f.toNonUnitalStarAlgHom
  mul_mem_left := by
    intro a b hb
    change f (a*b) ∈ I.toNonUnitalStarSubalgebra
    rw [map_mul]
    exact I.mul_mem_left _ _ hb
  mul_mem_right := by
    intro a b ha
    change f (a*b) ∈ I.toNonUnitalStarSubalgebra
    rw [map_mul]
    exact I.mul_mem_right _ _ ha
  closed := by
    change IsClosed (f ⁻¹' (I.toNonUnitalStarSubalgebra : Set B))
    exact I.closed.preimage (map_continuous f)

lemma quotient_nontrivial [Nontrivial A] (I : ClosedStarIdeal A)
    (hI : (1:A) ∉ I.toNonUnitalStarSubalgebra) : Nontrivial I.Quotient := by
  apply nontrivial_of_ne (1:I.Quotient) 0
  intro h
  apply hI
  apply (I.mk_eq_zero 1).mp
  simpa only [map_one] using h

lemma quotient_simple [Nontrivial A] (I : ClosedStarIdeal A)
    (hmax : ∀ J : ClosedStarIdeal A, I.toNonUnitalStarSubalgebra ≤ J.toNonUnitalStarSubalgebra →
      (1:A) ∉ J.toNonUnitalStarSubalgebra → J.toNonUnitalStarSubalgebra ≤ I.toNonUnitalStarSubalgebra) :
    CStarSimple I.Quotient := by
  intro J
  by_cases h1 : (1:I.Quotient) ∈ J.toNonUnitalStarSubalgebra
  · right
    intro a
    simpa using J.mul_mem_left a 1 h1
  · left
    let K := J.comap I.mkStarAlgHom
    have hIK : I.toNonUnitalStarSubalgebra ≤ K.toNonUnitalStarSubalgebra := by
      intro a ha
      change I.quotientMap a ∈ J.toNonUnitalStarSubalgebra
      rw [(I.mk_eq_zero a).mpr ha]
      exact J.toNonUnitalStarSubalgebra.zero_mem
    have hK : (1:A) ∉ K.toNonUnitalStarSubalgebra := by
      intro hh
      apply h1
      change I.mkStarAlgHom 1 ∈ J.toNonUnitalStarSubalgebra at hh
      simpa using hh
    have hKI := hmax K hIK hK
    intro b hb
    obtain ⟨a,rfl⟩ := I.mk_surjective b
    exact (I.mk_eq_zero a).mpr (hKI hb)
end ClosedStarIdeal

end KaplanskyConsequences

end

end OAI
