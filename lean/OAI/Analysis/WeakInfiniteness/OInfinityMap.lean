import Mathlib
import OAI.Analysis.WeakInfiniteness.CStarClosedRange
import OAI.Analysis.WeakInfiniteness.OInfinityUniversal

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

variable {A : Type u} [CStarAlgebra A]

lemma oInfinity_graph_bound (s : ℕ → A)
    (hs : ∀ i j,star (s i)*s j=if i=j then 1 else 0)
    (z : OInfinity × A)
    (hz : z ∈ closedStarSpan (Set.range fun i => (oInfinityIsometry i,s i))) :
    ‖z.2‖ ≤ ‖z.1‖ := by
  change z ∈ {z : OInfinity × A | ‖z.2‖ ≤ ‖z.1‖}
  apply closure_minimal (s := (StarAlgebra.adjoin ℂ
    (Set.range fun i => (oInfinityIsometry i,s i)) : Set _)) ?_ ?_ hz
  · intro z hz
    obtain ⟨c,rfl⟩ := exists_cuntzPolynomial_of_mem_adjoin _ _ hz
    change ‖(StarAlgHom.snd ℂ OInfinity A) (cuntzPolynomial _ c)‖ ≤
      ‖(StarAlgHom.fst ℂ OInfinity A) (cuntzPolynomial _ c)‖
    rw [map_cuntzPolynomial,map_cuntzPolynomial]
    exact norm_cuntzPolynomial_le s hs c
  · exact isClosed_le (continuous_norm.comp continuous_snd) (continuous_norm.comp continuous_fst)

def oInfinityGraph (s : ℕ → A) : StarSubalgebra ℂ (OInfinity × A) :=
  closedStarSpan (Set.range fun i => (oInfinityIsometry i,s i))

instance oInfinityGraphCStar (s : ℕ → A) : CStarAlgebra (oInfinityGraph s) := closedStarSpanCStar _

def oInfinityGraphFirst (s : ℕ → A) : oInfinityGraph s →⋆ₐ[ℂ] OInfinity :=
  (StarAlgHom.fst ℂ OInfinity A).comp (oInfinityGraph s).subtype

lemma oInfinityGraphFirst_isometry (s : ℕ → A)
    (hs : ∀ i j,star (s i)*s j=if i=j then 1 else 0) :
    Isometry (oInfinityGraphFirst s) := by
  apply Isometry.of_dist_eq
  intro x y
  change dist x.val.1 y.val.1=dist x.val y.val
  rw [dist_eq_norm,dist_eq_norm,Prod.norm_def]
  have hb := oInfinity_graph_bound s hs (x-y).val (x-y).property
  change ‖x.val.2-y.val.2‖ ≤ ‖x.val.1-y.val.1‖ at hb
  exact (max_eq_left hb).symm

lemma oInfinityGraphFirst_surjective (s : ℕ → A)
    (hs : ∀ i j,star (s i)*s j=if i=j then 1 else 0) :
    Function.Surjective (oInfinityGraphFirst s) := by
  let : CompleteSpace (oInfinityGraph s) := (closedStarSpan_closed _).completeSpace_coe
  let φ := oInfinityGraphFirst s
  let S := φ.range.map oInfinitySubalgebra.subtype
  have hS : IsClosed (S : Set CuntzAmbient) := by
    have hi : Isometry (oInfinitySubalgebra.subtype.comp φ) :=
      isometry_subtype_coe.comp (oInfinityGraphFirst_isometry s hs)
    have he : (S : Set CuntzAmbient)=Set.range (oInfinitySubalgebra.subtype.comp φ) := by
      ext x
      simp only [S]
      change (∃ y,(∃ z,φ z=y) ∧ _=x) ↔ ∃ z,_=x
      constructor
      · rintro ⟨y,⟨z,rfl⟩,rfl⟩; exact ⟨z,rfl⟩
      · rintro ⟨z,rfl⟩; exact ⟨φ z,⟨z,rfl⟩,rfl⟩
    rw [he]
    exact hi.isClosedEmbedding.isClosed_range
  have hgen : Set.range cuntzGenerator ⊆ S := by
    rintro _ ⟨i,rfl⟩
    refine ⟨oInfinityIsometry i,?_,rfl⟩
    exact ⟨⟨(oInfinityIsometry i,s i),subset_closedStarSpan _ ⟨i,rfl⟩⟩,rfl⟩
  have ht : oInfinitySubalgebra ≤ S := closedStarSpan_le (Set.range cuntzGenerator) S hS hgen
  intro x
  obtain ⟨y,hy,hey⟩ := ht x.property
  obtain ⟨z,hz⟩ := hy
  refine ⟨z,?_⟩
  apply Subtype.ext
  exact (congrArg (fun y : OInfinity => y.val) hz).trans hey

def oInfinityMap (s : ℕ → A)
    (hs : ∀ i j,star (s i)*s j=if i=j then 1 else 0) : OInfinity →⋆ₐ[ℂ] A :=
  let equiv : oInfinityGraph s ≃⋆ₐ[ℂ] OInfinity :=
    StarAlgEquiv.ofBijective (oInfinityGraphFirst s)
      ⟨(oInfinityGraphFirst_isometry s hs).injective,oInfinityGraphFirst_surjective s hs⟩
  ((StarAlgHom.snd ℂ OInfinity A).comp (oInfinityGraph s).subtype).comp
    equiv.symm.toStarAlgHom

@[simp] lemma oInfinityMap_isometry (s : ℕ → A)
    (hs : ∀ i j,star (s i)*s j=if i=j then 1 else 0) (i : ℕ) :
    oInfinityMap s hs (oInfinityIsometry i)=s i := by
  let z : oInfinityGraph s :=
    ⟨(oInfinityIsometry i,s i),subset_closedStarSpan _ ⟨i,rfl⟩⟩
  let e : oInfinityGraph s ≃⋆ₐ[ℂ] OInfinity := StarAlgEquiv.ofBijective (oInfinityGraphFirst s)
    ⟨(oInfinityGraphFirst_isometry s hs).injective,oInfinityGraphFirst_surjective s hs⟩
  have he : e z=oInfinityIsometry i := rfl
  change (e.symm (oInfinityIsometry i)).val.2=s i
  have hz : e.symm (oInfinityIsometry i)=z := by
    exact (congrArg e.symm he).symm.trans (e.symm_apply_apply z)
  exact congrArg (fun w : oInfinityGraph s => w.val.2) hz

lemma oInfinity_generators_dense :
    closedStarSpan (Set.range oInfinityIsometry)=⊤ := by
  let S := closedStarSpan (Set.range oInfinityIsometry)
  let T := S.map oInfinitySubalgebra.subtype
  have ht : IsClosed (T : Set CuntzAmbient) := by
    change IsClosed (oInfinitySubalgebra.subtype '' (S : Set OInfinity))
    exact isometry_subtype_coe.isClosedEmbedding.isClosedMap _ (closedStarSpan_closed _)
  have hg : Set.range cuntzGenerator ⊆ T := by
    rintro _ ⟨i,rfl⟩
    exact ⟨oInfinityIsometry i,subset_closedStarSpan _ ⟨i,rfl⟩,rfl⟩
  have hle : oInfinitySubalgebra ≤ T := closedStarSpan_le _ T ht hg
  apply top_unique
  intro x _
  obtain ⟨y,hy,he⟩ := hle x.property
  exact (Subtype.ext he : y=x) ▸ hy

lemma oInfinity_hom_ext (φ ψ : OInfinity →⋆ₐ[ℂ] A)
    (h : ∀ i,φ (oInfinityIsometry i)=ψ (oInfinityIsometry i)) : φ=ψ := by
  let S : StarSubalgebra ℂ OInfinity :=
    { carrier := {x | φ x=ψ x}
      zero_mem' := by simp
      add_mem' := by intro x y hx hy; change φ x=ψ x at hx; change φ y=ψ y at hy; change φ (x+y)=ψ (x+y); simp only [map_add,hx,hy]
      mul_mem' := by intro x y hx hy; change φ x=ψ x at hx; change φ y=ψ y at hy; change φ (x*y)=ψ (x*y); simp only [map_mul,hx,hy]
      algebraMap_mem' := by intro r; exact (φ.commutes r).trans (ψ.commutes r).symm
      star_mem' := by intro x hx; change φ x=ψ x at hx; change φ (star x)=ψ (star x); simp only [map_star,hx] }
  have hc : IsClosed (S : Set OInfinity) := isClosed_eq (starHom_continuous φ) (starHom_continuous ψ)
  have hle : closedStarSpan (Set.range oInfinityIsometry) ≤ S := by
    apply closedStarSpan_le _ S hc
    rintro _ ⟨i,rfl⟩
    exact h i
  rw [oInfinity_generators_dense] at hle
  ext x
  exact hle (show x ∈ (⊤ : StarSubalgebra ℂ OInfinity) from trivial)

end

end WeakPureInfiniteness
end

end OAI
