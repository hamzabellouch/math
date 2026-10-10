import Mathlib

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

open Filter Topology

universe u v

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

def starHomLimitFun (f : ℕ → A →⋆ₙₐ[ℂ] B) (hf : ∀ a,CauchySeq (fun n => f n a)) (a : A) : B :=
  Classical.choose (cauchySeq_tendsto_of_complete (hf a))

lemma starHomLimitFun_tendsto (f : ℕ → A →⋆ₙₐ[ℂ] B) (hf : ∀ a,CauchySeq (fun n => f n a))
    (a : A) : Tendsto (fun n => f n a) atTop (𝓝 (starHomLimitFun f hf a)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (hf a))

def starHomLimit (f : ℕ → A →⋆ₙₐ[ℂ] B) (hf : ∀ a,CauchySeq (fun n => f n a)) : A →⋆ₙₐ[ℂ] B where
  toFun := starHomLimitFun f hf
  map_zero' := by
    apply tendsto_nhds_unique (starHomLimitFun_tendsto f hf 0)
    simpa only [map_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:B)) atTop (𝓝 0))
  map_add' a b := by
    apply tendsto_nhds_unique (starHomLimitFun_tendsto f hf (a+b))
    simpa only [map_add] using (starHomLimitFun_tendsto f hf a).add (starHomLimitFun_tendsto f hf b)
  map_mul' a b := by
    apply tendsto_nhds_unique (starHomLimitFun_tendsto f hf (a*b))
    simpa only [map_mul] using (starHomLimitFun_tendsto f hf a).mul (starHomLimitFun_tendsto f hf b)
  map_smul' t a := by
    apply tendsto_nhds_unique (starHomLimitFun_tendsto f hf (t • a))
    simpa only [map_smul,MonoidHom.id_apply] using (starHomLimitFun_tendsto f hf a).const_smul t
  map_star' a := by
    apply tendsto_nhds_unique (starHomLimitFun_tendsto f hf (star a))
    simpa only [map_star] using (starHomLimitFun_tendsto f hf a).star

lemma starHomLimit_isometry (f : ℕ → A →⋆ₙₐ[ℂ] B)
    (hf : ∀ a,CauchySeq (fun n => f n a)) (hi : ∀ n,Isometry (f n)) :
    Isometry (starHomLimit f hf) := by
  apply Isometry.of_dist_eq
  intro a b
  have ht := (starHomLimitFun_tendsto f hf a).dist (starHomLimitFun_tendsto f hf b)
  change dist (starHomLimitFun f hf a) (starHomLimitFun f hf b)=dist a b
  apply tendsto_nhds_unique ht
  simpa only [(hi _).dist_eq] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => dist a b) atTop (𝓝 (dist a b)))

lemma cauchySeq_isometries_of_dense {ι : Type*} (d : ι → A) (hd : DenseRange d)
    (f : ℕ → A →⋆ₙₐ[ℂ] B) (hi : ∀ n,Isometry (f n))
    (hc : ∀ i,CauchySeq (fun n => f n (d i))) (a : A) : CauchySeq (fun n => f n a) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨i,hiε⟩ := Metric.denseRange_iff.mp hd a (ε/3) (by positivity)
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp (hc i) (ε/3) (by positivity)
  refine ⟨N,fun m hm n hn => ?_⟩
  have he := dist_triangle4 (f m a) (f m (d i)) (f n (d i)) (f n a)
  rw [(hi m).dist_eq,(hi n).dist_eq,dist_comm (d i) a] at he
  have hmid := hN m hm n hn
  linarith

def starEquivOfConvergentIsometries (f : ℕ → A →⋆ₙₐ[ℂ] B)
    (hf : ∀ a,CauchySeq (fun n => f n a)) (hi : ∀ n,Isometry (f n))
    (hd : DenseRange (starHomLimit f hf)) : A ≃⋆ₐ[ℂ] B := by
  let g := starHomLimit f hf
  have hg : Isometry g := starHomLimit_isometry f hf hi
  have hs : Function.Surjective g := by
    intro b
    have h := hd b
    rwa [hg.isClosedEmbedding.isClosed_range.closure_eq] at h
  exact StarAlgEquiv.ofBijective g ⟨hg.injective,hs⟩

end

end WeakPureInfiniteness
end

end OAI
