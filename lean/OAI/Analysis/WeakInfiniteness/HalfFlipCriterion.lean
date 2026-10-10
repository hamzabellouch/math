import Mathlib
import OAI.Analysis.WeakInfiniteness.CentralCopiesTensor
import OAI.Analysis.WeakInfiniteness.InnerNorm
import OAI.Analysis.WeakInfiniteness.MapInner

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

universe u v

variable (D : Type v) [CStarAlgebra D]

def ApproximateHalfFlip : Prop :=
  ∀ (K : Finset D) (ε : ℝ),0<ε →
    ∃ u : unitary (Unitization ℂ (MinimalTensor D D)),∀ d ∈ K,
      ‖unitizationInnerFun u (minimalElementary d 1)-minimalElementary 1 d‖<ε

variable {A : Type u} {D} [CStarAlgebra A]

lemma mapUnitary_snd (φ : MinimalTensor D D →⋆ₙₐ[ℂ] MinimalTensor A D)
    (u : unitary (Unitization ℂ (MinimalTensor D D))) :
    (mapUnitary φ u).val.snd=φ u.val.snd := by
  simp [mapUnitary,Unitization.starMap_apply,Unitization.algebraMap_eq_inl]

lemma elementaryUnitaryIntertwining_of_centralCopies_halfFlip
    (hcentral : ApproximatelyCentralCopies A D) (hflip : ApproximateHalfFlip D) :
    ElementaryUnitaryIntertwining A D := by
  classical
  intro E T ε hε
  let M : ℝ := 1+∑ p ∈ T,(‖p.1‖+‖p.2‖)
  have hM : 0<M := by dsimp only [M]; positivity
  have hnorm (p : A × D) (hp : p ∈ T) : ‖p.1‖≤M ∧ ‖p.2‖≤M := by
    have hh := Finset.single_le_sum (f := fun q : A × D => ‖q.1‖+‖q.2‖)
      (fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) hp
    have h1 := norm_nonneg p.1
    have h2 := norm_nonneg p.2
    dsimp only [M]
    constructor <;> linarith
  let δ := ε/(4*(1+M))
  have hδ : 0<δ := by dsimp only [δ]; positivity
  have hδε : δ<ε := by
    dsimp only [δ]
    apply (div_lt_iff₀ (by positivity : 0<4*(1+M))).mpr
    nlinarith
  have hMδ : 2*M*δ<ε := by
    have he : 4*(1+M)*δ=ε := by dsimp only [δ]; field_simp
    nlinarith
  obtain ⟨u,hu⟩ := hflip (T.image Prod.snd) δ hδ
  obtain ⟨θ,hθ⟩ := hcentral.tensor_commutator (E ∪ T.image Prod.fst) u.val.snd δ hδ
  let Φ := tensorCopyMap θ
  let v := mapUnitary Φ u
  have hfix (a : A) (ha : a ∈ E ∪ T.image Prod.fst) :
      ‖unitizationInnerFun v (minimalLeftEmbedding A D a)-minimalLeftEmbedding A D a‖<δ := by
    rw [norm_unitizationInnerFun_sub]
    dsimp only [v]
    rw [mapUnitary_snd]
    exact hθ a ha
  have hmove (d : D) (hd : d ∈ T.image Prod.snd) :
      ‖unitizationInnerFun v (minimalLeftEmbedding A D (θ d))-minimalElementary (1:A) d‖<δ := by
    have he : unitizationInnerFun v (minimalLeftEmbedding A D (θ d))-
        minimalElementary (1:A) d =
        Φ (unitizationInnerFun u (minimalElementary d 1)-minimalElementary (1:D) d) := by
      rw [map_sub,map_unitizationInnerFun]
      dsimp only [Φ,v,tensorCopyMap]
      simp only [minimalMapAny_elementary,StarAlgHom.coe_toNonUnitalStarAlgHom,
        NonUnitalStarAlgHom.coe_id,id_eq,map_one]
      rfl
    rw [he]
    exact (NonUnitalStarAlgHom.norm_apply_le _ _).trans_lt (hu d hd)
  refine ⟨v,?_,?_⟩
  · intro a ha
    rw [dist_eq_norm]
    exact (hfix a (Finset.mem_union_left _ ha)).trans hδε
  · rintro ⟨a,d⟩ hp
    refine ⟨a*θ d,?_⟩
    rw [dist_eq_norm]
    let x := minimalLeftEmbedding A D a
    let y := minimalLeftEmbedding A D (θ d)
    let z := minimalElementary (1:A) d
    have he : unitizationInnerFun v (minimalLeftEmbedding A D (a*θ d))-minimalElementary a d=
        (unitizationInnerFun v x-x)*unitizationInnerFun v y+
          x*(unitizationInnerFun v y-z) := by
      change unitizationInnerHom v (minimalLeftEmbedding A D (a*θ d))-_=_
      rw [map_mul,map_mul]
      have hxz : x*z=minimalElementary a d := by
        change minimalElementary a 1*minimalElementary 1 d=_
        rw [← minimalElementary_mul,mul_one,one_mul]
      rw [← hxz]
      change unitizationInnerHom v x*unitizationInnerHom v y-x*z=_
      change unitizationInnerFun v x*unitizationInnerFun v y-x*z=_
      noncomm_ring
    rw [he]
    have ha := hfix a (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(a,d),hp,rfl⟩))
    have hd := hmove d (Finset.mem_image.mpr ⟨(a,d),hp,rfl⟩)
    have hn := hnorm (a,d) hp
    have hx : ‖x‖≤M := (NonUnitalStarAlgHom.norm_apply_le _ _).trans hn.1
    have hy : ‖unitizationInnerFun v y‖≤M := by
      exact (NonUnitalStarAlgHom.norm_apply_le (unitizationInnerHom v) y).trans
        ((NonUnitalStarAlgHom.norm_apply_le (minimalLeftEmbedding A D) (θ d)).trans
          ((NonUnitalStarAlgHom.norm_apply_le θ.toNonUnitalStarAlgHom d).trans hn.2))
    calc
      _ ≤ ‖(unitizationInnerFun v x-x)*unitizationInnerFun v y‖+
          ‖x*(unitizationInnerFun v y-z)‖ := norm_add_le _ _
      _ ≤ ‖unitizationInnerFun v x-x‖*‖unitizationInnerFun v y‖+
          ‖x‖*‖unitizationInnerFun v y-z‖ := by gcongr <;> exact norm_mul_le _ _
      _ ≤ δ*M+M*δ := by gcongr
      _ = 2*M*δ := by ring
      _ < ε := hMδ

end

end WeakPureInfiniteness
end

end OAI
