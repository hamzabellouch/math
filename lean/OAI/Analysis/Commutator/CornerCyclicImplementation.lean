import Mathlib
import OAI.Analysis.Commutator.ConcreteCornerVonNeumann
import OAI.Analysis.Commutator.CornerCyclic
import OAI.Analysis.Commutator.EmbeddedCyclicImplementation
import OAI.Analysis.Commutator.MatrixCornerExtension

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.ReducingRepresentation

open MatrixCornerHilbert

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma corner_dense (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {p : A} (hp : IsStarProjection p)
    (Ω : H) (hΩ : DenseRange (fun a : A => σ a Ω)) (hpΩ : σ p Ω=Ω) :
    DenseRange (fun a : Corner hp => corner σ hp a
      (⟨Ω,(mem_fixedSpace _ _).mpr hpΩ⟩ : fixedSpace (σ p))) := by
  have hs : Function.Surjective (cornerProjection σ hp) := fun x => ⟨(x:H),cornerProjection_fixed σ hp x⟩
  have hd := hs.denseRange.comp hΩ (cornerProjection σ hp).continuous
  intro x
  apply (closure_mono ?_) (hd x)
  rintro _ ⟨a,rfl⟩
  let b : Corner hp := ⟨p*a*p,by rw [←mul_assoc,←mul_assoc,hp.isIdempotentElem.eq],
    by rw [mul_assoc _ p p,hp.isIdempotentElem.eq]⟩
  refine ⟨b,?_⟩
  apply Subtype.ext
  change σ (p*a*p) Ω=σ p (σ a Ω)
  simp only [map_mul,mul_apply_eq_comp,hpΩ]

end Kadison.ReducingRepresentation

namespace Kadison.MatrixCornerImplementation

open MatrixCornerHilbert ReducingRepresentation ConcreteCorner MatrixCornerExtension

variable {H K ι : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [Fintype ι] [DecidableEq ι]

variable (M : VonNeumannAlgebra H)
  (σ : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (j : K →ₗᵢ[ℂ] H)
  (hj : ∀ a x, j (σ a x)=inclusion M a (j x))

variable {p : Algebra M} (hp : IsStarProjection p)

def cornerEmbedding : fixedSpace (σ p) →ₗᵢ[ℂ] Space hp where
  toFun x := ⟨j (x:K),by
    rw [mem_fixedSpace,←hj,MatrixCornerHilbert.fixed_apply]⟩
  map_add' x y := Subtype.ext (map_add j (x:K) (y:K))
  map_smul' z x := Subtype.ext (map_smul j z (x:K))
  norm_map' x := j.norm_map (x:K)

lemma cornerEmbedding_intertwines (a : Corner hp) (x : fixedSpace (σ p)) :
    cornerEmbedding M σ j hj hp (corner σ hp a x)=
      representation hp a (cornerEmbedding M σ j hj hp x) := by
  apply Subtype.ext
  exact hj (a:Algebra M) (x:K)

variable (G : K →L[ℂ] H) (hGp : ∀ x, G (σ p x)=inclusion M p (G x))

local instance : NormedAddCommGroup (fixedSpace (σ p) →L[ℂ] Space hp) := ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℂ (fixedSpace (σ p) →L[ℂ] Space hp) := ContinuousLinearMap.toNormedSpace

omit [Fintype ι] [DecidableEq ι] in
lemma corner_derivation_bound {ε : ℝ} (hε : 0≤ε)
    (hδ : ∀ a : Corner hp, ‖G.comp (σ (a:Algebra M))-(inclusion M (a:Algebra M)).comp G‖≤ε*‖a‖)
    (a : Corner hp) :
    ‖(cornerMap σ (inclusion M) G hGp).comp (corner σ hp a)-
      (representation hp a).comp (cornerMap σ (inclusion M) G hGp)‖≤ε*‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hε (norm_nonneg _))
  intro x
  change ‖G (σ (a:Algebra M) (x:K))-inclusion M (a:Algebra M) (G (x:K))‖≤(ε*‖a‖)*‖x‖
  exact ((G.comp (σ (a:Algebra M))-(inclusion M (a:Algebra M)).comp G).le_opNorm (x:K)).trans
    (mul_le_mul_of_nonneg_right (hδ a) (norm_nonneg _))

include hj hGp in
theorem exists_matrix_corner_intertwiner (v : ι → Algebra M)
    (hcol : ∀ i j, star (v i)*v j=if i=j then p else 0)
    (hinit : ∀ i, p*star (v i)=star (v i))
    (htotal : ∑ i, v i*star (v i)=1)
    (hGv : ∀ i x, G (σ (v i) x)=inclusion M (v i) (G x))
    (Ω : K) (hΩ : DenseRange (fun a : Algebra M => σ a Ω)) (hpΩ : σ p Ω=Ω)
    {ε : ℝ} (hε : 0≤ε)
    (hδ : ∀ a : Corner hp, ‖G.comp (σ (a:Algebra M))-(inclusion M (a:Algebra M)).comp G‖≤ε*‖a‖) :
    ∃ T : K →L[ℂ] H, (∀ a : Algebra M, T.comp (σ a)=(inclusion M a).comp T) ∧
      ‖G-T‖≤16*ε := by
  let Ωp : fixedSpace (σ p) := ⟨Ω,(mem_fixedSpace _ _).mpr hpΩ⟩
  obtain ⟨T,hT,hn⟩ := CyclicSpatial.exists_embedded_cyclic_intertwiner
    (corner σ hp) (representation hp) (cornerEmbedding M σ j hj hp)
    (cornerEmbedding_intertwines M σ j hj hp) (vonNeumann hp)
    (representation_injective hp) (vonNeumann_range hp)
    (cornerMap σ (inclusion M) G hGp) Ωp (corner_dense σ hp Ω hΩ hpΩ) hε
    (corner_derivation_bound M σ hp G hGp hε hδ)
  refine ⟨extend σ (inclusion M) v hcol hinit htotal T,?_,?_⟩
  · exact extend_intertwines σ (inclusion M) hp v hcol hinit htotal T hT
  · exact (norm_sub_extend_le σ (inclusion M) v hcol hinit htotal G hGp T hGv).trans hn

end Kadison.MatrixCornerImplementation

end

end
end

end OAI
