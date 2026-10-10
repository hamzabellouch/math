import OAI.Analysis.KadisonKastler.PureCommutingCompression
import OAI.Analysis.KadisonKastler.IsometricCompressionState

namespace OAI

/-! # Compression along a state-preserving inclusion

The GNS isometry supplies a concrete unital positive compression and its
matrix coefficients. It will be used to prescribe the two product marginals.
-/

namespace KadisonKastler

open NaimarkZFC
open scoped ComplexOrder

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

theorem gns_matrix_coefficient (P : B →ₚ[ℂ] ℂ) (x c y : B) :
    inner ℂ (P.gnsStarAlgHom x (gnsVector P))
      (P.gnsStarAlgHom c (P.gnsStarAlgHom y (gnsVector P)))=P (star x*c*y) := by
  rw [← gnsVector_coefficient P (star x*c*y)]
  simp only [map_mul,map_star,mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.adjoint_inner_right]

def gnsInclusion (P : B →ₚ[ℂ] ℂ) (Q : A →ₚ[ℂ] ℂ)
    (ι : A →⋆ₐ[ℂ] B) (hPQ : ∀ a, Q a=P (ι a)) : Q.GNS →L[ℂ] P.GNS :=
  cyclicGNSMap Q (P.gnsStarAlgHom.comp ι).toNonUnitalStarAlgHom (gnsVector P)
    (fun a => (hPQ a).trans (gnsVector_coefficient P (ι a)).symm)

theorem gnsInclusion_isometry (P : B →ₚ[ℂ] ℂ) (Q : A →ₚ[ℂ] ℂ)
    (ι : A →⋆ₐ[ℂ] B) (hPQ : ∀ a, Q a=P (ι a)) : Isometry (gnsInclusion P Q ι hPQ) := by
  apply (AddMonoidHomClass.isometry_iff_norm _).mpr
  exact cyclicGNSMap_norm Q (P.gnsStarAlgHom.comp ι).toNonUnitalStarAlgHom
    (gnsVector P) (fun a => (hPQ a).trans (gnsVector_coefficient P (ι a)).symm)

theorem gnsInclusion_vector (P : B →ₚ[ℂ] ℂ) (Q : A →ₚ[ℂ] ℂ)
    (ι : A →⋆ₐ[ℂ] B) (hPQ : ∀ a, Q a=P (ι a)) :
    gnsInclusion P Q ι hPQ (gnsVector Q)=gnsVector P := by
  change cyclicGNSMap Q (P.gnsStarAlgHom.comp ι).toNonUnitalStarAlgHom (gnsVector P)
    (fun a => (hPQ a).trans (gnsVector_coefficient P (ι a)).symm) (Q.toPreGNS 1)=_
  rw [cyclicGNSMap_apply]
  have hone : (P.gnsStarAlgHom.comp ι) 1=1 := map_one _
  change (P.gnsStarAlgHom.comp ι) 1 (gnsVector P)=_
  rw [hone]
  rfl

theorem gnsInclusion_intertwines (P : B →ₚ[ℂ] ℂ) (Q : A →ₚ[ℂ] ℂ)
    (ι : A →⋆ₐ[ℂ] B) (hPQ : ∀ a, Q a=P (ι a)) (a : A) :
    (gnsInclusion P Q ι hPQ).comp (Q.gnsStarAlgHom a)=
      (P.gnsStarAlgHom (ι a)).comp (gnsInclusion P Q ι hPQ) :=
  cyclicGNSMap_intertwines Q (P.gnsStarAlgHom.comp ι).toNonUnitalStarAlgHom
    (gnsVector P) (fun a => (hPQ a).trans (gnsVector_coefficient P (ι a)).symm) a

theorem gnsInclusion_orbit (P : B →ₚ[ℂ] ℂ) (Q : A →ₚ[ℂ] ℂ)
    (ι : A →⋆ₐ[ℂ] B) (hPQ : ∀ a, Q a=P (ι a)) (a : A) :
    gnsInclusion P Q ι hPQ (Q.gnsStarAlgHom a (gnsVector Q))=
      P.gnsStarAlgHom (ι a) (gnsVector P) := by
  have h := congrArg (fun L : Q.GNS →L[ℂ] P.GNS => L (gnsVector Q))
    (gnsInclusion_intertwines P Q ι hPQ a)
  change gnsInclusion P Q ι hPQ (Q.gnsStarAlgHom a (gnsVector Q))=
    P.gnsStarAlgHom (ι a) (gnsInclusion P Q ι hPQ (gnsVector Q)) at h
  rwa [gnsInclusion_vector] at h

def gnsCompression (P : B →ₚ[ℂ] ℂ) (Q : A →ₚ[ℂ] ℂ)
    (ι : A →⋆ₐ[ℂ] B) (hPQ : ∀ a, Q a=P (ι a)) : B →L[ℂ] (Q.GNS →L[ℂ] Q.GNS) :=
  (operatorCompression (gnsInclusion P Q ι hPQ)).comp (starAlgHomCLM P.gnsStarAlgHom)

theorem gnsCompression_state (P : B →ₚ[ℂ] ℂ) (Q : A →ₚ[ℂ] ℂ)
    (ι : A →⋆ₐ[ℂ] B) (hPQ : ∀ a, Q a=P (ι a))
    (F : (Q.GNS →L[ℂ] Q.GNS) →L[ℂ] ℂ) (hF : IsState F) :
    IsState (F.comp (gnsCompression P Q ι hPQ)) := by
  have hG := state_comp_isometricCompression (gnsInclusion P Q ι hPQ)
    (gnsInclusion_isometry P Q ι hPQ) F hF
  have he : F.comp (gnsCompression P Q ι hPQ)=
      restrictState P.gnsStarAlgHom (F.comp (operatorCompression (gnsInclusion P Q ι hPQ))) := by
    ext b
    rfl
  rw [he]
  exact isState_restrict P.gnsStarAlgHom
    (F.comp (operatorCompression (gnsInclusion P Q ι hPQ))) hG

theorem gnsCompression_pairing (P : B →ₚ[ℂ] ℂ) (Q : A →ₚ[ℂ] ℂ)
    (ι : A →⋆ₐ[ℂ] B) (hPQ : ∀ a, Q a=P (ι a)) (c : B) (x y : A) :
    inner ℂ (Q.gnsStarAlgHom x (gnsVector Q))
      (gnsCompression P Q ι hPQ c (Q.gnsStarAlgHom y (gnsVector Q)))=
        P (star (ι x)*c*ι y) := by
  change inner ℂ (Q.gnsStarAlgHom x (gnsVector Q))
    ((gnsInclusion P Q ι hPQ).adjoint
      (P.gnsStarAlgHom c (gnsInclusion P Q ι hPQ (Q.gnsStarAlgHom y (gnsVector Q)))))=_
  rw [ContinuousLinearMap.adjoint_inner_right,gnsInclusion_orbit,gnsInclusion_orbit]
  exact gns_matrix_coefficient P (ι x) c (ι y)

theorem gnsCompression_eq_of_pairings (P : B →ₚ[ℂ] ℂ) (Q : A →ₚ[ℂ] ℂ)
    (ι : A →⋆ₐ[ℂ] B) (hPQ : ∀ a, Q a=P (ι a)) (c : B) (T : Q.GNS →L[ℂ] Q.GNS)
    (hT : ∀ x y : A, P (star (ι x)*c*ι y)=
      inner ℂ (Q.gnsStarAlgHom x (gnsVector Q)) (T (Q.gnsStarAlgHom y (gnsVector Q)))) :
    gnsCompression P Q ι hPQ c=T := by
  apply DFunLike.coe_injective
  apply (gnsVector_cyclic Q).equalizer (gnsCompression P Q ι hPQ c).continuous T.continuous
  funext y
  apply DenseRange.eq_of_inner_right ℂ (gnsVector_cyclic Q)
  intro x
  change inner ℂ (Q.gnsStarAlgHom x (gnsVector Q))
    (gnsCompression P Q ι hPQ c (Q.gnsStarAlgHom y (gnsVector Q)))=
      inner ℂ (Q.gnsStarAlgHom x (gnsVector Q)) (T (Q.gnsStarAlgHom y (gnsVector Q)))
  rw [gnsCompression_pairing]
  exact hT x y

end

end KadisonKastler

end OAI
