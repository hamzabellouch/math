import Mathlib
import OAI.Analysis.Commutator.HilbertModuleExtension
import OAI.Analysis.Commutator.ReducingRepresentation

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.MatrixCornerExtension

open MatrixCornerHilbert

variable {A K H ι : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [DecidableEq ι]

variable (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

variable {p : A} (hp : IsStarProjection p) (v : ι → A)
  (hcol : ∀ i j, star (v i)*v j=if i=j then p else 0)
  (hinit : ∀ i, p*star (v i)=star (v i))
  (htotal : ∑ i, v i*star (v i)=1)

include hcol in
omit [Fintype ι] in
lemma mapped_col (i j : ι) : star (σ (v i))*σ (v j)=if i=j then σ p else 0 := by
  simpa only [map_mul,map_star,apply_ite,map_zero] using congrArg σ (hcol i j)

include hinit in
omit [Fintype ι] [DecidableEq ι] in
lemma mapped_init (i : ι) : σ p*star (σ (v i))=star (σ (v i)) := by
  simpa only [map_mul,map_star] using congrArg σ (hinit i)

include htotal in
omit [DecidableEq ι] in
lemma mapped_total : ∑ i, σ (v i)*star (σ (v i))=1 := by
  simpa only [map_sum,map_mul,map_star,map_one] using congrArg σ htotal

def columns (i : ι) : fixedSpace (σ p) →ₗᵢ[ℂ] K :=
  matrixInsert (σ p) (fun i => σ (v i)) (mapped_col σ v hcol) i

include hinit htotal in
lemma columns_total : IsHilbertSum ℂ (fun _ : ι => fixedSpace (σ p)) (columns σ v hcol) :=
  matrixInsert_isHilbertSum (σ p) (fun i => σ (v i)) (mapped_col σ v hcol)
    (mapped_init σ v hinit) (mapped_total σ v htotal)

include hinit in
omit [Fintype ι] in
lemma columns_project (i : ι) (x : K) :
    (ActualHilbertSum.project (fun _ : ι => fixedSpace (σ p)) (columns σ v hcol) i x : K)=
      (star (σ (v i))) x :=
  matrixInsert_adjoint (σ p) (fun i => σ (v i)) (mapped_col σ v hcol)
    (mapped_init σ v hinit) i x

include hp hinit in
omit [Fintype ι] [DecidableEq ι] in
lemma final_support (i : ι) : v i*p=v i := by
  simpa only [star_mul,star_star,hp.isSelfAdjoint.star_eq] using congrArg star (hinit i)

def entry (i j : ι) (a : A) : Corner hp :=
  ⟨star (v i)*a*v j,by rw [←mul_assoc,←mul_assoc,hinit i],
    by rw [mul_assoc,final_support hp v hinit j]⟩

omit [Fintype ι] in
lemma columns_block (i j : ι) (a : A) (x : fixedSpace (σ p)) :
    ActualHilbertSum.project (fun _ : ι => fixedSpace (σ p)) (columns σ v hcol) i
      (σ a (columns σ v hcol j x)) =
      ReducingRepresentation.corner σ hp (entry hp v hinit i j a) x := by
  apply Subtype.ext
  rw [columns_project σ v hcol hinit]
  change star (σ (v i)) (σ a (σ (v j) x))=σ (star (v i)*a*v j) x
  simp only [map_mul,map_star,mul_apply_eq_comp]

def extend (T : fixedSpace (σ p) →L[ℂ] fixedSpace (ρ p)) : K →L[ℂ] H :=
  HilbertModuleExtension.extend (columns σ v hcol) (columns ρ v hcol)
    (columns_total σ v hcol hinit htotal) (columns_total ρ v hcol hinit htotal) T

lemma extend_norm_le (T : fixedSpace (σ p) →L[ℂ] fixedSpace (ρ p)) :
    ‖extend σ ρ v hcol hinit htotal T‖≤‖T‖ :=
  HilbertModuleExtension.extend_norm_le _ _ _ _ T

lemma extend_intertwines (T : fixedSpace (σ p) →L[ℂ] fixedSpace (ρ p))
    (hT : ∀ a : Corner hp, T.comp (ReducingRepresentation.corner σ hp a)=
      (ReducingRepresentation.corner ρ hp a).comp T) (a : A) :
    (extend σ ρ v hcol hinit htotal T).comp (σ a)=
      (ρ a).comp (extend σ ρ v hcol hinit htotal T) := by
  apply HilbertModuleExtension.extend_intertwines
  intro i j x
  rw [columns_block σ hp v hcol hinit,columns_block ρ hp v hcol hinit]
  exact congrArg (fun R : fixedSpace (σ p) →L[ℂ] fixedSpace (ρ p) => R x)
    (hT (entry hp v hinit i j a))

variable (G : K →L[ℂ] H) (hGp : ∀ x, G (σ p x)=ρ p (G x))

def cornerMap : fixedSpace (σ p) →L[ℂ] fixedSpace (ρ p) :=
  G.restrict (by
    intro x hx
    rw [mem_fixedSpace] at hx ⊢
    rw [←hGp x,hx])

lemma norm_sub_extend_le (T : fixedSpace (σ p) →L[ℂ] fixedSpace (ρ p))
    (hGv : ∀ i x, G (σ (v i) x)=ρ (v i) (G x)) :
    ‖G-extend σ ρ v hcol hinit htotal T‖≤‖cornerMap σ ρ G hGp-T‖ := by
  apply HilbertModuleExtension.norm_sub_extend_le
  intro i x
  exact hGv i x

end Kadison.MatrixCornerExtension

end

end
end

end OAI
