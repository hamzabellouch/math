import Mathlib
import OAI.Analysis.Commutator.MatrixCornerExtension
import OAI.Analysis.Commutator.ModuleZeroExtension

namespace OAI

noncomputable section

noncomputable section

open scoped InnerProductSpace ENNReal

open ContinuousLinearMap

namespace Kadison.HilbertModuleExtension

variable {ι E F K H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (V : ι → E →ₗᵢ[ℂ] K) (W : ι → F →ₗᵢ[ℂ] H)
  (hV : IsHilbertSum ℂ (fun _ : ι => E) V) (hW : IsHilbertSum ℂ (fun _ : ι => F) W)

end Kadison.HilbertModuleExtension

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

variable (G : K →L[ℂ] H) (hGp : ∀ x, G (σ p x)=ρ p (G x))

end Kadison.MatrixCornerExtension

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.ReducingRepresentation

open MatrixCornerHilbert MatrixCornerExtension

variable {A H F ι : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [Fintype ι] [DecidableEq ι]

variable (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F))

variable {p : A} (hp : IsStarProjection p) (v : ι → A)
  (hcol : ∀ i j, star (v i)*v j=if i=j then p else 0)
  (hinit : ∀ i, p*star (v i)=star (v i))
  (htotal : ∑ i, v i*star (v i)=1)

variable (K : Submodule ℂ H) [CompleteSpace K]
  (hinv : ∀ (a : A) (x : H), x∈K → σ a x∈K)

variable (G : H →L[ℂ] F) (hGp : ∀ x, G (σ p x)=ρ p (G x))

lemma restrict_intertwining (a : A) (hG : ∀ x, G (σ a x)=ρ a (G x)) (x : K) :
    (G.comp K.subtypeL) (restrict σ K hinv a x)=ρ a ((G.comp K.subtypeL) x) :=
  hG x

include hcol hinit htotal in
theorem local_module_from_corner
    (V : fixedSpace (restrict σ K hinv p) →L[ℂ] fixedSpace (ρ p))
    (hV : ∀ a : Corner hp,
      V.comp (corner (restrict σ K hinv) hp a)-(corner ρ hp a).comp V=
        (cornerMap (restrict σ K hinv) ρ (G.comp K.subtypeL)
          (restrict_intertwining σ ρ K hinv G p hGp)).comp (corner (restrict σ K hinv) hp a)-
        (corner ρ hp a).comp (cornerMap (restrict σ K hinv) ρ (G.comp K.subtypeL)
          (restrict_intertwining σ ρ K hinv G p hGp)))
    (hGv : ∀ i x, G (σ (v i) x)=ρ (v i) (G x)) :
    ∃ T : H →L[ℂ] F,
      (∀ a : A, T.comp (σ a)=(ρ a).comp T) ∧
      ∀ z∈K, ‖G z-T z‖≤‖V‖*‖z‖ := by
  let σK := restrict σ K hinv
  let GK := G.comp K.subtypeL
  let GE := cornerMap σK ρ GK (restrict_intertwining σ ρ K hinv G p hGp)
  let R := GE-V
  have hR : ∀ a : Corner hp, R.comp (corner σK hp a)=(corner ρ hp a).comp R := by
    intro a
    dsimp only [R]
    rw [sub_comp,comp_sub]
    have he := hV a
    change V.comp (corner σK hp a)-(corner ρ hp a).comp V=
      GE.comp (corner σK hp a)-(corner ρ hp a).comp GE at he
    apply sub_eq_sub_iff_add_eq_add.mpr
    exact (sub_eq_sub_iff_add_eq_add.mp he).symm.trans (add_comm _ _)
  let TK := MatrixCornerExtension.extend σK ρ v hcol hinit htotal R
  have hTK (a : A) : TK.comp (σK a)=(ρ a).comp TK :=
    MatrixCornerExtension.extend_intertwines σK ρ hp v hcol hinit htotal R hR a
  have hnorm : ‖GK-TK‖≤‖V‖ := by
    have he := MatrixCornerExtension.norm_sub_extend_le σK ρ v hcol hinit htotal GK
      (restrict_intertwining σ ρ K hinv G p hGp) R
      (fun i => restrict_intertwining σ ρ K hinv G (v i) (hGv i))
    have hsub : GE-R=V := sub_sub_cancel GE V
    exact he.trans_eq (congrArg norm hsub)
  refine ⟨extendZero (K := K) TK,extendZero_intertwines σ ρ K hinv TK hTK,?_⟩
  intro z hz
  exact norm_sub_extendZero_apply_le K G TK ‖V‖ hnorm ⟨z,hz⟩

end Kadison.ReducingRepresentation
end
end
end
end

end OAI
