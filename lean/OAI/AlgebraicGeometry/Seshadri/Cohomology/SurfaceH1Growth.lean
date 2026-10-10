import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.SurfacePositiveSquare
import OAI.AlgebraicGeometry.Seshadri.Cohomology.SurfaceH2Untwist

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}}
local instance : HasExt.{1} X.Modules := schemeHasExt

lemma cohomologyDimension_middle_bound (p : X ⟶ Spec (CommRingCat.of ℂ))
    {T : ShortComplex X.Modules} (hT : T.ShortExact) (n : ℕ)
    (hf₁ : letI := Module.compHom (cohomology T.X₁ n) (baseScalars p)
      Module.Finite ℂ (cohomology T.X₁ n))
    (hf₂ : letI := Module.compHom (cohomology T.X₂ n) (baseScalars p)
      Module.Finite ℂ (cohomology T.X₂ n))
    (hf₃ : letI := Module.compHom (cohomology T.X₃ n) (baseScalars p)
      Module.Finite ℂ (cohomology T.X₃ n)) :
    cohomologyDimension p T.X₂ n ≤ cohomologyDimension p T.X₁ n +
      cohomologyDimension p T.X₃ n := by
  let := Module.compHom (cohomology T.X₁ n) (baseScalars p)
  let := Module.compHom (cohomology T.X₂ n) (baseScalars p)
  let := Module.compHom (cohomology T.X₃ n) (baseScalars p)
  let := hf₁
  let := hf₂
  let := hf₃
  let f : cohomology T.X₁ n →ₗ[ℂ] cohomology T.X₂ n :=
    { toFun := (Ext.mk₀ T.f).postcompOfLinear Γ(X,⊤) (O X) (add_zero n)
      map_add' := (Ext.mk₀ T.f).postcompOfLinear Γ(X,⊤) (O X) (add_zero n) |>.map_add
      map_smul' := fun r x => ((Ext.mk₀ T.f).postcompOfLinear Γ(X,⊤) (O X) (add_zero n)).map_smul (baseScalars p r) x }
  let g : cohomology T.X₂ n →ₗ[ℂ] cohomology T.X₃ n :=
    { toFun := (Ext.mk₀ T.g).postcompOfLinear Γ(X,⊤) (O X) (add_zero n)
      map_add' := (Ext.mk₀ T.g).postcompOfLinear Γ(X,⊤) (O X) (add_zero n) |>.map_add
      map_smul' := fun r x => ((Ext.mk₀ T.g).postcompOfLinear Γ(X,⊤) (O X) (add_zero n)).map_smul (baseScalars p r) x }
  apply finrank_middle_le_of_exact f g
  intro x
  constructor
  · exact Ext.covariant_sequence_exact₂ (O X) hT x
  · rintro ⟨y,rfl⟩
    change (y.comp (Ext.mk₀ T.f) (add_zero n)).comp (Ext.mk₀ T.g) (add_zero n) = 0
    rw [Ext.comp_assoc,Ext.mk₀_comp_mk₀,T.zero,Ext.mk₀_zero,Ext.comp_zero] <;> omega

theorem Surface.power_H1_linear_bound (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ B G : ℕ, ∀ n : ℕ, cohomologyDimension S.structureMap (L.pow n).sheaf 1 ≤ B+G*n := by
  classical
  obtain ⟨d,hd,-,N,s,hs,v,hne,hi,hC⟩ := S.coprime_integral_section L hL 1 (by decide)
  let := hi
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let I := sectionIdeal k s hs v
  let C : IntegralCurve S := ⟨I.subscheme,I.subschemeι,inferInstance,inferInstance,hC⟩
  let G := cohomologyDimension (C.embedding ≫ S.structureMap) (O C.scheme) 1
  let f (n : ℕ) := cohomologyDimension S.structureMap (L.pow n).sheaf 1
  have hstep (n : ℕ) : f (n+d) ≤ f n+G := by
    let M := L.pow n
    let P := L.pow d
    let Q := (P.tensor M).pullback C.embedding
    let φ : M.sheaf ⟶ (P.tensor M).sheaf :=
      sectionMultiply P M (sectionCombination k s v)
    let : Mono φ := sectionMultiply_mono P M (sectionCombination k s v) hne
    obtain ⟨hz,hseq⟩ := CartierSequence.exact S.structureMap M (P.tensor M) φ I (by
      intro x
      obtain ⟨U,hx,⟨e⟩,⟨g⟩⟩ := common_affine_frames P M x
      refine ⟨U,hx,g,tensorFrame P M U.1 e g,?_⟩
      exact (sectionIdeal_on_any_frame k s hs v U e).trans
        (tensor_multiply_ideal P M (sectionCombination k s v) U e g).symm)
    have H := cohomologyDimension_middle_bound S.structureMap hseq 1
      (S.cohomology_finite L hL M 1) (S.cohomology_finite L hL (P.tensor M) 1)
      (C.pushforward_cohomology_finite S L hL Q 1)
    rw [cohomologyDimension_pushforward] at H
    have hdeg : 0 ≤ curveDegree S (P.tensor M) C := by
      rw [curveDegree_tensor S L hL,curveDegree_pow S L hL,curveDegree_pow S L hL]
      have hp := (C.ample_degree_positive S L hL).le
      exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hp) (mul_nonneg (Nat.cast_nonneg _) hp)
    have hg := C.H1_le S L hL Q hdeg
    have he := cohomologyDimension_iso S.structureMap (linePowerAdd L d n) 1
    change f (d+n) = cohomologyDimension S.structureMap (P.tensor M).sheaf 1 at he
    rw [Nat.add_comm d n] at he
    rw [he]
    exact H.trans (Nat.add_le_add_left hg _)
  let B := ∑ j ∈ Finset.range d, f j
  refine ⟨B,G,?_⟩
  intro n
  change f n ≤ B+G*n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < d
    · have H : f n ≤ B := Finset.single_le_sum (fun j _ => Nat.zero_le (f j)) (Finset.mem_range.mpr hn)
      exact H.trans (Nat.le_add_right _ _)
    · have hdn : d ≤ n := by omega
      have H := hstep (n-d)
      rw [Nat.sub_add_cancel hdn] at H
      have HH := ih (n-d) (by omega)
      have hm : G*(n-d)+G ≤ G*n := by
        rw [← Nat.mul_succ]
        exact Nat.mul_le_mul_left _ (by omega)
      omega

theorem Surface.power_H0_quadratic_upper (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ B G : ℕ, ∀ n : ℕ,
      2*(cohomologyDimension S.structureMap (L.pow n).sheaf 0 : ℤ) ≤
      (n : ℤ)*((n : ℤ)-1)*selfIntersection S L +
      2*(n : ℤ)*(eulerCharacteristic S.structureMap 2 L.sheaf -
        eulerCharacteristic S.structureMap 2 (O S.scheme)) +
      2*eulerCharacteristic S.structureMap 2 (O S.scheme) + 2*B+2*G*n := by
  obtain ⟨B,G,hG⟩ := S.power_H1_linear_bound L hL
  refine ⟨B,G,fun n => ?_⟩
  have he := S.power_euler_quadratic L hL n
  rw [surface_euler_expansion] at he
  have h := hG n
  have hb : (cohomologyDimension S.structureMap (L.pow n).sheaf 1 : ℤ) ≤ B+(G:ℤ)*n := by exact_mod_cast h
  have hn : (0:ℤ) ≤ cohomologyDimension S.structureMap (L.pow n).sheaf 2 := Nat.cast_nonneg _
  nlinarith
end
end MaximalSeshadri.Geometry

end

end OAI
