import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Divisors.IntegralCurveCartier
import OAI.AlgebraicGeometry.Seshadri.Intersection.CurveIdealDegree
import OAI.AlgebraicGeometry.Seshadri.Intersection.SurfacePositiveSquare
import OAI.AlgebraicGeometry.Seshadri.Divisors.CartierResidual

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini

lemma IntegralCurve.degree_nonneg_of_restriction (S : Surface)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (C : IntegralCurve S)
    (M : LineBundle S.scheme) (s : O S.scheme ⟶ M.sheaf)
    (hs : pullbackSection C.embedding s ≠ 0) : 0 ≤ curveDegree S M C := by
  obtain ⟨σ,hσ,B,a,ha,hclosed⟩ := C.exists_projective_sections S A hA
  let := hσ
  let := hclosed
  have H := projective_section_euler_difference (C.embedding ≫ S.structureMap)
    C.dimension a ha (M.pullback C.embedding) (pullbackSection C.embedding s) hs
  change curveDegree S M C = _ at H
  rw [H]
  positivity

theorem Surface.effective_mixed_nonneg (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) (M : LineBundle S.scheme)
    (s : O S.scheme ⟶ M.sheaf) (hs : s ≠ 0) : 0 ≤ mixedEuler S L M := by
  classical
  obtain ⟨d,hd,-,N,a,ha,v,hne,hi,hC⟩ := S.coprime_integral_section L hL 1 (by decide)
  let := hi
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let C : IntegralCurve S := ⟨(sectionIdeal k a ha v).subscheme,
    (sectionIdeal k a ha v).subschemeι,inferInstance,inferInstance,hC⟩
  have hdeg (B : LineBundle S.scheme) :
      curveDegree S B C = (d : ℤ)*mixedEuler S L B :=
    generated_curveDegree_eq_mixedEuler S L hL B d k a ha v hne hC
  obtain ⟨J,ι,hJ⟩ := C.invertible_ideal S
  let := hJ.1
  obtain ⟨x⟩ := (inferInstance : Nonempty C.scheme)
  obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames J M (C.embedding x)
  let : Nonempty U.1 := ⟨⟨_,hx⟩⟩
  let : Nonempty (C.embedding ⁻¹ᵁ U.1) := ⟨⟨x,hx⟩⟩
  let : IsNoetherianRing Γ(S.scheme,U.1) := IsLocallyNoetherian.component_noetherian U
  let I := C.embedding.ker.ideal U
  let : I.IsPrime := C.affine_ideal_prime S U inferInstance
  let g := U.1.topIso.hom (endValue (e.inv ≫
    (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
      (Scheme.Modules.restrictUnitIso U.1.ι).hom))
  have hg : g ∈ I := by
    change g ∈ C.embedding.ker.ideal U
    rw [InvertibleLocal.presented_frame_equation C.embedding.ker J ι hJ U e]
    exact Ideal.subset_span (Set.mem_singleton g)
  have hterm : ∃ n : ℕ, affineCoefficient U f s ∉ I^n := by
    by_contra! hn
    have hh : affineCoefficient U f s ∈ (⨅ n : ℕ, I^n) :=
      Ideal.mem_iInf.mpr hn
    rw [I.iInf_pow_eq_bot_of_isDomain (Ideal.IsPrime.ne_top inferInstance)] at hh
    exact ((isRegular_iff_ne_zero).mp (M.section_coefficient_regular s hs U f)) hh
  obtain ⟨n,hn⟩ := hterm
  suffices H : ∀ n : ℕ, ∀ B : LineBundle S.scheme,
      ∀ f : B.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∀ s : O S.scheme ⟶ B.sheaf, s ≠ 0 →
      affineCoefficient U f s ∉ I^n → 0 ≤ mixedEuler S L B from H n M f s hs hn
  intro n
  induction n with
  | zero =>
    intro B f t ht hn
    exact (hn (by simp)).elim
  | succ n ih =>
    intro B f t ht hn
    by_cases hz : pullbackSection C.embedding t = 0
    · obtain ⟨q,hq,-⟩ := C.divide_section S J B ι hJ t hz
      have hq0 : q ≠ 0 := by
        intro hzero
        apply ht
        rw [hzero,zero_comp] at hq
        exact hq.symm
      have hqn : affineCoefficient U (tensorFrame J B U.1 e f) q ∉ I^n := by
        intro hh
        apply hn
        have hp : g * affineCoefficient U (tensorFrame J B U.1 e f) q ∈ I^(n+1) := by
          rw [pow_succ']
          exact Ideal.mul_mem_mul hg hh
        have H := Ideal.mem_of_dvd (I^(n+1))
          (affineCoefficient_tensorInclusion J B ι U e f q).dvd hp
        simpa only [hq] using H
      have hnonneg := ih (J.tensor B) (tensorFrame J B U.1 e f) q hq0 hqn
      rw [mixedEuler_tensor_right S L hL,
        C.ideal_mixed_degree S L hL J ι hJ L] at hnonneg
      have hp := C.ample_degree_positive S L hL
      linarith
    · have hnonneg := C.degree_nonneg_of_restriction S L hL B t hz
      rw [hdeg B] at hnonneg
      have hd' : (0 : ℤ) < d := by exact_mod_cast hd
      nlinarith

end
end MaximalSeshadri.Geometry

end


end OAI
