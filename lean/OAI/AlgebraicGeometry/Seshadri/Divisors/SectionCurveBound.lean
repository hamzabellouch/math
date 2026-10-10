import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.EtaleRealization
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionComponent
import OAI.AlgebraicGeometry.Seshadri.Intersection.EffectiveDegree
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.ExactPointOrder
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.CurveOrderExact

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

lemma affineComplexPoint_mem (S : Surface) (U : S.scheme.affineOpens)
    (ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
      Γ(S.scheme,U.1) →ₐ[ℂ] ℂ) :
    (affineComplexPoint S.structureMap U ρ).left (fieldPoint ℂ) ∈ U.1 := by
  have H := Set.mem_range_self (f := U.2.fromSpec)
    (⟨RingHom.ker ρ,RingHom.ker_isPrime _⟩ : PrimeSpectrum Γ(S.scheme,U.1))
  rwa [U.2.range_fromSpec] at H

lemma Surface.etale_cancel_power (S : Surface) (U : S.scheme.affineOpens)
    (t : Fin 2 → Γ(S.scheme,U.1))
    (het : (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale)
    (ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
      Γ(S.scheme,U.1) →ₐ[ℂ] ℂ)
    (a b : Γ(S.scheme,U.1)) (n m : ℕ)
    (ha : a ∉ (RingHom.ker ρ)^(m+1)) (hab : a*b ∈ (RingHom.ker ρ)^n) :
    b ∈ (RingHom.ker ρ)^(n-m) := by
  let := (openScalars S.structureMap U.1).toAlgebra
  let : Nonempty U.1 := ⟨⟨_,affineComplexPoint_mem S U ρ⟩⟩
  let φ := MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t
  let : Algebra (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) := φ.toAlgebra
  let : IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z
      change openScalars S.structureMap U.1 z = φ (MvPolynomial.C z)
      simp [φ])
  let : Algebra.Etale (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) := het
  let : Algebra.IsStandardSmoothOfRelativeDimension 2 ℂ (MvPolynomial (Fin 2) ℂ) :=
    MaximalSeshadri.QuadraticJets.polynomial_binary_standardSmooth
  let : Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin 2) ℂ)
      Γ(S.scheme,U.1) := Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp inferInstance
  let : Algebra.IsStandardSmoothOfRelativeDimension 2 ℂ Γ(S.scheme,U.1) :=
    Algebra.IsStandardSmoothOfRelativeDimension.trans 2 0 ℂ (MvPolynomial (Fin 2) ℂ) _
  exact standard_smooth_cancel_power ρ a b n m ha hab

lemma Surface.section_contains_curve_of_order (S : Surface) (M : LineBundle S.scheme)
    (s : O S.scheme ⟶ M.sheaf) (hs : s ≠ 0)
    (U : S.scheme.affineOpens) (e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
      Γ(S.scheme,U.1) →ₐ[ℂ] ℂ) (n : ℕ) (hn : 0 < n)
    (ho : affineCoefficient U e s ∈ (RingHom.ker ρ)^n) :
    ∃ C : IntegralCurve S, pullbackSection C.embedding s = 0 := by
  let p : ComplexPoint S := affineComplexPoint S.structureMap U ρ
  obtain ⟨V,hp,hVU,f,t,het⟩ := S.etale_line_frame_inside M U.1 p.image
    (affineComplexPoint_mem S U ρ)
  obtain ⟨σ,hσ⟩ := affineComplexPoint_factor S.structureMap V p hp
  have ho' := (affineCoefficient_order_restrict_iff S.structureMap U V hVU e f ρ σ
    hσ.symm s n).mp ho
  apply S.section_contains_curve M s hs V f t het σ
  exact (Ideal.pow_le_self (Nat.ne_of_gt hn)) ho'

lemma IntegralCurve.residual_order (S : Surface) (C : IntegralCurve S)
    (J M : LineBundle S.scheme) (ι : J.sheaf ⟶ O S.scheme)
    (hJ : PresentsPullbackIdeal C.embedding.ker (𝟙 S.scheme) J ι)
    (s : O S.scheme ⟶ M.sheaf) (q : O S.scheme ⟶ (J.tensor M).sheaf)
    (hq : q ≫ tensorInclusion J M ι = s)
    (U : S.scheme.affineOpens) (f : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
      Γ(S.scheme,U.1) →ₐ[ℂ] ℂ) (n : ℕ)
    (ho : affineCoefficient U f s ∈ (RingHom.ker ρ)^n) :
    ∃ V : S.scheme.affineOpens,
    ∃ e : (J.tensor M).sheaf.restrict V.1.ι ≅ O V.1.toScheme,
    ∃ σ : letI := (openScalars S.structureMap V.1).toAlgebra;
      Γ(S.scheme,V.1) →ₐ[ℂ] ℂ,
      affineComplexPoint S.structureMap V σ = affineComplexPoint S.structureMap U ρ ∧
      affineCoefficient V e q ∈ (RingHom.ker σ)^
        (n-curveMultiplicity S C (affineComplexPoint S.structureMap U ρ)) := by
  let p : ComplexPoint S := affineComplexPoint S.structureMap U ρ
  obtain ⟨V,hp,hVU,e,t,het⟩ := S.etale_line_frame_inside J U.1 p.image
    (affineComplexPoint_mem S U ρ)
  obtain ⟨σ,hσ⟩ := affineComplexPoint_factor S.structureMap V p hp
  let f' := frameOnSmaller f V.1 hVU
  let g := V.1.topIso.hom (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor V.1.ι).map ι ≫
    (Scheme.Modules.restrictUnitIso V.1.ι).hom))
  refine ⟨V,tensorFrame J M V.1 e f',σ,hσ,?_⟩
  apply S.etale_cancel_power V t het σ g _ n (curveMultiplicity S C p)
  · intro hg
    have hh := C.affine_ideal_not_le_next_multiplicity S V σ
    rw [hσ, InvertibleLocal.presented_frame_equation C.embedding.ker J ι hJ V e] at hh
    exact hh (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hg))
  · have ho' := (affineCoefficient_order_restrict_iff S.structureMap U V hVU f f' ρ σ
      hσ.symm s n).mp ho
    apply (Ideal.mem_iff_of_associated (affineCoefficient_tensorInclusion J M ι V e f' q)).mpr
    simpa only [hq] using ho'

theorem section_bound_of_curve_bound (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) {r : ℕ} (p : Configuration S r) (a : ℝ) (ha : 0 ≤ a)
    (hC : ∀ C : IntegralCurve S,
      a*(totalMultiplicity S r C p:ℝ) ≤ (curveDegree S L C:ℝ))
    (M : LineBundle S.scheme) (s : O S.scheme ⟶ M.sheaf) (hs : s ≠ 0)
    (U : Fin r → S.scheme.affineOpens)
    (e : ∀ i, M.sheaf.restrict (U i).1.ι ≅ O (U i).1.toScheme)
    (ρ : ∀ i, letI := (openScalars S.structureMap (U i).1).toAlgebra;
      Γ(S.scheme,(U i).1) →ₐ[ℂ] ℂ)
    (hρ : ∀ i, affineComplexPoint S.structureMap (U i) (ρ i) = p.val i)
    (n : Fin r → ℕ)
    (ho : ∀ i, affineCoefficient (U i) (e i) s ∈ (RingHom.ker (ρ i))^(n i)) :
    a*(∑ i, n i:ℕ) ≤ (mixedEuler S L M:ℝ) := by
  classical
  suffices H : ∀ d : ℕ, ∀ M : LineBundle S.scheme,
      (mixedEuler S L M).toNat = d →
      ∀ s : O S.scheme ⟶ M.sheaf, s ≠ 0 →
      ∀ U : Fin r → S.scheme.affineOpens,
      ∀ e : ∀ i, M.sheaf.restrict (U i).1.ι ≅ O (U i).1.toScheme,
      ∀ ρ : ∀ i, letI := (openScalars S.structureMap (U i).1).toAlgebra;
        Γ(S.scheme,(U i).1) →ₐ[ℂ] ℂ,
      (∀ i, affineComplexPoint S.structureMap (U i) (ρ i) = p.val i) →
      ∀ n : Fin r → ℕ,
      (∀ i, affineCoefficient (U i) (e i) s ∈ (RingHom.ker (ρ i))^(n i)) →
      a*(∑ i, n i:ℕ) ≤ (mixedEuler S L M:ℝ) from
    H _ M rfl s hs U e ρ hρ n ho
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro M hd s hs U e ρ hρ n ho
    have hnonneg := S.effective_mixed_nonneg L hL M s hs
    by_cases hz : ∀ i, n i = 0
    · simp only [hz,Finset.sum_const_zero,Nat.cast_zero,mul_zero]
      exact_mod_cast hnonneg
    obtain ⟨i,hi⟩ := not_forall.mp hz
    obtain ⟨C,hCs⟩ := S.section_contains_curve_of_order M s hs (U i) (e i) (ρ i)
      (n i) (Nat.pos_of_ne_zero hi) (ho i)
    obtain ⟨J,ι,hJ⟩ := C.invertible_ideal S
    obtain ⟨q,hq,-⟩ := C.divide_section S J M ι hJ s hCs
    have hq0 : q ≠ 0 := by
      intro hh
      apply hs
      rw [hh,zero_comp] at hq
      exact hq.symm
    have hqnonneg := S.effective_mixed_nonneg L hL (J.tensor M) q hq0
    have heq : mixedEuler S L (J.tensor M) = mixedEuler S L M-curveDegree S L C := by
      rw [mixedEuler_tensor_right S L hL,C.ideal_mixed_degree S L hL J ι hJ L]
      ring
    have hlt : (mixedEuler S L (J.tensor M)).toNat < d := by
      rw [← hd]
      have hpos := C.ample_degree_positive S L hL
      omega
    choose V f σ hσ horders using fun j => C.residual_order S J M ι hJ s q hq
      (U j) (e j) (ρ j) (n j) (ho j)
    have hb := ih _ hlt (J.tensor M) rfl q hq0 V f σ
      (fun j => (hσ j).trans (hρ j))
      (fun j => n j-curveMultiplicity S C (p.val j)) (by
        intro j
        simpa only [hρ j] using horders j)
    have hn : (∑ j, n j:ℕ) ≤ (∑ j, (n j-curveMultiplicity S C (p.val j)):ℕ)+
        totalMultiplicity S r C p := by
      unfold totalMultiplicity
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun j _ => by omega
    have hn' : (∑ j, n j:ℕ) ≤
        ((∑ j, (n j-curveMultiplicity S C (p.val j)):ℕ):ℝ)+(totalMultiplicity S r C p:ℝ) := by
      exact_mod_cast hn
    have H := mul_le_mul_of_nonneg_left hn' ha
    have hc := hC C
    rw [heq,Int.cast_sub] at hb
    nlinarith only [H,hb,hc]

end
end MaximalSeshadri.Geometry

end


end OAI
