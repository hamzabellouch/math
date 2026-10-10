import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Model
import OAI.AlgebraicGeometry.Seshadri.Geometry.SmoothAffineRefinement
import OAI.AlgebraicGeometry.Seshadri.Configurations.SmoothRationalPoints
import OAI.AlgebraicGeometry.Seshadri.Geometry.EtalePointChart

namespace OAI


                                                
section

namespace MaximalSeshadri.LocalCurve
noncomputable section

open MvPolynomial
open MaximalSeshadri.AlgebraicJets

theorem two_le_dimension_of_standard_smooth {K S : Type} [Field K] [CommRing S]
    [Algebra K S] [Algebra.IsStandardSmoothOfRelativeDimension 2 K S]
    (ρ : S →ₐ[K] K) : 2 ≤ ringKrullDim S := by
  obtain ⟨x,hx,he⟩ := exists_centered_etale_coordinates 2 ρ
  let φ := aeval (R := K) x
  let : Algebra (MvPolynomial (Fin 2) K) S := φ.toRingHom.toAlgebra
  let : IsScalarTower K (MvPolynomial (Fin 2) K) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra.Etale (MvPolynomial (Fin 2) K) S := he
  let q := RingHom.ker ρ
  have : q.IsPrime := RingHom.ker_isPrime ρ
  have hq : q.under (MvPolynomial (Fin 2) K) = idealOfVars (Fin 2) K := by
    rw [idealOfVars_eq_ker_constantCoeff]
    have hc : ρ.toRingHom.comp φ.toRingHom = constantCoeff := by
      apply ringHom_ext
      · intro c; simp [φ]
      · intro i; simpa [φ] using hx i
    change RingHom.ker (ρ.toRingHom.comp φ.toRingHom) = _
    rw [hc]
  let : (idealOfVars (Fin 2) K).IsPrime := by
    rw [idealOfVars_eq_ker_constantCoeff]
    exact RingHom.ker_isPrime _
  let : q.LiesOver (idealOfVars (Fin 2) K) := ⟨hq.symm⟩
  let P : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {X (0 : Fin 2)}
  let : P.IsPrime := (Ideal.span_singleton_prime (X_ne_zero 0)).mpr X_prime
  have hP : P < idealOfVars (Fin 2) K := by
    refine lt_of_le_of_ne (Ideal.span_le.mpr (by
      rintro _ rfl
      exact Ideal.subset_span ⟨0,rfl⟩)) ?_
    intro H
    have h1 : X (1 : Fin 2) ∈ P := H ▸ Ideal.subset_span ⟨1,rfl⟩
    have hd : (X (0 : Fin 2) : MvPolynomial (Fin 2) K) ∣ X 1 :=
      Ideal.mem_span_singleton.mp h1
    have := X_dvd_X.mp hd
    norm_num at this
  obtain ⟨Q,hQ,hQP,hQL⟩ := Ideal.exists_ideal_lt_liesOver_of_lt q hP
  have := hQP
  have := hQL
  have hbot : (⊥ : Ideal (MvPolynomial (Fin 2) K)) < P := by
    apply bot_lt_iff_ne_bot.mpr
    intro H
    have h0 : X (0 : Fin 2) ∈ P := Ideal.subset_span (by simp)
    rw [H,Ideal.mem_bot] at h0
    exact X_ne_zero 0 h0
  obtain ⟨Q₀,hQ₀,hQ₀P,hQ₀L⟩ := Ideal.exists_ideal_lt_liesOver_of_lt Q hbot
  let l : LTSeries (PrimeSpectrum S) :=
    ((RelSeries.singleton {(a,b) : PrimeSpectrum S × PrimeSpectrum S | a < b} (⟨Q₀,hQ₀P⟩ : PrimeSpectrum S)).snoc
      (⟨Q,hQP⟩ : PrimeSpectrum S) hQ₀).snoc (⟨q,inferInstance⟩ : PrimeSpectrum S) hQ
  simpa only [show l.length = 2 from rfl, Nat.cast_ofNat, ringKrullDim] using
    Order.LTSeries.length_le_krullDim l
end
end MaximalSeshadri.LocalCurve

namespace MaximalSeshadri.Geometry
noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini

lemma Surface.two_le_dimension (S : Surface) : 2 ≤ topologicalKrullDim S.scheme := by
  obtain ⟨U,hxU,hU,hstd⟩ := exists_standard_smooth_affine_inside S.structureMap 2
    ⊤ (Classical.ofNonempty : S.scheme) (by trivial)
  let : Nonempty U.1 := ⟨⟨_,hxU⟩⟩
  let := (openScalars S.structureMap U.1).toAlgebra
  let : Algebra.IsStandardSmoothOfRelativeDimension 2 ℂ Γ(S.scheme,U.1) := hstd
  let : Algebra.IsStandardSmooth ℂ Γ(S.scheme,U.1) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 2
  have : Uncountable ℂ := by
    rw [← Cardinal.aleph0_lt_mk_iff, Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum
  obtain ⟨ρ,-⟩ := point_avoiding_sequence (F := ℂ) (A := Γ(S.scheme,U.1))
    (fun _ => 1) (fun _ => one_ne_zero)
  have hd := LocalCurve.two_le_dimension_of_standard_smooth ρ
  have : IsOpenImmersion U.2.fromSpec :=
    IsAffineOpen.isOpenImmersion_fromSpec U.2
  have he := U.2.fromSpec.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
  change topologicalKrullDim (PrimeSpectrum Γ(S.scheme,U.1)) ≤ _ at he
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at he
  exact hd.trans he
end
end MaximalSeshadri.Geometry

end

end OAI
