import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Divisors.IntegralCurveCartier
import OAI.AlgebraicGeometry.Seshadri.Intersection.BivariateSurfaceEuler
import OAI.AlgebraicGeometry.Seshadri.Geometry.CurveMultiplicity
import OAI.AlgebraicGeometry.Seshadri.Sheaves.AffineOrderRestriction
import OAI.AlgebraicGeometry.Seshadri.Sheaves.EtaleLineFrame
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.TwistedIdealPower
import OAI.AlgebraicGeometry.Seshadri.Interpolation.VeryGeneralInterpolation
import OAI.AlgebraicGeometry.Seshadri.Jets.EffectiveJetFrames
import OAI.AlgebraicGeometry.Seshadri.Blowup.UnequalNefNumerics

namespace OAI


                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

theorem curve_lower_of_homogeneous_section_test (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) {r : ℕ} (hr : 0 < r)
    (p : Configuration S r) (U : S.scheme.affineOpens)
    (eL : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (htest : ∀ k m : ℕ, 0 < k → 0 < m →
      (k:ℝ)*Real.sqrt ((selfIntersection S L:ℝ)/r) < (m:ℝ) →
      ∃ ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
          Fin r → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ),
        (∀ i, affineComplexPoint S.structureMap U (ρ i) = p.val i) ∧
        ∀ s : O S.scheme ⟶ (L.pow k).sheaf,
          (∀ i, affineCoefficient U (localPowerFrame U.1 eL k) s ∈
            (RingHom.ker (ρ i))^m) → s = 0)
    (C : IntegralCurve S) :
    Real.sqrt ((selfIntersection S L:ℝ)/r) * (totalMultiplicity S r C p:ℝ) ≤
      (curveDegree S L C:ℝ) := by
  classical
  by_contra hc
  have hneg : (curveDegree S L C:ℝ)-Real.sqrt ((selfIntersection S L:ℝ)/r)*
      (∑ i, curveMultiplicity S C (p.val i):ℕ) < 0 := by
    change ¬ _ ≤ _ at hc
    change _ - _ * (totalMultiplicity S r C p:ℝ) < 0
    linarith
  obtain ⟨J,ι,hJ⟩ := C.invertible_ideal S
  have hmono : Mono (C := S.scheme.Modules) (X := J.sheaf)
      (Y := structureSheaf S.scheme) ι := hJ.1
  let μ : Fin r → ℕ := fun i => curveMultiplicity S C (p.val i)
  obtain ⟨a,b,m,ha,hb,hm,ham,hbm,hmix,hquad⟩ :=
    NefNumerics.exists_integral_unequal_perturbation μ (selfIntersection S L)
      (curveDegree S L C) (selfIntersection S J) (S.selfIntersection_pos L hL)
        hr (C.ample_degree_positive S L hL) hneg
  let M := (L.pow a).tensor (J.pow b)
  have hj := C.ideal_mixed_degree S L hL J ι hJ L
  have hMM : 0 ≤ mixedEuler S L M := by
    dsimp [M]
    rw [mixedEuler_twist_pow S L hL,hj]
    linarith
  have hMQ : (∑ i, (m-b*μ i)^2:ℕ) < selfIntersection S M := by
    dsimp [M]
    rw [S.selfIntersection_twist_pow L hL,hj]
    nlinarith only [hquad]
  obtain ⟨ρ,hρ,-⟩ := htest a m ha hm ham
  have hpU (i : Fin r) : (p.val i).image ∈ U.1 := by
    rw [← hρ i]
    have H := Set.mem_range_self (f := U.2.fromSpec)
      (⟨RingHom.ker (ρ i),RingHom.ker_isPrime _⟩ : PrimeSpectrum Γ(S.scheme,U.1))
    rw [U.2.range_fromSpec] at H
    exact H
  choose V hpV hVU eJ t het using fun i => S.etale_line_frame_inside J U.1
    (p.val i).image (hpU i)
  choose σ hσ using fun i => affineComplexPoint_factor S.structureMap (V i) (p.val i) (hpV i)
  obtain ⟨N,hN,hEff⟩ := S.eventually_effective_with_arbitrary_jet_frames L hL M hMM
    (fun i => m-b*μ i) hMQ V t het σ
  let f (i : Fin r) : (L.pow (a*N)).sheaf.restrict (V i).1.ι ≅ O (V i).1.toScheme :=
    frameOnSmaller (localPowerFrame U.1 eL (a*N)) (V i).1 (hVU i)
  let e (i : Fin r) : (M.pow N).sheaf.restrict (V i).1.ι ≅ O (V i).1.toScheme :=
    twistedIdealPowerFrame L J a b N (V i).1 (eJ i) (f i)
  obtain ⟨s,hs,horders⟩ := hEff N le_rfl e
  let g := twistedIdealPowerInclusion L J ι a b N
  have : Mono g := @twistedIdealPowerInclusion_mono S.scheme L J ι hmono a b N
  have hnonzero : s ≫ g ≠ 0 := by
    intro hh
    apply hs
    apply (cancel_mono g).mp
    simpa using hh
  have hjet (i : Fin r) : affineCoefficient (V i) (f i) (s ≫ g) ∈
      (RingHom.ker (σ i))^(N*m) := by
    have hideal := C.affine_ideal_le_multiplicity S (V i) (σ i)
    rw [hσ i] at hideal
    have hmap : Ideal.span {affineMapCoefficient (V i) (e i) (f i) g} ≤
        (RingHom.ker (σ i))^(b*N*μ i) := by
      refine (twistedIdealPowerInclusion_ideal L J ι a b N (V i) (eJ i) (f i)).le.trans ?_
      refine (congrArg (fun ideal : Ideal Γ(S.scheme, (V i).1) => ideal^(b*N))
        (InvertibleLocal.presented_frame_equation C.embedding.ker J ι hJ
          (V i) (eJ i))).symm.le.trans ?_
      have HH := pow_le_pow_left' hideal (b*N)
      rw [← pow_mul] at HH
      have heq : curveMultiplicity S C (p.val i)*(b*N) = b*N*μ i := by dsimp [μ]; ring
      rw [heq] at HH
      exact HH
    have H := affineCoefficient_map_order (V i) (e i) (f i) s g
      (RingHom.ker (σ i)) (N*(m-b*μ i)) (b*N*μ i) (horders i) hmap
    have heq : N*(m-b*μ i)+b*N*μ i = N*m := by
      rw [show b*N*μ i = N*(b*μ i) by ring,← Nat.mul_add,Nat.sub_add_cancel (hbm i)]
    rwa [heq] at H
  have hkm : ((a*N:ℕ):ℝ)*Real.sqrt ((selfIntersection S L:ℝ)/r) < ((N*m:ℕ):ℝ) := by
    have H := mul_lt_mul_of_pos_left ham (show (0:ℝ) < N by exact_mod_cast hN)
    push_cast
    nlinarith only [H]
  obtain ⟨ρ',hρ',hsep⟩ := htest (a*N) (N*m) (Nat.mul_pos ha hN)
    (Nat.mul_pos hN hm) hkm
  apply hnonzero
  apply hsep
  intro i
  exact (affineCoefficient_order_restrict_iff S.structureMap U (V i) (hVU i)
    (localPowerFrame U.1 eL (a*N)) (f i) (ρ' i) (σ i)
      ((hρ' i).trans (hσ i).symm) (s ≫ g) (N*m)).mpr (hjet i)

theorem Surface.eventual_very_general_curve_lower (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
      ∃ Z : ℕ → Set (Configuration S r),
        (∀ n, IsClosed (Z n) ∧ Z n ≠ Set.univ) ∧
        (∃ p : Configuration S r, ∀ n, p ∉ Z n) ∧
        ∀ p : Configuration S r, (∀ n, p ∉ Z n) → ∀ C : IntegralCurve S,
          Real.sqrt ((selfIntersection S L:ℝ)/r)*(totalMultiplicity S r C p:ℝ) ≤
            (curveDegree S L C:ℝ) := by
  obtain ⟨U,eL,r₀,hr₀,h⟩ := S.eventual_very_general_interpolation L hL
  refine ⟨r₀,hr₀,fun r hr => ?_⟩
  obtain ⟨Z,hZ,hne,ht⟩ := h r hr
  exact ⟨Z,hZ,hne,fun p hp C => curve_lower_of_homogeneous_section_test S L hL
    (hr₀.trans_le hr) p U eL (ht p hp) C⟩
end
end MaximalSeshadri.Geometry

end

end OAI
