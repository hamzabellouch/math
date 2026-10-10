import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.InverseEndpointCoefficient

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set MeasureTheory
open scoped ComplexConjugate Topology ContDiff
variable {n : ℕ} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
local notation "V" => EuclideanSpace ℝ (Fin (n+1))
local notation "Assignment" => ℂ × ((ι ⊕ κ) → List (SphereAmbientND n →L[ℝ] SphereAmbientND n))

noncomputable def pairMaskProductND (S : Finset ι) (T : Finset κ)
    (f : V → ι → SmoothFunctionND V) (g : V → κ → SmoothFunctionND V)
    (z : V × V) : SmoothFunctionND V :=
  smoothFinsetProductND (S.disjSum T) (Sum.elim (f z.1) (fun k => smoothStarND (g z.2 k)))

noncomputable def inverseEndpointMixtureND (j : ℕ) (S : Finset ι) (T : Finset κ)
    (f : V → ι → SmoothFunctionND V) (g : V → κ → SmoothFunctionND V)
    (F G : V → ℂ) (D : ι → ℝ) (E : κ → ℝ)
    (δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K) (scale : ℝ)
    (ρ ν : Measure V) (X Y : Set V) (M N r : ℝ) (ψ : V → ℂ) : ℂ :=
  ((inverseAngularTermsND j (S.disjSum T)).map (fun a =>
    inverseEndpointCoefficientND S T D E a *
      ∫ ξ, SpatialFourierND.spatialFourierCoeff (n+1) δ K hδ hK j ξ *
        ∫ w, ψ w*sourceAngularTransformND ρ X M
          (fun x w => SpatialFourierND.spatialFourierPhase (n+1) scale ξ x*
            inverseLeftEndpointND S D f F a x w) r w *
          conj (sourceAngularTransformND ν Y N
            (fun y w => SpatialFourierND.spatialFourierPhase (n+1) scale ξ y*
              inverseRightEndpointND T E g G a y w) r w)
                ∂canonicalSphereMeasureND V)).sum

lemma inverse_pair_term_integrableND (j : ℕ) (S : Finset ι) (T : Finset κ)
    (f : V → ι → SmoothFunctionND V) (g : V → κ → SmoothFunctionND V)
    (F G : V → ℂ) (D : ι → ℝ) (E : κ → ℝ)
    (hD : ∀ i ∈ S, D i ≠ 0) (hE : ∀ k ∈ T, E k ≠ 0)
    (δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K) {s : ℝ} (hs : 0 < s)
    (μ : Measure (V × V)) [IsFiniteMeasure μ] (r : ℝ)
    (hsep : ∀ᵐ z ∂μ, δ ≤ dist z.1 z.2*s ∧ dist z.1 z.2*s ≤ K)
    (ψ : V → ℂ) (hψ : Continuous ψ) {P : ℝ} (hP : ∀ w, ‖ψ w‖ ≤ P)
    (B C : Assignment → ℝ)
    (hb : ∀ a ∈ inverseAngularTermsND j (S.disjSum T),
      Measurable (Function.uncurry (inverseLeftEndpointND S D f F a)))
    (hc : ∀ a ∈ inverseAngularTermsND j (S.disjSum T),
      Measurable (Function.uncurry (inverseRightEndpointND T E g G a)))
    (hB : ∀ a ∈ inverseAngularTermsND j (S.disjSum T), ∀ x w,
      ‖inverseLeftEndpointND S D f F a x w‖ ≤ B a)
    (hC : ∀ a ∈ inverseAngularTermsND j (S.disjSum T), ∀ y w,
      ‖inverseRightEndpointND T E g G a y w‖ ≤ C a) :
    Integrable (fun z => (F z.1*conj (G z.2))*
      inverseResidualKernelND j r s ψ (pairMaskProductND S T f g) z) μ := by
  let L := inverseAngularTermsND (n := n) j (S.disjSum T)
  have hi := integrable_list_sumND μ L (fun a z =>
    inverseEndpointCoefficientND S T D E a *
      (SpatialFourierND.spatialAnnulusKernel (n+1) δ K hδ hK j (s • (z.1-z.2)) *
        ∫ w, ψ w*spherePlaneWaveND r (z.1-z.2) w*
          inverseLeftEndpointND S D f F a z.1 w*conj (inverseRightEndpointND T E g G a z.2 w)
            ∂canonicalSphereMeasureND V)) (by
      intro a ha
      simpa only [inv_inv] using (spatial_angular_term_integrableND δ K hδ hK j s⁻¹
        (canonicalSphereMeasureND V) μ r hψ.measurable (hb a ha) (hc a ha)
        hP (hB a ha) (hC a ha)).const_mul (inverseEndpointCoefficientND S T D E a))
  apply hi.congr
  filter_upwards [hsep] with z hz
  have hd := inverse_distance_annulus_kernelND δ K hδ hK j (inv_pos.mpr hs)
    (x := z.1) (y := z.2) (by simpa only [div_inv_eq_mul] using hz.1)
    (by simpa only [div_inv_eq_mul] using hz.2)
  simp only [div_inv_eq_mul,inv_inv] at hd
  dsimp [inverseResidualKernelND,pairMaskProductND]
  rw [mul_left_comm,hd,euclideanAxisInverse_endpoints_spatialND j S T f g F G D E hD hE r z.1 z.2 ψ hψ]
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  ring

theorem all_mask_weighted_inverseND (ψ : V → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (η T₀ C₀ : ℝ) (hη : 0 < η) (hC₀ : 0 ≤ C₀) :
    ∃ J : ℕ, ∃ Error : ℝ, 0 ≤ Error ∧ ∀
      (S : Finset ι) (T : Finset κ)
      (f : V → ι → SmoothFunctionND V) (g : V → κ → SmoothFunctionND V)
      (F G : V → ℂ) (D : ι → ℝ) (E : κ → ℝ),
      (∀ i ∈ S, D i ≠ 0) → (∀ k ∈ T, E k ≠ 0) → ∀
      (δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K)
      (ρ ν : Measure V) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
      (X Y : Set V), MeasurableSet X → MeasurableSet Y → ∀
      (M N R A r s : ℝ),
      0 < r → 0 < s → 1 ≤ R → 1 ≤ A → A ≤ R^2 →
      (∀ x ∈ X, ∀ y ∈ Y, δ ≤ dist x y*s ∧ dist x y*s ≤ K) →
      (∀ᵐ z ∂(ρ.restrict X).prod (ν.restrict Y),
        R^η ≤ r*dist z.1 z.2 ∧ A^2/(r*dist z.1 z.2) ≤ R^(-η) ∧
        ψ =ᶠ[𝓝 ((dist z.1 z.2)⁻¹ • (z.1-z.2))] (fun _ => 1) ∧
        ψ =ᶠ[𝓝 (-((dist z.1 z.2)⁻¹ • (z.1-z.2)))] (fun _ => 0) ∧
        (∀ k ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 →
          ‖iteratedFDeriv ℝ k (pairMaskProductND S T f g z).1 w‖ ≤ C₀*A^k)) →
      (∀ᵐ z ∂(ρ.restrict X).prod (ν.restrict Y), ‖F z.1*conj (G z.2)‖ ≤ 1) →
      Integrable (fun z => (F z.1*conj (G z.2))*
        outgoingWeightedKernelND r s (pairMaskProductND S T f g) z)
          ((ρ.restrict X).prod (ν.restrict Y)) →
      ∀ (P : ℝ), (∀ w, ‖ψ w‖ ≤ P) → ∀ (B C : ℕ → Assignment → ℝ),
      (∀ j ≤ J, ∀ a ∈ inverseAngularTermsND j (S.disjSum T),
        Measurable (Function.uncurry (inverseLeftEndpointND S D f F a))) →
      (∀ j ≤ J, ∀ a ∈ inverseAngularTermsND j (S.disjSum T),
        Measurable (Function.uncurry (inverseRightEndpointND T E g G a))) →
      (∀ j ≤ J, ∀ a ∈ inverseAngularTermsND j (S.disjSum T), ∀ x w,
        ‖inverseLeftEndpointND S D f F a x w‖ ≤ B j a) →
      (∀ j ≤ J, ∀ a ∈ inverseAngularTermsND j (S.disjSum T), ∀ y w,
        ‖inverseRightEndpointND T E g G a y w‖ ≤ C j a) →
      ‖((M*N)⁻¹:ℝ) • (∫ z, (F z.1*conj (G z.2))*
          outgoingWeightedKernelND r s (pairMaskProductND S T f g) z
            ∂(ρ.restrict X).prod (ν.restrict Y)) -
        (∑ j ∈ Finset.range (J+1),
          ((((r/s)^((n:ℝ)/2):ℝ):ℂ)*((r/s:ℝ):ℂ)^(-(j:ℤ))) *
            inverseEndpointMixtureND j S T f g F G D E δ K hδ hK s⁻¹ ρ ν X Y M N r ψ)‖ ≤
        |(M*N)⁻¹| * ((δ^(-(n:ℝ)/2)*Error*R^(-T₀))*
          ((ρ.restrict X).prod (ν.restrict Y)).real univ) := by
  obtain ⟨J,Error,hError,hInv⟩ := integrated_weighted_inverseND ψ hψ η T₀ C₀ hη hC₀
  refine ⟨J,Error,hError,?_⟩
  intro S T f g F G D E hD hE δ K hδ hK ρ ν hρ hν X Y hX hY M N R A r s
    hr hs hR hA hup hsep hgeom hFG hraw P hP B C hb hc hB hC
  let μ := (ρ.restrict X).prod (ν.restrict Y)
  have hxy : ∀ᵐ z ∂μ, z.1 ∈ X ∧ z.2 ∈ Y :=
    (Measure.ae_prod_iff_ae_ae (hX.prod hY)).mpr (by
      filter_upwards [ae_restrict_mem hX] with x hx
      filter_upwards [ae_restrict_mem hY] with y hy
      exact ⟨hx,hy⟩)
  have hsep' : ∀ᵐ z ∂μ, δ ≤ dist z.1 z.2*s ∧ dist z.1 z.2*s ≤ K := by
    filter_upwards [hxy] with z hz
    exact hsep z.1 hz.1 z.2 hz.2
  have hi (j : ℕ) (hj : j ∈ Finset.range (J+1)) := inverse_pair_term_integrableND
    j S T f g F G D E hD hE δ K hδ hK hs μ r hsep' ψ hψ.continuous hP (B j) (C j)
      (hb j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      (hc j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      (hB j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      (hC j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
  have hg : ∀ᵐ z ∂μ, 0 < dist z.1 z.2 ∧ δ ≤ dist z.1 z.2*s ∧
      R^η ≤ r*dist z.1 z.2 ∧ A^2/(r*dist z.1 z.2) ≤ R^(-η) ∧
      ψ =ᶠ[𝓝 ((dist z.1 z.2)⁻¹ • (z.1-z.2))] (fun _ => 1) ∧
      ψ =ᶠ[𝓝 (-((dist z.1 z.2)⁻¹ • (z.1-z.2)))] (fun _ => 0) ∧
      (∀ k ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ k (pairMaskProductND S T f g z).1 w‖ ≤ C₀*A^k) := by
    filter_upwards [hsep',hgeom] with z hz hg
    have hdz : 0 < dist z.1 z.2 := (mul_pos_iff_of_pos_right hs).mp (hδ.trans_le hz.1)
    exact ⟨hdz,hz.1,hg⟩
  have hh := hInv μ (pairMaskProductND S T f g) (fun z => F z.1*conj (G z.2))
    R A r s δ hr hs hδ hR hA hup hg hFG hraw hi
  have he (j : ℕ) (hj : j ∈ Finset.range (J+1)) :
      ((M*N)⁻¹:ℝ) • (∫ z, (F z.1*conj (G z.2))*
        inverseResidualKernelND j r s ψ (pairMaskProductND S T f g) z ∂μ) =
      inverseEndpointMixtureND j S T f g F G D E δ K hδ hK s⁻¹ ρ ν X Y M N r ψ := by
    have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    convert integrated_inverse_endpoint_termND j S T f g F G D E hD hE δ K hδ hK
      (inv_pos.mpr hs) ρ ν hX hY M N r (by
        intro x hx y hy
        simpa only [div_inv_eq_mul] using hsep x hx y hy)
      ψ hψ.continuous hP (B j) (C j) (hb j hj') (hc j hj') (hB j hj') (hC j hj') using 1
    · simp only [inverseResidualKernelND,pairMaskProductND,div_inv_eq_mul]
      congr 1
      apply integral_congr_ae
      filter_upwards with z
      ring
    · rfl
  have hmul := mul_le_mul_of_nonneg_left hh (abs_nonneg ((M*N)⁻¹))
  rw [← Real.norm_eq_abs,← norm_smul] at hmul
  rw [smul_sub,Finset.smul_sum] at hmul
  have heq : ((∑ j ∈ Finset.range (J+1), ((M*N)⁻¹:ℝ) •
      (((((r/s)^((n:ℝ)/2):ℝ):ℂ)*((r/s:ℝ):ℂ)^(-(j:ℤ))) *
        (∫ z, (F z.1*conj (G z.2))*inverseResidualKernelND j r s ψ
          (pairMaskProductND S T f g) z ∂μ)))) =
      (∑ j ∈ Finset.range (J+1),
        ((((r/s)^((n:ℝ)/2):ℝ):ℂ)*((r/s:ℝ):ℂ)^(-(j:ℤ))) *
          inverseEndpointMixtureND j S T f g F G D E δ K hδ hK s⁻¹ ρ ν X Y M N r ψ) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [← mul_smul_comm,he j hj]
  simpa only [heq,Real.norm_eq_abs] using hmul

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
