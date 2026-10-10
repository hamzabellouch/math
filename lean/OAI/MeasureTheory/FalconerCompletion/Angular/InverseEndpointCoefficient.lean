import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.IntegrableListSum
import OAI.MeasureTheory.FalconerCompletion.Graphs.SmoothEval
import OAI.MeasureTheory.FalconerCompletion.Sphere.InverseWeightCancellation

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open MeasureTheory Set
open scoped ComplexConjugate
variable {n : ℕ} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
local notation "V" => EuclideanSpace ℝ (Fin (n+1))
local notation "Assignment" => ℂ × ((ι ⊕ κ) → List (SphereAmbientND n →L[ℝ] SphereAmbientND n))

noncomputable def inverseEndpointCoefficientND (S : Finset ι) (T : Finset κ)
    (D : ι → ℝ) (E : κ → ℝ) (a : Assignment) : ℂ :=
  a.1 * (((∏ i ∈ S, D i^(a.2 (Sum.inl i)).length) *
    (∏ k ∈ T, E k^(a.2 (Sum.inr k)).length):ℝ):ℂ)

noncomputable def inverseLeftEndpointND (S : Finset ι) (D : ι → ℝ)
    (f : V → ι → SmoothFunctionND V) (F : V → ℂ) (a : Assignment) (x w : V) : ℂ :=
  F x * ∏ i ∈ S, (euclideanAngularWordND (D i) (a.2 (Sum.inl i)) (f x i)).1 w

noncomputable def inverseRightEndpointND (T : Finset κ) (E : κ → ℝ)
    (g : V → κ → SmoothFunctionND V) (G : V → ℂ) (a : Assignment) (y w : V) : ℂ :=
  G y * ∏ k ∈ T, (euclideanAngularWordND (E k) (a.2 (Sum.inr k)) (g y k)).1 w

lemma euclideanAxisInverse_endpoints_spatialND (j : ℕ) (S : Finset ι) (T : Finset κ)
    (f : V → ι → SmoothFunctionND V) (g : V → κ → SmoothFunctionND V)
    (F G : V → ℂ) (D : ι → ℝ) (E : κ → ℝ)
    (hD : ∀ i ∈ S, D i ≠ 0) (hE : ∀ k ∈ T, E k ≠ 0)
    (r : ℝ) (x y : V) (ψ : V → ℂ) (hψ : Continuous ψ) :
    F x*conj (G y) * sphereAxisIntegralND r (x-y) (fun w =>
      ψ w*(euclideanSphereBND j (smoothFinsetProductND (S.disjSum T)
        (Sum.elim (f x) (fun k => smoothStarND (g y k))))).1 w) =
      ((inverseAngularTermsND j (S.disjSum T)).map (fun a =>
        inverseEndpointCoefficientND S T D E a *
          ∫ w, ψ w*spherePlaneWaveND r (x-y) w*
            inverseLeftEndpointND S D f F a x w*conj (inverseRightEndpointND T E g G a y w)
              ∂canonicalSphereMeasureND V)).sum := by
  rw [euclideanAxisInverse_endpointsND j S T (f x) (g y) D E hD hE r (x-y) ψ hψ,
    ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  dsimp only [inverseEndpointCoefficientND]
  rw [mul_left_comm]
  congr 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with w
  simp only [inverseLeftEndpointND,inverseRightEndpointND,map_mul]
  ring

lemma inverse_distance_annulus_kernelND (δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K)
    (j : ℕ) {scale : ℝ} (hs : 0 < scale) {x y : V}
    (hl : δ ≤ dist x y / scale) (hu : dist x y / scale ≤ K) :
    ((dist x y/scale:ℝ):ℂ)^(-(j:ℤ)) =
      SpatialFourierND.spatialAnnulusKernel (n+1) δ K hδ hK j (scale⁻¹ • (x-y)) := by
  have hn : ‖scale⁻¹ • (x-y)‖ = dist x y / scale := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hs,← dist_eq_norm,div_eq_inv_mul]
  rw [SpatialFourierND.spatialAnnulusKernel_eq _ δ K hδ hK j (by rwa [hn]) (by rwa [hn]),hn]
  simp only [zpow_neg,zpow_natCast,Complex.ofReal_inv,Complex.ofReal_pow]

theorem integrated_inverse_endpoint_termND (j : ℕ) (S : Finset ι) (T : Finset κ)
    (f : V → ι → SmoothFunctionND V) (g : V → κ → SmoothFunctionND V)
    (F G : V → ℂ) (D : ι → ℝ) (E : κ → ℝ)
    (hD : ∀ i ∈ S, D i ≠ 0) (hE : ∀ k ∈ T, E k ≠ 0)
    (δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K) {scale : ℝ} (hs : 0 < scale)
    (ρ ν : Measure V) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    {X Y : Set V} (hX : MeasurableSet X) (hY : MeasurableSet Y) (M N r : ℝ)
    (hsep : ∀ x ∈ X, ∀ y ∈ Y, δ ≤ dist x y/scale ∧ dist x y/scale ≤ K)
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
    ((M*N)⁻¹:ℝ) • (∫ z : V × V,
      ((dist z.1 z.2/scale:ℝ):ℂ)^(-(j:ℤ)) * (F z.1*conj (G z.2) *
        sphereAxisIntegralND r (z.1-z.2) (fun w => ψ w*
          (euclideanSphereBND j (smoothFinsetProductND (S.disjSum T)
            (Sum.elim (f z.1) (fun k => smoothStarND (g z.2 k))))).1 w))
              ∂(ρ.restrict X).prod (ν.restrict Y)) =
    ((inverseAngularTermsND j (S.disjSum T)).map (fun a =>
      inverseEndpointCoefficientND S T D E a *
        ∫ ξ, SpatialFourierND.spatialFourierCoeff (n+1) δ K hδ hK j ξ *
          ∫ w, ψ w*sourceAngularTransformND ρ X M
            (fun x w => SpatialFourierND.spatialFourierPhase (n+1) scale ξ x*
              inverseLeftEndpointND S D f F a x w) r w *
            conj (sourceAngularTransformND ν Y N
              (fun y w => SpatialFourierND.spatialFourierPhase (n+1) scale ξ y*
                inverseRightEndpointND T E g G a y w) r w)
                  ∂canonicalSphereMeasureND V)).sum := by
  rw [← finite_spatial_angular_factorizationND (inverseAngularTermsND j (S.disjSum T))
    δ K hδ hK j scale (canonicalSphereMeasureND V) ρ ν X Y M N r
    (inverseEndpointCoefficientND S T D E) hψ.measurable hb hc hP hB hC]
  congr 1
  apply integral_congr_ae
  have hm : ∀ᵐ z ∂(ρ.restrict X).prod (ν.restrict Y), z.1 ∈ X ∧ z.2 ∈ Y := by
    exact (Measure.ae_prod_iff_ae_ae (hX.prod hY)).mpr (by
      filter_upwards [ae_restrict_mem hX] with x hx
      filter_upwards [ae_restrict_mem hY] with y hy
      exact ⟨hx,hy⟩)
  filter_upwards [hm] with z hz
  rw [inverse_distance_annulus_kernelND δ K hδ hK j hs (hsep z.1 hz.1 z.2 hz.2).1
    (hsep z.1 hz.1 z.2 hz.2).2,
    euclideanAxisInverse_endpoints_spatialND j S T f g F G D E hD hE r z.1 z.2 ψ hψ,
    ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  exact mul_left_comm _ _ _
end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set MeasureTheory
open scoped ContDiff Topology

lemma integral_finset_remainderND {Z Q : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsFiniteMeasure μ] (S : Finset Q) (f : Z → ℂ) (g : Q → Z → ℂ)
    (c : Q → ℂ) (hf : Integrable f μ) (hg : ∀ i ∈ S, Integrable (g i) μ) {E : ℝ}
    (hb : ∀ᵐ z ∂μ, ‖f z-∑ i ∈ S, c i*g i z‖ ≤ E) :
    ‖(∫ z, f z ∂μ)-∑ i ∈ S, c i*(∫ z, g i z ∂μ)‖ ≤ E*μ.real univ := by
  have hi := integrable_finsetSum S (fun i hi => (hg i hi).const_mul (c i))
  have he : (∫ z, (∑ i ∈ S, c i*g i z) ∂μ)=∑ i ∈ S, c i*(∫ z, g i z ∂μ) := by
    rw [integral_finsetSum S (fun i hi => (hg i hi).const_mul (c i))]
    simp only [integral_const_mul]
  rw [← he,← integral_sub hf hi]
  exact norm_integral_le_of_norm_le_const hb

lemma scalar_finset_remainderND {Q : Type*} (S : Finset Q) (f a c : ℂ) (p g : Q → ℂ) :
    c*f-(∑ i ∈ S, (a*p i)*(c*g i)) = c*(f-a*(∑ i ∈ S, p i*g i)) := by
  rw [mul_sub]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin (n+1))

noncomputable def outgoingWeightedKernelND (r s : ℝ)
    (b : V × V → SmoothFunctionND V) (z : V × V) : ℂ :=
  (((dist z.1 z.2*s)^(-(n:ℝ)/2):ℝ):ℂ) *
    (Complex.exp (Complex.I*(r*dist z.1 z.2)) * (b z).1 ((dist z.1 z.2)⁻¹ • (z.1-z.2)))

noncomputable def inverseResidualKernelND (j : ℕ) (r s : ℝ) (ψ : V → ℂ)
    (b : V × V → SmoothFunctionND V) (z : V × V) : ℂ :=
  ((dist z.1 z.2*s:ℝ):ℂ)^(-(j:ℤ)) *
    sphereAxisIntegralND r (z.1-z.2) (fun w => ψ w*(euclideanSphereBND j (b z)).1 w)

theorem integrated_weighted_inverseND (ψ : V → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (κ T C : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C) :
    ∃ J : ℕ, ∃ E : ℝ, 0 ≤ E ∧ ∀ (μ : Measure (V × V)) [IsFiniteMeasure μ]
      (b : V × V → SmoothFunctionND V) (c : V × V → ℂ) (R A r s δ : ℝ),
      0 < r → 0 < s → 0 < δ → 1 ≤ R → 1 ≤ A → A ≤ R^2 →
      (∀ᵐ z ∂μ, 0 < dist z.1 z.2 ∧ δ ≤ dist z.1 z.2*s ∧
        R^κ ≤ r*dist z.1 z.2 ∧ A^2/(r*dist z.1 z.2) ≤ R^(-κ) ∧
        ψ =ᶠ[𝓝 ((dist z.1 z.2)⁻¹ • (z.1-z.2))] (fun _ => 1) ∧
        ψ =ᶠ[𝓝 (-((dist z.1 z.2)⁻¹ • (z.1-z.2)))] (fun _ => 0) ∧
        (∀ k ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ k (b z).1 w‖ ≤ C*A^k)) →
      (∀ᵐ z ∂μ, ‖c z‖ ≤ 1) →
      Integrable (fun z => c z*outgoingWeightedKernelND r s b z) μ →
      (∀ j ∈ Finset.range (J+1), Integrable (fun z => c z*inverseResidualKernelND j r s ψ b z) μ) →
      ‖(∫ z, c z*outgoingWeightedKernelND r s b z ∂μ) -
        (∑ j ∈ Finset.range (J+1),
          ((((r/s)^((n:ℝ)/2):ℝ):ℂ)*((r/s:ℝ):ℂ)^(-(j:ℤ))) *
          (∫ z, c z*inverseResidualKernelND j r s ψ b z ∂μ))‖ ≤
        (δ^(-(n:ℝ)/2)*E*R^(-T))*μ.real univ := by
  obtain ⟨J,E,hE,hEb⟩ := weighted_euclidean_inverseND ψ hψ κ T C hκ hC
  refine ⟨J,E,hE,?_⟩
  intro μ hμ b c R A r s δ hr hs hδ hR hA hup hgeom hc hraw hterms
  apply integral_finset_remainderND μ (Finset.range (J+1)) _ _ _ hraw hterms
  filter_upwards [hgeom,hc] with z hz hcz
  obtain ⟨hD,hδD,hΛ,hratio,hplus,hminus,hb⟩ := hz
  have hh := hEb (b z) R A r s z.1 z.2 hD hr hs hR hA hΛ hup hratio hplus hminus hb
  have hW : (dist z.1 z.2*s)^(-(n:ℝ)/2) ≤ δ^(-(n:ℝ)/2) :=
    Real.rpow_le_rpow_of_nonpos hδ hδD (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (by norm_num))
  have hbound : ‖outgoingWeightedKernelND r s b z -
      ((((r/s)^((n:ℝ)/2):ℝ):ℂ) * (∑ j ∈ Finset.range (J+1),
        ((r/s:ℝ):ℂ)^(-(j:ℤ)) * inverseResidualKernelND j r s ψ b z))‖ ≤
        δ^(-(n:ℝ)/2)*E*R^(-T) := by
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hW hE) (Real.rpow_nonneg (by linarith) _))
  rw [scalar_finset_remainderND,norm_mul]
  exact (mul_le_mul hcz hbound (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
