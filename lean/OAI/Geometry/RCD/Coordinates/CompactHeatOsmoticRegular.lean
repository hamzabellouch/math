import OAI.Geometry.RCD.Coordinates.BoundedHeatLogRegular
import OAI.Geometry.RCD.Heat.CompactHeatOsmoticGradient

namespace OAI

/-! # Bounded regular representatives of the actual osmotic potential -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2≤n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0<ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem osmotic_regular
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0≤ρ₀ x) (hp₁ : ∀ x, 0≤ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x|≤C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x|≤C₁)
    (hμ : μ.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (k : ℕ) (t : Ioo (0:ℝ) 1) {Ω : Set X} (hΩ : IsCompact Ω) :
    ∃ (η : SobolevSpace (hausdorff n X) hX.quadratic) (q : Lp ℝ 2 (hausdorff n X))
      (V : X → ℝ) (L B : ℝ≥0),
      IsWeakLaplacian (hausdorff n X) hX.quadratic η q ∧ LipschitzWith L V ∧
      (∀ x, |V x|≤B) ∧ (SobolevSpace.toLp (hausdorff n X) hX.quadratic η =ᵐ[hausdorff n X] V) ∧
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic η
        =ᵐ[(hausdorff n X).restrict Ω] D.osmoticPotential k t) := by
  let m := hausdorff n X
  let Q := hX.quadratic
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  let c : ℝ≥0 := ⟨ε k/4,(div_pos (hε k) (by norm_num)).le⟩
  have hc : 0<(c:ℝ) := div_pos (hε k) (by norm_num)
  have hs : 0<(c:ℝ)*(t:ℝ) := mul_pos hc t.property.1
  have ht : 0<(c:ℝ)*(1-t) := mul_pos hc (sub_pos.mpr t.property.2)
  obtain ⟨f,A,-,hf,hef⟩ := hX.compact_heat_factor_nonnegative_L2 hn p μ ρ₀ hm₀ hp₀ hC₀ hμ
    (D.left k) (fun a => (D.left_pos k a).le)
  obtain ⟨g,B,-,hg,heg⟩ := hX.compact_heat_factor_nonnegative_L2 hn p ν ρ₁ hm₁ hp₁ hC₁ hν
    (D.right k) (fun a => (D.right_pos k a).le)
  have hpf : ∀ x∈Ω, 0<kernelHeat m Q hk ((c:ℝ)*t) f x := by
    intro x _
    rw [← hef _ hs x]
    exact hX.compactHeatFactor_positive hn p μ (D.left k) (D.left_pos k) _ hs x
  have hpg : ∀ x∈Ω, 0<kernelHeat m Q hk ((c:ℝ)*(1-t)) g x := by
    intro x _
    rw [← heg _ ht x]
    exact hX.compactHeatFactor_positive hn p ν (D.right k) (D.right_pos k) _ ht x
  obtain ⟨u,du,U,L,A',hdu,hU,hUA,hu,hur⟩ := hX.bounded_heat_log_regular hn p f A hf hs hΩ hpf
  obtain ⟨v,dv,V,M,B',hdv,hV,hVB,hv,hvr⟩ := hX.bounded_heat_log_regular hn p g B hg ht hΩ hpg
  let η := (c:ℝ) • (u+v)
  have hrep : SobolevSpace.toLp m Q η =ᵐ[m] fun x => (c:ℝ)*(U x+V x) := by
    filter_upwards [hu,hv,Lp.coeFn_add (SobolevSpace.toLp m Q u) (SobolevSpace.toLp m Q v),
      Lp.coeFn_smul (c:ℝ) (SobolevSpace.toLp m Q (u+v))] with x hux hvx ha hm
    change SobolevSpace.toLp m Q η x=(c:ℝ)*SobolevSpace.toLp m Q (u+v) x at hm
    change SobolevSpace.toLp m Q u x=U x at hux
    change SobolevSpace.toLp m Q v x=V x at hvx
    rw [hm]
    simp only [map_add]
    rw [ha]
    simp only [Pi.add_apply]
    rw [hux,hvx]
  refine ⟨η,(c:ℝ) • (du+dv),fun x => (c:ℝ)*(U x+V x),‖(c:ℝ)‖₊*(L+M),c*(A'+B'),
    ((hdu.add m Q hdv).smul m Q (c:ℝ)),?_,?_,hrep,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have hh := mul_le_mul_of_nonneg_left ((hU.add hV).dist_le_mul x y) (abs_nonneg (c:ℝ))
    simpa only [Real.dist_eq,← mul_sub,abs_mul,NNReal.coe_mul,coe_nnnorm,
      Real.norm_eq_abs,mul_assoc] using hh
  · intro x
    rw [abs_mul,abs_of_nonneg c.coe_nonneg]
    exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add (hUA x) (hVB x))) c.coe_nonneg
  · filter_upwards [hur,hvr,ae_restrict_of_ae hrep,ae_restrict_of_ae hu,ae_restrict_of_ae hv]
      with x hux hvx he hu' hv'
    rw [he,← hu',← hv',hux,hvx,← hef _ hs x,← heg _ ht x]
    dsimp only [osmoticPotential,interpolationDensity]
    rw [Real.log_mul
      (hX.compactHeatFactor_positive hn p μ (D.left k) (D.left_pos k) _ _ x).ne'
      (hX.compactHeatFactor_positive hn p ν (D.right k) (D.right_pos k) _ _ x).ne']
    rfl

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
