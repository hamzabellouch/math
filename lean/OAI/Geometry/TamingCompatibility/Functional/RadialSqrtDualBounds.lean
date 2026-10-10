import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.RadialCutoffSupported
import OAI.Geometry.TamingCompatibility.Functional.RadialEnergyDual

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix MeasureTheory EuclideanSobolevOperators RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in

theorem scalarEnergyDual_sqrtSource_bound
    (p : A.centers) (τ : 𝓢(Space,ℝ))
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hτ : ∀ z ∈ K, τ z * coordinateWeight A p z = 1)
    (a : Space → ℝ) (V : Space → Space) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R) (haR : tsupport a ⊆ Metric.closedBall 0 R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b R ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 2) s, ∀ hsr : s ∈ Ioc (0:ℝ) R, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarEnergyDualLM A J α hs ht D p K hK hKD j
        (sqrtSourceSupported a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ C := by
  obtain ⟨c,hc,hbound⟩ := scalarEnergyDualLM_scaled_bound A J α hs ht D hD p τ K hK hKD hτ
  obtain ⟨E₀,hE₀,hinner⟩ := sqrtInnerSchwartz_uniform_inputs a (fun _ => 1) V ha contDiff_const hV hK₀ R 0
  obtain ⟨E₁,hE₁,hshell⟩ := sqrtShellSchwartz_uniform_inputs a (fun _ => 1) V ha contDiff_const hV hK₀ R 0
  refine ⟨125*c*(E₀+8*E₁)*R^3,by positivity,?_⟩
  intro j s hsr b hb
  have hs0 : 0 < s := hsr.1
  obtain ⟨N,hN,hN2,hmin⟩ := exists_minimal_dyadic_scale hsr.1 hsr.2
  let L := scalarEnergyDualLM A J α hs ht D p K hK hKD j
  have h₀ : ‖L (sqrtInnerSupported a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ 125*c*E₀*s^3 := by
    have h := hbound j (sqrtInnerSupported a V ha hV R haR K hsr.1 b (hcenters b hb))
      b (5*s) E₀ (by positivity) (by positivity)
      ((shiftedSqrtInner_support a V hsr.1 b).trans
        (Metric.closedBall_subset_ball (by linarith [hsr.1] : 2*s < 5*s)))
      (hinner s hsr b hb).1
    apply h.trans_eq
    ring
  have h₁ : ∀ k < N,
      ‖L (sqrtShellSupported a V ha hV R haR K (mul_pos hsr.1 (by positivity : 0 < (2:ℝ)^k))
        hsr.1 b (hcenters b hb))‖ ≤ 125*c*E₁*(s*2^k)^3 := by
    intro k hk
    have hr : s*2^k ∈ Ioc (0:ℝ) R := ⟨by positivity,(hmin k hk).le⟩
    have hr0 : 0 < s*2^k := hr.1
    have hsr' : s ∈ Ioc (0:ℝ) (s*2^k) := ⟨hsr.1,by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := k)]⟩
    have h := hbound j (sqrtShellSupported a V ha hV R haR K hr.1 hsr.1 b (hcenters b hb))
      b (5*(s*2^k)) E₁ (by positivity) (by positivity)
      ((shiftedSqrtShell_support a V hr.1 s b).trans
        (Metric.closedBall_subset_ball (by linarith [hr.1] : 4*(s*2^k) < 5*(s*2^k))))
      (hshell (s*2^k) hr s hsr' b hb).1
    apply h.trans_eq
    ring
  change ‖L _‖ ≤ _
  rw [sqrtSupported_reconstruction a V ha hV R haR K hsr.1 b (hcenters b hb) N hN,map_add,map_sum]
  apply (norm_add_le (L (sqrtInnerSupported a V ha hV R haR K hsr.1 b (hcenters b hb))) _).trans
  apply (add_le_add h₀ ((norm_sum_le (Finset.range N) (fun k => L (sqrtShellSupported a V ha hV R haR K
    (mul_pos hs0 (by positivity : 0 < (2:ℝ)^k)) hs0 b (hcenters b hb)))).trans (Finset.sum_le_sum
    (fun k hk => h₁ k (Finset.mem_range.mp hk))))).trans
  rw [← Finset.mul_sum]
  have hi : s^3 ≤ R^3 := pow_le_pow_left₀ hs0.le hsr.2 3
  have ht' : (s*2^N)^3 ≤ (2*R)^3 := pow_le_pow_left₀ (by positivity) hN2 3
  have hsum := (sum_dyadic_cube_le hsr.1.le N).trans ht'
  calc
    _ ≤ 125*c*E₀*R^3 + 125*c*E₁*(2*R)^3 := by gcongr
    _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix MeasureTheory EuclideanSobolevOperators RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in

theorem scalarEnergyDual_logError_bound
    (p : A.centers) (τ : 𝓢(Space,ℝ))
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hτ : ∀ z ∈ K, τ z * coordinateWeight A p z = 1)
    (V : Space → Space) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R) (S : ℝ)
    (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 2) s, ∀ _hsr : s ∈ Icc (0:ℝ) S, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarEnergyDualLM A J α hs ht D p K hK hKD j
        (logErrorSupported V hV hR K s b (hcenters b hb))‖ ≤ C := by
  obtain ⟨c,hc,hbound⟩ := scalarEnergyDualLM_scaled_bound A J α hs ht D hD p τ K hK hKD hτ
  obtain ⟨E,hE,hinput⟩ := logErrorSchwartz_uniform_inputs V hV hR
    (fun _ => 1) contDiff_const hK₀ S 0
  refine ⟨c*E*(3*R)^3,by positivity,?_⟩
  intro j s hsr b hb
  exact hbound j (logErrorSupported V hV hR K s b (hcenters b hb)) b (3*R) E
    (by positivity) hE
    ((shiftedLogError_support V hR s b).trans
      (Metric.closedBall_subset_ball (by linarith : 2*R < 3*R)))
    (hinput s hsr b hb).1

include hD in

theorem scalarEnergyDual_cutoffLog_bound
    (p : A.centers) (τ : 𝓢(Space,ℝ))
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hτ : ∀ z ∈ K, τ z * coordinateWeight A p z = 1)
    (V : Space → Space) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 2) s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarEnergyDualLM A J α hs ht D p K hK hKD j
        (logCutoffSourceSupported V hV hR hsr.1 K b (hcenters b hb))‖ ≤ C := by
  obtain ⟨C₀,hC₀,hsource⟩ := scalarEnergyDual_logSource_bound A J α hs ht D hD
    p τ K hK hKD hτ (scaledCutoff R) V (scaledCutoff_smooth R) hV (2*R)
    (by positivity) (scaledCutoff_tsupport hR) K₀ hK₀ hcenters
  obtain ⟨C₁,hC₁,herror⟩ := scalarEnergyDual_logError_bound A J α hs ht D hD
    p τ K hK hKD hτ V hV R hR (2*R) K₀ hK₀ hcenters
  refine ⟨C₀+C₁,add_nonneg hC₀ hC₁,?_⟩
  intro j s hsr b hb
  rw [logCutoffSourceSupported_eq,map_add]
  exact (norm_add_le
    (scalarEnergyDualLM A J α hs ht D p K hK hKD j
      (logSourceSupported (scaledCutoff R) V (scaledCutoff_smooth R) hV
        (2*R) (scaledCutoff_tsupport hR) K hsr.1 b (hcenters b hb))) _).trans
    (add_le_add (hsource j s hsr b hb) (herror j s ⟨hsr.1.le,hsr.2⟩ b hb))

include hD in

theorem scalarEnergyDual_sqrtError_bound
    (p : A.centers) (τ : 𝓢(Space,ℝ))
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hτ : ∀ z ∈ K, τ z * coordinateWeight A p z = 1)
    (V : Space → Space) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R) (S : ℝ)
    (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 2) s, ∀ _hsr : s ∈ Icc (0:ℝ) S, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarEnergyDualLM A J α hs ht D p K hK hKD j
        (sqrtErrorSupported V hV hR K s b (hcenters b hb))‖ ≤ C := by
  obtain ⟨c,hc,hbound⟩ := scalarEnergyDualLM_scaled_bound A J α hs ht D hD p τ K hK hKD hτ
  obtain ⟨E,hE,hinput⟩ := sqrtErrorSchwartz_uniform_inputs V hV hR
    (fun _ => 1) contDiff_const hK₀ S 0
  refine ⟨c*E*(3*R)^3,by positivity,?_⟩
  intro j s hsr b hb
  exact hbound j (sqrtErrorSupported V hV hR K s b (hcenters b hb)) b (3*R) E
    (by positivity) hE
    ((shiftedSqrtError_support V hR s b).trans
      (Metric.closedBall_subset_ball (by linarith : 2*R < 3*R)))
    (hinput s hsr b hb).1

include hD in

theorem scalarEnergyDual_cutoffSqrt_bound
    (p : A.centers) (τ : 𝓢(Space,ℝ))
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hτ : ∀ z ∈ K, τ z * coordinateWeight A p z = 1)
    (V : Space → Space) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 2) s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarEnergyDualLM A J α hs ht D p K hK hKD j
        (sqrtCutoffSourceSupported V hV hR hsr.1 K b (hcenters b hb))‖ ≤ C := by
  obtain ⟨C₀,hC₀,hsource⟩ := scalarEnergyDual_sqrtSource_bound A J α hs ht D hD
    p τ K hK hKD hτ (scaledCutoff R) V (scaledCutoff_smooth R) hV (2*R)
    (by positivity) (scaledCutoff_tsupport hR) K₀ hK₀ hcenters
  obtain ⟨C₁,hC₁,herror⟩ := scalarEnergyDual_sqrtError_bound A J α hs ht D hD
    p τ K hK hKD hτ V hV R hR (2*R) K₀ hK₀ hcenters
  refine ⟨C₀+C₁,add_nonneg hC₀ hC₁,?_⟩
  intro j s hsr b hb
  rw [sqrtCutoffSourceSupported_eq,map_add]
  exact (norm_add_le
    (scalarEnergyDualLM A J α hs ht D p K hK hKD j
      (sqrtSourceSupported (scaledCutoff R) V (scaledCutoff_smooth R) hV
        (2*R) (scaledCutoff_tsupport hR) K hsr.1 b (hcenters b hb))) _).trans
    (add_le_add (hsource j s hsr b hb) (herror j s ⟨hsr.1.le,hsr.2⟩ b hb))

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
