import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialMixedLogDyadic

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

def antiEnergyDualLM : antiPre A J α hs ht →ₗ[ℝ] StrongDual ℝ (antiEnergy A J α hs ht) where
  toFun f := (innerSL ℝ (smoothL2 A J α hs ht true f.val)).comp (energyInclusion A J α hs ht)
  map_add' f g := by ext u; simp
  map_smul' c f := by ext u; simp

def scalarEnergyDualLM (p : A.centers) (K : Set Space) (hK : IsCompact K)
    (hKD : K ⊆ (D p).domain) (j : Fin 2) :
    supportedSchwartz K →ₗ[ℝ] StrongDual ℝ (antiEnergy A J α hs ht) :=
  (antiEnergyDualLM A J α hs ht).comp (scalarTestLM A J α hs ht D p K hK hKD j)

include hD in

lemma scalarEnergyDualLM_scaled_bound
    (p : A.centers) (τ : 𝓢(Space,ℝ))
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hτ : ∀ z ∈ K, τ z * coordinateWeight A p z = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 2) (f : supportedSchwartz K)
      (b : Space) (r M : ℝ), 0 ≤ r → 0 ≤ M →
      tsupport f.val ⊆ Metric.ball b r → (∀ z, |f.val z| ≤ M) →
      ‖scalarEnergyDualLM A J α hs ht D p K hK hKD j f‖ ≤ C*M*r^3 := by
  obtain ⟨C,hC,hpair⟩ := critical_chart_pairing A J α hs ht D hD p τ hKD hτ
  obtain ⟨C',hC',hscale⟩ := densityTest_scale_bound A J α hs ht D p hK hKD
  refine ⟨C*C',mul_nonneg hC hC',?_⟩
  intro j f b r M hr hM hsupport hval
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hp := hpair f.val (supportedSchwartz_compact hK f) f.property j v
  have hg := hscale f.val (supportedSchwartz_compact hK f) f.property b r M hr hM hsupport hval
  change |⟪smoothL2 A J α hs ht true (scalarTestLM A J α hs ht D p K hK hKD j f).val,
    energyInclusion A J α hs ht v⟫| ≤ _
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hC) (norm_nonneg v)
  exact hp.trans (by nlinarith only [hb])

include hD in
lemma harmonic_seminorm_dual_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : antiPre A J α hs ht →ₗ[ℝ] F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f h : antiPre A J α hs ht,
      smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
        (smoothL2 A J α hs ht true f.val) →
      ‖L h‖ ≤ C*‖antiEnergyDualLM A J α hs ht f‖ := by
  obtain ⟨C,hC,hbound⟩ := harmonic_seminorm_bound A J α hs ht D hD L
  refine ⟨C,hC,fun f h hh => ?_⟩
  have hhh : smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
      (smoothL2 A J α hs ht true h.val) := by
    rw [hh,(harmonicAnti A J α hs ht).starProjection_eq_self_iff.mpr
      ((harmonicAnti A J α hs ht).starProjection_apply_mem _)]
  have hd := harmonicAnti_dual_bound A J α hs ht (smoothL2 A J α hs ht true f.val)
    ‖antiEnergyDualLM A J α hs ht f‖ (ContinuousLinearMap.opNorm_nonneg _) (fun v =>
      (antiEnergyDualLM A J α hs ht f).le_opNorm v)
  rw [← hh] at hd
  exact (hbound h h hhh).trans (mul_le_mul_of_nonneg_left hd hC)
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

theorem scalarEnergyDual_logSource_bound
    (p : A.centers) (τ : 𝓢(Space,ℝ))
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hτ : ∀ z ∈ K, τ z * coordinateWeight A p z = 1)
    (a : Space → ℝ) (V : Space → Space) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R) (haR : tsupport a ⊆ Metric.closedBall 0 R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b R ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 2) s, ∀ hsr : s ∈ Ioc (0:ℝ) R, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarEnergyDualLM A J α hs ht D p K hK hKD j
        (logSourceSupported a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ C := by
  obtain ⟨c,hc,hbound⟩ := scalarEnergyDualLM_scaled_bound A J α hs ht D hD p τ K hK hKD hτ
  obtain ⟨E₀,hE₀,hinner⟩ := logInnerSchwartz_uniform_inputs a (fun _ => 1) V ha contDiff_const hV hK₀ R 0
  obtain ⟨E₁,hE₁,hshell⟩ := logShellSchwartz_uniform_inputs a (fun _ => 1) V ha contDiff_const hV hK₀ R 0
  refine ⟨125*c*(E₀+4*E₁)*R^2,by positivity,?_⟩
  intro j s hsr b hb
  have hs0 : 0 < s := hsr.1
  obtain ⟨N,hN,hN2,hmin⟩ := exists_minimal_dyadic_scale hsr.1 hsr.2
  let L := scalarEnergyDualLM A J α hs ht D p K hK hKD j
  have h₀ : ‖L (logInnerSupported a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ 125*c*E₀*s^2 := by
    have h := hbound j (logInnerSupported a V ha hV R haR K hsr.1 b (hcenters b hb))
      b (5*s) (E₀/s) (by positivity) (by positivity)
      ((shiftedLogInner_support a V hsr.1 b).trans
        (Metric.closedBall_subset_ball (by linarith [hsr.1] : 2*s < 5*s)))
      (hinner s hsr b hb).1
    apply h.trans_eq
    field_simp [hsr.1.ne']
    ring
  have h₁ : ∀ k < N,
      ‖L (logShellSupported a V ha hV R haR K (mul_pos hsr.1 (by positivity : 0 < (2:ℝ)^k))
        hsr.1 b (hcenters b hb))‖ ≤ 125*c*E₁*(s*2^k)^2 := by
    intro k hk
    have hr : s*2^k ∈ Ioc (0:ℝ) R := ⟨by positivity,(hmin k hk).le⟩
    have hr0 : 0 < s*2^k := hr.1
    have hsr' : s ∈ Ioc (0:ℝ) (s*2^k) := ⟨hsr.1,by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := k)]⟩
    have h := hbound j (logShellSupported a V ha hV R haR K hr.1 hsr.1 b (hcenters b hb))
      b (5*(s*2^k)) (E₁/(s*2^k)) (by positivity) (by positivity)
      ((shiftedLogShell_support a V hr.1 s b).trans
        (Metric.closedBall_subset_ball (by linarith [hr.1] : 4*(s*2^k) < 5*(s*2^k))))
      (hshell (s*2^k) hr s hsr' b hb).1
    apply h.trans_eq
    field_simp [hr.1.ne']
    ring
  change ‖L _‖ ≤ _
  rw [logSupported_reconstruction a V ha hV R haR K hsr.1 b (hcenters b hb) N hN,map_add,map_sum]
  apply (norm_add_le (L (logInnerSupported a V ha hV R haR K hsr.1 b (hcenters b hb))) _).trans
  apply (add_le_add h₀ ((norm_sum_le (Finset.range N) (fun k => L (logShellSupported a V ha hV R haR K
    (mul_pos hs0 (by positivity : 0 < (2:ℝ)^k)) hs0 b (hcenters b hb)))).trans (Finset.sum_le_sum
    (fun k hk => h₁ k (Finset.mem_range.mp hk))))).trans
  rw [← Finset.mul_sum]
  have hi : s^2 ≤ R^2 := by nlinarith [hsr.1,hsr.2]
  have ht' : (s*2^N)^2 ≤ (2*R)^2 := by nlinarith [hN2,show 0 < s*2^N by positivity]
  have hsum := (sum_dyadic_square_le hsr.1.le N).trans ht'
  calc
    _ ≤ 125*c*E₀*R^2 + 125*c*E₁*(2*R)^2 := by gcongr
    _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
