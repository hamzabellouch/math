import OAI.Geometry.RCD.Sobolev.WeakLaplacianDomain

namespace OAI

/-! # A dense compact test core with actual L² Laplacians -/

open Set Filter MeasureTheory Topology
open scoped NNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Compact Lipschitz Sobolev functions whose weak Laplacian belongs to L². -/
def compactLaplacianCore (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) (Ω : Set X) :
    Submodule ℝ (SobolevSpace μ hQ) :=
  SobolevSpace.dirichletCore μ hQ Ω ⊓ weakLaplacianDomain μ hQ

theorem NoncollapsedRCD.compactLaplacianCore_closure {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {Ω : Set X} (hΩ : IsOpen Ω) :
    (compactLaplacianCore (hausdorff n X) hX.quadratic Ω).topologicalClosure =
      SobolevSpace.dirichlet (hausdorff n X) hX.quadratic Ω := by
  let μ := hausdorff n X
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _
      (inf_le_left.trans (Submodule.le_topologicalClosure _))
      (Submodule.isClosed_topologicalClosure _)
  apply Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
  rintro u ⟨φ,L,hφ,hcompact,hsupport,hu⟩
  obtain ⟨χ,hχ,hχ1⟩ := hX.exists_open_regular_cutoff hn hΩ hcompact hsupport
  let M := SobolevSpace.cutoffCLM μ hX.quadratic χ.lipschitz χ.compact χ.abs_le
    (fun x => (χ.bounds x).1)
  have hMu : M u=u := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [SobolevSpace.cutoffCLM_coe μ hX.quadratic χ.lipschitz χ.compact χ.abs_le
      (fun x => (χ.bounds x).1) u,hu] with x hx hux
    change SobolevSpace.toLp μ hX.quadratic (M u) x = SobolevSpace.toLp μ hX.quadratic u x
    rw [hx,hux]
    by_cases hz : φ x=0
    · rw [hz,mul_zero]
    · rw [hχ1 x (subset_tsupport φ hz),one_mul]
  obtain ⟨A,hA⟩ := hcompact.exists_bound_of_continuous hφ.continuous
  let B : ℝ≥0 := ⟨max A 0,le_max_right _ _⟩
  have hB (x : X) : |φ x| ≤ B := by
    have hb : |φ x| ≤ A := by simpa only [Real.norm_eq_abs] using hA x
    exact hb.trans (le_max_left _ _)
  have huB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hX.quadratic u x| ≤ B :=
    hu.mono fun x hx => hx ▸ hB x
  let t (k : ℕ) : ℝ := 1/((k:ℝ)+1)
  have ht (k : ℕ) : 0<t k := by dsimp only [t]; positivity
  let us (k : ℕ) := heatSobolev μ hX.quadratic (t k) (ht k)
    (SobolevSpace.toLp μ hX.quadratic u)
  have hconv : Tendsto us atTop (𝓝 u) := by
    have hc := ((heatH1_continuous μ hX.quadratic u).tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [heatH1_zero,Function.comp_def,heatH1,dite_eq_left (ht _),
      lt_self_iff_false,dite_false,us,t] using hc
  have hconvM : Tendsto (fun k => M (us k)) atTop (𝓝 u) := by
    simpa only [hMu,Function.comp_def] using M.continuous.tendsto u |>.comp hconv
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hconvM
  apply Eventually.of_forall
  intro k
  apply Submodule.le_topologicalClosure
  constructor
  · obtain ⟨v,hv,hev⟩ := hX.heat_lipschitz K n hn
      (SobolevSpace.toLp μ hX.quadratic u) hφ hu.symm B hB (ht k).le
    obtain ⟨D,hD⟩ := lipschitz_mul_constant_outside_compact χ.lipschitz hv 0
      (by simpa using χ.compact) χ.abs_le
    refine ⟨fun x => χ.weight x*v x,D,hD,χ.compact.mul_right,
      tsupport_mul_subset_left.trans hχ,?_⟩
    filter_upwards [SobolevSpace.cutoffCLM_coe μ hX.quadratic χ.lipschitz χ.compact χ.abs_le
      (fun x => (χ.bounds x).1) (us k),hev] with x hx hvx
    exact hx.trans (congrArg (fun z => χ.weight x*z) hvx)
  · have hbound : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hX.quadratic (us k) x| ≤ B :=
      heatAt_abs_le_const μ hX.quadratic (t k) B _ huB
    obtain ⟨d,hd,-⟩ := (heatSobolev_weak_laplacian μ hX.quadratic (t k) (ht k)
      (SobolevSpace.toLp μ hX.quadratic u)).cutoff μ hX.quadratic (us k) χ.sobolev
      _ χ.laplacian χ.weak_laplacian χ.lipschitz χ.compact χ.abs_le
      (fun x => (χ.bounds x).1) χ.representative hbound
    exact ⟨d,hd⟩

/-- The same core as a submodule of the actual zero-boundary space. -/
def regularDirichletCore (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) (Ω : Set X) :
    Submodule ℝ (SobolevSpace.dirichlet μ hQ Ω) :=
  (compactLaplacianCore μ hQ Ω).comap (SobolevSpace.dirichlet μ hQ Ω).subtype

theorem NoncollapsedRCD.regularDirichletCore_dense {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {Ω : Set X} (hΩ : IsOpen Ω) :
    Dense (regularDirichletCore (hausdorff n X) hX.quadratic Ω :
      Set (SobolevSpace.dirichlet (hausdorff n X) hX.quadratic Ω)) := by
  let μ := hausdorff n X
  intro φ
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have himage : Subtype.val '' (regularDirichletCore μ hX.quadratic Ω :
      Set (SobolevSpace.dirichlet μ hX.quadratic Ω)) =
      (compactLaplacianCore μ hX.quadratic Ω : Set (SobolevSpace μ hX.quadratic)) := by
    ext u
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact hv
    · intro hu
      exact ⟨⟨u,Submodule.le_topologicalClosure _ hu.1⟩,hu,rfl⟩
  rw [himage]
  change φ.val ∈ (compactLaplacianCore μ hX.quadratic Ω).topologicalClosure
  rw [hX.compactLaplacianCore_closure hn hΩ]
  exact φ.property

end RegularPointCoordinates

end

end OAI
