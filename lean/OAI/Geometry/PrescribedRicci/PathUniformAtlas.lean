import Mathlib
import OAI.Geometry.PrescribedPotential.BoundedPoisson
import OAI.Geometry.PrescribedRicci.PathUniformSobolevBase
import OAI.Geometry.PrescribedRicci.UniformFrozenEstimate
import OAI.Geometry.PrescribedRicci.UniformPathPatches

namespace OAI

/-! Path Uniform Atlas. -/

section

 

noncomputable section
open Set Filter Topology Manifold IsManifold Matrix
open scoped ContDiff SchwartzMap BoundedContinuousFunction ComplexOrder MatrixOrder Matrix.Norms.Elementwise Classical
namespace Anticanonical.SourceSmooth
open EllipticKernel SobolevChart FrozenPoisson MetricLocalization GlobalElliptic
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X}

structure UniformPathPatch (g : KaehlerMetric A) (line : SemipositiveAnticanonicalMetric A) where
  index : Fin A.count
  center : EC d
  domain : Set (EC d)
  isOpen_domain : IsOpen domain
  center_mem : center ∈ domain
  domain_sub : domain ⊆ (A.euclideanChart index).target
  bound : ℝ
  bound_pos : 0 < bound
  matrix_bound : ∀ z : g.NormalizedPathSolution line,
    ‖(g.deform z.potential z.positive).matrix index (coordinateEquiv d center)‖ ≤ bound
  coefficient : g.NormalizedPathSolution line → SmoothCoefficients (BasisIndex d) (EC d)
  small : ∀ z, perturbationBound (stdOrthonormalBasis ℝ (EC d)) (coefficientBCF (coefficient z)) *
    uniformEllipticBound d bound ≤ 1/2
  equals : ∀ z, ∀ y ∈ domain, ∀ k l,
    extendedCoefficient ((g.deform z.potential z.positive).matrix index (coordinateEquiv d center))
      (coefficientBCF (coefficient z)) k l y =
      (traceBilin ((g.deform z.potential z.positive).matrix index (coordinateEquiv d y))
        (rankTwo (stdOrthonormalBasis ℝ (EC d) k) (stdOrthonormalBasis ℝ (EC d) l)) : ℂ)

namespace UniformPathPatch
variable {g : KaehlerMetric A} {line : SemipositiveAnticanonicalMetric A}
def source (p : UniformPathPatch g line) : Set X :=
  (A.euclideanChart p.index).source ∩ (A.euclideanChart p.index) ⁻¹' p.domain
omit [ConnectedSpace X] in
lemma isOpen_source (p : UniformPathPatch g line) : IsOpen p.source :=
  (A.euclideanChart p.index).isOpen_inter_preimage p.isOpen_domain
omit [ConnectedSpace X] in
lemma source_sub (p : UniformPathPatch g line) : p.source ⊆ (A.euclideanChart p.index).source :=
  fun _ hx => hx.1
omit [ConnectedSpace X] in
lemma center_target (p : UniformPathPatch g line) : p.center ∈ (A.euclideanChart p.index).target :=
  p.domain_sub p.center_mem

theorem exists_at (g : KaehlerMetric A) (line : SemipositiveAnticanonicalMetric A)
    (hd : 2 ≤ d) (x : X) : ∃ p : UniformPathPatch g line, x ∈ p.source := by
  obtain ⟨i,hi⟩ := A.covers x
  let e := A.euclideanChart i
  have hxe : x ∈ e.source := by simpa [e] using hi
  have hx : e x ∈ e.target := e.mapsTo hxe
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds hx)
  have hc : Metric.closedBall (e x) (ε/2) ⊆ e.target :=
    (Metric.closedBall_subset_ball (by linarith : ε/2 < ε)).trans hball
  obtain ⟨M,r,hM,hr,hrR,hpatch⟩ := g.volumePath_uniform_patch line hd i (e x)
    (by linarith : 0 < ε/2) hc (stdOrthonormalBasis ℝ (EC d))
  have hp (z : g.NormalizedPathSolution line) :=
    hpatch z.potential z.positive z.mean_zero z.time z.constant z.time_mem z.equation
  choose hb a has hac hsmall heq using hp
  let coeff (z : g.NormalizedPathSolution line) : SmoothCoefficients (BasisIndex d) (EC d) :=
    fun k l => (hac z k l).toSchwartzMap (has z k l)
  have he (z : g.NormalizedPathSolution line) : coefficientBCF (coeff z) = a z := by
    funext k l; ext y; rfl
  let p : UniformPathPatch g line := {
    index := i
    center := e x
    domain := Metric.ball (e x) (r/2)
    isOpen_domain := Metric.isOpen_ball
    center_mem := Metric.mem_ball_self (by linarith)
    domain_sub := fun y hy => hc ((Metric.closedBall_subset_closedBall hrR)
      ((Metric.ball_subset_closedBall).trans (Metric.closedBall_subset_closedBall (by linarith : r/2 ≤ r)) hy))
    bound := M
    bound_pos := hM
    matrix_bound := hb
    coefficient := coeff
    small := by intro z; rw [he]; exact hsmall z
    equals := by
      intro z y hy k l
      rw [he]
      change (traceBilin _ _ : ℂ)+a z k l y = _
      rw [heq z y (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hy).le) k l]
      ring }
  exact ⟨p,hxe,Metric.mem_ball_self (by linarith)⟩

theorem finite_cover (g : KaehlerMetric A) (line : SemipositiveAnticanonicalMetric A) (hd : 2 ≤ d) :
    ∃ S : Finset (UniformPathPatch g line), ∀ x : X, ∃ p ∈ S, x ∈ p.source := by
  obtain ⟨S,hS⟩ := isCompact_univ.elim_finite_subcover (fun p : UniformPathPatch g line => p.source)
    (fun p => p.isOpen_source) (by
      intro x _
      obtain ⟨p,hp⟩ := exists_at g line hd x
      exact mem_iUnion.mpr ⟨p,hp⟩)
  refine ⟨S,fun x => ?_⟩
  obtain ⟨p,hp,hx⟩ := mem_iUnion₂.mp (hS (mem_univ x))
  exact ⟨p,hp,hx⟩
end UniformPathPatch

theorem exists_uniform_path_localizers (g : KaehlerMetric A)
    (line : SemipositiveAnticanonicalMetric A) (hd : 2 ≤ d) :
    ∃ (S : Finset (UniformPathPatch g line)) (D : Localizers A S),
      (∀ p : S, D.index p = p.val.index) ∧
      (∀ p : S, tsupport (D.weight p : X → ℂ) ⊆ p.val.source) := by
  obtain ⟨S,hS⟩ := UniformPathPatch.finite_cover g line hd
  let := A.chartedSpace
  let := A.isManifold
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ,Coordinates d) (s:=(Set.univ : Set X)) isClosed_univ
    (fun p : S => p.val.source) (fun p => p.val.isOpen_source) (by
      intro x _
      obtain ⟨p,hp,hx⟩ := hS x
      exact mem_iUnion.mpr ⟨⟨p,hp⟩,hx⟩)
  let f (p : S) : SmoothRealFunction A := ⟨ρ p,(A.contMDiff_iff (ρ p)).mp (ρ p).contMDiff⟩
  let D : Localizers A S := {
    index := fun p => p.val.index
    weight := fun p => Smooth.ofReal (f p)
    support_sub := by
      intro p
      rw [Smooth.ofReal_tsupport]
      exact (hρ p).trans p.val.source_sub
    sum_one := by
      intro x
      change (∑ p : S,((ρ p x : ℝ):ℂ)) = 1
      rw [← Complex.ofReal_sum]
      exact_mod_cast (show ∑ p : S,ρ p x = 1 by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)) }
  refine ⟨S,D,fun _ => rfl,?_⟩
  intro p
  change tsupport (Smooth.ofReal (f p) : X → ℂ) ⊆ _
  rw [Smooth.ofReal_tsupport]
  exact hρ p
end Anticanonical.SourceSmooth

end
end

end OAI
