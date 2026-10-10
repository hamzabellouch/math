import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.UnitaryLocalGarding

namespace OAI

section
section
section

section

noncomputable section
open scoped Manifold ContDiff SchwartzMap
namespace TamingCompatibility.GeometricChart
open ManifoldHodge ManifoldVolume ManifoldForms
open MetricModel MetricForms MetricHodge AntiInvariantFrame EuclideanEnergy LocalMatrixOperator
open MeasureTheory Set
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

structure Data (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X) where
  radius : ℝ
  energyConstant : ℝ
  lowerConstant : ℝ
  radius_pos : 0 < radius
  energy_pos : 0 < energyConstant
  lower_pos : 0 < lowerConstant
  domain : Set Space
  domain_open : IsOpen domain
  ball_subset : Metric.closedBall (extChartAt Model p p) (2*radius) ⊆ domain
  domain_subset : domain ⊆ (extChartAt Model p).target
  frame : Fin 4 → Space → Space
  frame_smooth : ∀ i, ContDiffOn ℝ ∞ (frame i) domain
  frame_gram : ∀ x ∈ domain, ∀ i j,
    (coordinateMetric J α ht p x).bilinear (frame i x) (frame j x) = if i = j then 1 else 0
  frame_complex : ∀ x ∈ domain,
    coordinateJ J p x (frame 0 x) = frame 1 x ∧
    coordinateJ J p x (frame 1 x) = -frame 0 x ∧
    coordinateJ J p x (frame 2 x) = frame 3 x ∧
    coordinateJ J p x (frame 3 x) = -frame 2 x
  garding : ∀ A B : S, tsupport A ⊆ Metric.closedBall (extChartAt Model p p) radius →
    tsupport B ⊆ Metric.closedBall (extChartAt Model p p) radius →
    (∫ x, gradientEnergy A B x) ≤ energyConstant * (∫ x,
      ‖oneVector (starThree (coordinateMetric J α ht p x)
        (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm x)
        (extDeriv (fun y => A y • realPart (coordinateMetric J α ht p y) (fun i => frame i y) +
          B y • imagPart (coordinateMetric J α ht p y) (fun i => frame i y)) x))‖^2) +
      lowerConstant * (∫ x, (A x)^2+(B x)^2)

theorem data_nonempty (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
    (ht : Tames α J) (p : X) : Nonempty (Data J α ht p) := by
  obtain ⟨r,K,C,hr,hK,hC,_,W,hW,hrW,hWU,b,hbs,hb,hJb,hgard⟩ :=
    exists_unitary_local_garding (isOpen_extChartAt_target p)
      (mem_extChartAt_target p) (coordinateMetric J α ht p) (coordinateJ J p)
      (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm)
      (coordinateMetric_smooth J α hs ht p) (coordinateJ_smooth J p)
      (fun x hx => coordinateJ_square J p hx)
      (fun x hx => coordinateMetric_hermitian J α ht p hx)
      (smooth_chart _ (hs.invariantPart J) p)
      (fun x hx => ManifoldTop.coordinateFundamental J α ht p hx)
  exact ⟨⟨r,K,C,hr,hK,hC,W,hW,hrW,hWU,b,hbs,hb,hJb,hgard⟩⟩

def data (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
    (ht : Tames α J) (p : X) : Data J α ht p := Classical.choice (data_nonempty J α hs ht p)

namespace Data
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (D : Data J α ht p)
def source : Set X := (extChartAt Model p).source ∩
  (extChartAt Model p) ⁻¹' Metric.ball (extChartAt Model p p) D.radius
lemma source_open : IsOpen D.source := by
  exact (continuousOn_extChartAt p).isOpen_inter_preimage (isOpen_extChartAt_source p) Metric.isOpen_ball
lemma mem_source : p ∈ D.source := ⟨mem_extChartAt_source p,Metric.mem_ball_self D.radius_pos⟩
lemma source_subset : D.source ⊆ (extChartAt Model p).source := Set.inter_subset_left
lemma source_image_subset : (extChartAt Model p) '' D.source ⊆
    Metric.closedBall (extChartAt Model p p) D.radius := by
  rintro x ⟨y,hy,rfl⟩
  exact Metric.ball_subset_closedBall hy.2
lemma small_ball_subset : Metric.closedBall (extChartAt Model p p) D.radius ⊆ D.domain :=
  (Metric.closedBall_subset_closedBall (by linarith [D.radius_pos])).trans D.ball_subset
end Data

theorem finite_data_partition [T2Space X] [CompactSpace X]
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J) :
    ∃ A : ManifoldLocalization.FiniteCharts X,
      ∀ p : A.centers, tsupport (A.partition p) ⊆ (data J α hs ht p.val).source := by
  classical
  obtain ⟨s,hscover⟩ := isCompact_univ.elim_finite_subcover
    (fun p : X => (data J α hs ht p).source)
    (fun p => (data J α hs ht p).source_open)
    (fun p _ => mem_iUnion_of_mem p (data J α hs ht p).mem_source)
  have hc : (univ : Set X) ⊆ ⋃ p : s, (data J α hs ht p.val).source := by
    intro x hx
    obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp (hscover hx)
    exact mem_iUnion_of_mem ⟨p,hp⟩ hxp
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate Model isClosed_univ
    (fun p : s => (data J α hs ht p.val).source)
    (fun p => (data J α hs ht p.val).source_open) hc
  refine ⟨⟨s,ρ,fun p => (hρ p).trans (data J α hs ht p.val).source_subset⟩,?_⟩
  exact hρ
end TamingCompatibility.GeometricChart

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization ManifoldHodge
open Set MetricForms AntiInvariantFrame
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in
omit [T2Space X] [CompactSpace X] in
lemma coordinateSupport_small (p : A.centers) : coordinateSupport A p ⊆
    Metric.closedBall (extChartAt Model p.val p.val) (D p).radius := by
  rintro x ⟨y,hy,rfl⟩
  exact (D p).source_image_subset ⟨y,hD p hy,rfl⟩
include hD in
omit [T2Space X] [CompactSpace X] in
lemma coordinateSupport_domain (p : A.centers) : coordinateSupport A p ⊆ (D p).domain :=
  (coordinateSupport_small A J α ht D hD p).trans (D p).small_ball_subset

omit [T2Space X] [CompactSpace X] in
lemma localizedFunction_zero_off {k : ℕ} (p : A.centers) (a : ManifoldForms.Form X k)
    {x : Space} (hx : x ∉ coordinateSupport A p) : localizedFunction A p a x = 0 := by
  unfold localizedFunction
  by_cases he : x ∈ (extChartAt Model p.val).target
  · rw [indicator_of_mem he]
    have hρ : (extChartAt Model p.val).symm x ∉ tsupport (A.partition p) := by
      intro h
      exact hx ⟨_,h,(extChartAt Model p.val).right_inv he⟩
    rw [image_eq_zero_of_notMem_tsupport hρ,zero_smul]
  · exact indicator_of_notMem he _

def scalar (p : A.centers) (a : TwoForm X) (j : Fin 4) : Space → ℝ :=
  (D p).domain.indicator (fun x => localizedFunction A p a x ![(D p).frame 0 x,(D p).frame j x])

omit [T2Space X] [CompactSpace X] in
lemma scalar_zero_off (p : A.centers) (a : TwoForm X) (j : Fin 4)
    {x : Space} (hx : x ∉ coordinateSupport A p) : scalar A J α ht D p a j x = 0 := by
  unfold scalar
  by_cases he : x ∈ (D p).domain
  · rw [indicator_of_mem he,localizedFunction_zero_off A p a hx]
    rfl
  · exact indicator_of_notMem he _

omit [T2Space X] in
lemma scalar_tsupport_subset (p : A.centers) (a : TwoForm X) (j : Fin 4) :
    tsupport (scalar A J α ht D p a j) ⊆ coordinateSupport A p := by
  apply closure_minimal _ (coordinateSupport_compact A p).isClosed
  intro x hx
  by_contra hn
  exact hx (scalar_zero_off A J α ht D p a j hn)

include hD in
omit [T2Space X] in
lemma scalar_smooth_compact (p : A.centers) (a : TwoForm X) (ha : IsSmooth a) (j : Fin 4) :
    ContDiff ℝ ∞ (scalar A J α ht D p a j) ∧ HasCompactSupport (scalar A J α ht D p a j) := by
  apply smooth_indicator_of_compact (D p).domain_open (coordinateSupport_compact A p)
    (coordinateSupport_domain A J α ht D hD p)
  · exact FormSmooth.contDiffOn_apply_two
      (localizedFunction_smooth_compact A p a ha).1.contDiffOn
      ((D p).frame_smooth 0) ((D p).frame_smooth j)
  · intro x _ hx
    rw [localizedFunction_zero_off A p a hx]
    rfl

def scalarSchwartz (p : A.centers) (a : TwoForm X) (ha : IsSmooth a) (j : Fin 4) :
    𝓢(Space,ℝ) :=
  (scalar_smooth_compact A J α ht D hD p a ha j).2.toSchwartzMap
    (scalar_smooth_compact A J α ht D hD p a ha j).1

omit [T2Space X] in
lemma scalarSchwartz_support (p : A.centers) (a : TwoForm X) (ha : IsSmooth a) (j : Fin 4) :
    tsupport (scalarSchwartz A J α ht D hD p a ha j) ⊆
      Metric.closedBall (extChartAt Model p.val p.val) (D p).radius :=
  (scalar_tsupport_subset A J α ht D p a j).trans (coordinateSupport_small A J α ht D hD p)
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
