import Mathlib
import OAI.Geometry.Cannon.Energy.RecordData

namespace OAI

section
section
section
noncomputable section
section
section
section
namespace CannonApprox

open Set Metric Filter Topology MeasureTheory CannonNode CannonMagnification CannonPacking CannonAnnular

structure FlowSetup {X Γ : Type*} [MetricSpace X] [MeasurableSpace X]
    {action : Γ → X ≃ₜ X} {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {p : ∀ n, ι n → X} {r : ℕ → ℝ} (R : RecordData action ι p r)
    (ell L CE LE : ℝ) (Q : ℕ) where
  ε : ℝ
  εpos : 0 < ε
  local_domain : closedBall R.x₀ (2*ε) ⊆ R.Ω
  c₀ : ℝ
  A : ℝ
  B : ℝ
  cPat : ℝ
  H : ℝ
  core : 2*L+2 < c₀
  inner : A=4*L*c₀+20
  outer : B=A+10
  pattern : cPat=2*CE*(2*L)/(A-2)^2
  pattern_pos : 0 < cPat
  margin : 12*cPat*(B+2)^2*LE < c₀
  separation : max (4*(B+1)) (max (4*R.Cμ*c₀) 2) < H
  ρ : ℝ
  ρpos : 0 < ρ
  small : (B+2)*ρ ≤ ε
  cutoff : ρ ≤ ε/2
  n : ℕ
  npos : 0 < n
  decay : radius ell (160*(Q+1)*n) < 1/4
  S : SourceConstruction R.f R.x₀ ε ell c₀ A B H ρ Q n
  energy : ∀ g, ∑ i, (S.len g i)^2 ≤ R.E * (R.ν univ : ℝ)
  good : ∀ N : ℕ, ∃ g ≥ N, (1/2:ℝ) ≤ S.flow.goodMass g

variable {X Γ : Type*} [MetricSpace X] [CompactSpace X] [LocallyPathConnectedSpace X]
  [MeasurableSpace X] [BorelSpace X]
  {action : Γ → X ≃ₜ X} {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
  {p : ∀ n, ι n → X} {r : ℕ → ℝ}

theorem RecordData.make_flow (R : RecordData action ι p r)
    (Q : ℕ) (CP CE LE ell L d₀ : ℝ)
    (hpack : PolynomialPacking (X:=X) Q CP) (hCP : 0 ≤ CP)
    (hCE : 0 < CE) (hLE : 0 < LE) (hell : 0 < ell) (hL : 1 ≤ L)
    (hdc : d₀ ≤ 1/(9*LE))
    (M : ℕ → ℝ) (hMnon : ∀ j, 0 ≤ M j)
    (hM : ∀ lam : ℝ, 1 < lam → ∃ C : ℝ, 0 < C ∧ ∀ j, M j ≤ C*lam^j)
    (δ : ℕ → Type*) [∀ j, Fintype (δ j)] (ξ : ∀ j, δ j → X)
    (hξ : ∀ j i i', i ≠ i' → radius ell j ≤ dist (ξ j i) (ξ j i'))
    (ω : ∀ j, δ j → ℝ) (hω : ∀ j, MacroscopicAdmissible (ξ j) (radius ell j) d₀ (ω j))
    (hωmass : ∀ j, (∑ i, (ω j i)^2) ≤ M j)
    (h : X → ℕ → X ≃ₜ X)
    (hexp : ∀ x k, Expansion (h x k) x (radius ell k) CE LE)
    (hpaths : ∀ x u v : X, ∀ s : ℝ, 0 < s → dist u x ≤ s → dist v x ≤ s →
      JoinedIn (ball x (L*s)) u v) :
    Nonempty (FlowSetup R ell L CE LE Q) := by
  classical
  obtain ⟨e,he,heΩ⟩ := Metric.isOpen_iff.mp R.isOpen R.x₀ R.x₀mem
  let ε := e/4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hloc : closedBall R.x₀ (2*ε) ⊆ R.Ω :=
    (closedBall_subset_ball (by dsimp [ε]; linarith only [he])).trans heΩ
  have hKΩ : closedBall R.x₀ ε ⊆ R.Ω :=
    (closedBall_subset_closedBall (by linarith only [hε])).trans hloc
  obtain ⟨s₀,hs₀,hmeasure⟩ := R.measure_bound (closedBall R.x₀ ε) isClosed_closedBall.isCompact hKΩ
  obtain ⟨c₀,A,B,cPat,H,hcore,hinner,houter,hpattern,hcPat,hmargin,hsep⟩ :=
    exists_flow_constants hL hCE hLE R.Cμ_pos.le
  have hc₀ : 2 ≤ c₀ := by linarith only [hcore,hL]
  have hc₀pos : 0 < c₀ := by linarith only [hc₀]
  have hA : 1 ≤ A := by rw [hinner]; nlinarith only [hL,hc₀]
  have hAB : A+3 ≤ B := by rw [houter]; linarith
  have hB : 0 ≤ B+1 := by linarith only [hA,hAB]
  have hB₂ : 0 < B+2 := by linarith only [hB]
  have hH : 0 < H := lt_trans (by norm_num : (0:ℝ) < 2)
    ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hsep))
  have hLc : L*c₀ ≤ A := by rw [hinner]; nlinarith only [mul_pos (zero_lt_one.trans_le hL) hc₀pos]
  let ρ := min (s₀/c₀) (min (ε/(B+2)) (ε/2))
  have hρ : 0 < ρ := lt_min (div_pos hs₀ hc₀pos)
    (lt_min (div_pos hε hB₂) (by positivity))
  have hρs : c₀*ρ ≤ s₀ := by
    have hh := (le_div_iff₀ hc₀pos).mp (min_le_left (s₀/c₀) (min (ε/(B+2)) (ε/2)))
    simpa only [mul_comm,ρ] using hh
  have hρB : (B+2)*ρ ≤ ε := by
    have hmin : ρ ≤ ε/(B+2) := (min_le_right _ _).trans (min_le_left _ _)
    have hh := (le_div_iff₀ hB₂).mp hmin
    simpa only [mul_comm,ρ] using hh
  have hρcut : ρ ≤ ε/2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨n,hn,hθ,⟨S⟩⟩ := exists_source_construction Q CP A B H c₀ CE LE d₀ ell L
    hpack hCP hA hAB hH hc₀ hCE.le hLE hdc hell hL hLc M hMnon hM δ ξ hξ ω hω hωmass
    h hexp hpaths R.Ω R.f R.continuous R.unit R.level R.diameter R.diameter_pos
    (fun t ht => ⟨(R.level_properties t ht).2.1.isPreconnected,
      (R.level_properties t ht).2.2.1,(R.level_properties t ht).2.2.2⟩)
    R.level_hits R.x₀ ε ρ hε hρ hloc R.variation
  have hE : ∀ g, ∑ i, (S.len g i)^2 ≤ R.E*(R.ν univ : ℝ) := by
    apply S.level_energy R.ν.toMeasure R.Cμ R.E R.E_nonneg hB hc₀pos.le hθ
      (lt_of_le_of_lt (le_max_left _ _) hsep) ?_ ?_ ?_
    · have hh := lt_of_le_of_lt (le_max_left (4*R.Cμ*c₀) 2)
        (lt_of_le_of_lt (le_max_right (4*(B+1)) _) hsep)
      nlinarith only [hh,mul_pos R.Cμ_pos hc₀pos]
    · intro x hx s hs hsr
      have hh := hmeasure (c₀*s) (mul_pos hc₀pos hs)
        ((mul_le_mul_of_nonneg_left hsr hc₀pos.le).trans hρs) x hx
      exact R.continuous.mono hh.1
    · intro x hx s hs hsr y hy z hz
      have hh := hmeasure (c₀*s) (mul_pos hc₀pos hs)
        ((mul_le_mul_of_nonneg_left hsr hc₀pos.le).trans hρs) x hx
      have hb := (isCompact_closedBall x (c₀*s)).image_of_continuousOn (R.continuous.mono hh.1)
      have hyl := csInf_le hb.bddBelow (mem_image_of_mem R.f hy)
      have hyu := le_csSup hb.bddAbove (mem_image_of_mem R.f hy)
      have hzl := csInf_le hb.bddBelow (mem_image_of_mem R.f hz)
      have hzu := le_csSup hb.bddAbove (mem_image_of_mem R.f hz)
      have hd : |R.f y-R.f z| ≤ CannonCrossEnergy.oscillation R.f (closedBall x (c₀*s)) := by
        unfold CannonCrossEnergy.oscillation
        exact abs_le.mpr ⟨by linarith only [hyl,hzu],by linarith only [hzl,hyu]⟩
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hd 2
      change (R.f y-R.f z)^2 ≤ R.E*(R.ν (closedBall x (R.Cμ*(c₀*s))) : ℝ)
      simpa only [sq_abs] using hsq.trans hh.2
  exact ⟨{
    ε := ε, εpos := hε, local_domain := hloc, c₀ := c₀, A := A, B := B,
    cPat := cPat, H := H, core := hcore, inner := hinner, outer := houter,
    pattern := hpattern, pattern_pos := hcPat, margin := hmargin, separation := hsep,
    ρ := ρ, ρpos := hρ, small := hρB, cutoff := hρcut, n := n, npos := hn, decay := hθ,
    S := S, energy := hE, good := S.arbitrarily_late_good hell hn _ hE }⟩

end CannonApprox

end

section

section

section

open Set Topology

namespace CannonRelease

open Set Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G)

variable (hthin : D.ThinTriangles)

local instance flowSetupRaySetoid1 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open Set Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) (hthin : D.ThinTriangles)

local instance flowSetupRaySetoid2 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance flowSetupRaySetoid3 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance flowSetupRaySetoid4 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance flowSetupRaySetoid5 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance flowSetupRaySetoid6 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance flowSetupRaySetoid7 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance flowSetupRaySetoid8 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance flowSetupRaySetoid9 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance flowSetupRaySetoid10 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance flowSetupRaySetoid11 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance flowSetupRaySetoid12 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance flowSetupRaySetoid13 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance flowSetupRaySetoid14 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance flowSetupRaySetoid15 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance flowSetupRaySetoid16 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance flowSetupRaySetoid17 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

open Set Metric Topology

namespace CannonRelease

open CannonGraph CannonVisual CannonPaths Set Metric

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance flowSetupRaySetoid18 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace

end
end
end
end
end
end
end
end
end

end OAI
