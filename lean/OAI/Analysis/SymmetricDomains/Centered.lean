import Mathlib
import OAI.Analysis.SymmetricDomains.AffineBand

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
open scoped Classical

namespace NashPatch
variable {n : ℕ}

noncomputable def recenter (p : NashPatch n) (x : Fin p.dim → ℝ) : NashPatch n where
  dim := p.dim
  domain := (fun y => y+x) ⁻¹' p.domain
  isOpen_domain := p.isOpen_domain.preimage (continuous_id.add continuous_const)
  isConnected_domain := (Homeomorph.addRight x).isConnected_preimage.mpr p.isConnected_domain
  semialgebraic_domain := p.semialgebraic_domain.polynomial_preimage (fun y => y+x)
    (fun i => MvPolynomial.X i + MvPolynomial.C (x i)) (by intros; simp)
  toFun := fun y => p.toFun (y+x)
  semialgebraic_toFun := by
    have hB := p.semialgebraic_domain.polynomial_preimage (d := id) (fun y => y+x)
      (fun i => MvPolynomial.X i + MvPolynomial.C (x i)) (by intros; simp)
    have ht : SemialgebraicOn ((fun y => y+x) ⁻¹' p.domain) (fun y => y+x) := by
      exact (SemialgebraicOn.polynomial hB (fun i => MvPolynomial.X i + MvPolynomial.C (x i))).congr
        (by intro y _; funext i; simp)
    exact p.semialgebraic_toFun.comp ht (fun _ h => h)
  analytic_toFun := by
    intro y hy
    exact (p.analytic_toFun (y+x) hy).comp (f := fun z => z+x) (x := y) (analyticAt_id.add analyticAt_const)
  injective_fderiv := by
    intro y hy
    have htr : HasFDerivAt (fun z : Fin p.dim → ℝ => z+x) (ContinuousLinearMap.id ℝ _) y :=
      (hasFDerivAt_id y).add_const x
    have hd := (p.analytic_toFun (y+x) hy).differentiableAt.hasFDerivAt.comp y htr
    change Function.Injective (fderiv ℝ (p.toFun ∘ (fun z => z+x)) y)
    rw [hd.fderiv]
    simpa only [ContinuousLinearMap.comp_id] using p.injective_fderiv (y+x) hy

lemma recenter_zero (p : NashPatch n) {x : Fin p.dim → ℝ} (hx : x ∈ p.domain) :
    0 ∈ (p.recenter x).domain := by
  change (0 : Fin p.dim → ℝ)+x ∈ p.domain
  simpa only [zero_add] using hx

lemma recenter_image (p : NashPatch n) (x : Fin p.dim → ℝ) : (p.recenter x).image = p.image := by
  change (fun y : Fin p.dim → ℝ => p.toFun (y+x)) '' ((fun y => y+x) ⁻¹' p.domain) =
    p.toFun '' p.domain
  apply Set.Subset.antisymm
  · rintro _ ⟨y,hy,rfl⟩
    exact ⟨y+x,hy,rfl⟩
  · rintro _ ⟨y,hy,rfl⟩
    refine ⟨y-x,?_,?_⟩
    · change y-x+x ∈ p.domain
      simpa only [sub_add_cancel] using hy
    · change p.toFun (y-x+x) = p.toFun y
      rw [sub_add_cancel]

noncomputable def centered (p : NashPatch n) : NashPatch n :=
  p.recenter p.isConnected_domain.nonempty.choose

lemma centered_zero (p : NashPatch n) : 0 ∈ p.centered.domain :=
  p.recenter_zero p.isConnected_domain.nonempty.choose_spec

lemma centered_image (p : NashPatch n) : p.centered.image = p.image := p.recenter_image _

end NashPatch

lemma HasFiniteNashCover.centered {n : ℕ} {S : Set (Fin n → ℝ)} (hS : HasFiniteNashCover S) :
    ∃ C : Finset (NashPatch n), (∀ p ∈ C, 0 ∈ p.domain) ∧
      ∀ y, y ∈ S ↔ ∃ p ∈ C, y ∈ p.image := by
  obtain ⟨C,hC⟩ := hS
  refine ⟨C.image NashPatch.centered,?_,?_⟩
  · intro p hp
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hp
    exact p.centered_zero
  · intro y
    rw [hC y]
    constructor
    · rintro ⟨p,hp,hy⟩
      exact ⟨p.centered,Finset.mem_image.mpr ⟨p,hp,rfl⟩,p.centered_image ▸ hy⟩
    · rintro ⟨p,hp,hy⟩
      obtain ⟨a,ha,hap⟩ := Finset.mem_image.mp hp
      subst p
      exact ⟨a,ha,a.centered_image ▸ hy⟩

end Release061

end

end OAI
