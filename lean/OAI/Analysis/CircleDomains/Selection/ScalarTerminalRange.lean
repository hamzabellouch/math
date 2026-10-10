import OAI.Analysis.CircleDomains.Selection.ScalarRegionLowerRange
import OAI.Analysis.CircleDomains.Topology.RetainedImageBoundary

namespace OAI

/-! The actual matched terminal contours propagate source scalar ranges
to their entire closed target disks, including all complementary dust. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 theorem imageScalar_lt_on_terminal (hG : IsOpen d.physicalDomain) (i : Fin m)
    (n : ℕ) (j : Fin (R.limit.cores n).count) {b : ℝ}
    (hb : ∀ x ∈ closure (jordanInterior ((R.limit.cores n).disk j)),
      (x : Sphere) ∈ d.physicalDomain → (Q i).physical (Complex.equivRealProdCLM x) < b) :
    ∀ z ∈ closure (jordanInterior (R.limit.contours n j)),
      z ∈ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) →
      R.imageScalar i z < b := by
  have hcap := target_closed_collar_subset_image
    ((R.limit.cores n).disk j) (R.limit.contours n j)
    ((R.limit.cores n).boundary_subset_domain j)
    (R.limit.boundary n j) (R.limit.side n j) (Subset.refl _)
  intro z hz himg
  have hzV : (z : Sphere) ∈ extendAtInfinity R.limit.function '' d.physicalDomain := by
    obtain ⟨x, hx, rfl⟩ := himg
    exact ⟨(x : Sphere), hx, by simp⟩
  obtain ⟨p, ⟨hpG, hpcap⟩, he⟩ := hcap ⟨hzV, z, hz, rfl⟩
  obtain ⟨x, hx, rfl⟩ := hpcap
  have hxz : R.limit.function x = z := OnePoint.coe_injective (by simpa using he)
  rw [← hxz, R.imageScalar_apply hG i hpG]
  exact hb x hx hpG

 theorem terminal_frontier_subset_image (n : ℕ) (j : Fin (R.limit.cores n).count) :
    frontier (jordanInterior (R.limit.contours n j)) ⊆
      R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) := by
  intro z hz
  obtain ⟨p, hp, he⟩ := (R.limit.boundary n j).symm ▸
    (show (z : Sphere) ∈ ((↑) : ℂ → Sphere) '' frontier (jordanInterior (R.limit.contours n j)) from
      ⟨z, hz, rfl⟩)
  obtain ⟨x, hx, rfl⟩ := hp
  refine ⟨x, (R.limit.cores n).boundary_subset_domain j ⟨x, hx, rfl⟩, ?_⟩
  exact OnePoint.coe_injective (by simpa using he)

 theorem ScalarWeakLimit.le_on_terminal {i : Fin m} (W : R.ScalarWeakLimit i)
    (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (n : ℕ) (j : Fin (R.limit.cores n).count) {b : ℝ} (hb : 0 ≤ b)
    (hsource : ∀ x ∈ closure (jordanInterior ((R.limit.cores n).disk j)),
      (x : Sphere) ∈ d.physicalDomain → (Q i).physical (Complex.equivRealProdCLM x) < b) :
    ∀ᵐ z ∂volume, z ∈ closure (jordanInterior (R.limit.contours n j)) → W.scalar z ≤ b :=
  W.le_on_closed_region hsch hG (jordanInterior_isOpen _)
    (isCompact_closure_jordanInterior _) (R.terminal_frontier_subset_image n j) hb
    (R.imageScalar_lt_on_terminal hG i n j hsource)

 theorem ScalarWeakLimit.ge_on_terminal {i : Fin m} (W : R.ScalarWeakLimit i)
    (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (n : ℕ) (j : Fin (R.limit.cores n).count) {a : ℝ} (ha : a ≤ 1)
    (hsource : ∀ x ∈ closure (jordanInterior ((R.limit.cores n).disk j)),
      (x : Sphere) ∈ d.physicalDomain → a < (Q i).physical (Complex.equivRealProdCLM x)) :
    ∀ᵐ z ∂volume, z ∈ closure (jordanInterior (R.limit.contours n j)) → a ≤ W.scalar z := by
  apply W.ge_on_closed_region hsch hG (jordanInterior_isOpen _)
    (isCompact_closure_jordanInterior _) (R.terminal_frontier_subset_image n j) ha
  have hcap := target_closed_collar_subset_image
    ((R.limit.cores n).disk j) (R.limit.contours n j)
    ((R.limit.cores n).boundary_subset_domain j)
    (R.limit.boundary n j) (R.limit.side n j) (Subset.refl _)
  intro z hz himg
  have hzV : (z : Sphere) ∈ extendAtInfinity R.limit.function '' d.physicalDomain := by
    obtain ⟨x, hx, rfl⟩ := himg
    exact ⟨(x : Sphere), hx, by simp⟩
  obtain ⟨p, ⟨hpG, hpcap⟩, he⟩ := hcap ⟨hzV, z, hz, rfl⟩
  obtain ⟨x, hx, rfl⟩ := hpcap
  have hxz : R.limit.function x = z := OnePoint.coe_injective (by simpa using he)
  rw [← hxz, R.imageScalar_apply hG i hpG]
  exact hsource x hx hpG

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
