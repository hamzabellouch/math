import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.InteriorRegularity
import OAI.Geometry.TamingCompatibility.Functional.NormalPatch

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.SchwartzCutoff
open Set Filter
open scoped ContDiff Topology SchwartzMap Manifold
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma exists_reciprocal {U : Set E} (hU : IsOpen U) {w : E → ℝ}
    (hw : ContDiffOn ℝ ∞ w U) {z : E} (hz : z ∈ U) (hwz : w z ≠ 0) :
    ∃ τ : 𝓢(E,ℝ), HasCompactSupport (τ : E → ℝ) ∧ tsupport τ ⊆ U ∧
      ∃ V : Set E, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V, τ y * w y = 1 := by
  have he : ∀ᶠ y in 𝓝 z, w y ≠ 0 :=
    (hw.continuousOn.continuousAt (hU.mem_nhds hz)).eventually_ne hwz
  obtain ⟨O,hOsub,hO,hzO⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds hz) he)
  obtain ⟨K,hK,hzK,hKO⟩ := exists_compact_between (isCompact_singleton (x := z)) hO
    (singleton_subset_iff.mpr hzO)
  obtain ⟨b,hbone,hbzero,-⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    𝓘(ℝ,E) (n := (⊤ : ℕ∞)) (isClosed_singleton (x := z)) hzK
  have hbs : tsupport b ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro y hy
    by_contra hn
    exact hy (hbzero y hn)
  have hbc : HasCompactSupport (b : E → ℝ) := hK.of_isClosed_subset (isClosed_tsupport b) hbs
  have hwO : ContDiffOn ℝ ∞ (fun y => (w y)⁻¹) O :=
    (hw.mono (fun _ hy => (hOsub hy).1)).inv (fun y hy => (hOsub hy).2)
  let τ : 𝓢(E,ℝ) := schwartz hO hwO b.contMDiff.contDiff hbc (hbs.trans hKO)
  have hτs : tsupport τ ⊆ tsupport b := tsupport_smul_subset_left _ _
  have hbn : ∀ᶠ y in 𝓝 z, b y = 1 :=
    hbone.filter_mono (nhds_le_nhdsSet (mem_singleton z))
  obtain ⟨V,hVsub,hV,hzV⟩ := mem_nhds_iff.mp (inter_mem (hO.mem_nhds hzO) hbn)
  refine ⟨τ,hbc.of_isClosed_subset (isClosed_tsupport τ) hτs,
    hτs.trans (hbs.trans (hKO.trans (fun _ hy => (hOsub hy).1))),V,hV,hzV,
    fun _ hy => (hOsub (hVsub hy).1).1,fun y hy => ?_⟩
  change (b y • (w y)⁻¹) * w y = 1
  rw [(hVsub hy).2,one_smul,inv_mul_cancel₀ (hOsub (hVsub hy).1).2]
end TamingCompatibility.SchwartzCutoff

end
end

section
noncomputable section
namespace TamingCompatibility.SchwartzCutoff
open Set
open scoped ContDiff Topology SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma exists_one_near {U : Set E} (hU : IsOpen U) {p : E} (hp : p ∈ U) :
    ∃ φ : 𝓢(E,ℝ), HasCompactSupport (φ : E → ℝ) ∧ tsupport φ ⊆ U ∧
      ∃ W : Set E, IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ ∀ x ∈ W, φ x = 1 := by
  obtain ⟨φ,hφ,hφU,W,hW,hpW,hWU,hφone⟩ := exists_reciprocal
    hU (w := fun _ => (1 : ℝ)) contDiffOn_const hp one_ne_zero
  exact ⟨φ,hφ,hφU,W,hW,hpW,hWU,fun x hx => by simpa only [mul_one] using hφone x hx⟩

end TamingCompatibility.SchwartzCutoff

namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution MeasureTheory Set
open scoped SchwartzMap
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma memSobolevLoc_of_global (n : ℕ) {u : 𝓢'(E,F)} (hu : MemSobolev n 2 u) (U : Set E) :
    MemSobolevLoc U n u := fun g _ _ => memSobolev_nat_product n g hu

lemma memSobolevLoc_one_of_global {u : 𝓢'(E,F)} (hu : MemSobolev 1 2 u) (U : Set E) :
    MemSobolevLoc U 1 u := by
  have hu' : MemSobolev (1 : ℕ) 2 u := by simpa only [Nat.cast_one] using hu
  simpa only [Nat.cast_one] using memSobolevLoc_of_global 1 hu' U

lemma schwartz_memSobolevLoc (g : 𝓢(E,F)) (n : ℕ) (U : Set E) :
    MemSobolevLoc U n (g : 𝓢'(E,F)) := memSobolevLoc_of_global n g.memSobolev U

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
