import Mathlib.Topology.CompactOpen
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Group.Basic

namespace OAI

/-! # Compact families of flow segments remain in an open domain -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {G V : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def flowSegmentPoint (Exp : V → G) (v : V) (z : (ℝ × ℝ) × G) (r : ℝ) : G :=
  z.2 * Exp (((1 - r) * z.1.1 + r * z.1.2) • v)

def flowSegmentDomain (U : Set G) (Exp : V → G) (v : V) : Set ((ℝ × ℝ) × G) :=
  {z | ∀ r ∈ Icc (0 : ℝ) 1, flowSegmentPoint Exp v z r ∈ U}

theorem isOpen_flowSegmentDomain (U : Set G) (hU : IsOpen U)
    (Exp : V → G) (hExp : Continuous Exp) (v : V) :
    IsOpen (flowSegmentDomain U Exp v) := by
  let F : ((ℝ × ℝ) × G) → C(ℝ, G) := fun z =>
    ⟨flowSegmentPoint Exp v z, by
      change Continuous (fun r : ℝ => z.2 * Exp (((1 - r) * z.1.1 + r * z.1.2) • v))
      fun_prop⟩
  have hc : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : ((ℝ × ℝ) × G) × ℝ => flowSegmentPoint Exp v p.1 p.2)
    dsimp [flowSegmentPoint]
    fun_prop
  exact (ContinuousMap.continuous_compactOpen.mp hc (Icc (0 : ℝ) 1) isCompact_Icc U hU)

theorem eventually_compact_flowSegments
    (U : Set G) (hU : IsOpen U) (Exp : V → G) (hExp : Continuous Exp)
    (v : ℕ → V) {v₀ : V} (hv : Tendsto v atTop (𝓝 v₀))
    (K : Set ((ℝ × ℝ) × G)) (hK : IsCompact K)
    (hKU : K ⊆ flowSegmentDomain U Exp v₀) :
    ∀ᶠ n in atTop, K ⊆ flowSegmentDomain U Exp (v n) := by
  let F : V → C(((ℝ × ℝ) × G) × ℝ, G) := fun w =>
    ⟨fun p => flowSegmentPoint Exp w p.1 p.2, by dsimp [flowSegmentPoint]; fun_prop⟩
  have hc : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : V × (((ℝ × ℝ) × G) × ℝ) =>
      flowSegmentPoint Exp p.1 p.2.1 p.2.2)
    dsimp [flowSegmentPoint]
    fun_prop
  have hmaps : MapsTo (F v₀) (K ×ˢ Icc (0 : ℝ) 1) U := by
    rintro ⟨z, r⟩ ⟨hz, hr⟩
    exact hKU hz r hr
  have he := ContinuousMap.tendsto_nhds_compactOpen.mp
    (hc.continuousAt.tendsto.comp hv) (K ×ˢ Icc (0 : ℝ) 1)
    (hK.prod isCompact_Icc) U hU hmaps
  filter_upwards [he] with n hn z hz r hr
  exact hn (x := (z, r)) ⟨hz, hr⟩

end PolycyclicRecognition

end

end OAI
