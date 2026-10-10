import OAI.GroupTheory.PolycyclicRecognition.Algebra.AdmissibleGeneratorWords
import Mathlib.Topology.Connected.LocallyConnected

namespace OAI

/-! # Connected neighborhoods admit one time interval for finitely many flows -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {G V I : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem flowLineBase_rescale
    (U : Set G) (Exp : V → G) (v : V) {T : ℝ} (hT : 0 < T) (g : G) :
    g ∈ flowLineBase U Exp (T • v) 1 ↔ g ∈ flowLineBase U Exp v T := by
  constructor
  · intro h s hs
    have hr : s / T ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hs.1 hT.le, (div_le_one hT).mpr hs.2⟩
    have hh := h (s / T) hr
    simpa only [smul_smul, div_mul_cancel₀ _ hT.ne'] using hh
  · intro h r hr
    have hs : r * T ∈ Icc (0 : ℝ) T :=
      ⟨mul_nonneg hr.1 hT.le, by nlinarith [hr.2]⟩
    simpa only [smul_smul] using h (r * T) hs

theorem exists_connected_flow_neighborhood
    [LocallyConnectedSpace G] [Finite I]
    (Ω : Set G) (hΩ : IsOpen Ω) (Exp : V → G) (hExp : Continuous Exp)
    (hExp0 : Exp 0 = 1) (X : I → V) {g : G} (hg : g ∈ Ω) :
    ∃ T : ℝ, 0 < T ∧ ∃ N : Set G, IsOpen N ∧ g ∈ N ∧ IsConnected N ∧ N ⊆ Ω ∧
      ∀ i, N ⊆ flowLineBase Ω Exp (X i) T := by
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, g ∈ flowLineBase Ω Exp (t • X i) 1 :=
    eventually_all.mpr (fun i => eventually_short_flowLineBase hΩ hExp hExp0 (X i) hg)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hsmall
  have hhalf : 0 < ε / 2 := half_pos hε
  have hd : dist (ε / 2) (0 : ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hhalf]
    linarith
  have hpoint (i : I) : g ∈ flowLineBase Ω Exp (X i) (ε / 2) :=
    (flowLineBase_rescale Ω Exp (X i) hhalf g).mp (he hd i)
  let Q := Ω ∩ ⋂ i, flowLineBase Ω Exp (X i) (ε / 2)
  have hQo : IsOpen Q := hΩ.inter
    (isOpen_iInter_of_finite fun i => isOpen_flowLineBase Ω hΩ Exp hExp (X i) (ε / 2))
  have hgQ : g ∈ Q := ⟨hg, mem_iInter.mpr hpoint⟩
  obtain ⟨N, hNQ, hNo, hgN, hNc⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance g Q (hQo.mem_nhds hgQ)
  refine ⟨ε / 2, hhalf, N, hNo, hgN, hNc, fun x hx => (hNQ hx).1, ?_⟩
  intro i x hx
  exact mem_iInter.mp (hNQ hx).2 i

end PolycyclicRecognition

end

end OAI
