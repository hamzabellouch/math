import Mathlib
import OAI.Analysis.SymmetricDomains.CriticalCountableCharts
import OAI.Analysis.SymmetricDomains.SupportedPositiveFiberVarying

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
open Set Filter Topology MeasureTheory
open scoped Classical

theorem actual_positive_maximizer_fiber
    {I : Type*} [Countable I] {N : ℕ}
    (P : MvPolynomial (Fin N) ℂ) (K : Set (Affine N)) (hK : IsClosed K)
    (d : I → ℕ) (B : ∀ i, Set (Fin (d i) → ℝ)) (hB : ∀ i, IsOpen (B i))
    (q : ∀ i, (Fin (d i) → ℝ) → Affine N)
    (hq : ∀ i, ContDiffOn ℝ 2 (q i) (B i))
    (hqK : ∀ i, MapsTo (q i) (B i) K)
    (hP : ∀ i x, x ∈ B i → MvPolynomial.eval (q i x) P ≠ 0)
    (hi : ∀ i x, x ∈ B i → Function.Injective (fderiv ℝ (q i) x))
    (bad : ∀ i, Set (Fin (d i) → ℝ)) (hbad : ∀ i, volume (bad i) = 0)
    (hcover : ∀ a : Affine N →L[ℂ] ℂ, ∃ i x, x ∈ B i ∧
      IsMaxOn (parameterPotential P a) K (q i x)) :
    ∃ i, ∃ (c : ActualCriticalChart P (q i)) (x : Fin (d i) → ℝ), c.base ⊆ B i ∧ x ∈ c.base ∧ x ∉ bad i ∧
      volume (Prod.mk x ⁻¹' c.maxLocus K) ≠ 0 := by
  choose C hCc hCB hcov using fun i => actual_critical_countable_charts P (B i) (hB i)
    (q i) (hq i) (hP i) (hi i)
  let : ∀ i, Countable (C i) := fun i => (hCc i).to_subtype
  let J := (i : I) × C i
  let E : J → Type := fun j => Fin (d j.1) → ℝ
  let F : J → Type := fun j => Fin j.2.val.fiberDim → ℝ
  let S (j : J) := j.2.val.maxLocus K
  let A (j : J) := j.2.val.param
  let : MeasurableSpace (Affine N →L[ℂ] ℂ) := borel _
  let ρ : Measure (Affine N →L[ℂ] ℂ) := Measure.addHaar
  have hρ : ρ univ ≠ 0 := by
    exact (isOpen_univ.measure_pos ρ Set.univ_nonempty).ne'
  have hall : univ ⊆ ⋃ j : J, A j '' S j := by
    intro a _
    obtain ⟨i,x,hx,hm⟩ := hcover a
    obtain ⟨c,hc,hxc⟩ := mem_iUnion₂.mp (hcov i hx)
    have hcrit := actual_maximizer_critical P (B i) (hB i) (q i) K (hqK i) (hP i) hx
      (((hq i x hx).contDiffAt ((hB i).mem_nhds hx)).differentiableAt (by norm_num)) a hm
    have heq := (realCriticalMatrix_eq_iff (q i) (parameterLogBase P ∘ q i)
      (((hq i x hx).contDiffAt ((hB i).mem_nhds hx)).differentiableAt (by norm_num))
      (((parameterLogBase_contDiffAt P (hP i x hx) (r := 1)).differentiableAt one_ne_zero).comp x
        (((hq i x hx).contDiffAt ((hB i).mem_nhds hx)).differentiableAt (by norm_num))) a).mp hcrit
    have har : a ∈ range (fun k => c.param (x,k)) := (c.range_param x hxc).symm ▸ heq
    obtain ⟨k,hk⟩ := har
    refine mem_iUnion.mpr ⟨⟨i,c,hc⟩,⟨(x,k),?_,hk⟩⟩
    exact ⟨hxc,hqK i hx,by simpa only [hk] using hm⟩
  obtain ⟨j,x,hxgood,hxpos⟩ := supported_positive_fiber_varying ρ E F
    (fun _ => volume) (fun _ => volume) (fun j => j.2.val.split.symm)
    S (fun j => j.2.val.measurableSet_maxLocus hK) A
    (fun j => j.2.val.differentiableOn_param_maxLocus K) (fun j => bad j.1)
    (fun j => hbad j.1) univ hρ hall
  have hxbase : x ∈ j.2.val.base := by
    by_contra hn
    apply hxpos
    have he : Prod.mk x ⁻¹' S j = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro k hk
      exact hn hk.1
    rw [he,measure_empty]
  exact ⟨j.1,j.2.val,x,hCB j.1 j.2.val j.2.property,hxbase,hxgood,hxpos⟩

end Release061

end

end OAI
