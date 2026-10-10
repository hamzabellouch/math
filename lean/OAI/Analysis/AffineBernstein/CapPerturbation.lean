import Mathlib
import OAI.Analysis.AffineBernstein.ConvexSmoothMax

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology

lemma isOpen_graphSublevel {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContinuousOn u Ω) (b : ℝ) :
    IsOpen {x | x ∈ Ω ∧ u x < b} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hg := (hu.continuousAt (hΩ.mem_nhds hx.1)).preimage_mem_nhds (Iio_mem_nhds hx.2)
  exact Filter.inter_mem (hΩ.mem_nhds hx.1) hg

lemma isCompact_lower_graphSublevel {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hu : ContinuousOn u Ω) {b d : ℝ} (hdb : d ≤ b)
    (hK : IsCompact {x | x ∈ Ω ∧ u x ≤ b}) :
    IsCompact {x | x ∈ Ω ∧ u x ≤ d} := by
  have hc : ContinuousOn u {x | x ∈ Ω ∧ u x ≤ b} := hu.mono fun _ hx => hx.1
  have hi := hc.lowerSemicontinuousOn.isCompact_inter_preimage_Iic hK d
  have he : {x | x ∈ Ω ∧ u x ≤ b} ∩ u ⁻¹' Iic d = {x | x ∈ Ω ∧ u x ≤ d} := by
    ext x
    exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1,hx.2.trans hdb⟩,hx.2⟩⟩
  simpa only [he] using hi

/-- A genuine compact smooth convex-cap replacement, with no stationarity or
area conclusion assumed. -/
theorem exists_cap_perturbation {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u q : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hq : ContDiffOn ℝ ∞ q Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) {b ε : ℝ} (hε : 0 < ε)
    (hK : IsCompact {x | x ∈ Ω ∧ u x ≤ b})
    (hqtop : ∀ x, x ∈ Ω → u x < b → q x ≤ b-2*ε)
    (hqp : ∀ x, x ∈ Ω → u x < b → (hessian q x).PosDef) :
    ∃ η : Space n → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ {x | x ∈ Ω ∧ u x < b} ∧
      (∀ x ∈ Ω, (hessian (fun y => u y+η y) x).PosDef) ∧
      ∀ x, x ∈ Ω → u x < b → ε ≤ q x-u x → u x+η x = q x := by
  let E : Set (Space n) := {x | x ∈ Ω ∧ u x < b}
  let K : Set (Space n) := {x | x ∈ Ω ∧ u x ≤ b-ε}
  let η := E.indicator (fun x => smoothPositivePart ε (q x-u x))
  have hE : IsOpen E := isOpen_graphSublevel hΩ hu.continuousOn b
  have hKE : K ⊆ E := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 (by linarith)⟩
  have hKc : IsCompact K := isCompact_lower_graphSublevel hu.continuousOn (by linarith) hK
  have hEΩ : E ⊆ Ω := fun _ hx => hx.1
  have hsm : ContDiffOn ℝ ∞ (fun x => smoothPositivePart ε (q x-u x)) E :=
    (smoothPositivePart_smooth ε).comp_contDiffOn ((hq.sub hu).mono hEΩ)
  have hzero : ∀ x ∈ E, x ∉ K → smoothPositivePart ε (q x-u x) = 0 := by
    intro x hx hxn
    have hl : b-ε < u x := lt_of_not_ge (fun hl => hxn ⟨hx.1,hl⟩)
    exact smoothPositivePart_zero hε (by linarith [hqtop x hx.1 hx.2])
  obtain ⟨hη,hηc,hηK⟩ := contDiff_indicator_of_compact hE hKc hKE hsm hzero
  change ContDiff ℝ ∞ η at hη
  change HasCompactSupport η at hηc
  change tsupport η ⊆ K at hηK
  have hηE := hηK.trans hKE
  refine ⟨η,hη,hηc,hηE,?_,?_⟩
  · intro x hx
    by_cases hxE : x ∈ E
    · have he : (fun y => u y+η y) =ᶠ[𝓝 x]
          (fun y => u y+smoothPositivePart ε (q y-u y)) := by
        filter_upwards [hE.mem_nhds hxE] with y hy
        simp only [η, Set.indicator_of_mem hy]
      rw [hessian_eq_of_eventuallyEq he]
      exact hessian_convex_smooth_max_posDef hΩ hu hq hε hx (hp x hx) (hqp x hx hxE.2)
    · have hn : x ∉ tsupport η := fun hh => hxE (hηE hh)
      have he : (fun y => u y+η y) =ᶠ[𝓝 x] u := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
        simp only [Pi.zero_apply] at hy
        simp only [hy,add_zero]
      rw [hessian_eq_of_eventuallyEq he]
      exact hp x hx
  · intro x hx hxb hbar
    have hxE : x ∈ E := ⟨hx,hxb⟩
    simp only [η, Set.indicator_of_mem hxE, smoothPositivePart_identity hε hbar]
    ring

end AffineBernstein
end

end OAI
