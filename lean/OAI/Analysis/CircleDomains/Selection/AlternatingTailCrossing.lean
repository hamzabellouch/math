import OAI.Analysis.CircleDomains.Topology.DiskCrossingInput
import OAI.Analysis.CircleDomains.Topology.LastEntryContinua

namespace OAI

/-! Alternating last-entry path tails cross in the interior of the disk. -/

open Set Function Metric

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem alternating_lastEntry_tails_intersect (hcross : UnitDiskAlternatingContinua)
    (V : Set X) (hV : IsOpen V) (f : X → ℂ)
    (hf : ContinuousOn f (closure V)) (hfinj : InjOn f (closure V))
    (hfdisk : MapsTo f (closure V) (closedBall 0 1))
    (γ : Fin 4 → C(PathTime, X))
    (hstart : ∀ i, γ i ⊥ ∉ V) (hend : ∀ i, γ i ⊤ ∈ V)
    (h02 : γ 0 ⊤ = γ 2 ⊤) (h13 : γ 1 ⊤ = γ 3 ⊤)
    (θ : Fin 4 → UnitAddCircle) (hθ : StrictMono (unitCircleCut ∘ θ))
    (hentry : ∀ i, f (γ i (lastEntryTime (γ i) V)) = standardCirclePoint (θ i)) :
    ∃ x ∈ V, (x ∈ lastEntryTail (γ 0) V ∨ x ∈ lastEntryTail (γ 2) V) ∧
      (x ∈ lastEntryTail (γ 1) V ∨ x ∈ lastEntryTail (γ 3) V) := by
  let A := lastEntryTail (γ 0) V ∪ lastEntryTail (γ 2) V
  let B := lastEntryTail (γ 1) V ∪ lastEntryTail (γ 3) V
  have hsub (i : Fin 4) : lastEntryTail (γ i) V ⊆ closure V :=
    lastEntryTail_subset_closure (γ i) hV (hstart i) (hend i)
  have hA : A ⊆ closure V := union_subset (hsub 0) (hsub 2)
  have hB : B ⊆ closure V := union_subset (hsub 1) (hsub 3)
  have hAc : IsCompact A := (isCompact_lastEntryTail (γ 0) V).union
    (isCompact_lastEntryTail (γ 2) V)
  have hBc : IsCompact B := (isCompact_lastEntryTail (γ 1) V).union
    (isCompact_lastEntryTail (γ 3) V)
  have hAn : IsConnected A := isConnected_union_lastEntryTails (γ 0) (γ 2) V h02
  have hBn : IsConnected B := isConnected_union_lastEntryTails (γ 1) (γ 3) V h13
  have hmem (i : Fin 4) : standardCirclePoint (θ i) ∈ f '' lastEntryTail (γ i) V :=
    ⟨_, lastEntry_mem_tail (γ i) V, hentry i⟩
  obtain ⟨z, ⟨x, hx, hfx⟩, y, hy, hfy⟩ := hcross (f '' A) (f '' B)
    (hAc.image_of_continuousOn (hf.mono hA)) (hAn.image f (hf.mono hA))
    (hBc.image_of_continuousOn (hf.mono hB)) (hBn.image f (hf.mono hB))
    (by rintro _ ⟨x, hx, rfl⟩; exact hfdisk (hA hx))
    (by rintro _ ⟨y, hy, rfl⟩; exact hfdisk (hB hy)) θ hθ
    (image_mono subset_union_left (hmem 0)) (image_mono subset_union_right (hmem 2))
    (image_mono subset_union_left (hmem 1)) (image_mono subset_union_right (hmem 3))
  have hxy : x = y := hfinj (hA hx) (hB hy) (hfx.trans hfy.symm)
  subst y
  have hne (i j : Fin 4) (hij : i ≠ j) :
      γ i (lastEntryTime (γ i) V) ≠ γ j (lastEntryTime (γ j) V) := by
    intro he
    have hh := congrArg f he
    rw [hentry i, hentry j] at hh
    exact hij (hθ.injective (congrArg unitCircleCut (standardCirclePoint_injective hh)))
  have hout (i j : Fin 4) (hij : i ≠ j)
      (hxi : x ∈ lastEntryTail (γ i) V) (hxj : x ∈ lastEntryTail (γ j) V) : x ∈ V := by
    by_contra hv
    exact hne i j hij ((lastEntryTail_outside (γ i) V hxi hv).symm.trans
      (lastEntryTail_outside (γ j) V hxj hv))
  refine ⟨x, ?_, hx, hy⟩
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hout 0 1 (by decide) hx hy
  · exact hout 0 3 (by decide) hx hy
  · exact hout 2 1 (by decide) hx hy
  · exact hout 2 3 (by decide) hx hy

end CircleDomainRigidity

end

end OAI
