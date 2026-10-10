import OAI.Probability.DilutedSpin.ScheduledRegularFrame

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {I : Type} [Fintype I] [DecidableEq I] {n : ℕ}

lemma partialKappa_ratio_bijective (T : PrescribedTree n) (q : I → T.Leaf)
    (hq : Function.Bijective q) (m : Fin (n+1) → ℝ) (u v : I) :
    partialKappa T m (Finset.univ.image q)/partialKappa T m ((insert v ({u}:Finset I)).image q)=
      partialKappa T m Finset.univ/partialKappa T m {q v,q u} := by
  classical
  rw [Finset.image_univ_of_surjective hq.2]
  simp only [Finset.image_insert,Finset.image_singleton]

end DilutedSpinGlass.PrescribedTree
namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
open scoped BigOperators
variable {α I : Type} [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]

omit [Fintype α] [DecidableEq α] in
/-- Exact grid-power cancellation for the actual delayed scheduled target,
with the canonical full-to-protected-pair kappa ratio. -/
theorem scheduled_relative_charge (H r d : ℕ) (k : ℕ+) (a : α)
    (C : Fin k → ReducedTopology) (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d)) (η : ℝ) (hη : 0<η)
    (heval : η≤((d+r+2:ℕ):ℝ)/((H+1+1+r+1+d:ℕ):ℝ)) :
    let L := H+1+1+r+1+d
    let Base := PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
    let Old := PrescribedTree.node k (fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
    let New := PrescribedTree.node k (fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1))
    let Target := heightCast (shiftedFrameHeight H r d) (splitFrame New (r+1) d)
    let S := splitFrame Old r d
    let B := shiftedPrefixDepths (stem Base r) d
    ∀ (q : I → Target.Leaf), Function.Bijective q → ∀ (u v : I), u≠v → ∀ l : ℕ,
    shiftedCharge B Target S l /
      |partialKappa Target (grid L 0 L) (Finset.univ.image q)/
        partialKappa Target (grid L 0 L) ((insert v ({u}:Finset I)).image q)| ≤
      chargeBound (2*(leaves S+l:ℕ)) ((B.card:ℝ)*(leaves S+l:ℕ)) l
        (2*branchingCount Base (fun _ => True)) / η^(branchExcess Target) := by
  dsimp only
  intro q hq u v huv l
  rw [partialKappa_ratio_bijective _ q hq]
  have hh := shiftedCharge_relative_bound (by omega : 0<H+1+1+r+1+d) _ _
    (splitFrame (.node k (fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val))) r d) l
    (q u) (q v) (fun h => huv (hq.1 h)) η hη
    (scheduled_frame_target_regular H r d k a C e Q η heval)
    (scheduled_frame_target_total H r d k a C e Q)
  simpa only [scheduled_frame_target_count] using hh

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
