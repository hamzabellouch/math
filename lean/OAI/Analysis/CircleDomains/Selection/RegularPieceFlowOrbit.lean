import OAI.Analysis.CircleDomains.Selection.RegularPieceFlow
import Mathlib.Analysis.Calculus.Deriv.Shift

namespace OAI

/-! Time translation and exact orbit identities for the constructed
regular-level flow. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma CompactRegularPieceFlow.trajectory_shift {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x : {z // z ∈ K}) (s t : ℝ) :
    F.trajectory ⟨F.trajectory x s,F.member x s⟩ t = F.trajectory x (t+s) := by
  have h := ODE_solution_unique_univ (v := fun _ : ℝ => F.field)
    (s := fun _ : ℝ => (univ : Set ℂ)) (t₀ := 0)
    (fun _ => F.lipschitz.lipschitzOnWith)
    (fun u => ⟨F.equation ⟨F.trajectory x s,F.member x s⟩ u,mem_univ _⟩)
    (fun u => ⟨(F.equation x (u+s)).comp_add_const u s,mem_univ _⟩)
    (by rw [F.initial,zero_add])
  exact congrFun h t

lemma CompactRegularPieceFlow.trajectory_shift_of_eq {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) {x y : {z // z ∈ K}} {s : ℝ}
    (hxy : F.trajectory x s = y.val) (t : ℝ) :
    F.trajectory y t = F.trajectory x (t+s) := by
  have hy : (⟨F.trajectory x s,F.member x s⟩ : {z // z ∈ K}) = y := Subtype.ext hxy
  simpa only [hy] using F.trajectory_shift x s t

lemma CompactRegularPieceFlow.range_eq_of_mem {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) {x y : {z // z ∈ K}}
    (hy : y.val ∈ range (F.trajectory x)) :
    range (F.trajectory y) = range (F.trajectory x) := by
  obtain ⟨s,hs⟩ := hy
  ext z
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t+s,(F.trajectory_shift_of_eq hs t).symm⟩
  · rintro ⟨t,rfl⟩
    refine ⟨t-s,?_⟩
    rw [F.trajectory_shift_of_eq hs,sub_add_cancel]

lemma CompactRegularPieceFlow.periodic_of_return {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x : {z // z ∈ K}) {p : ℝ}
    (hp : F.trajectory x p = x.val) : Periodic (F.trajectory x) p := by
  intro t
  exact (F.trajectory_shift_of_eq hp t).symm

lemma CompactRegularPieceFlow.orbits_eq_or_disjoint {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x y : {z // z ∈ K}) :
    range (F.trajectory x) = range (F.trajectory y) ∨
      Disjoint (range (F.trajectory x)) (range (F.trajectory y)) := by
  by_cases h : Disjoint (range (F.trajectory x)) (range (F.trajectory y))
  · exact Or.inr h
  · obtain ⟨z,hzx,hzy⟩ := Set.not_disjoint_iff.mp h
    let w : {z // z ∈ K} := ⟨z,by obtain ⟨t,rfl⟩ := hzx; exact F.member x t⟩
    have h1 : range (F.trajectory w) = range (F.trajectory x) := F.range_eq_of_mem hzx
    have h2 : range (F.trajectory w) = range (F.trajectory y) := F.range_eq_of_mem hzy
    exact Or.inl (h1.symm.trans h2)

end CircleDomainRigidity

end

end OAI
