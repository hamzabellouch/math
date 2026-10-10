import OAI.Analysis.CircleDomains.Uniformization.MixedAssignedLimit

namespace OAI

/-! A mixed limit retains the exact real subfamily limit. Reindexing the
finite terminal assignment preserves its point labels, so all previously
proved real-barrier conclusions apply to this same limit map. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem PhysicalTerminalDisks.exists_reindexed_assignment
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere}
    {τ : S → Sphere} {O : S → Set Sphere} {A B : Set S}
    (hAB : A = B)
    (T : PhysicalTerminalDisks G π (π '' Gᶜ) (fun s : A => τ s) (fun s => O s))
    (T' : PhysicalTerminalDisks G π (π '' Gᶜ) (fun s : B => τ s) (fun s => O s))
    (hT : HEq T T') {f : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T.H f V) :
    ∃ a' : TerminalComponentAssignment T'.H f V,
      ∀ (i : A) (j : B), (i : S) = j → a.point i = a'.point j := by
  subst B
  have hTT : T = T' := eq_of_heq hT
  subst T'
  exact ⟨a, fun i j h => congrArg a.point (Subtype.ext h)⟩

 def TerminalComponentAssignment.changeMap
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f f' : Sphere → Sphere} {V V' : Set Sphere}
    (a : TerminalComponentAssignment T f V) (hf : f = f') (hV : V = V') :
    TerminalComponentAssignment T f' V' := by
  subst f'
  subst V'
  exact a

 theorem TerminalComponentAssignment.changeMap_point
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f f' : Sphere → Sphere} {V V' : Set Sphere}
    (a : TerminalComponentAssignment T f V) (hf : f = f') (hV : V = V') (i : I) :
    (a.changeMap hf hV).point i = a.point i := by
  subst f'
  subst V'
  rfl

namespace FiniteTransfer

variable {S C : Type*} [LinearOrder C]
  {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ}
  {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C}
  {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}
  {M : MixedModelExhaustion d data retained O ε ρ}

 theorem AssignedMixedModelLimit.exists_real_assignment
    (L : AssignedMixedModelLimit M) (n : ℕ) :
    ∃ a : TerminalComponentAssignment (M.real.stages n).terminals.H
      (M.real.stages n).forward (M.real.stages n).domain,
      ∀ (i : (M.stages n).indices) (j : (M.real.stages n).indices),
        (i : S) = j → (L.assignment n).point i = a.point j := by
  obtain ⟨a, ha⟩ := PhysicalTerminalDisks.exists_reindexed_assignment (M.same_indices n)
    (M.stages n).terminals (M.real.stages n).terminals (M.same_terminals n) (L.assignment n)
  refine ⟨a.changeMap (M.same_forward n) (M.same_domain n), ?_⟩
  intro i j hij
  rw [TerminalComponentAssignment.changeMap_point]
  exact ha i j hij

 def AssignedMixedModelLimit.toReal (L : AssignedMixedModelLimit M) : AssignedRealModelLimit M.real := by
  classical
  choose a ha using L.exists_real_assignment
  refine {
    assignment := a
    subsequence := L.subsequence
    function := L.function
    center := L.center
    radius := L.radius
    cores := L.cores
    contours := L.contours
    strict := L.strict
    converges := ?_
    normalized := L.normalized
    conformal := L.conformal
    bounds := L.bounds
    nested := L.nested
    exhausts := L.exhausts
    boundary := L.boundary
    disjoint := L.disjoint
    image_core := L.image_core
    side := L.side
    marked := ?_ }
  · simpa only [M.same_forward] using L.converges
  · intro s
    obtain ⟨i, p, hp, hsrc, htgt, hsub, hlim⟩ := L.marked s
    refine ⟨i, p, hp, hsrc, htgt, hsub, ?_⟩
    have he (n : ℕ) : (L.assignment (L.subsequence n)).point
        (M.markIndex (L.subsequence n) s) =
        (a (L.subsequence n)).point (M.real.markIndex (L.subsequence n) s) :=
      ha _ _ _ rfl
    simpa only [he, M.same_domain] using hlim

end FiniteTransfer
end CircleDomainRigidity

end

end OAI
