import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.MarkingTwoScans

namespace OAI

section
namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
noncomputable section
variable {Ω Γ α ι : Type*} [Fintype Ω] [Fintype Γ] [Fintype α] [Fintype ι]

def selectedDeficit (p : Law Ω) (θ : Ω → Γ) (F : Ω → ι → α)
    (S : Γ → Finset ι) (J : ℝ) : ℝ :=
  ∑ z, (p.map θ).mass z*((S z).card*J-entropy (((p.cond θ z).map F).restrict (S z)))
end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Marking
open scoped BigOperators Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] [Finite K]

abbrev jointJ (K : Type*) (d : ℕ) : ℝ := Real.log (64*(Nat.card K:ℝ)^d)

def sourceMessage {Ω Γ : Type*} {N : ℕ} (C : Ω → Γ)
    (F : Ω → Fin N → ProjectivePair (K:=K) (V:=V)) :
    Ω → TwoMessage (K:=K) (V:=V) Γ N :=
  Selection.markingMessage C (fun x => twoMask (Nat.card K) (F x)) bothExpensive F

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

def excessCost {N : ℕ} (p : Selection.Law Ω) (C : Ω → Γ)
    (F : Ω → Fin N → ProjectivePair (K:=K) (V:=V)) (Jprev J₀ : ℝ) : ℝ :=
  Selection.entropy (p.map C)+Real.log (Fintype.card (TwoMask (K:=K) (V:=V) N))+
    N*J₀-Selection.entropy (p.map F)+
    (∑ x, p.mass x*((bothExpensive (twoMask (Nat.card K) (F x))).card:ℝ))*(Jprev-J₀)

theorem twoScan_subset_deficit {N n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : Selection.Law Ω) (C : Ω → Γ) (F : Ω → Fin N → ProjectivePair (K:=K) (V:=V))
    (D : Γ → Fin N → Finset (ProjectivePair (K:=K) (V:=V))) (Jprev : ℝ)
    (hcons : ∀ x, p.mass x≠0 → ScanConsistent ((List.ofFn (F x)).map toScan))
    (hinc : ∀ x, p.mass x≠0 → ∀ i, Incidence.Incident (F x i).1 (F x i).2)
    (hD : ∀ x, p.mass x≠0 → ∀ i, F x i∈D (C x) i)
    (hprev : ∀ c i, Real.log (D c i).card≤Jprev)
    (S : TwoMessage (K:=K) (V:=V) Γ N → Finset (Fin N))
    (hS : ∀ z, Disjoint (S z) (bothExpensive z.2.2)) :
    0 ≤ Selection.selectedDeficit p (sourceMessage C F) F S (jointJ K (n+2)) ∧
      Selection.selectedDeficit p (sourceMessage C F) F S (jointJ K (n+2)) ≤
        excessCost p C F Jprev (jointJ K (n+2)) := by
  have hh := Selection.marking_subset_deficit p C (fun x => twoMask (Nat.card K) (F x))
    bothExpensive F D cheapBoth Jprev (jointJ K (n+2)) hD hprev
    (fun x hx i hi => cheapBoth_mem C F x (hcons x hx) (hinc x hx) i hi)
    (fun z i _ => cheapBoth_log_card hdim z i) S hS
  change 0≤_ ∧ _≤_ at hh
  convert hh using 1 <;> simp only [Selection.selectedDeficit,sourceMessage,excessCost,Fintype.card_fin]
  all_goals congr!

end
end SharpLogRamsey.Marking

end

end OAI
