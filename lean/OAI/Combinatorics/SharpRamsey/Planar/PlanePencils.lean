import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.PreparedSparse

namespace OAI

section
namespace SharpLogRamsey.PreparedGeometry
open Finset PreparedRow PreparedProjectiveGeometry PreparedTypical
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPlanePencils_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPlanePencils_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _

lemma plane_neighbors_empty (hdim : Module.finrank K V=3)
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c a : ℝ) (ha : 0<a)
    (A : Finset (Projectivization K (Module.Dual K V))) (hA : A⊆pencil x)
    (H : Projectivization K (Module.Dual K V)) (hH : H∈A) :
    largeNeighbors S x c a A H=∅ := by
  apply filter_eq_empty_iff.mpr
  rintro J hJ ⟨hne,hh⟩
  have he := overlap_plane_zero hdim S x c H J hne
    (mem_filter.mp (hA hH)).2 (mem_filter.mp (hA hJ)).2
  linarith

theorem plane_pencils (hdim : Module.finrank K V=3)
    (R p h : ℕ) (hp : 0<p)
    (S O : Finset (Projectivization K V)) (x : Projectivization K V) (c L : ℝ≥0)
    (A : Finset (Projectivization K (Module.Dual K V))) (hA : A⊆pencil x)
    (f B C V₀ : ℝ) (hB : 0≤B)
    (htyp : ∀ H∈A,3/4≤outsideMass S O x c H ∧ outsideMass S O x c H≤2 ∧
      |outsideMass S O x c H-(1-f)|≤13/100)
    (hsq : (∑ H∈A,(outsideMass S O x c H-(1-f))^2)≤V₀)
    (hsqs : V₀≤C*B*Real.exp ((L:ℝ)/100))
    (hsqa : V₀≤B*Real.exp (((L:ℝ)*R)/100))
    (hcards : ((∑ i∈range 2,Nat.card K^i):ℝ)≤C*B^2)
    (hcarda : ((∑ i∈range 2,Nat.card K^i):ℝ)≤4*B^2)
    (hdir : (1:ℝ)≤4*B)
    (hdiag : C*2^R≤Real.exp ((L:ℝ)*R/20))
    (hpow : (2*(L:ℝ)^2)^R≤Real.exp ((L:ℝ)*R/25))
    (hsum : C^2*Real.exp ((L:ℝ)/50)≤Real.exp ((L:ℝ)*R/20))
    (htwo : 2≤Real.exp ((L:ℝ)*R/20))
    (hcert : MomentBudgetBridge.certificateOverhead p 0 ((L:ℝ)*R)≤Real.exp (2*((L:ℝ)*R)/25))
    (hshift : MomentBudgetBridge.shiftOverhead p 0≤Real.exp (2*((L:ℝ)*R)/25))
    (hpb : (p:ℝ)^2≤Real.exp (((L:ℝ)*R)/10))
    (hps : 2*(p:ℝ)+3≤Real.exp (((L:ℝ)*R)/10))
    (hh : 0<h) (hhs : h≤(R/2)/400) (hhe : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2) :
    SecondPencil 2 R S O x c L A f B C (∅ : Finset Unit) (fun _ => 0) ∧
    HighPencil 2 R p h S O x c L A f B (∅ : Finset Unit) (fun _ => 0) := by
  have hcover : ∀ H∈A,∀ J∈A,H≠J → 0<overlap (S\(O∪{x})) x c H J → False := by
    intro H hH J hJ hne hh
    have he := overlap_plane_zero hdim (S\(O∪{x})) x c H J hne
      (mem_filter.mp (hA hH)).2 (mem_filter.mp (hA hJ)).2
    linarith
  constructor
  · refine ⟨(fun H hH => (htyp H hH).1),(fun H hH => (htyp H hH).2.1),
      ?_,hsq.trans hsqs,hcards,?_,?_,?_,hdiag,hpow,?_,htwo⟩
    · intro H hH
      exact (htyp H hH).2.2.trans (by norm_num)
    · simp
    · intro H hH J hJ hne hh
      exact (hcover H hH J hJ hne hh).elim
    · simp
    · simpa using hsum
  · refine ⟨(fun H hH => (htyp H hH).1),(fun H hH => (htyp H hH).2.1),
      (fun H hH => (htyp H hH).2.2),hsq.trans hsqa,hcarda,?_,?_,?_,?_,?_,?_,
      ?_,?_,hpb,hps,hh,hhs,hhe⟩
    · simpa using hdir
    · simp
    · intro H hH J hJ hne hh
      exact (hcover H hH J hJ hne hh).elim
    · simp
    · simp
    · intro H hH
      have ha : (0:ℝ)<1/(100*(p:ℝ)) := by positivity
      rw [plane_neighbors_empty hdim (S\(O∪{x})) x c _ ha A hA H hH]
      simp only [card_empty,Nat.cast_zero]
      positivity
    · simpa using hcert
    · simpa using hshift

end
end SharpLogRamsey.PreparedGeometry

end

end OAI
