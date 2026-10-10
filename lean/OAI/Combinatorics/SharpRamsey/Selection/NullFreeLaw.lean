import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.FamilyAverages
import OAI.Combinatorics.SharpRamsey.Selection.ScheduledBanks

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {Ω : Type*} [Fintype Ω]

def Law.asPublic (μ : Law Ω) : PublicTables.Law Ω := ⟨μ.mass,μ.nonneg,μ.total⟩

lemma Law.nullFree_sum (μ : Law Ω) (f : Ω→ℝ) :
    (∑ ω : {ω // μ.mass ω≠0},μ.mass ω*f ω) = ∑ ω,μ.mass ω*f ω := by
  calc
    _ = ∑ ω∈univ.filter (fun ω=>μ.mass ω≠0),μ.mass ω*f ω :=
      (sum_subtype _ (by simp) _).symm
    _ = _ := by
      apply sum_subset (filter_subset _ _)
      intro ω hω hn
      have hh : μ.mass ω=0 := by simpa using hn
      simp [hh]

def Law.nullFree (μ : Law Ω) : Law {ω // μ.mass ω≠0} where
  mass ω := μ.mass ω
  nonneg ω := μ.nonneg ω
  total := by simpa only [mul_one,μ.total] using μ.nullFree_sum (fun _=>1)

lemma Law.nullFree_integral (μ : Law Ω) (f : Ω→ℝ) :
    (∑ ω,μ.nullFree.mass ω*f ω)=∑ ω,μ.mass ω*f ω := μ.nullFree_sum f

lemma Law.nullFree_positive (μ : Law Ω) (ω : {ω // μ.mass ω≠0}) : 0<μ.nullFree.mass ω :=
  lt_of_le_of_ne (μ.nonneg ω) (Ne.symm ω.property)

lemma Law.nullFree_public_integral (μ : Law Ω) (f : Ω→ℝ) :
    (∑ ω,μ.nullFree.asPublic.mass ω*f ω)=∑ ω,μ.mass ω*f ω := μ.nullFree_sum f

lemma Law.prod_sum_swap {A : Type*} [Fintype A] (μ : Law Ω) (ρ : Law A)
    (f : Ω→A→ℝ) :
    (∑ z,(μ.prod ρ).mass z*f z.1 z.2)=∑ a,ρ.mass a*(∑ ω,μ.mass ω*f ω a) := by
  simp only [Law.prod,Fintype.sum_prod_type,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intros
  ring

end
end SharpLogRamsey.Selection

end

end OAI
