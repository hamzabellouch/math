import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.AuxiliaryFamilies
import OAI.Combinatorics.SharpRamsey.Selection.FreshFamilies

namespace OAI

section
namespace SharpLogRamsey.ReadyTests
open Finset Real Incidence Validation SupportMixtures Selection
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

structure Call (S : Finset (Projectivization K V)) where
  source : Finset (Projectivization K V)
  proposal : Finset (Projectivization K V)
  targetOriginal : Finset (Projectivization K (Module.Dual K V))
  target : Finset (Projectivization K (Module.Dual K V))
  domain : Finset (Projectivization K (Module.Dual K V))
  overhead : ℝ
  source_nonempty : source.Nonempty
  source_original : source ⊆ S
  source_proposal : source ⊆ proposal
  target_nonempty : target.Nonempty
  target_original : target ⊆ targetOriginal
  target_domain : target ⊆ domain
  target_fraction : (targetOriginal.card : ℝ) ≤ 2 * target.card
  source_fraction : (S.card : ℝ) ≤ 2 * source.card
  proposal_ratio : (proposal.card : ℝ) ≤ exp overhead * source.card
  sparse : (incidenceCount S targetOriginal : ℝ) ≤
    (S.card : ℝ) * targetOriginal.card / (40000 * Nat.card K)

def Call.loss {S : Finset (Projectivization K V)} (c : Call S) (n : ℕ)
    (y : Projectivization K (Module.Dual K V)) : ℝ :=
  let q : ℝ := Nat.card K
  let h := scheduleLength q c.domain.card c.target.card
  let m := scheduleCutoff q c.overhead h
  PublicTables.integral (rowLaw c.proposal (c.source_nonempty.mono c.source_proposal) h)
    (implementAccept c.source
      (GoodCap SharpLogRamsey.Incidence.Incident q c.domain c.target (2000*q^(n+3)/S.card)))
    (fun z => if ¬pass SharpLogRamsey.Incidence.Incident q z y then 1 else 0) m

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))] in
lemma kernel_eq_uniform (S : Finset (Projectivization K V)) :
    kernel S = uniformMass S := by
  funext x
  simp only [kernel, uniformMass, one_div]

lemma Call.loss_bound {S : Finset (Projectivization K V)} (c : Call S)
    {n : ℕ} (hdim : Module.finrank K V = n+3)
    (y : Projectivization K (Module.Dual K V)) :
    c.loss n y ≤ 12*(Nat.card K:ℝ) *
      (∑ x, kernel S x * (if SharpLogRamsey.Incidence.Incident x y then 1 else 0)) := by
  have h := (scheduled_from_original hdim S c.source c.proposal
    (c.source_nonempty.mono c.source_original) c.source_nonempty
    c.source_original c.source_proposal c.targetOriginal c.target c.domain
    c.target_nonempty c.target_original c.target_domain c.target_fraction
    2 c.overhead (by norm_num) c.source_fraction c.proposal_ratio
    (by convert c.sparse using 1; ring)).2.2 y
  norm_num only [show (1000:ℝ)*2=2000 by norm_num,
    show (6:ℝ)*2=12 by norm_num] at h
  simpa only [Call.loss, sum_filter, kernel_eq_uniform, mul_ite, mul_one, mul_zero] using h

def loss {Ξ : Type*} [Fintype Ξ] (ρ : Selection.Law Ξ)
    {S : Finset (Projectivization K V)} (ready : Ξ → Option (Call S))
    (n : ℕ) (y : Projectivization K (Module.Dual K V)) : ℝ :=
  ∑ ξ, ρ.mass ξ * (ready ξ).elim 0 (fun c => c.loss n y)

lemma loss_bound {Ξ : Type*} [Fintype Ξ] (ρ : Selection.Law Ξ)
    {S : Finset (Projectivization K V)} (ready : Ξ → Option (Call S))
    {n : ℕ} (hdim : Module.finrank K V = n+3)
    (y : Projectivization K (Module.Dual K V)) :
    loss ρ ready n y ≤ 12*(Nat.card K:ℝ) *
      (∑ x, kernel S x * (if SharpLogRamsey.Incidence.Incident x y then 1 else 0)) := by
  let B := 12*(Nat.card K:ℝ) *
      (∑ x, kernel S x * (if SharpLogRamsey.Incidence.Incident x y then 1 else 0))
  have hB : 0 ≤ B := by
    dsimp [B]
    apply mul_nonneg (by positivity)
    exact sum_nonneg (fun x _ => mul_nonneg (kernel_nonneg _ _) (by split_ifs <;> norm_num))
  unfold loss
  calc
    _ ≤ ∑ ξ, ρ.mass ξ * B := by
      apply sum_le_sum
      intro ξ _
      apply mul_le_mul_of_nonneg_left _ (ρ.nonneg ξ)
      cases hc : ready ξ with
      | none => exact hB
      | some c => exact c.loss_bound hdim y
    _ = B := by rw [←sum_mul,ρ.total,one_mul]

end
end SharpLogRamsey.ReadyTests

end

end OAI
