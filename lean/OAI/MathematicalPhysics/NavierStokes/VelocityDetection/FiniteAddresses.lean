import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Stacks

namespace OAI

noncomputable section
namespace VelocityDetection.FiniteAddresses
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open Stacks

abbrev Box (N B : ℕ) := Fin N × Fin B × Fin B

def config {N B : ℕ} (c : Box N B) : Configuration (Fin N) :=
  ⟨c.1, c.2.1, c.2.2⟩

def sourceAddress {N B : ℕ} (c : Box N B) : ℕ := address B c.1 c.2.1 c.2.2

theorem sourceAddress_injective {N B : ℕ} (hB : 0 < B) :
    Injective (@sourceAddress N B) := by
  intro c d h
  obtain ⟨hi, hx, hy⟩ := address_injective hB c.2.1.isLt d.2.1.isLt c.2.2.isLt d.2.2.isLt h
  exact Prod.ext (Fin.ext hi) (Prod.ext (Fin.ext hx) (Fin.ext hy))

theorem sourceAddress_count {N B : ℕ} (c : Box N B) : sourceAddress c ≤ N * B ^ 2 :=
  address_le c.1.isLt c.2.1.isLt c.2.2.isLt

end VelocityDetection.FiniteAddresses
end

noncomputable section
namespace VelocityDetection.FiniteAddresses
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open Stacks
variable {N b : ℕ} (hb : 0 < b) (table : Fin N → Fin b → Option (Rule (Fin N) b))

def Active (B : ℕ) := {c : Box N B // (table c.1 ⟨c.2.2 % b, Nat.mod_lt _ hb⟩).isSome}

instance (B : ℕ) : Fintype (Active hb table B) := by
  classical
  unfold Active
  infer_instance

def rule {B : ℕ} (c : Active hb table B) : Rule (Fin N) b :=
  (table c.val.1 ⟨c.val.2.2 % b, Nat.mod_lt _ hb⟩).get c.property

theorem lookup_rule {B : ℕ} (c : Active hb table B) :
    table (config c.val).state ⟨(config c.val).rightStack % b, Nat.mod_lt _ hb⟩ =
      some (rule hb table c) := (Option.some_get c.property).symm

def target {B : ℕ} (c : Active hb table B) : Configuration (Fin N) :=
  applyRule (rule hb table c) (config c.val)

def targetAddress {B : ℕ} (c : Active hb table B) : ℕ :=
  let d := target hb table c
  address (b * B) d.state d.leftStack d.rightStack

theorem target_stacks_lt {B : ℕ} (hB : b ∣ B) (c : Active hb table B) :
    (target hb table c).leftStack < b * B ∧ (target hb table c).rightStack < b * B :=
  update_lt hb (rule hb table c).written.isLt c.val.2.1.isLt c.val.2.2.isLt hB _

theorem targetAddress_count {B : ℕ} (hB : b ∣ B) (c : Active hb table B) :
    targetAddress hb table c ≤ N * (b * B) ^ 2 :=
  address_le (target hb table c).state.isLt
    (target_stacks_lt hb table hB c).1 (target_stacks_lt hb table hB c).2

theorem targetAddress_injective {B : ℕ} (hBpos : 0 < B) (hBdiv : b ∣ B)
    (hdir : IncomingDirection table) (hin : IncomingRule table) :
    Injective (@targetAddress N b hb table B) := by
  intro c d h
  obtain ⟨hci, hcx, hcy⟩ := address_injective (Nat.mul_pos hb hBpos)
    (target_stacks_lt hb table hBdiv c).1 (target_stacks_lt hb table hBdiv d).1
    (target_stacks_lt hb table hBdiv c).2 (target_stacks_lt hb table hBdiv d).2 h
  have hconf : target hb table c = target hb table d := by
    cases hct : target hb table c
    cases hdt : target hb table d
    simp only [hct, hdt] at hci hcx hcy
    simp only [Configuration.mk.injEq]
    exact ⟨Fin.ext hci, hcx, hcy⟩
  have hs := applyRule_injective hb table hdir hin (config c.val) (config d.val)
    (rule hb table c) (rule hb table d) (lookup_rule hb table c) (lookup_rule hb table d) hconf
  apply Subtype.ext
  exact Prod.ext (congrArg Configuration.state hs)
    (Prod.ext (Fin.ext (congrArg Configuration.leftStack hs))
      (Fin.ext (congrArg Configuration.rightStack hs)))

end VelocityDetection.FiniteAddresses
end

end OAI
