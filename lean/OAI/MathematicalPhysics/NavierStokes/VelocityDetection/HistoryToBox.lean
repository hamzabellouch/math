import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.History
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TapeCodes

namespace OAI

noncomputable section
namespace VelocityDetection.History
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open scoped Topology ContDiff BigOperators ZeroAtInfty
open Set Function
open Stacks

def toBox {N B H : ℕ} (c : Configuration N) (hc : Fits B H c) : Box N B H :=
  (c.tape.state, ⟨c.tape.leftStack, hc.1⟩, ⟨c.tape.rightStack, hc.2.1⟩,
    ⟨c.history, hc.2.2⟩)

@[simp] theorem config_toBox {N B H : ℕ} (c : Configuration N) (hc : Fits B H c) :
    config (toBox c hc) = c := by cases c; rfl

end VelocityDetection.History
end

noncomputable section
namespace VelocityDetection.History
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open scoped Topology ContDiff BigOperators ZeroAtInfty
open Set Function
open Stacks
variable {N b : ℕ} (hb : 0 < b)
  (table : Fin N → Fin b → Option (Rule (Fin N) b))

def activeOf {B H : ℕ} (c : Configuration N) (hc : Fits B H c)
    (h : (Stacks.lookup hb table c.tape).isNone = false) : Active hb table B H :=
  ⟨toBox c hc, by simpa using h⟩

@[simp] theorem config_activeOf {B H : ℕ} (c : Configuration N) (hc : Fits B H c)
    (h : (Stacks.lookup hb table c.tape).isNone = false) :
    config (activeOf hb table c hc h).val = c := config_toBox c hc

theorem target_activeOf {B H : ℕ} (c : Configuration N) (hc : Fits B H c)
    (h : (Stacks.lookup hb table c.tape).isNone = false) :
    target hb table (activeOf hb table c hc h) = next hb table c := by
  have hr := lookup_rule hb table (activeOf hb table c hc h)
  simp only [config_activeOf] at hr
  simp only [target, config_activeOf, next, hr, Option.elim_some]

end VelocityDetection.History
end

end OAI
