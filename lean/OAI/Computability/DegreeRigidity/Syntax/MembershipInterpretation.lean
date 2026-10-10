import OAI.Computability.DegreeRigidity.SetModels.ExtensionBasicAxioms
import OAI.Computability.DegreeRigidity.SetModels.RecursiveNameSymmetry

namespace OAI

namespace TuringRigidity.BoundedSetTheory
universe u

def Formula.toMembership : Formula → RecursiveNames.Formula
  | .equal i j => .equal i j
  | .member i j => .member i j
  | .conj φ ψ => .conj φ.toMembership ψ.toMembership
  | .neg φ => .neg φ.toMembership
  | .existsMem i φ => .existsSet (.conj (.member 0 (i+1)) φ.toMembership)

theorem Formula.realize_toMembership (φ : Formula) (M : ZFSet.{u})
    (env : ℕ → ZFSet.{u}) :
    φ.toMembership.Realize (M : Set ZFSet.{u}) env ↔ φ.Realize M env := by
  induction φ generalizing env with
  | equal => rfl
  | member => rfl
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ env) (ihψ env)
  | neg φ ih => exact not_congr (ih env)
  | existsMem i φ ih =>
    have hcons (x : ZFSet.{u}) : (fun n => if n = 0 then x else env (n-1)) = cons x env := by
      funext n
      cases n <;> simp [cons]
    simp [toMembership,RecursiveNames.Formula.Realize,Formula.Realize,hcons,ih]

end TuringRigidity.BoundedSetTheory

end OAI
