import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.ClusterAlgebra

namespace OAI

noncomputable section

namespace ClusterDisplacement

variable {V : Type*} [Fintype V]

def products (K : ℕ → Kernel V) : ℕ → Kernel V
  | 0 => Kernel.identity
  | n+1 => (K n).comp (products K n)

def trajectory (K : ℕ → Kernel V) (u₀ : V → ℝ) (n : ℕ) : V → ℝ := (products K n).apply u₀

def Firm (K : Kernel V) : Prop := ∀u,energy (fun x => u x-K.apply u x)≤energy u-energy (K.apply u)

end ClusterDisplacement

end

end OAI
