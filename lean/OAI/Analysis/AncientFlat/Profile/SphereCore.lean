import Mathlib

namespace OAI
noncomputable section
open scoped ContDiff Laplacian
namespace CompactCore
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

def radialJet (j : ℕ) (f : V → ℂ) (x : V) : ℂ :=
  iteratedFDeriv ℝ j f x (fun _ => x)

def correction (f : V → ℂ) (x : V) : ℂ := radialJet 2 f x+29*radialJet 1 f x

def sphereLap (f : V → ℂ) : V → ℂ := Δ f-correction f

def compactOp (f : V → ℂ) (x : V) : ℂ :=
  (1/16:ℂ)*sphereLap (sphereLap f) x-(37/4:ℂ)*sphereLap f x+312*f x

def flatOp (f : V → ℂ) (x : V) : ℂ := (1/16:ℂ)*Δ (Δ f) x

def errorTwo (f : V → ℂ) (x : V) : ℂ :=
  -Δ (correction f) x-correction (Δ f) x-148*Δ f x
def errorFour (f : V → ℂ) (x : V) : ℂ :=
  correction (correction f) x+148*correction f x+4992*f x
end CompactCore

end

end OAI
