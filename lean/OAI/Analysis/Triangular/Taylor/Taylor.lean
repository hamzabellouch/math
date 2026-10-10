import OAI.Analysis.Triangular.Certificate.WaveIntervals

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

def otherSide (i : Fin 2) : Fin 2 := if i.val=0 then 1 else 0

def finiteSpectrum (side q : Fin 2) (j : Fin 31) (r : Fin 8) : ℂ :=
  if q.val=0 then fourierCoeff j*(Acoefficient side 22 r:ℂ)
  else ∑ col : Fin 22, finiteColumn ⟨col.val,by omega⟩ j*(Acoefficient side ⟨col.val,by omega⟩ r:ℂ)

def taylorPhase (q branch : Fin 2) (t : ℝ) : ℂ :=
  if branch.val=0 then I*Real.pi*t-(Real.pi*(damping q-h):ℝ)
  else I*Real.pi*zeta (damping q) h t

def taylorAmplitude (q branch : Fin 2) (t : ℝ) : ℂ :=
  if branch.val=0 then 1 else lambda (damping q) t

def taylorWave (q branch : Fin 2) (m : ℤ) (l : ℕ) (t : ℝ) : ℂ :=
  taylorAmplitude q branch t * exp (taylorPhase q branch t*m) *
    (taylorPhase q branch t)^(l+2) / ((l+2).factorial:ℂ)

def taylorRow (side : Fin 2) (m : ℤ) (y : ℝ) (l : ℕ) (r : Fin 8) : ℝ :=
  y^l*(∑ q : Fin 2, ∑ j : Fin 31,
    (finiteSpectrum side q j r*taylorWave q 0 m l (frequency j) +
    finiteSpectrum (otherSide side) q j r*taylorWave q 1 m l (frequency j))).re

def finiteTaylor (side : Fin 2) (m : ℤ) (y : ℝ) (e : Fin 8 → ℝ) (τ : ℝ) : ℝ :=
  ∑ l ∈ Finset.range 21, (∑ r : Fin 8, taylorRow side m y l r*e r)*τ^l

end AtomicTriangular.Construction
end

end OAI
