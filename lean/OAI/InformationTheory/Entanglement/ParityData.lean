import OAI.InformationTheory.Entanglement.ProjectionData

namespace OAI

noncomputable section
open scoped BigOperators Kronecker
open Matrix
namespace FiniteConstruction
open ChannelCompletion
abbrev Four := Fin 2 × Fin 2
abbrev Outcome := Fin 2 × Fin 2
def XQ : Matrix (Fin 2) (Fin 2) ℚ := !![0,1;1,0]
def ZQ : Matrix (Fin 2) (Fin 2) ℚ := !![1,0;0,-1]
def JQ : Matrix (Fin 2) (Fin 2) ℚ := !![0,-1;1,0]
def squareQ : Fin 3 → Fin 3 → Matrix Four Four ℚ :=
  ![![XQ ⊗ₖ 1,1 ⊗ₖ XQ,XQ ⊗ₖ XQ],
    ![1 ⊗ₖ ZQ,ZQ ⊗ₖ 1,ZQ ⊗ₖ ZQ],
    ![XQ ⊗ₖ ZQ,ZQ ⊗ₖ XQ,-(JQ ⊗ₖ JQ)]]
def contextQ : Fin 6 → Fin 3 → Matrix Four Four ℚ :=
  ![squareQ 0,squareQ 1,squareQ 2,
    (fun i => squareQ i 0),(fun i => squareQ i 1),(fun i => squareQ i 2)]
def signQ (i : Fin 2) : ℚ := if i=0 then -1 else 1
def eQ (t : Fin 6) : ℚ := if t=5 then -1 else 1
def hQ (t : Fin 6) (a : Outcome) : Matrix Four Four ℚ :=
  (1/4 : ℚ) • ((1+signQ a.1 • contextQ t 0)*(1+signQ a.2 • contextQ t 1))
def eigSignQ (t : Fin 6) (a : Outcome) : Fin 3 → ℚ :=
  ![signQ a.1,signQ a.2,eQ t*signQ a.1*signQ a.2]

lemma hQ_symmetric (t : Fin 6) (a : Outcome) : (hQ t a)ᵀ=hQ t a := by
  revert t a
  decide +kernel
lemma hQ_idempotent (t : Fin 6) (a : Outcome) : hQ t a*hQ t a=hQ t a := by
  revert t a
  decide +kernel
lemma hQ_orthogonal (t : Fin 6) (a b : Outcome) (hab : a ≠ b) : hQ t a*hQ t b=0 := by
  revert t a b
  decide +kernel
lemma hQ_complete (t : Fin 6) : ∑ a, hQ t a=1 := by
  revert t
  decide +kernel
lemma hQ_eigen (t : Fin 6) (a : Outcome) (j : Fin 3) :
    contextQ t j*hQ t a=eigSignQ t a j • hQ t a := by
  revert t a j
  decide +kernel

def h (t : Fin 6) (a : Outcome) : Mat Four := (hQ t a).map (Rat.castHom ℂ)
def context (t : Fin 6) (j : Fin 3) : Mat Four := (contextQ t j).map (Rat.castHom ℂ)
def eigSign (t : Fin 6) (a : Outcome) (j : Fin 3) : ℂ := eigSignQ t a j
end FiniteConstruction

end

end OAI
