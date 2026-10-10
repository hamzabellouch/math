import OAI.Analysis.Triangular.Construction.RepetitionOperators

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Matrix

def Wstar : ℝ := 61/10000
def DeltaStar : ℝ := 18/100000
def Ustar : ℝ := 48/100000
def Pstar : ℝ := 3/10000000

def ParameterPolytope (e : Fin 8 → ℝ) : Prop :=
  ∃ z w delta u a r p : ℝ,
    0 ≤ z ∧ z ≤ Z ∧ 0 ≤ w ∧ w ≤ Wstar ∧ 0 ≤ delta ∧ delta ≤ DeltaStar ∧
    0 ≤ u ∧ u ≤ Ustar ∧ 0 ≤ a ∧ a ≤ Z*u ∧ 0 ≤ r ∧ r ≤ Pstar ∧
    0 ≤ p ∧ p ≤ Pstar ∧ e = ![z,1,Z*w-delta,w,a,u,r,p]

end AtomicTriangular.Construction
end

end OAI
