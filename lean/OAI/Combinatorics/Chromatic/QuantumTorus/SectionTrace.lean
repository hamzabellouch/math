import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.QuantumTorusTrace
import OAI.Combinatorics.Chromatic.Walls.CompletedInverse

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
local instance sectionTraceAddCommGroup : AddCommGroup (Torus v Ω) := (Torus.instRing v Ω).toAddCommGroup
local instance sectionTraceAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance sectionTraceSub : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
lemma torus_eval_sum {J : Type*} (s : Finset J) (f : J → Torus v Ω) (r : M) :
    (∑j∈s,f j) r=∑j∈s,f j r := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj,Finset.sum_insert hj]
    change f j r+(∑j∈s,f j) r=_
    rw [ih]
include hΩ in
lemma series_coefficient_trace (r : M) (F X : PowerSeries (Torus v Ω)) (N : ℕ)
    (hF : ∀n≤N,∀m,Ω m r≠0 → (coeff n F) m=0) :
    (coeff N (F*X)) r=(coeff N (X*F)) r := by
  classical
  rw [coeff_mul,coeff_mul]
  change (∑p∈Finset.HasAntidiagonal.antidiagonal N, ((coeff p.1 F)*(coeff p.2 X) : Torus v Ω)) r =
    (∑p∈Finset.HasAntidiagonal.antidiagonal N, ((coeff p.1 X)*(coeff p.2 F) : Torus v Ω)) r
  rw [torus_eval_sum,torus_eval_sum]
  rw [←Finset.Nat.sum_antidiagonal_swap (f:=fun p=>((coeff p.1 X)*(coeff p.2 F)) r)]
  apply Finset.sum_congr rfl
  intro p hp
  apply coefficient_trace v Ω hΩ r
  exact hF p.1 (by have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp; omega)
include hΩ in
lemma adjoint_coefficient_trace (r : M) (F X : PowerSeries (Torus v Ω)) (N : ℕ)
    (hF0 : constantCoeff F=1)
    (hF : ∀n≤N,∀m,Ω m r≠0 → (coeff n F) m=0) :
    (coeff N (adjoint F X)) r=(coeff N X) r := by
  unfold adjoint
  rw [mul_assoc,series_coefficient_trace v Ω hΩ r F (X*invOfUnit F 1) N hF,
    mul_assoc,invOfUnit_mul F 1 hF0,mul_one]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
