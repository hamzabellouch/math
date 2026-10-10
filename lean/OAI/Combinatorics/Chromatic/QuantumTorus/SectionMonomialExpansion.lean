import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TorusAdjointExpansion

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M)
local instance sectionMonomialExpansionAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance sectionMonomialExpansionAddCommGroup : AddCommGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommGroup
local instance sectionMonomialExpansionAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance sectionMonomialExpansionSub : Sub (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toSub

def gradePoints (b:M) (j:ℕ) : Finset M := (shiftRootGrade_finite C b j).toFinset
lemma mem_gradePoints (b m:M) (j:ℕ) : m∈gradePoints C b j ↔ HasRootDegree C j (m-b) := by
  simp only [gradePoints,Set.Finite.mem_toFinset,Set.mem_ofPred_eq]

def monomialJump (W:PowerSeries (Torus LaurentRay.vUnit Ω)) (d:ℕ) (m r:M) : LaurentSeries ℚ :=
  coeff d (adjoint W (PowerSeries.C (Torus.X LaurentRay.vUnit Ω m))) r

lemma adjoint_graded_torus_expansion (W:PowerSeries (Torus LaurentRay.vUnit Ω))
    (b:M) (j d:ℕ) (f:Torus LaurentRay.vUnit Ω) (hf:f∈shiftRootGrade LaurentRay.vUnit Ω C b j) (r:M) :
    coeff d (adjoint W (PowerSeries.C f)) r =
      ∑m∈gradePoints C b j,f m*monomialJump Ω W d m r := by
  rw [adjoint_torus_expansion]
  apply Finset.sum_subset
  · intro m hm
    apply (mem_gradePoints C b m j).mpr
    by_contra hh
    exact (Finsupp.mem_support_iff.mp hm) (hf m hh)
  · intro m hm hn
    rw [Finsupp.notMem_support_iff.mp hn,zero_mul]

lemma adjoint_lower_grade_expansion (W X:PowerSeries (Torus LaurentRay.vUnit Ω))
    (hW:constantCoeff W=1) (b:M) (hX:ShiftGraded LaurentRay.vUnit Ω C b X) (N:ℕ) (r:M) :
    coeff N (adjoint W X) r = coeff N X r +
      ∑j∈Finset.range N,∑m∈gradePoints C b j,coeff j X m*monomialJump Ω W (N-j) m r := by
  rw [coeff_adjoint_lower W X hW N]
  change coeff N X r+(∑j∈Finset.range N,coeff (N-j) (adjoint W (PowerSeries.C (coeff j X)))) r=_
  rw [torus_ring_eval_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact adjoint_graded_torus_expansion Ω C W b j (N-j) (coeff j X) (hX j) r
end
end ElementaryPositivity.QuantumTorus

end

end OAI
