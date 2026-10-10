import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.QuantumTorusAlgebra
import OAI.Combinatorics.Chromatic.Walls.AdjointExpansion
import OAI.Combinatorics.Chromatic.Walls.TorusPositive
import OAI.Combinatorics.Chromatic.Walls.TranslatedCompletion

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint LaurentPositive WallUnits
noncomputable section
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ)
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance : AddCommGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommGroup
local instance : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance : Sub (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toSub
lemma torus_ring_eval_sum {J : Type*} (s : Finset J) (f : J → Torus LaurentRay.vUnit Ω) (r : M) :
    (∑j∈s,f j) r=∑j∈s,f j r := by
  classical
  induction s using Finset.induction_on with
  | empty=>rfl
  | @insert j s hj ih=>
    rw [Finset.sum_insert hj,Finset.sum_insert hj]
    change f j r+(∑j∈s,f j) r=_
    rw [ih]
lemma torus_eq_sum_X (f : Torus LaurentRay.vUnit Ω) :
    f=∑m∈f.support,f m • Torus.X LaurentRay.vUnit Ω m := by
  classical
  change f=∑m∈f.support,f m • Finsupp.single m 1
  simpa only [Finsupp.smul_single,smul_eq_mul,mul_one,Finsupp.sum] using (Finsupp.sum_single f).symm
lemma adjoint_torus_expansion (F : PowerSeries (Torus LaurentRay.vUnit Ω))
    (f : Torus LaurentRay.vUnit Ω) (N : ℕ) (r : M) :
    coeff N (adjoint F (PowerSeries.C f)) r=
      ∑m∈f.support,f m*(coeff N (adjoint F (PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)))) r := by
  classical
  conv_lhs => rw [torus_eq_sum_X Ω f]
  rw [map_sum]
  change (coeff N (adjoint F (∑m∈f.support,(PowerSeries.C (f m • Torus.X LaurentRay.vUnit Ω m) : PowerSeries (Torus LaurentRay.vUnit Ω))))) r=_
  simp only [adjoint,Finset.mul_sum,Finset.sum_mul,map_sum]
  change (∑m∈f.support,(coeff N (F*PowerSeries.C (f m • Torus.X LaurentRay.vUnit Ω m)*invOfUnit F 1) : Torus LaurentRay.vUnit Ω)) r=_
  rw [torus_ring_eval_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have HC : PowerSeries.C (f m • Torus.X LaurentRay.vUnit Ω m)=
      f m • (PowerSeries.C (Torus.X LaurentRay.vUnit Ω m) : PowerSeries (Torus LaurentRay.vUnit Ω)) := by
    ext n
    rw [coeff_C,coeff_smul,coeff_C]
    split_ifs <;> simp
  rw [HC,mul_smul_comm,smul_mul_assoc,coeff_smul]
  rfl

lemma adjoint_target_positive (F : PowerSeries (Torus LaurentRay.vUnit Ω))
    (f : Torus LaurentRay.vUnit Ω) (q : M →+ ℤ) (N : ℕ) (r : M)
    (hF : ∀n≤N,coeff n F∈chargeGrade LaurentRay.vUnit Ω q 0)
    (hf : TorusPositive Ω f)
    (hp : ∀m,q m=q r → Positive (coeff N (adjoint F (PowerSeries.C (Torus.X LaurentRay.vUnit Ω m))) r)) :
    Positive (coeff N (adjoint F (PowerSeries.C f)) r) := by
  classical
  rw [adjoint_torus_expansion]
  apply Positive.sum
  intro m hm
  by_cases hq : q m=q r
  · exact (hf m).mul (hp m hq)
  · have H:=adjoint_charge LaurentRay.vUnit Ω q F N hF m r (Ne.symm hq)
    rw [H,mul_zero]
    exact positive_zero
lemma adjoint_increment_positive (F X : PowerSeries (Torus LaurentRay.vUnit Ω))
    (q : M →+ ℤ) (N : ℕ) (r : M) (hF0 : constantCoeff F=1)
    (hF : ∀n≤N,coeff n F∈chargeGrade LaurentRay.vUnit Ω q 0)
    (hX : ∀j<N,TorusPositive Ω (coeff j X))
    (hp : ∀m,q m=q r → ∀j≤N,Positive (coeff j (adjoint F (PowerSeries.C (Torus.X LaurentRay.vUnit Ω m))) r)) :
    Positive (coeff N (adjoint F X) r-coeff N X r) := by
  rw [coeff_adjoint_lower F X hF0 N]
  change Positive ((coeff N X) r+(∑j∈Finset.range N,coeff (N-j) (adjoint F (PowerSeries.C (coeff j X)))) r-(coeff N X) r)
  rw [add_sub_cancel_left,torus_ring_eval_sum]
  apply Positive.sum
  intro j hj
  exact adjoint_target_positive Ω F (coeff j X) q (N-j) r
    (fun n hn=>hF n (hn.trans (Nat.sub_le _ _))) (hX j (Finset.mem_range.mp hj))
    (fun m hm=>hp m hm _ (Nat.sub_le _ _))
end
end ElementaryPositivity.QuantumTorus

end

end OAI
