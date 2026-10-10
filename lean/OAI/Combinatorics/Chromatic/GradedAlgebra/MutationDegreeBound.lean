import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.GlobalFiberBound

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)

def mutationSize : ℕ := (Finset.univ.erase pc).sup fun i=>(mutationPairing Ω C pc i).natAbs

lemma mutationSize_bound (i : I) (hi : i≠pc) :
    |mutationPairing Ω C pc i|≤(mutationSize Ω C pc:ℤ) := by
  have HH : (mutationPairing Ω C pc i).natAbs ≤ mutationSize Ω C pc:=
    Finset.le_sup (f:=fun i=>(mutationPairing Ω C pc i).natAbs) (Finset.mem_erase.mpr ⟨hi,Finset.mem_univ i⟩)
  simpa only [Int.natCast_natAbs] using (show ((mutationPairing Ω C pc i).natAbs:ℤ)≤(mutationSize Ω C pc:ℤ) from by exact_mod_cast HH)

lemma side_upper_le_abs (pos : Bool) (a : ℤ) : max 0 (-sideSign pos*a)≤|a| := by
  cases pos
  · simp only [sideSign,Bool.false_eq_true,ite_false,neg_neg,one_mul]
    exact max_le (abs_nonneg _) (le_abs_self _)
  · simp only [sideSign,ite_true,neg_mul,one_mul]
    exact max_le (abs_nonneg _) (neg_le_abs _)

include hcoord in
lemma fiberUpper_degree_bound (pos : Bool) {n : ℕ} {m : M} (hm : HasRootDegree C n m) :
    fiberUpper coord pc (mutationPairing Ω C pc) (sideSign pos) m≤
      (mutationSize Ω C pc:ℤ)*nonpDegree coord pc m := by
  obtain ⟨d,hd,hc,he⟩:=root_coordinates C coord hcoord hm
  change (∑i∈Finset.univ.erase pc,max 0 (-sideSign pos*mutationPairing Ω C pc i)*coord m i)≤
    (mutationSize Ω C pc:ℤ)*(∑i∈Finset.univ.erase pc,coord m i)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_right
  · exact (side_upper_le_abs pos _).trans (mutationSize_bound Ω C pc i (Finset.mem_erase.mp hi).1)
  · rw [hc]
    exact Int.natCast_nonneg _

include hcoord in
lemma fiber_full_degree_bound (pos : Bool) {n : ℕ} {m : M} (hm : HasRootDegree C n m)
    (hb : m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    (n:ℤ)≤((mutationSize Ω C pc+1:ℕ):ℤ)*nonpDegree coord pc m := by
  have Hn:=nonpDegree_root_eq C coord hcoord pc hm
  have Hk:=hb.2.trans (fiberUpper_degree_bound Ω C coord hcoord pc pos hm)
  push_cast
  nlinarith

include hcoord in
lemma mutation_root_image_bound (hΩ : ∀m,Ω m m=0) (pos : Bool) {n : ℕ} {m : M}
    (hm : HasRootDegree C n m)
    (hb : m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    ∃d : ℕ,HasRootDegree (mutatedRoots Ω C pc) d (mutationLinearPiece Ω C pc pos m) ∧
      (nonpDegree coord pc m:ℤ)≤(d:ℤ) ∧ n≤(mutationSize Ω C pc+1)*d := by
  obtain ⟨d,hd,hde⟩:=mutation_root_image Ω C coord hcoord pc hΩ pos hm hb
  have hwd : nonpDegree coord pc m≤(d:ℤ):=by have HB:=hb.2; omega
  have Hn:=fiber_full_degree_bound Ω C coord hcoord pc pos hm hb
  have HH : (n:ℤ)≤((mutationSize Ω C pc+1:ℕ):ℤ)*(d:ℤ):=
    Hn.trans (mul_le_mul_of_nonneg_left hwd (Int.natCast_nonneg _))
  refine ⟨d,hd,hwd,?_⟩
  exact_mod_cast HH

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀d m,HasRootDegree C d m → L (e m)=(d:ℝ))
include hcoord he hB hcomp hdeg in
theorem actual_wall_mutation_root_bound (r : M) (dr : ℕ) (hdr : 0<dr) (hrd : HasRootDegree C dr r)
    (h : Module.Dual ℝ E) (hg : ∀N,RayGeneric C N r (h.toAddMonoidHom.comp e))
    (pos : Bool) (hside : cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc))
    (j : ℕ) (m : M) (hm : PowerSeries.coeff j
      (chartZero WallUnits.LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e) (simpleTotalTransport Ω C)).val m≠0) :
    ∃d : ℕ,HasRootDegree (mutatedRoots Ω C pc) d (mutationLinearPiece Ω C pc pos m) ∧
      nonpDegree coord pc m≤(d:ℤ) ∧ j≤(mutationSize Ω C pc+1)*d := by
  have hΩ : ∀m,Ω m m=0:=by
    intro m; have HH:=hB (e m); rw [hcomp] at HH; exact_mod_cast HH
  exact mutation_root_image_bound Ω C coord hcoord pc hΩ pos
    (chart_root_of_ne WallUnits.LaurentRay.vUnit Ω C _ j m hm)
    (simple_fiber_bound Ω C coord hcoord pc e he B hB hcomp L hdeg r dr hdr hrd h hg pos hside j m hm)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
