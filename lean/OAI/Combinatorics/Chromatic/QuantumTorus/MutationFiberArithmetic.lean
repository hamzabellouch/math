import Mathlib
import OAI.Combinatorics.Chromatic.Walls.SimpleIncomingData

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
def mutationPairing : I → ℤ := fun i=>Ω (simpleRoot C pc) (simpleRoot C i)
include hcoord in
lemma root_simple_expansion {n : ℕ} {m : M} (hm : HasRootDegree C n m) :
    m=∑i,(coord m i) • simpleRoot C i := by
  obtain ⟨d,hd,hc,he⟩:=root_coordinates C coord hcoord hm
  have hsplit : (fun i=>(d i:ℤ))=∑i,((d i:ℤ) • (Pi.single i 1 : I → ℤ)) := by
    ext j
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hij; simp [Ne.symm hij]
    · simp
  calc
    m=∑i,(d i:ℤ) • simpleRoot C i:=by
      rw [←he,hsplit,map_sum]
      simp only [map_zsmul,simpleRoot]
    _=∑i,coord m i • simpleRoot C i:=by simp only [hc]
include hcoord in
lemma root_pairing_coordinates (hΩ : ∀m,Ω m m=0) {n : ℕ} {m : M}
    (hm : HasRootDegree C n m) :
    Ω (simpleRoot C pc) m=∑i∈Finset.univ.erase pc,mutationPairing Ω C pc i*coord m i := by
  have HH:=congrArg (Ω (simpleRoot C pc)) (root_simple_expansion C coord hcoord hm)
  rw [map_sum] at HH
  simp only [map_zsmul,smul_eq_mul] at HH
  rw [←Finset.sum_erase_add _ _ (Finset.mem_univ pc)] at HH
  simp only [hΩ,mul_zero,add_zero] at HH
  rw [HH]
  apply Finset.sum_congr (by ext i; simp)
  intro i hi
  exact mul_comm _ _
lemma max_zero_neg (a : ℤ) : max 0 a=max 0 (-a)+a := by
  by_cases ha : 0≤a
  · rw [max_eq_right ha,max_eq_left (by omega)]; omega
  · rw [max_eq_left (by omega),max_eq_right (by omega)]; omega
lemma fiberUpper_flip (α : I → ℤ) (σ : ℤ) (m : M) :
    fiberUpper coord pc α (-σ) m=fiberUpper coord pc α σ m+
      σ*(∑i∈Finset.univ.erase pc,α i*coord m i) := by
  change (∑i∈Finset.univ.erase pc,max 0 (-(-σ)*α i)*coord m i)=
    (∑i∈Finset.univ.erase pc,max 0 (-σ*α i)*coord m i)+σ*(∑i∈Finset.univ.erase pc,α i*coord m i)
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [neg_neg,max_zero_neg]
  have he : -(σ*α i)= -σ*α i:=by ring
  rw [he]
  ring
include hcoord in
lemma fiberUpper_simple (α : I → ℤ) (σ : ℤ) : fiberUpper coord pc α σ (simpleRoot C pc)=0 := by
  change (∑i∈Finset.univ.erase pc,max 0 (-σ*α i)*coord (simpleRoot C pc) i)=0
  apply Finset.sum_eq_zero
  intro i hi
  rw [simpleRoot_coordinates C coord hcoord]
  simp [(Finset.mem_erase.mp hi).1]
include hcoord in
lemma fiber_shift_bound (hΩ : ∀m,Ω m m=0) {n : ℕ} {m : M} (hm : HasRootDegree C n m)
    (σ : ℤ) (j : ℕ) (hj : (j:ℤ)≤σ*Ω (simpleRoot C pc) m)
    (hP : m∈fiberCone coord pc (mutationPairing Ω C pc) σ) :
    m+j • simpleRoot C pc∈fiberCone coord pc (mutationPairing Ω C pc) (-σ) := by
  have hc : coord (m+j • simpleRoot C pc) pc=coord m pc+(j:ℤ):=by
    simp only [map_add,map_nsmul,Pi.add_apply,Pi.smul_apply]
    rw [simpleRoot_coordinates C coord hcoord]
    simp
  have hu : fiberUpper coord pc (mutationPairing Ω C pc) (-σ) (m+j • simpleRoot C pc)=
      fiberUpper coord pc (mutationPairing Ω C pc) σ m+σ*Ω (simpleRoot C pc) m:=by
    rw [map_add,map_nsmul,fiberUpper_simple C coord hcoord,nsmul_zero,add_zero,fiberUpper_flip,
      ←root_pairing_coordinates Ω C coord hcoord pc hΩ hm]
  change 0≤coord (m+j • simpleRoot C pc) pc ∧
    coord (m+j • simpleRoot C pc) pc≤fiberUpper coord pc (mutationPairing Ω C pc) (-σ) (m+j • simpleRoot C pc)
  rw [hc,hu]
  exact ⟨add_nonneg hP.1 (Int.natCast_nonneg j),add_le_add hP.2 hj⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
