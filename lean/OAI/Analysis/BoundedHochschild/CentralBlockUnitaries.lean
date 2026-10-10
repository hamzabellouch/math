import OAI.Analysis.BoundedHochschild.FiniteUnitaryPrimitives

namespace OAI

/-! Finite groups assembled across finite central partitions. -/

noncomputable section

open scoped BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

variable {M I G : Type*} [CStarAlgebra M] [Fintype I]
  [Group G]
  (p : I → M) (hp : ∀ i, IsStarProjection (p i))
  (hc : ∀ i a, p i * a = a * p i)
  (ho : ∀ i j, i ≠ j → p i * p j = 0)
  (hs : ∑ i, p i = 1)

def centralBlock (a : I → M) : M := ∑ i, p i * a i

include hp hc ho in
lemma centralBlock_mul (a b : I → M) :
    centralBlock p a * centralBlock p b = centralBlock p (fun i => a i * b i) := by
  classical
  have ht (i j : I) : (p i * a i) * (p j * b j) =
      if i = j then p i * (a i * b i) else 0 := by
    have he : (p i * a i) * (p j * b j) = (p i * p j) * (a i * b j) := by
      calc
        _ = p i * (a i * p j) * b j := by noncomm_ring
        _ = p i * (p j * a i) * b j := by rw [hc j (a i)]
        _ = _ := by noncomm_ring
    rw [he]
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl, (hp i).isIdempotentElem.eq]
    · rw [ite_eq_right hij, ho i j hij, zero_mul]
  simp [centralBlock, Finset.sum_mul, Finset.mul_sum, ht]

include hp hc in
lemma centralBlock_star (a : I → M) :
    star (centralBlock p a) = centralBlock p (fun i => star (a i)) := by
  simp only [centralBlock, star_sum, star_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [(hp i).isSelfAdjoint.star_eq, hc]

include hs in
lemma centralBlock_one : centralBlock p (fun _ => 1) = 1 := by
  simpa only [centralBlock, mul_one] using hs

variable (ρ : G →* unitary M)

include hp hc ho hs in
lemma centralBlock_mem_unitary (a : I → G) :
    centralBlock p (fun i => (ρ (a i) : M)) ∈ unitary M := by
  constructor
  · rw [centralBlock_star p hp hc, centralBlock_mul p hp hc ho]
    simpa only [Unitary.coe_star_mul_self] using centralBlock_one p hs
  · rw [centralBlock_star p hp hc, centralBlock_mul p hp hc ho]
    have hm (i : I) : (ρ (a i) : M) * star (ρ (a i) : M) = 1 :=
      Unitary.mul_star_self_of_mem (ρ (a i)).property
    simpa only [hm] using centralBlock_one p hs

def centralBlockHom : (I → G) →* unitary M where
  toFun a := ⟨centralBlock p (fun i => (ρ (a i) : M)),
    centralBlock_mem_unitary p hp hc ho hs ρ a⟩
  map_one' := Subtype.ext (by
    simpa only [Pi.one_apply, map_one, Submonoid.coe_one] using centralBlock_one p hs)
  map_mul' a b := Subtype.ext (by
    simpa only [Pi.mul_apply, map_mul, Submonoid.coe_mul] using
      (centralBlock_mul p hp hc ho (fun i => (ρ (a i) : M))
        (fun i => (ρ (b i) : M))).symm)

end KadisonRingrose
end BoundedHochschild

end

end OAI
