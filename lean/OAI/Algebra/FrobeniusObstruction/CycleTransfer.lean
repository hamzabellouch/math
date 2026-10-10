import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.CycleTransfer
variable {k A H : Type*} [Field k] [AddCommGroup A] [Module k A]
  [AddCommGroup H] [Module k H]
variable (δ : A →ₗ[k] A) (j : H →ₗ[k] A) (p : A →ₗ[k] H)
variable (hpδ : ∀ x, p (δ x) = 0)
variable (hdecomp : ∀ z, δ z = 0 → ∃ y, z - j (p z) = δ y)

                                                                          
                                                                         
include hpδ hdecomp in
theorem operator (F G : A →ₗ[k] A) (T : H →ₗ[k] H)
    (hF : ∀ x, F (δ x) = δ (G x))
    (hT : ∀ x, T x = p (F (j x))) (z : A) (hz : δ z = 0) :
    T (p z) = p (F z) := by
  obtain ⟨y,hy⟩ := hdecomp z hz
  have h := congrArg (fun a => p (F a)) hy
  simp only [map_sub, hF, hpδ] at h
  rw [hT]
  exact (sub_eq_zero.mp h).symm

                                                                  
include hdecomp in
theorem pairing (Φ : A →ₗ[k] k) (hΦδ : ∀ a, Φ (δ a) = 0)
    (z : A) (hz : δ z = 0) : Φ (j (p z)) = Φ z := by
  obtain ⟨y,hy⟩ := hdecomp z hz
  have h := congrArg Φ hy
  simp only [map_sub, hΦδ] at h
  exact (sub_eq_zero.mp h).symm

                                                                        
                                                                                
include hdecomp in
theorem pairing_operator (F G : A →ₗ[k] A) (T : H →ₗ[k] H)
    (hδF : ∀ x, δ (F x) = G (δ x)) (hδj : ∀ x, δ (j x) = 0)
    (hT : ∀ x, T x = p (F (j x)))
    (Φ : A →ₗ[k] k) (hΦδ : ∀ a, Φ (δ a) = 0) (hΦF : ∀ a, Φ (F a) = 0)
    (x : H) : Φ (j (T x)) = 0 := by
  rw [hT, pairing δ j p hdecomp Φ hΦδ]
  · exact hΦF _
  · rw [hδF, hδj, map_zero]

end BoundaryOnly.FormalObstruction.CycleTransfer

end

end OAI
