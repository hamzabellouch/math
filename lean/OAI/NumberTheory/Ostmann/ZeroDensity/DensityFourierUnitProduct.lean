import OAI.NumberTheory.Ostmann.ZeroDensity.DensityFourierProduct

namespace OAI

/-! # The local factorization after the scalar multipliers in the quadratic sum -/

namespace Ostmann

open scoped BigOperators

theorem densityFourier_primeCRTFunction_unit (ps : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) (hc : ps.Pairwise Nat.Coprime)
    (f : ∀ p : ℕ, ZMod p → ℂ) (v : (ZMod ps.prod)ˣ) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    ∃ a : ∀ p : ℕ, (ZMod p)ˣ, ∀ n : ℤ,
      densityFourier (primeCRTFunction ps hp hc f) ((v : ZMod ps.prod) * (n : ZMod ps.prod)) =
        (ps.map fun p => primeDensityFourier f p ((a p : ZMod p) * (n : ZMod p))).prod := by
  classical
  let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
  obtain ⟨b, hb⟩ := densityFourier_primeCRTFunction ps hp hc f
  obtain ⟨j, hj⟩ := ZMod.intCast_surjective (v : ZMod ps.prod)
  let c : ∀ p : ℕ, (ZMod p)ˣ := fun p => if h : p ∈ ps then
    Units.map (ZMod.castHom (List.dvd_prod h) (ZMod p)).toMonoidHom v else 1
  have hcv (p : ℕ) (h : p ∈ ps) : (c p : ZMod p) = (j : ZMod p) := by
    simp only [c, dite_eq_left h, Units.coe_map]
    change (ZMod.castHom (List.dvd_prod h) (ZMod p)) (v : ZMod ps.prod) = _
    rw [← hj, map_intCast]
  refine ⟨fun p => b p * c p, ?_⟩
  intro n
  rw [← hj, ← Int.cast_mul, hb]
  apply congrArg List.prod
  apply List.map_congr_left
  intro p h
  rw [Units.val_mul, hcv p h, Int.cast_mul, mul_assoc]

theorem densityFourier_centered_unit_product (ps : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) (hc : ps.Pairwise Nat.Coprime)
    (S : ∀ p : ℕ, Finset (ZMod p)) (v : (ZMod ps.prod)ˣ) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    ∃ a : ∀ p : ℕ, (ZMod p)ˣ, ∀ n : ℤ,
      densityFourier (densityCRTList ps hp hc S).value ((v : ZMod ps.prod) * (n : ZMod ps.prod)) =
        (ps.map fun p => primeDensityFourier (fun p x => (centeredDensity (S p) x : ℂ)) p
          ((a p : ZMod p) * (n : ZMod p))).prod := by
  let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
  rw [densityCRTList_value_eq_primeCRTFunction]
  exact densityFourier_primeCRTFunction_unit ps hp hc _ v

end Ostmann

end OAI
