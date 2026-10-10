import OAI.NumberTheory.Ostmann.Tree.DensityAlgebra

namespace OAI

namespace Ostmann.Tree.Density
noncomputable section
open scoped BigOperators
variable {F : Type*} [Field F]
local instance : DecidableEq F := Classical.decEq F

theorem rootArgument_eq_cancel {d : ℕ} (P : Parameters F d) (D X c p q : Fˣ)
    (M N : Leaves d → Fˣ)
    (h : rootArgument P D p X c M = rootArgument P D q X c N) :
    p * Parameters.leafProduct M = q * Parameters.leafProduct N := by
  have he : D*p*X*c*Parameters.leafProduct M = D*q*X*c*Parameters.leafProduct N :=
    div_right_inj.mp h
  apply mul_left_cancel (a := D*X*c)
  calc
    (D*X*c)*(p*Parameters.leafProduct M) = D*p*X*c*Parameters.leafProduct M := by simp [mul_assoc, mul_left_comm, mul_comm]
    _ = D*q*X*c*Parameters.leafProduct N := he
    _ = (D*X*c)*(q*Parameters.leafProduct N) := by simp [mul_assoc, mul_left_comm, mul_comm]

theorem left_product_sq_eq {d : ℕ} (s a b u D Xl Xr c : Fˣ)
    (L R : Parameters F d) (hP : (Parameters.branch s a b u L R).consistent)
    (hc : (Parameters.branch s a b u L R).childConsistent c)
    (M N y : Leaves (d+1) → Fˣ)
    (hM : reconstruct D (.branch s a b u L R) Xl Xr c M = some y)
    (hN : reconstruct D (.branch s a b u L R) Xl Xr c N = some y) :
    Parameters.leafProduct (left M)^2 = Parameters.leafProduct (left N)^2 := by
  obtain ⟨hpM, hMl, hMr⟩ := reconstruct_branch_some s a b u D Xl Xr c L R M y hM
  obtain ⟨hpN, hNl, hNr⟩ := reconstruct_branch_some s a b u D Xl Xr c L R N y hN
  let pM := Units.mk0 _ hpM
  let pN := Units.mk0 _ hpN
  have hL : rootArgument L D pM Xl (u*a) (left M) =
      rootArgument L D pN Xl (u*a) (left N) := by
    apply Units.ext
    exact (reconstruct_difference L hP.2.2.1 D pM Xl (u*a) hP.1 _ _ hMl).symm.trans
      (reconstruct_difference L hP.2.2.1 D pN Xl (u*a) hP.1 _ _ hNl)
  have hR : rootArgument R D pM Xr (u*b) (right M) =
      rootArgument R D pN Xr (u*b) (right N) := by
    apply Units.ext
    exact (reconstruct_difference R hP.2.2.2 D pM Xr (u*b) hP.2.1 _ _ hMr).symm.trans
      (reconstruct_difference R hP.2.2.2 D pN Xr (u*b) hP.2.1 _ _ hNr)
  have hl := rootArgument_eq_cancel L D Xl (u*a) pM pN _ _ hL
  have hr := rootArgument_eq_cancel R D Xr (u*b) pM pN _ _ hR
  have ht := leafProduct_eq_of_reconstruct_eq (.branch s a b u L R) hP D Xl Xr c hc M N y hM hN
  rw [leafProduct_split, leafProduct_split] at ht
  calc
    Parameters.leafProduct (left M)^2 =
      ((pM*Parameters.leafProduct (left M))/(pM*Parameters.leafProduct (right M)))*
        (Parameters.leafProduct (left M)*Parameters.leafProduct (right M)) := by simp [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm]
    _ = ((pN*Parameters.leafProduct (left N))/(pN*Parameters.leafProduct (right N)))*
        (Parameters.leafProduct (left N)*Parameters.leafProduct (right N)) := by rw [hl, hr, ht]
    _ = Parameters.leafProduct (left N)^2 := by simp [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm]

theorem left_product_image_card_le_two {d : ℕ} (s a b u D Xl Xr c : Fˣ)
    (L R : Parameters F d) (hP : (Parameters.branch s a b u L R).consistent)
    (hc : (Parameters.branch s a b u L R).childConsistent c)
    (S : Finset (Leaves (d+1) → Fˣ)) (y : Leaves (d+1) → Fˣ)
    (hS : ∀ M ∈ S, reconstruct D (.branch s a b u L R) Xl Xr c M = some y) :
    (S.image (fun M => Parameters.leafProduct (left M))).card ≤ 2 := by
  classical
  by_cases hs : S.Nonempty
  · obtain ⟨M, hM⟩ := hs
    apply le_trans (Finset.card_le_card (t :=
      {Parameters.leafProduct (left M), -Parameters.leafProduct (left M)}) ?_) Finset.card_le_two
    intro x hx
    obtain ⟨N, hN, rfl⟩ := Finset.mem_image.mp hx
    have he := left_product_sq_eq s a b u D Xl Xr c L R hP hc N M y (hS N hN) (hS M hM)
    rcases Units.sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h <;> simp [h]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

theorem pivot_eq_of_left_product_eq {d : ℕ} (s a b u D Xl Xr c : Fˣ)
    (L R : Parameters F d) (hP : (Parameters.branch s a b u L R).consistent)
    (hc : (Parameters.branch s a b u L R).childConsistent c)
    (M N y : Leaves (d+1) → Fˣ)
    (hM : reconstruct D (.branch s a b u L R) Xl Xr c M = some y)
    (hN : reconstruct D (.branch s a b u L R) Xl Xr c N = some y)
    (hl : Parameters.leafProduct (left M) = Parameters.leafProduct (left N)) :
    pivot s a b u L R Xl Xr M = pivot s a b u L R Xl Xr N := by
  have ht := leafProduct_eq_of_reconstruct_eq (.branch s a b u L R) hP D Xl Xr c hc M N y hM hN
  rw [leafProduct_split, leafProduct_split, hl] at ht
  have hr := mul_left_cancel ht
  simp only [pivot, hl, hr]

end
end Ostmann.Tree.Density

end OAI
