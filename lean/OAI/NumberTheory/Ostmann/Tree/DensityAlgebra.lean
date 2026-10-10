import OAI.NumberTheory.Ostmann.Tree.DensityReconstruction

namespace OAI

namespace Ostmann.Tree.Density
noncomputable section
open scoped BigOperators
variable {F : Type*} [Field F]

theorem split_difference (s sl sr D u Hl Hr : Fˣ) (p : F)
    (hp : p ≠ 0) (he : p*((s : F)*u) = (sl : F)*Hr-(sr : F)*Hl) :
    (sl : F)/((D : F)*p*u*Hl) - (sr : F)/((D : F)*p*u*Hr) =
      (s : F)/((D : F)*Hl*Hr) := by
  field_simp
  linear_combination -he

theorem child_rootArgument {d : ℕ} (L : Parameters F d) (D p X u a : Fˣ)
    (M : Leaves d → Fˣ) :
    (rootArgument L D p X (u*a) M : F) =
      (L.frequency : F) / ((D : F)*p*u*(X*a*Parameters.leafProduct M)) := by
  simp only [rootArgument, Units.val_div_eq_div_val, Units.val_mul]
  congr 1
  ring

theorem branch_rootArgument {d : ℕ} (s a b u D Xl Xr : Fˣ)
    (L R : Parameters F d) (M : Leaves (d+1) → Fˣ) :
    (rootArgument (.branch s a b u L R) D Xl Xr (a*b) M : F) =
      (s : F) / ((D : F)*(Xl*a*Parameters.leafProduct (left M))*
        (Xr*b*Parameters.leafProduct (right M))) := by
  simp only [rootArgument, Parameters.frequency, leafProduct_split,
    Units.val_div_eq_div_val, Units.val_mul]
  congr 1
  ring

theorem rootArgument_difference {d : ℕ} (s a b u D Xl Xr : Fˣ)
    (L R : Parameters F d) (M : Leaves (d+1) → Fˣ)
    (hp : pivot s a b u L R Xl Xr M ≠ 0) :
    (rootArgument L D (Units.mk0 _ hp) Xl (u*a) (left M) : F) -
      (rootArgument R D (Units.mk0 _ hp) Xr (u*b) (right M) : F) =
        (rootArgument (.branch s a b u L R) D Xl Xr (a*b) M : F) := by
  rw [child_rootArgument, child_rootArgument, branch_rootArgument]
  apply split_difference s L.frequency R.frequency D u
    (Xl*a*Parameters.leafProduct (left M)) (Xr*b*Parameters.leafProduct (right M))
    _ hp
  simp only [pivot]
  exact div_mul_cancel₀ _ (mul_ne_zero (Units.ne_zero s) (Units.ne_zero u))

theorem reconstruct_difference {d : ℕ} (P : Parameters F d)
    (hP : P.consistent) (D Xl Xr c : Fˣ) (hc : P.childConsistent c)
    (M y : Leaves d → Fˣ) (h : reconstruct D P Xl Xr c M = some y) :
    difference y = (rootArgument P D Xl Xr c M : F) := by
  induction P generalizing D Xl Xr c with
  | leaf s sign =>
      simp only [reconstruct] at h
      rw [← Option.some.inj h]
      rfl
  | @branch d s a b u L R ihl ihr =>
      obtain ⟨hL, hR, hLc, hRc⟩ := hP
      obtain ⟨hp, hl, hr⟩ := reconstruct_branch_some s a b u D Xl Xr c L R M y h
      have hleft := ihl hLc D (Units.mk0 _ hp) Xl (u*a) hL (left M) (left y) hl
      have hright := ihr hRc D (Units.mk0 _ hp) Xr (u*b) hR (right M) (right y) hr
      change a*b=c at hc
      subst c
      exact (congrArg₂ (· - ·) hleft hright).trans
        (rootArgument_difference s a b u D Xl Xr L R M hp)

theorem leafProduct_eq_of_reconstruct_eq {d : ℕ} (P : Parameters F d)
    (hP : P.consistent) (D Xl Xr c : Fˣ) (hc : P.childConsistent c)
    (M N y : Leaves d → Fˣ)
    (hM : reconstruct D P Xl Xr c M = some y)
    (hN : reconstruct D P Xl Xr c N = some y) :
    Parameters.leafProduct M = Parameters.leafProduct N := by
  have he := (reconstruct_difference P hP D Xl Xr c hc M y hM).symm.trans
    (reconstruct_difference P hP D Xl Xr c hc N y hN)
  have hu : rootArgument P D Xl Xr c M = rootArgument P D Xl Xr c N := Units.ext he
  simpa only [rootArgument, div_right_inj, mul_right_inj] using hu

end
end Ostmann.Tree.Density

end OAI
