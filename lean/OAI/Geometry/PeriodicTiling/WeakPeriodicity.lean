import OAI.Geometry.PeriodicTiling.DirectionalLimits
import OAI.Geometry.PeriodicTiling.DirectionalSlices
import OAI.Geometry.PeriodicTiling.CosetPeriodicity
import OAI.Geometry.PeriodicTiling.CosetParts
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring

namespace OAI

namespace PeriodicTilingThree

theorem Tiles.exists_weak_periodic_partition {F : Finset Plane} {A : Set Plane}
    (h : Tiles F A) (h0 : (0 : Plane) ∈ F) :
    ∃ (m : ℕ) (parts : Fin m → Set Plane) (v : Fin m → Plane),
      (∀ x, (∑ j, tileIndicator ℝ (parts j) x) = tileIndicator ℝ A x) ∧
      (∀ j, v j ≠ 0) ∧ ∀ j, Period (parts j) (v j) := by
  classical
  obtain ⟨m, v, φ, hv, hpair, hφ, hsum, hp⟩ :=
    h.exists_directional_decomposition h0
  by_cases hm0 : m = 0
  · subst m
    have hA : A = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      have hx := hsum x
      by_contra hnot
      simp [tileIndicator, hnot] at hx
    refine ⟨1, fun _ => A, fun _ => (1, 0), ?_, ?_, ?_⟩
    · intro x
      simp
    · intro j hj
      have hz : (1 : ℤ) = 0 := congrArg Prod.fst hj
      exact one_ne_zero hz
    · intro j x
      simp [hA]
  · have hm : 0 < m := Nat.pos_of_ne_zero hm0
    let j₀ : Fin m := ⟨0, hm⟩
    obtain ⟨e, he, htrans, hspan⟩ := exists_common_transverse v hv hpair
    obtain ⟨K, hK, hKrep⟩ := exists_common_second_vector v j₀ e htrans
    let H : Plane := (K : ℤ) • v j₀
    choose α β hα hH using hKrep
    have hdet : planeDet e H ≠ 0 := by
      dsimp [H]
      rw [planeDet_zsmul_right]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)) (htrans j₀)
    have hlocal : ∀ x : Plane, ∃ w : Plane, w ≠ 0 ∧
        Function.Periodic
          (fun st : Plane => tileIndicator ℝ A (x + st.1 • e + st.2 • H)) w := by
      intro x
      let P : Fin m → ℤ → ℝ := fun j n => φ j (x + n • e)
      have hcoord (j : Fin m) (s t : ℤ) :
          φ j (x + s • e + t • H) = P j (s + β j * t) := by
        have hpoint : x + s • e + t • H =
            (x + (s + β j * t) • e) + (t * α j) • v j := by
          change x + s • e + t • ((K : ℤ) • v j₀) = _
          rw [hH j]
          apply Prod.ext <;> simp [smul_add, add_smul, zsmul_eq_mul] <;> ring
        rw [hpoint]
        exact (hp j).zsmul (t * α j) _
      have hlocalSum (st : Plane) :
          tileIndicator ℝ A (x + st.1 • e + st.2 • H) =
            1 - ∑ j, P j (st.1 + β j * st.2) := by
        have hz := hsum (x + st.1 • e + st.2 • H)
        have heq : (∑ j, φ j (x + st.1 • e + st.2 • H)) =
            ∑ j, P j (st.1 + β j * st.2) := by
          apply Finset.sum_congr rfl
          intro j _
          exact hcoord j st.1 st.2
        rw [heq] at hz
        linarith
      refine coset_configuration_has_period P β _
        (fun j n => (hφ j _).1) ?_ hlocalSum m hm ?_
      · intro i j hij n r
        exact directional_slice_pair_bound A v φ e hspan
          (fun j y => (hφ j y).1) hp hsum x i j hij n r
      · intro j
        exact directional_circle_slice_polynomial hm A v φ e hspan hp hsum j x
    obtain ⟨n, parts, w, hparts, hw⟩ :=
      finite_periodic_parts_of_coset_periods e H hdet hlocal
    exact ⟨n, parts, w, hparts, fun j => (hw j).1, fun j => (hw j).2⟩

end PeriodicTilingThree

end OAI
