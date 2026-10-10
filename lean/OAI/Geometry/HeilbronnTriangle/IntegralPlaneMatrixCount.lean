import OAI.Geometry.HeilbronnTriangle.IntegralPlaneRows
import OAI.Geometry.HeilbronnTriangle.PlaneTripleCount

namespace OAI


noncomputable section

namespace Problem355.IntegralPlaneMatrixCount

open Matrix Module IntegralPlaneLattice IntegralPlaneRows

theorem card_le (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
    (Γ : Submodule ℤ (plane x)) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    (T : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (hAx : ∀ A ∈ T, A.mulVec x = 0)
    (hrow : ∀ A (hA : A ∈ T) i, (rows x A (hAx A hA) i : plane x) ∈ Γ)
    (R : ℝ) (hR : 0 ≤ R)
    (hnorm : ∀ A ∈ T, ∀ i, ‖castVec (A i)‖ ≤ R)
    (hrank : ∀ A ∈ T, (A.map (Int.castRingHom ℝ)).rank = 2) :
    (T.card : ℝ) ≤ (9 * Real.pi * R ^ 2 / ZLattice.covolume Γ) ^ 3 := by
  classical
  let f : {A // A ∈ T} → Fin 3 → Γ := fun A i =>
    ⟨(rows x A.1 (hAx A.1 A.2) i : plane x), hrow A.1 A.2 i⟩
  have hf : Function.Injective f := by
    intro A B h
    apply Subtype.ext
    ext i j
    have hij := congrArg (fun u : Fin 3 → Γ => (((u i : plane x) : Ambient) j)) h
    change (A.1 i j : ℝ) = (B.1 i j : ℝ) at hij
    exact_mod_cast hij
  let U := T.attach.image f
  have hcard : U.card = T.card :=
    (Finset.card_image_of_injective _ hf).trans Finset.card_attach
  rw [← hcard]
  apply PlaneTripleCount.card_spanning_triples_le Γ (plane_finrank x z hz) U R hR
  · intro u hu i
    obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hu
    exact hnorm A.1 A.2 i
  · intro u hu
    obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hu
    exact span_rows_eq_top x z hz A.1 (hAx A.1 A.2) (hrank A.1 A.2)

theorem card_le_index (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
    (L Γ : Submodule ℤ (plane x))
    [DiscreteTopology L] [IsZLattice ℝ L]
    [DiscreteTopology Γ] [IsZLattice ℝ Γ] (hΓ : Γ ≤ L)
    (T : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (hAx : ∀ A ∈ T, A.mulVec x = 0)
    (hrow : ∀ A (hA : A ∈ T) i, (rows x A (hAx A hA) i : plane x) ∈ Γ)
    (R : ℝ) (hR : 0 ≤ R)
    (hnorm : ∀ A ∈ T, ∀ i, ‖castVec (A i)‖ ≤ R)
    (hrank : ∀ A ∈ T, (A.map (Int.castRingHom ℝ)).rank = 2) :
    (T.card : ℝ) ≤ (9 * Real.pi) ^ 3 * R ^ 6 /
      ((Γ.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) * ZLattice.covolume L) ^ 3 := by
  have h := card_le x z hz Γ T hAx hrow R hR hnorm hrank
  have hL : 0 < ZLattice.covolume L := ZLattice.covolume_pos L MeasureTheory.volume
  have hcov : ZLattice.covolume Γ =
      (Γ.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) * ZLattice.covolume L :=
    (div_eq_iff (ne_of_gt hL)).mp (ZLattice.covolume_div_covolume_eq_relIndex' Γ L hΓ)
  rw [hcov] at h
  simpa only [div_pow, mul_pow, ← pow_mul, Nat.reduceMul] using h

theorem card_le_of_minors (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
    (Γ : Submodule ℤ (plane x)) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    (T : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (hAx : ∀ A ∈ T, A.mulVec x = 0)
    (hrow : ∀ A (hA : A ∈ T) i, (rows x A (hAx A hA) i : plane x) ∈ Γ)
    (R : ℝ) (hR : 0 ≤ R)
    (hnorm : ∀ A ∈ T, ∀ i, ‖castVec (A i)‖ ≤ R)
    (hminor : ∀ A ∈ T, ∃ r c : Fin 2 → Fin 3, (A.submatrix r c).det ≠ 0) :
    (T.card : ℝ) ≤ (9 * Real.pi * R ^ 2 / ZLattice.covolume Γ) ^ 3 := by
  apply card_le x z hz Γ T hAx hrow R hR hnorm
  intro A hA
  obtain ⟨r, c, hm⟩ := hminor A hA
  exact real_rank_eq_two_of_minor x z hz A (hAx A hA) r c hm

end Problem355.IntegralPlaneMatrixCount

end

end OAI
