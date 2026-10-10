import OAI.Analysis.KadisonKastler.PolarSmoothing

namespace OAI

/-! # Continuous polar unitary paths

The polar decomposition identifies its unitary factor with
`a * inverse(abs a)`. This gives norm continuity for continuous paths
of invertible operators, together with quantitative smoothing bounds.
-/

namespace KadisonKastler

open scoped Topology CStarAlgebra

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def polarUnitary (t : Aˣ) : unitary A := (exists_unitary_mul_abs t).choose

theorem polarUnitary_mul_abs (t : Aˣ) :
    (polarUnitary t : A) * CFC.abs (t : A) = (t : A) :=
  (exists_unitary_mul_abs t).choose_spec

theorem polarUnitary_eq_mul_inverse_abs (t : Aˣ) :
    (polarUnitary t : A) = (t : A) * Ring.inverse (CFC.abs (t : A)) := by
  let s : Aˣ := (isUnit_abs t).unit
  have hs : (s : A) = CFC.abs (t : A) := (isUnit_abs t).unit_spec
  rw [← hs, Ring.inverse_unit]
  calc
    (polarUnitary t : A) = ((polarUnitary t : A) * (s : A)) * (s⁻¹ : Aˣ) := by
      simp only [mul_assoc, Units.mul_inv, mul_one]
    _ = (t : A) * (s⁻¹ : Aˣ) := by rw [hs, polarUnitary_mul_abs]

theorem polarUnitary_unique (t : Aˣ) (u : unitary A)
    (hu : (u : A) * CFC.abs (t : A) = (t : A)) : u = polarUnitary t := by
  apply Subtype.ext
  let s : Aˣ := (isUnit_abs t).unit
  have hs : (s : A) = CFC.abs (t : A) := (isUnit_abs t).unit_spec
  have he : (u : A) * (s : A) = (polarUnitary t : A) * s := by
    rw [hs, hu, polarUnitary_mul_abs]
  have hm := congrArg (fun a : A => a * (s⁻¹ : Aˣ)) he
  simpa only [mul_assoc, Units.mul_inv, mul_one] using hm

theorem continuous_polarUnitary : Continuous (polarUnitary : Aˣ → unitary A) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun t : Aˣ => (polarUnitary t : A))
  have he : (fun t : Aˣ => (polarUnitary t : A)) =
      (fun t : Aˣ => (t : A) * Ring.inverse (CFC.abs (t : A))) :=
    funext polarUnitary_eq_mul_inverse_abs
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro t
  let s : Aˣ := (isUnit_abs t).unit
  have hs : (s : A) = CFC.abs (t : A) := (isUnit_abs t).unit_spec
  have hi : ContinuousAt Ring.inverse (CFC.abs (t : A)) := by
    rw [← hs]
    exact NormedRing.inverse_continuousAt s
  have ha : Continuous (fun u : Aˣ => CFC.abs (u : A)) :=
    CFC.continuous_abs.comp Units.continuous_val
  exact Units.continuous_val.continuousAt.mul (hi.comp (f := fun u : Aˣ => CFC.abs (u : A)) ha.continuousAt)

/-- A continuous operator family known pointwise to be invertible gives
an actual norm-continuous family of polar unitaries. -/
theorem continuous_polarUnitary_of_isUnit {X : Type*} [TopologicalSpace X]
    (f : X → A) (hf : Continuous f) (hunit : ∀ x, IsUnit (f x)) :
    Continuous (fun x => polarUnitary (hunit x).unit) := by
  apply continuous_polarUnitary.comp
  apply Units.isOpenEmbedding_val.isEmbedding.continuous_iff.mpr
  have he : Units.val ∘ (fun x => (hunit x).unit) = f :=
    funext fun x => (hunit x).unit_spec
  rw [he]
  exact hf

theorem norm_polarUnitary_sub_le [Nontrivial A] (t : Aˣ) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (ht : ‖(t : A)‖ ≤ 1 + r)
    (hti : ‖((t⁻¹ : Aˣ) : A)‖ ≤ (1 - r)⁻¹) :
    ‖(polarUnitary t : A) - t‖ ≤ r := by
  obtain ⟨u, hu, hclose⟩ := exists_polar_unitary_of_norm_bounds t hr hr1 ht hti
  rwa [polarUnitary_unique t u hu] at hclose

end

end KadisonKastler

end OAI
