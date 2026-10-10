import OAI.Combinatorics.ProgressionColoring.CyclicModel
import OAI.Combinatorics.ProgressionColoring.RationalReturn
import OAI.Combinatorics.ProgressionColoring.PrimitiveVector

namespace OAI

/-!
# Primitive rational paths for the cyclic representatives

A closest positive return to a rectangle in the two representative systems
gives a primitive integer return vector. When the two displacements satisfy
the dilation relation, the first numerator is already primitive. Reducing it
modulo the return time gives the finite rational label and the two full paths.
-/

namespace QuantitativeVanDerWaerden

/-- An actual minimal rectangle return with matching dilated displacement
produces a primitive rational label for both cyclic representative paths. -/
theorem cyclic_primitive_return_path {q D dilation j h k : ℕ} (hq : 0 < q)
    (a d : CyclicGroup q D) (xlo xhi ylo yhi u : Fin D → ℝ)
    (hh : 0 < h) (hend : j + h < k)
    (hxleft : ∀ i, xlo i ≤ xRep q D (a + j • d) i ∧
      xRep q D (a + j • d) i < xhi i)
    (hyleft : ∀ i, ylo i ≤ yRep q D dilation (a + j • d) i ∧
      yRep q D dilation (a + j • d) i < yhi i)
    (hxright : ∀ i, xlo i ≤ xRep q D (a + (j + h) • d) i ∧
      xRep q D (a + (j + h) • d) i < xhi i)
    (hyright : ∀ i, ylo i ≤ yRep q D dilation (a + (j + h) • d) i ∧
      yRep q D dilation (a + (j + h) • d) i < yhi i)
    (hmin : ∀ l, 0 < l → l < h →
      ¬ ((∀ i, xlo i ≤ xRep q D (a + (j + l) • d) i ∧
        xRep q D (a + (j + l) • d) i < xhi i) ∧
        (∀ i, ylo i ≤ yRep q D dilation (a + (j + l) • d) i ∧
        yRep q D dilation (a + (j + l) • d) i < yhi i)))
    (hu : ∀ i, xRep q D (a + (j + h) • d) i - xRep q D (a + j • d) i = u i)
    (hv : ∀ i, yRep q D dilation (a + (j + h) • d) i -
      yRep q D dilation (a + j • d) i = (dilation : ℝ) * u i) :
    ∃ t : Fin D → ℤ, (∀ i, 0 ≤ t i ∧ t i < h) ∧ PrimitiveVector h t ∧
      (∀ (n : ℕ) (i : Fin D), ∃ z : ℤ, xRep q D (a + n • d) i - xRep q D a i -
        (n : ℝ) / h * ((t i : ℝ) + u i) = z) ∧
      (∀ (n : ℕ) (i : Fin D), ∃ z : ℤ, yRep q D dilation (a + n • d) i - yRep q D dilation a i -
        (n : ℝ) / h * ((dilation : ℝ) * ((t i : ℝ) + u i)) = z) := by
  let X : ℕ → Fin D → ℝ := fun n => xRep q D (a + n • d)
  let Y : ℕ → Fin D → ℝ := fun n => yRep q D dilation (a + n • d)
  have hXAP : ∀ n i, ∃ z : ℤ, X n i - xRep q D a i -
      (n : ℝ) * xRep q D d i = z := fun n i => xRep_ap_congr hq a d n i
  have hYAP : ∀ n i, ∃ z : ℤ, Y n i - yRep q D dilation a i -
      (n : ℝ) * yRep q D dilation d i = z :=
    fun n i => yRep_ap_congr hq dilation a d n i
  obtain ⟨T, hT⟩ := exists_integer_return_numerator X (xRep q D a) (xRep q D d)
    j h hXAP
  obtain ⟨S, hS⟩ := exists_integer_return_numerator Y (yRep q D dilation a)
    (yRep q D dilation d) j h hYAP
  have hp : PrimitiveVector h (Sum.elim T S) := by
    apply primitive_of_minimal_box_return
      (fun n => Sum.elim (X n) (Y n))
      (Sum.elim (xRep q D a) (yRep q D dilation a))
      (Sum.elim (xRep q D d) (yRep q D dilation d))
      (Sum.elim (fun _ => 0) (fun _ => -(1 / 2 : ℝ)))
      (Sum.elim xlo ylo) (Sum.elim xhi yhi) (Sum.elim T S) hh hend
    · intro n i
      cases i with
      | inl i => exact hXAP n i
      | inr i => exact hYAP n i
    · intro n _ i
      cases i with
      | inl i => simpa only [Sum.elim_inl, zero_add] using xRep_mem q D (a + n • d) i
      | inr i =>
        change -(1 / 2 : ℝ) ≤ yRep q D dilation (a + n • d) i ∧
          yRep q D dilation (a + n • d) i < -(1 / 2 : ℝ) + 1
        constructor
        · exact (yRep_mem q D dilation (a + n • d) i).1
        · linarith [(yRep_mem q D dilation (a + n • d) i).2]
    · intro i
      cases i with
      | inl i => exact hxleft i
      | inr i => exact hyleft i
    · intro i
      cases i with
      | inl i => exact hxright i
      | inr i => exact hyright i
    · intro i
      cases i with
      | inl i => exact hT i
      | inr i => exact hS i
    · intro l hl hlh hmem
      apply hmin l hl hlh
      exact ⟨fun i => hmem (Sum.inl i), fun i => hmem (Sum.inr i)⟩
  have hTu : ∀ i, (h : ℝ) * xRep q D d i - u i = T i := by
    intro i
    simpa only [X, hu i] using hT i
  have hSv : ∀ i, (h : ℝ) * yRep q D dilation d i - (dilation : ℝ) * u i = S i := by
    intro i
    simpa only [Y, hv i] using hS i
  have hcongr : ∀ i, ∃ z : ℤ, S i = (dilation : ℤ) * T i + (h : ℤ) * z := by
    intro i
    obtain ⟨z, hz⟩ := yRep_dilation_congr hq dilation d i
    refine ⟨z, ?_⟩
    have hr : (S i : ℝ) = (dilation : ℝ) * (T i : ℝ) + (h : ℝ) * z := by
      calc
        _ = (h : ℝ) * yRep q D dilation d i - (dilation : ℝ) * u i := (hSv i).symm
        _ = (dilation : ℝ) * ((h : ℝ) * xRep q D d i - u i) +
            (h : ℝ) * (yRep q D dilation d i - (dilation : ℝ) * xRep q D d i) := by ring
        _ = _ := by rw [hTu i, hz]
    exact_mod_cast hr
  have hpT : PrimitiveVector h T := hp.of_sum_congr_mul (dilation : ℤ) hcongr
  obtain ⟨t, htrange, htcongr, htstep⟩ := reduced_return_numerator hh T (xRep q D d) u hTu
  refine ⟨t, htrange, hpT.of_congr htcongr, ?_, ?_⟩
  · exact rational_path_congr X (xRep q D a) (xRep q D d) u t hXAP htstep
  · intro n i
    obtain ⟨z₀, hz₀⟩ := hYAP n i
    obtain ⟨z₁, hz₁⟩ := yRep_dilation_congr hq dilation d i
    obtain ⟨z₂, hz₂⟩ := htstep i
    refine ⟨z₀ + (n : ℤ) * (z₁ + (dilation : ℤ) * z₂), ?_⟩
    calc
      _ = (Y n i - yRep q D dilation a i - (n : ℝ) * yRep q D dilation d i) +
          (n : ℝ) * ((yRep q D dilation d i - (dilation : ℝ) * xRep q D d i) +
            (dilation : ℝ) * (xRep q D d i - ((t i : ℝ) + u i) / h)) := by dsimp [Y]; ring
      _ = _ := by rw [hz₀, hz₁, hz₂]; push_cast; ring

end QuantitativeVanDerWaerden

end OAI
