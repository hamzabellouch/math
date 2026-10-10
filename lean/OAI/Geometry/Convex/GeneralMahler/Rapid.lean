import OAI.Geometry.Convex.GeneralMahler.Growth

namespace OAI
/-! Polynomial growth and rapid layer decay with polynomial loss in
the Gaussian variables. Fubini and moment estimates. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real ProbabilityTheory
open scoped ENNReal NNReal Topology Pointwise
namespace GeneralMahler
section
variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
def rapid (f:X→E) := ∀ n:ℕ, ∃ C : ℝ, 0≤C ∧ ∀ x, ‖f x‖*(1+‖x‖)^n ≤ C
/-- First variable rapid (the tail layer), second moderate (Gaussian). -/
def mixed (f:X → Y → E) := ∀ n:ℕ, ∃ (C : ℝ) (m : ℕ), 0≤C ∧ ∀ x y,
    ‖f x y‖*(1+‖x‖)^n ≤ C*(1+‖y‖)^m

theorem poly_prod_bound {f : X → Y → E}
    (hf : PolyBound f.uncurry) : ∃ (C : ℝ) (m : ℕ), 0≤C ∧ ∀ x y,
    ‖f x y‖ ≤ C*(1+‖x‖)^m*(1+‖y‖)^m := by
  obtain ⟨C,m,hc,h⟩ := hf
  refine ⟨C,m,hc,fun x y => ?_⟩

  rw [mul_assoc, ← mul_pow]
  apply (h (x,y)).trans
  gcongr; change 1 + max ‖x‖ ‖y‖ ≤ _
  rcases max_choice ‖x‖ ‖y‖ with h|h <;> rw [h] <;> nlinarith [norm_nonneg x,norm_nonneg y]

namespace mixed
variable {f g : X → Y → E}

lemma poly (hf : mixed f) : PolyBound f.uncurry := by
  obtain ⟨C,k,hc,h⟩ := hf 0
  simp only [pow_zero,mul_one] at h
  refine ⟨C,k,hc,?_⟩
  rintro ⟨x,y⟩
  apply (h x y).trans
  gcongr; exact le_max_right ..

lemma mono {g : X→Y→F} (hf : mixed f) (h : ∀ x y, ‖g x y‖ ≤ ‖f x y‖) :
    mixed g := by
  intro n
  obtain ⟨C,m,hc,h'⟩ := hf n
  exact ⟨C,m,hc,fun x y=>le_trans (mul_le_mul_of_nonneg_right (h x y) (by positivity)) (h' x y)⟩

lemma add (hf : mixed f) (hg : mixed g) : mixed fun x y => f x y + g x y := by
  intro n
  obtain ⟨C,m,hc,h⟩ := hf n
  obtain ⟨D,l,hd,h'⟩ := hg n
  refine ⟨C+D,m+l,by positivity,fun x y => ?_⟩
  calc
    _ ≤ (‖f x y‖+‖g x y‖)*(1+‖x‖)^n := by gcongr; apply norm_add_le
    _ ≤ C*(1+‖y‖)^m+D*(1+‖y‖)^l := by rw [add_mul]; exact add_le_add (h x y) (h' x y)
    _ ≤ _ := by rw [add_mul]; gcongr <;> simp

lemma neg (hf : mixed f) : mixed fun x y => -(f x y) := hf.mono (by simp)
lemma sub (hf : mixed f) (hg : mixed g) :
    mixed fun x y => f x y - g x y := by simpa [sub_eq_add_neg] using hf.add hg.neg

lemma product {G : Type*} [NormedAddCommGroup G]
    {g : X→Y→F} {h : X→Y→G} (hf : mixed f)
    (hg : PolyBound g.uncurry) (he : ∀ x y, ‖h x y‖ ≤ ‖f x y‖*‖g x y‖) : mixed h := by
  obtain ⟨C,m,hc,H⟩ := poly_prod_bound hg
  intro n
  obtain ⟨D,l,hd,H'⟩ := hf (n+m)
  refine ⟨C*D,l+m,by positivity,fun x y => ?_⟩
  calc
    _ ≤ (‖f x y‖*(C*(1+‖x‖)^m*(1+‖y‖)^m))*(1+‖x‖)^n := by
      apply mul_le_mul_of_nonneg_right ((he x y).trans (by gcongr; exact H x y)) (by positivity)
    _ = (‖f x y‖*(1+‖x‖)^(n+m))*(C*(1+‖y‖)^m) := by rw [pow_add]; ring
    _ ≤ (D*(1+‖y‖)^l)*(C*(1+‖y‖)^m) :=
      mul_le_mul_of_nonneg_right (H' x y) (by positivity)
    _ = _ := by rw [pow_add]; ring

-- Polynomial cutoff in layer
lemma of_cutoff (hf : PolyBound f.uncurry)
    {d : Y → ℝ} (hd : PolyBound d) (h : ∀ x y, d y < ‖x‖ → f x y = 0) :
    mixed f := by
  intro n
  obtain ⟨C,m,hc,H⟩ := poly_prod_bound hf
  obtain ⟨D,l,hD,H'⟩ := hd
  use C*(1+D)^(m+n),l*(m+n)+m,by positivity
  intro x y
  rcases lt_or_ge (d y) ‖x‖ with hxy|hxy
  · rw [h _ _ hxy,norm_zero, zero_mul]; positivity
  have hle : 1 + ‖x‖ ≤ (1+D)*(1+‖y‖)^l := by
    have he := H' y
    have hp : 1 ≤ (1+‖y‖)^l := one_le_pow₀ (by simp)
    have hz : d y ≤ ‖d y‖ := le_abs_self _
    linarith
  calc
    _ ≤ (C*(1+‖x‖)^m*(1+‖y‖)^m)*(1+‖x‖)^n :=
        mul_le_mul_of_nonneg_right (H x y) (by positivity)
    _ = C*(1+‖x‖)^(m+n)*(1+‖y‖)^m := by rw [pow_add]; ring
    _ ≤ C*((1+D)*(1+‖y‖)^l)^(m+n)*(1+‖y‖)^m := by gcongr
    _ = _ := by simp only [pow_mul,pow_add,mul_pow]; ring

lemma of_rapid {f : X → E} (h : rapid f) : mixed (fun x (_ : Y) => f x) :=
  fun n => by
    obtain ⟨C,hc,H⟩ := h n
    exact ⟨C,0,hc,fun x _=>by simpa using H x⟩
end mixed

section Integrals
variable [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsAddHaarMeasure μ]

lemma envelope_inv_int :
    Integrable (fun x:X => ((1+‖x‖)^(Module.finrank ℝ X+1))⁻¹) μ := by
  have H := (integrable_one_add_norm (μ := μ)
    (r := ((Module.finrank ℝ X+1:ℕ):ℝ)) (by exact_mod_cast Nat.lt_succ_self _))
  convert H using 1
  ext x; rw [Real.rpow_neg (by positivity),Real.rpow_natCast]

lemma mixed_integrable_left {f : X → Y → E}
    (h : mixed f) (y : Y) (hf : AEStronglyMeasurable (fun x => f x y) μ) :
    Integrable (fun x => f x y) μ := by
  obtain ⟨C,l,hc,H⟩ := h (Module.finrank ℝ X+1)
  refine ((envelope_inv_int (X := X)).const_mul (C*(1+‖y‖)^l)).mono' hf (ae_of_all _ fun x => ?_)
  rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]; apply H

lemma poly_integral_left [NormedSpace ℝ E] {f : X → Y → E}
    (h : mixed f)
    (hf : ∀ y, AEStronglyMeasurable (fun x=>f x y) μ) :
    PolyBound (fun y=>∫ x, f x y ∂μ) := by
  let p := Module.finrank ℝ X+1
  let g := fun x:X => ((1+‖x‖)^p)⁻¹
  obtain ⟨C,l,hc,H⟩ := h p
  have hg : Integrable g μ := envelope_inv_int
  refine ⟨C*(∫ x,g x ∂μ),l, mul_nonneg hc (integral_nonneg (fun x=>by unfold g; positivity)),fun y=>?_⟩
  calc
    _ ≤ ∫ x, ‖f x y‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, C*(1+‖y‖)^l * g x ∂μ :=
      integral_mono (mixed_integrable_left h y (hf y)).norm (hg.const_mul _) (fun x=>by
        dsimp only [g]; rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]
        apply H)
    _ = _ := by rw [integral_const_mul]; ring

variable [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
  {ν : Measure Y} [IsGaussian ν]

lemma mixed_integrable {f : X → Y → E}
    (h : mixed f) (hf : AEStronglyMeasurable f.uncurry (μ.prod ν)) :
    Integrable f.uncurry (μ.prod ν) := by
  let p := Module.finrank ℝ X+1
  let g := fun x:X => ((1+‖x‖)^p)⁻¹
  obtain ⟨C,l,hc,H⟩ := h p
  have hg : Integrable g μ := envelope_inv_int
  have hi := (hg.mul_prod ((integrable_envelope l (μ := ν)).const_mul C))
  apply hi.mono' hf (ae_of_all _ ?_)
  rintro ⟨x,y⟩
  change ‖f x y‖ ≤ g x * (C*(1+‖y‖)^l)
  dsimp only [g]; rw [ mul_comm, ← div_eq_mul_inv,le_div_iff₀ (by positivity)]
  apply H
end Integrals
end
end GeneralMahler

end

end OAI
