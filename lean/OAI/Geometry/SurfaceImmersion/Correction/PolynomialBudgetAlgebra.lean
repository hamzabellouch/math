import OAI.Geometry.SurfaceImmersion.Correction.PositivePolynomialBounds

namespace OAI

/-! Finite composition and inverse-scale evaluation of the polynomial
budgets in the correction construction. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

lemma HasPolynomialBound.of_le {f g : ℝ → ℝ} (hg : HasPolynomialBound g)
    (h0 : ∀ x, 1 ≤ x → 0 ≤ f x) (hle : ∀ x, 1 ≤ x → f x ≤ g x) :
    HasPolynomialBound f := by
  obtain ⟨d,C,hC,hg⟩ := hg
  exact ⟨d,C,hC,fun x hx => ⟨h0 x hx,(hle x hx).trans (hg x hx).2⟩⟩

lemma HasPolynomialBound.max {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) : HasPolynomialBound (fun x => max (f x) (g x)) := by
  have hfn : ∀ x, 1 ≤ x → 0 ≤ f x := by
    obtain ⟨_,_,_,h⟩ := hf
    exact fun x hx => (h x hx).1
  have hgn : ∀ x, 1 ≤ x → 0 ≤ g x := by
    obtain ⟨_,_,_,h⟩ := hg
    exact fun x hx => (h x hx).1
  exact (hf.add hg).of_le (fun x hx => (hfn x hx).trans (le_max_left _ _))
    (fun x hx => max_le (le_add_of_nonneg_right (hgn x hx)) (le_add_of_nonneg_left (hfn x hx)))

lemma HasPolynomialBound.sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, HasPolynomialBound (f i)) :
    HasPolynomialBound (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using polynomialBound_const (show (0:ℝ) ≤ 0 by rfl)
  | @insert i s hi ih =>
    have h := (hf i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using h

lemma HasPolynomialBound.comp {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) (hge : ∀ x, 1 ≤ x → 1 ≤ g x) :
    HasPolynomialBound (fun x => f (g x)) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  obtain ⟨e,D,hD,hg⟩ := hg
  refine ⟨e*d,C*D^d,one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hD),?_⟩
  intro x hx
  refine ⟨(hf (g x) (hge x hx)).1,?_⟩
  calc
    f (g x) ≤ C*(g x)^d := (hf (g x) (hge x hx)).2
    _ ≤ C*(D*x^e)^d := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hg x hx).1 (hg x hx).2 _) (zero_le_one.trans hC)
    _ = (C*D^d)*x^(e*d) := by rw [mul_pow,pow_mul]; ring

/-- Polynomial degree is chosen before all multiplicative constants. -/
theorem HasPolynomialBound.at_inverse_scale {f : ℝ → ℝ} (hf : HasPolynomialBound f)
    (p : ℕ) : ∃ d : ℕ, ∀ D : ℝ, 1 ≤ D → ∃ C : ℝ, 1 ≤ C ∧
      ∀ z : ℝ, 0 < z → z ≤ 1 → 0 ≤ f (D/z^p) ∧ f (D/z^p) ≤ C/z^d := by
  obtain ⟨d,A,hA,hf⟩ := hf
  refine ⟨p*d,fun D hD => ⟨A*D^d,one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hD),?_⟩⟩
  intro z hz hz1
  have hzD : 1 ≤ D/z^p := by
    apply (le_div_iff₀ (pow_pos hz p)).mpr
    simpa only [one_mul] using (pow_le_one₀ hz.le hz1).trans hD
  refine ⟨(hf _ hzD).1,?_⟩
  calc
    f (D/z^p) ≤ A*(D/z^p)^d := (hf _ hzD).2
    _ = (A*D^d)/z^(p*d) := by rw [div_pow,pow_mul]; ring

end ClosedSurfaceR4.RealModes

end

end OAI
