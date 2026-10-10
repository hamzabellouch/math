import OAI.NumberTheory.Ostmann.Characters.AffineFourier
import OAI.NumberTheory.Ostmann.Preliminaries.Autocorrelation

namespace OAI

/-!
# Identifying the Fourier matrix of the affine action

The finite matrix from `AffineFourier` is the action of
`F(t) ↦ ∑ c(a,b) F(at+b)` on nonzero additive frequencies.
-/

namespace Ostmann

open scoped BigOperators

theorem additiveFourier_sum {p : ℕ} [NeZero p] {ι : Type*}
    (s : Finset ι) (F : ι → ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => ∑ i ∈ s, F i x) a =
      ∑ i ∈ s, additiveFourier (F i) a := by
  simp only [additiveFourier_apply, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]

theorem additiveFourier_const_mul {p : ℕ} [NeZero p]
    (c : ℂ) (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => c * f x) a = c * additiveFourier f a := by
  simp only [additiveFourier_apply, mul_assoc]
  rw [← Finset.mul_sum]
  ring

theorem additiveFourier_add_right {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (b a : ZMod p) :
    additiveFourier (fun x => f (x + b)) a =
      ZMod.stdAddChar (b * a) * additiveFourier f a := by
  have h := additiveFourier_translation_sum f a (-b)
  simp only [sub_neg_eq_add, neg_mul, neg_neg] at h
  simp only [additiveFourier_apply]
  rw [h]
  ring

theorem additiveFourier_unit_mul {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (u : (ZMod p)ˣ) (a : ZMod p) :
    additiveFourier (fun x => f ((u : ZMod p) * x)) a =
      additiveFourier f (((u⁻¹ : (ZMod p)ˣ) : ZMod p) * a) := by
  exact congrArg (fun z : ℂ => (p : ℂ)⁻¹ * z) (ZMod.dft_comp_unitMul f u a)

theorem additiveFourier_affine_shift {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (u : (ZMod p)ˣ) (b a : ZMod p) :
    additiveFourier (fun x => f ((u : ZMod p) * x + b)) a =
      ZMod.stdAddChar (b * (((u⁻¹ : (ZMod p)ˣ) : ZMod p) * a)) *
        additiveFourier f (((u⁻¹ : (ZMod p)ˣ) : ZMod p) * a) := by
  rw [additiveFourier_unit_mul (fun x => f (x + b)), additiveFourier_add_right]

noncomputable def affineAction {p : ℕ} [Fact p.Prime]
    (c : (ZMod p)ˣ × ZMod p → ℂ) (f : ZMod p → ℂ) (t : ZMod p) : ℂ :=
  ∑ a : (ZMod p)ˣ, ∑ b : ZMod p, c (a, b) * f ((a : ZMod p) * t + b)

theorem additiveFourier_affineAction {p : ℕ} [Fact p.Prime]
    (c : (ZMod p)ˣ × ZMod p → ℂ) (f : ZMod p → ℂ) (η : (ZMod p)ˣ) :
    additiveFourier (affineAction c f) η =
      ∑ ξ : (ZMod p)ˣ, affineFourierMatrix c η ξ * additiveFourier f ξ := by
  classical
  have hfreq (ξ : (ZMod p)ˣ) :
      (((η / ξ)⁻¹ : (ZMod p)ˣ) : ZMod p) * (η : ZMod p) = (ξ : ZMod p) := by
    rw [← Units.val_mul]
    congr 1
    simp [div_eq_mul_inv, mul_assoc]
  unfold affineAction
  simp only [additiveFourier_sum, additiveFourier_const_mul,
    additiveFourier_affine_shift]
  calc
    _ = ∑ ξ : (ZMod p)ˣ, ∑ b : ZMod p, c (η / ξ, b) *
        (ZMod.stdAddChar (b * ((((η / ξ)⁻¹ : (ZMod p)ˣ) : ZMod p) * (η : ZMod p))) *
          additiveFourier f ((((η / ξ)⁻¹ : (ZMod p)ˣ) : ZMod p) * (η : ZMod p))) := by
      exact (((Equiv.inv (ZMod p)ˣ).trans (Equiv.mulLeft η)).bijective.sum_comp
        (fun a : (ZMod p)ˣ => ∑ b : ZMod p, c (a, b) *
          (ZMod.stdAddChar (b * (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * (η : ZMod p))) *
            additiveFourier f (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * (η : ZMod p))))).symm
    _ = _ := by
      simp_rw [hfreq]
      apply Finset.sum_congr rfl
      intro ξ _
      simp only [affineFourierMatrix, additiveCharacterSum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      rw [mul_comm b (ξ : ZMod p)]
      ring

theorem additiveFourier_affineAction_zero {p : ℕ} [Fact p.Prime]
    (c : (ZMod p)ˣ × ZMod p → ℂ) (f : ZMod p → ℂ)
    (hf : additiveFourier f 0 = 0) :
    additiveFourier (affineAction c f) 0 = 0 := by
  unfold affineAction
  simp only [additiveFourier_sum, additiveFourier_const_mul,
    additiveFourier_affine_shift, mul_zero, AddChar.map_zero_eq_one, hf,
    Finset.sum_const_zero]

theorem sum_units_eq_sum_of_zero {p : ℕ} [Fact p.Prime]
    {R : Type*} [AddCommMonoid R] (F : ZMod p → R) (hF : F 0 = 0) :
    (∑ u : (ZMod p)ˣ, F u) = ∑ x : ZMod p, F x := by
  classical
  calc
    _ = ∑ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, F x := by
      apply Finset.sum_bij (fun (u : (ZMod p)ˣ) _ => (u : ZMod p))
      · intro u _
        exact Finset.mem_erase.mpr ⟨Units.ne_zero u, Finset.mem_univ _⟩
      · intro u _ v _ huv
        exact Units.val_injective huv
      · intro x hx
        refine ⟨Units.mk0 x (Finset.mem_erase.mp hx).1, Finset.mem_univ _, rfl⟩
      · intro _ _
        rfl
    _ = ∑ x : ZMod p, F x := by
      simpa only [hF, add_zero] using
        Finset.sum_erase_add (Finset.univ : Finset (ZMod p)) F (Finset.mem_univ 0)

/-- The affine action on mean-zero functions, in counting-measure squared norm. -/
theorem affineAction_energy_bound {p : ℕ} [Fact p.Prime]
    (c : (ZMod p)ˣ × ZMod p → ℂ) (f : ZMod p → ℂ)
    (hf : additiveFourier f 0 = 0) :
    (∑ t : ZMod p, ‖affineAction c f t‖ ^ 2) ≤
      ((p : ℝ) * ∑ ab : (ZMod p)ˣ × ZMod p, ‖c ab‖ ^ 2) *
        ∑ t : ZMod p, ‖f t‖ ^ 2 := by
  have hp : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have hout := sum_units_eq_sum_of_zero
    (fun a : ZMod p => ‖additiveFourier (affineAction c f) a‖ ^ 2)
    (by rw [additiveFourier_affineAction_zero c f hf, norm_zero, zero_pow (by decide)])
  have hin := sum_units_eq_sum_of_zero (fun a : ZMod p => ‖additiveFourier f a‖ ^ 2)
    (by rw [hf, norm_zero, zero_pow (by decide)])
  calc
    _ = (p : ℝ) * ∑ η : (ZMod p)ˣ,
        ‖∑ ξ : (ZMod p)ˣ, affineFourierMatrix c η ξ * additiveFourier f ξ‖ ^ 2 := by
      rw [additiveFourier_energy, ← hout]
      simp_rw [additiveFourier_affineAction]
    _ ≤ (p : ℝ) * (((p : ℝ) * ∑ ab : (ZMod p)ˣ × ZMod p, ‖c ab‖ ^ 2) *
        ∑ ξ : (ZMod p)ˣ, ‖additiveFourier f ξ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (affineFourier_action_energy_bound c (fun ξ => additiveFourier f ξ)) hp
    _ = _ := by rw [hin, additiveFourier_energy f]; ring

/-- The coefficient array arising from `T* T` has squared action norm at most `3/p`. -/
theorem affineAction_collected_energy_bound {p : ℕ} [Fact p.Prime]
    (G : (ZMod p)ˣ → ℂ) (hG : (∑ r : (ZMod p)ˣ, ‖G r‖ ^ 2) ≤ (p : ℝ))
    (f : ZMod p → ℂ) (hf : additiveFourier f 0 = 0) :
    (∑ t : ZMod p, ‖affineAction (affineCoefficient G) f t‖ ^ 2) ≤
      (3 / (p : ℝ)) * ∑ t : ZMod p, ‖f t‖ ^ 2 := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  refine (affineAction_energy_bound (affineCoefficient G) f hf).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  calc
    _ ≤ (p : ℝ) * (3 / (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (affineCoefficient_sq_sum_le G hG) hp.le
    _ = 3 / (p : ℝ) := by field_simp [ne_of_gt hp]

end Ostmann

end OAI
