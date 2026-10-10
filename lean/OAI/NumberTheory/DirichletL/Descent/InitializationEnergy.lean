import OAI.NumberTheory.DirichletL.Inversion.InitialFibers
import OAI.NumberTheory.DirichletL.Descent.Fibers
import OAI.NumberTheory.DirichletL.Descent.Sharp

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CanonicalQuadraticSieve SevenEighths.InverseInitialFibers
open IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

abbrev InitialChild := Ideal Eis × Ideal Eis × Eis

def initialChild {J : ℕ} (x : InitialTuple J) : InitialChild :=
  (idealQuotient x.divisor x.common, x.divisor * x.residual,
    primaryGenerator x.divisor * x.frequency)

structure InitialSourceValid {J : ℕ} (x : InitialTuple J) : Prop where
  common_ne_zero : x.common ≠ 0
  residual_ne_zero : x.residual ≠ 0
  divisor_good : primaryGenerator x.divisor ≠ 0
  divisor_dvd : x.divisor ∣ x.common
  assigned_dvd : ∀ i, (x.assigned i).val ∣ x.common * x.residual

theorem initialChild_valid {J : ℕ} (x : InitialTuple J) (hx : InitialSourceValid x) :
    Valid x (initialChild x).1 (initialChild x).2.1 (initialChild x).2.2 := by
  have ht : idealQuotient x.divisor x.common * x.divisor = x.common := by
    rw [mul_comm, idealQuotient_mul hx.divisor_dvd]
  refine ⟨ht, rfl, hx.divisor_good, rfl, ?_⟩
  intro i
  change (x.assigned i).val ∣ idealQuotient x.divisor x.common * (x.divisor * x.residual)
  rw [← mul_assoc, ht]
  exact hx.assigned_dvd i

theorem initialChild_nonzero {J : ℕ} (x : InitialTuple J) (hx : InitialSourceValid x) :
    (initialChild x).1 ≠ 0 ∧ (initialChild x).2.1 ≠ 0 := by
  have hD : x.divisor ≠ 0 := by intro he; exact hx.divisor_good (by simp [he])
  constructor
  · intro ht
    have he := (initialChild_valid x hx).common_eq
    rw [ht, zero_mul] at he
    exact hx.common_ne_zero he.symm
  · exact mul_ne_zero hD hx.residual_ne_zero

def initialQuotientSet {J : ℕ} (source : Finset (InitialTuple J)) : Finset (Ideal Eis) :=
  source.image (fun x => (initialChild x).1)

def initialDivisorWeight (J : ℕ) (c : InitialChild) : ℝ :=
  ((idealDivisors c.2.1).card : ℝ) ^ (J + 1) * ((idealDivisors c.1).card : ℝ) ^ J

theorem initialChild_fiber_weight {J : ℕ} (source : Finset (InitialTuple J))
    (hsource : ∀ x ∈ source, InitialSourceValid x) (c : InitialChild)
    (ht : c.1 ≠ 0) (hf : c.2.1 ≠ 0) (w : InitialTuple J → ℝ)
    (hw : ∀ x ∈ source, w x ≤ 1) :
    (∑ x ∈ source with initialChild x = c, w x) ≤ initialDivisorWeight J c := by
  have hvalid : ∀ x ∈ source.filter (fun x => initialChild x = c), Valid x c.1 c.2.1 c.2.2 := by
    intro x hx
    obtain ⟨hxs, he⟩ := Finset.mem_filter.mp hx
    simpa only [he] using initialChild_valid x (hsource x hxs)
  calc
    _ ≤ ∑ _x ∈ source.filter (fun x => initialChild x = c), (1 : ℝ) :=
      Finset.sum_le_sum (fun x hx => hw x (Finset.mem_filter.mp hx).1)
    _ = ((source.filter (fun x => initialChild x = c)).card : ℝ) := by simp
    _ ≤ initialDivisorWeight J c := by
      have hh := valid_tuple_card_le_separated _ c.1 c.2.1 c.2.2 ht hf hvalid
      dsimp only [initialDivisorWeight]
      exact_mod_cast hh

theorem initial_energy_projection {J : ℕ} (source : Finset (InitialTuple J))
    (hsource : ∀ x ∈ source, InitialSourceValid x)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ source, (initialChild x).2.1 ∈ labels ∧ (initialChild x).2.2 ∈ rows)
    (w : InitialTuple J → ℝ) (hw : ∀ x ∈ source, w x ≤ 1) (F : InitialChild → ℂ) :
    (∑ x ∈ source, w x * ‖F (initialChild x)‖ ^ 2) ≤
      ∑ t ∈ initialQuotientSet source, ((idealDivisors t).card : ℝ) ^ J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ) ^ (J + 1) *
          ∑ k ∈ rows, ‖F (t, f, k)‖ ^ 2 := by
  have hmaps : ∀ x ∈ source, initialChild x ∈ initialQuotientSet source ×ˢ (labels ×ˢ rows) := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      Finset.mem_product.mpr (hchild x hx)⟩
  have hfiber : ∀ c ∈ initialQuotientSet source ×ˢ (labels ×ˢ rows),
      (∑ x ∈ source with initialChild x = c, w x) ≤ initialDivisorWeight J c := by
    intro c hc
    obtain ⟨ht, hfk⟩ := Finset.mem_product.mp hc
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp ht
    have ht0 : c.1 ≠ 0 := he ▸ (initialChild_nonzero x (hsource x hx)).1
    exact initialChild_fiber_weight source hsource c ht0
      (hlabels c.2.1 (Finset.mem_product.mp hfk).1) w hw
  have he := fiber_energy_bound source (initialQuotientSet source ×ˢ (labels ×ˢ rows))
    initialChild w (initialDivisorWeight J) (fun c => ‖F c‖ ^ 2) hmaps
    (fun _ _ => sq_nonneg _) hfiber
  apply he.trans_eq
  simp only [Finset.sum_product, initialDivisorWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro k hk
  ring

def initialPositiveEnergy {J : ℕ} (source : Finset (InitialTuple J))
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (F : InitialChild → ℂ) : ℝ :=
  ∑ t ∈ initialQuotientSet source, ((idealDivisors t).card : ℝ) ^ J *
    ∑ f ∈ labels, ((idealDivisors f).card : ℝ) ^ (J + 1) *
      ∑ k ∈ rows, ‖F (t, f, k)‖ ^ 2

theorem initialPositiveEnergy_nonneg {J : ℕ} (source : Finset (InitialTuple J))
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (F : InitialChild → ℂ) :
    0 ≤ initialPositiveEnergy source labels rows F := by
  unfold initialPositiveEnergy
  positivity

theorem initial_weighted_count {J : ℕ} (source : Finset (InitialTuple J))
    (hsource : ∀ x ∈ source, InitialSourceValid x)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ source, (initialChild x).2.1 ∈ labels ∧ (initialChild x).2.2 ∈ rows)
    (w : InitialTuple J → ℝ) (hw0 : ∀ x ∈ source, 0 ≤ w x) (hw1 : ∀ x ∈ source, w x ≤ 1)
    (F G : InitialChild → ℂ) :
    ‖∑ x ∈ source, (w x : ℂ) * F (initialChild x) * star (G (initialChild x))‖ ≤
      Real.sqrt (initialPositiveEnergy source labels rows F) *
        Real.sqrt (initialPositiveEnergy source labels rows G) := by
  have hF := initial_energy_projection source hsource labels rows hlabels hchild w hw1 F
  have hG := initial_energy_projection source hsource labels rows hlabels hchild w hw1 G
  apply (weighted_cauchy source w (F ∘ initialChild) (G ∘ initialChild) hw0).trans
  exact mul_le_mul (Real.sqrt_le_sqrt hF) (Real.sqrt_le_sqrt hG)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem initial_weighted_count_normalized {J : ℕ} (source : Finset (InitialTuple J))
    (hsource : ∀ x ∈ source, InitialSourceValid x)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ source, (initialChild x).2.1 ∈ labels ∧ (initialChild x).2.2 ∈ rows)
    (w : InitialTuple J → ℝ) (hw0 : ∀ x ∈ source, 0 ≤ w x) (hw1 : ∀ x ∈ source, w x ≤ 1)
    (F G : InitialChild → ℂ) (H : ℝ) (hH : 0 < H) :
    ‖∑ x ∈ source, (w x : ℂ) * F (initialChild x) * star (G (initialChild x))‖ ≤
      H * (Real.sqrt (H⁻¹ * initialPositiveEnergy source labels rows F) *
        Real.sqrt (H⁻¹ * initialPositiveEnergy source labels rows G)) := by
  apply (initial_weighted_count source hsource labels rows hlabels hchild w hw0 hw1 F G).trans_eq
  rw [Real.sqrt_mul (inv_nonneg.mpr hH.le), Real.sqrt_mul (inv_nonneg.mpr hH.le)]
  have hc : H * (Real.sqrt H⁻¹) ^ 2 = 1 := by
    rw [Real.sq_sqrt (inv_nonneg.mpr hH.le), mul_inv_cancel₀ hH.ne']
  calc
    _ = (H * (Real.sqrt H⁻¹) ^ 2) *
        (Real.sqrt (initialPositiveEnergy source labels rows F) *
          Real.sqrt (initialPositiveEnergy source labels rows G)) := by rw [hc, one_mul]
    _ = _ := by ring

end
end SevenEighths.InverseMoment

end OAI
