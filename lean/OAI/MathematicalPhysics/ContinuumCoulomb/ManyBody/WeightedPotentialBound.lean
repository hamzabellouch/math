import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.TruncatedNuclearForm

namespace OAI

/-! Integrate a pointwise potential error with explicit near-pole terms on
an arbitrary weak-H1 state. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem weighted_potential_truncated_bound {α : Type*} [Fintype α]
    {n : ℕ} (u : Coulomb.H1Vector n) (s : SpinConfiguration n) (i : Fin n)
    (F : Position → ℝ) (hF : Measurable F) (R : α → Position) (r B c : ℝ)
    (hbound : ∀ y, |F y| ≤ B+c*(∑ a, Coulomb.truncatedCoulomb r (y-R a))) :
    Integrable (fun x => F (Coulomb.position x i)*‖u.value s x‖^2) ∧
    |∫ x, F (Coulomb.position x i)*‖u.value s x‖^2| ≤
      B*(∫ x, ‖u.value s x‖^2)+c*(∑ a, ∫ x,
        Coulomb.truncatedCoulomb r (Coulomb.position x i-R a)*‖u.value s x‖^2) := by
  let T : α → Configuration n → ℝ := fun a x =>
    Coulomb.truncatedCoulomb r (Coulomb.position x i-R a)*‖u.value s x‖^2
  have hT (a : α) : Integrable (T a) := (truncated_nuclear_integrable_bound u s i (R a) r).1
  have hmass := (u.value_L2 s).integrable_norm_pow (p := 2) (by decide)
  have hdom : Integrable (fun x => B*‖u.value s x‖^2+c*(∑ a, T a x)) :=
    (hmass.const_mul B).add ((integrable_finsetSum _ (fun a _ => hT a)).const_mul c)
  have hnorm (x : Configuration n) :
      ‖F (Coulomb.position x i)*‖u.value s x‖^2‖ ≤ B*‖u.value s x‖^2+c*(∑ a, T a x) := by
    rw [norm_mul,Real.norm_eq_abs,Real.norm_of_nonneg (sq_nonneg _)]
    have hb := mul_le_mul_of_nonneg_right (hbound (Coulomb.position x i)) (sq_nonneg ‖u.value s x‖)
    apply hb.trans_eq
    simp only [add_mul,mul_assoc,Finset.sum_mul,T]
  have hI : Integrable (fun x => F (Coulomb.position x i)*‖u.value s x‖^2) :=
    hdom.mono' (((hF.comp (Coulomb.positionCLM i).continuous.measurable).aestronglyMeasurable).mul
      ((u.value_L2 s).aestronglyMeasurable.norm.pow 2)) (Filter.Eventually.of_forall hnorm)
  refine ⟨hI,?_⟩
  calc
    _ ≤ ∫ x, ‖F (Coulomb.position x i)*‖u.value s x‖^2‖ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => F (Coulomb.position x i)*‖u.value s x‖^2)
    _ ≤ ∫ x, B*‖u.value s x‖^2+c*(∑ a, T a x) := integral_mono hI.norm hdom hnorm
    _ = B*(∫ x, ‖u.value s x‖^2)+c*(∑ a, ∫ x, T a x) := by
      rw [integral_add (hmass.const_mul B) ((integrable_finsetSum _ (fun a _ => hT a)).const_mul c),
        integral_const_mul,integral_const_mul,integral_finsetSum _ (fun a _ => hT a)]

theorem weighted_potential_absolute_bound {α : Type*} [Fintype α]
    {n : ℕ} (u : Coulomb.H1Vector n) (s : SpinConfiguration n) (i : Fin n)
    (F : Position → ℝ) (hF : Measurable F) (R : α → Position) (r B c : ℝ)
    (hbound : ∀ y, |F y| ≤ B+c*(∑ a, Coulomb.truncatedCoulomb r (y-R a))) :
    Integrable (fun x => |F (Coulomb.position x i)| * ‖u.value s x‖^2) ∧
    (∫ x, |F (Coulomb.position x i)| * ‖u.value s x‖^2) ≤
      B*(∫ x, ‖u.value s x‖^2)+c*(∑ a, ∫ x,
        Coulomb.truncatedCoulomb r (Coulomb.position x i-R a)*‖u.value s x‖^2) := by
  have he := weighted_potential_truncated_bound u s i (fun y => |F y|) hF.abs R r B c
    (fun y => by simpa only [abs_abs] using hbound y)
  rw [abs_of_nonneg (integral_nonneg (fun x => mul_nonneg (abs_nonneg _) (sq_nonneg _)))] at he
  exact he

end ContinuumCoulomb

end

end OAI
