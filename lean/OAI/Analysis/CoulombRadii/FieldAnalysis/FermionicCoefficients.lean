import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.Space

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

open scoped Classical

def FermionicCoefficients {n : ℕ} {α : Type*} (f : (Fin n → α) → ℂ) : Prop :=
  ∀ (p : Equiv.Perm (Fin n)) b, f (b ∘ p) = ((p.sign : ℤ) : ℂ) * f b

lemma FermionicCoefficients.vanish_of_repeat {n : ℕ} {α : Type*}
    {f : (Fin n → α) → ℂ} (hf : FermionicCoefficients f)
    {b : Fin n → α} {i j : Fin n} (hij : i ≠ j) (hb : b i = b j) : f b = 0 := by
  classical
  have heq : b ∘ Equiv.swap i j = b := by
    funext k
    by_cases hi : k = i
    · subst k; simpa using hb.symm
    by_cases hj : k = j
    · subst k; simpa using hb
    simp [Equiv.swap_apply_of_ne_of_ne hi hj]
  have h := hf (Equiv.swap i j) b
  rw [heq, Equiv.Perm.sign_swap hij] at h
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at h
  have hz : 2 * f b = 0 := by linear_combination h
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

lemma FermionicCoefficients.pointwise_occupation {n : ℕ} {α : Type*}
    {f : (Fin n → α) → ℂ} (hf : FermionicCoefficients f) (a : α) (b : Fin n → α) :
    (∑ i, if b i = a then ‖f b‖^2 else (0 : ℝ)) ≤ ‖f b‖^2 := by
  classical
  by_cases hz : f b = 0
  · simp [hz]
  have hinj : Function.Injective b := by
    intro i j heq
    by_contra hne
    exact hz (hf.vanish_of_repeat hne heq)
  by_cases he : ∃ i, b i = a
  · obtain ⟨i, hi⟩ := he
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      have hj : b j ≠ a := by intro h; exact hji (hinj (h.trans hi.symm))
      simp [hj]
    · simp
  · simp only [not_exists] at he
    simp only [ite_eq_right (he _), Finset.sum_const_zero]
    positivity

lemma FermionicCoefficients.occupation_sum {n : ℕ} {α : Type*}
    {f : (Fin n → α) → ℂ} (hf : FermionicCoefficients f)
    (hs : Summable (fun b => ‖f b‖^2)) (a : α) :
    (∑' b, ∑ i, if b i = a then ‖f b‖^2 else (0 : ℝ)) ≤ ∑' b, ‖f b‖^2 := by
  apply Summable.tsum_le_tsum (fun b => hf.pointwise_occupation a b) _ hs
  exact Summable.of_nonneg_of_le (fun b => Finset.sum_nonneg (fun i _ => by positivity))
    (fun b => hf.pointwise_occupation a b) hs

noncomputable def coefficientPermEquiv {n : ℕ} {α : Type*} (p : Equiv.Perm (Fin n)) :
    (Fin n → α) ≃ (Fin n → α) where
  toFun b := b ∘ p
  invFun b := b ∘ p.symm
  left_inv b := by ext i; simp
  right_inv b := by ext i; simp

lemma FermionicCoefficients.norm_permute {n : ℕ} {α : Type*}
    {f : (Fin n → α) → ℂ} (hf : FermionicCoefficients f)
    (p : Equiv.Perm (Fin n)) (b : Fin n → α) : ‖f (b ∘ p)‖ = ‖f b‖ := by
  rw [hf p b, norm_mul]
  have hsign : ‖((p.sign : ℤ) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or (p.sign) with h | h <;> simp [h]
  rw [hsign, one_mul]

lemma FermionicCoefficients.occupation_eq {n : ℕ} {α : Type*}
    {f : (Fin n → α) → ℂ} (hf : FermionicCoefficients f)
    (a : α) (i j : Fin n) :
    (∑' b, if b i = a then ‖f b‖^2 else (0 : ℝ)) =
      ∑' b, if b j = a then ‖f b‖^2 else (0 : ℝ) := by
  classical
  let p := Equiv.swap i j
  have he := (coefficientPermEquiv (α := α) p).tsum_eq
    (fun b => if b i = a then ‖f b‖^2 else (0 : ℝ))
  change (∑' b, if (b ∘ p) i = a then ‖f (b ∘ p)‖^2 else (0 : ℝ)) = _ at he
  simp only [Function.comp_apply, p, Equiv.swap_apply_left, hf.norm_permute] at he
  exact he.symm

theorem FermionicCoefficients.pauli_bound {n : ℕ} {α : Type*}
    {f : (Fin n → α) → ℂ} (hf : FermionicCoefficients f)
    (hs : Summable (fun b => ‖f b‖^2)) (a : α) (i : Fin n) :
    (n : ℝ) * (∑' b, if b i = a then ‖f b‖^2 else (0 : ℝ)) ≤ ∑' b, ‖f b‖^2 := by
  classical
  have hsi : ∀ j : Fin n, Summable (fun b => if b j = a then ‖f b‖^2 else (0 : ℝ)) := by
    intro j
    exact Summable.of_nonneg_of_le (fun b => by positivity)
      (fun b => by split_ifs <;> simp) hs
  have heq : (∑' b, ∑ j : Fin n, if b j = a then ‖f b‖^2 else (0 : ℝ)) =
      (n : ℝ) * (∑' b, if b i = a then ‖f b‖^2 else (0 : ℝ)) := by
    rw [Summable.tsum_finsetSum (fun j _ => hsi j)]
    simp_rw [hf.occupation_eq a _ i]
    simp
  rw [← heq]
  exact hf.occupation_sum hs a

noncomputable def permuteIsometry {n : ℕ} (p : Equiv.Perm (Fin n)) :
    Configuration n ≃ₗᵢ[ℝ] Configuration n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p.symm.prodCongr (Equiv.refl (Fin 3)))

lemma permuteIsometry_apply {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Configuration n) :
    permuteIsometry p x = permute p x := by
  ext a
  rfl

lemma permute_measurePreserving {n : ℕ} (p : Equiv.Perm (Fin n)) :
    MeasurePreserving (permute p) volume volume := by
  convert (permuteIsometry p).measurePreserving using 1; rfl

lemma integral_permute {n : ℕ} (p : Equiv.Perm (Fin n))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Configuration n → E) :
    (∫ x, f (permute p x)) = ∫ x, f x := by
  have h := (permuteIsometry p).measurePreserving.integral_comp
    (permuteIsometry p).toHomeomorph.measurableEmbedding f
  simpa only [permuteIsometry_apply] using h

noncomputable def spinPermEquiv {n : ℕ} (p : Equiv.Perm (Fin n)) : Spins n ≃ Spins n where
  toFun s := s ∘ p
  invFun s := s ∘ p.symm
  left_inv s := by ext i; simp
  right_inv s := by ext i; simp

lemma sign_complex_norm {n : ℕ} (p : Equiv.Perm (Fin n)) :
    ‖((p.sign : ℤ) : ℂ)‖ = 1 := by
  rcases Int.units_eq_one_or (p.sign) with h | h <;> simp [h]

lemma Antisymmetric.norm_permute {n : ℕ} {ψ : H1Vector n} (hψ : Antisymmetric ψ)
    (p : Equiv.Perm (Fin n)) (s : Spins n) :
    ∀ᵐ x ∂volume, ‖ψ.value (s ∘ p) (permute p x)‖ = ‖ψ.value s x‖ := by
  filter_upwards [hψ p s] with x hx
  rw [hx, norm_mul, sign_complex_norm, one_mul]

lemma antisymmetric_expectation_permute {n : ℕ} {ψ : H1Vector n} (hψ : Antisymmetric ψ)
    (p : Equiv.Perm (Fin n)) (f : Configuration n → ℝ) :
    (∑ s, ∫ x, f (permute p x) * ‖ψ.value s x‖^2) =
      ∑ s, ∫ x, f x * ‖ψ.value s x‖^2 := by
  have he : ∀ s, (∫ x, f (permute p x) * ‖ψ.value s x‖^2) =
      ∫ x, f x * ‖ψ.value (s ∘ p) x‖^2 := by
    intro s
    calc
      _ = ∫ x, f (permute p x) * ‖ψ.value (s ∘ p) (permute p x)‖^2 := by
        apply integral_congr_ae
        filter_upwards [hψ.norm_permute p s] with x hx
        rw [hx]
      _ = _ := integral_permute p (fun x => f x * ‖ψ.value (s ∘ p) x‖^2)
  simp_rw [he]
  exact (spinPermEquiv p).sum_comp (fun s => ∫ x, f x * ‖ψ.value s x‖^2)

noncomputable def tensorOrbital {n : ℕ} {α : Type*}
    (v : α → Space → Fin 2 → ℂ) (b : Fin n → α) (s : Spins n) (x : Configuration n) : ℂ :=
  ∏ i, v (b i) (position x i) (s i)

lemma position_permute {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Configuration n) (i : Fin n) :
    position (permute p x) i = position x (p i) := rfl

lemma tensorOrbital_permute {n : ℕ} {α : Type*}
    (v : α → Space → Fin 2 → ℂ) (b : Fin n → α) (p : Equiv.Perm (Fin n))
    (s : Spins n) (x : Configuration n) :
    tensorOrbital v (b ∘ p) (s ∘ p) (permute p x) = tensorOrbital v b s x := by
  unfold tensorOrbital
  simp only [Function.comp_apply, position_permute]
  exact Equiv.prod_comp p (fun i => v (b i) (position x i) (s i))

noncomputable def orbitalCoefficient {n : ℕ} {α : Type*} (ψ : H1Vector n)
    (v : α → Space → Fin 2 → ℂ) (b : Fin n → α) : ℂ :=
  ∑ s, ∫ x, star (tensorOrbital v b s x) * ψ.value s x

lemma orbitalCoefficient_antisymmetric {n : ℕ} {α : Type*} {ψ : H1Vector n}
    (hψ : Antisymmetric ψ) (v : α → Space → Fin 2 → ℂ)
    (p : Equiv.Perm (Fin n)) (b : Fin n → α) :
    orbitalCoefficient ψ v (b ∘ p) = ((p.sign : ℤ) : ℂ) * orbitalCoefficient ψ v b := by
  unfold orbitalCoefficient
  rw [← (spinPermEquiv p).sum_comp (fun s =>
    ∫ x, star (tensorOrbital v (b ∘ p) s x) * ψ.value s x)]
  simp only [spinPermEquiv, Equiv.coe_fn_mk]
  have he : ∀ s, (∫ x, star (tensorOrbital v (b ∘ p) (s ∘ p) x) * ψ.value (s ∘ p) x) =
      ((p.sign : ℤ) : ℂ) * ∫ x, star (tensorOrbital v b s x) * ψ.value s x := by
    intro s
    rw [← integral_permute p (fun x =>
      star (tensorOrbital v (b ∘ p) (s ∘ p) x) * ψ.value (s ∘ p) x)]
    simp only [tensorOrbital_permute]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hψ p s] with x hx
    rw [hx]
    ring
  simp_rw [he]
  rw [Finset.mul_sum]

end Coulomb

end
end

end OAI
