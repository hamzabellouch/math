import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.SlaterPole

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_OrbitalPole_scope

open MeasureTheory Filter
open scoped BigOperators ContDiff

def orbitalPole (φ : SlaterParticle → ℂ) (a : Space) : ℝ :=
  ∫ z : SlaterParticle, ‖φ z‖^2 / ‖a-z.2‖ ∂slaterParticleMeasure

lemma orbitalPole_nonneg (φ : SlaterParticle → ℂ) (a : Space) : 0 ≤ orbitalPole φ a :=
  integral_nonneg (fun _z => div_nonneg (sq_nonneg _) (norm_nonneg _))

lemma orbitalPole_spins {φ : SlaterParticle → ℂ}
    (hφ : ∀ s, ContDiff ℝ ∞ (fun x : Space => φ (s,x)))
    (hc : ∀ s, HasCompactSupport (fun x : Space => φ (s,x))) (a : Space) :
    orbitalPole φ a = ∑ s : Fin 2, ∫ y : Space, ‖φ (s,y)‖^2 / ‖a-y‖ := by
  rw [orbitalPole,integral_prod _ (orbital_pole_integrable hφ hc a),integral_count]

lemma orbitalPole_continuous {φ : SlaterParticle → ℂ}
    (hφ : ∀ s, ContDiff ℝ ∞ (fun x : Space => φ (s,x)))
    (hc : ∀ s, HasCompactSupport (fun x : Space => φ (s,x))) : Continuous (orbitalPole φ) := by
  have he : orbitalPole φ = fun a => ∑ s : Fin 2, ∫ y : Space, ‖φ (s,y)‖^2 / ‖a-y‖ :=
    funext (orbitalPole_spins hφ hc)
  rw [he]
  apply continuous_finsetSum
  intro s _
  have hs := compact_norm_sq (hc s)
  have hd : Continuous (fun x : Space => ‖φ (s,x)‖^2) := (hφ s).continuous.norm.pow 2
  exact CoulombAnalysis.tfPotential_continuous (hd.integrable_of_hasCompactSupport hs)
    (hd.memLp_of_hasCompactSupport hs)

end Work_OrbitalPole_scope

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def occupationWeight (p : ι → ℝ) (m : ι → Bool) : ℝ :=
  ∏ i, if m i then p i else 1-p i

omit [DecidableEq ι] in
lemma occupationWeight_nonneg {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (m : ι → Bool) : 0 ≤ occupationWeight p m := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact (hp i).1
  · exact sub_nonneg.mpr (hp i).2

lemma occupation_product (p : ι → ℝ) (f : ι → Bool → ℝ) :
    (∑ m : ι → Bool, occupationWeight p m * ∏ i, f i (m i)) =
      ∏ i, ((1-p i) * f i false + p i * f i true) := by
  simp only [occupationWeight, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b => (if b then p i else 1-p i)*f i b)]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  ring

lemma occupationWeight_sum (p : ι → ℝ) : (∑ m : ι → Bool, occupationWeight p m) = 1 := by
  simpa only [Finset.prod_const_one,mul_one,sub_add_cancel,Finset.prod_const_one] using
    occupation_product p (fun _ _ => 1)

lemma occupation_first (p : ι → ℝ) (j : ι) :
    (∑ m : ι → Bool, occupationWeight p m * (if m j then 1 else 0)) = p j := by
  have hp := occupation_product p (fun i b => if i=j then (if b then 1 else 0) else 1)
  have he (m : ι → Bool) :
      (∏ i : ι, if i=j then (if m i then (1:ℝ) else 0) else 1) = if m j then 1 else 0 := by
    simp
  simp_rw [he] at hp
  rw [hp]
  trans ∏ i : ι, if i=j then p i else 1
  · apply Finset.prod_congr rfl
    intro i _
    by_cases hij : i=j <;> simp [hij]
  · simp

lemma occupation_second {p : ι → ℝ} {j k : ι} (hjk : j ≠ k) :
    (∑ m : ι → Bool, occupationWeight p m *
      ((if m j then 1 else 0) * (if m k then 1 else 0))) = p j*p k := by
  have hp := occupation_product p (fun i b =>
    (if i=j then (if b then (1:ℝ) else 0) else 1) *
    (if i=k then (if b then (1:ℝ) else 0) else 1))
  simp only [Finset.prod_mul_distrib] at hp
  have he (m : ι → Bool) (r : ι) :
      (∏ i : ι, if i=r then (if m i then (1:ℝ) else 0) else 1) = if m r then 1 else 0 := by
    simp
  simp_rw [he] at hp
  rw [hp]
  trans ∏ i : ι, (if i=j then p i else 1) * (if i=k then p i else 1)
  · apply Finset.prod_congr rfl
    intro i _
    by_cases hij : i=j
    · subst i; simp [hjk]
    · by_cases hik : i=k
      · subst i; simp [hij]
      · simp [hij,hik]
  · rw [Finset.prod_mul_distrib]
    simp

lemma occupation_sum (p : ι → ℝ) (f : ι → ℝ) :
    (∑ m : ι → Bool, occupationWeight p m * ∑ i, if m i then f i else 0) =
      ∑ i, p i*f i := by
  have he (m : ι → Bool) (i : ι) : (if m i then f i else 0) =
      (if m i then 1 else 0) * f i := by cases m i <;> simp
  simp_rw [he,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc,← Finset.sum_mul,occupation_first]

lemma occupation_pair_sum (p : ι → ℝ) (f : ι → ι → ℝ) (hf : ∀ i, f i i = 0) :
    (∑ m : ι → Bool, occupationWeight p m *
      ∑ i, ∑ j, if m i && m j then f i j else 0) =
      ∑ i, ∑ j, p i*p j*f i j := by
  have he (m : ι → Bool) (i j : ι) : (if m i && m j then f i j else 0) =
      ((if m i then 1 else 0)*(if m j then 1 else 0)) * f i j := by
    cases m i <;> cases m j <;> simp
  simp_rw [he,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i=j
  · subst j; simp [hf]
  · calc
      _ = (∑ m : ι → Bool, occupationWeight p m *
          ((if m i then 1 else 0)*(if m j then 1 else 0))) * f i j := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro m _
        ring
      _ = _ := by rw [occupation_second hij]

end CoulombAtom

end

end OAI
