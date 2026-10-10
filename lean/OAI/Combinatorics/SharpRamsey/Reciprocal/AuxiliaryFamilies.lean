import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.CanonicalAuxiliaryLaw

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real SupportMixtures
open scoped Classical BigOperators
noncomputable section
variable {A B I J Ω Θ : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype J]
  [Fintype Ω] [Fintype Θ]

lemma Law.pi_coordinate_sum (p : I → Law A) (i : I) (f : A → ℝ) :
    (∑ z, (Law.pi p).mass z * f (z i)) = ∑ a, (p i).mass a * f a := by
  let ρ := Law.pi (fun j : {j : I // j ≠ i} => p j)
  have hm (z : I → A) : (Law.pi p).mass z = (p i).mass (z i) *
      ρ.mass (fun j => z j) := by
    change (∏ j, (p j).mass (z j)) = (p i).mass (z i) *
      (∏ j : {j : I // j ≠ i}, (p j).mass (z j))
    have he : (∏ j ∈ (univ : Finset I).erase i, (p j).mass (z j)) =
        ∏ j : {j : I // j ≠ i}, (p j).mass (z j) :=
      prod_subtype _ (by simp) _
    rw [← he]
    exact (mul_prod_erase univ (fun j => (p j).mass (z j)) (mem_univ i)).symm
  calc
    _ = ∑ z, (p i).mass (z i) * ρ.mass (fun j => z j) * f (z i) := by
      simp_rw [hm]
    _ = ∑ z : A × ({j : I // j ≠ i} → A), (p i).mass z.1 * ρ.mass z.2 * f z.1 :=
      Fintype.sum_equiv (Equiv.piSplitAt i (fun _ : I => A)) _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro a _
      simp only [← sum_mul, ← mul_sum, ρ.total, mul_one]

lemma Law.independent_coordinates_sum (p : I → Law A) (q : J → Law B)
    (i : I) (j : J) (f : A → B → ℝ) :
    (∑ z, ((Law.pi p).prod (Law.pi q)).mass z * f (z.1 i) (z.2 j)) =
      ∑ a, ∑ b, (p i).mass a * (q j).mass b * f a b := by
  change (∑ z : (I → A) × (J → B), (Law.pi p).mass z.1 * (Law.pi q).mass z.2 * f (z.1 i) (z.2 j)) = _
  rw [Fintype.sum_prod_type]
  simp only [mul_assoc, ← mul_sum]
  simp_rw [Law.pi_coordinate_sum q j]
  exact Law.pi_coordinate_sum p i (fun a => ∑ b, (q j).mass b * f a b)

namespace AuxiliarySupport
variable {p : I → Law A} {q : J → Law B} {goodA : I → Finset A}
  {goodB : J → Finset B} {MA κA : I → ℝ} {MB κB : J → ℝ}

def familyLaw (X : ∀ i, AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
    (Y : ∀ j, AuxiliarySupport (q j) (goodB j) (MB j) (κB j)) :
    Law ((I → Finset A) × (J → Finset B)) :=
  (Law.pi (fun i => (X i).setLaw)).prod (Law.pi (fun j => (Y j).setLaw))

lemma familyLaw_support (X : ∀ i, AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
    (Y : ∀ j, AuxiliarySupport (q j) (goodB j) (MB j) (κB j))
    (z : (I → Finset A) × (J → Finset B)) (hz : (familyLaw X Y).mass z ≠ 0) :
    (∀ i, z.1 i ⊆ goodA i ∧ MA i * exp (-κA i) / 2 ≤ ((z.1 i).card : ℝ) ∧
      ((z.1 i).card : ℝ) ≤ MA i) ∧
    (∀ j, z.2 j ⊆ goodB j ∧ MB j * exp (-κB j) / 2 ≤ ((z.2 j).card : ℝ) ∧
      ((z.2 j).card : ℝ) ≤ MB j) := by
  have hz' : (∏ i, (X i).setLaw.mass (z.1 i)) *
      (∏ j, (Y j).setLaw.mass (z.2 j)) ≠ 0 := hz
  constructor
  · intro i
    apply (X i).setLaw_support
    exact (prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hz').1) i (mem_univ _)
  · intro j
    apply (Y j).setLaw_support
    exact (prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hz').2) j (mem_univ _)

theorem familyLaw_incidence
    (X : ∀ i, AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
    (Y : ∀ j, AuxiliarySupport (q j) (goodB j) (MB j) (κB j))
    (i : I) (j : J) (R : A → B → Prop) :
    (∑ z, (familyLaw X Y).mass z * pairing (kernel (z.1 i)) (kernel (z.2 j))
      (fun a b => if R a b then 1 else 0)) ≤
      (4 * exp 1) * (4 * exp 1) * ((p i).prod (q j)).event
        (univ.filter (fun z => z.1 ∈ goodA i ∧ z.2 ∈ goodB j ∧ R z.1 z.2)) := by
  rw [familyLaw, Law.independent_coordinates_sum
    (fun i => (X i).setLaw) (fun j => (Y j).setLaw) i j
    (fun S T => pairing (kernel S) (kernel T) (fun a b => if R a b then 1 else 0))]
  have h := independent_pairing_le (X i).setLaw.mass (Y j).setLaw.mass id id
    (fun a b => if R a b then (1 : ℝ) else 0)
    (fun a => if a ∈ goodA i then (p i).mass a else 0)
    (fun b => if b ∈ goodB j then (q j).mass b else 0)
    (4 * exp 1) (4 * exp 1) (X i).setLaw.nonneg (Y j).setLaw.nonneg
    (by intros; split_ifs <;> norm_num) (X i).setLaw_density (Y j).setLaw_density
  simpa only [id_eq, good_pairing_eq_event] using h

end AuxiliarySupport

lemma Law.history_observable_sum (μ : Law Ω) (θ : Ω → Θ) (F : Ω → B)
    (f : Θ → B → ℝ) :
    (∑ ω, μ.mass ω * f (θ ω) (F ω)) =
      ∑ z, (μ.map θ).mass z * ∑ b, ((μ.cond θ z).map F).mass b * f z b := by
  simp only [mul_sum, ← mul_assoc, Law.cond_map_weight]
  have h := μ.sum_map (fun ω => (F ω, θ ω)) (fun z => f z.2 z.1)
  rw [Fintype.sum_prod_type, sum_comm] at h
  exact h.symm

lemma Law.withKernel_observable_sum (μ : Law Ω) (θ : Ω → Θ) (ρ : Θ → Law A)
    (F : Ω → B) (f : Θ → B → A → ℝ) :
    (∑ x, (μ.withKernel θ ρ).mass x * f (θ x.1) (F x.1) x.2) =
      ∑ z, (μ.map θ).mass z * ∑ a, (ρ z).mass a *
        ∑ b, ((μ.cond θ z).map F).mass b * f z b a := by
  rw [μ.withKernel_sum θ ρ (fun ω a => f (θ ω) (F ω) a)]
  rw [μ.history_observable_sum θ F (fun z b => ∑ a, (ρ z).mass a * f z b a)]
  apply sum_congr rfl
  intro z _
  congr 1
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  ring

end
end SharpLogRamsey.Selection

end

end OAI
