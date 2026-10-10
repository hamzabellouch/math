import Mathlib
import OAI.Probability.ThorpCompatibility.FiniteLaw

namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

@[ext] lemma ext (P Q : Law α) (h : ∀ a, P.mass a = Q.mass a) : P = Q := by
  cases P
  cases Q
  congr
  exact funext h

lemma mean_const (P : Law α) (c : ℝ) : P.mean (fun _ => c) = c := by
  simp [mean, ← Finset.sum_mul, P.total]

lemma mean_add (P : Law α) (f g : α → ℝ) :
    P.mean (fun a => f a + g a) = P.mean f + P.mean g := by
  simp [mean, mul_add, Finset.sum_add_distrib]

lemma mean_sub (P : Law α) (f g : α → ℝ) :
    P.mean (fun a => f a - g a) = P.mean f - P.mean g := by
  simp [mean, mul_sub, Finset.sum_sub_distrib]

lemma mean_mul_const (P : Law α) (f : α → ℝ) (c : ℝ) :
    P.mean (fun a => f a * c) = P.mean f * c := by
  simp [mean, ← mul_assoc, Finset.sum_mul]

lemma mean_const_mul (P : Law α) (c : ℝ) (f : α → ℝ) :
    P.mean (fun a => c * f a) = c * P.mean f := by
  simpa [mul_comm] using P.mean_mul_const f c

lemma mean_mono (P : Law α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    P.mean f ≤ P.mean g := by
  exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (P.nonneg a)

lemma mean_congr_support (P : Law α) {f g : α → ℝ}
    (h : ∀ a, 0 < P.mass a → f a = g a) : P.mean f = P.mean g := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : P.mass a = 0
  · simp [ha]
  · rw [h a (lt_of_le_of_ne (P.nonneg a) (Ne.symm ha))]

lemma map_mass_mean (P : Law α) (f : α → β) (b : β) :
    (P.map f).mass b = P.mean (fun a => if f a = b then 1 else 0) := by
  classical
  simp [map, mean, mul_ite]

lemma map_map (P : Law α) (f : α → β) (g : β → γ) :
    (P.map f).map g = P.map (g ∘ f) := by
  classical
  ext c
  rw [map_mass_mean, P.mean_map, map_mass_mean]
  rfl

lemma map_id (P : Law α) : P.map id = P := by
  classical
  ext a
  simp [map]

lemma mass_le_one (P : Law α) (a : α) : P.mass a ≤ 1 := by
  rw [← P.total]
  exact Finset.single_le_sum (fun b _ => P.nonneg b) (Finset.mem_univ a)

lemma mass_le_map (P : Law α) (f : α → β) (a : α) :
    P.mass a ≤ (P.map f).mass (f a) := by
  classical
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun b => if f b = f a then P.mass b else 0)
    (fun b _ => by split_ifs <;> simp_all [P.nonneg]) (Finset.mem_univ a)
  simpa [map] using h

lemma map_mass_pos (P : Law α) (f : α → β) {a : α} (ha : 0 < P.mass a) :
    0 < (P.map f).mass (f a) := lt_of_lt_of_le ha (P.mass_le_map f a)

noncomputable def entropy (P : Law α) : ℝ := -P.mean (fun a => Real.log (P.mass a))

lemma uniformDeficit_eq (P : Law α) :
    P.uniformDeficit = Real.log (Fintype.card α) - P.entropy := by
  simp [uniformDeficit, entropy, mean]

lemma entropy_nonneg (P : Law α) : 0 ≤ P.entropy := by
  unfold entropy
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro a _
  apply mul_nonpos_of_nonneg_of_nonpos (P.nonneg a)
  exact Real.log_nonpos (P.nonneg a) (P.mass_le_one a)

lemma entropy_map_injective (P : Law α) (f : α → β) (hf : Function.Injective f) :
    (P.map f).entropy = P.entropy := by
  classical
  have hm (a : α) : (P.map f).mass (f a) = P.mass a := by
    simp [map, hf.eq_iff]
  unfold entropy
  rw [P.mean_map]
  simp only [Function.comp_def, hm]

noncomputable def condMass (P : Law α) (X : α → β) (Y : α → γ) : α → ℝ :=
  fun a => (P.map (fun b => (X b, Y b))).mass (X a, Y a) /
    (P.map Y).mass (Y a)

noncomputable def condEntropy (P : Law α) (X : α → β) (Y : α → γ) : ℝ :=
  (P.map (fun a => (X a, Y a))).entropy - (P.map Y).entropy

lemma condMass_pos (P : Law α) (X : α → β) (Y : α → γ)
    {a : α} (ha : 0 < P.mass a) : 0 < P.condMass X Y a :=
  div_pos (P.map_mass_pos _ ha) (P.map_mass_pos _ ha)

lemma condEntropy_eq_mean (P : Law α) (X : α → β) (Y : α → γ) :
    P.condEntropy X Y = -P.mean (fun a => Real.log (P.condMass X Y a)) := by
  have hm : P.mean (fun a => Real.log (P.condMass X Y a)) =
      P.mean (fun a => Real.log ((P.map (fun b => (X b, Y b))).mass (X a, Y a)) -
        Real.log ((P.map Y).mass (Y a))) := by
    apply P.mean_congr_support
    intro a ha
    exact Real.log_div (P.map_mass_pos _ ha).ne' (P.map_mass_pos _ ha).ne'
  rw [hm, P.mean_sub]
  unfold condEntropy entropy
  rw [P.mean_map, P.mean_map]
  simp only [Function.comp_def]
  ring

lemma entropy_pair_comm (P : Law α) (X : α → β) (Y : α → γ) :
    (P.map (fun a => (X a, Y a))).entropy =
      (P.map (fun a => (Y a, X a))).entropy := by
  have h := (P.map (fun a => (X a, Y a))).entropy_map_injective Prod.swap
    Prod.swap_injective
  simpa [map_map, Function.comp_def] using h.symm

lemma entropy_func_pair (P : Law α) (X : α → β) (f : β → γ) :
    (P.map (fun a => (X a, f (X a)))).entropy = (P.map X).entropy := by
  have hi : Function.Injective (fun b => (b, f b)) := fun _ _ h => congrArg Prod.fst h
  simpa [map_map, Function.comp_def] using (P.map X).entropy_map_injective _ hi

lemma condEntropy_const (P : Law α) (X : α → β) (c : γ) :
    P.condEntropy X (fun _ => c) = (P.map X).entropy := by
  have hz : (P.map (fun _ => c)).entropy = 0 := by
    classical
    unfold entropy
    rw [P.mean_map]
    have hc : (P.map (fun _ => c)).mass c = 1 := by simp [map, P.total]
    simp [hc, mean]
  rw [condEntropy, hz, sub_zero]
  exact P.entropy_func_pair X (fun _ => c)

end Law
end ThorpCompatibility

end OAI
