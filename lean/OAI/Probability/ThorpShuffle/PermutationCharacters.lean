import OAI.Probability.ThorpShuffle.VectorOrbits

namespace OAI

universe uE

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Specht
open scoped Classical
open Thorp.Young

lemma degree_gt_one {n : ℕ} (p : NShape n) (hn : 16 ≤ n) (hp : 0 < defect p) :
    1 < degree p := by
  by_cases hs : 4 * defect p ≤ n
  · have hh := small_defect_degree p hs
    have h3 : 3 ≤ 3 ^ defect p := by simpa using Nat.pow_le_pow_right (by omega : 0 < 3) (show 1 ≤ defect p by omega)
    omega
  · have hb := bulk_degree p (by omega) (by omega)
    have h2 : (2 : ℝ) ≤ (2 : ℝ)^(n/16) := by
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show 1 ≤ n/16 by omega)
    have : (1 : ℝ) < degree p := lt_of_lt_of_le (by norm_num) (h2.trans hb)
    exact_mod_cast this

lemma full_reciprocal_bound (n : ℕ) :
    (symmetricFamily n).reciprocalSum ≤ 2 + exceptionalReciprocalSum n := by
  have hzero : slice n 0 ≤ 2 := by
    have h := slice_bound n 0 1 (by norm_num) (fun p _ => by exact_mod_cast degree_pos p)
    norm_num at h
    exact h
  have he : (symmetricFamily n).reciprocalSum = slice n 0 + exceptionalReciprocalSum n := by
    unfold slice
    rw [← Finset.sum_subtype (Finset.univ.filter (fun p : NShape n => defect p = 0)) (by simp), Finset.sum_filter]
    unfold exceptionalReciprocalSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    change inverseDegree p = _
    by_cases hp : defect p = 0
    · simp only [hp, lt_self_iff_false, ↓reduceIte, add_zero]
    · simp only [hp, Nat.pos_of_ne_zero hp, ↓reduceIte, zero_add]
  rw [he]
  linarith

lemma exceptional_count (n : ℕ) : Fintype.card {p : NShape n // defect p = 0} ≤ 2 := by
  simpa using defect_card_bound n 0

end Thorp.Specht

namespace Thorp.Specht
open scoped Classical

variable {α : Type} [Fintype α]

def permutationFamily (α : Type) [Fintype α] [DecidableEq α] : Thorp.Fourier.Family (Equiv.Perm α) :=
  (symmetricFamily (Fintype.card α)).pull (Equiv.permCongrHom (Fintype.equivFin α))

lemma complexSign_permCongr {β : Type} [Fintype β] (e : α ≃ β) (g : Equiv.Perm α) :
    complexSign (e.permCongr g) = complexSign g := by
  simp only [complexSign, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.Perm.sign_permCongr]

lemma complexSign_norm (g : Equiv.Perm α) : ‖complexSign g‖ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h <;> simp [complexSign, h]

lemma complexSign_eq [DecidableEq α] (g : Equiv.Perm α) :
    complexSign g = (((Equiv.Perm.sign g : ℤˣ) : ℤ) : ℂ) := by
  change (((@Equiv.Perm.sign α (Classical.typeDecidableEq α) _ g : ℤˣ) : ℤ) : ℂ) = _
  rw [Subsingleton.elim (Classical.typeDecidableEq α) (inferInstance : DecidableEq α)]

lemma complexSign_sum [DecidableEq α] [Nontrivial α] : (∑ g : Equiv.Perm α, complexSign g) = 0 := by
  obtain ⟨a, ha⟩ := Equiv.Perm.sign_surjective α (-1)
  have he : complexSign a = -1 := by rw [complexSign_eq, ha]; simp
  have hh := Equiv.sum_comp (Equiv.mulLeft a) (fun g : Equiv.Perm α => complexSign g)
  simp only [Equiv.coe_mulLeft, map_mul, he, neg_one_mul, Finset.sum_neg_distrib] at hh
  linear_combination - (1/2 : ℂ) * hh

lemma permutation_exceptional_action [DecidableEq α] (p : NShape (Fintype.card α)) (hp : defect p = 0) :
    (permutationFamily α).degree p = 1 ∧
      ((∀ (g : Equiv.Perm α) (v : Space (α:=Fin (Fintype.card α)) p), (permutationFamily α).rep p g v = v) ∨
       (∀ (g : Equiv.Perm α) (v : Space (α:=Fin (Fintype.card α)) p), (permutationFamily α).rep p g v = complexSign g • v)) := by
  obtain ⟨hd, htr | hsign⟩ := exceptional_action p hp
  · exact ⟨hd, Or.inl fun g v => htr _ v⟩
  · refine ⟨hd, Or.inr ?_⟩
    intro g v
    change family p ((Fintype.equivFin α).permCongr g) v = _
    rw [hsign, complexSign_permCongr]

end Thorp.Specht

namespace Thorp.Fourier
open scoped Classical
variable {G : Type} [Group G] [Fintype G]

def realConv (μ ν : G → ℝ) (g : G) : ℝ := ∑ h, μ h * ν (h⁻¹ * g)

def realPower (ν : G → ℝ) : ℕ → G → ℝ
  | 0 => fun g => if g = 1 then 1 else 0
  | k+1 => realConv ν (realPower ν k)

lemma realConv_nonneg (μ ν : G → ℝ) (hμ : ∀ g, 0 ≤ μ g) (hν : ∀ g, 0 ≤ ν g) :
    ∀ g, 0 ≤ realConv μ ν g := fun _ => Finset.sum_nonneg (fun h _ => mul_nonneg (hμ h) (hν _))

lemma realConv_sum (μ ν : G → ℝ) : ∑ g, realConv μ ν g = (∑ g, μ g) * (∑ g, ν g) := by
  unfold realConv
  rw [Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro g _
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft g⁻¹) ν

lemma realPower_nonneg (ν : G → ℝ) (hν : ∀ g, 0 ≤ ν g) (k : ℕ) : ∀ g, 0 ≤ realPower ν k g := by
  induction k with
  | zero => intro g; simp only [realPower]; split_ifs <;> norm_num
  | succ k ih => exact realConv_nonneg ν (realPower ν k) hν ih

lemma realPower_sum (ν : G → ℝ) (hν : ∑ g, ν g = 1) (k : ℕ) : ∑ g, realPower ν k g = 1 := by
  induction k with
  | zero => simp [realPower]
  | succ k ih => rw [realPower, realConv_sum, hν, ih, mul_one]

variable {E : Type uE} [AddCommGroup E] [Module ℂ E]

lemma integrated_realConv (ρ : Representation ℂ G E) (μ ν : G → ℝ) :
    integrated ρ (fun g => (realConv μ ν g : ℂ)) = integrated ρ (fun g => (μ g : ℂ)) *
      integrated ρ (fun g => (ν g : ℂ)) := by
  rw [← integrated_convolution]
  congr 1
  funext g
  simp only [realConv, convolution, Complex.ofReal_sum, Complex.ofReal_mul]

lemma integrated_realPower (ρ : Representation ℂ G E) (ν : G → ℝ) (k : ℕ) :
    integrated ρ (fun g => (realPower ν k g : ℂ)) = (integrated ρ (fun g => (ν g : ℂ)))^k := by
  induction k with
  | zero =>
    rw [pow_zero]
    have he : (fun g => (realPower ν 0 g : ℂ)) = delta := by funext g; simp only [realPower, delta]; split_ifs <;> norm_num
    rw [he, integrated_delta]
  | succ k ih => rw [realPower, integrated_realConv, ih, pow_succ']

lemma integrated_real_sub (ρ : Representation ℂ G E) (μ ν : G → ℝ) :
    integrated ρ (fun g => ((μ g - ν g : ℝ) : ℂ)) =
      integrated ρ (fun g => (μ g : ℂ)) - integrated ρ (fun g => (ν g : ℂ)) := by
  simp only [integrated, Complex.ofReal_sub, sub_smul, Finset.sum_sub_distrib]

end Thorp.Fourier

end

end OAI
