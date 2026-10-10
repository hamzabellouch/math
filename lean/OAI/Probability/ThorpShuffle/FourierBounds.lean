import OAI.Probability.ThorpShuffle.CosetBounds

namespace OAI

universe uG uE

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier.Family
open scoped Classical
variable {H : Type} [Group H] [Fintype H] (F : Family H)

def reciprocalSum : ℝ := ∑ b, ((F.degree b : ℝ) ^ 2)⁻¹

lemma reciprocalSum_nonneg : 0 ≤ F.reciprocalSum :=
  Finset.sum_nonneg (fun _ _ => inv_nonneg.mpr (sq_nonneg _))

lemma low_degree_sq (D : ℕ) :
    (∑ b ∈ Finset.univ.filter (fun b => F.degree b ^ 8 ≤ D), (F.degree b : ℝ)^2)^2 ≤
      (D : ℝ) * F.reciprocalSum ^ 2 := by
  let s := Finset.univ.filter (fun b => F.degree b ^ 8 ≤ D)
  have hpos (b : F.Index) : (0 : ℝ) < F.degree b := by exact_mod_cast F.positive b
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := fun b => (F.degree b : ℝ)^2) (f := fun b => ((F.degree b : ℝ)^2)⁻¹)
    (g := fun b => (F.degree b : ℝ)^6)
    (fun b _ => inv_nonneg.mpr (sq_nonneg _)) (fun b _ => pow_nonneg (hpos b).le _)
    (fun b _ => by apply le_of_eq; field_simp)
  have hsmall : ∑ b ∈ s, ((F.degree b : ℝ)^2)⁻¹ ≤ F.reciprocalSum :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun b _ _ => inv_nonneg.mpr (sq_nonneg _))
  have hlarge : ∑ b ∈ s, (F.degree b : ℝ)^6 ≤ (D : ℝ) * F.reciprocalSum := by
    calc
      _ ≤ ∑ b ∈ s, (D : ℝ) * ((F.degree b : ℝ)^2)⁻¹ := by
        apply Finset.sum_le_sum
        intro b hb
        have hh : (F.degree b : ℝ)^8 ≤ D := by exact_mod_cast (Finset.mem_filter.mp hb).2
        apply (le_mul_inv_iff₀ (pow_pos (hpos b) 2)).mpr
        calc
          _ = (F.degree b : ℝ)^8 := by ring
          _ ≤ _ := hh
      _ = (D : ℝ) * ∑ b ∈ s, ((F.degree b : ℝ)^2)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg _)
  calc
    _ ≤ _ := hcs
    _ ≤ F.reciprocalSum * ((D : ℝ) * F.reciprocalSum) :=
      mul_le_mul hsmall hlarge (Finset.sum_nonneg (fun b _ => pow_nonneg (hpos b).le _)) F.reciprocalSum_nonneg
    _ = _ := by ring

end Thorp.Fourier.Family

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} [Group G] [Fintype G]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

noncomputable def hsSq (A : Module.End ℂ E) : ℝ :=
  ∑ k, ‖A (stdOrthonormalBasis ℂ E k)‖ ^ 2

lemma hsSq_nonneg (A : Module.End ℂ E) : 0 ≤ hsSq A :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma hsSq_le (A : Module.End ℂ E) (R : ℝ) (hA : ∀ v, ‖A v‖ ^ 2 ≤ R * ‖v‖ ^ 2) :
    hsSq A ≤ (Module.finrank ℂ E : ℝ) * R := by
  calc
    _ ≤ ∑ k, R * ‖stdOrthonormalBasis ℂ E k‖ ^ 2 := Finset.sum_le_sum (fun k _ => hA _)
    _ = _ := by simp

omit [FiniteDimensional ℂ E] in
lemma norm_integrated_sq (ρ : Representation ℂ G E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) (f : G → ℂ) (v : E) :
    ((‖integrated ρ f v‖ ^ 2 : ℝ) : ℂ) =
      ∑ g, ∑ h, conj (f g) * f h * ⟪v, ρ (g⁻¹ * h) v⟫_ℂ := by
  rw [Complex.ofReal_pow, ← RCLike.ofReal_eq_complex_ofReal, ← inner_self_eq_norm_sq_to_K]
  simp only [integrated, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [sum_inner]
  simp only [inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro h _
  rw [map_mul, Module.End.mul_apply, inner_inv ρ hu]
  ring

lemma hsSq_integrated (ρ : Representation ℂ G E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) (f : G → ℂ) :
    (hsSq (integrated ρ f) : ℂ) =
      ∑ g, ∑ h, conj (f g) * f h * ρ.character (g⁻¹ * h) := by
  simp only [hsSq, Complex.ofReal_sum, norm_integrated_sq ρ hu]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [← Finset.mul_sum]
  congr 1
  exact (LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ E)).symm

namespace Family
variable {G : Type} [Group G] [Fintype G] (F : Family G)

theorem parseval (f : G → ℂ) :
    (Fintype.card G : ℝ) * ∑ g, ‖f g‖ ^ 2 =
      ∑ i, (F.degree i : ℝ) * hsSq (integrated (F.rep i) f) := by
  apply Complex.ofReal_injective
  push_cast
  symm
  simp only [hsSq_integrated _ (F.unitary _), Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.sum_comm]
  have he (h : G) : ∑ i, (F.degree i : ℂ) *
      (conj (f g) * f h * (F.rep i).character (g⁻¹ * h)) =
      conj (f g) * f h * (if g⁻¹ * h = 1 then (Fintype.card G : ℂ) else 0) := by
    rw [← F.regular, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [degree]
    ring
  simp only [he, inv_mul_eq_one, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, Complex.conj_mul']
  ring

end Family
end Thorp.Fourier

namespace Thorp.Fourier
open scoped Classical
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma power_norm_sq (A : Module.End ℂ E) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ v, ‖A v‖ ^ 2 ≤ R * ‖v‖ ^ 2) (k : ℕ) (v : E) :
    ‖(A ^ k) v‖ ^ 2 ≤ R ^ k * ‖v‖ ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ' A k, Module.End.mul_apply, pow_succ' R k]
      exact (hA _).trans (by nlinarith [mul_le_mul_of_nonneg_left ih hR])

lemma eight_degree_bound (D : ℝ) (hD : 0 < D) (B S C : ℝ)
    (hs : S ^ 2 ≤ D * C ^ 2) :
    D ^ 2 * (8 * B * S / D) ^ 8 ≤ (8 * B * C) ^ 8 * (D ^ 2)⁻¹ := by
  have hh := pow_le_pow_left₀ (sq_nonneg S) hs 4
  have hscalar : 0 ≤ (8 * B)^8 := by positivity
  have ht := mul_le_mul_of_nonneg_left hh hscalar
  apply (le_mul_inv_iff₀ (pow_pos hD 2)).mpr
  field_simp
  field_simp at ht
  nlinarith

namespace Family
variable {G : Type} [Group G] [Fintype G] (F : Family G)

lemma l1_sq_le_parseval (f : G → ℝ) :
    (∑ g, |f g|)^2 ≤ ∑ i, (F.degree i : ℝ) * hsSq (integrated (F.rep i) (fun g => (f g : ℂ))) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : G => (1 : ℝ)) (fun g => |f g|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    sq_abs] at hc
  have hp := F.parseval (fun g => (f g : ℂ))
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hp
  exact hc.trans_eq hp

end Family
end Thorp.Fourier

end

end OAI
