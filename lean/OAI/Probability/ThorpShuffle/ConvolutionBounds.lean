import OAI.Probability.ThorpShuffle.PermutationCharacters

namespace OAI

universe uE

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier
open scoped Classical
variable {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

lemma hsSq_power_le (A : Module.End ℂ E) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ v, ‖A v‖ ^ 2 ≤ R * ‖v‖ ^ 2) (k : ℕ) :
    hsSq (A ^ k) ≤ (Module.finrank ℂ E : ℝ) * R ^ k := by
  unfold hsSq
  calc
    _ ≤ ∑ i, R ^ k * ‖stdOrthonormalBasis ℂ E i‖ ^ 2 :=
      Finset.sum_le_sum (fun i _ => power_norm_sq A R hR hA k _)
    _ = _ := by simp [(stdOrthonormalBasis ℂ E).norm_eq_one, mul_comm]

lemma Family.eight_transform_bound (F : Family H) (ρ : Representation ℂ G E)
    [Representation.IsIrreducible ρ]
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hd : 0 < Module.finrank ℂ E) (ψ : (Fin 8 → H) →* G) (ν : G → ℝ) (B : ℝ)
    (hν : ∀ g, 0 ≤ ν g) (h1 : ∑ g, ν g = 1) (hB : 0 ≤ B)
    (hcoset : ∀ i g, ∑ h, ν (g * ψ (Pi.mulSingle i h)) ≤
      B * (Fintype.card H : ℝ) / Fintype.card G) :
    (Module.finrank ℂ E : ℝ) * hsSq (integrated ρ (fun g => (realPower ν 8 g : ℂ))) ≤
      (8 * B * F.reciprocalSum)^8 * ((Module.finrank ℂ E : ℝ)^2)⁻¹ := by
  let S : ℝ := ∑ b ∈ Finset.univ.filter (fun b => F.degree b ^ 8 ≤ Module.finrank ℂ E), (F.degree b : ℝ)^2
  let R : ℝ := 8 * B * S / Module.finrank ℂ E
  have hD : (0 : ℝ) < Module.finrank ℂ E := by exact_mod_cast hd
  have hR : 0 ≤ R := by dsimp [R, S]; positivity
  have hA (v : E) : ‖integrated ρ (fun g => (ν g : ℂ)) v‖ ^ 2 ≤ R * ‖v‖ ^ 2 := by
    simpa only [R, S, Fintype.card_fin, Nat.cast_ofNat] using F.integrated_norm_sq ρ hu (Nat.ne_of_gt hd) ψ ν B hν h1 hB (by
      intro i g
      convert hcoset i g using 1
      apply Finset.sum_congr rfl
      intro h _
      congr 4
      exact Subsingleton.elim _ _) v
  rw [integrated_realPower]
  calc
    _ ≤ (Module.finrank ℂ E : ℝ) * ((Module.finrank ℂ E : ℝ) * R^8) :=
      mul_le_mul_of_nonneg_left (hsSq_power_le _ R hR hA 8) hD.le
    _ = (Module.finrank ℂ E : ℝ)^2 * R^8 := by ring
    _ ≤ _ := eight_degree_bound _ hD B S F.reciprocalSum (F.low_degree_sq _)

omit [FiniteDimensional ℂ E] in
lemma integrated_uniform_real (ρ : Representation ℂ G E) [Representation.IsIrreducible ρ]
    (hd : 1 < Module.finrank ℂ E) :
    integrated ρ (fun _ => (((Fintype.card G : ℝ)⁻¹ : ℝ) : ℂ)) = 0 := by
  simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using integrated_uniform_zero ρ hd

omit [FiniteDimensional ℂ E] in
lemma centered_trivial (ρ : Representation ℂ G E) (hρ : ∀ g v, ρ g v = v)
    (ν : G → ℝ) (h1 : ∑ g, ν g = 1) :
    integrated ρ (fun g => ((realPower ν 8 g - (Fintype.card G : ℝ)⁻¹ : ℝ) : ℂ)) = 0 := by
  rw [integrated_real_sub]
  have htr (g : G) (v : E) : ρ g v = (1 : ℂ) • v := by simpa using hρ g v
  rw [integrated_scalar ρ (fun _ => 1) htr, integrated_scalar ρ (fun _ => 1) htr]
  simp only [mul_one, ← Complex.ofReal_sum, realPower_sum ν h1, Complex.ofReal_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [Complex.ofReal_inv, Complex.ofReal_natCast, Fintype.card_ne_zero]

omit [FiniteDimensional ℂ E] in
lemma centered_character (ρ : Representation ℂ G E) (χ : G → ℂ)
    (hρ : ∀ g v, ρ g v = χ g • v) (hχ : ∑ g, χ g = 0)
    (ν : G → ℝ) :
    integrated ρ (fun g => ((realPower ν 8 g - (Fintype.card G : ℝ)⁻¹ : ℝ) : ℂ)) =
      (∑ g, (ν g : ℂ) * χ g)^8 • LinearMap.id := by
  rw [integrated_real_sub, integrated_realPower, integrated_scalar ρ χ hρ,
    integrated_scalar ρ χ hρ]
  simp only [← Finset.mul_sum, hχ, mul_zero, zero_smul, sub_zero]
  simp only [smul_pow, show (LinearMap.id : Module.End ℂ E) = 1 from rfl, one_pow]

end Thorp.Fourier

namespace Thorp.Specht
open scoped Classical
open Thorp.Fourier
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Nontrivial α]

theorem permutation_eight_bound (hn : 16 ≤ Fintype.card α)
    (ψ : (Fin 8 → Equiv.Perm β) →* Equiv.Perm α) (ν : Equiv.Perm α → ℝ) (B : ℝ)
    (hν : ∀ g, 0 ≤ ν g) (h1 : ∑ g, ν g = 1) (hB : 0 ≤ B)
    (hcoset : ∀ i g, ∑ h, ν (g * ψ (Pi.mulSingle i h)) ≤
      B * (Fintype.card (Equiv.Perm β) : ℝ) / Fintype.card (Equiv.Perm α)) :
    (∑ g, |realPower ν 8 g - (Fintype.card (Equiv.Perm α) : ℝ)⁻¹|)^2 ≤
      2 * ‖∑ g, (ν g : ℂ) * complexSign g‖^16 +
        (8 * B * (permutationFamily β).reciprocalSum)^8 * exceptionalReciprocalSum (Fintype.card α) := by
  let F := permutationFamily α
  let H := permutationFamily β
  let bias : ℝ := ‖∑ g, (ν g : ℂ) * complexSign g‖^16
  let K : ℝ := (8 * B * H.reciprocalSum)^8
  let f : Equiv.Perm α → ℝ := fun g => realPower ν 8 g - (Fintype.card (Equiv.Perm α) : ℝ)⁻¹
  have hp (p : F.Index) :
      (F.degree p : ℝ) * hsSq (integrated (F.rep p) (fun g => (f g : ℂ))) ≤
        if defect p = 0 then bias else K * inverseDegree p := by
    by_cases hz : defect p = 0
    · rw [ite_eq_left hz]
      obtain ⟨hd, htr | hsign⟩ := permutation_exceptional_action (α:=α) p hz
      · have hh := centered_trivial (F.rep p) htr ν h1
        change integrated (F.rep p) (fun g => (f g : ℂ)) = 0 at hh
        rw [hh]
        simp only [hsSq, LinearMap.zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0),
          Finset.sum_const_zero, mul_zero]
        exact pow_nonneg (norm_nonneg _) _
      · have hh := centered_character (F.rep p) complexSign hsign (complexSign_sum (α:=α)) ν
        change integrated (F.rep p) (fun g => (f g : ℂ)) = _ at hh
        rw [hh, hsSq_scalar]
        change (F.degree p : ℝ) * ((F.degree p : ℝ) * ‖(∑ g, (ν g : ℂ) * complexSign g)^8‖^2) ≤ bias
        rw [show F.degree p = 1 from hd]
        simp only [Nat.cast_one, one_mul, norm_pow, ← pow_mul]
        exact le_rfl
    · rw [ite_eq_right hz]
      have hgt : 1 < Module.finrank ℂ (F.Space p) := degree_gt_one p hn (Nat.pos_of_ne_zero hz)
      have hu := integrated_uniform_real (F.rep p) hgt
      have he : integrated (F.rep p) (fun g => (f g : ℂ)) =
          integrated (F.rep p) (fun g => (realPower ν 8 g : ℂ)) := by
        rw [show (fun g => (f g : ℂ)) = (fun g => ((realPower ν 8 g - (Fintype.card (Equiv.Perm α) : ℝ)⁻¹ : ℝ) : ℂ)) from rfl,
          integrated_real_sub, hu, sub_zero]
      rw [he]
      exact H.eight_transform_bound (F.rep p) (F.unitary p) (by omega) ψ ν B hν h1 hB hcoset
  have hs : (∑ p : NShape (Fintype.card α), if defect p = 0 then bias else K * inverseDegree p) =
      (Fintype.card {p : NShape (Fintype.card α) // defect p = 0} : ℝ) * bias +
        K * exceptionalReciprocalSum (Fintype.card α) := by
    rw [show (Fintype.card {p : NShape (Fintype.card α) // defect p = 0} : ℝ) * bias =
      ∑ p : NShape (Fintype.card α), if defect p = 0 then bias else 0 by rw [← Finset.sum_filter]; simp [Fintype.card_subtype],
      exceptionalReciprocalSum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hz : defect p = 0
    · simp only [hz, lt_self_iff_false, ↓reduceIte, mul_zero, add_zero]
    · simp only [hz, Nat.pos_of_ne_zero hz, ↓reduceIte, zero_add]
  have hc : (Fintype.card {p : NShape (Fintype.card α) // defect p = 0} : ℝ) ≤ 2 := by
    exact_mod_cast exceptional_count (Fintype.card α)
  calc
    _ ≤ ∑ p, (F.degree p : ℝ) * hsSq (integrated (F.rep p) (fun g => (f g : ℂ))) := F.l1_sq_le_parseval f
    _ ≤ ∑ p : NShape (Fintype.card α), if defect p = 0 then bias else K * inverseDegree p :=
      Finset.sum_le_sum (fun p _ => hp p)
    _ = _ := hs
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hc (pow_nonneg (norm_nonneg _) _)) le_rfl

end Thorp.Specht

end

end OAI
