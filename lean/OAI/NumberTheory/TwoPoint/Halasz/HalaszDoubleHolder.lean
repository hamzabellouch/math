import OAI.NumberTheory.TwoPoint.Halasz.HalaszFiberHolder
import OAI.NumberTheory.TwoPoint.Halasz.HalaszCollisionPartition

namespace OAI

/-! The two Hölder steps in Ford's double mean-value argument (Lemma 5.1),
with the full complete-system frequency on both sides. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem halasz_double_holder {ι : Type*} (B : Finset ι) (k M r s : ℕ)
    (hr : 1≤r) (hs : 1≤s) (α : ι → Fin k → AddCircle (1:ℝ)) :
    ∃ ε : ι → ℂ, (∀ b, ‖ε b‖=1) ∧
    ‖∑ b∈B,halaszVinogradovPolynomial k M (α b)‖^(2*r*s) ≤
      (B.card:ℝ)^((r-1)*(2*s))*(M:ℝ)^(r*(2*s-2))*
        (halaszVinogradovCount r k M:ℝ)*
          ∑ c∈(univ : Finset (Fin r → Fin M)).image (halaszVinogradovFrequency k),
            ‖∑ b∈B,ε b*halaszVinogradovCharacter c (α b)‖^(2*s) := by
  let P := fun b => halaszVinogradovPolynomial k M (α b)
  choose ε hεnorm hεeq using (fun b : ι => Complex.exists_norm_eq_mul_self ((P b)^r))
  refine ⟨ε,hεnorm,?_⟩
  let V := fun c : Fin k → ℤ => ∑ b∈B,ε b*halaszVinogradovCharacter c (α b)
  have hnonneg : 0≤∑ b∈B,‖P b‖^r := sum_nonneg (fun _ _ => by positivity)
  have hexpand : ((∑ b∈B,‖P b‖^r:ℝ):ℂ)=∑ x : Fin r → Fin M,
      V (halaszVinogradovFrequency k x) := by
    push_cast
    simp_rw [show ∀ b, ((‖P b‖:ℝ):ℂ)^r=ε b*(P b)^r from fun b => by
      simpa only [norm_pow,Complex.ofReal_pow] using hεeq b]
    dsimp only [P]
    simp_rw [halasz_vinogradov_power_expand,mul_sum]
    exact sum_comm
  have hnorm : (∑ b∈B,‖P b‖^r:ℝ)=
      ‖∑ x : Fin r → Fin M,V (halaszVinogradovFrequency k x)‖ := by
    have hh := congrArg norm hexpand
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnonneg] using hh
  have h1 := halasz_complex_sum_power B P hr
  have hp := pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) r) h1 (2*s)
  rw [mul_pow,← pow_mul,← pow_mul,hnorm] at hp
  have h2 := halasz_fiber_holder (univ : Finset (Fin r → Fin M))
    (halaszVinogradovFrequency k) V hs
  rw [halasz_frequency_energy] at h2
  simp only [card_univ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,← pow_mul] at h2
  have hh := mul_le_mul_of_nonneg_left h2
    (pow_nonneg (Nat.cast_nonneg B.card) ((r-1)*(2*s)))
  have he : r*(2*s)=2*r*s := by ring
  rw [he] at hp
  have himage (d : DecidableEq (Fin k → ℤ)) :
      @Finset.image (Fin r → Fin M) (Fin k → ℤ) d (halaszVinogradovFrequency k) univ =
      @Finset.image (Fin r → Fin M) (Fin k → ℤ)
        (fun a b => Fintype.decidablePiFintype a b) (halaszVinogradovFrequency k) univ := by
    ext c
    simp only [mem_image]
  rw [himage] at hh
  exact hp.trans (by simpa only [V,mul_assoc] using hh)

end TwoPointCorrelations

end OAI
