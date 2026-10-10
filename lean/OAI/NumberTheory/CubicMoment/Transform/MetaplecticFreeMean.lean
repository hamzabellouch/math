import OAI.NumberTheory.CubicMoment.Estimates.PrimaryNormMultiplicity
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCubeMean

namespace OAI

/-! The free primary variable in each retained metaplectic support block
has inverse-square-root coefficients. Its actual energy and rational norm
multiplicity give the ordinary mean-value bound. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_free_dyad_energy (S : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b) (v : Eisenstein → ℂ) {L K : ℝ} (hL : 0 < L)
    (hsize : ∀ b ∈ S, L/2 ≤ norm b ∧ norm b ≤ L)
    (hv : ∀ b ∈ S, ‖v b‖^2 ≤ K^2/norm b) :
    (∑ b ∈ S, ‖v b‖^2) ≤ 36*K^2 := by
  have hsub : S ⊆ nonzeroNormBall L := by
    intro b hb
    exact mem_nonzeroNormBall.mpr ⟨(hsize b hb).2,primary_ne_zero (hS b hb)⟩
  have hcard : (S.card:ℝ) ≤ 18*L :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (nonzeroNormBall_card_le hL.le)
  have hterm (b : Eisenstein) (hb : b ∈ S) : ‖v b‖^2 ≤ 2*K^2/L := by
    apply (hv b hb).trans
    calc
      _ ≤ K^2/(L/2) := div_le_div_of_nonneg_left (sq_nonneg K) (half_pos hL) (hsize b hb).1
      _ = _ := by field_simp [hL.ne']
  calc
    _ ≤ ∑ b ∈ S, 2*K^2/L := Finset.sum_le_sum hterm
    _ = (S.card:ℝ)*(2*K^2/L) := by simp
    _ ≤ (18*L)*(2*K^2/L) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by field_simp [hL.ne']; ring

/-- The actual free-primary dyad mean; the only analytic input is MV. -/
theorem metaplectic_free_meanAbsolute_sq {ε C : ℝ} (hε : 0 < ε)
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 < D ∧ ∀ (S : Finset Eisenstein), (∀ b ∈ S, primary b) →
      ∀ (v : Eisenstein → ℂ) (L K T u : ℝ) (ℓ : ℤ),
      1 ≤ L → 0 < T → (∀ b ∈ S, L/2 ≤ norm b ∧ norm b ≤ L) →
      (∀ b ∈ S, ‖v b‖^2 ≤ K^2/norm b) →
      ((∫ t in T..2*T, ‖∑ b ∈ S, v b*theta ℓ b*mellinPhase (t+u) (norm b)‖)/T)^2 ≤
        C*D*(1+2*L/T)*L^ε*K^2 := by
  obtain ⟨D,hD,hfiber⟩ := primary_norm_fiber_length_bound hε
  refine ⟨36*D*2^ε,by positivity,?_⟩
  intro S hS v L K T u ℓ hL hT hsize hv
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hN (b : Eisenstein) (hb : b ∈ S) : normNat b ∈ Finset.Icc 1 ⌈L⌉₊ := by
    apply Finset.mem_Icc.mpr
    constructor
    · exact_mod_cast (show (1:ℝ) ≤ (normNat b:ℝ) by
        rw [normNat_cast]
        exact one_le_norm (primary_ne_zero (hS b hb)))
    · have hh : (normNat b:ℝ) ≤ (⌈L⌉₊:ℝ) := by
        rw [normNat_cast]
        exact (hsize b hb).2.trans (Nat.le_ceil L)
      exact_mod_cast hh
  have he := metaplectic_free_dyad_energy S hS v hLp hsize hv
  have hm := fixedAngular_translated_meanAbsolute_sq hMV hC S v ⌈L⌉₊
    (D*(⌈L⌉₊:ℝ)^ε) hN (fun b hb => primary_ne_zero (hS b hb))
    (hfiber S hS ⌈L⌉₊) ℓ u hT
  have hceil : (⌈L⌉₊:ℝ) ≤ 2*L := by linarith [Nat.ceil_lt_add_one hLp.le]
  have hc : (⌈L⌉₊:ℝ)^ε ≤ (2*L)^ε :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hceil hε.le
  have hf : 1+(⌈L⌉₊:ℝ)/T ≤ 1+2*L/T := by
    linarith [div_le_div_of_nonneg_right hceil hT.le]
  calc
    _ ≤ C*(1+(⌈L⌉₊:ℝ)/T)*(D*(⌈L⌉₊:ℝ)^ε)*(36*K^2) :=
      hm.trans (mul_le_mul_of_nonneg_left he (by positivity))
    _ ≤ C*(1+2*L/T)*(D*(2*L)^ε)*(36*K^2) := by gcongr
    _ = _ := by rw [Real.mul_rpow (by norm_num) hLp.le]; ring

end CubicFirstMoment

end

end OAI
