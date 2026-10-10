import OAI.NumberTheory.Ostmann.Characters.RichShellSelectionFinite

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters
open Construction Filter

theorem three_rich_harmonic_intervals (α β c : ℝ) (hα : 0 < α) (hαβ : α < β) (hc : 0 < c) :
    ∃ ρ γ : ℝ, 0 < ρ ∧ 0 < γ ∧ ∀ᶠ L : ℝ in atTop,
      ∀ E : Finset ℕ,
        (∀ p ∈ E, p.Prime ∧ α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
        c*L ≤ harmonicPrimeMass E →
        ∃ w A B D : ℝ, γ*L ≤ w ∧ w ≤ (β-α+1)*L ∧ 0 ≤ A ∧
          A+2*w ≤ B ∧ B+2*w ≤ D ∧ D+w ≤ β*L ∧
          ρ*L ≤ harmonicIntervalMass E A (A+w) ∧
          ρ*L ≤ harmonicIntervalMass E B (B+w) ∧
          ρ*L ≤ harmonicIntervalMass E D (D+w) := by
  obtain ⟨C,hC,hcap⟩ := harmonicIntervalMass_mertens
  let b := β-α+1
  have hb : 0 < b := by dsimp [b]; linarith
  obtain ⟨q,hq⟩ := exists_nat_gt (max 1 (16*b/c))
  have hq1 : 1 ≤ q := by have := (le_max_left _ _).trans_lt hq; exact_mod_cast this.le
  have hqr : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
  have hqbig : 16*b < c*(q:ℝ) := by
    have := (div_lt_iff₀ hc).mp ((le_max_right _ _).trans_lt hq)
    nlinarith
  refine ⟨c/(2*(q:ℝ)),(β-α)/(q:ℝ),by positivity,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop (2/α),
    eventually_ge_atTop (C*(q:ℝ)/b)] with L hL hLa hLC
  have hLpos : 0 < L := by linarith
  have haL : 2 ≤ α*L := by have := (div_le_iff₀ hα).mp hLa; nlinarith
  have hCL : C*(q:ℝ) ≤ b*L := by have := (div_le_iff₀ hb).mp hLC; nlinarith
  intro E hE hm
  let a := α*L-1
  let w := ((β-α)*L+1)/(q:ℝ)
  let t := c*L/(2*(q:ℝ))
  let F : ℕ → ℝ := fun i => harmonicIntervalMass E (a+(i:ℝ)*w) (a+((i:ℝ)+1)*w)
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hw : 0 < w := by dsimp [w]; positivity
  have hqw : (q:ℝ)*w = (β-α)*L+1 := by dsimp [w]; field_simp
  have hwB : w ≤ b*L/(q:ℝ) := by
    apply (le_div_iff₀ hqr).mpr
    dsimp [b] at ⊢
    nlinarith
  have hCB : C ≤ b*L/(q:ℝ) := (le_div_iff₀ hqr).mpr hCL
  have hF (i : ℕ) (_ : i < q) : F i ≤ 2*(b*L/(q:ℝ)) := by
    have hlow : 0 ≤ a+(i:ℝ)*w := add_nonneg ha (mul_nonneg (Nat.cast_nonneg _) hw.le)
    have hh := hcap E (fun p hp => (hE p hp).1) (a+(i:ℝ)*w) (a+((i:ℝ)+1)*w)
      hlow (by nlinarith)
    dsimp [F]
    linarith
  have hsum : (∑ i ∈ Finset.range q, F i) = harmonicPrimeMass E := by
    rw [harmonicIntervalMass_grid E a w hw.le q]
    apply harmonicIntervalMass_eq_of_support
    intro p hp
    have hs := (hE p hp).2
    dsimp [a]
    constructor <;> nlinarith
  have hnum : (q:ℝ)*t+4*(2*(b*L/(q:ℝ))) < c*L := by
    have hmul := mul_lt_mul_of_pos_right hqbig hLpos
    dsimp [t]
    apply (mul_lt_mul_iff_left₀ hqr).mp
    field_simp
    nlinarith
  have hcard := five_large_weights q F t (2*(b*L/(q:ℝ))) (by dsimp [t]; positivity)
    (by positivity) hF (by rw [hsum]; exact hnum.trans_le hm)
  obtain ⟨i,hi,j,hj,k,hk,hij,hjk⟩ := three_separated_indices _ hcard
  obtain ⟨hi,him⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj,hjm⟩ := Finset.mem_filter.mp hj
  obtain ⟨hk,hkm⟩ := Finset.mem_filter.mp hk
  have hkq : (k:ℝ)+1 ≤ q := by exact_mod_cast Finset.mem_range.mp hk
  have hijr : (i:ℝ)+2 ≤ j := by exact_mod_cast hij
  have hjkr : (j:ℝ)+2 ≤ k := by exact_mod_cast hjk
  refine ⟨w,a+(i:ℝ)*w,a+(j:ℝ)*w,a+(k:ℝ)*w,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp [w]
    apply (le_div_iff₀ hqr).mpr
    have he : ((β-α)/(q:ℝ)*L)*(q:ℝ) = (β-α)*L := by field_simp
    rw [he]
    linarith
  · exact hwB.trans (div_le_self (by positivity) (by exact_mod_cast hq1))
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_right hijr hw.le]
  · nlinarith [mul_le_mul_of_nonneg_right hjkr hw.le]
  · dsimp [a]
    nlinarith [mul_le_mul_of_nonneg_right hkq hw.le]
  · simpa only [F,t,add_mul,one_mul,div_mul_eq_mul_div,add_assoc] using him
  · simpa only [F,t,add_mul,one_mul,div_mul_eq_mul_div,add_assoc] using hjm
  · simpa only [F,t,add_mul,one_mul,div_mul_eq_mul_div,add_assoc] using hkm

end Ostmann.Characters

end

end OAI
