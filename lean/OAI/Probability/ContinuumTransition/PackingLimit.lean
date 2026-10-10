import OAI.Probability.ContinuumTransition.FreeUpper

namespace OAI

section
open scoped Topology BigOperators
open Filter Set
namespace ContinuumTemperature

noncomputable def packingDensity : ℝ :=
  sSup ((fun L : ℝ => (packingNumber L : ℝ)/(L+2)^3) '' Ici 0)

theorem packing_fractions_bddAbove :
    BddAbove ((fun L : ℝ => (packingNumber L : ℝ)/(L+2)^3) '' Ici 0) := by
  refine ⟨64, ?_⟩
  rintro _ ⟨L,hL,rfl⟩
  change 0 ≤ L at hL
  apply (div_le_iff₀ (pow_pos (by linarith : 0 < L+2) 3)).2
  have hh := pow_le_pow_left₀ (by linarith : 0 ≤ 4*L+2)
    (by linarith : 4*L+2 ≤ 4*(L+2)) 3
  have hp := packingNumber_bound hL
  nlinarith only [hp,hh]

theorem packing_fraction_le {L : ℝ} (hL : 0 ≤ L) :
    (packingNumber L : ℝ)/(L+2)^3 ≤ packingDensity :=
  le_csSup packing_fractions_bddAbove ⟨L,hL,rfl⟩

theorem packingDensity_pos : 0 < packingDensity := by
  have hp : IsPacking 0 1 := by
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro i j; simp
    · intro i j hij
      exact (hij (Subsingleton.elim _ _)).elim
  have hn : (1 : ℝ) ≤ packingNumber 0 := by exact_mod_cast hp.le_packingNumber
  have hh := packing_fraction_le (L := 0) (le_refl 0)
  norm_num at hh
  linarith

theorem packingNumber_tendsto :
    Tendsto (fun L : ℝ => (packingNumber L : ℝ)/L^3) atTop (𝓝 packingDensity) := by
  refine tendsto_order.2 ⟨?_,?_⟩
  · intro c hc
    obtain ⟨v,⟨ℓ,hℓ,rfl⟩,hv⟩ := exists_lt_of_lt_csSup
      (Set.Nonempty.image _ (nonempty_Ici : (Ici (0 : ℝ)).Nonempty)) hc
    have ht : Tendsto (fun L : ℝ => ((tileCount ℓ L : ℝ)/L^3)*(packingNumber ℓ : ℝ))
        atTop (𝓝 ((packingNumber ℓ : ℝ)/(ℓ+2)^3)) := by
      simpa only [div_eq_mul_inv, inv_pow, mul_comm] using
        (tileCount_asymptotic hℓ).mul_const (packingNumber ℓ : ℝ)
    filter_upwards [ht.eventually_const_lt hv, eventually_gt_atTop (0 : ℝ)] with L hc hL
    apply hc.trans_le
    have hi := packingNumber_tiling hℓ hL.le
    have hh := div_le_div_of_nonneg_right (Nat.cast_le.mpr hi :
        ((tileCount ℓ L*packingNumber ℓ : ℕ) : ℝ) ≤ packingNumber L) (pow_pos hL 3).le
    simpa only [Nat.cast_mul, div_mul_eq_mul_div] using hh
  · intro c hc
    have hi : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have ht : Tendsto (fun L : ℝ => packingDensity*(1+2/L)^3) atTop (𝓝 packingDensity) := by
      simpa only [mul_zero, add_zero, one_pow, mul_one, div_eq_mul_inv] using
        (((hi.const_mul 2).const_add 1).pow 3).const_mul packingDensity
    filter_upwards [ht.eventually_lt_const hc, eventually_gt_atTop (0 : ℝ)] with L hc hL
    apply lt_of_le_of_lt _ hc
    have hh := mul_le_mul_of_nonneg_right (packing_fraction_le hL.le)
      (show 0 ≤ ((L+2)^3/L^3) by positivity)
    have he : ((packingNumber L : ℝ)/(L+2)^3)*((L+2)^3/L^3) =
        (packingNumber L : ℝ)/L^3 := by
      have hn : L+2 ≠ 0 := by positivity
      field_simp
    rw [he] at hh
    convert hh using 1
    field_simp

end ContinuumTemperature
end

end OAI
