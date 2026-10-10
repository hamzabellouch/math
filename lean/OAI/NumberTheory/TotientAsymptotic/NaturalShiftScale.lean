import OAI.NumberTheory.TotientAsymptotic.OrderedPrefixCoordinates
import OAI.NumberTheory.TotientAsymptotic.UniformPrefactor

namespace OAI

/-! The shift at a fixed distance below m(x) has the correct geometric scale. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem natural_shift_scale_lower : ∃ d : ℝ,0 < d ∧
    ∀ᶠ x : ℝ in atTop, ∀ n H : ℕ,0 < n → 1 ≤ H → n+H=m x →
      d*(rho^H)⁻¹ ≤ B x/((n:ℝ)*g (n+1)) := by
  obtain ⟨C,hC,hstep⟩ := uniform_step_bound fordRenewalInput
  refine ⟨rho/C,div_pos rho_pos hC,?_⟩
  filter_upwards [hstep,B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x hx hB
  intro n H hn hH hNm
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hidx : H-1 ≤ m x := by omega
  have he : m x-(H-1)=n+1 := by omega
  have hh := hx (H-1) hidx
  rw [he] at hh
  have hsmall : (n:ℝ)*g (n+1)/B x ≤ C*rho^(H-1) := by
    apply le_trans _ hh
    apply div_le_div_of_nonneg_right _ hB.le
    apply mul_le_mul_of_nonneg_right _ (g_pos _).le
    exact_mod_cast Nat.le_succ n
  have hprod := (div_le_iff₀ hB).mp hsmall
  apply (le_div_iff₀ (mul_pos hn' (g_pos _))).mpr
  calc
    _ ≤ (rho/C*(rho^H)⁻¹)*(C*rho^(H-1)*B x) :=
      mul_le_mul_of_nonneg_left hprod
        (mul_nonneg (div_pos rho_pos hC).le (inv_pos.mpr (pow_pos rho_pos H)).le)
    _ = B x := by
      rw [show rho^H=rho^(H-1)*rho by
        calc rho^H = rho^((H-1)+1) := by congr 1; omega
             _ = _ := pow_succ _ _]
      field_simp [rho_pos.ne',hC.ne']

theorem natural_contracted_coordinate_lower : ∃ d : ℝ,0 < d ∧
    ∀ᶠ x : ℝ in atTop, ∀ n H : ℕ,0 < n → 1 ≤ H → n+H=m x →
      ∀ K : ℝ,0 < K → ∀ u : Fin n → ℝ,
        u ∈ orderedSlackRegion n (B x) (K*B x/((n:ℝ)*g (n+1))) → ∀ i : Fin n,
          d*K*(rho^(m x-i.val))⁻¹ ≤
            simplexScale (enlargementScale
              (fun r => 1+rowContractionError (m x-r))) u i := by
  obtain ⟨d,hd,hscale⟩ := natural_shift_scale_lower
  obtain ⟨c,hc,hcoord⟩ := contracted_ordered_coordinate_lower
  refine ⟨c*d,mul_pos hc hd,?_⟩
  filter_upwards [hscale,B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x hx hB
  intro n H hn hH hNm K hK u hu i
  have ht : 0 ≤ K*B x/((n:ℝ)*g (n+1)) :=
    div_nonneg (mul_pos hK hB).le (mul_nonneg (Nat.cast_nonneg _) (g_pos _).le)
  have hh := hcoord (by omega : n ≤ m x) ht hu i
  have hlo := mul_le_mul_of_nonneg_left (hx n H hn hH hNm) hK.le
  have hlo' : K*d*(rho^H)⁻¹ ≤ K*B x/((n:ℝ)*g (n+1)) := by
    simpa only [mul_assoc,mul_div_assoc] using hlo
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlo' hc.le) (inv_pos.mpr (pow_pos rho_pos (n-i.val))).le
  have hp : rho^H*rho^(n-i.val)=rho^(m x-i.val) := by
    rw [←pow_add]
    congr 1
    have := i.isLt
    omega
  have hid : (c*d)*K*(rho^(m x-i.val))⁻¹=
      (c*(K*d*(rho^H)⁻¹))*(rho^(n-i.val))⁻¹ := by
    rw [←hp,mul_inv_rev]
    ring
  exact hid.trans_le (hmul.trans hh)

end TotientAsymptotic

end

end OAI
