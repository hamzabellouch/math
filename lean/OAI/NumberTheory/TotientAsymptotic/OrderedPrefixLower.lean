import OAI.NumberTheory.TotientAsymptotic.OrderedTranslateVolume
import OAI.NumberTheory.TotientAsymptotic.OrderedShiftBudget

namespace OAI

/-! A uniform positive fraction of the prefix volume has strict order and slack. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace TotientAsymptotic

theorem ordered_prefix_volume_lower : ∃ K δ : ℝ,0 < K ∧ 0 < δ ∧
    ∀ᶠ N : ℕ in atTop, ∀ B : ℝ,0 < B →
      δ*volume.real (prefixRegion (N+2) B 0 0) ≤
        volume.real (orderedSlackRegion (N+2) B
          (K*B/((N+2:ℝ)*g (N+3)))) := by
  obtain ⟨A,c,s,hA,hc,hs,hvol⟩ := ordered_translate_volume
  obtain ⟨c₀,hc₀,hgap⟩ := renewalBackground_uniform_gap
  obtain ⟨C,hC,hupper⟩ := renewal_uniform_upper
  let D := c₀*rho/C
  have hD : 0 < D := div_pos (mul_pos hc₀ rho_pos) hC
  obtain ⟨K,hK,hsmall⟩ := exists_ordered_shift_size hA hc hs hD
  refine ⟨K,Real.exp (-2*K)/2,hK,by positivity,?_⟩
  obtain ⟨L,hL⟩ := exists_nat_gt (max (2*K) (2*s*D*K))
  filter_upwards [eventually_ge_atTop L] with N hN
  intro B hB
  have hn : (0:ℝ) < N+2 := by positivity
  have hLN : (L:ℝ) ≤ N+2 := by exact_mod_cast (show L ≤ N+2 by omega)
  have hKbound : 2*K ≤ N+2 := (le_max_left _ _).trans (hL.le.trans hLN)
  have hsbound : 2*s*D*K ≤ N+2 := (le_max_right _ _).trans (hL.le.trans hLN)
  let t := K*B/((N+2:ℝ)*g (N+3))
  let T := D*K*B/(N+2:ℝ)
  let E := t*(g (N+3)-a (N+3))
  have heq : N+2+1=N+3 := by omega
  obtain ⟨ht,hE,hcost⟩ := renewal_shift_cost (by omega : 0 < N+2) hB hK
  simp only [Nat.cast_add,Nat.cast_ofNat,heq] at ht hE hcost
  change 0 < t at ht
  change 0 ≤ E at hE
  change E ≤ K*B/(N+2:ℝ) at hcost
  have hcosthalf : K*B/(N+2:ℝ) ≤ B/2 := by
    apply (div_le_iff₀ hn).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hKbound hB.le]
  have hEB : 2*E ≤ B := by linarith only [hcost,hcosthalf]
  have hB' : 0 < B-E := by linarith only [hB,hEB]
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hThalf : s*T ≤ B/2 := by
    dsimp [T]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hn).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hsbound hB.le]
  have hTB : s*T ≤ B-E := by linarith only [hThalf,hEB]
  have hgapT : T ≤ c₀*t*(rho^(N+2))⁻¹ := by
    have hh := renewal_gap_cost_comparison hC hc₀ hupper (N+2)
    rw [heq] at hh
    calc
      T = t*(D*g (N+3)) := by dsimp [T,t]; field_simp [(g_pos (N+3)).ne',hn.ne']
      _ ≤ t*(c₀*(rho^(N+2))⁻¹) := mul_le_mul_of_nonneg_left hh ht.le
      _ = _ := by ring
  have hcoord (i : Fin (N+1)) : rho^(i.val+1)*T ≤
      renewalBackground (N+2) t i.castSucc-renewalBackground (N+2) t i.succ := by
    have hh := hgapT.trans (hgap N t ht.le i)
    have hh' := (le_div_iff₀ (pow_pos rho_pos (i.val+1))).mp hh
    simpa only [mul_comm] using hh'
  have hscaled : s*D*K ≤ s*(N+2:ℝ)*T/(B-E) := by
    apply (le_div_iff₀ hB').mpr
    have he : s*(N+2:ℝ)*T=s*D*K*B := by dsimp [T]; field_simp
    rw [he]
    nlinarith only [mul_nonneg (show 0 ≤ s*D*K by positivity) hE]
  have hden : 0 < 1-Real.exp (-c) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hsmall' : Real.exp (A-s*(N+2:ℝ)*T/(B-E))/(1-Real.exp (-c)) ≤ 1/2 := by
    apply le_trans _ hsmall
    apply div_le_div_of_nonneg_right _ hden.le
    exact Real.exp_le_exp.mpr (by linarith only [hscaled])
  have hmain := hvol N B t T hB ht.le hE
    (by simpa only [E,mul_assoc] using hEB) hT hTB hcoord hsmall'
  have hbudget : (N+2:ℝ)*E/B ≤ K := by
    apply (div_le_iff₀ hB).mpr
    have hh := (le_div_iff₀ hn).mp hcost
    nlinarith only [hh]
  have hexp : Real.exp (-2*K) ≤ Real.exp (-2*(N+2:ℝ)*E/B) := by
    apply Real.exp_le_exp.mpr
    have he : -2*(N+2:ℝ)*E/B= -2*((N+2:ℝ)*E/B) := by ring
    rw [he]
    linarith only [hbudget]
  apply le_trans _ hmain
  have hh := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hexp (by norm_num : (0:ℝ) ≤ 2))
    (show 0 ≤ volume.real (prefixRegion (N+2) B 0 0) from ENNReal.toReal_nonneg)
  have harg : -2*(N+2:ℝ)*E/B=
      -2*(N+2:ℝ)*t*(g (N+3)-a (N+3))/B := by dsimp [E]; ring
  rw [harg] at hh
  exact hh

end TotientAsymptotic

end

end OAI
