import Mathlib
import OAI.Probability.SKValue.Evolution.MildBurgersJets
import OAI.Probability.SKValue.Equations.BetaBound
import OAI.Probability.SKValue.Equations.WeightedCap

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma SmoothEvolution.jet_mild_bound {T a b Γ A K : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) (hγ : MonotoneOn γ (Icc (0 : ℝ) T))
    (hi : IntervalIntegrable γ volume 0 T) (ha : 0≤a) (hab : a<b) (hb : b≤T) (m : ℕ)
    (hΓ : 0≤Γ) (hA : 0≤A) (hK : 0≤K)
    (hγbd : ∀ s∈Icc a b, |γ s|≤Γ)
    (hprev : ∀ s∈Icc a b, ∀ x, |iteratedDeriv m (deriv (V s)) x|≤A)
    (hprod : ∀ s∈Icc a b, ∀ x,
      |iteratedDeriv m (fun y ↦ deriv (V s) y*deriv (deriv (V s)) y) x|≤
        |iteratedDeriv (m+1) (deriv (V s)) x|+K)
    {t : ℝ} (ht : t∈Ico a b) (x : ℝ) :
    |iteratedDeriv (m+1) (deriv (V t)) x|≤A/Real.sqrt (b-t)+
      Γ*(8*weightedCap a b (fun s ↦ iteratedDeriv (m+1) (deriv (V s)))+2*K*Real.sqrt (b-t)) := by
  let F := fun s ↦ iteratedDeriv (m+1) (deriv (V s))
  let R := weightedCap a b F
  obtain ⟨C,hC,hbd⟩ := h.bound (m+1)
  have hbd' : ∀ s∈Icc a b, ∀ y, |F s y|≤C := fun s hs y ↦ hbd s ⟨ha.trans hs.1,hs.2.trans hb⟩ y
  have hR : 0≤R := weightedCap_nonneg hab.le hC hbd'
  have habT : b∈Icc (0 : ℝ) T := ⟨ha.trans hab.le,hb⟩
  have htT : t∈Icc (0 : ℝ) T := ⟨ha.trans ht.1,ht.2.le.trans hb⟩
  let G := fun s y ↦ deriv (V s) y*deriv (deriv (V s)) y
  let H := fun s ↦ γ s*deriv (heat (s-t) (iteratedDeriv m (G s))) x
  let J := fun s ↦ Γ*(R*sqrtKernel t b s+K*(Real.sqrt (s-t))⁻¹)
  have hg := h.gradient_family.mul h.gradient_family.deriv
  have hi' : IntervalIntegrable γ volume t b := hi.mono_set (by
    simp only [uIcc_of_le ht.2.le,uIcc_of_le (ha.trans (hab.le.trans hb))]
    exact Icc_subset_Icc htT.1 hb)
  have hHi : IntervalIntegrable H volume t b := by
    have hh := hi'.mul_continuousOn (show ContinuousOn
        (fun s ↦ heat (s-t) (iteratedDeriv (m+1) (G s)) x) (uIcc t b) from by
      simpa only [uIcc_of_le ht.2.le] using
        ((hg.iteratedDeriv (m+1)).heat_continuousOn t x).mono (Icc_subset_Icc htT.1 hb))
    apply hh.congr
    intro s hs
    rw [uIoc_of_le ht.2.le] at hs
    have hsT : s∈Icc (0 : ℝ) T := ⟨htT.1.trans hs.1.le,hs.2.trans hb⟩
    dsimp only [H,G]
    rw [iteratedDeriv_succ, ((hg.slices s hsT).iteratedDeriv m).heat_deriv]
  have hJi : IntervalIntegrable J volume t b :=
    (((sqrtKernel_integrable ht.2).const_mul R).add
      ((intervalIntegrable_inv_sqrt_sub ht.2.le).const_mul K)).const_mul Γ
  have hpoint (s : ℝ) (hs : s∈Ioo t b) : |H s|≤J s := by
    have hsab : s∈Ico a b := ⟨ht.1.trans hs.1.le,hs.2⟩
    have hsT : s∈Icc (0 : ℝ) T := ⟨ha.trans hsab.1,hs.2.le.trans hb⟩
    have hspos := Real.sqrt_pos.mpr (sub_pos.mpr hs.1)
    have hsbpos := Real.sqrt_pos.mpr (sub_pos.mpr hs.2)
    have hf := ((hg.slices s hsT).iteratedDeriv m).heat_kernel_deriv_bound
      (A := R/Real.sqrt (b-s)+K) (by positivity)
      (fun y ↦ (hprod s ⟨hsab.1,hsab.2.le⟩ y).trans
        (add_le_add (abs_le_weightedCap_div hab.le hC hbd' hsab y) le_rfl))
      (sub_pos.mpr hs.1) x
    dsimp only [H]
    rw [abs_mul]
    apply (mul_le_mul (hγbd s ⟨hsab.1,hsab.2.le⟩) hf (abs_nonneg _) hΓ).trans_eq
    dsimp only [J,sqrtKernel]
    ring
  have hint : |∫ s in t..b, H s|≤Γ*(8*R+2*K*Real.sqrt (b-t)) := by
    calc
      _ ≤ ∫ s in t..b, |H s| := intervalIntegral.abs_integral_le_integral_abs ht.2.le
      _ ≤ ∫ s in t..b, J s := intervalIntegral.integral_mono_on_of_le_Ioo ht.2.le hHi.abs hJi hpoint
      _ = Γ*(R*(∫ s in t..b, sqrtKernel t b s)+K*(2*Real.sqrt (b-t))) := by
        dsimp only [J]
        rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
          ((sqrtKernel_integrable ht.2).const_mul R) ((intervalIntegrable_inv_sqrt_sub ht.2.le).const_mul K),
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,integral_inv_sqrt_sub ht.2.le]
      _ ≤ Γ*(R*8+K*(2*Real.sqrt (b-t))) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left
          (sqrtKernel_integral_le_eight ht.2) hR) le_rfl) hΓ
      _ = _ := by ring
  have hterm := ((h.slices b habT).jets.iteratedDeriv m).heat_kernel_deriv_bound hA
    (hprev b ⟨hab.le,le_rfl⟩) (sub_pos.mpr ht.2) x
  have hid := congrFun (h.burgers_jet_mild hm hγ hi htT.1 ht.2.le hb m) x
  change F t x=_+(∫ s in t..b, H s) at hid
  change |F t x|≤A/Real.sqrt (b-t)+Γ*(8*R+2*K*Real.sqrt (b-t))
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hterm hint)

end SKValue

end

end OAI
