import OAI.NumberTheory.CubicMoment.Estimates.TypeILow

namespace OAI

/-! Fixed logarithmic coefficient factors can be retained in the actual
weight family. This is the form used by short logarithmic convolutions. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def logPowerWeight {γ : Type*} (Y : γ → ℝ) (W : γ → ℝ → ℂ)
    (d : ℕ) (i : γ) (x : ℝ) : ℂ := ((1+Real.log (Y i))^d:ℝ) • W i x

def LogarithmicWeightFamily.logPower {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ}
    (h : LogarithmicWeightFamily Y W) (d : ℕ) :
    LogarithmicWeightFamily Y (logPowerWeight Y W d) := by
  have hsupp (i : γ) : Function.support (logPowerWeight Y W d i) ⊆ Function.support (W i) := by
    intro x hx hz
    exact hx (by simp [logPowerWeight,hz])
  refine ⟨h.length_one,fun i => (h.compact i).mono (hsupp i),
    fun i => (closure_mono (hsupp i)).trans (h.positive i),
    fun i => (h.smooth i).const_smul _,h.radius,h.radius_nonneg,?_,?_⟩
  · intro i u hu
    apply h.support_bound i u
    exact closure_mono (fun x hx => by
      intro hz
      exact hx (by simp [logPowerWeight,hz])) hu
  · intro n
    obtain ⟨C,A,hC,hbound⟩ := h.derivative_bound n
    refine ⟨C,A+d,hC,?_⟩
    intro i u
    have hw : ContDiff ℝ ∞ (fun v => W i (Real.exp (-v))) := (h.smooth i).comp (by fun_prop)
    have hL : 0 ≤ 1+Real.log (Y i) := by linarith [Real.log_nonneg (h.length_one i)]
    change ‖iteratedFDeriv ℝ n (fun v => ((1+Real.log (Y i))^d:ℝ) •
      W i (Real.exp (-v))) u‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' ((hw.of_le (by exact_mod_cast le_top)).contDiffAt),
      norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hL _)]
    calc
      _ ≤ (1+Real.log (Y i))^d*(C*(1+Real.log (Y i))^A) :=
        mul_le_mul_of_nonneg_left (hbound i u) (pow_nonneg hL _)
      _ = _ := by rw [pow_add]; ring

theorem typeI_low_log_coefficients
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    (ℓ : ℤ) (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {B A : ℝ} (hB : 1 ≤ B) (hA : 0 ≤ A) (k d : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X R U : ℝ),
      2 ≤ X → B ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, Y (w r) = X) →
      (∀ r ∈ S, ∀ x : ℝ, B < x → W (w r) x = 0) →
      (∀ r ∈ S, ‖α r‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k*(1+Real.log X)^d) →
      ‖∑ r ∈ S, α r*(metaplecticAngularSmoothSum r ℓ (W (w r)) U 0-
        angularSmoothModel r ℓ (W (w r)) U)‖ ≤ K*X^(5/6-1/100:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := typeI_low_of_published hV (hW.logPower d) ℓ hGamma hB hA k
  refine ⟨K,hK,?_⟩
  intro w S α X R U hX hBX hR hU hRU hRhi hS hY hcut hα
  let L : ℝ := (1+Real.log X)^d
  have hLb : 0 < 1+Real.log X := by
    linarith [Real.log_nonneg (show 1 ≤ X by linarith)]
  have hLp : 0 < L := pow_pos hLb _
  have hLc : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hLp.ne'
  let β : Eisenstein → ℂ := fun r => α r/(L:ℂ)
  have hβ (r : Eisenstein) (hr : r ∈ S) :
      ‖β r‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k := by
    rw [show β r = α r/(L:ℂ) from rfl,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hLp]
    exact (div_le_iff₀ hLp).mpr (hα r hr)
  have hv (r : Eisenstein) (hr : r ∈ S) :
      logPowerWeight Y W d (w r) = fun x => (L:ℂ)*W (w r) x := by
    funext x
    simp only [logPowerWeight,hY r hr,Complex.real_smul,L]
  have he : (∑ r ∈ S, β r*(metaplecticAngularSmoothSum r ℓ (logPowerWeight Y W d (w r)) U 0-
      angularSmoothModel r ℓ (logPowerWeight Y W d (w r)) U)) =
    ∑ r ∈ S, α r*(metaplecticAngularSmoothSum r ℓ (W (w r)) U 0-
      angularSmoothModel r ℓ (W (w r)) U) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [hv r hr,metaplecticAngularSmoothSum_const_mul,angularSmoothModel_const_mul]
    dsimp [β]
    field_simp [hLc]
  rw [←he]
  exact hbound w S β X R U hX hBX hR hU hRU hRhi hS hY
    (fun r hr x hx => by
      rw [hv r hr]
      change (L:ℂ)*W (w r) x = 0
      rw [hcut r hr x hx,mul_zero]) hβ

end CubicFirstMoment

end

end OAI
