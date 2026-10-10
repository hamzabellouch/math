import OAI.Analysis.CircleDomains.Sobolev.PotentialLineRegularity
import OAI.Analysis.CircleDomains.Sobolev.LineLIntegralDerivativeBound

namespace OAI

/-! The actual path-bound potential has the expected derivative estimate
on every physical chart line with finite density integral. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem potential_chart_lintegral_increment_bound
    (d : PathCodeData X Y) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (v : Y → ℝ) (hv : ∀y (hy : y ∈ d.physicalDomain),
      v y = u (d.domainEquiv ⟨y, hy⟩).val)
    (φ : ℝ → Y) (hφ : Measurable φ) {a b : ℝ} {L : ℝ≥0}
    (hL : LipschitzOnWith L φ (Icc a b)) (hdom : MapsTo φ (Icc a b) d.physicalDomain) :
    ∀x ∈ Icc a b, ∀y ∈ Icc a b,
      ENNReal.ofReal |v (φ x) - v (φ y)| ≤
        ∫⁻t in uIoc x y, 4 * ((L : ℝ≥0∞) * g (φ t)) := by
  have hseg (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x < y) :
      ENNReal.ofReal |v (φ y) - v (φ x)| ≤
        ∫⁻t in uIoc x y, 4 * ((L : ℝ≥0∞) * g (φ t)) := by
    have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
    have hi := potential_chart_interval_bound d hdisj ν N u g hg m hm hpath v hv
      φ hφ hxy (hL.mono hsub) (fun t ht => hdom (hsub ht))
    rw [uIoc_of_le hxy.le,
      lintegral_const_mul' 4 (fun t => (L : ℝ≥0∞) * g (φ t)) (by norm_num),
      lintegral_const_mul' (L : ℝ≥0∞) (fun t => g (φ t)) ENNReal.coe_ne_top]
    rwa [show (∫⁻t in Ioc x y, g (φ t)) = ∫⁻t in Icc x y, g (φ t) from
      setLIntegral_congr Ioc_ae_eq_Icc]
  intro x hx y hy
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · simpa only [abs_sub_comm] using hseg x y hx hy hxy
  · simp
  · simpa only [uIoc_comm y x] using hseg y x hy hx hyx

theorem potential_chart_derivative_bound
    (d : PathCodeData X Y) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (v : Y → ℝ) (hv : ∀y (hy : y ∈ d.physicalDomain),
      v y = u (d.domainEquiv ⟨y, hy⟩).val)
    (φ : ℝ → Y) (hφ : Measurable φ) {a b : ℝ} (hab : a ≤ b) {L : ℝ≥0}
    (hL : LipschitzOnWith L φ (Icc a b)) (hdom : MapsTo φ (Icc a b) d.physicalDomain)
    (hfinite : (∫⁻t in Icc a b, g (φ t)) < ∞) :
    ∀ᵐ x ∂volume.restrict (Icc a b),
      |deriv (v ∘ φ) x| ≤ 4 * ((L : ℝ) * (g (φ x)).toReal) := by
  let ρ : ℝ → ℝ≥0∞ := fun t => 4 * ((L : ℝ≥0∞) * g (φ t))
  have hρ : Measurable ρ := measurable_const.mul (measurable_const.mul (hg.comp hφ))
  have hfin : (∫⁻t in Icc a b, ρ t) < ∞ := by
    dsimp [ρ]
    rw [lintegral_const_mul' 4 (fun t => (L : ℝ≥0∞) * g (φ t)) (by norm_num),
      lintegral_const_mul' (L : ℝ≥0∞) (fun t => g (φ t)) ENNReal.coe_ne_top]
    exact ENNReal.mul_lt_top (by simp) (ENNReal.mul_lt_top ENNReal.coe_lt_top hfinite)
  have hi := ae_abs_deriv_le_of_lintegral_bound hab hρ hfin
    (potential_chart_lintegral_increment_bound d hdisj ν N u g hg m hm hpath v hv φ hφ hL hdom)
  simpa only [ρ, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.coe_toReal,
    Function.comp_def] using hi

end CircleDomainRigidity

end OAI
