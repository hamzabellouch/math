import OAI.NumberTheory.PiExponent.Jets.FormalBranchOrder
import OAI.NumberTheory.PiExponent.Jets.JetGeometry

namespace OAI

noncomputable section

namespace PiExponent.FormalBranchOrder

open MvPowerSeries

variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem rational_weight_le_of_contact
    (v : σ → ℚ) (μ : ℚ) (a : σ → MvPowerSeries τ S)
    (hcontact : ∀ i (k : ℕ), (a i).order = (k : ℕ∞) → μ * v i ≤ (k : ℚ))
    (d : σ →₀ ℕ) (n : ℕ)
    (hbound : d.weight (order ∘ a) ≤ (n : ℕ∞)) :
    μ * d.weight v ≤ (n : ℚ) := by
  classical
  have hfinite : ∀ i ∈ d.support, (a i).order ≠ ⊤ := by
    intro i hi
    apply ne_top_of_le_ne_top (by simp : (n : ℕ∞) ≠ ⊤)
    exact (Finsupp.le_weight_of_ne_zero' (order ∘ a)
      (Finsupp.mem_support_iff.mp hi)).trans hbound
  have hsum :
      ((∑ i ∈ d.support, d i * (a i).order.toNat : ℕ) : ℕ∞) =
        d.weight (order ∘ a) := by
    simp only [Nat.cast_sum, Nat.cast_mul, Finsupp.weight_apply,
      Finsupp.sum, Function.comp_apply, nsmul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ENat.natCast_toNat (hfinite i hi)]
  have hnat : (∑ i ∈ d.support, d i * (a i).order.toNat : ℕ) ≤ n := by
    exact_mod_cast hsum.symm ▸ hbound
  calc
    μ * d.weight v = ∑ i ∈ d.support, (d i : ℚ) * (μ * v i) := by
      simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ d.support, (d i : ℚ) * ((a i).order.toNat : ℚ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (hcontact i _ (ENat.natCast_toNat (hfinite i hi)).symm) (by positivity)
    _ ≤ (n : ℚ) := by exact_mod_cast hnat

theorem rational_order_subst_of_jet_vanishing
    (v : σ → ℚ) (μ H : ℚ) (hμ : 0 ≤ μ)
    (f : MvPowerSeries σ R) (a : σ → MvPowerSeries τ S)
    (ha : HasSubst a)
    (hjet : ∀ d : σ →₀ ℕ, d.weight v < H → coeff d f = 0)
    (hcontact : ∀ i (k : ℕ), (a i).order = (k : ℕ∞) → μ * v i ≤ (k : ℚ)) :
    (⌈μ * H⌉₊ : ℕ∞) ≤ (f.subst a).order := by
  classical
  by_cases htop : (f.subst a).order = ⊤
  · rw [htop]
    exact le_top
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [← hn, ENat.natCast_le_natCast, Nat.ceil_le]
  obtain ⟨d, hd⟩ := ENat.exists_eq_iInf
    (fun d : σ →₀ ℕ => ⨅ _ : coeff d f ≠ 0, d.weight (order ∘ a))
  have hbound : (⨅ _ : coeff d f ≠ 0, d.weight (order ∘ a)) ≤ (n : ℕ∞) :=
    hd.le.trans ((le_weightedOrder_subst (fun _ : τ => 1) ha f).trans hn.ge)
  have hdne : coeff d f ≠ 0 := by
    intro he
    simp [he] at hbound
  have hbound' : d.weight (order ∘ a) ≤ (n : ℕ∞) := by
    simpa [hdne] using hbound
  have hH : H ≤ d.weight v := by
    by_contra! h
    exact hdne (hjet d h)
  exact (mul_le_mul_of_nonneg_left hH hμ).trans
    (rational_weight_le_of_contact v μ a hcontact d n hbound')

theorem rational_order_subst_of_mem_weightedIdeal
    (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i) (μ H : ℚ) (hμ : 0 ≤ μ)
    (f : MvPowerSeries σ R) (a : σ → MvPowerSeries τ S)
    (ha : HasSubst a) (hf : f ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ i (k : ℕ), (a i).order = (k : ℕ∞) → μ * v i ≤ (k : ℚ)) :
    (⌈μ * H⌉₊ : ℕ∞) ≤ (f.subst a).order :=
  rational_order_subst_of_jet_vanishing v μ H hμ f a ha hf hcontact

theorem hasSubst_of_positive_rational_contact [Finite σ]
    (v : σ → ℚ) (hv : ∀ i, 0 < v i) (μ : ℚ) (hμ : 0 < μ)
    (a : σ → MvPowerSeries τ S)
    (hcontact : ∀ i (k : ℕ), (a i).order = (k : ℕ∞) → μ * v i ≤ (k : ℚ)) :
    HasSubst a := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  apply order_ne_zero_iff_constCoeff_eq_zero.mp
  intro hz
  have h := hcontact i 0 hz
  have hp := mul_pos hμ (hv i)
  norm_num at h
  exact (not_le_of_gt hp) h

theorem rational_powerSeries_order_subst_of_mem_weightedIdeal
    (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i) (μ H : ℚ) (hμ : 0 ≤ μ)
    (f : MvPowerSeries σ R) (a : σ → PowerSeries S)
    (ha : HasSubst a) (hf : f ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ i (k : ℕ), (a i).order = (k : ℕ∞) → μ * v i ≤ (k : ℚ)) :
    (⌈μ * H⌉₊ : ℕ∞) ≤ PowerSeries.order (f.subst a) := by
  simp only [PowerSeries.order_eq_order] at hcontact ⊢
  exact rational_order_subst_of_mem_weightedIdeal v hv μ H hμ f a ha hf hcontact

theorem rational_mul_cutoff_le_order_toNat
    (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i) (μ H : ℚ) (hμ : 0 ≤ μ)
    (f : MvPowerSeries σ R) (a : σ → MvPowerSeries τ S)
    (ha : HasSubst a) (hf : f ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ i (k : ℕ), (a i).order = (k : ℕ∞) → μ * v i ≤ (k : ℚ))
    (hne : f.subst a ≠ 0) :
    μ * H ≤ ((f.subst a).order.toNat : ℚ) := by
  have h := rational_order_subst_of_mem_weightedIdeal v hv μ H hμ f a ha hf hcontact
  have hn : (f.subst a).order ≠ ⊤ := order_eq_top_iff.not.mpr hne
  have hh := ENat.toNat_le_toNat h hn
  have hh' : ⌈μ * H⌉₊ ≤ (f.subst a).order.toNat := by simpa using hh
  exact Nat.ceil_le.mp hh'

end PiExponent.FormalBranchOrder

end

end OAI
