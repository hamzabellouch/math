import OAI.NumberTheory.PiExponent.Jets.FormalBranchOrderRational

namespace OAI

noncomputable section
namespace PiExponent.BranchContact

variable {ι : Type*} [Fintype ι]

def active (a : ι → PowerSeries ℂ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => a i ≠ 0)

@[simp] theorem mem_active (a : ι → PowerSeries ℂ) (i : ι) :
    i ∈ active a ↔ a i ≠ 0 := by
  classical
  simp [active]

theorem active_nonempty (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0) :
    (active a).Nonempty := by
  obtain ⟨i,hi⟩ := hne
  exact ⟨i,(mem_active a i).mpr hi⟩

def contact (v : ι → ℚ) (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0) : ℚ :=
  (active a).inf' (active_nonempty a hne) (fun i => ((a i).order.toNat : ℚ) / v i)

theorem contact_le (v : ι → ℚ) (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (i : ι) (hi : a i ≠ 0) :
    contact v a hne ≤ ((a i).order.toNat : ℚ) / v i :=
  Finset.inf'_le _ ((mem_active a i).mpr hi)

theorem exists_attains (v : ι → ℚ) (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0) :
    ∃ i, a i ≠ 0 ∧ contact v a hne = ((a i).order.toNat : ℚ) / v i := by
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' (active_nonempty a hne)
    (fun i => ((a i).order.toNat : ℚ) / v i)
  exact ⟨i,(mem_active a i).mp hi,he⟩

theorem contact_pos (v : ι → ℚ) (hv : ∀ i, 0 < v i)
    (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (hc : ∀ i, PowerSeries.constantCoeff (a i) = 0) : 0 < contact v a hne := by
  obtain ⟨i,hi,he⟩ := exists_attains v a hne
  rw [he]
  apply div_pos _ (hv i)
  have horder := PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (hc i)
  rw [← PowerSeries.coe_toNat_order hi] at horder
  have hnat : 1 ≤ (a i).order.toNat := by exact_mod_cast horder
  exact_mod_cast (show 0 < (a i).order.toNat by omega)

theorem contact_bound (v : ι → ℚ) (hv : ∀ i, 0 < v i)
    (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0) (i : ι) (k : ℕ)
    (hk : (a i).order = (k : ℕ∞)) : contact v a hne * v i ≤ (k : ℚ) := by
  have hi : a i ≠ 0 := by
    intro hz
    simp [hz] at hk
  have hnat : (a i).order.toNat = k := by simpa using congrArg ENat.toNat hk
  exact hnat ▸ (le_div_iff₀ (hv i)).mp (contact_le v a hne i hi)

theorem le_contact (v : ι → ℚ) (hv : ∀ i, 0 < v i)
    (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0) (μ : ℚ)
    (hμ : ∀ i (k : ℕ), (a i).order = (k : ℕ∞) → μ * v i ≤ (k : ℚ)) :
    μ ≤ contact v a hne := by
  apply Finset.le_inf'
  intro i hi
  apply (le_div_iff₀ (hv i)).mpr
  exact hμ i _ (PowerSeries.coe_toNat_order ((mem_active a i).mp hi)).symm

theorem order_add_lower (B : ℚ) (f g : PowerSeries ℂ)
    (hf : ∀ k : ℕ, f.order = (k : ℕ∞) → B ≤ (k : ℚ))
    (hg : ∀ k : ℕ, g.order = (k : ℕ∞) → B ≤ (k : ℚ))
    (k : ℕ) (hk : (f + g).order = (k : ℕ∞)) : B ≤ (k : ℚ) := by
  have hmin : min f.order g.order ≤ (k : ℕ∞) :=
    (PowerSeries.min_order_le_order_add f g).trans hk.le
  rcases min_le_iff.mp hmin with h | h
  · have hn : f.order ≠ ⊤ := ne_top_of_le_ne_top (by simp) h
    have he := ENat.natCast_toNat hn
    have hb := hf f.order.toNat he.symm
    have hnat : f.order.toNat ≤ k := by
      exact_mod_cast he.symm ▸ h
    exact hb.trans (by exact_mod_cast hnat)
  · have hn : g.order ≠ ⊤ := ne_top_of_le_ne_top (by simp) h
    have he := ENat.natCast_toNat hn
    have hb := hg g.order.toNat he.symm
    have hnat : g.order.toNat ≤ k := by
      exact_mod_cast he.symm ▸ h
    exact hb.trans (by exact_mod_cast hnat)

theorem exists_attaining_add (v : ι → ℚ) (hv : ∀ i, 0 < v i)
    (a t : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (ht : ∀ i (k : ℕ), (t i).order = (k : ℕ∞) → contact v a hne * v i < (k : ℚ)) :
    ∃ i, a i + t i ≠ 0 ∧ (a i + t i).order = (a i).order ∧
      contact v a hne = ((a i + t i).order.toNat : ℚ) / v i := by
  obtain ⟨i,hi,he⟩ := exists_attains v a hne
  have heq : contact v a hne * v i = ((a i).order.toNat : ℚ) :=
    (eq_div_iff (ne_of_gt (hv i))).mp he
  have hord : (a i).order < (t i).order := by
    by_cases hzero : t i = 0
    · simpa [hzero] using PowerSeries.order_finite_iff_ne_zero.mpr hi
    · have ht' := ht i (t i).order.toNat (PowerSeries.coe_toNat_order hzero).symm
      rw [heq] at ht'
      have hnat : (a i).order.toNat < (t i).order.toNat := by exact_mod_cast ht'
      rw [← PowerSeries.coe_toNat_order hi, ← PowerSeries.coe_toNat_order hzero]
      exact_mod_cast hnat
  have hsum : (a i + t i).order = (a i).order := by
    rw [PowerSeries.order_add_of_order_ne _ _ hord.ne, inf_eq_left.mpr hord.le]
  have hne' : a i + t i ≠ 0 := by
    intro hz
    have hh := PowerSeries.order_eq_top.mpr hz
    rw [hsum] at hh
    exact hi (PowerSeries.order_eq_top.mp hh)
  exact ⟨i,hne',hsum,hsum ▸ he⟩

theorem add_not_all_zero (v : ι → ℚ) (hv : ∀ i, 0 < v i)
    (a t : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (ht : ∀ i (k : ℕ), (t i).order = (k : ℕ∞) → contact v a hne * v i < (k : ℚ)) :
    ∃ i, a i + t i ≠ 0 := by
  obtain ⟨i,hi,_⟩ := exists_attaining_add v hv a t hne ht
  exact ⟨i,hi⟩

theorem contact_add_high_tail (v : ι → ℚ) (hv : ∀ i, 0 < v i)
    (a t : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (ht : ∀ i (k : ℕ), (t i).order = (k : ℕ∞) → contact v a hne * v i < (k : ℚ)) :
    contact v (fun i => a i + t i) (add_not_all_zero v hv a t hne ht) = contact v a hne := by
  apply le_antisymm
  · obtain ⟨i,hi,horder,he⟩ := exists_attaining_add v hv a t hne ht
    exact (contact_le v _ _ i hi).trans_eq he.symm
  · apply le_contact v hv _ _
    intro i k hk
    exact order_add_lower _ (a i) (t i) (contact_bound v hv a hne i)
      (fun n hn => (ht i n hn).le) k hk

end PiExponent.BranchContact

end

end OAI
