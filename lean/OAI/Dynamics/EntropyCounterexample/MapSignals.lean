import OAI.Dynamics.EntropyCounterexample.MapData

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340.Construction

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

theorem preparationCoeff_eq_zero_of_outside {t : ℝ} (ht : t ∉ Set.Ioo 8 12) :
    preparationCoeff t = 0 := by
  by_contra h
  have hs : t ∈ Function.support preparationCoeff := h
  rw [preparationCoeff_support] at hs
  exact ht hs

theorem baseInput_eq_zero_of_outside (D : SphereData) (i : Fin 3)
    {t : ℝ} (ht : t ∉ Set.Ioo 8 12) (z : Sphere) : baseInput D i t z = 0 := by
  simp [baseInput, preparationCoeff_eq_zero_of_outside ht]

theorem input_eq_zero_of_coe_outside (D : SphereData) (i : Fin 3)
    {t : ℝ} (ht : t ∈ Set.Ico 0 100) (hout : t ∉ Set.Ioo 8 12) (z : Sphere) :
    input D i (t : AddCircle (100 : ℝ)) z = 0 := by
  rw [input, AddCircle.liftIco_zero_coe_apply ht]
  exact baseInput_eq_zero_of_outside D i hout z

theorem periodicReadout_eq_zero_of_coe_outside (i : Fin 3)
    {t : ℝ} (ht : t ∈ Set.Ico 0 100) (hout : t ∉ Set.Ioo 74 80) :
    periodicReadout i (t : AddCircle (100 : ℝ)) = 0 := by
  rw [periodicReadout, AddCircle.liftIco_zero_coe_apply ht]
  by_contra h
  have hs : t ∈ Function.support (readoutCoeff i) := h
  rw [readoutCoeff_support] at hs
  exact hout (readoutInterval_subset i hs)

theorem readout_eq_zero_of_coe_outside (D : SphereData)
    {t : ℝ} (ht : t ∈ Set.Ico 0 100) (hout : t ∉ Set.Ioo 74 80)
    (v : Fin 3 → Sphere) : readout D (t : AddCircle (100 : ℝ)) v = 0 := by
  simp [readout, periodicReadout_eq_zero_of_coe_outside _ ht hout]

theorem rawMap_main_of_no_readout (D : SphereData)
    {t : ℝ} (ht : t ∈ Set.Ico 0 100) (hout : t ∉ Set.Ioo 74 80)
    (z : Sphere) (v : Fin 3 → Sphere) :
    (rawMap D ((t : AddCircle (100 : ℝ)), z, v)).2.1 = perturbedSquare 0 z := by
  simp only [rawMap, readout_eq_zero_of_coe_outside D ht hout v]

theorem concreteMap_register_reset (L : ℝ) (hL : 2 < L)
    {t : ℝ} (ht : t ∈ Set.Icc 2 5) (z : Sphere) (v : Fin 3 → Sphere) (i : Fin 3) :
    (concreteMap L hL ((t : AddCircle (100 : ℝ)), z, v)).2.2 i = ((0 : ℂ) : Sphere) := by
  have hstrip : t ∈ Set.Ico (0 : ℝ) 100 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hout : t ∉ Set.Ioo (8 : ℝ) 12 := by
    intro h
    linarith [ht.2, h.1]
  have hg : periodicGain (concreteData L hL) (t : AddCircle (100 : ℝ)) = 0 := by
    rw [periodicGain, AddCircle.liftIco_zero_coe_apply hstrip]
    exact gainProfile_eq_zero L ht
  simp [concreteMap, rawMap, hg, input_eq_zero_of_coe_outside _ _ hstrip hout z]

theorem periodicGain_eq_gain_of_coe (L : ℝ) (hL : 2 < L)
    {t : ℝ} (ht : t ∈ Set.Icc 7 90) :
    periodicGain (concreteData L hL) (t : AddCircle (100 : ℝ)) = L := by
  rw [periodicGain, AddCircle.liftIco_zero_coe_apply
    (show t ∈ Set.Ico (0 : ℝ) 100 from ⟨by linarith [ht.1], by linarith [ht.2]⟩)]
  exact gainProfile_eq_gain L ht

@[simp] theorem clock_coe_add_int_period (t : ℝ) (k : ℤ) :
    ((t + 100 * (k : ℝ) : ℝ) : AddCircle (100 : ℝ)) = (t : AddCircle (100 : ℝ)) := by
  have hzero : ((100 * (k : ℝ) : ℝ) : AddCircle (100 : ℝ)) = 0 := by
    rw [mul_comm, ← zsmul_eq_mul, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]
  rw [AddCircle.coe_add, hzero, add_zero]

end Problem340.Construction

end

end OAI
