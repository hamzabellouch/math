import OAI.Dynamics.EntropyCounterexample.Map
import OAI.Dynamics.EntropyCounterexample.SphereCutoffsAffine
import OAI.Dynamics.EntropyCounterexample.Saturation
import OAI.Dynamics.EntropyCounterexample.GainProfile

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340.Construction

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

def concreteData (L : ℝ) (hL : 2 < L) : SphereData where
  gate := SphereCutoffs.onePointClockGate
  cutoff := SphereCutoffs.onePointPreparationCutoff
  saturation := sphereSaturation (3 * L) (by linarith)
  gain := gainProfile L
  L := L

def concreteMap (L : ℝ) (hL : 2 < L) : RawManifold → RawManifold :=
  rawMap (concreteData L hL)

theorem concrete_gate_mem_Icc (L : ℝ) (hL : 2 < L) (z : Sphere) :
    (concreteData L hL).gate z ∈ Set.Icc (0 : ℝ) 1 :=
  SphereCutoffs.onePointClockGate_mem_Icc z

theorem concrete_cutoff_mem_Icc (L : ℝ) (hL : 2 < L) (z : Sphere) :
    (concreteData L hL).cutoff z ∈ Set.Icc (0 : ℝ) 1 :=
  SphereCutoffs.onePointPreparationCutoff_mem_Icc z

theorem concrete_saturation_bound (L : ℝ) (hL : 2 < L) (z : Sphere) :
    ‖(concreteData L hL).saturation z‖ ≤ 2 :=
  norm_sphereSaturation_le_two (3 * L) _ z

theorem concrete_gain_mem_Icc (L : ℝ) (hL : 2 < L) (t : ℝ) :
    (concreteData L hL).gain t ∈ Set.Icc (0 : ℝ) L :=
  gainProfile_mem_Icc (by linarith) t

theorem concrete_input_summable (L : ℝ) (hL : 2 < L)
    (i : Fin 3) (t : ℝ) (z : Sphere) :
    Summable (fun n => inputTerm (concreteData L hL) i n t z) :=
  summable_inputTerm _ (by change 1 < L; linarith)
    (fun z => (concrete_cutoff_mem_Icc L hL z).1)
    (fun z => (concrete_cutoff_mem_Icc L hL z).2) i t z

theorem concrete_input_bound (L : ℝ) (hL : 2 < L)
    (i : Fin 3) (t : ℝ) (z : Sphere) :
    ‖baseInput (concreteData L hL) i t z‖ ≤ L / (10 * (L - 1)) :=
  norm_baseInput_le _ (by change 1 < L; linarith)
    (fun z => (concrete_cutoff_mem_Icc L hL z).1)
    (fun z => (concrete_cutoff_mem_Icc L hL z).2) i t z

theorem concreteMap_not_bijective (L : ℝ) (hL : 2 < L) :
    ¬ Function.Bijective (concreteMap L hL) :=
  rawMap_not_bijective _

@[simp] theorem concrete_saturation_zero (L : ℝ) (hL : 2 < L) :
    (concreteData L hL).saturation ((0 : ℂ) : Sphere) = 0 := by
  simp [concreteData]

@[simp] theorem concrete_gate_infty (L : ℝ) (hL : 2 < L) :
    (concreteData L hL).gate ∞ = 1 := rfl

@[simp] theorem concrete_gate_zero (L : ℝ) (hL : 2 < L) :
    (concreteData L hL).gate ((0 : ℂ) : Sphere) = 0 := by
  exact SphereCutoffs.affineClockGate_eq_zero (by simp)

@[simp] theorem clockIncrement_infty (L : ℝ) (hL : 2 < L)
    (t : AddCircle (100 : ℝ)) :
    clockIncrement (concreteData L hL) t ∞ = 1 := by
  simp [clockIncrement, AddCircle.liftIco]

theorem concreteMap_infty_zero (L : ℝ) (hL : 2 < L)
    (t : AddCircle (100 : ℝ)) :
    concreteMap L hL (t, ∞, fun _ => ((0 : ℂ) : Sphere)) =
      (t + (1 : ℝ), ∞, fun _ => ((0 : ℂ) : Sphere)) := by
  simp [concreteMap, rawMap]

private theorem readoutCoeff_fifty (i : Fin 3) : readoutCoeff i 50 = 0 := by
  by_contra h
  have hs : (50 : ℝ) ∈ Function.support (readoutCoeff i) := h
  rw [readoutCoeff_support] at hs
  have hb := readoutInterval_subset i hs
  norm_num at hb

@[simp] theorem periodicReadout_fifty (i : Fin 3) :
    periodicReadout i ((50 : ℝ) : AddCircle (100 : ℝ)) = 0 := by
  rw [periodicReadout, AddCircle.liftIco_coe_apply (by norm_num)]
  exact readoutCoeff_fifty i

@[simp] theorem readout_fifty (D : SphereData) (v : Fin 3 → Sphere) :
    readout D ((50 : ℝ) : AddCircle (100 : ℝ)) v = 0 := by
  simp [readout]

@[simp] theorem clockIncrement_fifty_zero (L : ℝ) (hL : 2 < L) :
    clockIncrement (concreteData L hL) ((50 : ℝ) : AddCircle (100 : ℝ))
      ((0 : ℂ) : Sphere) = 0 := by
  rw [clockIncrement, AddCircle.liftIco_coe_apply (by norm_num)]
  simp only [concrete_gate_zero, Clock.increment_zero]
  exact (Clock.barrier_eq_zero_iff 50).2 ⟨0, by norm_num⟩

@[simp] theorem periodicGain_fifty (L : ℝ) (hL : 2 < L) :
    periodicGain (concreteData L hL) ((50 : ℝ) : AddCircle (100 : ℝ)) = L := by
  rw [periodicGain, AddCircle.liftIco_coe_apply (by norm_num)]
  exact gainProfile_eq_gain L (by norm_num)

theorem concreteMap_fifty_zero (L : ℝ) (hL : 2 < L) (v : Fin 3 → Sphere) :
    concreteMap L hL (((50 : ℝ) : AddCircle (100 : ℝ)), ((0 : ℂ) : Sphere), v) =
      (((50 : ℝ) : AddCircle (100 : ℝ)), ((0 : ℂ) : Sphere),
        fun i => (((L : ℂ) * (concreteData L hL).saturation (v i)) : Sphere)) := by
  simp [concreteMap, rawMap]

end Problem340.Construction

end

end OAI
