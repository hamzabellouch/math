import OAI.Probability.DilutedSpin.AveragedRootBounds
import OAI.Probability.DilutedSpin.CompoundSample
import OAI.Probability.DilutedSpin.ConcentrationRate
import OAI.Probability.DilutedSpin.PhysicalInsertionIdentity
import OAI.Probability.DilutedSpin.RootMapLaw

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped NNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N L : ℕ}

lemma integrable_energyRoot_field_mean (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (field : Y → ℝ) (hfield : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (E : (Fin N → Spin) → ℝ) :
    Integrable (fun h => ∫ a,energyRoot Q m field factor h a E ∂compoundRootLaw ν s)
      (rootLaw N (fun _ => ξ)) := by
  have hmi : Measurable (fun h : RootPath Y N => ∫ a,energyRoot Q m field factor h a E ∂compoundRootLaw ν s) := by
    exact ((measurable_energyRoot Q m field hfield factor).comp
      ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
  exact Integrable.of_bound hmi.aestronglyMeasurable (‖E‖+H*N+D*s)
    (ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs] using energyRoot_marks_bound ν s Q m hm field factor hh hf h E))

lemma averagedEnergyRoot_increment (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (field : Y → ℝ) (hfield : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (E J : (Fin N → Spin) → ℝ) :
    averagedEnergyRoot ξ ν s Q m field factor (E+J)-averagedEnergyRoot ξ ν s Q m field factor E=
      ∫ h,∫ a,energyRoot Q m field factor h a (E+J)-energyRoot Q m field factor h a E
        ∂compoundRootLaw ν s ∂rootLaw N (fun _ => ξ) := by
  unfold averagedEnergyRoot
  rw [← integral_sub (integrable_energyRoot_field_mean ξ ν s Q m hm field hfield factor hh hf (E+J))
    (integrable_energyRoot_field_mean ξ ν s Q m hm field hfield factor hh hf E)]
  apply integral_congr_ae
  filter_upwards [] with h
  exact (integral_sub (integrable_energyRoot_marks ν s Q m hm field factor hh hf h (E+J))
    (integrable_energyRoot_marks ν s Q m hm field factor hh hf h E)).symm

omit [MeasurableSpace Y] [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
lemma energyRoot_increment_bound
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (field : Y → ℝ)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (h : RootPath Y N) (a : Sigma (RootPath I)) (E J : (Fin N → Spin) → ℝ) :
    |energyRoot Q m field factor h a (E+J)-energyRoot Q m field factor h a E|≤‖J‖ := by
  simpa only [dist_eq_norm,Real.norm_eq_abs,add_sub_cancel_left,NNReal.coe_one,one_mul] using
    (energyRoot_lipschitz Q m hm field factor h a).dist_le_mul (E+J) E

end DilutedSpinGlass.PhysicalRoot

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory

def selectedCount : (l : ℕ) → RootPath Bool l → ℕ
  | 0,_ => 0
  | l+1,(true,b) => selectedCount l b+1
  | l+1,(false,b) => selectedCount l b

def selectRoot {X : Type} : (l : ℕ) → (b : RootPath Bool l) → RootPath X l → RootPath X (selectedCount l b)
  | 0,_,z => z
  | l+1,(true,b),z => (z.1,selectRoot l b z.2)
  | l+1,(false,b),z => selectRoot l b z.2

lemma measurePreserving_selectRoot {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (l : ℕ) (b : RootPath Bool l) :
    MeasurePreserving (selectRoot (X := X) l b) (rootLaw l (fun _ => μ))
      (rootLaw (selectedCount l b) (fun _ => μ)) := by
  induction l with
  | zero => exact MeasurePreserving.id _
  | succ l ih =>
    cases b with | mk a b =>
      cases a
      · change MeasurePreserving (fun z : X×RootPath X l => selectRoot l b z.2)
          (μ.prod (rootLaw l (fun _ => μ))) (rootLaw (selectedCount l b) (fun _ => μ))
        exact (ih b).comp (measurePreserving_snd (μ := μ) (ν := rootLaw l (fun _ => μ)))
      · change MeasurePreserving (fun z : X×RootPath X l => (z.1,selectRoot l b z.2))
          (μ.prod (rootLaw l (fun _ => μ))) (μ.prod (rootLaw (selectedCount l b) (fun _ => μ)))
        exact (MeasurePreserving.id μ).prod (ih b)

lemma integral_selectRoot {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (l : ℕ) (b : RootPath Bool l)
    (F : RootPath X (selectedCount l b) → ℝ) (hF : Measurable F) :
    (∫ z,F (selectRoot l b z) ∂rootLaw l (fun _ => μ))=
      ∫ z,F z ∂rootLaw (selectedCount l b) (fun _ => μ) := by
  have h := measurePreserving_selectRoot μ l b
  rw [← h.map_eq,integral_map h.measurable.aemeasurable hF.aestronglyMeasurable]

end DilutedSpinGlass

end

end OAI
