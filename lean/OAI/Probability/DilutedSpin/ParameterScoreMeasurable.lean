import OAI.Probability.DilutedSpin.GlobalSelectedError

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y U : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U] {L M : ℕ}

omit [Fintype Ω] [∀ index, Fintype (A index)] [Countable I] [MeasurableSpace I]
  [MeasurableSingletonClass I] in
lemma measurable_otherLog_family (base : U → FinitePath Ω L → ℝ)
    (hb : ∀ y, Measurable (fun u => base u y)) {n : ℕ} (roots : Fin n → I)
    (sel : I → Bool) (fixed : U → (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hf : ∀ i x y, Measurable (fun u => fixed u i x y))
    (y : FinitePath (Ω × Row (A := A) roots) L) :
    Measurable (fun u => otherLog (base u) roots sel (fixed u) y) := by
  apply (hb _).add
  apply Finset.measurable_sum
  intro j _
  by_cases h : sel (roots j) = true
  · simp only [h,ite_true]
    exact measurable_const
  · simp only [h]
    exact (hf _ _ _).log

variable (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma measurable_selectedScore_family
    (base : U → FinitePath Ω L → ℝ) {n : ℕ} (roots : Fin n → I)
    (sel : I → Bool) (fixed : U → (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) (t : ℝ) (u : U → ℝ)
    (hb : ∀ y, Measurable (fun z => base z y))
    (hf : ∀ i x y, Measurable (fun z => fixed z i x y)) (hu : Measurable u) :
    Measurable (fun z => selectedScore T Q m (base z) roots sel (fixed z) D E t (u z)) := by
  have hh := KernelTower.measurable_correctedPerturbScore (tower roots L T Q) m
    (base := fun z : U => otherLog (base z) roots sel (fixed z))
    (D := fun _ : U => selectedCoefficient roots sel D)
    (E := fun _ : U => selectedCoefficient roots sel E)
    (t := fun _ : U => t) (u := u)
    (measurable_otherLog_family base hb roots sel fixed hf)
    (fun _ _ => measurable_const) (fun _ _ => measurable_const) measurable_const hu
  have hh' := hh.sub ((measurable_const : Measurable (fun _ : U => (4:ℝ)*n)).mul hu)
  convert hh' using 1
  funext z
  simp only [Pi.sub_apply,Pi.mul_apply,corrected_score_eq,add_sub_cancel_right]

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma measurable_selectedDeviation_family
    (base : U → FinitePath Ω L → ℝ) {n : ℕ} (roots : Fin n → I)
    (sel : I → Bool) (fixed : U → (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) (t : ℝ) (u center : U → ℝ)
    (hb : ∀ y, Measurable (fun z => base z y))
    (hf : ∀ i x y, Measurable (fun z => fixed z i x y)) (hu : Measurable u) (hc : Measurable center) :
    Measurable (fun z =>
      (KernelTower.law L (KernelTower.tilt L (tower roots L T Q) m
        (KernelTower.perturbLog (otherLog (base z) roots sel (fixed z))
          (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t (u z)))).expect
            (fun w => |KernelTower.perturbScore (selectedCoefficient roots sel D)
              (selectedCoefficient roots sel E) t (u z) w-center z|)) := by
  apply KernelTower.measurable_path_expect L (tower roots L T Q) m
    (f := fun z : U => KernelTower.perturbLog (otherLog (base z) roots sel (fixed z))
      (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t (u z))
    (g := fun z : U => fun w => |KernelTower.perturbScore (selectedCoefficient roots sel D)
      (selectedCoefficient roots sel E) t (u z) w-center z|)
  · exact KernelTower.measurable_perturbLog (measurable_otherLog_family base hb roots sel fixed hf)
      (fun _ _ => measurable_const) (fun _ _ => measurable_const) measurable_const hu
  · intro w
    exact ((KernelTower.measurable_perturbScore
      (D := fun _ : U => selectedCoefficient roots sel D)
      (E := fun _ : U => selectedCoefficient roots sel E)
      (t := fun _ : U => t) (u := u)
      (fun _ _ => measurable_const) (fun _ _ => measurable_const) measurable_const hu w).sub hc).abs

variable
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed : U → (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) (t : ℝ)
    (u : U → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hf : ∀ i x y, Measurable (fun z => fixed z i x y)) (hu : Measurable u)
include hb hf hu

lemma measurable_fullSelectedRawScore_family :
    Measurable (fun z : FullRootState Y X I M × U =>
      fullSelectedRawScore T Q m base sel (fixed z.2) D E t z.1 (u z.2)) := by
  unfold fullSelectedRawScore
  apply measurable_packRoot_param (F := fun h k x n y v =>
    selectedScore T Q m (base h k x) (rootArray n y) sel (fixed v) D E t (u v))
  intro k n
  have hh : Measurable (fun z : ((RootPath Y M × RootPath X k) × U) × RootPath I n =>
      selectedScore T Q m (base z.1.1.1 k z.1.1.2) (rootArray n z.2) sel (fixed z.1.2) D E t (u z.1.2)) := by
    apply measurable_from_prod_countable_left
    intro y
    exact measurable_selectedScore_family T Q m
      (fun z : (RootPath Y M × RootPath X k) × U => base z.1.1 k z.1.2)
      (rootArray n y) sel (fun z => fixed z.2) D E t (fun z => u z.2)
      (fun w => (hb k w).comp measurable_fst)
      (fun i x a => (hf i x a).comp measurable_snd) (hu.comp measurable_snd)
  exact hh.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

lemma measurable_fullSelectedDeviation_family (center : U → ℝ) (hc : Measurable center) :
    Measurable (fun z : FullRootState Y X I M × U =>
      fullSelectedDeviation T Q m base sel (fixed z.2) D E t z.1 (u z.2) (center z.2)) := by
  apply measurable_packRoot_param (F := fun h k x n y v =>
    fullSelectedDeviation T Q m base sel (fixed v) D E t (h,⟨k,x⟩,⟨n,y⟩) (u v) (center v))
  intro k n
  have hh : Measurable (fun z : ((RootPath Y M × RootPath X k) × U) × RootPath I n =>
      fullSelectedDeviation T Q m base sel (fixed z.1.2) D E t
        (z.1.1.1,⟨k,z.1.1.2⟩,⟨n,z.2⟩) (u z.1.2) (center z.1.2)) := by
    apply measurable_from_prod_countable_left
    intro y
    exact measurable_selectedDeviation_family T Q m
      (fun z : (RootPath Y M × RootPath X k) × U => base z.1.1 k z.1.2)
      (rootArray n y) sel (fun z => fixed z.2) D E t (fun z => u z.2) (fun z => center z.2)
      (fun w => (hb k w).comp measurable_fst)
      (fun i x a => (hf i x a).comp measurable_snd) (hu.comp measurable_snd) (hc.comp measurable_snd)
  exact hh.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

lemma measurable_fullSelectedError_family
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0) :
    Measurable (fun z : U => fullSelectedError ξ μ ν r s T Q m base sel (fixed z) D E t (u z)) := by
  exact (measurable_fullSelectedDeviation_family T Q m base sel fixed D E t u hb hf hu _
    (measurable_fullSelectedRawScore_family T Q m base sel fixed D E t u hb hf hu).stronglyMeasurable.integral_prod_left'.measurable).stronglyMeasurable.integral_prod_left'.measurable

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
