import OAI.Probability.DilutedSpin.FullSelectedRawConcentration
import OAI.Probability.DilutedSpin.FullThermalAverage

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

noncomputable def fullSelectedDeviation
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ) (z : FullRootState Y X I M) (u center : ℝ) : ℝ :=
  let roots := rootArray z.2.2.1 z.2.2.2
  let f := KernelTower.perturbLog (otherLog (base z.1 z.2.1.1 z.2.1.2) roots sel fixed)
    (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t u
  let g := KernelTower.perturbScore (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t u
  (KernelTower.law L (KernelTower.tilt L (tower roots L T Q) m f)).expect (fun y => |g y-center|)

variable (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedDeviation_nonneg (z : FullRootState Y X I M) (u center : ℝ) :
    0 ≤ fullSelectedDeviation T Q m base sel fixed D E t z u center :=
  FiniteLaw.expect_nonneg _ (fun _ => abs_nonneg _)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedDeviation_split (z : FullRootState Y X I M) (u center : ℝ) :
    fullSelectedDeviation T Q m base sel fixed D E t z u center ≤
      fullSelectedThermal T Q m base sel fixed D E t z u+
        |fullSelectedRawScore T Q m base sel fixed D E t z u-center| := by
  let roots := rootArray z.2.2.1 z.2.2.2
  let f := KernelTower.perturbLog (otherLog (base z.1 z.2.1.1 z.2.1.2) roots sel fixed)
    (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t u
  let g := KernelTower.perturbScore (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t u
  let P := KernelTower.law L (KernelTower.tilt L (tower roots L T Q) m f)
  have hh := P.expect_mono (fun y => abs_sub_le (g y) (P.expect g) center)
  rw [FiniteLaw.expect_add,FiniteLaw.expect_const] at hh
  change P.expect (fun y => |g y-center|) ≤
    P.expect (fun y => |g y-P.expect g|)+|fullSelectedRawScore T Q m base sel fixed D E t z u-center|
  have hG : fullSelectedRawScore T Q m base sel fixed D E t z u = P.expect g := by
    dsimp [fullSelectedRawScore,packRoot,selectedScore,P,f,g,roots]
    rw [selected_perturbLog_eq]
  rw [hG]
  exact hh

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedDeviation_bound
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    {u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (z : FullRootState Y X I M) (center : ℝ) :
    fullSelectedDeviation T Q m base sel fixed D E t z u center ≤ 2*(z.2.2.1:ℝ)+|center| := by
  apply (FiniteLaw.expect_mono _ (fun y => (abs_sub _ _).trans
    (add_le_add (KernelTower.perturbScore_bound _ _
      (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht hu y) le_rfl))).trans_eq
  exact FiniteLaw.expect_const _ _

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedRawScore_bound
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    {u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (z : FullRootState Y X I M) :
    |fullSelectedRawScore T Q m base sel fixed D E t z u| ≤ 2*(z.2.2.1:ℝ) := by
  apply FiniteLaw.abs_expect_le
  exact KernelTower.perturbScore_bound _ _ (selectedCoefficient_bound _ sel D hD)
    (selectedCoefficient_bound _ sel E hE) ht hu

theorem measurable_fullSelectedRawScore
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fun z : FullRootState Y X I M × ℝ => fullSelectedRawScore T Q m base sel fixed D E t z.1 z.2) := by
  simp_rw [fullSelectedRawScore_eq]
  exact (measurable_fullSelectedScore T Q m base sel fixed D E t hb).sub
    ((measurable_const.mul measurable_snd).mul ((measurable_sigmaUncurry (f := fun n (_ : RootPath I n) => (n:ℝ)) (fun _ => measurable_const)).comp measurable_fst.snd.snd))

theorem measurable_fullSelectedDeviation
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {center : ℝ → ℝ} (hc : Measurable center) :
    Measurable (fun z : FullRootState Y X I M × ℝ => fullSelectedDeviation T Q m base sel fixed D E t z.1 z.2 (center z.2)) := by
  apply measurable_packRoot_param (F := fun h k x n y u =>
    fullSelectedDeviation T Q m base sel fixed D E t (h,⟨k,x⟩,⟨n,y⟩) u (center u))
  intro k n
  have hh : Measurable (fun z : ((RootPath Y M × RootPath X k) × ℝ) × RootPath I n =>
      fullSelectedDeviation T Q m base sel fixed D E t (z.1.1.1,⟨k,z.1.1.2⟩,⟨n,z.2⟩) z.1.2 (center z.1.2)) := by
    apply measurable_from_prod_countable_left
    intro y
    dsimp only [fullSelectedDeviation]
    apply KernelTower.measurable_path_expect L (tower (rootArray n y) L T Q) m
      (f := fun z : (RootPath Y M × RootPath X k) × ℝ =>
        KernelTower.perturbLog (otherLog (base z.1.1 k z.1.2) (rootArray n y) sel fixed)
          (selectedCoefficient (rootArray n y) sel D) (selectedCoefficient (rootArray n y) sel E) t z.2)
      (g := fun z : (RootPath Y M × RootPath X k) × ℝ => fun w =>
        |KernelTower.perturbScore (selectedCoefficient (rootArray n y) sel D)
          (selectedCoefficient (rootArray n y) sel E) t z.2 w-center z.2|)
    · apply KernelTower.measurable_perturbLog
      · intro w
        exact ((hb k (physical (rootArray n y) L w)).comp measurable_fst).add measurable_const
      · exact fun _ _ => measurable_const
      · exact fun _ _ => measurable_const
      · exact measurable_const
      · exact measurable_snd
    · intro w
      exact ((KernelTower.measurable_perturbScore
        (D := fun _ : (RootPath Y M × RootPath X k) × ℝ => selectedCoefficient (rootArray n y) sel D)
        (E := fun _ : (RootPath Y M × RootPath X k) × ℝ => selectedCoefficient (rootArray n y) sel E)
        (t := fun _ : (RootPath Y M × RootPath X k) × ℝ => t) (u := fun z => z.2)
        (fun _ _ => measurable_const) (fun _ _ => measurable_const) measurable_const measurable_snd w).sub
          (hc.comp measurable_snd)).abs
  exact hh.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
