import OAI.Probability.DilutedSpin.MeasurableEncoding
import OAI.Probability.DilutedSpin.PhysicalEncodingInterior

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
local instance rootEncodingMeasurableSpace (space : TopCat) : MeasurableSpace space := borel space
local instance rootEncodingBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

lemma measurable_packRoot_into {X I Y W : Type} [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSpace Y] [MeasurableSpace W] {M : ℕ}
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → W}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n =>
      F z.1.1 k z.1.2 n z.2)) :
    Measurable (fun z : FullRootState Y X I M => F z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2) := by
  have hn (k : ℕ) : Measurable (fun z : (RootPath Y M × RootPath X k) × Sigma (RootPath I) =>
      F z.1.1 k z.1.2 z.2.1 z.2.2) := measurable_prodSigma
        (f := fun (z : RootPath Y M × RootPath X k) n y => F z.1 k z.2 n y) (hF k)
  have hk : Measurable (fun z : (RootPath Y M × Sigma (RootPath I)) × Sigma (RootPath X) =>
      F z.1.1 z.2.1 z.2.2 z.1.2.1 z.1.2.2) :=
    measurable_prodSigma (f := fun (z : RootPath Y M × Sigma (RootPath I)) k x =>
      F z.1 k x z.2.1 z.2.2) (fun k =>
        (hn k).comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd))
  exact hk.comp ((measurable_fst.prodMk measurable_snd.snd).prodMk measurable_snd.fst)

namespace HeterogeneousMarks
open ConcreteReservoir PrescribedTree KernelTower
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

variable (T : KernelTower Ω (L+1)) (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (L+1) → ℝ)
    (old : (i : I) → FinitePath Ω (L+1) → FinitePath (A i) (L+1) → ℝ)
    (V : FinitePath Ω (L+1) → Site N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

noncomputable def rootEncoding (z : FullRootState Y X I M) (i : Site N) : Hierarchy L :=
  encode L (rootTower T Q m base old z) (fun y => rootVector V z y i)

include hb in
lemma measurable_rootEncoding (i : Site N) : Measurable (fun z => rootEncoding T Q m base old V z i) := by
  apply measurable_packRoot_into (F := fun h k x n y =>
    encode L (tilt (L+1) (tower (rootArray n y) (L+1) T Q) m
      (logWeight (base h k x) (rootArray n y) old))
      (fun w => V (physical (rootArray n y) (L+1) w) i))
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  exact measurable_encode_tilt L (tower (rootArray n y) (L+1) T Q) m
    (fun w => (hb k _).add measurable_const) (fun _ => measurable_const)

include hb in
lemma measurable_rootEncoding_joint : Measurable (fun z : FullRootState Y X I M × Site N =>
    rootEncoding T Q m base old V z.1 z.2) := by
  apply measurable_from_prod_countable_left
  exact measurable_rootEncoding T Q m base old V hb

noncomputable def rootEncodingLaw (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ] :
    Hierarchy (L+1) :=
  ⟨Measure.map
    (fun z : FullRootState Y X I M × Site N => rootEncoding T Q m base old V z.1 z.2)
    (μ.prod (siteLaw N)),
    (Measure.isProbabilityMeasure_map_iff
      (measurable_rootEncoding_joint T Q m base old V hb).aemeasurable).mpr inferInstance⟩

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootEncoding_moment (z : FullRootState Y X I M) (i : Site N)
    (hV : TerminalInterior L (rootTower T Q m base old z) (fun y => rootVector V z y i))
    (S : PrescribedTree (L+1)) :
    labelMoment L S (rootEncoding T Q m base old V z i) =
      (sampleLaw S (rootTower T Q m base old z)).expect
        (leafProduct S (fun y => rootVector V z y i)) :=
  (encode_moment L _ _ hV S).trans (treeMean_eq_expect S _ _)

lemma rootEncodingLaw_moment (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]
    (hV : ∀ z i, TerminalInterior L (rootTower T Q m base old z) (fun y => rootVector V z y i))
    (S : PrescribedTree (L+1)) :
    (∫ η, labelMoment L S η ∂(rootEncodingLaw T Q m base old V hb μ).toMeasure) =
      ∫ z, (sampleLaw S (rootTower T Q m base old z)).expect
        (treeOverlap S (rootVector V z)) ∂μ := by
  have hc := (labelMoment_continuous_bound L S).1
  have hi : Integrable (fun z : FullRootState Y X I M × Site N =>
      labelMoment L S (rootEncoding T Q m base old V z.1 z.2)) (μ.prod (siteLaw N)) := by
    apply Integrable.of_bound (hc.measurable.comp
      (measurable_rootEncoding_joint T Q m base old V hb)).aestronglyMeasurable 1
    exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Function.comp_apply] using
      (labelMoment_continuous_bound L S).2 (rootEncoding T Q m base old V z.1 z.2))
  change (∫ η, labelMoment L S η ∂Measure.map
    (fun z : FullRootState Y X I M × Site N => rootEncoding T Q m base old V z.1 z.2)
    (μ.prod (siteLaw N))) = _
  rw [integral_map (measurable_rootEncoding_joint T Q m base old V hb).aemeasurable
      hc.aestronglyMeasurable,integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [integral_siteLaw]
  simp_rw [rootEncoding_moment T Q m base old V _ _ (hV _ _) S]
  change (∑ i, (sampleLaw S (rootTower T Q m base old z)).expect
    (leafProduct S (fun y => rootVector V z y i)))/(max N 1 : ℕ) = _
  unfold treeOverlap
  rw [FiniteLaw.expect_div,FiniteLaw.expect_fintype_sum]

end HeterogeneousMarks
end DilutedSpinGlass

end

end OAI
