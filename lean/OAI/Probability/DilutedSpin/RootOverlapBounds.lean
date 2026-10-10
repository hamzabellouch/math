import OAI.Probability.DilutedSpin.MixedDeviation
import OAI.Probability.DilutedSpin.RegularNodeEstimates
import OAI.Probability.DilutedSpin.RootMarkerEstimate

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PrescribedTree
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {B : I → Type} [∀ i, Fintype (B i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

variable (S : PrescribedTree L)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (B i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (B i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]
    (hV : ∀ y i, |V y i| ≤ 1)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma root_overlapMoment_eq [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] (j : ℕ) (z : FullRootState Y X I M) :
    (S.sampleLaw (rootTower T Q m base old z)).expect (fun w => (treeOverlap S (rootVector V z) w)^j) =
    rootTreeMean S T Q m base old (fun x => (spatialProduct (fun _ : S.Leaf => V) x)^j) z := by
  unfold rootTreeMean packRoot
  apply FiniteLaw.expect_congr
  intro w
  rw [treeOverlap_eq_spatialProduct]
  rfl

include hb hV in
lemma integrable_rootOverlapMoment (j : ℕ) : Integrable (fun z : FullRootState Y X I M =>
    (S.sampleLaw (rootTower T Q m base old z)).expect (fun w => (treeOverlap S (rootVector V z) w)^j)) μ := by
  simp_rw [root_overlapMoment_eq]
  apply integrable_rootTreeMean T Q m base old hb _ _ μ (B := 1)
  intro x
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (spatialProduct_bound _ (fun _ => hV) x)

include hb hV in
lemma root_overlapVariance_nonneg :
    0 ≤ overlapVariance μ (rootAlphabet (Ω := Ω) (A := B)) S (rootTower T Q m base old) (rootVector V) := by
  apply FiniteLaw.mixedVariance_nonneg
  · simpa using integrable_rootOverlapMoment S T Q m base old V hb μ hV 1
  · exact integrable_rootOverlapMoment S T Q m base old V hb μ hV 2

include hb hV in
lemma root_overlapVariance_le_one :
    overlapVariance μ (rootAlphabet (Ω := Ω) (A := B)) S (rootTower T Q m base old) (rootVector V)≤1 := by
  apply FiniteLaw.mixedVariance_le_one
  · exact integrable_rootOverlapMoment S T Q m base old V hb μ hV 2
  · intro z w
    rw [treeOverlap_eq_spatialProduct]
    exact spatialProduct_bound _ (fun _ y i => hV _ i) _

end DilutedSpinGlass.HeterogeneousMarks

end

section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory _root_.OAI.MeasureTheory
variable {Z : Type} [MeasurableSpace Z]

lemma mixedDeviation_distance {μ ν : Measure Z} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {d : ℝ} (hd : BoundedDistance μ ν d)
    (Ω : Z → Type) [∀ z, Fintype (Ω z)] (P : (z : Z) → FiniteLaw (Ω z))
    (F : (z : Z) → Ω z → ℝ) (hF : ∀ z w, |F z w|≤1)
    (hm : Measurable (fun z => (P z).expect (F z)))
    (ha : ∀ c : ℝ, Measurable (fun z => (P z).expect (fun w => |F z w-c|))) :
    |mixedDeviation μ Ω P F-mixedDeviation ν Ω P F|≤3*d := by
  let c := ∫ z, (P z).expect (F z) ∂μ
  let e := ∫ z, (P z).expect (F z) ∂ν
  let G (a : ℝ) (z : Z) := (P z).expect (fun w => |F z w-a|)
  have hc : |c|≤1 := abs_integral_le_bound (fun z => (P z).abs_expect_le (hF z))
  have he : |e|≤1 := abs_integral_le_bound (fun z => (P z).abs_expect_le (hF z))
  have hce : |c-e|≤d := by simpa only [one_mul] using hd _ hm 1 (fun z => (P z).abs_expect_le (hF z))
  have hG (a : ℝ) (z : Z) : |G a z|≤1+|a| := by
    apply (P z).abs_expect_le
    intro w
    rw [abs_abs]
    exact (abs_sub (F z w) a).trans (by linarith [hF z w])
  have hi (a : ℝ) (κ : Measure Z) [IsProbabilityMeasure κ] : Integrable (G a) κ :=
    (bounded_memLp (ha a) (hG a) 1).integrable le_rfl
  have hGc (z : Z) : |G c z|≤2 := (hG c z).trans (by linarith)
  have hdist : |(∫ z, G c z ∂μ)-(∫ z, G c z ∂ν)|≤2*d := hd _ (ha c) 2 hGc
  have hchange : |(∫ z, G c z ∂ν)-(∫ z, G e z ∂ν)|≤|c-e| := by
    rw [← integral_sub (hi c ν) (hi e ν)]
    apply abs_integral_le_bound
    intro z
    change |(P z).expect (fun w => |F z w-c|)-(P z).expect (fun w => |F z w-e|)|≤_
    rw [← expect_sub]
    apply (P z).abs_expect_le
    intro w
    calc
      _ ≤ |(F z w-c)-(F z w-e)| := abs_abs_sub_abs_le_abs_sub _ _
      _ = |c-e| := by rw [show (F z w-c)-(F z w-e)=e-c by ring,abs_sub_comm]
  change |(∫ z, G c z ∂μ)-(∫ z, G e z ∂ν)|≤_
  have ht := (abs_sub_le (∫ z, G c z ∂μ) (∫ z, G c z ∂ν) (∫ z, G e z ∂ν)).trans
    (add_le_add hdist (hchange.trans hce))
  linarith

end DilutedSpinGlass.FiniteLaw

end

end OAI
