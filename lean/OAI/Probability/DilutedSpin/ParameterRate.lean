import OAI.Probability.DilutedSpin.AnchorExtension
import OAI.Probability.DilutedSpin.FullPalm
import OAI.Probability.DilutedSpin.MeasurableEnergy
import OAI.Probability.DilutedSpin.ParameterConcentration
import OAI.Probability.DilutedSpin.SingletonRoot

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

abbrev rootAlphabet (z : FullRootState Y X I M) :=
  Ω × Row (A := A) (rootArray z.2.2.1 z.2.2.2)

noncomputable def rootTower (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (z : FullRootState Y X I M) : KernelTower (rootAlphabet (Ω := Ω) (A := A) z) L :=
  KernelTower.tilt L (tower (rootArray z.2.2.1 z.2.2.2) L T Q) m
    (logWeight (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) old)

def rootVector (V : FinitePath Ω L → Fin N → ℝ) (z : FullRootState Y X I M) :
    FinitePath (rootAlphabet (Ω := Ω) (A := A) z) L → Fin N → ℝ :=
  fun w => V (physical (rootArray z.2.2.1 z.2.2.2) L w)

noncomputable def rootConditionalEnergy (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (d : ℕ) (V : FinitePath Ω L → Fin N → ℝ) (z : FullRootState Y X I M) : ℝ :=
  KernelTower.prefixEnergyAt L (rootTower T Q m base old z) d (rootVector V z)

variable (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (d : ℕ) (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
lemma measurable_rootConditionalEnergy : Measurable (rootConditionalEnergy T Q m base old d V) := by
  change Measurable (packRoot (fun h k x n y =>
    KernelTower.prefixEnergyAt L
      (KernelTower.tilt L (tower (rootArray n y) L T Q) m (logWeight (base h k x) (rootArray n y) old))
      d (fun w => V (physical (rootArray n y) L w))))
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  exact KernelTower.measurable_prefixEnergyAt_tilt L (tower (rootArray n y) L T Q) m d
    (fun w => (hb k _).add measurable_const) (fun _ _ => measurable_const)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootConditionalEnergy_bound (hd : d < L) (hV : ∀ x i, |V x i| ≤ 1)
    (z : FullRootState Y X I M) : |rootConditionalEnergy T Q m base old d V z| ≤ 2 := by
  rw [rootConditionalEnergy,abs_of_nonneg (KernelTower.prefixEnergyAt_nonneg _ _ _ _)]
  exact KernelTower.prefixEnergyAt_le_two L _ d hd _ (fun x i => hV _ i)

include hb in
lemma integrable_rootConditionalEnergy (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    (hd : d < L) (hV : ∀ x i, |V x i| ≤ 1) :
    Integrable (rootConditionalEnergy T Q m base old d V) μ := by
  apply Integrable.of_bound (measurable_rootConditionalEnergy T Q m base old d V hb).aestronglyMeasurable 2
  exact ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs] using (rootConditionalEnergy_bound T Q m base old d V hd hV z))

include hb in
lemma integrable_rootTreeMean (S : PrescribedTree L) (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    {B : ℝ} (hf : ∀ x, |f x| ≤ B) : Integrable (rootTreeMean S T Q m base old f) μ := by
  apply Integrable.of_bound (measurable_rootTreeMean S T Q m base old f hb).aestronglyMeasurable B
  exact ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs] using (rootTreeMean_bound S T Q m base old f hf z))

end DilutedSpinGlass.HeterogeneousMarks
end

end

section
section
namespace DilutedSpinGlass
open Filter Set
open scoped Topology

lemma tendsto_scoreMargin : Tendsto scoreMargin atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => (N:ℝ)^(-(1:ℝ)/8)) atTop (𝓝 0)
  simpa only [neg_div,Function.comp_def] using
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/8)).comp tendsto_natCast_atTop_atTop

lemma eventually_scoreMargin_interval {a b : ℝ} (ha : -(1:ℝ)/4 < a) (hb : b < 1/4) :
    ∀ᶠ N in atTop, Icc (a-scoreMargin N) (b+scoreMargin N) ⊆ Ioo (-(1:ℝ)/4) (1/4) := by
  have h1 := tendsto_scoreMargin.eventually (gt_mem_nhds (show (0:ℝ) < a+1/4 by linarith))
  have h2 := tendsto_scoreMargin.eventually (gt_mem_nhds (show (0:ℝ) < 1/4-b by linarith))
  filter_upwards [h1,h2] with N h1 h2 u hu
  exact ⟨by linarith [hu.1],by linarith [hu.2]⟩

end DilutedSpinGlass

namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks Set Filter
open scoped NNReal ENNReal BigOperators Topology
variable {X I : ℕ → Type} {Y J : Type}
  [∀ N, MeasurableSpace (X N)] [MeasurableSpace Y]
  [∀ N, Countable (I N)] [∀ N, MeasurableSpace (I N)] [∀ N, MeasurableSingletonClass (I N)]
  [DecidableEq J] {A : (N : ℕ) → I N → Type} [∀ N i, Fintype (A N i)] {L : ℕ}

/-- The actual globally centered dictionary score error, divided by its type
intensity. The dictionary, sites, and mark alphabets are allowed to vary with N. -/
noncomputable def normalizedParameterError
    (μ : (N : ℕ) → Measure (X N)) (ν : (N : ℕ) → Measure (I N)) (ξ : Measure Y)
    (r : ℕ → ℝ≥0) (V : (N : ℕ) → X N → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (Q : (N : ℕ) → (i : I N) → Fin (L+1) → FiniteLaw (A N i)) (m : Fin (L+1) → ℝ)
    (key : (N : ℕ) → I N → J) (a b t w : J → ℝ)
    (D E : (N : ℕ) → (i : I N) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A N i) (L+1) → ℝ)
    (j : J) (N : ℕ) (u : J → ℝ) : ℝ :=
  parameterError (fun _ : Fin N => ξ) (μ N) (ν N) (r N)
    ⟨scoreScale N,Real.rpow_nonneg (Nat.cast_nonneg N) _⟩
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L) (Q N) m
    (fun h k x z => energy (V N) field h k x (KernelTower.terminalState L z))
    (key N) a b t (D N) (E N) j u / (w j*scoreScale N)

variable (μ : (N : ℕ) → Measure (X N)) [∀ N, IsProbabilityMeasure (μ N)]
    (ν : (N : ℕ) → Measure (I N)) [∀ N, IsProbabilityMeasure (ν N)]
    (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (r : ℕ → ℝ≥0) (V : (N : ℕ) → X N → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (Q : (N : ℕ) → (i : I N) → Fin (L+1) → FiniteLaw (A N i)) (m : Fin (L+1) → ℝ)
    (key : (N : ℕ) → I N → J) (a b t w : J → ℝ)
    (D E : (N : ℕ) → (i : I N) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A N i) (L+1) → ℝ)

omit [∀ size, Countable (I size)] [∀ size, MeasurableSingletonClass (I size)]
  [∀ size, IsProbabilityMeasure (μ size)] [∀ size, IsProbabilityMeasure (ν size)]
  [IsProbabilityMeasure ξ] in
lemma normalizedParameterError_nonneg (hw : ∀ j, 0 < w j) (j : J) (N : ℕ) (u : J → ℝ) :
    0 ≤ normalizedParameterError μ ν ξ r V field Q m key a b t w D E j N u :=
  div_nonneg (parameterError_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (mul_nonneg (hw j).le (Real.rpow_nonneg (Nat.cast_nonneg N) _))

 
theorem normalizedParameterError_tendsto
    (hVm : ∀ N σ, Measurable (fun x => V N x σ)) (hhm : Measurable field)
    {C H c R : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hR : 0 ≤ R)
    (hr : ∀ N, (r N:ℝ) ≤ R*N)
    (hV : ∀ N x σ, |V N x σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hm : ∀ l, c ≤ m l)
    (hab : ∀ j, a j < b j) (ha : ∀ j, -(1:ℝ)/4 < a j) (hb : ∀ j, b j < 1/4)
    (ht : ∀ j, |t j| ≤ 1/4) (hw : ∀ j, 0 < w j)
    (hD : ∀ N i x y, |D N i x y| ≤ 1) (hE : ∀ N i x y, |E N i x y| ≤ 1) (j : J) :
    Tendsto (fun N => ∫ u, normalizedParameterError μ ν ξ r V field Q m key a b t w D E j N u
      ∂Measure.infinitePi (fun j => intervalParameterLaw (a j) (b j))) atTop (𝓝 0) := by
  let (j : J) : IsProbabilityMeasure (intervalParameterLaw (a j) (b j)) := intervalParameterLaw_probability (hab j)
  let K := 3*C^2*R+4+2*H^2
  let ell := b j-a j
  let T := ell*(4+4*ell)/c
  have he : 0 < ell := sub_pos.mpr (hab j)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hI : ∀ j, Icc (a j) (b j) ⊆ Icc (-(1:ℝ)/4) (1/4) :=
    fun j u hu => ⟨(ha j).le.trans hu.1,hu.2.trans (hb j).le⟩
  apply squeeze_zero' (Eventually.of_forall (fun N => integral_nonneg
    (normalizedParameterError_nonneg μ ν ξ r V field Q m key a b t w D E hw j N)))
  · filter_upwards [eventually_ge_atTop 1,eventually_scoreMargin_interval (ha j) (hb j)] with N hN hJ
    have hn : (0:ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hbnd := spin_parameter_concentration (μ N) (ν N) ξ (r N)
      ⟨scoreScale N,Real.rpow_nonneg (Nat.cast_nonneg N) _⟩ (V N) field
      (hVm N) hhm hC hc (hV N) hh (Q N) m hm (key N) a b t hab hI ht
      (D N) (E N) (hD N) (hE N) j (Real.rpow_pos_of_pos hn _) hJ
    have hnrm := score_envelope_bound hn hK hT he (hw j)
      (physical_score_variance_linear hN (hr N)) hbnd
    simpa only [normalizedParameterError,integral_div,scoreScale,scoreMargin,K,T,ell] using hnrm
  · exact tendsto_score_rate ((Real.sqrt T/ell+1)/w j) ((4*Real.sqrt K+12/ell)/w j)

end DilutedSpinGlass.PhysicalRoot
end

end

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {L n : ℕ}

/-- The old reservoir and the new insertion factor are distinct arguments.
Keeping `old` fixed is essential when extracting a single analytic function
from the entire countable dictionary of insertion parameter values. -/
noncomputable def externalTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (new numerator : FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) : ℝ :=
  (S.sampleLaw (KernelTower.tilt L
    (KernelTower.prod L (KernelTower.tilt L (tower roots L T Q) m
      (logWeight base roots old)) (markPrior L (Q i))) m
    (fun y => Real.log (new (physical roots L (KernelTower.pathFst L y))
      (KernelTower.pathSnd L y))))).expect (fun x =>
        f (fun b => physical roots L (KernelTower.pathFst L (S.pathAt b x))) *
          (numerator (physical roots L (KernelTower.pathFst L (S.pathAt a x)))
            (KernelTower.pathSnd L (S.pathAt a x)) /
            new (physical roots L (KernelTower.pathFst L (S.pathAt a x)))
              (KernelTower.pathSnd L (S.pathAt a x))))

lemma inserted_eq_external (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) :
    insertedTreeScore S a T Q m base roots i factor numerator f =
      externalTreeScore S a T Q m base roots i factor (factor i) (numerator i) f := rfl

/-- Exact link to the proved all-order anchor Taylor calculus, for arbitrary
old disorder and mark alphabets; the old kernels do not vary with `new`. -/
lemma external_eq_anchorInsertion (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (new numerator : FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) :
    externalTreeScore S a T Q (fun j => m j.succ) base roots i old new numerator f =
      PrescribedTree.anchorInsertion S
        (KernelTower.prod L (KernelTower.tilt L (tower roots L T Q) (fun j => m j.succ)
          (logWeight base roots old)) (markPrior L (Q i))) m a
        (fun x => f (fun b => physical roots L (KernelTower.pathFst L (S.pathAt b x))) *
          numerator (physical roots L (KernelTower.pathFst L (S.pathAt a x)))
            (KernelTower.pathSnd L (S.pathAt a x)))
        (fun y => new (physical roots L (KernelTower.pathFst L y)) (KernelTower.pathSnd L y)) := by
  apply FiniteLaw.expect_congr
  intro x
  exact (mul_div_assoc _ _ _).symm

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
