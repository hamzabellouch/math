import OAI.Probability.FreeIsing.Estimates.CenteredLocalDensity
import OAI.Probability.FreeIsing.Spectral.RadialPowerGrowth
import OAI.Probability.FreeIsing.Spectral.SpectralTransfer
import OAI.Probability.FreeIsing.Trees.Escape
import OAI.Probability.FreeIsing.Trees.WordAction

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem367.TreeLawKoopman

variable {d : ℕ} {A : Type*} [MeasurableSpace A]
variable (μ : Measure (TreeVertex d → A))
variable (hμ : ∀ g : TreeAut d, MeasurePreserving (relabel g) μ μ)

def reflection (c : Fin d) : (TreeVertex d → A) → (TreeVertex d → A) :=
  relabel (prefixTreeAut c)

omit [MeasurableSpace A] in
theorem reflection_involutive (c : Fin d) :
    Function.Involutive (reflection (A := A) c) := by
  intro U
  funext v
  change U (prefixFlip c (prefixFlip c v)) = U v
  rw [prefixFlip_twice]

def average : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  koopmanAverage (fun c : Fin d => reflection c) (fun c => hμ (prefixTreeAut c))

theorem average_selfAdjoint : IsSelfAdjoint (average μ hμ) :=
  koopmanAverage_selfAdjoint _ _ reflection_involutive

def generatorOperator (c : Fin d) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  koopmanL2 (reflection c) (hμ (prefixTreeAut c))

@[simp] theorem generatorOperator_sq (c : Fin d) :
    generatorOperator μ hμ c * generatorOperator μ hμ c = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  exact koopmanL2_involutive _ _ (reflection_involutive c) f

def wordRelabel (w : List (Fin d)) :
    (TreeVertex d → A) → (TreeVertex d → A) :=
  relabel (TreeKoopman.wordAut w).symm

theorem list_koopman_eq (w : List (Fin d)) :
    (w.map (generatorOperator μ hμ)).prod =
      koopmanL2 (wordRelabel w) (hμ (TreeKoopman.wordAut w).symm) := by
  induction w with
  | nil =>
    apply ContinuousLinearMap.ext
    intro f
    change f = Lp.compMeasurePreserving id _ f
    simp
  | cons c w ih =>
    rw [List.map_cons, List.prod_cons, ih]
    apply ContinuousLinearMap.ext
    intro f
    change Lp.compMeasurePreserving (reflection c) _
      (Lp.compMeasurePreserving (wordRelabel w) _ f) =
      Lp.compMeasurePreserving (wordRelabel (c :: w)) _ f
    exact (Lp.compMeasurePreserving_comp_apply f
      (hμ (TreeKoopman.wordAut w).symm) (hμ (prefixTreeAut c))).symm

theorem wordOperator_eq (v : TreeVertex d) :
    RadialWalk.wordOperator (generatorOperator μ hμ) v =
      koopmanL2 (wordRelabel v.1) (hμ (TreeKoopman.wordAut v.1).symm) :=
  list_koopman_eq μ hμ v.1

theorem operatorAverage_eq :
    RadialWalk.operatorAverage (generatorOperator μ hμ) = average μ hμ := by
  simp [RadialWalk.operatorAverage, average, koopmanAverage, generatorOperator]

variable [IsFiniteMeasure μ]

def centeredAverage : centeredL2 μ →L[ℝ] centeredL2 μ :=
  centeredKoopmanAverage (fun c : Fin d => reflection c)
    (fun c => hμ (prefixTreeAut c)) reflection_involutive

theorem centeredAverage_selfAdjoint : IsSelfAdjoint (centeredAverage μ hμ) :=
  centeredKoopmanAverage_selfAdjoint _ _ _

@[simp] theorem centeredAverage_apply_coe (f : centeredL2 μ) :
    (centeredAverage μ hμ f : Lp ℝ 2 μ) = average μ hμ f := rfl

theorem centeredAverage_pow_apply_coe (n : ℕ) (f : centeredL2 μ) :
    ((centeredAverage μ hμ ^ n) f : Lp ℝ 2 μ) = (average μ hμ ^ n) f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', mul_apply_eq_comp, centeredAverage_apply_coe]
    rw [ih]

def LocalCriticalDecay : Prop :=
  ∀ (s : Finset (TreeVertex d)) (f : Lp ℝ 2 μ) (F : (s → A) → ℝ),
    Measurable F → (f =ᵐ[μ] fun U => F (fun i => U i)) →
    (∫ U, f U ∂μ) = 0 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : TreeAut d,
      |inner ℝ f (koopmanL2 (relabel g) (hμ g) f)| ≤
        C * (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ (g.toEquiv TreeEscape.root).1.length

omit [IsFiniteMeasure μ] in

theorem local_average_power_bound (hd : 3 ≤ d) (hlocal : LocalCriticalDecay μ hμ)
    (s : Finset (TreeVertex d)) (f : Lp ℝ 2 μ) (F : (s → A) → ℝ)
    (hF : Measurable F) (hf : f =ᵐ[μ] fun U => F (fun i => U i))
    (hzero : (∫ U, f U ∂μ) = 0) :
    ∃ C : ℝ, ∀ n : ℕ, ‖(average μ hμ ^ n) f‖ ≤ C * RadialWalk.rate d ^ n := by
  obtain ⟨C, hC, hcov⟩ := hlocal s f F hF hf hzero
  have hword (v : TreeVertex d) :
      |inner ℝ f (RadialWalk.wordOperator (generatorOperator μ hμ) v f)| ≤
        C * RadialWalk.treeWeight d v := by
    have hdepth : ((TreeKoopman.wordAut v.1).symm.toEquiv TreeEscape.root).1.length =
        v.1.length := by
      change ((TreeKoopman.wordAut v.1).toEquiv.symm TreeEscape.root).1.length = _
      rw [TreeEscape.symm_root_depth, TreeKoopman.wordAut_root v.1 v.2]
    simpa only [wordOperator_eq, wordRelabel, RadialWalk.treeWeight,
      RadialWalk.weight, hdepth] using hcov (TreeKoopman.wordAut v.1).symm
  have hsym : (RadialWalk.operatorAverage (generatorOperator μ hμ) :
      Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ).IsSymmetric := by
    rw [operatorAverage_eq]
    exact (average_selfAdjoint μ hμ).isSymmetric
  refine ⟨Real.sqrt C, fun n => ?_⟩
  simpa only [operatorAverage_eq] using
    RadialWalk.norm_power_le_of_radial_bound (generatorOperator μ hμ)
      (generatorOperator_sq μ hμ) hsym hd f hC hword n

theorem centeredAverage_norm_le (hd : 3 ≤ d) (hlocal : LocalCriticalDecay μ hμ) :
    ‖centeredAverage μ hμ‖ ≤ 2 * Real.sqrt ((d : ℝ) - 1) / d := by
  apply selfAdjoint_opNorm_le_of_dense_power_bound (centeredAverage μ hμ)
    (centeredAverage_selfAdjoint μ hμ) (RadialWalk.rate_nonneg d)
    (dense_centered_finite_coordinate μ)
  intro f hf
  obtain ⟨s, F, hF, hf⟩ := hf
  obtain ⟨C, hC⟩ := local_average_power_bound μ hμ hd hlocal s (f : Lp ℝ 2 μ)
    F hF hf ((mem_centeredL2_iff _).mp f.property)
  refine ⟨C, fun n => ?_⟩
  change ‖((centeredAverage μ hμ ^ n) f : Lp ℝ 2 μ)‖ ≤ _
  rw [centeredAverage_pow_apply_coe]
  exact hC n

end Problem367.TreeLawKoopman

end

end OAI
