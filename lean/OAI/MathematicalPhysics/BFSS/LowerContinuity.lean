import Mathlib
import OAI.MathematicalPhysics.BFSS.FormCompactness

namespace OAI

/-! Weighted moment and closed normal-form lower semicontinuity. -/

namespace BFSSNormalAnalysis
noncomputable section
open MeasureTheory Filter Topology
variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {μ : Measure X}

theorem weighted_moment_norm_lsc (f : ℕ → Lp F 2 μ) (u : Lp F 2 μ)
    (w : X → ℝ) (hw : AEStronglyMeasurable w μ) (B : ℝ)
    (hf : Tendsto f atTop (𝓝 u))
    (hm : ∀ n, MemLp (fun x => w x • f n x) 2 μ)
    (hB : Tendsto (fun n => ‖(hm n).toLp (fun x => w x • f n x)‖) atTop (𝓝 B)) :
    ∃ hu : MemLp (fun x => w x • u x) 2 μ,
      ‖hu.toLp (fun x => w x • u x)‖ ≤ B := by
  have hB0 : 0 ≤ B := ge_of_tendsto' hB (fun n => norm_nonneg _)
  obtain ⟨σ,hσ,ha⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
  have he (n : ℕ) : eLpNorm (fun x => w x • f (σ n) x) 2 μ =
      ENNReal.ofReal ‖(hm (σ n)).toLp (fun x => w x • f (σ n) x)‖ := by
    rw [Lp.norm_toLp,ENNReal.ofReal_toReal (hm (σ n)).eLpNorm_ne_top]
  have ht : Tendsto (fun n => eLpNorm (fun x => w x • f (σ n) x) 2 μ)
      atTop (𝓝 (ENNReal.ofReal B)) := by
    simp_rw [he]
    exact ENNReal.continuous_ofReal.tendsto B |>.comp (hB.comp hσ.tendsto_atTop)
  have hlim : eLpNorm (fun x => w x • u x) 2 μ ≤ ENNReal.ofReal B := by
    have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2)
      (fun n => (hm (σ n)).aestronglyMeasurable) (fun x => w x • u x)
      (hw.smul (Lp.memLp u).aestronglyMeasurable)
      (ha.mono (fun x hx => tendsto_const_nhds.smul hx))
    rwa [ht.liminf_eq] at hfatou
  have hu : MemLp (fun x => w x • u x) 2 μ :=
    hlim.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hu,?_⟩
  rw [Lp.norm_toLp]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlim).trans_eq (ENNReal.toReal_ofReal hB0)

lemma weighted_moment_sq_lsc (f : ℕ → Lp F 2 μ) (u : Lp F 2 μ)
    (w : X → ℝ) (hw : AEStronglyMeasurable w μ) (B : ℝ)
    (hf : Tendsto f atTop (𝓝 u))
    (hm : ∀ n, MemLp (fun x => w x • f n x) 2 μ)
    (hB : Tendsto (fun n => ‖(hm n).toLp (fun x => w x • f n x)‖^2) atTop (𝓝 B)) :
    ∃ hu : MemLp (fun x => w x • u x) 2 μ,
      ‖hu.toLp (fun x => w x • u x)‖^2 ≤ B := by
  have hB0 : 0 ≤ B := ge_of_tendsto' hB (fun n => sq_nonneg _)
  have hn : Tendsto (fun n => ‖(hm n).toLp (fun x => w x • f n x)‖) atTop (𝓝 (Real.sqrt B)) := by
    simpa only [Real.sqrt_sq_eq_abs,abs_norm] using hB.sqrt
  obtain ⟨hu,h⟩ := weighted_moment_norm_lsc f u w hw (Real.sqrt B) hf hm hn
  refine ⟨hu,?_⟩
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (Real.sq_sqrt hB0)
end
end BFSSNormalAnalysis
namespace BFSSSliceSobolev
noncomputable section
open MeasureTheory Set Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace.SeparableSpace F]
variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [IsSeparable μ]
variable {ι : Type*} [Fintype ι] (e : ι → E)

omit [FiniteDimensional ℝ E] in
lemma closedGraph_extract_sequence (f : ℕ → Lp F 2 μ)
    (v : ℕ → Gradient (F := F) μ (ι := ι)) (u : Lp F 2 μ) (B : ℝ)
    (hd : ∀ n, (f n,v n) ∈ closedGraph μ e)
    (hf : Tendsto f atTop (𝓝 u)) (hB : ∀ n, ‖v n‖ ≤ B) :
    ∃ (z : Gradient (F := F) μ (ι := ι)) (σ : ℕ → ℕ), StrictMono σ ∧
      (u,z) ∈ closedGraph μ e ∧
      ∀ y : Gradient (F := F) μ (ι := ι),
        Tendsto (fun n => inner ℝ (v (σ n)) y) atTop (𝓝 (inner ℝ z y)) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp F 2 μ) := Lp.SecondCountableTopology
  let : SecondCountableTopology (Gradient (F := F) μ (ι := ι)) :=
    PiLp.secondCountableTopology 2 (fun _ : ι => Lp F 2 μ)
  obtain ⟨z,σ,hσ,_,hz⟩ := BFSSNormalAnalysis.bounded_weak_subsequence v B hB
  refine ⟨z,σ,hσ,?_,hz⟩
  exact BFSSNormalAnalysis.strong_weak_mem_closed_convex
    (closedGraph (F := F) μ e : Set _) (closedGraph (F := F) μ e).convex
    (graph (F := F) μ e).isClosed_topologicalClosure
    (fun n => f (σ n)) (fun n => v (σ n)) u z
    (fun n => hd (σ n)) (hf.comp hσ.tendsto_atTop) hz

omit [FiniteDimensional ℝ E] in
theorem weighted_closed_form_lsc (w : E → ℝ) (hw : AEStronglyMeasurable w μ)
    (A : F →L[ℝ] F) (f : ℕ → Lp F 2 μ)
    (v : ℕ → Gradient (F := F) μ (ι := ι)) (u : Lp F 2 μ) (B C L : ℝ)
    (hd : ∀ n, (f n,v n) ∈ closedGraph μ e)
    (hm : ∀ n, MemLp (fun x => w x • f n x) 2 μ)
    (hf : Tendsto f atTop (𝓝 u)) (hB : ∀ n, ‖v n‖ ≤ B)
    (hC : ∀ n, ‖(hm n).toLp (fun x => w x • f n x)‖ ≤ C)
    (hL : Tendsto (fun n => (1/2 : ℝ)*‖v n‖^2+
      ‖(hm n).toLp (fun x => w x • f n x)‖^2+inner ℝ (f n) (A.compLp (f n))) atTop (𝓝 L)) :
    ∃ z : Gradient (F := F) μ (ι := ι), ∃ hu : MemLp (fun x => w x • u x) 2 μ,
      (u,z) ∈ closedGraph μ e ∧
      (1/2 : ℝ)*‖z‖^2+‖hu.toLp (fun x => w x • u x)‖^2+inner ℝ u (A.compLp u) ≤ L := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp F 2 μ) := Lp.SecondCountableTopology
  let : SecondCountableTopology (Gradient (F := F) μ (ι := ι)) :=
    PiLp.secondCountableTopology 2 (fun _ : ι => Lp F 2 μ)
  let a : ℕ → Fin 2 → ℝ := fun n => ![‖v n‖^2,‖(hm n).toLp (fun x => w x • f n x)‖^2]
  have ha (n : ℕ) (i : Fin 2) : 0 ≤ a n i := by
    fin_cases i <;> exact sq_nonneg _
  have hb (n : ℕ) : ∑ i, a n i ≤ B^2+C^2 := by
    simp only [Fin.sum_univ_two,a,Matrix.cons_val_zero,Matrix.cons_val_one]
    exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hB n) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (hC n) 2)
  obtain ⟨b,σ,hσ,hb⟩ := BFSSNormalAnalysis.finite_nonnegative_energy_subsequence a _ ha hb
  have ht0 : Tendsto (fun n => ‖v (σ n)‖^2) atTop (𝓝 (b 0)) := hb 0
  have ht1 : Tendsto (fun n => ‖(hm (σ n)).toLp (fun x => w x • f (σ n) x)‖^2)
      atTop (𝓝 (b 1)) := hb 1
  obtain ⟨z,τ,hτ,hz,hwk⟩ := closedGraph_extract_sequence μ e
    (fun n => f (σ n)) (fun n => v (σ n)) u B (fun n => hd (σ n))
    (hf.comp hσ.tendsto_atTop) (fun n => hB (σ n))
  have hkin : ‖z‖^2 ≤ b 0 := BFSSNormalAnalysis.weak_norm_sq_le_limit
    (fun n => v (σ (τ n))) z (b 0) hwk (ht0.comp hτ.tendsto_atTop)
  obtain ⟨hu,hpot⟩ := BFSSNormalAnalysis.weighted_moment_sq_lsc
    (fun n => f (σ n)) u w hw (b 1) (hf.comp hσ.tendsto_atTop)
    (fun n => hm (σ n)) ht1
  have hferm : Tendsto (fun n => inner ℝ (f (σ n)) (A.compLp (f (σ n))))
      atTop (𝓝 (inner ℝ u (A.compLp u))) :=
    (hf.comp hσ.tendsto_atTop).inner
      ((A.compLpL 2 μ).continuous.tendsto u |>.comp (hf.comp hσ.tendsto_atTop))
  have heq : (1/2 : ℝ)*b 0+b 1+inner ℝ u (A.compLp u) = L :=
    tendsto_nhds_unique ((ht0.const_mul (1/2 : ℝ)).add ht1 |>.add hferm)
      (hL.comp hσ.tendsto_atTop)
  refine ⟨z,hu,hz,?_⟩
  linarith only [hkin,hpot,heq]
end
end BFSSSliceSobolev
namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] normalSlice gaugeAction coreToL2 deformedFermionField
local instance lowerContinuityFermionNormedAddCommGroup :
    NormedAddCommGroup (Fermion N →L[ℝ] Fermion N) := inferInstance
local instance lowerContinuityFermionNormedSpace :
    NormedSpace ℝ (Fermion N →L[ℝ] Fermion N) := inferInstance

theorem normalForm_lsc (q : Boson N)
    (f : ℕ → Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)))
    (v : ℕ → M.NormalGradient q) (u : Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)))
    (B E : ℝ≥0) (L : ℝ)
    (hd : ∀ n, M.NormalFormDomain q (f n) (v n))
    (hB : ∀ n, ‖f n‖ ≤ B) (hE : ∀ n, M.normalOscillatorForm q (f n) (v n) ≤ E)
    (hf : Tendsto f atTop (𝓝 u))
    (hL : Tendsto (fun n => M.normalOscillatorForm q (f n) (v n)) atTop (𝓝 L)) :
    ∃ z : M.NormalGradient q, M.NormalFormDomain q u z ∧ M.normalOscillatorForm q u z ≤ L := by
  let w := M.normalMomentWeight q
  let mw (n : ℕ) := (hd n).2.toLp (fun x => w x • f n x)
  let K : ℝ := E+‖M.deformedFermionField 1 1 q‖*(B : ℝ)^2
  have hK : 0 ≤ K := add_nonneg E.coe_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _))
  have hbound (n : ℕ) : (1/2 : ℝ)*‖v n‖^2+‖mw n‖^2 ≤ K := by
    exact (M.normalOscillator_coercive q (f n) (v n) (hd n)).trans
      (add_le_add (hE n) (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hB n) 2) (norm_nonneg _)))
  have hA (n : ℕ) : ‖v n‖ ≤ Real.sqrt (2*K) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity)]
    nlinarith [hbound n,sq_nonneg ‖mw n‖]
  have hC (n : ℕ) : ‖mw n‖ ≤ Real.sqrt K := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hK]
    nlinarith [hbound n,sq_nonneg ‖v n‖]
  have hform : Tendsto (fun n => (1/2 : ℝ)*‖v n‖^2+‖mw n‖^2+
      inner ℝ (f n) ((M.deformedFermionField 1 1 q).compLp (f n))) atTop (𝓝 L) := by
    convert hL using 1
    ext n
    exact (M.normalOscillatorForm_weighted q (f n) (v n) (hd n)).symm
  obtain ⟨z,hu,hz,he⟩ := BFSSSliceSobolev.weighted_closed_form_lsc volume
    (EuclideanSpace.basisFun (M.NormalIndex q) ℝ) w
    (M.normalMomentWeight_continuous q).aestronglyMeasurable
    (M.deformedFermionField 1 1 q) f v u (Real.sqrt (2*K)) (Real.sqrt K) L
    (fun n => (hd n).1) (fun n => (hd n).2) hf hA hC hform
  have hzu : M.NormalFormDomain q u z := ⟨hz,hu⟩
  refine ⟨z,hzu,?_⟩
  rw [M.normalOscillatorForm_weighted q u z hzu]
  exact he
end
end BFSSQuantum.AlgebraData

end OAI
