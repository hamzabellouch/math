import Mathlib
import OAI.MathematicalPhysics.BFSS.EnergyExtraction
import OAI.MathematicalPhysics.BFSS.LowerContinuity

namespace OAI

/-! Positive normal-form gap and nonzero zero-form extraction. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] normalSlice gaugeAction coreToL2 deformedFermionField

def NormalZeroOrthogonal (q : Boson N)
    (u : Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q))) : Prop :=
  ∀ z : Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)),
    ∀ v : M.NormalGradient q, M.NormalFormDomain q z v →
      M.normalOscillatorForm q z v = 0 → inner ℝ u z = 0

theorem normal_unit_gap (q : Boson N) (hq : q ∈ M.massiveZeros) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)),
      ∀ v : M.NormalGradient q, M.NormalFormDomain q u v → ‖u‖ = 1 →
        M.NormalZeroOrthogonal q u → δ ≤ M.normalOscillatorForm q u v := by
  by_contra hgap
  let ε : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := one_div_pos.mpr (by positivity)
  have hε1 (n : ℕ) : ε n ≤ 1 := by
    apply (div_le_iff₀ (show 0 < (n : ℝ)+1 by positivity)).2
    simp only [one_mul]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hbad (n : ℕ) : ∃ u : Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)),
      ∃ v : M.NormalGradient q, M.NormalFormDomain q u v ∧ ‖u‖ = 1 ∧
        M.NormalZeroOrthogonal q u ∧ M.normalOscillatorForm q u v < ε n := by
    by_contra! hn
    apply hgap
    exact ⟨ε n,hε n,hn⟩
  choose f v hd hn ho he using hbad
  have hE (n : ℕ) : M.normalOscillatorForm q (f n) (v n) ≤ (1 : ℝ≥0) :=
    (he n).le.trans (hε1 n)
  have hB (n : ℕ) : ‖f n‖ ≤ (1 : ℝ≥0) := by simp only [hn,NNReal.coe_one,le_refl]
  have hzero : Tendsto (fun n => M.normalOscillatorForm q (f n) (v n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => M.normalOscillator_nonneg q hq (f n) (v n) (hd n))
      (fun n => (he n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : IsCompact (closure (range f)) :=
    (M.normalForm_totallyBounded q hq f v 1 1 hd hB hE).closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨u,_,σ,hσ,hu⟩ := hc.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  have hun : ‖u‖ = 1 := tendsto_nhds_unique hu.norm
    (by simpa only [Function.comp_apply,hn] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  obtain ⟨z,hz,hzE⟩ := M.normalForm_lsc q (fun n => f (σ n)) (fun n => v (σ n)) u
    1 1 0 (fun n => hd (σ n)) (fun n => hB (σ n)) (fun n => hE (σ n)) hu
    (hzero.comp hσ.tendsto_atTop)
  have hz0 : M.normalOscillatorForm q u z = 0 := le_antisymm hzE (M.normalOscillator_nonneg q hq u z hz)
  have horth (n : ℕ) : inner ℝ (f (σ n)) u = 0 := ho (σ n) u z hz hz0
  have hi : inner ℝ u u = 0 := tendsto_nhds_unique (hu.inner tendsto_const_nhds)
    (by simpa only [Function.comp_apply,horth] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  rw [real_inner_self_eq_norm_sq,hun] at hi
  norm_num at hi
end
end BFSSQuantum.AlgebraData
namespace BFSSNormalAnalysis
noncomputable section
open MeasureTheory Filter Topology
variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {μ : Measure X}

lemma moment_smul_memLp (w : X → ℝ) (u : Lp F 2 μ)
    (hu : MemLp (fun x => w x • u x) 2 μ) (r : ℝ) :
    MemLp (fun x => w x • (r • u) x) 2 μ := by
  apply MemLp.ae_eq _ (hu.const_smul r)
  filter_upwards [Lp.coeFn_smul r u] with x hx
  simp only [Pi.smul_apply] at hx
  rw [hx]
  exact smul_comm _ _ _

lemma moment_smul_toLp (w : X → ℝ) (u : Lp F 2 μ)
    (hu : MemLp (fun x => w x • u x) 2 μ) (r : ℝ)
    (hr : MemLp (fun x => w x • (r • u) x) 2 μ) :
    hr.toLp (fun x => w x • (r • u) x) = r • hu.toLp (fun x => w x • u x) := by
  apply Lp.ext
  filter_upwards [hr.coeFn_toLp,hu.coeFn_toLp,Lp.coeFn_smul r (hu.toLp _),Lp.coeFn_smul r u]
    with x h₁ h₂ h₃ h₄
  simp only [Pi.smul_apply] at h₃ h₄
  rw [h₁,h₃,h₂,h₄,smul_comm]

lemma weighted_energy_smul {F' : Type*} [NormedAddCommGroup F']
    [InnerProductSpace ℝ F'] {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : F' →L[ℝ] F') (u z : Lp F' 2 μ) (v : G) (r : ℝ) :
    (1/2 : ℝ)*‖r • v‖^2+‖r • z‖^2+inner ℝ (r • u) (A.compLp (r • u)) =
      r^2*((1/2 : ℝ)*‖v‖^2+‖z‖^2+inner ℝ u (A.compLp u)) := by
  have he : A.compLp (r • u) = r • A.compLp u := (A.compLpL 2 μ).map_smul r u
  rw [he,real_inner_smul_left,real_inner_smul_right,norm_smul,norm_smul,
    Real.norm_eq_abs,mul_pow,mul_pow,sq_abs]
  ring

end
end BFSSNormalAnalysis

namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory Filter Topology Set
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] normalSlice gaugeAction coreToL2 deformedFermionField
local instance normalGapFermionNormedAddCommGroup :
    NormedAddCommGroup (Fermion N →L[ℝ] Fermion N) := inferInstance
local instance normalGapFermionNormedSpace :
    NormedSpace ℝ (Fermion N →L[ℝ] Fermion N) := inferInstance

lemma NormalFormDomain.smul {q : Boson N}
    {u : Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q))}
    {v : M.NormalGradient q} (hd : M.NormalFormDomain q u v) (r : ℝ) :
    M.NormalFormDomain q (r • u) (r • v) :=
  ⟨(BFSSSliceSobolev.closedGraph volume (EuclideanSpace.basisFun (M.NormalIndex q) ℝ)).smul_mem r hd.1,
   BFSSNormalAnalysis.moment_smul_memLp (M.normalMomentWeight q) u hd.2 r⟩

lemma normalOscillator_smul (q : Boson N)
    (u : Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)))
    (v : M.NormalGradient q) (hd : M.NormalFormDomain q u v) (r : ℝ) :
    M.normalOscillatorForm q (r • u) (r • v) = r^2 * M.normalOscillatorForm q u v := by
  let z := hd.2.toLp (fun x => M.normalMomentWeight q x • u x)
  let zr := (hd.smul M r).2.toLp (fun x => M.normalMomentWeight q x • (r • u) x)
  have hm : zr = r • z := BFSSNormalAnalysis.moment_smul_toLp
    (M.normalMomentWeight q) u hd.2 r (hd.smul M r).2
  have hE : (1/2 : ℝ)*‖r • v‖^2+‖r • z‖^2+
      inner ℝ (r • u) ((M.deformedFermionField 1 1 q).compLp (r • u)) =
      r^2*((1/2 : ℝ)*‖v‖^2+‖z‖^2+
      inner ℝ u ((M.deformedFermionField 1 1 q).compLp u)) :=
      BFSSNormalAnalysis.weighted_energy_smul (M.deformedFermionField 1 1 q) u z v r

  calc
    M.normalOscillatorForm q (r • u) (r • v) = (1/2 : ℝ)*‖r • v‖^2+‖zr‖^2+
      inner ℝ (r • u) ((M.deformedFermionField 1 1 q).compLp (r • u)) :=
        M.normalOscillatorForm_weighted q (r • u) (r • v) (hd.smul M r)
    _ = (1/2 : ℝ)*‖r • v‖^2+‖r • z‖^2+
      inner ℝ (r • u) ((M.deformedFermionField 1 1 q).compLp (r • u)) :=
        congrArg (fun t => (1/2 : ℝ)*‖r • v‖^2+‖t‖^2+
          inner ℝ (r • u) ((M.deformedFermionField 1 1 q).compLp (r • u))) hm
    _ = r^2*((1/2 : ℝ)*‖v‖^2+‖z‖^2+
      inner ℝ u ((M.deformedFermionField 1 1 q).compLp u)) := hE
    _ = r^2*M.normalOscillatorForm q u v :=
      congrArg (r^2 * ·) (M.normalOscillatorForm_weighted q u v hd).symm

theorem normal_gap (q : Boson N) (hq : q ∈ M.massiveZeros) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)),
      ∀ v : M.NormalGradient q, M.NormalFormDomain q u v →
        M.NormalZeroOrthogonal q u → δ*‖u‖^2 ≤ M.normalOscillatorForm q u v := by
  obtain ⟨δ,hδ,hgap⟩ := M.normal_unit_gap q hq
  refine ⟨δ,hδ,?_⟩
  intro u v hd ho
  by_cases hu : u = 0
  · simpa only [hu,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero] using
      M.normalOscillator_nonneg q hq u v hd
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let r : ℝ := ‖u‖⁻¹
  have hr : 0 < r := inv_pos.mpr hn
  have hunit : ‖r • u‖ = 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact inv_mul_cancel₀ hn.ne'
  have hor : M.NormalZeroOrthogonal q (r • u) := by
    intro z w hz he
    rw [real_inner_smul_left,ho z w hz he,mul_zero]
  have hs := hgap (r • u) (r • v) (hd.smul M r) hunit hor
  rw [M.normalOscillator_smul q u v hd r] at hs
  have hmul := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖u‖)
  have he : r^2*‖u‖^2 = 1 := by rw [←mul_pow,inv_mul_cancel₀ hn.ne',one_pow]
  calc
    δ*‖u‖^2 ≤ r^2*M.normalOscillatorForm q u v*‖u‖^2 := hmul
    _ = M.normalOscillatorForm q u v := by rw [mul_right_comm,he,one_mul]
end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData.GaugeData
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal
variable {N : ℕ} {M : AlgebraData N} {G : M.GaugeData}
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2
  MeasuredNormalPatch.closedProfile

theorem NormalClosedEnergyData.zero_forms {h : ℕ → ℝ} {x : ℕ → G.coreNormClosure}
    (D : G.NormalClosedEnergyData h x 0) (q : D.S) :
    M.normalOscillatorForm q.val (D.u q) (D.v q) = 0 := by
  have hp (r : D.S) : 0 ≤ M.normalOscillatorForm r.val (D.u r) (D.v r) :=
    M.normalOscillator_nonneg r.val (D.zero r.val r.property) (D.u r) (D.v r) (D.domain r)
  apply le_antisymm _ (hp q)
  exact (Finset.single_le_sum (fun r _ => hp r) (Finset.mem_univ q)).trans D.energy

theorem NormalClosedEnergyData.exists_nonzero_zero_form {h : ℕ → ℝ}
    {x : ℕ → G.coreNormClosure} (D : G.NormalClosedEnergyData h x 0)
    (hx : ∀ n, ‖x n‖ = 1) :
    ∃ q : D.S, D.u q ≠ 0 ∧ M.normalOscillatorForm q.val (D.u q) (D.v q) = 0 := by
  classical
  have hn : ∑ q : D.S, ‖D.u q‖^2 = 1 := by
    apply tendsto_nhds_unique D.norm
    simpa only [hx,one_pow] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have he : ∃ q : D.S, D.u q ≠ 0 := by
    by_contra! he
    simp only [he,norm_zero,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero] at hn
    norm_num at hn
  obtain ⟨q,hq⟩ := he
  exact ⟨q,hq,D.zero_forms q⟩
end
end BFSSQuantum.AlgebraData.GaugeData

end OAI
