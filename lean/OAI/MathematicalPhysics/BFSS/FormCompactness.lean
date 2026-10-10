import Mathlib
import OAI.MathematicalPhysics.BFSS.FormClosure

namespace OAI

/-! Weighted form compactness and confining coercivity. -/

namespace BFSSSliceSobolev
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal
variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
local notation "X" => EuclideanSpace ℝ ι
local notation "μ" => (volume : Measure X)
local notation "e" => (EuclideanSpace.basisFun ι ℝ)

omit [CompleteSpace F] in
theorem core_moment_totallyBounded (f : ℕ → Core (E := X) (F := F))
    (A B C : ℝ≥0)
    (hA : ∀ n, ‖gradient μ e (f n)‖ ≤ A)
    (hB : ∀ n, ‖toL2 μ (f n)‖ ≤ B)
    (hC : ∀ n, (∫ x : X, ‖x‖^2*‖f n x‖^2) ≤ (C : ℝ)^2) :
    TotallyBounded (range (fun n => toL2 μ (f n))) := by
  classical
  let D : ℝ≥0 := (Fintype.card ι+1)*A
  have hder (n : ℕ) : (∫ x : X, ‖fderiv ℝ (f n : X → F) x‖^2) ≤ (D : ℝ)^2 := by
    calc
      _ ≤ ∫ x : X, (Fintype.card ι : ℝ) * ∑ j, ‖fderiv ℝ (f n : X → F) x (e j)‖^2 := by
        apply integral_mono (op_derivative_sq_integrable μ (f n))
          ((integrable_finsetSum _ (fun j _ => derivative_sq_integrable μ (f n) (e j))).const_mul _)
        intro x
        simpa only [EuclideanSpace.basisFun_apply] using BFSSRellich.opNorm_sq_le_coordinate_sum (ι := ι) (fderiv ℝ (f n : X → F) x)
      _ = (Fintype.card ι : ℝ)*‖gradient μ e (f n)‖^2 := by rw [integral_const_mul,gradient_norm_sq]
      _ ≤ (Fintype.card ι : ℝ)*(A : ℝ)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hA n) 2) (by positivity)
      _ ≤ (D : ℝ)^2 := by
        change (Fintype.card ι : ℝ)*(A : ℝ)^2 ≤ (((Fintype.card ι : ℝ)+1)*(A : ℝ))^2
        nlinarith [sq_nonneg ((Fintype.card ι : ℝ)*(A : ℝ)),mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card ι)) (sq_nonneg (A : ℝ))]
  have hnorm (n : ℕ) : (∫ x : X, ‖f n x‖^2) ≤ (B : ℝ)^2 := by
    rw [←toL2_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB n) 2
  have hlocal (R : ℝ) (hR : 0 < R) : TotallyBounded (range (fun n =>
      BFSSRellich.localLp (K := Metric.closedBall (0 : X) R) (f n) (f n).continuous)) := by
    let φ : ContDiffBump (0 : X) := ⟨R,2*R,hR,by linarith⟩
    apply BFSSRellich.localRellich_on φ (fun _ hx => hx) (fun n => (f n : X → F))
      (fun n => (f n).contDiff.of_le (by simp)) D B
    · intro n
      exact (setIntegral_le_integral (op_derivative_sq_integrable μ (f n))
        (Eventually.of_forall (fun x => sq_nonneg _))).trans (hder n)
    · intro n
      exact (setIntegral_le_integral
        ((f n).continuous.norm.pow 2 |>.integrable_of_hasCompactSupport
          (norm_sq_compact (f n) (f n).hasCompactSupport))
        (Eventually.of_forall (fun x => sq_nonneg _))).trans (hnorm n)
  have ht := BFSSRellich.weighted_tight_compactness (fun n => (f n : X → F))
    (fun n => (f n).continuous) (fun n => (f n).hasCompactSupport)
    (fun _ : X => (1 : ℝ)) continuous_const (fun _ : ℕ => (0 : ℝ)) tendsto_const_nhds C
    (by simpa only [one_smul] using hC) hlocal
  have he (n : ℕ) : toL2 μ (f n) = BFSSRellich.compactLp (f n) (f n).continuous (f n).hasCompactSupport := rfl
  simpa only [one_smul,←he] using ht
end
end BFSSSliceSobolev
namespace BFSSSliceSobolev
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal
variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
local notation "X" => EuclideanSpace ℝ ι
local notation "μ" => (volume : Measure X)
local notation "e₀" => (EuclideanSpace.basisFun ι ℝ)

omit [CompleteSpace F] [FiniteDimensional ℝ F] in
lemma weightedToL2_norm_sq (w : X → ℝ) (hw : Continuous w)
    (f : Core (E := X) (F := F)) :
    ‖weightedToL2 μ w hw f‖^2 = ∫ x : X, w x ^ 2 * ‖f x‖^2 := by
  rw [BFSSLocalL2.lp_norm_sq]
  apply integral_congr_ae
  filter_upwards [weightedToL2_ae μ w hw f] with x hx
  rw [hx,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]

omit [CompleteSpace F] [FiniteDimensional ℝ F] in
lemma weightedClosure_approx (w : X → ℝ) (hw : Continuous w)
    {u : Lp F 2 μ} {v : Gradient (F := F) μ (ι := ι)} {m : Lp F 2 μ}
    (hd : (u,v,m) ∈ weightedClosure μ e₀ w hw) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Core (E := X) (F := F), dist u (toL2 μ f) < ε ∧
      dist v (gradient μ e₀ f) < ε ∧ dist m (weightedToL2 μ w hw f) < ε := by
  obtain ⟨p,⟨f,rfl⟩,hp⟩ := Metric.mem_closure_iff.mp hd ε hε
  simp only [Prod.dist_eq] at hp
  exact ⟨f,(lt_of_le_of_lt (le_max_left _ _) hp),
    (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hp),
    (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hp)⟩

theorem weightedClosure_totallyBounded (w : X → ℝ) (hw : Continuous w)
    (c : ℝ) (hc : 0 < c) (hcw : ∀ x : X, c * ‖x‖^2 ≤ w x ^ 2)
    (u : ℕ → Lp F 2 μ) (v : ℕ → Gradient (F := F) μ (ι := ι)) (m : ℕ → Lp F 2 μ)
    (A B C : ℝ≥0) (hd : ∀ n, (u n,v n,m n) ∈ weightedClosure μ e₀ w hw)
    (hA : ∀ n, ‖v n‖ ≤ A) (hB : ∀ n, ‖u n‖ ≤ B) (hC : ∀ n, ‖m n‖ ≤ C) :
    TotallyBounded (range u) := by
  let ε : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := one_div_pos.mpr (by positivity)
  have hε1 (n : ℕ) : ε n ≤ 1 := by
    apply (div_le_iff₀ (show 0 < (n : ℝ)+1 by positivity)).2
    simp only [one_mul]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  choose f hfu hfv hfm using (fun n => weightedClosure_approx w hw (hd n) (hε n))
  have hfA (n : ℕ) : ‖gradient μ e₀ (f n)‖ ≤ (A+1 : ℝ≥0) := by
    have hdist : dist (gradient μ e₀ (f n)) (v n) ≤ 1 := by simpa only [dist_comm] using (hfv n).le.trans (hε1 n)
    have he := norm_le_norm_add_const_of_dist_le hdist
    change _ ≤ (A : ℝ)+1
    linarith [hA n]
  have hfB (n : ℕ) : ‖toL2 μ (f n)‖ ≤ (B+1 : ℝ≥0) := by
    have hdist : dist (toL2 μ (f n)) (u n) ≤ 1 := by simpa only [dist_comm] using (hfu n).le.trans (hε1 n)
    have he := norm_le_norm_add_const_of_dist_le hdist
    change _ ≤ (B : ℝ)+1
    linarith [hB n]
  have hfC (n : ℕ) : ‖weightedToL2 μ w hw (f n)‖ ≤ (C : ℝ)+1 := by
    have hdist : dist (weightedToL2 μ w hw (f n)) (m n) ≤ 1 := by simpa only [dist_comm] using (hfm n).le.trans (hε1 n)
    have he := norm_le_norm_add_const_of_dist_le hdist
    linarith [hC n]
  let D : ℝ≥0 := ⟨Real.sqrt (((C : ℝ)+1)^2/c),Real.sqrt_nonneg _⟩
  have hmoment (n : ℕ) : (∫ x : X, ‖x‖^2*‖f n x‖^2) ≤ (D : ℝ)^2 := by
    change _ ≤ (Real.sqrt (((C : ℝ)+1)^2/c))^2
    rw [Real.sq_sqrt (div_nonneg (sq_nonneg _) hc.le)]
    apply (le_div_iff₀ hc).2
    rw [mul_comm,←integral_const_mul]
    calc
      _ ≤ ∫ x : X, w x ^ 2 * ‖f n x‖^2 := by
        apply integral_mono
          ((((continuous_norm.pow 2).mul ((f n).continuous.norm.pow 2)).integrable_of_hasCompactSupport
            (norm_sq_compact (f n) (f n).hasCompactSupport).mul_left).const_mul c)
          (((hw.pow 2).mul ((f n).continuous.norm.pow 2)).integrable_of_hasCompactSupport
            (norm_sq_compact (f n) (f n).hasCompactSupport).mul_left)
        intro x
        change c*(‖x‖^2*‖f n x‖^2) ≤ w x ^ 2*‖f n x‖^2
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hcw x) (sq_nonneg ‖f n x‖)
      _ = ‖weightedToL2 μ w hw (f n)‖^2 := (weightedToL2_norm_sq w hw (f n)).symm
      _ ≤ ((C : ℝ)+1)^2 := pow_le_pow_left₀ (norm_nonneg _) (hfC n) 2
  apply BFSSRellich.totallyBounded_asymptotic (fun n => toL2 μ (f n)) u
    (core_moment_totallyBounded f (A+1) (B+1) D hfA hfB hmoment)
  have hdist (n : ℕ) : dist (toL2 μ (f n)) (u n) ≤ ε n := by simpa only [dist_comm] using (hfu n).le
  exact squeeze_zero (fun n => dist_nonneg) hdist tendsto_one_div_add_atTop_nhds_zero_nat
end
end BFSSSliceSobolev
namespace BFSSNormalAnalysis
noncomputable section
open MeasureTheory
variable {X F : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
lemma constant_quadratic_abs_le (A : F →L[ℝ] F) (u : Lp F 2 μ) :
    |inner ℝ u (A.compLp u)| ≤ ‖A‖*‖u‖^2 := by
  calc
    _ ≤ ‖u‖*‖A.compLp u‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖u‖*(‖A‖*‖u‖) := mul_le_mul_of_nonneg_left (A.norm_compLp_le u) (norm_nonneg _)
    _ = _ := by ring
lemma constant_quadratic_coercive (A : F →L[ℝ] F) (u : Lp F 2 μ) (a : ℝ) :
    a ≤ a+inner ℝ u (A.compLp u)+‖A‖*‖u‖^2 := by
  have hh := (abs_le.mp (constant_quadratic_abs_le μ A u)).1
  linarith only [hh]
end
end BFSSNormalAnalysis
namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] normalSlice gaugeAction coreToL2 deformedFermionField
local instance formCompactnessFermionNormedAddCommGroup :
    NormedAddCommGroup (Fermion N →L[ℝ] Fermion N) := inferInstance
local instance formCompactnessFermionNormedSpace :
    NormedSpace ℝ (Fermion N →L[ℝ] Fermion N) := inferInstance

lemma normalOscillatorForm_weighted (q : Boson N)
    (u : Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)))
    (v : M.NormalGradient q) (hd : M.NormalFormDomain q u v) :
    M.normalOscillatorForm q u v = (1/2 : ℝ)*‖v‖^2+
      ‖hd.2.toLp (fun x => M.normalMomentWeight q x • u x)‖^2+
      inner ℝ u ((M.deformedFermionField 1 1 q).compLp u) := by
  exact congrArg₂ (fun a b : ℝ => (1/2 : ℝ)*‖v‖^2+a+b)
    (M.normalPotential_norm_sq q u hd.2).symm
    (BFSSNormalAnalysis.constant_quadratic_eq volume (M.deformedFermionField 1 1 q) u)

lemma normalOscillator_coercive (q : Boson N)
    (u : Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)))
    (v : M.NormalGradient q) (hd : M.NormalFormDomain q u v) :
    (1/2 : ℝ)*‖v‖^2+
      ‖hd.2.toLp (fun x => M.normalMomentWeight q x • u x)‖^2 ≤
      M.normalOscillatorForm q u v+‖M.deformedFermionField 1 1 q‖*‖u‖^2 := by
  rw [M.normalOscillatorForm_weighted q u v hd]
  exact BFSSNormalAnalysis.constant_quadratic_coercive volume
    (M.deformedFermionField 1 1 q) u _

theorem normalForm_totallyBounded (q : Boson N) (hq : q ∈ M.massiveZeros)
    (u : ℕ → Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)))
    (v : ℕ → M.NormalGradient q) (B E : ℝ≥0)
    (hd : ∀ n, M.NormalFormDomain q (u n) (v n))
    (hB : ∀ n, ‖u n‖ ≤ B) (hE : ∀ n, M.normalOscillatorForm q (u n) (v n) ≤ E) :
    TotallyBounded (range u) := by
  obtain ⟨c,hc,hcq⟩ := M.normalQuadratic_coercive q hq
  let w := M.normalMomentWeight q
  let mw (n : ℕ) := (hd n).2.toLp (fun x => w x • u n x)
  let K : ℝ := E+‖M.deformedFermionField 1 1 q‖*(B : ℝ)^2
  have hK : 0 ≤ K := add_nonneg E.coe_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _))
  let A : ℝ≥0 := ⟨Real.sqrt (2*K),by positivity⟩
  let C : ℝ≥0 := ⟨Real.sqrt K,by positivity⟩
  have hbound (n : ℕ) : (1/2 : ℝ)*‖v n‖^2+‖mw n‖^2 ≤ K := by
    exact (M.normalOscillator_coercive q (u n) (v n) (hd n)).trans
      (add_le_add (hE n) (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hB n) 2) (norm_nonneg _)))
  have hA (n : ℕ) : ‖v n‖ ≤ A := by
    apply (sq_le_sq₀ (norm_nonneg _) A.coe_nonneg).mp
    change ‖v n‖^2 ≤ (Real.sqrt (2*K))^2
    rw [Real.sq_sqrt (by positivity)]
    nlinarith [hbound n,sq_nonneg ‖mw n‖]
  have hC (n : ℕ) : ‖mw n‖ ≤ C := by
    apply (sq_le_sq₀ (norm_nonneg _) C.coe_nonneg).mp
    change ‖mw n‖^2 ≤ (Real.sqrt K)^2
    rw [Real.sq_sqrt hK]
    nlinarith [hbound n,sq_nonneg ‖v n‖]
  apply BFSSSliceSobolev.weightedClosure_totallyBounded w
    (M.normalMomentWeight_continuous q) c hc _ u v mw A B C _ hA hB hC
  · intro x
    change c*‖x‖^2 ≤ (Real.sqrt (M.normalQuadratic q (M.normalCoordinateIsometry q x : Boson N)))^2
    rw [Real.sq_sqrt (M.normalQuadratic_nonneg q _)]
    have hn : ‖(M.normalCoordinateIsometry q x : Boson N)‖ = ‖x‖ :=
      (M.normalCoordinateIsometry q).norm_map x
    simpa only [hn] using hcq (M.normalCoordinateIsometry q x) (M.normalCoordinateIsometry q x).property
  · intro n
    exact BFSSSliceSobolev.mem_weightedClosure volume
      (EuclideanSpace.basisFun (M.NormalIndex q) ℝ) w (M.normalMomentWeight_continuous q)
      (hd n).1 (hd n).2
end
end BFSSQuantum.AlgebraData

end OAI
