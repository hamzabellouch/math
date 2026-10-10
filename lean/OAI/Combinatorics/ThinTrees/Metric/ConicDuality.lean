import Mathlib
import OAI.Combinatorics.ThinTrees.Metric.MatrixBound

namespace OAI

/-! Metric conic duality. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree
open scoped Classical MatrixOrder Topology
open Filter

section GeneralFinite
variable {V E T J : Type*} [Fintype V] [DecidableEq V] [Fintype T] [Fintype J]

omit [DecidableEq V] in
lemma trace_pairing_continuous (Z : Matrix V V ℝ) :
    Continuous (fun D : Matrix V V ℝ => (D*Z).trace) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  fun_prop

lemma trace_pairing_convex (Z : Matrix V V ℝ) (d : ℝ) :
    ConvexOn ℝ {D : Matrix V V ℝ | D.PosDef} (fun D => (D*Z).trace-d) := by
  refine ⟨MatrixDual.posDef_convex,?_⟩
  intro X _ Y _ a b _ _ hab
  simp only [add_mul,smul_mul_assoc,trace_add,trace_smul,smul_eq_mul]
  nlinarith only [congrArg (fun v : ℝ => v*d) hab]

lemma trace_test_slater (Z : J → Matrix V V ℝ) {d : J → ℝ} (hd : ∀j, 0 < d j) :
    ∃D : Matrix V V ℝ, D.PosDef ∧ ∀j, (D*Z j).trace-d j < 0 := by
  have hlim (j : J) : Tendsto (fun t : ℝ => t*(Z j).trace) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => t*(Z j).trace) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀j, t*(Z j).trace < d j :=
    eventually_all.mpr (fun j => (hlim j).eventually_lt_const (hd j))
  have hp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := eventually_mem_nhdsWithin
  obtain ⟨t,ht,htp⟩ := (he.and hp).exists
  refine ⟨t • (1 : Matrix V V ℝ),Matrix.PosDef.one.smul htp,?_⟩
  intro j
  simpa only [smul_mul_assoc,one_mul,trace_smul,smul_eq_mul,sub_lt_zero] using ht j

lemma trace_weighted_tests (Z : J → Matrix V V ℝ) (y d : J → ℝ) (D : Matrix V V ℝ) :
    ((∑j, y j • Z j)*D).trace-∑j, y j*d j = ∑j, y j*((D*Z j).trace-d j) := by
  simp only [sum_mul,smul_mul_assoc,trace_sum,trace_smul,smul_eq_mul,mul_sub,sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [trace_mul_comm]

lemma finite_shortcut_of_trace_bound (b : E → V → ℝ) (O : T → Finset E)
    (Z : J → Matrix V V ℝ) (hZ : ∀j, (Z j).PosSemidef) (d : J → ℝ)
    (hd : ∀j, 0 < d j) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀lam : T → ℝ, ∀y : J → ℝ, (∀t, 0 ≤ lam t) → (∑t, lam t)=1 →
      (∀j, 0 ≤ y j) →
      (CFC.sqrt (CFC.sqrt (∑j, y j • Z j) * ShortcutDual.objectiveMatrix b O lam *
        CFC.sqrt (∑j, y j • Z j))).trace^2 ≤ K * ∑j, y j*d j)
    {eta : ℝ} (heta : 0 < eta) :
    ∃D : Matrix V V ℝ, D.PosDef ∧
      (∀t, ShortcutDual.boundaryAverage b O t D < K+eta) ∧
      (∀j, (D*Z j).trace < d j) := by
  have hs := Duality.strict_feasible_of_dual_bound {D : Matrix V V ℝ | D.PosDef}
    MatrixDual.posDef_convex (ShortcutDual.boundaryAverage b O) (fun j D => (D*Z j).trace-d j)
    (ShortcutDual.boundaryAverage_convex b O) (fun j => trace_pairing_convex (Z j) (d j))
    (trace_test_slater Z hd) (K+eta)
  obtain ⟨D,hD,hf,hg⟩ := hs (by
    intro lam y hlam hlams hy
    let A := ShortcutDual.objectiveMatrix b O lam
    let W := ∑j, y j • Z j
    let N := (CFC.sqrt (CFC.sqrt W*A*CFC.sqrt W)).trace
    let v := ∑j, y j*d j
    have hv : 0 ≤ v := sum_nonneg (fun j _ => mul_nonneg (hy j) (hd j).le)
    have hN : 0 ≤ N := (CFC.sqrt_nonneg _).posSemidef.trace_nonneg
    have hb : N^2 ≤ K*v := hbound lam y hlam hlams hy
    have hNv : 2*N ≤ K+v := by nlinarith only [hb,hK,hv,hN,sq_nonneg (K-v)]
    have hW : W.PosSemidef := Matrix.posSemidef_sum _ (fun j _ => (hZ j).smul (hy j))
    obtain ⟨D,hD,hval⟩ := MatrixDual.trace_objective_approx
      (ShortcutDual.objectiveMatrix_posSemidef b O hlam) hW
      (show 2*N < K+eta+v by linarith only [hNv,heta])
    refine ⟨D,hD,?_⟩
    have htr := trace_weighted_tests Z y d D
    rw [ShortcutDual.trace_objectiveMatrix] at hval
    change (∑t,lam t*ShortcutDual.boundaryAverage b O t D) + (W*D).trace < K+eta+v at hval
    linarith only [hval,htr])
  exact ⟨D,hD,hf,fun j => sub_neg.mp (hg j)⟩

end GeneralFinite

section Pairing
variable {n : ℕ}

lemma trace_gram_pairing (B X : Matrix (Fin n) (Fin n) ℝ) :
    (B*(Xᵀ*X)).trace=∑i, qform B (X i) := by
  rw [←mul_assoc,trace_mul_cycle]
  apply sum_congr rfl
  intro i _
  simp only [diag_apply,mul_apply,transpose_apply,qform,mulVec,dotProduct]
  simp only [sum_mul,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  ring

lemma trace_pairing_nonneg {B Z : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.PosSemidef) (hZ : Z.PosSemidef) : 0 ≤ (B*Z).trace := by
  conv_rhs => rw [←sqrt_gram hZ]
  rw [trace_gram_pairing]
  exact sum_nonneg (fun i _ => qform_nonneg hB _)

lemma trace_pairing_pos {B Z : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.PosDef) (hZ : Z.PosSemidef) (hZ0 : Z ≠ 0) : 0 < (B*Z).trace := by
  have hX : CFC.sqrt Z ≠ 0 := by
    intro he
    have hh := sqrt_gram hZ
    rw [he,transpose_zero,zero_mul] at hh
    exact hZ0 hh.symm
  have hi : ∃i, CFC.sqrt Z i ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hX (funext hh)
  obtain ⟨i,hi⟩ := hi
  rw [←sqrt_gram hZ,trace_gram_pairing]
  apply sum_pos'
  · intro j _
    exact qform_nonneg hB.posSemidef _
  · exact ⟨i,mem_univ i,by simpa only [qform,star_trivial] using hB.dotProduct_mulVec_pos hi⟩

lemma trace_pairing_mono {B D Z : Matrix (Fin n) (Fin n) ℝ}
    (hBD : B ≤ D) (hZ : Z.PosSemidef) : (B*Z).trace ≤ (D*Z).trace := by
  have hh := trace_pairing_nonneg (Matrix.le_iff.mp hBD) hZ
  simpa only [sub_mul,trace_sub,sub_nonneg] using hh

lemma test_one : Test (1 : Matrix (Fin n) (Fin n) ℝ) := by
  refine ⟨Matrix.PosSemidef.one,?_⟩
  intro u v w
  have heq (a b : Fin n) : qform (1 : Matrix (Fin n) (Fin n) ℝ) (difference a b)=
      if a=b then 0 else 2 := by
    by_cases hab : a=b
    · simp [hab,difference,qform]
    · norm_num [qform,difference,MultiGraph.point,sub_dotProduct,dotProduct_sub,hab,Ne.symm hab]
  simp only [heq]
  split_ifs <;> try norm_num
  all_goals simp_all

end Pairing
end
end AlgorithmicThinTrees.MetricTests
end

end OAI
