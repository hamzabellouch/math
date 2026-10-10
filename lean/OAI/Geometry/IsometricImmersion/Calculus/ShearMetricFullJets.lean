import OAI.Geometry.IsometricImmersion.Calculus.ShearMetricJets
import OAI.Geometry.IsometricImmersion.Comparison.ShearFirstJetComparison

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem metricInShearCoordinates_sub (g h : MetricField) (q0 : ℝ) :
    metricInShearCoordinates (fun p => g p-h p) q0 =
      fun p => metricInShearCoordinates g q0 p-metricInShearCoordinates h q0 p := by
  funext p
  ext i j
  simp only [metricInShearCoordinates,affinePullbackMetric,Matrix.mul_apply,
    Matrix.transpose_apply,Matrix.sub_apply,Fin.sum_univ_two]
  ring

theorem sheared_metric_full_jet_bound {g : MetricField} {U : Set Coord}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun p => g p i j) U) (hU : IsOpen U)
    {q0 B : ℝ} (hq0 : |q0| ≤ 1) (hB : 0 ≤ B) {p : Coord}
    (hp : inverseShearCoordinates q0 p ∈ U) (n : ℕ)
    (hjet : ∀ i j, ‖iteratedFDeriv ℝ n (fun q => g q i j) (inverseShearCoordinates q0 p)‖ ≤ B)
    (i j : Fin 2) :
    ‖iteratedFDeriv ℝ n (fun q => metricInShearCoordinates g q0 q i j) p‖ ≤ 4*2^n*B := by
  let V := inverseShearCoordinates q0 ⁻¹' U
  have hV : IsOpen V := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  let c (a b : Fin 2) := inverseShearMatrix q0 a i*inverseShearMatrix q0 b j
  let f (a b : Fin 2) := heightInShearCoordinates (fun q => g q a b) q0
  let term (a b : Fin 2) : Coord → ℝ := fun q => c a b*f a b q
  have hfs (a b : Fin 2) : ContDiffOn ℝ ∞ (f a b) V :=
    heightInShearCoordinates_contDiffOn (hg a b) q0
  have hts (a b : Fin 2) : ContDiffAt ℝ n (term a b) p :=
    ((contDiffOn_const.mul (hfs a b)).contDiffAt (hV.mem_nhds hp)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hc (a b : Fin 2) : |c a b| ≤ 1 := by
    dsimp only [c]
    rw [abs_mul]
    exact (mul_le_mul (inverseShearMatrix_entry_le_one hq0 a i)
      (inverseShearMatrix_entry_le_one hq0 b j) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hnormL : ‖inverseShearCLM q0‖ ≤ 2 := (inverseShearCLM_norm_le q0).trans (by linarith)
  have htB (a b : Fin 2) : ‖iteratedFDeriv ℝ n (term a b) p‖ ≤ B*2^n := by
    have hchain := local_linear_full_jet_norm_bound (hg a b) hU (inverseShearCLM q0) hp n
    have hfB : ‖iteratedFDeriv ℝ n (f a b) p‖ ≤ B*2^n := by
      exact hchain.trans (mul_le_mul (hjet a b)
        (pow_le_pow_left₀ (norm_nonneg _) hnormL n) (pow_nonneg (norm_nonneg _) n) hB)
    change ‖iteratedFDeriv ℝ n ((c a b) • f a b) p‖ ≤ B*2^n
    rw [iteratedFDeriv_const_smul_apply
      (((hfs a b).contDiffAt (hV.mem_nhds hp)).of_le (WithTop.coe_le_coe.mpr le_top)),norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul (hc a b) hfB (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  rw [metricInShearCoordinates_four_terms]
  change ‖iteratedFDeriv ℝ n ((term 0 0+term 0 1)+(term 1 0+term 1 1)) p‖ ≤ _
  rw [iteratedFDeriv_add_apply (f := term 0 0+term 0 1) (g := term 1 0+term 1 1)
      ((hts 0 0).add (hts 0 1)) ((hts 1 0).add (hts 1 1)),
    iteratedFDeriv_add_apply (hts 0 0) (hts 0 1),iteratedFDeriv_add_apply (hts 1 0) (hts 1 1)]
  calc
    _ ≤ (B*2^n+B*2^n)+(B*2^n+B*2^n) := (norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add (htB 0 0) (htB 0 1)))
        ((norm_add_le _ _).trans (add_le_add (htB 1 0) (htB 1 1))))
    _ = _ := by ring

theorem sheared_metric_full_jet_difference_le {g h : MetricField} {U : Set Coord}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun p => g p i j) U)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun p => h p i j) U) (hU : IsOpen U)
    {q0 epsilon : ℝ} (hq0 : |q0| ≤ 1) (he : 0 ≤ epsilon) {p : Coord}
    (hp : inverseShearCoordinates q0 p ∈ U) (n : ℕ)
    (hjet : ∀ i j, ‖iteratedFDeriv ℝ n (fun q => g q i j-h q i j)
      (inverseShearCoordinates q0 p)‖ ≤ epsilon) (i j : Fin 2) :
    ‖iteratedFDeriv ℝ n (fun q => metricInShearCoordinates g q0 q i j-
      metricInShearCoordinates h q0 q i j) p‖ ≤ 4*2^n*epsilon := by
  have hb := sheared_metric_full_jet_bound
    (g := fun q => g q-h q) (fun a b => (hg a b).sub (hh a b)) hU hq0 he hp n hjet i j
  simpa only [metricInShearCoordinates_sub,Matrix.sub_apply] using hb

end SmoothLocal.Pulse

end

end OAI
