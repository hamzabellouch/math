import OAI.Combinatorics.Progressions.Geometry.CubicBoxGlobalExpansion
import OAI.Combinatorics.Progressions.Linear.CubicKernelApproximation

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_cubic_approximated_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p r : ℝ}, 0 ≤ p → 0 ≤ r →
      Real.exp ((p + r + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-((p + r + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) ((p + r + C) ^ C),
        ∃ V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) ((p + r + C) ^ C),
          V.dim ≤ 8 * M.dim ∧
          (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) k x,
            V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) =
              V.eval k x) ∧
          NativeIntegerVectorEquivalence 2 ((p + r + C) ^ C)
            M.eval (fun k x => V.eval k (fun j => x j.1)) ∧
          NativeIntegerVectorEquivalence 2 ((p + r + C) ^ C)
            M.cubicMixedDerivative V.cubicTrilinearTriple ∧
          ∃ out : Fin M.outputDim, ∃ χ : ZMod N → AddChar (ZMod N) ℂ,
            (∀ h ∈ H, Real.exp (-((p + r + C) ^ C)) ≤ ‖finiteFourierCoeff
              (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N out (correlationInput h n))) (χ h)‖) ∧
            ∃ (branch : Bool) (i j : Fin V.outputDim × Fin V.outputDim) (D G : (Fin 3 → ℤ) → ℂ),
              Nonempty (NativeIntegerExpansion (fun _ : Fin 3 => 1) 2 ((p + r + C) ^ C) D) ∧
              Nonempty (NativeIntegerExpansion (fun _ : Fin 3 => 1) 2 ((p + r + C) ^ C) G) ∧
              (∀ z, ‖D z‖ ≤ 1) ∧
              (∀ z : Fin 3 → ZMod N, ‖G (fun k => ((z k).val : ℤ))‖ ≤ 1) ∧
              Real.exp (-((p + r + C) ^ C)) ≤
                (𝔼 z : Fin 3 → ZMod N, ‖D (fun k => ((z k).val : ℤ))‖ ^ 2) ∧
              Real.exp (-((p + r + C) ^ C)) ≤
                (𝔼 z : Fin 3 → ZMod N,
                  ‖V.cubicAntisymmetricPair i j ((z 1).val : ℤ) ((z 2).val : ℤ)
                      (cyclicBranchOffset (z 0) branch) * D (fun k => ((z k).val : ℤ))‖ ^ 2) ∧
              (𝔼 z : Fin 3 → ZMod N,
                ‖V.cubicAntisymmetricPair i j ((z 1).val : ℤ) ((z 2).val : ℤ)
                    (cyclicBranchOffset (z 0) branch) * D (fun k => ((z k).val : ℤ)) -
                  G (fun k => ((z k).val : ℤ))‖) ≤ Real.exp (-r) := by
  obtain ⟨a, _, hmodel⟩ := exists_cubic_factored_model
  obtain ⟨b, _, horbit⟩ := exists_cubic_box_orbit_factors
  obtain ⟨c, _, hglobal⟩ := exists_cubic_box_global_expansion
  obtain ⟨d, _, hcompare⟩ := exists_cubic_kernel_approximation
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  let R := (Q + Polynomial.C b) ^ b
  let T := X + 2 * Q + 2
  let S := (Q + R + T + Polynomial.C c) ^ c
  let U := (Q + S + Polynomial.C d) ^ d
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (3 * Q + R + S + U + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p r hp hr hN f hf hGowers
  let v := p + r
  let q := (v + a) ^ a
  let w := (q + b) ^ b
  let t := v + 2 * q + 2
  let u := (q + w + t + c) ^ c
  let z := (q + u + d) ^ d
  have hv : 0 ≤ v := add_nonneg hp hr
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hz : 0 ≤ z := by dsimp only [z]; positivity
  have hsum : 3 * q + w + u + z + 2 ≤ (p + r + C) ^ C := by
    simpa [X, Q, R, T, S, U, v, q, w, t, u, z, Polynomial.eval₂_pow] using hbudget v hv
  have hqC : q ≤ (p + r + C) ^ C := by linarith only [hsum, hq, hw, hu, hz]
  have hwC : w ≤ (p + r + C) ^ C := by linarith only [hsum, hq, hu, hz]
  have huC : u ≤ (p + r + C) ^ C := by linarith only [hsum, hq, hw, hz]
  have hzC : z ≤ (p + r + C) ^ C := by linarith only [hsum, hq, hw, hu]
  have henergyC : 2 * q + 1 ≤ (p + r + C) ^ C := by linarith only [hsum, hq, hw, hu, hz]
  obtain ⟨H, hH, hHdense, M, V, hdim, hsymm, hdiag, E, out, χ, hcorr, F, hbias⟩ :=
    hmodel hv ((Real.exp_le_exp.mpr hqC).trans hN) f hf
      ((Real.exp_le_exp.mpr (by dsimp only [v]; linarith only [hr])).trans hGowers)
  let := F.topology
  let := F.topologicalAdd
  let := F.continuousSMul
  let := F.hausdorff
  let shift : ℤ := -(if F.branch then (N : ℤ) else 0)
  obtain ⟨O⟩ := horbit V F ((Real.exp_le_exp.mpr hwC).trans hN)
  obtain ⟨B, ⟨EB⟩, hBunit, hBerror⟩ :=
    hglobal V F.leftIndex F.rightIndex shift O hw ht ((Real.exp_le_exp.mpr huC).trans hN)
  have hbias' : Real.exp (-q) ≤ (finiteTripleBoxCorrelation (fun k h y : ZMod N =>
      V.cubicAntisymmetricPair F.leftIndex F.rightIndex h.val y.val ((k.val : ℤ) + shift))).re := by
    simpa only [shift, cyclicBranchOffset, sub_eq_add_neg] using hbias
  obtain ⟨D, G, hD, hG, hDunit, hGunit, hmass, henergy, herr⟩ :=
    hcompare V F.leftIndex F.rightIndex shift B hu EB hBunit
      (Real.exp_pos (-q)) (Real.exp_pos (-t)) hbias' hBerror
  have hdelta : (Real.exp (-q)) ^ 2 = Real.exp (-(2 * q)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hlower : Real.exp (-((p + r + C) ^ C)) ≤ (Real.exp (-q)) ^ 2 / 2 := by
    rw [hdelta]
    exact (Real.exp_le_exp.mpr (by linarith only [henergyC])).trans
      (exp_sub_one_le_half_exp (-(2 * q)))
  have herror : 2 * Real.exp (-t) / (Real.exp (-q)) ^ 2 ≤ Real.exp (-r) := by
    rw [hdelta, mul_div_assoc, ← Real.exp_sub]
    have he : -t - -(2 * q) = -v - 2 := by dsimp only [t]; ring
    rw [he]
    calc
      _ ≤ 2 * (Real.exp (-v) / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact (Real.exp_le_exp.mpr (by linarith : -v - 2 ≤ -v - 1)).trans
          (exp_sub_one_le_half_exp (-v))
      _ = Real.exp (-v) := by ring
      _ ≤ Real.exp (-r) := Real.exp_le_exp.mpr (by dsimp only [v]; linarith only [hp])
  have hK (x : Fin 3 → ZMod N) :
      (V.mono hqC).cubicAntisymmetricPair F.leftIndex F.rightIndex (x 1).val (x 2).val
          (cyclicBranchOffset (x 0) F.branch) =
        V.cubicAntisymmetricPair F.leftIndex F.rightIndex (x 1).val (x 2).val
          (((x 0).val : ℤ) + shift) := by
    simp only [NativeMultidegreeNilcharacter.cubicAntisymmetricPair,
      NativeMultidegreeNilcharacter.mono_eval, cyclicBranchOffset, shift, sub_eq_add_neg]
  refine ⟨H, hH, ?_, M.mono hqC, V.mono hqC, ?_, hsymm, hdiag.mono hqC, E.mono hqC,
    out, χ, ?_, F.branch, F.leftIndex, F.rightIndex, D, G,
    hD.map (fun ED => ED.mono hzC), hG.map (fun EG => EG.mono hzC), hDunit, hGunit,
    hlower.trans hmass, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hHdense
  · change V.dim ≤ 8 * M.dim
    exact hdim
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · simpa only [hK] using hlower.trans henergy
  · simpa only [hK] using herr.trans herror

end Erdos3

end

end OAI
