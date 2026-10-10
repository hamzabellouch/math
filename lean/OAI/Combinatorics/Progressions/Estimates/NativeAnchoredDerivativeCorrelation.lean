import OAI.Combinatorics.Progressions.Estimates.CorrelatingVerticalPair

namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

def nativeAnchorBudget (b : ℝ) : ℝ :=
  productNiltestBudget (raisedNiltestBudget (b + 2)) + b + 2

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

def HasNativeCorrelatingAnchor (f : ZMod N → ℂ) (H : Finset (ZMod N)) (b : ℝ) : Prop :=
  ∃ y : Fin 2 → ZMod N, ∃ S : Finset (ZMod N), S ⊆ H ∧ S.Nonempty ∧
    Real.exp (-b) * N ≤ (S.card : ℝ) ∧
    NativeIntegerVectorEquivalence 1 b
      (R.pairAnchoredVector (fun k => ((y k).val : ℤ)) 0)
      (R.pairAnchoredVector (fun k => ((y k).val : ℤ)) 1) ∧
    ∀ h ∈ S, Nonempty (NativeVectorCorrelation 1 N b
      (fun out n => multiplicativeDerivative f h n *
        star (R.pairAnchoredVector (fun k => ((y k).val : ℤ)) 0 out
          ![(h.val : ℤ), (n.val : ℤ)])))

theorem hasNativeCorrelatingAnchor_of_weighted {b : ℝ} {f : ZMod N → ℂ}
    {H : Finset (ZMod N)} {out : Fin W.outputDim} (hb : 0 ≤ b)
    (h : R.HasCorrelatingAnchor f H out b) :
    R.HasNativeCorrelatingAnchor f H (nativeAnchorBudget b) := by
  obtain ⟨y, S, hSH, hS, hsize, w, hw, hequiv, hcorr⟩ := h
  have hbase : 2 ≤ b + 2 := by linarith
  have hbb : b ≤ b + 2 := by linarith
  have hprod : 0 ≤ productNiltestBudget (raisedNiltestBudget (b + 2)) := by
    unfold productNiltestBudget productObservableLipBudget raisedNiltestBudget
    positivity
  have hbf : b ≤ nativeAnchorBudget b := by unfold nativeAnchorBudget; linarith
  have hpf : productNiltestBudget (raisedNiltestBudget (b + 2)) ≤ nativeAnchorBudget b := by
    unfold nativeAnchorBudget
    linarith
  refine ⟨y, S, hSH, hS,
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hbf))
      (Nat.cast_nonneg N)).trans hsize, hequiv.mono hbf, ?_⟩
  intro h hh
  let F := fun (j : Fin W.outputDim) (n : ZMod N) => multiplicativeDerivative f h n *
    star (R.pairAnchoredVector (fun k => ((y k).val : ℤ)) 0 j ![(h.val : ℤ), (n.val : ℤ)])
  have hpoint (n : ZMod N) : (w n : ℂ) * F out n =
      multiplicativeDerivative f h n *
        star ((w n : ℂ) * R.pairAnchoredVector (fun k => ((y k).val : ℤ)) 0 out
          ![(h.val : ℤ), (n.val : ℤ)]) := by
    simp only [F, star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  have hmean : Real.exp (-(b + 2)) ≤ ‖𝔼 n : ZMod N, (w n : ℂ) * F out n‖ := by
    simpa only [hpoint] using
      (Real.exp_le_exp.mpr (neg_le_neg hbb)).trans (hcorr h hh)
  obtain ⟨T⟩ := NativeVectorCorrelation.exists_of_mean 1 N (fun j n => (w n : ℂ) * F j n)
    hbase ⟨out, hmean⟩
  obtain ⟨U⟩ := NativeVectorCorrelation.exists_absorb_positive F w hbase (hw.mono le_rfl hbb) T
  exact ⟨U.mono hpf⟩

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI
