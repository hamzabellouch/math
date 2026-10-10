import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.Phases
import OAI.MathematicalPhysics.PEPSFilters.Interpolation

namespace OAI

/-! Pinned-sector interpolation and the original-state entropy upper comparison. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
open Set Filter
open scoped Topology
open scoped BigOperators

namespace PolynomialPEPS.PinnedEntropy
open scoped BigOperators Matrix.Norms.L2Operator
open NestedFilter.Spectral

def localMapCLM {L q : ℕ} (A : Finset (Vertex L)) :
    Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ →L[ℂ]
      (State L q →L[ℂ] State L q) :=
  LinearMap.toContinuousLinearMap
    ((Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap.comp
      (liftLocalHom A).toAlgHom.toLinearMap)

@[simp] lemma localMapCLM_apply {L q : ℕ} (A : Finset (Vertex L))
    (B : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) :
    localMapCLM A B = asMap (liftLocal A B) := rfl

lemma asMap_norm {L q : ℕ} (B : Operator L q) : ‖asMap B‖ = ‖B‖ :=
  StarAlgEquiv.norm_map (Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ)) B

lemma asMap_inner_hermitian {L q : ℕ} {B : Operator L q} (hB : B.IsHermitian)
    (v w : State L q) : inner ℂ (asMap B v) w = inner ℂ v (asMap B w) := by
  exact (hB.isSelfAdjoint.map (Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ))).isSymmetric v w

lemma liftLocal_hermitian {L q : ℕ} (A : Finset (Vertex L))
    {B : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ}
    (hB : B.IsHermitian) : (liftLocal A B).IsHermitian :=
  (hB.isSelfAdjoint.map (liftLocalHom A)).isHermitian

lemma inner_projection {L q : ℕ} {P : Operator L q}
    (hP : P.IsHermitian) (hP2 : P * P = P) (v : State L q) :
    inner ℂ (asMap P v) (asMap P v) = inner ℂ v (asMap P v) := by
  rw [asMap_inner_hermitian hP, ← asMap_mul, hP2]

lemma inner_projection_commute {L q : ℕ} {P B : Operator L q}
    (hP : P.IsHermitian) (hP2 : P * P = P) (hPB : Commute P B)
    (v : State L q) :
    inner ℂ (asMap P v) (asMap B (asMap P v)) = inner ℂ v (asMap (B * P) v) := by
  rw [asMap_inner_hermitian hP, ← asMap_mul, ← asMap_mul,
    hPB.eq, mul_assoc, hP2]

lemma pinned_norm_sq {L q : ℕ} (S : Finset (Vertex L)) (Ω : State L q)
    (i : RegionConfiguration q S) :
    ‖asMap (liftLocal S (eigenProjector (reducedDensity_isHermitian Ω S) i)) Ω‖ ^ 2 =
      (reducedDensity_isHermitian Ω S).eigenvalues i := by
  let P := eigenProjector (reducedDensity_isHermitian Ω S) i
  have hP : P.IsHermitian := (eigenProjector_positive _ _).isHermitian
  have hp2 : liftLocal S P * liftLocal S P = liftLocal S P := by
    rw [← liftLocal_mul, eigenProjector_sq]
  have hi := inner_projection (liftLocal_hermitian S hP) hp2 Ω
  rw [inner_asMap_liftLocal, eigenProjector_mul_self, Matrix.trace_smul,
    eigenProjector_trace, smul_eq_mul, mul_one] at hi
  rw [inner_self_eq_norm_sq_to_K] at hi
  simpa only [P, RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.ofReal_re]
    using congrArg Complex.re hi

lemma regionCorner_calculus {L q : ℕ} {S T : Finset (Vertex L)} (hST : S ⊆ T)
    (P : Matrix (RegionConfiguration q S) (RegionConfiguration q S) ℂ)
    (hP : P.IsHermitian) (hP2 : P * P = P)
    {B : Matrix (RegionConfiguration q (T \ S)) (RegionConfiguration q (T \ S)) ℂ}
    (hB : B.IsHermitian) (f : ℝ → ℂ) (hf : f 0 = 0) :
    applyFn (hB.isSelfAdjoint.map (regionCornerHom hST P hP hP2)).isHermitian f =
      regionTensor hST P (applyFn hB f) :=
  (applyFn_map hB (regionCornerHom hST P hP hP2) f hf).symm

lemma original_support_fixes {L q : ℕ} (Ω : State L q) (A : Finset (Vertex L)) (a : ℝ) :
    asMap (liftLocal A (applyFn (reducedDensity_isHermitian Ω A)
      (fun x => scalarPower a x 0))) Ω = Ω :=
  asMap_liftLocal_fix_of_mul_density A _ Ω (power_zero_mul_self _ a)

lemma corner_power_fixes {L q : ℕ} {S T : Finset (Vertex L)} (hST : S ⊆ T)
    (P : Matrix (RegionConfiguration q S) (RegionConfiguration q S) ℂ)
    (_hP : P.IsHermitian) (hP2 : P * P = P)
    (Ω : State L q) (a : ℝ) :
    asMap (liftLocal T (regionTensor hST P (applyFn (reducedDensity_isHermitian Ω (T \ S))
      (fun x => scalarPower a x 0)))) (asMap (liftLocal S P) Ω) = asMap (liftLocal S P) Ω := by
  rw [lift_regionTensor, ← asMap_mul]
  have hc := lift_core_shell_commute hST P
    (applyFn (reducedDensity_isHermitian Ω (T \ S)) (fun x => scalarPower a x 0))
  rw [mul_assoc, ← hc.eq, ← mul_assoc, ← liftLocal_mul, hP2, asMap_mul,
    original_support_fixes]

lemma ground_log_expectation {L q : ℕ} (Ω : State L q) (A : Finset (Vertex L)) :
    (inner ℂ Ω (asMap (liftLocal A
      (applyFn (reducedDensity_isHermitian Ω A) (fun x => (Real.log x : ℂ)))) Ω)).re =
      -vonNeumannEntropy Ω A := by
  rw [inner_asMap_liftLocal]
  conv_lhs => arg 1; arg 1; arg 2; rw [← applyFn_id (reducedDensity_isHermitian Ω A)]
  rw [← applyFn_mul, applyFn_trace, Complex.re_sum]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    vonNeumannEntropy, Real.negMulLog_def, ← Finset.sum_neg_distrib, neg_mul, neg_neg]
  apply Finset.sum_congr rfl
  intro i _
  ring

end PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Spectral
open scoped Matrix.Norms.L2Operator
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma applyFn_smul {A : Matrix n n ℂ} (hA : A.IsHermitian) (c : ℂ) (f : ℝ → ℂ) :
    applyFn hA (fun x => c * f x) = c • applyFn hA f := by
  unfold applyFn
  rw [← map_smul, ← Matrix.diagonal_smul]
  rfl

end PolynomialPEPS.PinnedEntropy.NestedFilter.Spectral

namespace PolynomialPEPS.PinnedEntropy
open scoped BigOperators Matrix.Norms.L2Operator
open NestedFilter.Spectral

lemma corner_right_projection {L q : ℕ} {S T : Finset (Vertex L)} (hST : S ⊆ T)
    (P : Matrix (RegionConfiguration q S) (RegionConfiguration q S) ℂ) (hP2 : P * P = P)
    (B : Matrix (RegionConfiguration q (T \ S)) (RegionConfiguration q (T \ S)) ℂ) :
    liftLocal T (regionTensor hST P B) * liftLocal S P = liftLocal T (regionTensor hST P B) := by
  rw [← lift_regionTensor_one_right hST, ← liftLocal_mul, ← regionTensor_mul, hP2, mul_one]

lemma corner_log_derivative {L q : ℕ} {S T : Finset (Vertex L)} (hST : S ⊆ T)
    (P : Matrix (RegionConfiguration q S) (RegionConfiguration q S) ℂ)
    (hP : P.IsHermitian) (hP2 : P * P = P)
    (Ω : State L q) (a : ℝ) :
    inner ℂ (asMap (liftLocal S P) Ω)
      (asMap (liftLocal T (regionTensor hST P
        (applyFn (reducedDensity_isHermitian Ω (T \ S))
          (fun x => ((a / 2 * Real.log x : ℝ) : ℂ))))) (asMap (liftLocal S P) Ω)) =
    ((a / 2 : ℝ) : ℂ) * inner ℂ (asMap (liftLocal S P) Ω)
      (asMap (liftLocal (T \ S)
        (applyFn (reducedDensity_isHermitian Ω (T \ S))
          (fun x => (Real.log x : ℂ)))) (asMap (liftLocal S P) Ω)) := by
  rw [lift_regionTensor, asMap_mul, ← asMap_inner_hermitian (liftLocal_hermitian S hP),
    ← asMap_mul, ← liftLocal_mul, hP2]
  simp only [Complex.ofReal_mul]
  rw [applyFn_smul]
  change inner ℂ _ (localMapCLM (T \ S) (((a / 2 : ℝ) : ℂ) •
    applyFn (reducedDensity_isHermitian Ω (T \ S)) (fun x => (Real.log x : ℂ))) _) = _
  rw [map_smul, _root_.smul_apply, inner_smul_right]
  rfl

end PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.PinnedEntropy.NestedFilter
open scoped BigOperators Matrix.Norms.L2Operator
open Spectral Analytic

theorem pinned_sector_comparison {L q m : ℕ} [NeZero q]
    {S : Finset (Vertex L)} {X : Fin (m+1) → Finset (Vertex L)}
    (hST : ∀ j, S ⊆ X j) (hX : Monotone X)
    {Ω : State L q} (hΩ : ‖Ω‖ = 1)
    {a : Fin (m+1) → ℝ} (ha : ∀ j, 0 < a j)
    {F : FilterFamily q (m+1) X} (hF : IsMaximizer Ω a F)
    (P : Matrix (RegionConfiguration q S) (RegionConfiguration q S) ℂ)
    (hP : P.PosSemidef) (hP2 : P * P = P) (hPtr : P.trace = 1)
    (hv : asMap (liftLocal S P) Ω ≠ 0) :
    Real.log (‖asMap (liftLocal S P) Ω‖ ^ 2) +
      (∑ j, a j * (inner ℂ (asMap (liftLocal S P) Ω)
        (asMap (liftLocal (X j \ S)
          (applyFn (reducedDensity_isHermitian Ω (X j \ S))
            (fun x => (Real.log x : ℂ)))) (asMap (liftLocal S P) Ω))).re) /
          ‖asMap (liftLocal S P) Ω‖ ^ 2 ≤ Real.log (‖output F Ω‖ ^ 2) := by
  let v := asMap (liftLocal S P) Ω
  let R (j : Fin (m+1)) := regionTensor (hST j) P (reducedDensity Ω (X j \ S))
  have hR (j : Fin (m+1)) : (R j).PosSemidef :=
    regionTensor_positive (hST j) hP (reducedDensity_posSemidef _ _)
  have htr (j : Fin (m+1)) : (R j).trace = 1 := by
    dsimp only [R]
    rw [regionTensor_trace, hPtr, trace_reducedDensity, hΩ]
    norm_num
  have hnat (j : Fin (m+1)) (f : ℝ → ℂ) (hf : f 0 = 0) :
      applyFn (hR j).isHermitian f = regionTensor (hST j) P
        (applyFn (reducedDensity_isHermitian Ω (X j \ S)) f) :=
    regionCorner_calculus (hST j) P hP.isHermitian hP2 _ f hf
  let T (j : Fin (m+1)) (z : ℂ) :=
    localMapCLM (X j) (applyFn (hR j).isHermitian (fun x => scalarPower (a j) x z))
  let D (j : Fin (m+1)) :=
    localMapCLM (X j) (applyFn (hR j).isHermitian (fun x => ((a j / 2 * Real.log x : ℝ) : ℂ)))
  have hTeq (j : Fin (m+1)) (z : ℂ) : T j z = asMap (liftLocal (X j)
      (regionTensor (hST j) P (applyFn (reducedDensity_isHermitian Ω (X j \ S))
        (fun x => scalarPower (a j) x z)))) := by
    dsimp [T]
    rw [hnat j _ (by simp [scalarPower])]
  have hproj (j : Fin (m+1)) (z : ℂ) : T j z v = T j z Ω := by
    rw [hTeq]
    change asMap _ (asMap (liftLocal S P) Ω) = _
    rw [← asMap_mul, corner_right_projection (hST j) P hP2]
  have hfix (j : Fin (m+1)) : T j 0 v = v := by
    rw [hTeq]
    exact corner_power_fixes (hST j) P hP.isHermitian hP2 Ω (a j)
  have hstrip (j : Fin (m+1)) (w : State L q) : inner ℂ v (T j 0 w) = inner ℂ v w := by
    have hh : (liftLocal (X j)
        (applyFn (hR j).isHermitian (fun x => scalarPower (a j) x 0))).IsHermitian :=
      liftLocal_hermitian _ (power_zero_hermitian _ _)
    change inner ℂ v (asMap (liftLocal (X j)
      (applyFn (hR j).isHermitian (fun x => scalarPower (a j) x 0))) w) = _
    rw [← asMap_inner_hermitian hh]
    exact congrArg (fun u => inner ℂ u w) (hfix j)
  have hentire (j : Fin (m+1)) : Differentiable ℂ (T j) :=
    (localMapCLM (X j)).differentiable.comp (power_entire (hR j).isHermitian (a j))
  have hderiv (j : Fin (m+1)) : HasDerivAt (T j) (D j) 0 :=
    (localMapCLM (X j)).hasFDerivAt.comp_hasDerivAt 0 (power_hasDerivAt_zero (hR j).isHermitian (a j))
  have hnorm (j : Fin (m+1)) (z : ℂ) (hz : 0 ≤ z.re) : ‖T j z‖ ≤ 1 := by
    dsimp [T]
    rw [asMap_norm, liftLocal_norm]
    exact power_norm_le_one (hR j) (htr j) (ha j).le hz
  have hright (z : ℂ) (hz : z.re = 1) : ‖chain (fun j => T j z) v‖ ≤ ‖output F Ω‖ := by
    have hstart : chain (fun j => T j z) v = chain (fun j => T j z) Ω := by
      rw [chain_succ, chain_succ, hproj 0 z]
    rw [hstart]
    let G : FilterFamily q (m+1) X := fun j =>
      ⟨applyFn (hR j).isHermitian (fun x => scalarPower (a j) x 1), power_one_positive (hR j) (ha j)⟩
    let U : Fin (m+1) → Operator L q := fun j =>
      liftLocal (X j) (applyFn (hR j).isHermitian (fun x => scalarPhase (a j) x z.im))
    have hG : Admissible a G := fun j => power_one_tracePower (hR j) (htr j) (ha j)
    have hUs (j : Fin (m+1)) : SupportedOn (U j) (X j) := ⟨_, rfl⟩
    have hUu (j : Fin (m+1)) : U j ∈ unitary _ := liftLocal_unitary _ (spectralPhase_unitary _ _ _)
    have he (j : Fin (m+1)) :
        liftLocal (X j) (applyFn (hR j).isHermitian (fun x => scalarPower (a j) x z)) =
          U j * liftLocal (X j) (G j).matrix := by
      rw [power_right _ _ hz, liftLocal_mul]
    change ‖matrixOutput (fun j => liftLocal (X j)
      (applyFn (hR j).isHermitian (fun x => scalarPower (a j) x z))) Ω‖ ≤ _
    simp only [he]
    exact twisted_norm_le_maximizer hX hF G hG U hUs hUu
  have ht := chain_entropy_tangent_nonneg T D hv (norm_nonneg _) hentire hderiv hfix hstrip hnorm hright
  have hdi (j : Fin (m+1)) : inner ℂ v (D j v) =
      ((a j / 2 : ℝ) : ℂ) * inner ℂ v (asMap (liftLocal (X j \ S)
        (applyFn (reducedDensity_isHermitian Ω (X j \ S)) (fun x => (Real.log x : ℂ)))) v) := by
    dsimp [D]
    rw [hnat j _ (by simp)]
    exact corner_log_derivative (hST j) P hP.isHermitian hP2 Ω (a j)
  have hs : 2 * (∑ j, inner ℂ v (D j v)).re =
      ∑ j, a j * (inner ℂ v (asMap (liftLocal (X j \ S)
        (applyFn (reducedDensity_isHermitian Ω (X j \ S)) (fun x => (Real.log x : ℂ)))) v)).re := by
    rw [Complex.re_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hdi, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  rw [hs] at ht
  exact ht

end PolynomialPEPS.PinnedEntropy.NestedFilter

namespace PolynomialPEPS.PinnedEntropy
open scoped BigOperators Matrix.Norms.L2Operator
open NestedFilter.Spectral

lemma asMap_sum {L q : ℕ} {ι : Type*} [Fintype ι] (B : ι → Operator L q) (v : State L q) :
    asMap (∑ i, B i) v = ∑ i, asMap (B i) v := by
  change Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ) (∑ i, B i) v = _
  rw [map_sum, _root_.sum_apply]
  rfl

lemma pinned_expectation_sum {L q : ℕ} {S T : Finset (Vertex L)} (hST : S ⊆ T)
    (Ω : State L q)
    (B : Matrix (RegionConfiguration q (T \ S)) (RegionConfiguration q (T \ S)) ℂ) :
    (∑ i, inner ℂ (asMap (liftLocal S (eigenProjector (reducedDensity_isHermitian Ω S) i)) Ω)
      (asMap (liftLocal (T \ S) B)
        (asMap (liftLocal S (eigenProjector (reducedDensity_isHermitian Ω S) i)) Ω))) =
      inner ℂ Ω (asMap (liftLocal (T \ S) B) Ω) := by
  let P (i : RegionConfiguration q S) := liftLocal S (eigenProjector (reducedDensity_isHermitian Ω S) i)
  have hsum : ∑ i, P i = 1 := by
    change (∑ i, liftLocalHom S (eigenProjector (reducedDensity_isHermitian Ω S) i)) = 1
    rw [← map_sum, eigenProjector_sum, map_one]
  have he (i : RegionConfiguration q S) :
      inner ℂ (asMap (P i) Ω) (asMap (liftLocal (T \ S) B) (asMap (P i) Ω)) =
        inner ℂ Ω (asMap (liftLocal (T \ S) B * P i) Ω) := by
    apply inner_projection_commute
    · exact liftLocal_hermitian S (eigenProjector_positive _ _).isHermitian
    · dsimp only [P]
      rw [← liftLocal_mul, eigenProjector_sq]
    · exact lift_core_shell_commute hST _ B
  change (∑ i, inner ℂ (asMap (P i) Ω) (asMap (liftLocal (T \ S) B) (asMap (P i) Ω))) = _
  simp only [he]
  rw [← inner_sum, ← asMap_sum, ← Finset.mul_sum, hsum, mul_one]

end PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.PinnedEntropy.NestedFilter
open scoped BigOperators Matrix.Norms.L2Operator
open Spectral

theorem upperComparison_zero {L q m : ℕ} [NeZero q]
    {S : Finset (Vertex L)} {X : Fin (m+1) → Finset (Vertex L)}
    (hST : ∀ j, S ⊆ X j) (hX : Monotone X)
    {Ω : State L q} (hΩ : ‖Ω‖ = 1)
    {a : Fin (m+1) → ℝ} (ha : ∀ j, 0 < a j)
    {F : FilterFamily q (m+1) X} (hF : IsMaximizer Ω a F) (r : ℝ) :
    UpperComparison S Ω a F 0 r := by
  classical
  let p (i : RegionConfiguration q S) := (reducedDensity_isHermitian Ω S).eigenvalues i
  let v (i : RegionConfiguration q S) :=
    asMap (liftLocal S (eigenProjector (reducedDensity_isHermitian Ω S) i)) Ω
  let b (i : RegionConfiguration q S) (j : Fin (m+1)) :=
    (inner ℂ (v i) (asMap (liftLocal (X j \ S)
      (applyFn (reducedDensity_isHermitian Ω (X j \ S)) (fun x => (Real.log x : ℂ)))) (v i))).re
  have hp (i) : 0 ≤ p i := (reducedDensity_posSemidef S Ω).eigenvalues_nonneg i
  have hpn (i) : ‖v i‖ ^ 2 = p i := pinned_norm_sq S Ω i
  have hpsum : ∑ i, p i = 1 := by
    exact density_eigenvalues_sum (reducedDensity_posSemidef S Ω) (by
      rw [trace_reducedDensity, hΩ]
      norm_num)
  have hsector (i) : p i * Real.log (p i) + ∑ j, a j * b i j ≤
      p i * Real.log (‖output F Ω‖ ^ 2) := by
    rcases eq_or_lt_of_le (hp i) with hzero | hpos
    · have hv : v i = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (v i), hpn i])
      simp [← hzero, b, hv]
    have hv : v i ≠ 0 := by
      intro hv
      have hn := hpn i
      rw [hv, norm_zero, sq, zero_mul] at hn
      exact (ne_of_gt hpos) hn.symm
    have hh := pinned_sector_comparison hST hX hΩ ha hF
      (eigenProjector (reducedDensity_isHermitian Ω S) i)
      (eigenProjector_positive _ _) (eigenProjector_sq _ _) (eigenProjector_trace _ _) hv
    change Real.log (‖v i‖ ^ 2) + (∑ j, a j * b i j) / ‖v i‖ ^ 2 ≤ _ at hh
    rw [hpn] at hh
    calc
      p i * Real.log (p i) + ∑ j, a j * b i j =
          p i * (Real.log (p i) + (∑ j, a j * b i j) / p i) := by
        field_simp [ne_of_gt hpos]
      _ ≤ p i * Real.log (‖output F Ω‖ ^ 2) := mul_le_mul_of_nonneg_left hh (hp i)
  have hlogs : (∑ i, p i * Real.log (p i)) = -vonNeumannEntropy Ω S := by
    simp only [vonNeumannEntropy, Real.negMulLog_def, p, neg_mul,
      Finset.sum_neg_distrib, neg_neg]
  have hb (j : Fin (m+1)) : (∑ i, b i j) = -vonNeumannEntropy Ω (X j \ S) := by
    dsimp only [b, v]
    rw [← Complex.re_sum, pinned_expectation_sum (hST j), ground_log_expectation]
  have hbsum : (∑ i, ∑ j, a j * b i j) =
      -(∑ j, a j * vonNeumannEntropy Ω (X j \ S)) := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hb, mul_neg, Finset.sum_neg_distrib]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hsector i)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hpsum, one_mul, hlogs, hbsum] at hsum
  unfold UpperComparison logCost
  simp only [zero_mul, add_zero]
  linarith

end PolynomialPEPS.PinnedEntropy.NestedFilter

end

end OAI
