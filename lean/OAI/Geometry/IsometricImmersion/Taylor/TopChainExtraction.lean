import OAI.Geometry.IsometricImmersion.Taylor.ChainResidual
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation

theorem ChainWord.prepend_single (n : ℕ) :
    (ChainWord.single n).prepend = ChainWord.pair 1 n := rfl

theorem ChainWord.bump_single (n : ℕ) :
    (ChainWord.single n).bump (0 : Fin 1) = ChainWord.single (n + 1) := by
  change ChainWord.mk 1 _ = ChainWord.mk 1 _
  congr 1
  ext i
  fin_cases i
  simp [ChainWord.single]

theorem ChainWord.prepend_pair (a b : ℕ) :
    (ChainWord.pair a b).prepend = ChainWord.triple 1 a b := rfl

theorem ChainWord.bump_pair_zero (a b : ℕ) :
    (ChainWord.pair a b).bump (0 : Fin 2) = ChainWord.pair (a + 1) b := by
  apply congrArg (ChainWord.mk 2)
  change Function.update (![a, b] : Fin 2 → ℕ) (0 : Fin 2) (a + 1) = ![a + 1, b]
  funext i
  fin_cases i <;> simp

theorem ChainWord.bump_pair_one (a b : ℕ) :
    (ChainWord.pair a b).bump (1 : Fin 2) = ChainWord.pair a (b + 1) := by
  change ChainWord.mk 2 _ = ChainWord.mk 2 _
  congr 1
  ext i
  fin_cases i <;> simp [ChainWord.pair]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem chainTerm_single_eq (F : E → ℝ) (J : ℝ → E) (n : ℕ) (t : ℝ) :
    chainTerm F J (ChainWord.single n) t =
      fderiv ℝ F (J t) (iteratedDeriv n J t) := by
  simp only [chainTerm, ChainWord.single, Matrix.cons_val_fin_one]
  exact iteratedFDeriv_one_apply (𝕜 := ℝ) (f := F) (x := J t)
    (fun _ : Fin 1 => iteratedDeriv n J t)

theorem chainTerm_pair_eq (F : E → ℝ) (J : ℝ → E) (a b : ℕ) (t : ℝ) :
    chainTerm F J (ChainWord.pair a b) t =
      iteratedFDeriv ℝ 2 F (J t) ![iteratedDeriv a J t, iteratedDeriv b J t] := by
  apply congrArg (iteratedFDeriv ℝ 2 F (J t))
  ext i
  fin_cases i <;> rfl

theorem chainTerm_triple_eq (F : E → ℝ) (J : ℝ → E) (a b c : ℕ) (t : ℝ) :
    chainTerm F J (ChainWord.triple a b c) t =
      iteratedFDeriv ℝ 3 F (J t)
        ![iteratedDeriv a J t, iteratedDeriv b J t, iteratedDeriv c J t] := by
  apply congrArg (iteratedFDeriv ℝ 3 F (J t))
  ext i
  fin_cases i <;> rfl

theorem chainTerm_pair_symm {F : E → ℝ} (J : ℝ → E) {t : ℝ}
    (hF : ContDiffAt ℝ ∞ F (J t)) (a b : ℕ) :
    chainTerm F J (ChainWord.pair a b) t = chainTerm F J (ChainWord.pair b a) t := by
  rw [chainTerm_pair_eq, chainTerm_pair_eq]
  have hs := hF.isSymmSndFDerivAt (by
    simp only [minSmoothness, ite_eq_left (inferInstance : IsRCLikeNormedField ℝ)]
    exact WithTop.coe_le_coe.mpr le_top)
  exact hs.iteratedFDeriv_cons

theorem chainTerm_single_hasDerivAt {F : E → ℝ} {J : ℝ → E} {t : ℝ}
    (hF : ContDiffAt ℝ ∞ F (J t)) (hJ : ContDiffAt ℝ ∞ J t) (n : ℕ) :
    HasDerivAt (chainTerm F J (ChainWord.single n))
      (chainTerm F J (ChainWord.single (n + 1)) t +
        chainTerm F J (ChainWord.pair 1 n) t) t := by
  have h := chainTerm_hasDerivAt hF hJ (ChainWord.single n)
  change HasDerivAt _
    (chainTerm F J (ChainWord.single n).prepend t +
      ∑ i : Fin 1, chainTerm F J ((ChainWord.single n).bump i) t) t at h
  simpa only [Fin.sum_univ_one, ChainWord.prepend_single, ChainWord.bump_single,
    add_comm] using h

theorem chainTerm_pair_hasDerivAt {F : E → ℝ} {J : ℝ → E} {t : ℝ}
    (hF : ContDiffAt ℝ ∞ F (J t)) (hJ : ContDiffAt ℝ ∞ J t) (a b : ℕ) :
    HasDerivAt (chainTerm F J (ChainWord.pair a b))
      (chainTerm F J (ChainWord.triple 1 a b) t +
        chainTerm F J (ChainWord.pair (a + 1) b) t +
        chainTerm F J (ChainWord.pair a (b + 1)) t) t := by
  have h := chainTerm_hasDerivAt hF hJ (ChainWord.pair a b)
  change HasDerivAt _
    (chainTerm F J (ChainWord.pair a b).prepend t +
      ∑ i : Fin 2, chainTerm F J ((ChainWord.pair a b).bump i) t) t at h
  simpa only [Fin.sum_univ_two, ChainWord.prepend_pair, ChainWord.bump_pair_zero,
    ChainWord.bump_pair_one, add_assoc] using h

theorem top_chain_three {F : E → ℝ} {J : ℝ → E} {t : ℝ}
    (hF : ContDiffAt ℝ ∞ F (J t)) (hJ : ContDiffAt ℝ ∞ J t) :
    iteratedDeriv 3 (F ∘ J) t =
      chainTerm F J (ChainWord.single 3) t +
        3 * chainTerm F J (ChainWord.pair 1 2) t +
        chainSum F J (topResidualWords 0) t := by
  have h := iteratedDeriv_vcomp_three
    (hF.of_le (WithTop.coe_le_coe.mpr le_top))
    (hJ.of_le (WithTop.coe_le_coe.mpr le_top))
  have heq : iteratedDeriv 3 (F ∘ J) t =
      chainTerm F J (ChainWord.triple 1 1 1) t +
      chainTerm F J (ChainWord.pair 2 1) t +
      2 * chainTerm F J (ChainWord.pair 1 2) t +
      chainTerm F J (ChainWord.single 3) t := by
    rw [chainTerm_triple_eq, chainTerm_pair_eq, chainTerm_pair_eq, chainTerm_single_eq]
    simp only [iteratedDeriv_one, two_smul, two_mul] at h ⊢
    convert h using 1
    have hv : (![deriv J t, deriv J t, deriv J t] : Fin 3 → E) = fun _ => deriv J t := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
  rw [chainTerm_pair_symm J hF 2 1] at heq
  simp only [topResidualWords, chainSum, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  linarith [heq]

theorem top_chain_expansion
    {F : E → ℝ} {J : ℝ → E} {O : Set E} {I : Set ℝ}
    (hO : IsOpen O) (hI : IsOpen I) (hF : ContDiffOn ℝ ∞ F O)
    (hJ : ContDiffOn ℝ ∞ J I) (hmap : MapsTo J I O) :
    ∀ m t, t ∈ I →
      iteratedDeriv (m + 3) (F ∘ J) t =
        chainTerm F J (ChainWord.single (m + 3)) t +
          (m + 3 : ℝ) * chainTerm F J (ChainWord.pair 1 (m + 2)) t +
          chainSum F J (topResidualWords m) t := by
  intro m
  induction m with
  | zero =>
    intro t ht
    simpa only [Nat.zero_add, Nat.cast_zero, zero_add] using top_chain_three (hF.contDiffAt (hO.mem_nhds (hmap ht)))
      (hJ.contDiffAt (hI.mem_nhds ht))
  | succ m ih =>
    intro t ht
    have hFt := hF.contDiffAt (hO.mem_nhds (hmap ht))
    have hJt := hJ.contDiffAt (hI.mem_nhds ht)
    have heq : iteratedDeriv (m + 3) (F ∘ J) =ᶠ[𝓝 t]
        (fun r => chainTerm F J (ChainWord.single (m + 3)) r +
          (m + 3 : ℝ) * chainTerm F J (ChainWord.pair 1 (m + 2)) r +
          chainSum F J (topResidualWords m) r) := by
      filter_upwards [hI.mem_nhds ht] with r hr
      exact ih r hr
    have hd := ((chainTerm_single_hasDerivAt hFt hJt (m + 3)).add
      ((chainTerm_pair_hasDerivAt hFt hJt 1 (m + 2)).const_mul (m + 3 : ℝ))).add
      (chainSum_hasDerivAt hFt hJt (topResidualWords m))
    have hd' := hd.deriv
    change deriv (fun r => chainTerm F J (ChainWord.single (m + 3)) r +
      (m + 3 : ℝ) * chainTerm F J (ChainWord.pair 1 (m + 2)) r +
      chainSum F J (topResidualWords m) r) t = _ at hd'
    rw [show m + 1 + 3 = (m + 3) + 1 by omega, iteratedDeriv_succ, heq.deriv_eq, hd']
    rw [topResidualWords_sum_succ]
    simp only [Nat.cast_add, Nat.add_assoc, Nat.reduceAdd]
    ring

theorem actualP_top_chain_expansion
    {g : SmoothLocal.Geometry.MetricField} {z : SmoothLocal.Geometry.Coord → ℝ}
    {U : Set SmoothLocal.Geometry.Coord} {x y : ℝ}
    (hg : SmoothLocal.Geometry.SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, SmoothLocal.Geometry.covHessian g z p 1 1 ≠ 0)
    (hp : (![x, y] : SmoothLocal.Geometry.Coord) ∈ U) (m : ℕ) :
    iteratedDeriv (m + 3) (sixVariableP g ∘ solutionJetCurve z x) y =
      chainTerm (sixVariableP g) (solutionJetCurve z x) (ChainWord.single (m + 3)) y +
      (m + 3 : ℝ) * chainTerm (sixVariableP g) (solutionJetCurve z x)
        (ChainWord.pair 1 (m + 2)) y +
      chainSum (sixVariableP g) (solutionJetCurve z x) (topResidualWords m) y := by
  let I : Set ℝ := {t | (![x, t] : SmoothLocal.Geometry.Coord) ∈ U}
  have hI : IsOpen I := hU.preimage (verticalPoint_contDiff x).continuous
  have hJ : ContDiffOn ℝ ∞ (solutionJetCurve z x) I := by
    intro t ht
    exact (solutionJetCurve_contDiffAt hU hz ht).contDiffWithinAt
  have hmap : MapsTo (solutionJetCurve z x) I (darbouxStateDomain g U) := by
    intro t ht
    exact solutionJet_mem_domain g z ht (hyy _ ht)
  exact top_chain_expansion (darbouxStateDomain_isOpen hg hU) hI
    (sixVariableP_contDiffOn hg hU) hJ hmap m y hp

end SmoothLocal.HighEquation

end

end OAI
