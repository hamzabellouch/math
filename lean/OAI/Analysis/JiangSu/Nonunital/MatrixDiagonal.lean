import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nonunital.RankIdentification

namespace OAI


noncomputable section
namespace NonunitalGamma
open Filter Topology TraceCone
open scoped ComplexOrder ENNReal NNReal CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def diagonalHom : (ι → A) →⋆ₙₐ[ℂ] CStarMatrix ι ι A where
  toFun a := CStarMatrix.ofMatrix (Matrix.diagonal a)
  map_zero' := by ext i j;simp
  map_add' a b := by ext i j;by_cases hij : i=j <;> simp [Matrix.diagonal,hij]
  map_smul' z a := by ext i j;by_cases hij : i=j <;> simp [Matrix.diagonal,hij]
  map_mul' a b := by
    ext i j
    change Matrix.diagonal (fun k => a k*b k) i j=(Matrix.diagonal a*Matrix.diagonal b) i j
    rw [Matrix.diagonal_mul_diagonal]
  map_star' a := by
    ext i j
    by_cases hij : i=j <;> simp [CStarMatrix.star_apply,Matrix.diagonal,hij,eq_comm]

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma diagonalHom_apply (a : ι → A) (i j : ι) :
    diagonalHom a i j=if i=j then a i else 0 := rfl

lemma diagonalHom_nonneg (a : ι → A) (ha : ∀ i,0 ≤ a i) : 0 ≤ diagonalHom a :=
  map_nonneg diagonalHom ha
lemma diagonalHom_norm_le_one (a : ι → A) (ha : ∀ i,‖a i‖ ≤ 1) : ‖diagonalHom a‖ ≤ 1 :=
  (NonUnitalStarAlgHom.norm_apply_le diagonalHom a).trans ((pi_norm_le_iff_of_nonneg zero_le_one).mpr ha)

def evalHom (i : ι) : (ι → A) →⋆ₙₐ[ℂ] A := Pi.evalNonUnitalStarAlgHom ℂ (fun _ : ι => A) i

private noncomputable abbrev realPower {B : Type*} [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] (b : B) (r : ℝ≥0) : B := CFC.nnrpow b r

lemma diagonal_power (a : ι → A) (ha : ∀ i,0 ≤ a i) (r : ℝ≥0) (hr : 0 < r) :
    realPower (diagonalHom a) r=diagonalHom (fun i => CFC.nnrpow (a i) r) := by
  have hd := congrArg Subtype.val (Positive.map_power diagonalHom ⟨a,ha⟩ r hr)
  change diagonalHom (CFC.nnrpow a r)=realPower (diagonalHom a) r at hd
  rw [←hd]
  congr 1
  funext i
  have hi := congrArg Subtype.val (Positive.map_power (evalHom i) ⟨a,ha⟩ r hr)
  exact hi

lemma matrixTrace_diagonal (τ : ExtendedTrace A) (a : ι → A) (ha : ∀ i,0 ≤ a i) :
    τ.matrixTrace ι ⟨diagonalHom a,diagonalHom_nonneg a ha⟩=∑ i,τ ⟨a i,ha i⟩ := by
  rw [ExtendedTrace.matrixTrace_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Subtype.ext
  simp [Positive.matrixDiagonal]

lemma matrixRank_diagonal (τ : ExtendedTrace A) (a : ι → A) (ha : ∀ i,0 ≤ a i) :
    (τ.matrixTrace ι).rank ⟨diagonalHom a,diagonalHom_nonneg a ha⟩=∑ i,τ.rank ⟨a i,ha i⟩ := by
  have ht := tendsto_finsetSum Finset.univ (fun i _ => τ.tendsto_roots_rank_all ⟨a i,ha i⟩)
  apply tendsto_nhds_unique ((τ.matrixTrace ι).tendsto_roots_rank_all
    ⟨diagonalHom a,diagonalHom_nonneg a ha⟩)
  convert ht using 1
  funext n
  have he : Positive.power (Positive.rootExponent n) ⟨diagonalHom a,diagonalHom_nonneg a ha⟩=
      ⟨diagonalHom (fun i => CFC.nnrpow (a i) (Positive.rootExponent n)),
        diagonalHom_nonneg _ (fun _ => CFC.nnrpow_nonneg ..)⟩ := by
    apply Subtype.ext
    exact diagonal_power a ha _ (Positive.rootExponent_pos n)
  rw [he,matrixTrace_diagonal]
  rfl

end NonunitalGamma

end


noncomputable section
namespace NonunitalGamma
open Filter Topology TraceCone
open scoped ComplexOrder ENNReal NNReal CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def rampElement (c : A) (j : ℕ) : A := cfcₙ (ramp j) c

omit [PartialOrder A] [StarOrderedRing A] in
lemma inr_rampElement (c : A) (j : ℕ) :
    (Unitization.inr (rampElement c j) : Unitization ℂ A)=cfc (ramp j) (Unitization.inr c) :=
  Unitization.real_cfcₙ_eq_cfc_inr c (ramp j) (ramp_zero j)

lemma rampElement_nonneg (c : A) (j : ℕ) : 0 ≤ rampElement c j :=
  cfcₙ_nonneg (fun t _ => ramp_nonneg j t)

omit [PartialOrder A] [StarOrderedRing A] in
lemma rampElement_norm_le (c : A) (j : ℕ) : ‖rampElement c j‖ ≤ 1 := by
  rw [←Unitization.norm_inr (𝕜 := ℂ),inr_rampElement]
  apply norm_cfc_le zero_le_one
  intro t _
  rw [Real.norm_eq_abs,abs_of_nonneg (ramp_nonneg j t)]
  exact ramp_le_one j t

lemma rampElement_sum (c : A) (hc : 0 ≤ c) (N : ℕ) (hN : ‖c‖ ≤ N) :
    (∑ j ∈ Finset.range N,rampElement c j)=c := by
  apply Unitization.inr_injective (R := ℂ)
  change (Unitization.inrNonUnitalStarAlgHom ℂ A) (∑ j ∈ Finset.range N,rampElement c j)=Unitization.inr c
  rw [map_sum]
  simp only [Unitization.inrNonUnitalStarAlgHom_apply,inr_rampElement]
  apply ramp_cfc_sum _ (Unitization.inr_nonneg_iff.mpr hc)
  simpa only [Unitization.norm_inr] using hN

lemma NormalizedTrace.rank_ne_top (τ : NormalizedTrace A) (c : A) (hc : 0 ≤ c) : τ.rank c ≠ ∞ :=
  ne_of_lt ((Pureness.normalizedRootRank_le_one τ.unitized (Unitization.inr c)
    (Unitization.inr_nonneg_iff.mpr hc)).trans_lt ENNReal.one_lt_top)

lemma rampElement_rank_defect (τ : NormalizedTrace A) (c : A) (hc : 0 ≤ c)
    (N : ℕ) (hN : ‖c‖ ≤ N) :
    0 ≤ (∑ j ∈ Finset.range (N+1),(τ.rank (rampElement c j)).toReal)-(τ.functional c).re ∧
    (∑ j ∈ Finset.range (N+1),(τ.rank (rampElement c j)).toReal)-(τ.functional c).re ≤
      (τ.rank c).toReal := by
  have hi := ramp_rank_defect τ.unitized (Unitization.inr c)
    (Unitization.inr_nonneg_iff.mpr hc) N (by simpa only [Unitization.norm_inr] using hN)
  simpa only [NormalizedTrace.rank,inr_rampElement,NormalizedTrace.unitized_inr] using hi

theorem rank_approximation [Nontrivial A] (hsimple : TopologicallySimple A)
    (hproj : Projectionless A) (hT : Nonempty (NormalizedTrace A))
    (g : A) (hg : 0 ≤ g) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ N : ℕ, ∃ k : Positive (CStarMatrix (Fin (N+1)) (Fin (N+1)) A),
      ‖k.1‖ ≤ 1 ∧ ∀ τ : NormalizedTrace A,
        (τ.weight.matrixTrace (Fin (N+1))).rank k ≠ ∞ ∧
        τ.weight.matrixTrace (Fin (N+1)) k ≠ ∞ ∧
        |(τ.weight.matrixTrace (Fin (N+1)) k).toReal-(τ.functional g).re| < ξ ∧
        0 ≤ ((τ.weight.matrixTrace (Fin (N+1))).rank k).toReal-
          (τ.weight.matrixTrace (Fin (N+1)) k).toReal ∧
        ((τ.weight.matrixTrace (Fin (N+1))).rank k).toReal-
          (τ.weight.matrixTrace (Fin (N+1)) k).toReal < ξ := by
  classical
  obtain ⟨c,hc,hct,hcr⟩ := arbitrarily_small_rank_trace_transfer hsimple hproj hT g hg hξ
  obtain ⟨N,hN⟩ := exists_nat_gt ‖c‖
  let a : Fin (N+1) → A := fun i => rampElement c i
  have ha : ∀ i,0 ≤ a i := fun i => rampElement_nonneg c i
  let k : Positive (CStarMatrix (Fin (N+1)) (Fin (N+1)) A) :=
    ⟨diagonalHom a,diagonalHom_nonneg a ha⟩
  have hsum : (∑ i,a i)=c := by
    rw [Fin.sum_univ_eq_sum_range (fun j => rampElement c j)]
    apply rampElement_sum c hc
    exact hN.le.trans (by exact_mod_cast (Nat.le_succ N))
  refine ⟨N,k,diagonalHom_norm_le_one a (fun i => rampElement_norm_le c i),fun τ => ?_⟩
  have ht : τ.weight.matrixTrace (Fin (N+1)) k=ENNReal.ofReal (τ.functional c).re := by
    rw [matrixTrace_diagonal τ.weight a ha]
    change (∑ i, ENNReal.ofReal (τ.functional (a i)).re)=_
    rw [←ENNReal.ofReal_sum_of_nonneg (fun i _ => (τ.functional.map_nonneg (ha i)).1)]
    rw [←Complex.re_sum,←map_sum,hsum]
  have hr : (τ.weight.matrixTrace (Fin (N+1))).rank k=∑ i,τ.rank (a i) := by
    rw [matrixRank_diagonal τ.weight a ha]
    apply Finset.sum_congr rfl
    intro i _
    exact τ.weight_rank _ (ha i)
  have hf : (τ.weight.matrixTrace (Fin (N+1))).rank k ≠ ∞ := by
    rw [hr]
    exact ENNReal.sum_ne_top.mpr (fun i _ => τ.rank_ne_top _ (ha i))
  have hrr : ((τ.weight.matrixTrace (Fin (N+1))).rank k).toReal=
      ∑ j ∈ Finset.range (N+1),(τ.rank (rampElement c j)).toReal := by
    rw [hr,ENNReal.toReal_sum (fun i _ => τ.rank_ne_top _ (ha i))]
    exact Fin.sum_univ_eq_sum_range (fun j => (τ.rank (rampElement c j)).toReal) (N+1)
  have htR : (τ.weight.matrixTrace (Fin (N+1)) k).toReal=(τ.functional c).re := by
    rw [ht,ENNReal.toReal_ofReal (τ.functional.map_nonneg hc).1]
  have herr : |(τ.functional c).re-(τ.functional g).re|<ξ := by
    rw [←Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans_lt (hct τ)
  have hsmall : (τ.rank c).toReal<ξ := by
    have h := (ENNReal.toReal_lt_toReal (τ.rank_ne_top c hc) ENNReal.ofReal_ne_top).mpr (hcr τ)
    simpa only [ENNReal.toReal_ofReal hξ.le] using h
  have hdef := rampElement_rank_defect τ c hc N hN.le
  refine ⟨hf,?_,?_,?_,?_⟩
  · rw [ht];exact ENNReal.ofReal_ne_top
  · rwa [htR]
  · rw [hrr,htR];exact hdef.1
  · rw [hrr,htR];exact hdef.2.trans_lt hsmall

end NonunitalGamma

end

end OAI
