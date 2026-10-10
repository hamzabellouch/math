import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootEuclideanCoordinates

namespace OAI

/-!
# Contracting diagonal dynamics on full upper-root leaves

The explicit root coordinates identify the contracting unipotent
foliation. Uniform root-weight gaps give an exponential bound on its
Euclidean size; strict gaps give convergence to the identity.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma timeVectorHomeomorph_zero (c : EliminationChain P D) :
    c.timeVectorHomeomorph c.zeroTime = 0 := by
  induction c with
  | done => ext k; exact Fin.elim0 k
  | step a b hab hP hb tail ih =>
      change Fin.cons (α := fun _ : Fin (tail.roots.length + 1) => ℝ)
        0 (tail.timeVectorHomeomorph tail.zeroTime) = 0
      rw [ih]
      ext k
      exact Fin.cases rfl (fun _ => rfl) k

end EliminationChain

lemma upperRootEuclideanCoordinates_zero (n : ℕ) :
    upperRootEuclideanCoordinates n (completeRootChain n).zeroTime = 0 := by
  ext p
  change (completeRootChain n).timeVectorHomeomorph (completeRootChain n).zeroTime
    ((upperRootIndexEquiv n).symm p) = 0
  rw [EliminationChain.timeVectorHomeomorph_zero]
  rfl

def upperRootSize (n : ℕ) (t : UpperRootTime n) : ℝ :=
  ‖upperRootEuclideanCoordinates n t‖

lemma upperRootSize_dilation_le (n : ℕ) (ell : Fin n → ℝ) (ε r : ℝ)
    (hgap : ∀ p : allPositiveRoots n, ε ≤ ell p.val.2 - ell p.val.1)
    (hr : 0 ≤ r) (t : UpperRootTime n) :
    upperRootSize n ((completeRootChain n).rootDilation ell r t) ≤
      Real.exp (-ε * r) * upperRootSize n t := by
  unfold upperRootSize
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mpr
  intro p
  rw [upperRootEuclideanCoordinates_dilation, norm_mul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul
  · apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (hgap p) hr
    nlinarith
  · exact norm_le_pi_norm _ p
  · exact norm_nonneg _
  · exact (Real.exp_pos _).le

lemma upperRootDilation_tendsto_zero (n : ℕ) (ell : Fin n → ℝ)
    (hgap : ∀ p : allPositiveRoots n, ell p.val.1 < ell p.val.2) (t : UpperRootTime n) :
    Tendsto (fun r : ℝ => (completeRootChain n).rootDilation ell r t)
      atTop (𝓝 (completeRootChain n).zeroTime) := by
  have h : Tendsto (fun r : ℝ => upperRootEuclideanCoordinates n
      ((completeRootChain n).rootDilation ell r t)) atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro p
    have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.Tendsto.const_mul_atTop (sub_pos.mpr (hgap p)) tendsto_id)
    have hm := he.mul_const (upperRootEuclideanCoordinates n t p)
    have hs (r : ℝ) : -((ell p.val.2 - ell p.val.1) * r) =
        (ell p.val.1 - ell p.val.2) * r := by ring
    simpa only [Function.comp_def, id_eq, hs, zero_mul, Pi.zero_apply,
      upperRootEuclideanCoordinates_dilation] using hm
  have h' := (upperRootEuclideanCoordinates n).symm.continuous.tendsto 0 |>.comp h
  have hz : (upperRootEuclideanCoordinates n).symm 0 = (completeRootChain n).zeroTime := by
    apply (upperRootEuclideanCoordinates n).injective
    rw [Homeomorph.apply_symm_apply, upperRootEuclideanCoordinates_zero]
  simpa only [Function.comp_def, Homeomorph.symm_apply_apply, hz] using h'

lemma upperRoot_conjugate_tendsto_one (n : ℕ) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0)
    (hgap : ∀ p : allPositiveRoots n, ell p.val.1 < ell p.val.2)
    (g : positiveRootGeneratedGroup (allPositiveRoots n)) :
    Tendsto (fun r : ℝ => diagonalOneParameter ell hell r * g.val *
      diagonalOneParameter ell hell (-r)) atTop (𝓝 1) := by
  let t := (upperRootWordHomeomorph n).symm g
  have h := (upperRootWord_isEmbedding n).continuous.tendsto
    (completeRootChain n).zeroTime |>.comp (upperRootDilation_tendsto_zero n ell hgap t)
  have hg : (completeRootChain n).word t = g.val :=
    congrArg Subtype.val ((upperRootWordHomeomorph n).apply_symm_apply g)
  simpa only [Function.comp_def, (completeRootChain n).word_rootDilation ell hell, hg,
    EliminationChain.word_zeroTime] using h

end DukePrimeDegree

end

end OAI
