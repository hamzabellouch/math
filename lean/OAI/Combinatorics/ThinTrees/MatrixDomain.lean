import OAI.Combinatorics.ThinTrees.GraphMatrix

namespace OAI

universe uV

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder Matrix.Norms.Elementwise
namespace StrongThinTree
variable {V : Type uV} [Fintype V] [DecidableEq V]
omit [DecidableEq V] in
lemma isClosed_psd : IsClosed {X : Matrix V V ℝ | X.PosSemidef} := by
  have heq : {X : Matrix V V ℝ | X.PosSemidef}=
      {X | X.IsHermitian} ∩ ⋂v : V → ℝ, {X | 0 ≤ qform X v} := by
    ext X
    simp only [Set.mem_ofPred,Set.mem_inter_iff,Set.mem_iInter]
    exact ⟨fun h => ⟨h.isHermitian,qform_nonneg h⟩,fun h =>
      Matrix.PosSemidef.of_dotProduct_mulVec_nonneg h.1 (by simpa only [star_trivial,qform] using h.2)⟩
  rw [heq]
  apply IsClosed.inter
  · exact isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  · exact isClosed_iInter (fun v => isClosed_le continuous_const (qform_continuous v))
omit [DecidableEq V] in
lemma isClosed_matrixAbove (A : Matrix V V ℝ) : IsClosed {X : Matrix V V ℝ | A ≤ X} :=
  isClosed_psd.preimage (continuous_id.sub continuous_const)
lemma psd_entry_bound {X : Matrix V V ℝ} (hX : X.PosSemidef) {C : ℝ} (hC : 0 ≤ C)
    (hdiag : ∀i, X i i ≤ C) (i j : V) : |X i j| ≤ C := by
  have hi : 0 ≤ X i i := by simpa only [qform_single] using qform_nonneg hX (Pi.single i 1)
  have hj : 0 ≤ X j j := by simpa only [qform_single] using qform_nonneg hX (Pi.single j 1)
  have hh := quadratic_cauchy_schwarz hX (Pi.single i 1) (Pi.single j 1)
  simp only [mulVec_single_one,single_one_dotProduct] at hh
  change (X i j)^2 ≤ X i i*X j j at hh
  have hm := mul_le_mul (hdiag i) (hdiag j) hj hC
  nlinarith [sq_abs (X i j),abs_nonneg (X i j)]

namespace MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)

def matrixDomain : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | G.baseMatrix ≤ X ∧ ∀S : Finset (Fin n), S.Nonempty → S ≠ univ →
    qform X (cutIndicator S) ≤ 3*(G.cut univ S).card}
lemma domain_pd (hn : 0 < n) {X : Matrix (Fin n) (Fin n) ℝ} (hX : X ∈ G.matrixDomain) : X.PosDef :=
  posDef_of_le (G.baseMatrix_pd hn) hX.1
lemma domain_closed : IsClosed G.matrixDomain := by
  simp only [matrixDomain,Set.ofPred_and,Set.ofPred_forall]
  exact (isClosed_matrixAbove _).inter (isClosed_iInter fun S => isClosed_iInter fun _ =>
    isClosed_iInter fun _ => isClosed_le (qform_continuous _) continuous_const)
lemma domain_convex : Convex ℝ G.matrixDomain := by
  intro X hX Y hY a b ha hb hab
  refine ⟨?_,?_⟩
  · have hh := add_le_add (smul_le_smul_of_nonneg_left hX.1 ha) (smul_le_smul_of_nonneg_left hY.1 hb)
    simpa only [←add_smul,hab,one_smul] using hh
  · intro S hS hS'
    rw [qform_add,qform_smul,qform_smul]
    have hh := add_le_add (mul_le_mul_of_nonneg_left (hX.2 S hS hS') ha)
      (mul_le_mul_of_nonneg_left (hY.2 S hS hS') hb)
    simpa only [←add_mul,hab,one_mul] using hh
lemma domain_nonempty (hn : 0 < n) (hc : G.EdgeConnected 1) : G.matrixDomain.Nonempty := by
  refine ⟨G.baseMatrix,le_rfl,?_⟩
  intro S hS hS'
  rw [G.baseMatrix_cut]
  have hcut : (1:ℝ) ≤ (G.cut univ S).card := by exact_mod_cast hc S hS hS'
  have hcard : (S.card:ℝ) ≤ n := by exact_mod_cast (show S.card ≤ n by simpa using card_le_univ S)
  have hdiv : (S.card:ℝ)/n ≤ 1 := (div_le_one (Nat.cast_pos.mpr hn)).mpr hcard
  linarith
lemma indicator_singleton (i : Fin n) : cutIndicator {i}=Pi.single i 1 := by
  ext j
  simp [cutIndicator,Pi.single_apply,eq_comm]
lemma domain_diag_bound (hn : 2 ≤ n) {X : Matrix (Fin n) (Fin n) ℝ} (hX : X ∈ G.matrixDomain) (i : Fin n) :
    X i i ≤ 3*m := by
  have hproper : ({i} : Finset (Fin n)) ≠ univ := by
    intro he
    have hh := congrArg card he
    simp only [card_singleton,card_univ,Fintype.card_fin] at hh
    omega
  have hh := hX.2 {i} (singleton_nonempty _) hproper
  rw [indicator_singleton,qform_single] at hh
  have hm : ((G.cut univ {i}).card:ℝ) ≤ m := by exact_mod_cast (show (G.cut univ {i}).card ≤ m by simpa using card_le_univ (G.cut univ {i}))
  linarith
lemma domain_bounded (hn : 2 ≤ n) : Bornology.IsBounded G.matrixDomain := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨3*m,fun X hX => ?_⟩
  have hC : (0:ℝ) ≤ 3*m := by positivity
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro j
  simpa only [Real.norm_eq_abs] using psd_entry_bound (G.domain_pd (by omega) hX).posSemidef hC
    (G.domain_diag_bound hn hX) i j
lemma domain_compact (hn : 2 ≤ n) : IsCompact G.matrixDomain :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨G.domain_closed,G.domain_bounded hn⟩
lemma resistance_continuousAt {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosDef) (e : Fin m) :
    ContinuousAt (fun Y => G.resistance Y e) X := by
  apply (qform_continuous (G.incidence e)).continuousAt.comp
  apply continuousAt_matrix_inv
  simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hX.det_pos.ne'
lemma resistance_continuousOn (hn : 0 < n) (e : Fin m) : ContinuousOn (fun X => G.resistance X e) G.matrixDomain :=
  fun _ hX => (G.resistance_continuousAt (G.domain_pd hn hX) e).continuousWithinAt

end MultiGraph
end StrongThinTree

end
end

end OAI
