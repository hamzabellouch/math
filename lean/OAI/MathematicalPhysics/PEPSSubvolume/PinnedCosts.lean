import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.EntropyComparison
import OAI.MathematicalPhysics.PEPSSubvolume.PinnedSpectral

namespace OAI

/-! Feasible pinned filters, positive sector costs and entropy invariance. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
open Matrix
open Filter Topology
open Set Filter Complex Complex.HadamardThreeLines
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.Pinning
open Matrix
variable {L q : ℕ}

theorem foldl_pin {ι : Type*} (P : Operator L q) (hP : P * P = P)
    (B : ι → Operator L q) (hc : ∀ i, Commute P (B i)) (l : List ι) (R : Operator L q) :
    l.foldl (fun R i => P * B i * R) (P * R) =
      P * l.foldl (fun R i => B i * R) R := by
  induction l generalizing R with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [show P * B i * (P * R) = P * (B i * R) by
      rw [← mul_assoc, ← mul_assoc, (hc i).eq, mul_assoc (B i), hP, ← (hc i).eq, mul_assoc]]
    exact ih _

theorem commute_foldl {ι : Type*} (P : Operator L q)
    (B : ι → Operator L q) (hc : ∀ i, Commute P (B i)) (l : List ι)
    (R : Operator L q) (hR : Commute P R) :
    Commute P (l.foldl (fun R i => B i * R) R) := by
  induction l generalizing R with
  | nil => exact hR
  | cons i l ih => exact ih _ ((hc i).mul_right hR)

theorem foldl_pin_nonempty {ι : Type*} (P : Operator L q) (hP : P * P = P)
    (B : ι → Operator L q) (hc : ∀ i, Commute P (B i)) (l : List ι) (hl : l ≠ []) :
    l.foldl (fun R i => P * B i * R) 1 =
      l.foldl (fun R i => B i * R) 1 * P := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons i l =>
    simp only [List.foldl_cons,mul_one]
    rw [foldl_pin P hP B hc l (B i)]
    exact (commute_foldl P B hc l (B i) (hc i)).eq

def insertedFilter (C X : Finset (Vertex L)) (hCX : C ⊆ X)
    (u : EuclideanSpace ℂ (RegionConfiguration q C))
    (G : LocalPositiveFilter q (X \ C)) : LocalPositiveFilter q X where
  matrix := insertedMatrix C X hCX u G.matrix
  positive := insertedMatrix_posSemidef C X hCX u G.matrix G.positive

theorem insertedFilter_feasible {n : ℕ} (C : Finset (Vertex L))
    (X : Fin n → Finset (Vertex L)) (hCX : ∀ j, C ⊆ X j)
    (u : EuclideanSpace ℂ (RegionConfiguration q C)) (hu : ‖u‖ = 1)
    (a : Fin n → ℝ) (ha : ∀ j, 0 < a j)
    (G : FilterFamily q n (fun j => X j \ C)) (hG : FilterFeasible a G) :
    FilterFeasible a (fun j => insertedFilter C (X j) (hCX j) u (G j)) := by
  intro j
  change (∑ i, Real.rpow
    ((insertedMatrix_posSemidef C (X j) (hCX j) u (G j).matrix
      (G j).positive).isHermitian.eigenvalues i) (2 / a j)) = 1
  rw [insertedMatrix_tracePower C (X j) (hCX j) u hu (G j).matrix
    (G j).positive (2 / a j) (div_pos (by norm_num) (ha j))]
  exact hG j

theorem inserted_filter_product {n : ℕ} (hn : 0 < n) (C : Finset (Vertex L))
    (X : Fin n → Finset (Vertex L)) (hCX : ∀ j, C ⊆ X j)
    (u : EuclideanSpace ℂ (RegionConfiguration q C)) (hu : ‖u‖ = 1)
    (G : FilterFamily q n (fun j => X j \ C)) :
    orderedFilterProduct (fun j => insertedFilter C (X j) (hCX j) u (G j)) =
      orderedFilterProduct G * liftLocal C (coreMatrix C u) := by
  have hP : liftLocal C (coreMatrix C u) * liftLocal C (coreMatrix C u) =
      liftLocal C (coreMatrix C u) := by rw [← liftLocal_mul, coreMatrix_idempotent C u hu]
  have hc (j : Fin n) : Commute (liftLocal C (coreMatrix C u))
      (liftLocal (X j \ C) (G j).matrix) :=
    lift_core_shell_commute C (X j) (hCX j) _ _
  unfold orderedFilterProduct
  simp only [insertedFilter, lift_insertedMatrix]
  apply foldl_pin_nonempty _ hP _ hc
  intro hz
  have hlen := congrArg List.length hz
  have hn0 : n = 0 := by simpa using hlen
  omega

theorem inserted_filteredVector {n : ℕ} (hn : 0 < n) (C : Finset (Vertex L))
    (X : Fin n → Finset (Vertex L)) (hCX : ∀ j, C ⊆ X j)
    (u : EuclideanSpace ℂ (RegionConfiguration q C)) (hu : ‖u‖ = 1)
    (G : FilterFamily q n (fun j => X j \ C)) (ψ : State L q) :
    filteredVector (fun j => insertedFilter C (X j) (hCX j) u (G j)) ψ =
      filteredVector G (asMap (liftLocal C (coreMatrix C u)) ψ) := by
  unfold filteredVector
  rw [inserted_filter_product hn C X hCX u hu G]
  simp only [asMap, map_mul, mul_apply_eq_comp]

def pinnedVector (C : Finset (Vertex L))
    (u : EuclideanSpace ℂ (RegionConfiguration q C)) (ψ : State L q) : State L q :=
  asMap (liftLocal C (coreMatrix C u)) ψ

def normalizedPinned (C : Finset (Vertex L))
    (u : EuclideanSpace ℂ (RegionConfiguration q C)) (ψ : State L q) : State L q :=
  ((‖pinnedVector C u ψ‖⁻¹ : ℝ) : ℂ) • pinnedVector C u ψ

theorem normalizedPinned_norm (C : Finset (Vertex L))
    (u : EuclideanSpace ℂ (RegionConfiguration q C)) (ψ : State L q)
    (hc : 0 < ‖pinnedVector C u ψ‖) : ‖normalizedPinned C u ψ‖ = 1 := by
  simp only [normalizedPinned, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_inv, abs_norm, inv_mul_cancel₀ (ne_of_gt hc)]

theorem shell_filter_bound {n : ℕ} (hn : 0 < n) (C : Finset (Vertex L))
    (X : Fin n → Finset (Vertex L)) (hCX : ∀ j, C ⊆ X j)
    (u : EuclideanSpace ℂ (RegionConfiguration q C)) (hu : ‖u‖ = 1)
    (a : Fin n → ℝ) (ha : ∀ j, 0 < a j) (ψ : State L q)
    (F : FilterFamily q n X) (hF : IsFilterOptimizer ψ a F)
    (G : FilterFamily q n (fun j => X j \ C)) (hG : FilterFeasible a G) :
    ‖filteredVector G (normalizedPinned C u ψ)‖ ≤
      ‖filteredVector F ψ‖ / ‖pinnedVector C u ψ‖ := by
  have hi := hF.2 (fun j => insertedFilter C (X j) (hCX j) u (G j))
    (insertedFilter_feasible C X hCX u hu a ha G hG)
  rw [inserted_filteredVector hn C X hCX u hu G ψ] at hi
  change ‖filteredVector G (pinnedVector C u ψ)‖ ≤ _ at hi
  calc
    ‖filteredVector G (normalizedPinned C u ψ)‖ =
        ‖pinnedVector C u ψ‖⁻¹ * ‖filteredVector G (pinnedVector C u ψ)‖ := by
      simp [normalizedPinned,filteredVector, norm_smul]
    _ ≤ ‖pinnedVector C u ψ‖⁻¹ * ‖filteredVector F ψ‖ :=
      mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (norm_nonneg _))
    _ = _ := by rw [div_eq_mul_inv,mul_comm]

theorem common_filter_bound_pos (X : ℕ → Finset (Vertex L))
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j) (ψ : State L q) (hψ : ‖ψ‖ = 1)
    (n : ℕ) (N : ℝ) (hB : ∀ G : FilterFamily q n (fun j => X j.val),
      FilterFeasible (fun j => a j.val) G → ‖filteredVector G ψ‖ ≤ N) : 0 < N := by
  let w := fun j => (reducedDensity_isHermitian ψ (X j)).eigenvalues
  let U := fun j => (reducedDensity_isHermitian ψ (X j)).eigenvectorUnitary
  have hw : ∀ j i, 0 ≤ w j i := fun j i =>
    (reducedDensity_posSemidef ψ (X j)).eigenvalues_nonneg i
  have hsum : ∀ j, ∑ i, w j i = 1 := fun j => marginal_eigenvalues_sum ψ hψ (X j)
  exact PhysicalCurve.filter_bound_pos X U
    (fun j => MarginalRegularization.probabilities (w j) 1)
    (fun j => MarginalRegularization.probabilities_pos (w j) (hw j) 1 zero_lt_one)
    (fun j => MarginalRegularization.probabilities_sum (w j) (hsum j) 1 zero_lt_one)
    a ha ψ hψ n N hB

theorem pinned_sector_cost (hq : 0 < q) (C : Finset (Vertex L))
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X) (hCX : ∀ j, C ⊆ X j)
    (u : EuclideanSpace ℂ (RegionConfiguration q C)) (hu : ‖u‖ = 1)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j) (ψ : State L q)
    (n : ℕ) (hn : 0 < n)
    (F : FilterFamily q n (fun j => X j.val))
    (hF : IsFilterOptimizer ψ (fun j => a j.val) F)
    (hc : 0 < ‖pinnedVector C u ψ‖) :
    -Real.log (‖filteredVector F ψ‖ ^ 2) ≤
      -Real.log (‖pinnedVector C u ψ‖ ^ 2) +
      ∑ j ∈ Finset.range n, a j * vonNeumannEntropy (normalizedPinned C u ψ) (X j \ C) := by
  let Y := fun j => X j \ C
  have hY : Monotone Y := fun i j hij => Finset.sdiff_subset_sdiff_left C (hX hij)
  have hB := fun G hG => shell_filter_bound hn C (fun j : Fin n => X j.val)
    (fun j => hCX j.val) u hu (fun j => a j.val) (fun j => ha j.val) ψ F hF G hG
  have hnorm := normalizedPinned_norm C u ψ hc
  have hpos := common_filter_bound_pos Y a ha (normalizedPinned C u ψ) hnorm n
    (‖filteredVector F ψ‖ / ‖pinnedVector C u ψ‖) hB
  have hN : 0 < ‖filteredVector F ψ‖ := (div_pos_iff.mp hpos).elim
    (fun h => h.1) (fun h => (not_lt_of_ge (norm_nonneg _) h.1).elim)
  have hb := PhysicalCurve.filter_bound_cost_le_sum_entropy hq Y hY a ha
    (normalizedPinned C u ψ) hnorm n (‖filteredVector F ψ‖ / ‖pinnedVector C u ψ‖) hB
  rw [div_pow,Real.log_div (pow_ne_zero _ (ne_of_gt hN)) (pow_ne_zero _ (ne_of_gt hc))] at hb
  dsimp only [Y] at hb
  linarith

end PolynomialPEPS.Subvolume.Pinning

namespace PolynomialPEPS.Subvolume.MatrixEntropy
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem entropy_unitary_conjugate {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (U : unitary (Matrix n n ℂ)) :
    entropy ((U : Matrix n n ℂ) * A * (U : Matrix n n ℂ).conjTranspose)
      (hA.mul_mul_conjTranspose_same (U : Matrix n n ℂ)).isHermitian =
      entropy A hA.isHermitian := by
  unfold entropy
  have heig := (hA.mul_mul_conjTranspose_same
    (U : Matrix n n ℂ)).isHermitian.eigenvalues_eq_eigenvalues_iff hA.isHermitian
  rw [heig.mpr ?_]
  rw [Matrix.charpoly_mul_comm, ← mul_assoc]
  simp only [← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self, one_mul]

theorem entropy_concave_mixture {s : Type*} [Fintype s]
    (p : s → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : ∑ k, p k = 1)
    (A : s → Matrix n n ℂ) (hA : ∀ k, (A k).PosSemidef) :
    ∑ k, p k * entropy (A k) (hA k).isHermitian ≤
      entropy (∑ k, p k • A k)
        (Matrix.posSemidef_sum _ (fun k _ => (hA k).smul (hp k))).isHermitian := by
  let B := ∑ k, p k • A k
  have hB : B.PosSemidef := Matrix.posSemidef_sum _ (fun k _ => (hA k).smul (hp k))
  let U := hB.isHermitian.eigenvectorUnitary
  let C : s → Matrix n n ℂ := fun k =>
    (U : Matrix n n ℂ).conjTranspose * A k * (U : Matrix n n ℂ)
  have hC (k : s) : (C k).PosSemidef := (hA k).conjTranspose_mul_mul_same _
  have hentropy (k : s) : entropy (C k) (hC k).isHermitian =
      entropy (A k) (hA k).isHermitian := by
    simpa [C, ← Matrix.star_eq_conjTranspose] using entropy_unitary_conjugate (hA k) (star U)
  have hdiag (i : n) : ∑ k, p k * ((C k) i i).re = hB.isHermitian.eigenvalues i := by
    have h := congrArg (fun M : Matrix n n ℂ => (M i i).re)
      hB.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, C, B, U, ← Matrix.star_eq_conjTranspose, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.sum_apply, Complex.re_sum,
      Matrix.diagonal_apply] using h
  have hbound (i : n) : ∑ k, p k * Real.negMulLog ((C k) i i).re ≤
      Real.negMulLog (hB.isHermitian.eigenvalues i) := by
    rw [← hdiag]
    simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.le_map_sum
      (fun k (_ : k ∈ (Finset.univ : Finset s)) => hp k) hsum
      (fun k (_ : k ∈ (Finset.univ : Finset s)) =>
        (Complex.nonneg_iff.mp ((hC k).diag_nonneg (i := i))).1)
  calc
    ∑ k, p k * entropy (A k) (hA k).isHermitian =
        ∑ k, p k * entropy (C k) (hC k).isHermitian := by simp_rw [hentropy]
    _ ≤ ∑ k, p k * ∑ i, Real.negMulLog ((C k) i i).re :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (entropy_le_diagonal (hC k)) (hp k)
    _ = ∑ i, ∑ k, p k * Real.negMulLog ((C k) i i).re := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ entropy B hB.isHermitian := Finset.sum_le_sum fun i _ => hbound i

end PolynomialPEPS.Subvolume.MatrixEntropy

end

end OAI
