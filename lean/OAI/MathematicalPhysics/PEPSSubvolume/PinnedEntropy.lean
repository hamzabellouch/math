import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.GeometricLower
import OAI.MathematicalPhysics.PEPSSubvolume.PinnedCosts

namespace OAI

/-! Pinned entropy bounds and geometric upper comparison. -/

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

def coreColumn (C : Finset (Vertex L))
    (U : unitary (Matrix (RegionConfiguration q C) (RegionConfiguration q C) ℂ))
    (i : RegionConfiguration q C) : EuclideanSpace ℂ (RegionConfiguration q C) :=
  WithLp.toLp 2 (fun x => (U : Matrix (RegionConfiguration q C) (RegionConfiguration q C) ℂ) x i)

theorem coreColumn_norm (C : Finset (Vertex L))
    (U : unitary (Matrix (RegionConfiguration q C) (RegionConfiguration q C) ℂ))
    (i : RegionConfiguration q C) : ‖coreColumn C U i‖ = 1 := by
  have hinner : inner ℂ (coreColumn C U i) (coreColumn C U i) = 1 := by
    have h := congrArg (fun A => A i i) (Unitary.coe_star_mul_self U)
    simpa only [PiLp.inner_apply,coreColumn,WithLp.ofLp_toLp,RCLike.inner_apply,
      Matrix.mul_apply,Matrix.star_apply,Matrix.one_apply_eq,starRingEnd_apply,mul_comm] using h
  have hsq : ‖coreColumn C U i‖ ^ 2 = 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ),hinner]
    rfl
  nlinarith [norm_nonneg (coreColumn C U i)]

theorem sum_coreMatrix (C : Finset (Vertex L))
    (U : unitary (Matrix (RegionConfiguration q C) (RegionConfiguration q C) ℂ)) :
    ∑ i, coreMatrix C (coreColumn C U i) = 1 := by
  ext x y
  have h := congrArg (fun A => A x y) (Unitary.coe_mul_star_self U)
  simpa [Matrix.sum_apply,coreMatrix,coreColumn,Matrix.mul_apply,Matrix.star_apply] using h

theorem asMap_mul_apply (A B : Operator L q) (ψ : State L q) :
    asMap (A * B) ψ = asMap A (asMap B ψ) := by
  simp only [asMap,map_mul,mul_apply_eq_comp]

theorem asMap_sum_apply {ι : Type*} [Fintype ι] (A : ι → Operator L q) (ψ : State L q) :
    asMap (∑ i, A i) ψ = ∑ i, asMap (A i) ψ := by
  simp only [asMap,map_sum,_root_.sum_apply]

theorem sum_pinnedVector (C : Finset (Vertex L))
    (U : unitary (Matrix (RegionConfiguration q C) (RegionConfiguration q C) ℂ))
    (ψ : State L q) : ∑ i, pinnedVector C (coreColumn C U i) ψ = ψ := by
  unfold pinnedVector
  rw [← asMap_sum_apply]
  change asMap (∑ i, localLiftHom C (coreMatrix C (coreColumn C U i))) ψ = ψ
  rw [← map_sum, sum_coreMatrix, map_one]
  simp [asMap]

theorem pinned_self_inner (C : Finset (Vertex L))
    (u : EuclideanSpace ℂ (RegionConfiguration q C)) (_hu : ‖u‖ = 1)
    (ψ ζ : State L q) :
    inner ℂ (pinnedVector C u ψ) ζ = inner ℂ ψ (pinnedVector C u ζ) := by
  have h : IsSelfAdjoint (asMap (liftLocal C (coreMatrix C u))) :=
    ((coreMatrix_isHermitian C u).isSelfAdjoint.map (localLiftHom C)).map Matrix.toEuclideanCLM
  exact h.isSymmetric ψ ζ

theorem pinnedVector_idempotent (C : Finset (Vertex L))
    (u : EuclideanSpace ℂ (RegionConfiguration q C)) (hu : ‖u‖ = 1)
    (ψ : State L q) : pinnedVector C u (pinnedVector C u ψ) = pinnedVector C u ψ := by
  unfold pinnedVector
  rw [← asMap_mul_apply,← liftLocal_mul,coreMatrix_idempotent C u hu]

theorem inner_pinned_shell (C X : Finset (Vertex L)) (hCX : C ⊆ X)
    (u : EuclideanSpace ℂ (RegionConfiguration q C)) (hu : ‖u‖ = 1)
    (A : Matrix (RegionConfiguration q (X \ C)) (RegionConfiguration q (X \ C)) ℂ)
    (ψ : State L q) :
    inner ℂ (pinnedVector C u ψ) (asMap (liftLocal (X \ C) A) (pinnedVector C u ψ)) =
      inner ℂ ψ (asMap (liftLocal (X \ C) A) (pinnedVector C u ψ)) := by
  rw [pinned_self_inner C u hu]
  congr 1
  have hc := lift_core_shell_commute C X hCX (coreMatrix C u) A
  change asMap (liftLocal C (coreMatrix C u))
    (asMap (liftLocal (X \ C) A) (pinnedVector C u ψ)) = _
  rw [← asMap_mul_apply,hc.eq,asMap_mul_apply]
  change asMap (liftLocal (X \ C) A) (pinnedVector C u (pinnedVector C u ψ)) = _
  rw [pinnedVector_idempotent C u hu]

theorem sum_pinned_marginals (C X : Finset (Vertex L)) (hCX : C ⊆ X)
    (U : unitary (Matrix (RegionConfiguration q C) (RegionConfiguration q C) ℂ))
    (ψ : State L q) :
    ∑ i, reducedDensity (pinnedVector C (coreColumn C U i) ψ) (X \ C) =
      reducedDensity ψ (X \ C) := by
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro A
  rw [Matrix.mul_sum,Matrix.trace_sum]
  simp_rw [← inner_liftLocal_trace,inner_pinned_shell C X hCX _ (coreColumn_norm C U _)]
  rw [← inner_sum,← map_sum,sum_pinnedVector]

theorem pinned_norm_sq (C : Finset (Vertex L))
    (u : EuclideanSpace ℂ (RegionConfiguration q C)) (hu : ‖u‖ = 1)
    (ψ : State L q) : ‖pinnedVector C u ψ‖ ^ 2 =
      (Matrix.trace (coreMatrix C u * reducedDensity ψ C)).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),pinned_self_inner C u hu,pinnedVector_idempotent C u hu]
  exact congrArg Complex.re (inner_liftLocal_trace C (coreMatrix C u) ψ)

theorem trace_coreMatrix (C : Finset (Vertex L))
    (U : unitary (Matrix (RegionConfiguration q C) (RegionConfiguration q C) ℂ))
    (i : RegionConfiguration q C)
    (A : Matrix (RegionConfiguration q C) (RegionConfiguration q C) ℂ) :
    Matrix.trace (coreMatrix C (coreColumn C U i) * A) =
      ((U : Matrix (RegionConfiguration q C) (RegionConfiguration q C) ℂ).conjTranspose * A * (U : Matrix (RegionConfiguration q C) (RegionConfiguration q C) ℂ)) i i := by
  classical
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,coreMatrix,coreColumn,
    Matrix.conjTranspose_apply,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

theorem schmidt_weight (C : Finset (Vertex L)) (ψ : State L q)
    (i : RegionConfiguration q C) :
    ‖pinnedVector C (coreColumn C (reducedDensity_isHermitian ψ C).eigenvectorUnitary i) ψ‖ ^ 2 =
      (reducedDensity_isHermitian ψ C).eigenvalues i := by
  rw [pinned_norm_sq C _ (coreColumn_norm C _ i),trace_coreMatrix]
  have h := congrArg (fun A => (A i i).re)
    (reducedDensity_isHermitian ψ C).conjStarAlgAut_star_eigenvectorUnitary
  simpa only [Unitary.conjStarAlgAut_apply,Unitary.coe_star,star_star,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose,
    Matrix.diagonal_apply_eq,Function.comp_def,RCLike.ofReal_eq_complex_ofReal,
    Complex.ofReal_re] using h

theorem reducedDensity_smul (S : Finset (Vertex L)) (c : ℂ) (ψ : State L q) :
    reducedDensity (c • ψ) S = (Complex.normSq c : ℂ) • reducedDensity ψ S := by
  have hC : coefficientMatrix (c • ψ) S = c • coefficientMatrix ψ S := by
    ext x y
    rfl
  simp only [reducedDensity,hC,Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,
    smul_smul]
  rw [mul_comm (star c) c]
  have hn : c * star c = (Complex.normSq c : ℂ) := Complex.mul_conj c
  rw [hn]

theorem reducedDensity_zero (S : Finset (Vertex L)) :
    reducedDensity (0 : State L q) S = 0 := by
  ext x y
  simp [reducedDensity,coefficientMatrix,Matrix.mul_apply]

theorem normalizedPinned_marginal (C S : Finset (Vertex L))
    (u : EuclideanSpace ℂ (RegionConfiguration q C)) (ψ : State L q) :
    ((‖pinnedVector C u ψ‖ ^ 2 : ℝ) : ℂ) • reducedDensity (normalizedPinned C u ψ) S =
      reducedDensity (pinnedVector C u ψ) S := by
  by_cases hz : pinnedVector C u ψ = 0
  · simp [normalizedPinned,hz,reducedDensity_zero]
  · have hc : ‖pinnedVector C u ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    rw [normalizedPinned,reducedDensity_smul,smul_smul]
    have he : ((‖pinnedVector C u ψ‖ ^ 2 : ℝ) : ℂ) *
        (Complex.normSq ((‖pinnedVector C u ψ‖⁻¹ : ℝ) : ℂ) : ℂ) = 1 := by
      rw [Complex.normSq_ofReal,← Complex.ofReal_mul]
      norm_cast
      field_simp
    rw [he,one_smul]

end PolynomialPEPS.Subvolume.Pinning

namespace PolynomialPEPS.Subvolume.Pinning
open Matrix
variable {L q : ℕ}

def schmidtProbability (C : Finset (Vertex L)) (ψ : State L q)
    (i : RegionConfiguration q C) : ℝ :=
  ‖pinnedVector C (coreColumn C (reducedDensity_isHermitian ψ C).eigenvectorUnitary i) ψ‖ ^ 2

def schmidtState (C : Finset (Vertex L)) (ψ : State L q)
    (i : RegionConfiguration q C) : State L q :=
  normalizedPinned C (coreColumn C (reducedDensity_isHermitian ψ C).eigenvectorUnitary i) ψ

theorem schmidtProbability_nonneg (C : Finset (Vertex L)) (ψ : State L q)
    (i : RegionConfiguration q C) : 0 ≤ schmidtProbability C ψ i := sq_nonneg _

theorem schmidtProbability_sum (C : Finset (Vertex L)) (ψ : State L q) (hψ : ‖ψ‖ = 1) :
    ∑ i, schmidtProbability C ψ i = 1 := by
  simp only [schmidtProbability,schmidt_weight]
  exact marginal_eigenvalues_sum ψ hψ C

theorem schmidtProbability_entropy (C : Finset (Vertex L)) (ψ : State L q) :
    ∑ i, Real.negMulLog (schmidtProbability C ψ i) = vonNeumannEntropy ψ C := by
  simp only [schmidtProbability,schmidt_weight,vonNeumannEntropy]

theorem schmidt_shell_mixture (C X : Finset (Vertex L)) (hCX : C ⊆ X) (ψ : State L q) :
    ∑ i, schmidtProbability C ψ i • reducedDensity (schmidtState C ψ i) (X \ C) =
      reducedDensity ψ (X \ C) := by
  have he (i : RegionConfiguration q C) :
      schmidtProbability C ψ i • reducedDensity (schmidtState C ψ i) (X \ C) =
        reducedDensity (pinnedVector C (coreColumn C
          (reducedDensity_isHermitian ψ C).eigenvectorUnitary i) ψ) (X \ C) := by
    simp only [schmidtProbability,schmidtState]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact
      normalizedPinned_marginal C (X \ C)
        (coreColumn C (reducedDensity_isHermitian ψ C).eigenvectorUnitary i) ψ
  simp_rw [he]
  exact sum_pinned_marginals C X hCX _ ψ

theorem average_schmidt_shell_entropy (C X : Finset (Vertex L)) (hCX : C ⊆ X)
    (ψ : State L q) (hψ : ‖ψ‖ = 1) :
    ∑ i, schmidtProbability C ψ i * vonNeumannEntropy (schmidtState C ψ i) (X \ C) ≤
      vonNeumannEntropy ψ (X \ C) := by
  have h := MatrixEntropy.entropy_concave_mixture (schmidtProbability C ψ)
    (schmidtProbability_nonneg C ψ) (schmidtProbability_sum C ψ hψ)
    (fun i => reducedDensity (schmidtState C ψ i) (X \ C))
    (fun i => reducedDensity_posSemidef (schmidtState C ψ i) (X \ C))
  simpa only [schmidt_shell_mixture C X hCX ψ,MatrixEntropy.entropy,vonNeumannEntropy] using h

end PolynomialPEPS.Subvolume.Pinning

namespace PolynomialPEPS.Subvolume.Pinning
open Matrix
variable {L q : ℕ}

theorem optimizer_cost_le_core_add_shell_entropy (hq : 0 < q)
    (C : Finset (Vertex L)) (X : ℕ → Finset (Vertex L))
    (hX : Monotone X) (hCX : ∀ j, C ⊆ X j)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
    (ψ : State L q) (hψ : ‖ψ‖ = 1) (n : ℕ) (hn : 0 < n)
    (F : FilterFamily q n (fun j => X j.val))
    (hF : IsFilterOptimizer ψ (fun j => a j.val) F) :
    -Real.log (‖filteredVector F ψ‖ ^ 2) ≤
      vonNeumannEntropy ψ C +
      ∑ j ∈ Finset.range n, a j * vonNeumannEntropy ψ (X j \ C) := by
  let p := schmidtProbability C ψ
  let v := schmidtState C ψ
  let cost := -Real.log (‖filteredVector F ψ‖ ^ 2)
  have hsector (i : RegionConfiguration q C) :
      p i * cost ≤ Real.negMulLog (p i) +
        p i * ∑ j ∈ Finset.range n, a j * vonNeumannEntropy (v i) (X j \ C) := by
    by_cases hz : p i = 0
    · simp only [hz,zero_mul,Real.negMulLog_zero,add_zero,le_refl]
    · have hp : 0 < p i := lt_of_le_of_ne (schmidtProbability_nonneg C ψ i) (Ne.symm hz)
      have hc : 0 < ‖pinnedVector C (coreColumn C
          (reducedDensity_isHermitian ψ C).eigenvectorUnitary i) ψ‖ := by
        have hh : 0 < ‖pinnedVector C (coreColumn C
          (reducedDensity_isHermitian ψ C).eigenvectorUnitary i) ψ‖ ^ 2 := hp
        exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm (sq_pos_iff.mp hh))
      have hb := pinned_sector_cost hq C X hX hCX
        (coreColumn C (reducedDensity_isHermitian ψ C).eigenvectorUnitary i)
        (coreColumn_norm C _ i) a ha ψ n hn F hF hc
      have hw := mul_le_mul_of_nonneg_left hb (le_of_lt hp)
      change p i * cost ≤ p i * (-Real.log (p i) + _) at hw
      simpa only [mul_add,Real.negMulLog_def,mul_neg,neg_mul,v,schmidtState] using hw
  have havg := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (RegionConfiguration q C))) => hsector i)
  rw [← Finset.sum_mul,show ∑ i, p i = 1 from schmidtProbability_sum C ψ hψ,one_mul,
    Finset.sum_add_distrib,show ∑ i, Real.negMulLog (p i) = vonNeumannEntropy ψ C from
      schmidtProbability_entropy C ψ] at havg
  have hsum : (∑ i, p i * ∑ j ∈ Finset.range n, a j * vonNeumannEntropy (v i) (X j \ C)) ≤
      ∑ j ∈ Finset.range n, a j * vonNeumannEntropy ψ (X j \ C) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro j hj
    have hh := mul_le_mul_of_nonneg_left (average_schmidt_shell_entropy C (X j) (hCX j) ψ hψ)
      (le_of_lt (ha j))
    simpa only [Finset.mul_sum,mul_left_comm,p,v] using hh
  exact havg.trans (by linarith [hsum])

end PolynomialPEPS.Subvolume.Pinning

namespace PolynomialPEPS.Subvolume.GeometricComparison
open scoped BigOperators
open PolynomialPEPS.Subvolume.RectangleContours PolynomialPEPS.Subvolume.HarmonicWeights
open PolynomialPEPS.Subvolume.GeometricLower
variable {L q : ℕ}

theorem rectangle_weighted_conditional_contraction (hq : 0 < q) (J Δ E₀ : ℝ)
    (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hv : Vertex L → Operator L q) (he : Edge L → Operator L q) (Ω : State L q)
    (hΩ : ‖Ω‖=1) (hH : IsGridHamiltonian J hv he)
    (hg : asMap (Hamiltonian hv he) Ω=(E₀:ℂ) • Ω)
    (hgap : FullSystemGap (Hamiltonian hv he) Ω E₀ Δ)
    (lo₁ hi₁ lo₂ hi₂ : ℤ) (r : ℕ) (hr : 0 < r)
    (h₁ : hi₁-lo₁+1 ≤ r) (h₂ : hi₂-lo₂+1 ≤ r) :
    let C := rectangle (L:=L) lo₁ hi₁ lo₂ hi₂ 0
    let n := 2^(blocks q J Δ)*r
    let X := fun j => rectangle (L:=L) lo₁ hi₁ lo₂ hi₂ (j+1)
    (∑ j ∈ Finset.range n, weight r n j *
      (vonNeumannEntropy Ω (X j)-vonNeumannEntropy Ω (X j \ C))) ≤
      vonNeumannEntropy Ω C+bufferConstant q J Δ*(r:ℝ) := by
  let C := rectangle (L:=L) lo₁ hi₁ lo₂ hi₂ 0
  let n := 2^(blocks q J Δ)*r
  let X := fun j => rectangle (L:=L) lo₁ hi₁ lo₂ hi₂ (j+1)
  obtain ⟨F,hF,_,hlow⟩ := rectangle_optimizer_entropy_lower hq J Δ E₀ hJ hΔ hv he Ω hΩ hH hg hgap
    lo₁ hi₁ lo₂ hi₂ r hr h₁ h₂
  change (∑ j ∈ Finset.range n, weight r n j*vonNeumannEntropy Ω (X j))-
    bufferConstant q J Δ*(r:ℝ) ≤ -Real.log (‖filteredVector F Ω‖^2) at hlow
  have hn : 0<n := Nat.mul_pos (pow_pos (by omega) _) hr
  have hweights := buffer_weights r (blocks q J Δ) hr (blocks_large q J Δ).1
    (fun j => (boundaryCard (X j):ℝ))
    (fun j _ => rectangle_boundary_weight lo₁ hi₁ lo₂ hi₂ r j hr h₁ h₂)
  have hu := Pinning.optimizer_cost_le_core_add_shell_entropy hq C X
    (fun j k hjk => monotone_rectangle lo₁ hi₁ lo₂ hi₂ (Nat.add_le_add_right hjk 1))
    (fun j => monotone_rectangle lo₁ hi₁ lo₂ hi₂ (Nat.zero_le _))
    (weight r n) (fun j => (hweights.1 j).1) Ω hΩ n hn F hF
  simp only [mul_sub,Finset.sum_sub_distrib]
  linarith only [hlow,hu]

end PolynomialPEPS.Subvolume.GeometricComparison

end

end OAI
