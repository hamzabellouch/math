import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.EntropyHolder
import OAI.MathematicalPhysics.PEPSSubvolume.OptimizerExistence

namespace OAI

/-! Reoptimized prefix costs and nested entropy lower comparisons. -/

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
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.PrefixLower
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder
variable {L q n : ℕ}

theorem ordered_product_succ {X : Fin (n+1) → Finset (Vertex L)}
    (F : FilterFamily q (n+1) X) :
    orderedFilterProduct F = liftLocal (X (Fin.last n)) (F (Fin.last n)).matrix *
      orderedFilterProduct (fun j : Fin n => F j.castSucc) := by
  simp only [orderedFilterProduct,List.finRange_succ_last,List.foldl_append,List.foldl_map,
    List.foldl_cons,List.foldl_nil]

theorem filtered_vector_succ {X : Fin (n+1) → Finset (Vertex L)}
    (F : FilterFamily q (n+1) X) (ψ : State L q) :
    filteredVector F ψ = asMap (liftLocal (X (Fin.last n)) (F (Fin.last n)).matrix)
      (filteredVector (fun j : Fin n => F j.castSucc) ψ) := by
  rw [filteredVector,ordered_product_succ]
  simp only [asMap,map_mul,mul_apply_eq_comp]
  rfl

theorem optimized_prefix_amplitude {X : Fin (n+1) → Finset (Vertex L)}
    (a : Fin (n+1) → ℝ) (ψ : State L q)
    (F : FilterFamily q (n+1) X) (hF : FilterFeasible a F)
    (G : FilterFamily q n (fun j => X j.castSucc))
    (hG : IsFilterOptimizer ψ (fun j : Fin n => a j.castSucc) G) :
    ‖inner ℂ ψ (filteredVector F ψ)‖ ≤
      ‖asMap (liftLocal (X (Fin.last n)) (F (Fin.last n)).matrix) ψ‖ *
        ‖filteredVector G ψ‖ := by
  let A := asMap (liftLocal (X (Fin.last n)) (F (Fin.last n)).matrix)
  have hself : IsSelfAdjoint A :=
    (((F (Fin.last n)).positive.isHermitian.isSelfAdjoint.map
      (localLiftHom (X (Fin.last n)))).map Matrix.toEuclideanCLM)
  have hpre := hG.2 (fun j : Fin n => F j.castSucc) (fun j => hF j.castSucc)
  rw [filtered_vector_succ]
  change ‖inner ℂ ψ (A (filteredVector (fun j : Fin n => F j.castSucc) ψ))‖ ≤ ‖A ψ‖ * _
  have hi : inner ℂ (A ψ) (filteredVector (fun j : Fin n => F j.castSucc) ψ) =
      inner ℂ ψ (A (filteredVector (fun j : Fin n => F j.castSucc) ψ)) :=
    hself.isSymmetric ψ (filteredVector (fun j : Fin n => F j.castSucc) ψ)
  rw [← hi]
  exact (norm_inner_le_norm (A ψ) (filteredVector (fun j : Fin n => F j.castSucc) ψ)).trans
    (mul_le_mul_of_nonneg_left hpre (norm_nonneg _))

theorem optimized_prefix_overlap {X : Fin (n+1) → Finset (Vertex L)}
    (a : Fin (n+1) → ℝ) (ψ : State L q)
    (F : FilterFamily q (n+1) X) (hF : FilterFeasible a F)
    (G : FilterFamily q n (fun j => X j.castSucc))
    (hG : IsFilterOptimizer ψ (fun j : Fin n => a j.castSucc) G)
    (hN : 0 < ‖filteredVector F ψ‖) :
    ‖filteredVector F ψ‖ * ‖inner ℂ ψ
      (((‖filteredVector F ψ‖⁻¹ : ℝ) : ℂ) • filteredVector F ψ)‖ ≤
      ‖asMap (liftLocal (X (Fin.last n)) (F (Fin.last n)).matrix) ψ‖ *
        ‖filteredVector G ψ‖ := by
  have h := optimized_prefix_amplitude a ψ F hF G hG
  simpa only [inner_smul_right,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_inv,abs_norm,← mul_assoc,mul_inv_cancel₀ (ne_of_gt hN),one_mul] using h

end PolynomialPEPS.Subvolume.PrefixLower

namespace PolynomialPEPS.Subvolume.NestedLower
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
open PolynomialPEPS.Subvolume.SpectralCurve PolynomialPEPS.Subvolume.HermitianReplacement
open PolynomialPEPS.Subvolume.ContourEnergy PolynomialPEPS.Subvolume.OptimizerNeutral
open PolynomialPEPS.Subvolume.PhysicalCurve PolynomialPEPS.Subvolume.PrefixLower
variable {L q : ℕ}

lemma curve_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) (r : ι → ℝ) (z : ℂ) : IsUnit (curve U r z) := by
  apply isUnit_iff_exists.mpr
  refine ⟨curve U r (-z),?_,?_⟩
  · rw [← curve_add,add_neg_cancel,curve_zero]
  · rw [← curve_add,neg_add_cancel,curve_zero]

lemma norm_asMap_pos (M : Operator L q) (hM : IsUnit M)
    (Ω : State L q) (hΩ : Ω≠0) : 0 < ‖asMap M Ω‖ := by
  apply norm_pos_iff.mpr
  intro hz
  have hu : IsUnit (Matrix.toEuclideanCLM (𝕜:=ℂ) (n:=Configuration L q) M) :=
    hM.map Matrix.toEuclideanCLM
  obtain ⟨T,hT⟩ := hu.exists_left_inv
  have hv := congrArg (fun f : State L q →L[ℂ] State L q => f Ω) hT
  change T (asMap M Ω)=Ω at hv
  rw [hz,map_zero] at hv
  exact hΩ hv.symm

lemma optimizer_norm_pos (hq : 0 < q) {n : ℕ} {X : Fin n → Finset (Vertex L)}
    (a : Fin n → ℝ) (ha : ∀ j, 0 < a j) (Ω : State L q) (hΩ : ‖Ω‖=1)
    (F : FilterFamily q n X) (hF : IsFilterOptimizer Ω a F) : 0 < ‖filteredVector F Ω‖ := by
  classical
  let : Nonempty (Fin q) := ⟨⟨0,hq⟩⟩
  let p (j : Fin n) : RegionConfiguration q (X j) → ℝ := fun _ =>
    (Fintype.card (RegionConfiguration q (X j)) : ℝ)⁻¹
  have hp (j : Fin n) (i : RegionConfiguration q (X j)) : 0 < p j i := by
    dsimp [p]
    positivity
  have hs (j : Fin n) : ∑ i,p j i=1 := by
    simp only [p,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [mul_inv_cancel₀ (by positivity)]
  let r (j : Fin n) := fun i => a j/2*Real.log (p j i)
  let G : FilterFamily q n X := fun j => ⟨curve 1 (r j) 1,curve_posSemidef 1 (r j) 1⟩
  have hG : FilterFeasible a G := fun j => tracePower_curve_one 1 (p j) (hp j) (hs j) (a j) (ha j)
  have hfold (l : List (Fin n)) : ∀ P : Operator L q, IsUnit P →
      IsUnit (l.foldl (fun A j => liftLocal (X j) (G j).matrix*A) P) := by
    induction l with
    | nil => intro P hP; exact hP
    | cons j l ih =>
      intro P hP
      exact ih _ (((curve_isUnit 1 (r j) 1).map (localLiftHom (X j))).mul hP)
  have hpos : 0 < ‖filteredVector G Ω‖ := norm_asMap_pos _ (hfold _ 1 isUnit_one) Ω
    (norm_ne_zero_iff.mp (by rw [hΩ]; norm_num))
  exact hpos.trans_le (hF.2 G hG)

def extend (X : ℕ → Finset (Vertex L)) (n : ℕ)
    (F : FilterFamily q n (fun j => X j.val)) (j : ℕ) : LocalPositiveFilter q (X j) :=
  if h : j<n then F ⟨j,h⟩ else ⟨0,Matrix.PosSemidef.zero⟩

@[simp] lemma extend_fin (X : ℕ → Finset (Vertex L)) (n : ℕ)
    (F : FilterFamily q n (fun j => X j.val)) (j : Fin n) : extend X n F j=F j := by
  simp only [extend,dite_eq_left j.isLt]

lemma optimizer_half_fidelity (hq : 0 < q) (J Δ E₀ : ℝ) (hJ : 0≤J) (hΔ : 0 < Δ)
    (hv : Vertex L → Operator L q) (he : Edge L → Operator L q) (Ω : State L q)
    (hH : IsGridHamiltonian J hv he)
    (hg : asMap (Hamiltonian hv he) Ω=(E₀:ℂ) • Ω)
    (hgap : FullSystemGap (Hamiltonian hv he) Ω E₀ Δ)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X) (a : ℕ → ℝ) (n : ℕ)
    (F : FilterFamily q n (fun j => X j.val))
    (hF : IsFilterOptimizer Ω (fun j => a j.val) F)
    (ha : ∀ j, j<n → 0 < a j ∧ a j≤1/2)
    (hunique : ∀ e : Edge L, ∀ j k, j<n → k<n →
      Splits (EdgeSites e) (X j) → Splits (EdgeSites e) (X k) → j=k)
    (hbudget : (8*(q:ℝ)^2*J/Δ)*(∑ j ∈ Finset.range n, (a j)^2*(boundaryCard (X j):ℝ))≤1/2) :
    (1/2:ℝ)*‖filteredVector F Ω‖^2≤‖inner ℂ Ω (filteredVector F Ω)‖^2 := by
  let G := extend X n F
  have hG : IsFilterOptimizer Ω (fun j : Fin n => a j.val) (fun j : Fin n => G j.val) := by
    simpa only [G,extend_fin] using hF
  let vh := fun v => symmetrize (hv v)
  let eh := fun e => symmetrize (he e)
  have heq : Hamiltonian vh eh=Hamiltonian hv he := replacement_preserves_H hv he hH.2.2
  have hb := optimizer_excitation_bound hq X hX a Ω n G hG ha hunique vh eh
    (fun v => symmetrize_supported _ _ (hH.1 v).1)
    (fun e => symmetrize_supported _ _ (hH.2.1 e).1)
    (fun e => symmetrize_hermitian (he e)) J E₀ hJ
    (fun e => (symmetrize_norm _).trans (hH.2.1 e).2) (by rwa [heq])
  have hvect : asMap (orderedPrefix (fun j => liftLocal (X j) (G j).matrix) n) Ω=filteredVector F Ω := by
    rw [← orderedFilterProduct_eq_prefix]
    simp only [G,extend_fin,filteredVector]
  dsimp only at hb
  rw [heq,hvect] at hb
  have hf := gap_fidelity (Hamiltonian hv he) Ω (filteredVector F Ω) E₀ Δ
    (8*(q:ℝ)^2*J*(∑ j : Fin n, (a j)^2*(boundaryCard (X j):ℝ))) hgap hΔ hb
  have hs : (∑ j : Fin n, (a j)^2*(boundaryCard (X j):ℝ))=
      ∑ j ∈ Finset.range n, (a j)^2*(boundaryCard (X j):ℝ) := Fin.sum_univ_eq_sum_range (fun j => (a j)^2*(boundaryCard (X j):ℝ)) n
  rw [hs] at hf
  have he : 8*(q:ℝ)^2*J*(∑ j ∈ Finset.range n, (a j)^2*(boundaryCard (X j):ℝ))/Δ=
      (8*(q:ℝ)^2*J/Δ)*(∑ j ∈ Finset.range n, (a j)^2*(boundaryCard (X j):ℝ)) := by ring
  rw [he] at hf
  nlinarith [sq_nonneg ‖filteredVector F Ω‖]

end PolynomialPEPS.Subvolume.NestedLower

namespace PolynomialPEPS.Subvolume.NestedLower
open scoped BigOperators Matrix.Norms.L2Operator
open PolynomialPEPS.Subvolume.ContourEnergy PolynomialPEPS.Subvolume.PrefixLower
variable {L q : ℕ}

lemma boundary_budget_mono (X : ℕ → Finset (Vertex L)) (a : ℕ → ℝ) (n m : ℕ) (hnm : n ≤ m) :
    (∑ j ∈ Finset.range n, (a j)^2*(boundaryCard (X j):ℝ)) ≤ ∑ j ∈ Finset.range m, (a j)^2*(boundaryCard (X j):ℝ) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm)
  intro j _ _
  positivity

theorem optimizer_norm_bound (hq : 0 < q) (J Δ E₀ : ℝ) (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hv : Vertex L → Operator L q) (he : Edge L → Operator L q) (Ω : State L q)
    (hΩ : ‖Ω‖=1) (hH : IsGridHamiltonian J hv he)
    (hg : asMap (Hamiltonian hv he) Ω=(E₀:ℂ) • Ω)
    (hgap : FullSystemGap (Hamiltonian hv he) Ω E₀ Δ)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X) (a : ℕ → ℝ) :
    ∀ n : ℕ,
    (∀ j, j < n → 0 < a j ∧ a j ≤ 1/8) →
    (∀ e : Edge L, ∀ j k, j < n → k < n →
      Splits (EdgeSites e) (X j) → Splits (EdgeSites e) (X k) → j=k) →
    (∀ j, j < n → (32*(q:ℝ)^2*J*(boundaryCard (X j):ℝ)/Δ)*(a j)^2 ≤ 1/8) →
    ((8*(q:ℝ)^2*J/Δ)*(∑ j ∈ Finset.range n, (a j)^2*(boundaryCard (X j):ℝ)) ≤ 1/2) →
    ∀ F : FilterFamily q n (fun j => X j.val),
      IsFilterOptimizer Ω (fun j => a j.val) F →
    ‖filteredVector F Ω‖^2 ≤ Real.exp ((∑ j ∈ Finset.range n,
      (-a j*vonNeumannEntropy Ω (X j)+(256*(q:ℝ)^2*J*(boundaryCard (X j):ℝ)/Δ)*(a j)^2))+
      (n:ℝ)*Real.log 2) := by
  intro n
  induction n with
  | zero =>
    intro ha hu hs hb F hF
    simp [filteredVector,orderedFilterProduct,asMap,hΩ]
  | succ n ih =>
    intro ha hu hs hb F hF
    have han : 0 < a n ∧ a n ≤ 1/8 := ha n (Nat.lt_succ_self n)
    obtain ⟨G,hG⟩ := OptimizerExistence.exists_optimizer hq
      (X := fun j : Fin n => X j.val) (fun j : Fin n => a j.val)
      (fun j => (ha j (Nat.lt_trans j.isLt (Nat.lt_succ_self n))).1) Ω
    have hbn : (8*(q:ℝ)^2*J/Δ)*(∑ j ∈ Finset.range n, (a j)^2*(boundaryCard (X j):ℝ)) ≤ 1/2 := by
      apply le_trans _ hb
      exact mul_le_mul_of_nonneg_left (boundary_budget_mono X a n (n+1) (Nat.le_succ n)) (by positivity)
    have hgpre := ih (fun j hj => ha j (Nat.lt_succ_of_lt hj))
      (fun e j k hj hk => hu e j k (Nat.lt_succ_of_lt hj) (Nat.lt_succ_of_lt hk))
      (fun j hj => hs j (Nat.lt_succ_of_lt hj)) hbn G hG
    have hlast := GroundMGF.single_filter_entropy hq J Δ E₀ hJ hΔ hv he Ω hΩ hH hg hgap
      (X n) (F (Fin.last n)) (a n) han.1 han.2 (hs n (Nat.lt_succ_self n)) (hF.1 (Fin.last n))
    have hf := optimizer_half_fidelity hq J Δ E₀ hJ hΔ hv he Ω hH hg hgap X hX a (n+1) F hF
      (fun j hj => ⟨(ha j hj).1,le_trans (ha j hj).2 (by norm_num)⟩) hu hb
    have hp := optimized_prefix_amplitude (fun j : Fin (n+1) => a j.val) Ω F hF.1 G hG
    have hp2 := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr hp
    rw [mul_pow] at hp2
    change ‖inner ℂ Ω (filteredVector F Ω)‖^2 ≤
      ‖asMap (liftLocal (X n) (F (Fin.last n)).matrix) Ω‖^2*‖filteredVector G Ω‖^2 at hp2
    have hbprod := mul_le_mul hlast hgpre (sq_nonneg ‖filteredVector G Ω‖)
      (Real.exp_pos _).le
    calc
      _ ≤ 2*(‖asMap (liftLocal (X n) (F (Fin.last n)).matrix) Ω‖^2*‖filteredVector G Ω‖^2) := by
        nlinarith only [hf,hp2]
      _ ≤ 2*(Real.exp (-a n*vonNeumannEntropy Ω (X n)+
          (256*(q:ℝ)^2*J*(boundaryCard (X n):ℝ)/Δ)*(a n)^2)*
        Real.exp ((∑ j ∈ Finset.range n, (-a j*vonNeumannEntropy Ω (X j)+
          (256*(q:ℝ)^2*J*(boundaryCard (X j):ℝ)/Δ)*(a j)^2))+(n:ℝ)*Real.log 2)) :=
        mul_le_mul_of_nonneg_left hbprod (by norm_num)
      _ = _ := by
        rw [Finset.sum_range_succ,Nat.cast_add,Nat.cast_one]
        rw [show (∑ j ∈ Finset.range n, (-a j*vonNeumannEntropy Ω (X j)+
          (256*(q:ℝ)^2*J*(boundaryCard (X j):ℝ)/Δ)*(a j)^2))+
          (-a n*vonNeumannEntropy Ω (X n)+(256*(q:ℝ)^2*J*(boundaryCard (X n):ℝ)/Δ)*(a n)^2)+
          ((n:ℝ)+1)*Real.log 2 = Real.log 2+
          ((-a n*vonNeumannEntropy Ω (X n)+(256*(q:ℝ)^2*J*(boundaryCard (X n):ℝ)/Δ)*(a n)^2)+
          ((∑ j ∈ Finset.range n, (-a j*vonNeumannEntropy Ω (X j)+
          (256*(q:ℝ)^2*J*(boundaryCard (X j):ℝ)/Δ)*(a j)^2))+(n:ℝ)*Real.log 2)) by ring]
        simp only [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ) < 2)]

theorem optimizer_entropy_lower (hq : 0 < q) (J Δ E₀ : ℝ) (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hv : Vertex L → Operator L q) (he : Edge L → Operator L q) (Ω : State L q)
    (hΩ : ‖Ω‖=1) (hH : IsGridHamiltonian J hv he)
    (hg : asMap (Hamiltonian hv he) Ω=(E₀:ℂ) • Ω)
    (hgap : FullSystemGap (Hamiltonian hv he) Ω E₀ Δ)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X) (a : ℕ → ℝ) (n : ℕ)
    (ha : ∀ j, j < n → 0 < a j ∧ a j ≤ 1/8)
    (hu : ∀ e : Edge L, ∀ j k, j < n → k < n →
      Splits (EdgeSites e) (X j) → Splits (EdgeSites e) (X k) → j=k)
    (hs : ∀ j, j < n → (32*(q:ℝ)^2*J*(boundaryCard (X j):ℝ)/Δ)*(a j)^2 ≤ 1/8)
    (hb : (8*(q:ℝ)^2*J/Δ)*(∑ j ∈ Finset.range n, (a j)^2*(boundaryCard (X j):ℝ)) ≤ 1/2)
    (F : FilterFamily q n (fun j => X j.val))
    (hF : IsFilterOptimizer Ω (fun j => a j.val) F) :
    (∑ j ∈ Finset.range n, a j*vonNeumannEntropy Ω (X j)) -
      ((n:ℝ)*Real.log 2+(∑ j ∈ Finset.range n,
        (256*(q:ℝ)^2*J*(boundaryCard (X j):ℝ)/Δ)*(a j)^2)) ≤ -Real.log (‖filteredVector F Ω‖^2) := by
  have hn := optimizer_norm_pos hq (fun j : Fin n => a j.val) (fun j => (ha j j.isLt).1) Ω hΩ F hF
  have h := optimizer_norm_bound hq J Δ E₀ hJ hΔ hv he Ω hΩ hH hg hgap X hX a n ha hu hs hb F hF
  have hl := Real.log_le_log (sq_pos_of_pos hn) h
  rw [Real.log_exp] at hl
  simp only [Finset.sum_add_distrib,neg_mul,Finset.sum_neg_distrib] at hl
  linarith

end PolynomialPEPS.Subvolume.NestedLower

end

end OAI
