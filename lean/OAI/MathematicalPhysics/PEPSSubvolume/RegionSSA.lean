import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.PinnedEntropy
import OAI.MathematicalPhysics.PEPSSubvolume.SSARegularized

namespace OAI

/-! Physical-region entropy submodularity and buffer bounds. -/

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
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.RegionSSA
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
open Matrix QuantumSSA Pinning PhysicalModular LocalTensorDecomposition LocalBlocks
variable {L q : ℕ}

theorem density_between_dual (Ω : State L q) {C X : Finset (Vertex L)} (hCX : C ⊆ X)
    (a : Matrix (RegionConfiguration q C) (RegionConfiguration q C) ℂ) :
    (reducedDensity Ω X * liftBetween hCX a).trace=(reducedDensity Ω C*a).trace := by
  rw [Matrix.trace_mul_comm,← inner_liftLocal_trace, liftLocal_liftBetween,inner_liftLocal_trace,
    Matrix.trace_mul_comm]

theorem split_tensorLeft (hq : 0<q) (C X : Finset (Vertex L)) (hCX : C ⊆ X)
    (a : Matrix (RegionConfiguration q C) (RegionConfiguration q C) ℂ) :
    reindexHom (splitEquiv C X hCX) (tensorLeftHom a)=liftBetween hCX a := by
  have h1 : liftBetween (Finset.sdiff_subset : X\C ⊆ X) (1 : Matrix (RegionConfiguration q (X\C)) _ ℂ)=1 :=
    (liftBetweenHom hq Finset.sdiff_subset).map_one
  change Matrix.reindex (splitEquiv C X hCX) (splitEquiv C X hCX)
    (a ⊗ₖ (1 : Matrix (RegionConfiguration q (X\C)) _ ℂ))=_
  simpa only [h1,Matrix.mul_one,Matrix.kronecker] using lift_split_tensor C X hCX a 1

theorem split_tensorRight (hq : 0<q) (C X : Finset (Vertex L)) (hCX : C ⊆ X)
    (a : Matrix (RegionConfiguration q (X\C)) (RegionConfiguration q (X\C)) ℂ) :
    reindexHom (splitEquiv C X hCX) (tensorRightHom a)=liftBetween Finset.sdiff_subset a := by
  have h1 : liftBetween hCX (1 : Matrix (RegionConfiguration q C) _ ℂ)=1 :=
    (liftBetweenHom hq hCX).map_one
  change Matrix.reindex (splitEquiv C X hCX) (splitEquiv C X hCX)
    ((1 : Matrix (RegionConfiguration q C) _ ℂ) ⊗ₖ a)=_
  simpa only [h1,Matrix.one_mul,Matrix.kronecker] using lift_split_tensor C X hCX 1 a

theorem density_ptrR (hq : 0<q) (Ω : State L q) (C X : Finset (Vertex L)) (hCX : C ⊆ X) :
    ptrR (reindexHom (splitEquiv C X hCX).symm (reducedDensity Ω X))=reducedDensity Ω C := by
  classical
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro a
  rw [← ptrR_dual,← trace_mul_reindexHom]
  change (reducedDensity Ω X * reindexHom (splitEquiv C X hCX) (tensorLeftHom a)).trace=_
  rw [split_tensorLeft hq,density_between_dual]

theorem density_ptrL (hq : 0<q) (Ω : State L q) (C X : Finset (Vertex L)) (hCX : C ⊆ X) :
    ptrL (reindexHom (splitEquiv C X hCX).symm (reducedDensity Ω X))=reducedDensity Ω (X\C) := by
  classical
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro a
  rw [← ptrL_dual,← trace_mul_reindexHom]
  change (reducedDensity Ω X * reindexHom (splitEquiv C X hCX) (tensorRightHom a)).trace=_
  rw [split_tensorRight hq,density_between_dual]

theorem traceEntropy_density (Ω : State L q) (X : Finset (Vertex L)) :
    traceEntropy (reducedDensity Ω X)=vonNeumannEntropy Ω X :=
  traceEntropy_spectral _ (reducedDensity_isHermitian Ω X)

end PolynomialPEPS.Subvolume.RegionSSA

namespace PolynomialPEPS.Subvolume.RegionSSA
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
open Matrix QuantumSSA Pinning PhysicalModular LocalTensorDecomposition LocalBlocks
variable {L q : ℕ}

def shellPairEquiv (C X Y : Finset (Vertex L)) (hCX : C ⊆ X) (hXY : X ⊆ Y) :
    (RegionConfiguration q (X\C) × RegionConfiguration q (Y\X)) ≃
      RegionConfiguration q (Y\C) where
  toFun w v := if h : v.val∈X then w.1 ⟨v,Finset.mem_sdiff.mpr
    ⟨h,(Finset.mem_sdiff.mp v.property).2⟩⟩ else w.2 ⟨v,Finset.mem_sdiff.mpr
    ⟨(Finset.mem_sdiff.mp v.property).1,h⟩⟩
  invFun w := (fun v => w ⟨v,Finset.mem_sdiff.mpr
    ⟨hXY (Finset.mem_sdiff.mp v.property).1,(Finset.mem_sdiff.mp v.property).2⟩⟩,
    fun v => w ⟨v,Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp v.property).1,
      fun hc => (Finset.mem_sdiff.mp v.property).2 (hCX hc)⟩⟩)
  left_inv w := by
    apply Prod.ext <;> funext v
    · simp [(Finset.mem_sdiff.mp v.property).1]
    · simp [(Finset.mem_sdiff.mp v.property).2]
  right_inv w := by
    funext v
    dsimp only
    split_ifs <;> rfl

theorem join_three (C X Y : Finset (Vertex L)) (hCX : C ⊆ X) (hXY : X ⊆ Y)
    (u : RegionConfiguration q C) (w : RegionConfiguration q (X\C))
    (z : RegionConfiguration q (Y\X)) :
    joinWithin X Y (joinWithin C X u w) z =
      joinWithin C Y u (shellPairEquiv C X Y hCX hXY (w,z)) := by
  funext v
  by_cases hc : v.val∈C
  · simp [joinWithin,hc,hCX hc]
  · by_cases hx : v.val∈X <;> simp [joinWithin,hc,hx,shellPairEquiv]

variable {m n p k : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype k]
  [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq k]

theorem ptrR_reindex_left (e : m ≃ k) (A : Matrix (m×n) (m×n) ℂ) :
    ptrR (reindexHom (Equiv.prodCongr e (Equiv.refl n)) A)=reindexHom e (ptrR A) := rfl

theorem ptrL_reindex_right (e : n ≃ k) (A : Matrix (m×n) (m×n) ℂ) :
    ptrL (reindexHom (Equiv.prodCongr (Equiv.refl m) e) A)=reindexHom e (ptrL A) := rfl

end PolynomialPEPS.Subvolume.RegionSSA

namespace PolynomialPEPS.Subvolume.RegionSSA
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
open Matrix QuantumSSA Pinning PhysicalModular LocalTensorDecomposition LocalBlocks
variable {L q : ℕ}

theorem conditional_entropy_antitone (hq : 0<q) (Ω : State L q)
    (C X Y : Finset (Vertex L)) (hCX : C ⊆ X) (hXY : X ⊆ Y) :
    vonNeumannEntropy Ω Y-vonNeumannEntropy Ω (Y\C) ≤
      vonNeumannEntropy Ω X-vonNeumannEntropy Ω (X\C) := by
  classical
  let : Nonempty (RegionConfiguration q C) := ⟨fun _ => ⟨0,hq⟩⟩
  let : Nonempty (RegionConfiguration q (Y\X)) := ⟨fun _ => ⟨0,hq⟩⟩
  let eC := splitEquiv (q:=q) C X hCX
  let eX := splitEquiv (q:=q) X Y hXY
  let eS := shellPairEquiv (q:=q) C X Y hCX hXY
  let A := reindexHom (Equiv.prodCongr eC.symm (Equiv.refl (RegionConfiguration q (Y\X))))
    (reindexHom eX.symm (reducedDensity Ω Y))
  have hA : A.PosSemidef := reindexHom_posSemidef _
    (reindexHom_posSemidef _ (reducedDensity_posSemidef Ω Y))
  have hR : ptrR A=reindexHom eC.symm (reducedDensity Ω X) := by
    dsimp only [A]
    rw [ptrR_reindex_left,density_ptrR hq]
  have hassoc : assocMatrix A =
      reindexHom (Equiv.prodCongr (Equiv.refl (RegionConfiguration q C)) eS.symm)
        (reindexHom (splitEquiv C Y (hCX.trans hXY)).symm (reducedDensity Ω Y)) := by
    ext x y
    change reducedDensity Ω Y
      (joinWithin X Y (joinWithin C X x.1 x.2.1) x.2.2)
      (joinWithin X Y (joinWithin C X y.1 y.2.1) y.2.2) =
        reducedDensity Ω Y (joinWithin C Y x.1 (eS (x.2.1,x.2.2)))
          (joinWithin C Y y.1 (eS (y.2.1,y.2.2)))
    rw [join_three C X Y hCX hXY,join_three C X Y hCX hXY]
  have hD : ptrL (assocMatrix A)=reindexHom eS.symm (reducedDensity Ω (Y\C)) := by
    rw [hassoc,ptrL_reindex_right,density_ptrL hq]
  have hM : ptrR (ptrL (assocMatrix A))=reducedDensity Ω (X\C) := by
    rw [← ptrL_ptrR_assoc,hR,density_ptrL hq]
  have heA : traceEntropy A=vonNeumannEntropy Ω Y := by
    dsimp only [A]
    rw [entropy_reindexHom _ (reindexHom_posSemidef _ (reducedDensity_posSemidef Ω Y)).isHermitian,
      entropy_reindexHom _ (reducedDensity_isHermitian Ω Y),traceEntropy_density]
  have hh := strong_subadditivity hA
  rw [heA,hM,hR,hD,entropy_reindexHom _ (reducedDensity_isHermitian Ω X),
    entropy_reindexHom _ (reducedDensity_isHermitian Ω (Y\C)),
    traceEntropy_density,traceEntropy_density,traceEntropy_density] at hh
  linarith only [hh]

end PolynomialPEPS.Subvolume.RegionSSA

namespace PolynomialPEPS.Subvolume.GeometricComparison
open scoped BigOperators
open PolynomialPEPS.Subvolume.RectangleContours PolynomialPEPS.Subvolume.HarmonicWeights
open PolynomialPEPS.Subvolume.GeometricLower
variable {L q : ℕ}

theorem rectangle_conditional_contraction (hq : 0 < q) (J Δ E₀ : ℝ)
    (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hv : Vertex L → Operator L q) (he : Edge L → Operator L q) (Ω : State L q)
    (hΩ : ‖Ω‖=1) (hH : IsGridHamiltonian J hv he)
    (hg : asMap (Hamiltonian hv he) Ω=(E₀:ℂ) • Ω)
    (hgap : FullSystemGap (Hamiltonian hv he) Ω E₀ Δ)
    (lo₁ hi₁ lo₂ hi₂ : ℤ) (r : ℕ) (hr : 0 < r)
    (h₁ : hi₁-lo₁+1 ≤ r) (h₂ : hi₂-lo₂+1 ≤ r) :
    let C := rectangle (L:=L) lo₁ hi₁ lo₂ hi₂ 0
    let n := 2^(blocks q J Δ)*r
    let Y := rectangle (L:=L) lo₁ hi₁ lo₂ hi₂ n
    vonNeumannEntropy Ω Y-vonNeumannEntropy Ω (Y\C) ≤
      vonNeumannEntropy Ω C/4+bufferConstant q J Δ*(r:ℝ)/4 := by
  let C := rectangle (L:=L) lo₁ hi₁ lo₂ hi₂ 0
  let n := 2^(blocks q J Δ)*r
  let Y := rectangle (L:=L) lo₁ hi₁ lo₂ hi₂ n
  let X := fun j => rectangle (L:=L) lo₁ hi₁ lo₂ hi₂ (j+1)
  have hn : 0<n := Nat.mul_pos (pow_pos (by omega) _) hr
  have hc := rectangle_weighted_conditional_contraction hq J Δ E₀ hJ hΔ hv he Ω
    hΩ hH hg hgap lo₁ hi₁ lo₂ hi₂ r hr h₁ h₂
  have hs : 4*(vonNeumannEntropy Ω Y-vonNeumannEntropy Ω (Y\C)) ≤
      ∑ j ∈ Finset.range n, weight r n j*
        (vonNeumannEntropy Ω (X j)-vonNeumannEntropy Ω (X j\C)) := by
    calc
      _ = (∑ j ∈ Finset.range n, weight r n j)*
          (vonNeumannEntropy Ω Y-vonNeumannEntropy Ω (Y\C)) := by rw [sum_weight r n hr hn]
      _ = ∑ j ∈ Finset.range n, weight r n j*
          (vonNeumannEntropy Ω Y-vonNeumannEntropy Ω (Y\C)) := Finset.sum_mul ..
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (weight_pos r n j hr hn))
        exact RegionSSA.conditional_entropy_antitone hq Ω C (X j) Y
          (monotone_rectangle lo₁ hi₁ lo₂ hi₂ (Nat.zero_le _))
          (monotone_rectangle lo₁ hi₁ lo₂ hi₂ (by have := Finset.mem_range.mp hj; omega))
  change _ ≤ vonNeumannEntropy Ω C+bufferConstant q J Δ*(r:ℝ) at hc
  change vonNeumannEntropy Ω Y-vonNeumannEntropy Ω (Y\C) ≤ _
  linarith only [hc,hs]

end PolynomialPEPS.Subvolume.GeometricComparison

end

end OAI
