import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.NestedLower
import OAI.MathematicalPhysics.PEPSSubvolume.RectangleContours
import OAI.MathematicalPhysics.PEPSSubvolume.HarmonicWeights

namespace OAI

/-! Uniform geometric-buffer entropy lower bounds. -/

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

namespace PolynomialPEPS.Subvolume.GeometricLower
open scoped BigOperators
open PolynomialPEPS.Subvolume.RectangleContours PolynomialPEPS.Subvolume.HarmonicWeights
open PolynomialPEPS.Subvolume.ContourEnergy PolynomialPEPS.Subvolume.NestedLower
variable {L q : ℕ}

def blocks (q : ℕ) (J Δ : ℝ) : ℕ := 96+Nat.ceil (147456*(q:ℝ)^2*J/Δ)

def bufferConstant (q : ℕ) (J Δ : ℝ) : ℝ := (2:ℝ)^(blocks q J Δ)*Real.log 2+1

lemma blocks_large (q : ℕ) (J Δ : ℝ) :
    96 ≤ blocks q J Δ ∧ 147456*(q:ℝ)^2*J/Δ ≤ (blocks q J Δ:ℝ) := by
  constructor
  · exact Nat.le_add_right _ _
  · exact (Nat.le_ceil _).trans (by simp only [blocks,Nat.cast_add,Nat.cast_ofNat]; linarith)

lemma rectangle_boundary_weight (lo₁ hi₁ lo₂ hi₂ : ℤ) (r j : ℕ) (hr : 0 < r)
    (h₁ : hi₁-lo₁+1 ≤ r) (h₂ : hi₂-lo₂+1 ≤ r) :
    (boundaryCard (rectangle (L:=L) lo₁ hi₁ lo₂ hi₂ (j+1)):ℝ) ≤ 12*((r:ℝ)+j) := by
  have h := boundaryCard_le (L:=L) lo₁ hi₁ lo₂ hi₂ (j+1) r h₁ h₂
  have h' : (boundaryCard (rectangle (L:=L) lo₁ hi₁ lo₂ hi₂ (j+1)):ℝ) ≤
      4*((r:ℝ)+2*((j:ℝ)+1)) := by exact_mod_cast h
  have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
  linarith [Nat.cast_nonneg (α:=ℝ) j]

lemma rectangle_unique_split (lo₁ hi₁ lo₂ hi₂ : ℤ) (e : Edge L) (j k : ℕ)
    (hj : Splits (EdgeSites e) (rectangle lo₁ hi₁ lo₂ hi₂ (j+1)))
    (hk : Splits (EdgeSites e) (rectangle lo₁ hi₁ lo₂ hi₂ (k+1))) : j=k := by
  have h := unique_crossing lo₁ hi₁ lo₂ hi₂ e (j+1) (k+1)
    ((edge_splits_iff e _).mp hj) ((edge_splits_iff e _).mp hk)
  omega

lemma buffer_energy (J Δ : ℝ) (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (lo₁ hi₁ lo₂ hi₂ : ℤ) (r : ℕ) (hr : 0 < r)
    (h₁ : hi₁-lo₁+1 ≤ r) (h₂ : hi₂-lo₂+1 ≤ r) :
    let n := 2^(blocks q J Δ)*r
    ((q:ℝ)^2*J/Δ)*(∑ j ∈ Finset.range n,
      (weight r n j)^2*(boundaryCard (rectangle (L:=L) lo₁ hi₁ lo₂ hi₂ (j+1)):ℝ)) ≤ 1/256 := by
  let s := blocks q J Δ
  have hs := blocks_large q J Δ
  have hs0 : 0 < (s:ℝ) := by
    have hs' : (96:ℝ) ≤ s := by exact_mod_cast hs.1
    linarith
  have hw := (buffer_weights r s hr hs.1
    (fun j => (boundaryCard (rectangle (L:=L) lo₁ hi₁ lo₂ hi₂ (j+1)):ℝ))
    (fun j _ => rectangle_boundary_weight lo₁ hi₁ lo₂ hi₂ r j hr h₁ h₂)).2.2
  apply (mul_le_mul_of_nonneg_left hw (by positivity)).trans
  apply (le_div_iff₀ (by norm_num : (0:ℝ) < 256)).mpr
  change (q:ℝ)^2*J/Δ*(576/(s:ℝ))*256 ≤ 1
  calc
    _ = (147456*(q:ℝ)^2*J/Δ)/(s:ℝ) := by ring
    _ ≤ 1 := by
      apply (div_le_iff₀ hs0).mpr
      simpa only [one_mul] using hs.2

theorem rectangle_optimizer_entropy_lower (hq : 0 < q) (J Δ E₀ : ℝ)
    (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hv : Vertex L → Operator L q) (he : Edge L → Operator L q) (Ω : State L q)
    (hΩ : ‖Ω‖=1) (hH : IsGridHamiltonian J hv he)
    (hg : asMap (Hamiltonian hv he) Ω=(E₀:ℂ) • Ω)
    (hgap : FullSystemGap (Hamiltonian hv he) Ω E₀ Δ)
    (lo₁ hi₁ lo₂ hi₂ : ℤ) (r : ℕ) (hr : 0 < r)
    (h₁ : hi₁-lo₁+1 ≤ r) (h₂ : hi₂-lo₂+1 ≤ r) :
    let n := 2^(blocks q J Δ)*r
    let X := fun j => rectangle (L:=L) lo₁ hi₁ lo₂ hi₂ (j+1)
    ∃ F : FilterFamily q n (fun j => X j.val),
      IsFilterOptimizer Ω (fun j => weight r n j.val) F ∧
      (∑ j ∈ Finset.range n, weight r n j)=4 ∧
      (∑ j ∈ Finset.range n, weight r n j*vonNeumannEntropy Ω (X j))-
        bufferConstant q J Δ*(r:ℝ) ≤ -Real.log (‖filteredVector F Ω‖^2) := by
  let s := blocks q J Δ
  let n := 2^s*r
  let X := fun j => rectangle (L:=L) lo₁ hi₁ lo₂ hi₂ (j+1)
  have hs := blocks_large q J Δ
  have hn : 0 < n := Nat.mul_pos (pow_pos (by omega) _) hr
  have hw := buffer_weights r s hr hs.1
    (fun j => (boundaryCard (X j):ℝ))
    (fun j _ => rectangle_boundary_weight lo₁ hi₁ lo₂ hi₂ r j hr h₁ h₂)
  obtain ⟨F,hF⟩ := OptimizerExistence.exists_optimizer hq
    (X := fun j : Fin n => X j.val) (fun j : Fin n => weight r n j.val)
    (fun j => (hw.1 j).1) Ω
  refine ⟨F,hF,hw.2.1,?_⟩
  have hb := buffer_energy (q:=q) (L:=L) J Δ hJ hΔ lo₁ hi₁ lo₂ hi₂ r hr h₁ h₂
  change ((q:ℝ)^2*J/Δ)*(∑ j ∈ Finset.range n, (weight r n j)^2*(boundaryCard (X j):ℝ)) ≤ 1/256 at hb
  have hterm (j : ℕ) (hj : j < n) :
      ((q:ℝ)^2*J/Δ)*((weight r n j)^2*(boundaryCard (X j):ℝ)) ≤ 1/256 := by
    apply le_trans _ hb
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.single_le_sum (f := fun k => (weight r n k)^2*(boundaryCard (X k):ℝ))
      (fun k _ => by positivity) (Finset.mem_range.mpr hj)
  have hm := optimizer_entropy_lower hq J Δ E₀ hJ hΔ hv he Ω hΩ hH hg hgap
    X (fun j k hjk => monotone_rectangle lo₁ hi₁ lo₂ hi₂ (Nat.add_le_add_right hjk 1))
    (weight r n) n (fun j _ => hw.1 j)
    (fun e j k _ _ => rectangle_unique_split lo₁ hi₁ lo₂ hi₂ e j k)
    (fun j hj => by
      have ht := hterm j hj
      simp only [div_eq_mul_inv] at ht ⊢
      nlinarith only [ht]) (by
      simp only [div_eq_mul_inv] at hb ⊢
      nlinarith only [hb]) F hF
  have herr : (∑ j ∈ Finset.range n,
      (256*(q:ℝ)^2*J*(boundaryCard (X j):ℝ)/Δ)*(weight r n j)^2) ≤ 1 := by
    have heq : (∑ j ∈ Finset.range n,
        (256*(q:ℝ)^2*J*(boundaryCard (X j):ℝ)/Δ)*(weight r n j)^2) =
        256*((q:ℝ)^2*J/Δ)*(∑ j ∈ Finset.range n, (weight r n j)^2*(boundaryCard (X j):ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq]
    simp only [div_eq_mul_inv] at hb ⊢
    nlinarith only [hb]
  have hnr : (n:ℝ)*Real.log 2+1 ≤ bufferConstant q J Δ*(r:ℝ) := by
    have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
    simp only [n,s,bufferConstant,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    nlinarith only [hr']
  exact le_trans (by linarith only [herr,hnr]) hm

end PolynomialPEPS.Subvolume.GeometricLower

end

end OAI
