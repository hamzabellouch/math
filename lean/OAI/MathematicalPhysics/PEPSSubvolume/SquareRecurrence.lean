import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.RegionSSA
import OAI.MathematicalPhysics.PEPSSubvolume.EntropyDimension
import OAI.MathematicalPhysics.PEPSSubvolume.TilingEntropy
import OAI.MathematicalPhysics.PEPSSubvolume.RectangleTiling

namespace OAI

/-! Uniform entropy contraction across square scales. -/

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

namespace PolynomialPEPS.Subvolume.RectangleTiling
open scoped BigOperators
open PolynomialPEPS.Subvolume.HarmonicWeights PolynomialPEPS.Subvolume.GeometricLower
open PolynomialPEPS.Subvolume.RectangleContours
variable {L q : ℕ}

theorem physical_color_recurrence (hq : 0<q) (J Δ E₀ : ℝ)
    (hJ : 0≤J) (hΔ : 0<Δ)
    (hv : Vertex L → Operator L q) (he : Edge L → Operator L q) (Ω : State L q)
    (hΩ : ‖Ω‖=1) (hH : IsGridHamiltonian J hv he)
    (hg : asMap (Hamiltonian hv he) Ω=(E₀:ℂ) • Ω)
    (hgap : FullSystemGap (Hamiltonian hv he) Ω E₀ Δ)
    (lo₁ lo₂ : ℤ) (M r : ℕ) (hr : 0<r)
    (F : ℝ) (hF : ∀ i : Index M, vonNeumannEntropy Ω (tile lo₁ lo₂ r i)≤F) :
    let b := 2^(blocks q J Δ)
    let K : ℝ := ((b+1:ℕ):ℝ)^2
    vonNeumannEntropy Ω (box lo₁ lo₂ M r) ≤
      ((M:ℝ)^2-3/(4*K)*((interior b M).card:ℝ))*F+
        ((interior b M).card:ℝ)*(bufferConstant q J Δ*(r:ℝ)/4)/K := by
  classical
  let b := 2^(blocks q J Δ)
  let C := tile (L:=L) (M:=M) lo₁ lo₂ r
  let Y := collar (L:=L) (M:=M) lo₁ lo₂ r b
  have hdis : ((Finset.univ : Finset (Index M)) : Set (Index M)).Pairwise
      (fun i j => Disjoint (C i) (C j)) :=
    fun i _ j _ hij => tiles_disjoint lo₁ lo₂ r hr i j hij
  have hCY : ∀ i∈interior b M, C i ⊆ Y i := by
    intro i hi
    exact monotone_rectangle _ _ _ _ (Nat.zero_le _)
  have hY : ∀ k : Index (b+1), ∀ i∈interior b M, color b i=k →
      Y i\C i ⊆ PolynomialPEPS.SubvolumeTiling.unionTiles C
        (Finset.univ\(interior b M).filter (fun j => color b j=k)) := by
    intro k i hi hk
    subst k
    exact collar_exposed lo₁ lo₂ r b hr i hi
  have hc : ∀ i∈interior b M, vonNeumannEntropy Ω (Y i)-vonNeumannEntropy Ω (Y i\C i)≤
      vonNeumannEntropy Ω (C i)/4+bufferConstant q J Δ*(r:ℝ)/4 := by
    intro i hi
    apply GeometricComparison.rectangle_conditional_contraction hq J Δ E₀ hJ hΔ
      hv he Ω hΩ hH hg hgap _ _ _ _ r hr <;> linarith
  have hh := PolynomialPEPS.SubvolumeTiling.color_recurrence (vonNeumannEntropy Ω)
    (vonNeumannEntropy_empty Ω hΩ) (RegionSSA.conditional_entropy_antitone hq Ω)
    C Y Finset.univ (interior b M) (Finset.subset_univ _) (color b) hdis hCY hY
    (bufferConstant q J Δ*(r:ℝ)/4) F hc (fun i _ => hF i)
  dsimp only [PolynomialPEPS.SubvolumeTiling.unionTiles,C] at hh
  rw [tiles_cover lo₁ lo₂ r hr] at hh
  simpa only [Finset.card_univ,Index,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,pow_two] using hh

theorem physical_density_contraction (hq : 0<q) (J Δ E₀ : ℝ)
    (hJ : 0≤J) (hΔ : 0<Δ)
    (hv : Vertex L → Operator L q) (he : Edge L → Operator L q) (Ω : State L q)
    (hΩ : ‖Ω‖=1) (hH : IsGridHamiltonian J hv he)
    (hg : asMap (Hamiltonian hv he) Ω=(E₀:ℂ) • Ω)
    (hgap : FullSystemGap (Hamiltonian hv he) Ω E₀ Δ)
    (lo₁ lo₂ : ℤ) (r : ℕ) (hr : 0<r) (F : ℝ) (hF0 : 0≤F)
    (hF : ∀ i : Index (4*(2^(blocks q J Δ)+1)), vonNeumannEntropy Ω (tile lo₁ lo₂ r i)≤F) :
    let b := 2^(blocks q J Δ)
    let M := 4*(b+1)
    let K : ℝ := ((b+1:ℕ):ℝ)^2
    vonNeumannEntropy Ω (box lo₁ lo₂ M r) ≤
      (1-3/(16*K))*(M:ℝ)^2*F+(M:ℝ)^2*(bufferConstant q J Δ*(r:ℝ)/4)/K := by
  let b := 2^(blocks q J Δ)
  let M := 4*(b+1)
  let K : ℝ := ((b+1:ℕ):ℝ)^2
  let N : ℝ := (interior b M).card
  have hK : 0<K := by dsimp [K]; positivity
  have hNlo : (M:ℝ)^2/4≤N := by
    have hh : ((2*(b+1):ℕ):ℝ)^2≤N := by
      dsimp only [N,M]
      exact_mod_cast interior_card_lower b
    dsimp only [M]
    push_cast at hh ⊢
    nlinarith only [hh]
  have hNhi : N≤(M:ℝ)^2 := by
    dsimp only [N]
    exact_mod_cast interior_card_upper b M
  have hB : 0≤bufferConstant q J Δ*(r:ℝ)/4 := by
    dsimp only [bufferConstant]
    positivity
  have hh := physical_color_recurrence hq J Δ E₀ hJ hΔ hv he Ω hΩ hH hg hgap lo₁ lo₂ M r hr F hF
  change vonNeumannEntropy Ω (box lo₁ lo₂ M r) ≤ ((M:ℝ)^2-3/(4*K)*N)*F+
    N*(bufferConstant q J Δ*(r:ℝ)/4)/K at hh
  apply hh.trans
  change ((M:ℝ)^2-3/(4*K)*N)*F+N*(bufferConstant q J Δ*(r:ℝ)/4)/K ≤
    (1-3/(16*K))*(M:ℝ)^2*F+(M:ℝ)^2*(bufferConstant q J Δ*(r:ℝ)/4)/K
  have hd : 0≤3/(4*K) := le_of_lt (div_pos (by norm_num) (mul_pos (by norm_num) hK))
  have h1 := mul_le_mul_of_nonneg_right hNlo (mul_nonneg hd hF0)
  have h2 := mul_le_mul_of_nonneg_right hNhi (div_nonneg hB (le_of_lt hK))
  have he : 3/(16*K)=(3/(4*K))/4 := by ring
  rw [he]
  apply add_le_add
  · calc
      _ = (M:ℝ)^2*F-N*(3/(4*K)*F) := by ring
      _ ≤ (M:ℝ)^2*F-((M:ℝ)^2/4)*(3/(4*K)*F) := sub_le_sub_left h1 _
      _ = _ := by ring
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hNhi hB) (le_of_lt hK)

end PolynomialPEPS.Subvolume.RectangleTiling

namespace PolynomialPEPS.Subvolume.RectangleTiling
open scoped BigOperators
open PolynomialPEPS.Subvolume.HarmonicWeights PolynomialPEPS.Subvolume.GeometricLower
open PolynomialPEPS.Subvolume.RectangleContours
variable {L q : ℕ}

lemma tile_as_box (lo₁ lo₂ : ℤ) (r : ℕ) {M : ℕ} (i : Index M) :
    tile (L:=L) lo₁ lo₂ r i =
      box (lo₁+(i.1.val:ℤ)*r) (lo₂+(i.2.val:ℤ)*r) 1 r := by
  unfold tile box
  congr 1 <;> push_cast <;> ring

lemma box_mul (lo₁ lo₂ : ℤ) (M r : ℕ) :
    box (L:=L) lo₁ lo₂ M r=box lo₁ lo₂ 1 (M*r) := by
  unfold box
  congr 1 <;> push_cast <;> ring

lemma unit_box_card (lo₁ lo₂ : ℤ) : (box (L:=L) lo₁ lo₂ 1 1).card≤1 := by
  apply Finset.card_le_one.mpr
  intro v hv w hw
  rw [mem_box] at hv hw
  apply Prod.ext <;> apply Fin.ext <;> omega

theorem physical_three_child_gain (hq : 0<q) (J Δ E₀ : ℝ)
    (hJ : 0≤J) (hΔ : 0<Δ)
    (hv : Vertex L → Operator L q) (he : Edge L → Operator L q) (Ω : State L q)
    (hΩ : ‖Ω‖=1) (hH : IsGridHamiltonian J hv he)
    (hg : asMap (Hamiltonian hv he) Ω=(E₀:ℂ) • Ω)
    (hgap : FullSystemGap (Hamiltonian hv he) Ω E₀ Δ)
    (lo₁ lo₂ : ℤ) (r : ℕ) (hr : 0<r) (F : ℝ) (hF0 : 0≤F)
    (hF : ∀ i : Index (4*(2^(blocks q J Δ)+1)), vonNeumannEntropy Ω (tile lo₁ lo₂ r i)≤F) :
    let M := 4*(2^(blocks q J Δ)+1)
    vonNeumannEntropy Ω (box lo₁ lo₂ 1 (M*r)) ≤
      ((M:ℝ)^2-3)*F+4*bufferConstant q J Δ*(r:ℝ) := by
  let b := 2^(blocks q J Δ)
  let M := 4*(b+1)
  let K : ℝ := ((b+1:ℕ):ℝ)^2
  have hK : K≠0 := by dsimp [K]; positivity
  have hc : (M:ℝ)^2=16*K := by dsimp [M,K]; push_cast; ring
  have hh := physical_density_contraction hq J Δ E₀ hJ hΔ hv he Ω hΩ hH hg hgap lo₁ lo₂ r hr F hF0 hF
  change vonNeumannEntropy Ω (box lo₁ lo₂ M r) ≤
    (1-3/(16*K))*(M:ℝ)^2*F+(M:ℝ)^2*(bufferConstant q J Δ*(r:ℝ)/4)/K at hh
  rw [box_mul] at hh
  convert hh using 1
  rw [hc]
  field_simp
  ring

theorem square_scale_entropy (hq : 0<q) (J Δ E₀ : ℝ)
    (hJ : 0≤J) (hΔ : 0<Δ)
    (hv : Vertex L → Operator L q) (he : Edge L → Operator L q) (Ω : State L q)
    (hΩ : ‖Ω‖=1) (hH : IsGridHamiltonian J hv he)
    (hg : asMap (Hamiltonian hv he) Ω=(E₀:ℂ) • Ω)
    (hgap : FullSystemGap (Hamiltonian hv he) Ω E₀ Δ)
    (k : ℕ) (lo₁ lo₂ : ℤ) :
    let M := 4*(2^(blocks q J Δ)+1)
    vonNeumannEntropy Ω (box lo₁ lo₂ 1 (M^k)) ≤
      (Real.log q+4*bufferConstant q J Δ)*((M:ℝ)^2-2)^k := by
  let M := 4*(2^(blocks q J Δ)+1)
  let R : ℝ := (M:ℝ)^2-2
  let A := Real.log q+4*bufferConstant q J Δ
  have hM : (4:ℝ)≤M := by
    dsimp only [M]
    exact_mod_cast (Nat.mul_le_mul_left 4 (Nat.succ_le_succ (Nat.zero_le (2^(blocks q J Δ)))))
  have hMr : 0<(M:ℝ) := lt_of_lt_of_le (by norm_num) hM
  have hMn : 0<M := by exact_mod_cast hMr
  have hR : (M:ℝ)≤R := by dsimp [R]; nlinarith only [hM]
  have hR0 : 0≤R := (le_of_lt hMr).trans hR
  have hQ : 0≤Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hB : 0≤bufferConstant q J Δ := by dsimp [bufferConstant]; positivity
  have hA : 0≤A := add_nonneg hQ (mul_nonneg (by norm_num) hB)
  change vonNeumannEntropy Ω (box lo₁ lo₂ 1 (M^k))≤A*R^k
  induction k generalizing lo₁ lo₂ with
  | zero =>
    simp only [pow_zero,mul_one]
    have hh := vonNeumannEntropy_le_card_log hq Ω hΩ (box lo₁ lo₂ 1 1)
    have hn : ((box (L:=L) lo₁ lo₂ 1 1).card:ℝ)≤1 := by exact_mod_cast unit_box_card (L:=L) lo₁ lo₂
    have ht := mul_le_mul_of_nonneg_right hn hQ
    dsimp only [A]
    linarith only [hh,ht,hB]
  | succ k ih =>
    have hf : ∀ i : Index M, vonNeumannEntropy Ω (tile lo₁ lo₂ (M^k) i)≤A*R^k := by
      intro i
      rw [tile_as_box]
      exact ih _ _
    have hh := physical_three_child_gain hq J Δ E₀ hJ hΔ hv he Ω hΩ hH hg hgap lo₁ lo₂
      (M^k) (pow_pos hMn _) (A*R^k) (mul_nonneg hA (pow_nonneg hR0 _)) hf
    change vonNeumannEntropy Ω (box lo₁ lo₂ 1 (M*M^k)) ≤
      ((M:ℝ)^2-3)*(A*R^k)+4*bufferConstant q J Δ*(M^k:ℕ) at hh
    rw [pow_succ' M k]
    apply hh.trans
    push_cast
    have hp : (M:ℝ)^k≤R^k := pow_le_pow_left₀ (le_of_lt hMr) hR k
    have he := mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num : (0:ℝ)≤4) hB)
    have ha : 4*bufferConstant q J Δ≤A := by dsimp [A]; linarith only [hQ]
    have he' := mul_le_mul_of_nonneg_right ha (pow_nonneg hR0 k)
    change _ ≤ A*R^(k+1)
    calc
      _ ≤ ((M:ℝ)^2-3)*(A*R^k)+A*R^k := add_le_add le_rfl (he.trans he')
      _ = A*(R^k*R) := by dsimp only [R]; ring
      _ = A*R^(k+1) := by rw [pow_succ R k]

end PolynomialPEPS.Subvolume.RectangleTiling

end

end OAI
