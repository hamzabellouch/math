import OAI.Probability.ContinuumTransition.FiniteBlocks

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem gibbsEnergy_const (c : ℝ) {ι : Type} [Fintype ι] (x : ι → Space) :
    gibbsEnergy (fun _ _ => c) x = c*((Fintype.card ι : ℝ)^2-Fintype.card ι)/2 := by
  rw [gibbsEnergy_eq_sum_sub_diag]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem gibbsEnergy_congr {V W : Space → Space → ℝ} {ι : Type} [Fintype ι]
    (x : ι → Space) (h : ∀ i j, V (x i) (x j) = W (x i) (x j)) :
    gibbsEnergy V x = gibbsEnergy W x := by
  unfold gibbsEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [h]

theorem gibbsFamily_shift (φ : ℝ → ℝ) (β μ γ : ℝ) (ι : Type) [Fintype ι] (x : ι → Space) :
    gibbsFamily (fun x y => φ ‖x-y‖-γ) β (μ+β*γ/2) ι x =
      Real.exp (μ*Fintype.card ι+β*γ/2*(Fintype.card ι : ℝ)^2)*symmetricWeight φ β x := by
  unfold gibbsFamily symmetricWeight
  split_ifs
  · rw [gibbsEnergy_sub, gibbsEnergy_radial, gibbsEnergy_const, ← Real.exp_add]
    congr 1
    ring
  · simp

theorem familyTerm_shift (φ : ℝ → ℝ) (β μ γ : ℝ) (A : Set Space) (n : ℕ) :
    familyTerm (gibbsFamily (fun x y => φ ‖x-y‖-γ) β (μ+β*γ/2)) A n =
      Real.exp (μ*n+β*γ/2*(n : ℝ)^2)*setPartition φ β A n := by
  unfold familyTerm familyIntegral
  simp_rw [gibbsFamily_shift, Fintype.card_fin]
  rw [integral_const_mul, mul_div_assoc]
  simp only [setPartition, generalPartition, Fintype.card_fin]

theorem integrableOn_gibbs_of_lower {V : Space → Space → ℝ}
    (hVm : Measurable (Function.uncurry V)) {C β h : ℝ} (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hV : ∀ x y, -C ≤ V x y) {D : Set Space} (hD : volume D ≠ ⊤)
    (ι : Type) [Fintype ι] : IntegrableOn (gibbsFamily V β h ι) {x | ∀ i, x i ∈ D} := by
  let n : ℝ := Fintype.card ι
  apply integrableOn_family_of_bound (gibbsFamily V β h) hD
    (measurable_gibbsFamily hVm β h ι) (gibbsFamily_nonneg V β h ι)
    (C := Real.exp ((h+β*C*n/2)*n))
  intro x
  unfold gibbsFamily
  split_ifs
  · apply Real.exp_le_exp.mpr
    have he := gibbsEnergy_mono (U := fun _ _ => -C) (V := V) x (fun i j => hV (x i) (x j))
    rw [gibbsEnergy_const] at he
    have hn : 0 ≤ n := Nat.cast_nonneg _
    have hh := mul_le_mul_of_nonneg_left he hβ
    change -C*(n^2-n)/2 ≤ gibbsEnergy V x at he
    change h*n-β*gibbsEnergy V x ≤ (h+β*C*n/2)*n
    nlinarith only [hh, mul_nonneg (mul_nonneg hβ hC) hn]
  · exact (Real.exp_pos _).le

noncomputable def quadraticBlock (q : ℕ) (φ : ℝ → ℝ) (γ : ℝ) : Space → Space → ℝ :=
  blockCut q (fun x y => φ ‖x-y‖-γ)

theorem measurable_quadraticBlock (q : ℕ) {φ : ℝ → ℝ} (hφ : Measurable φ) (γ : ℝ) :
    Measurable (Function.uncurry (quadraticBlock q φ γ)) :=
  measurable_blockCut q ((hφ.comp ((measurable_fst.sub measurable_snd).norm)).sub_const γ)

theorem quadraticBlock_symm (q : ℕ) (φ : ℝ → ℝ) (γ : ℝ) (x y : Space) :
    quadraticBlock q φ γ x y = quadraticBlock q φ γ y x := by
  simp only [quadraticBlock, blockCut]
  rw [norm_sub_rev y x]
  congr 1
  exact propext eq_comm

theorem quadraticBlock_on {q : ℕ} (hq : 0 < q) (φ : ℝ → ℝ) (γ : ℝ) {k : Lattice}
    {x y : Space} (hx : x ∈ gridBox ((q : ℝ)/4) k) (hy : y ∈ gridBox ((q : ℝ)/4) k) :
    quadraticBlock q φ γ x y = φ ‖x-y‖-γ := by
  have hu : 0 < (q : ℝ)/4 := by positivity
  simp only [quadraticBlock, blockCut, (mem_gridBox_iff hu _ _).1 hx,
    (mem_gridBox_iff hu _ _).1 hy, ite_true]

theorem quadraticBlock_cross {q : ℕ} (hq : 0 < q) (φ : ℝ → ℝ) (γ : ℝ) {k l : Lattice}
    (hkl : k ≠ l) {x y : Space} (hx : x ∈ gridBox ((q : ℝ)/4) k)
    (hy : y ∈ gridBox ((q : ℝ)/4) l) : quadraticBlock q φ γ x y = 0 := by
  have hu : 0 < (q : ℝ)/4 := by positivity
  simp only [quadraticBlock, blockCut, (mem_gridBox_iff hu _ _).1 hx,
    (mem_gridBox_iff hu _ _).1 hy, ite_eq_right hkl]

theorem familyTerm_quadraticBlock {q : ℕ} (hq : 0 < q) (φ : ℝ → ℝ) (β μ γ : ℝ)
    (k : Lattice) (n : ℕ) :
    familyTerm (gibbsFamily (quadraticBlock q φ γ) β (μ+β*γ/2)) (gridBox ((q : ℝ)/4) k) n =
      Real.exp (μ*n+β*γ/2*(n : ℝ)^2)*setPartition φ β (gridBox ((q : ℝ)/4) k) n := by
  rw [← familyTerm_shift]
  unfold familyTerm familyIntegral
  congr 1
  apply setIntegral_congr_fun (measurableSet_generalConfigurations (measurableSet_gridBox _ _) (Fin n))
  intro x hx
  unfold gibbsFamily
  rw [gibbsEnergy_congr (W := fun x y => φ ‖x-y‖-γ) x (fun i j => quadraticBlock_on hq φ γ (hx i) (hx j))]

end ContinuumTemperature
end

end OAI
