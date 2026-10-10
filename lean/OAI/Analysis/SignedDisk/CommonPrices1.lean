import OAI.Analysis.SignedDisk.ActualMarkTrees1

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace CommonPrices
open DyadicHats ConeCoordinates Finset DirectionNeighbors

def cellRoots (N : ℕ) (p : ℤ × ℤ) : Finset (Grid N) :=
  univ.filter (fun q => (q : ℤ × ℤ) ∈ window 20 p)

lemma cellPrice_spatial {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (P : Finset (ℤ × ℤ)) :
    (∑ p ∈ P, cellPrice N r h k (cellRoots N p)) ≤ 1681*∑ q : Grid N, rootPrice N r h k q := by
  simp only [cellPrice,cellRoots,sum_filter]
  rw [Finset.sum_comm]
  rw [mul_sum]
  apply sum_le_sum
  intro q _
  have hn := rootPrice_nonneg hr hR hN hh hsupp k q
  have hs : P.filter (fun p => (q:ℤ×ℤ) ∈ window 20 p) ⊆ window 20 q := by
    intro p hp
    exact (mem_window_comm 20 _ _).mp (mem_filter.mp hp).2
  have hc : ((P.filter (fun p => (q:ℤ×ℤ) ∈ window 20 p)).card : ℝ) ≤ 1681 := by
    have hc := Finset.card_le_card hs
    rw [card_window] at hc
    exact_mod_cast hc
  rw [← sum_filter,sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hc hn

/-- The common geometric price has a genuine uniform spatial-and-scale
budget, including every desired finite set of observation cells. -/
theorem cellPrice_budget {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) (P : ℕ → Finset (ℤ × ℤ)) :
    (∑ k ∈ range (m+1), ∑ p ∈ P k, cellPrice N r h k (cellRoots N p)) ≤
      1681*((fixedPalette.labels.card:ℝ)*2/(1-rho))*(∫ y, ‖h y‖) := by
  calc
    _ ≤ ∑ k ∈ range (m+1), 1681*∑ q : Grid N, rootPrice N r h k q :=
      sum_le_sum (fun k _ => cellPrice_spatial hr hR hN hh hsupp k (P k))
    _ = 1681*(∑ k ∈ range (m+1), ∑ q : Grid N, rootPrice N r h k q) := by rw [mul_sum]
    _ ≤ _ := by
      have ht := mul_le_mul_of_nonneg_left (rootPrice_budget hr hR hN hh hsupp m) (by norm_num : (0:ℝ) ≤ 1681)
      have he : 1681*(2*(fixedPalette.labels.card:ℝ)*(1-rho)⁻¹*(∫ y, ‖h y‖)) =
          1681*((fixedPalette.labels.card:ℝ)*2/(1-rho))*(∫ y, ‖h y‖) := by ring
      exact ht.trans_eq he

end CommonPrices

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks Finset DirectionNeighbors

lemma nodeCharge_scale {N : ℕ} (v : Grid N → ℂ) (k : ℕ) {b : ℝ} (hb : 0 ≤ b)
    (q : Grid N) (C : List (Grid N) → ℝ) :
    nodeCharge (tree v k b q) C = b*nodeCharge (tree v k 1 q) C := by
  induction k generalizing b q C with
  | zero => simp [tree,nodeCharge,Real.norm_eq_abs,abs_of_nonneg hb,mul_assoc]
  | succ k ih =>
    change ‖vector (tree v (k+1) b q)‖*C []+
      (∑ a : Grid N, nodeCharge (tree v k (b*step q a) a) (fun p => C (a::p))) =
      b*(‖vector (tree v (k+1) 1 q)‖*C []+
      (∑ a : Grid N, nodeCharge (tree v k (1*step q a) a) (fun p => C (a::p))))
    simp only [vector_tree,norm_smul,Real.norm_eq_abs,abs_of_nonneg hb,
      abs_one,one_mul]
    simp_rw [ih (mul_nonneg hb (step_nonneg _ _)),ih (step_nonneg _ _)]
    rw [mul_add,mul_sum]
    congr 1
    · ring
    · apply sum_congr rfl
      intro a ha
      ring

def spatialCharge {N : ℕ} (C : ℕ → Grid N → ℝ) (k : ℕ) (q : Grid N)
    (p : List (Grid N)) : ℝ := C (k-p.length) (lastVertex q p)

lemma spatialCharge_cons {N : ℕ} (C : ℕ → Grid N → ℝ) (k : ℕ) (q a : Grid N)
    (p : List (Grid N)) : spatialCharge C (k+1) q (a::p) = spatialCharge C k a p := by
  simp [spatialCharge,List.length_cons,lastVertex]

lemma sum_nodeCharge {N : ℕ} (v : Grid N → ℂ) (k : ℕ) (C : ℕ → Grid N → ℝ) :
    (∑ q, nodeCharge (tree v k 1 q) (spatialCharge C k q)) =
      ∑ j ∈ range (k+1), ∑ a : Grid N,
        ‖∑ z : Grid N, coeff N j a z • v z‖*C j a := by
  induction k with
  | zero =>
    have hv (a : Grid N) : (∑ z : Grid N, coeff N 0 a z • v z) = v a := by
      simpa only [tree,vector,one_smul] using (vector_tree v 0 1 a).symm
    simp only [tree,nodeCharge,one_smul,spatialCharge,List.length_nil,Nat.sub_zero,
      lastVertex,Nat.zero_add,sum_range_one,hv]
  | succ k ih =>
    have hrec (q : Grid N) : nodeCharge (tree v (k+1) 1 q) (spatialCharge C (k+1) q) =
        ‖∑ z : Grid N, coeff N (k+1) q z • v z‖*C (k+1) q+
        ∑ a : Grid N, step q a*nodeCharge (tree v k 1 a) (spatialCharge C k a) := by
      change ‖vector (tree v (k+1) 1 q)‖*spatialCharge C (k+1) q []+_ = _
      simp only [vector_tree,one_smul,spatialCharge,List.length_nil,Nat.sub_zero,lastVertex,
        one_mul,List.length_cons,Nat.add_sub_add_right]
      congr 1
      apply sum_congr rfl
      intro a ha
      exact nodeCharge_scale v k (step_nonneg q a) a _
    simp_rw [hrec]
    rw [sum_add_distrib,Finset.sum_comm (f := fun (q a : Grid N) => step q a*
      nodeCharge (tree v k 1 a) (spatialCharge C k a))]
    simp_rw [← sum_mul,grid_step_column,one_mul]
    rw [ih]
    conv_rhs => rw [sum_range_succ]
    exact add_comm _ _

lemma sum_energyCharge {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) :
    (∑ q : Grid N, nodeCharge (tree (fun q => vectorMass h r q) k 1 q)
      (pathEnergy h r k q)) =
      ∑ j ∈ range (k+1), ∑ q : Grid N, scalarMass h (scale r j) q*energy h (scale r j) q := by
  change (∑ q : Grid N, nodeCharge (tree (fun q => vectorMass h r q) k 1 q)
    (spatialCharge (fun j q => energy h (scale r j) q) k q)) = _
  rw [sum_nodeCharge]
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro q hq
  rw [← vectorMass_coeff hr hR hN hh hsupp]
  rfl

/-- Particle observations use the prescribed terminal vertex, not a hat-density
surrogate. This is the frozen spatial location carried throughout the process. -/
def particleSwitches {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (q : Grid N)
    (p : List (Grid N)) (b : ℕ) : ℝ :=
  pathSwitches h r k (point r (lastVertex q p)) p b

theorem particle_switch_bound {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    particleEval (tree (fun q => vectorMass h r q) k 1 q) (particleSwitches h r k q) ≤
      2560004*terminalMass (tree (fun q => vectorMass h r q) k 1 q)+
      2000000*nodeCharge (tree (fun q => vectorMass h r q) k 1 q) (pathEnergy h r k q) := by
  have hp := particleEval_mono_active (tree (fun q => vectorMass h r q) k 1 q)
    (F := particleSwitches h r k q)
    (fun p b hp hb => path_switch_bound hr hR hN hh hsupp k q hp hb (x := point r (lastVertex q p)) (by
      rw [hat_at_point hr.ne']
      norm_num))
  simp only [particleEval_add,particleEval_smul,particleEval_const,particle_occupancy,
    root_marked_occupancy] at hp
  have hm := costWithRoot_le (by simp : ‖(1:ℂ)‖ = 1)
    (by norm_num : (0:ℝ) < 1/800) (tree (fun q => vectorMass h r q) k 1 q)
  norm_num at hm
  change particleEval _ (particleSwitches h r k q) ≤ _ at hp
  linarith

/-- The switch budget for the actual finite spatial forest, with every birth
population included and frozen terminal positions observed. -/
theorem forest_switch_budget {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) :
    (∑ q : Grid N, particleEval (tree (fun q => vectorMass h r q) k 1 q)
      (particleSwitches h r k q)) ≤
      (2560004+2000000*(576*(4097:ℝ)^2))*(∫ y, ‖h y‖) := by
  have hs := sum_le_sum (fun q (_ : q ∈ (univ : Finset (Grid N))) =>
    particle_switch_bound hr hR hN hh hsupp k q)
  simp only [sum_add_distrib,← mul_sum] at hs
  rw [sum_terminalMass,sum_energyCharge hr hR hN hh hsupp] at hs
  have ht := sum_scalarMass_grid_le (N := N) hh r
  have he := neighbor_energy_budget hr hR hN hh hsupp (k+1)
  change (∑ q : Grid N, ‖vectorMass h r q‖) ≤ ∫ y, ‖h y‖ at ht
  nlinarith only [hs,ht,he]

end ActualMarkTrees

namespace FiniteLabels
variable {ι : Type*} [Fintype ι]
lemma expect_const (μ : Law ι) (c : ℝ) : expect μ (fun _ => c) = c := by
  rw [expect,← Finset.sum_mul,μ.total,one_mul]
lemma expect_mul (μ : Law ι) (f : ι → ℝ) (c : ℝ) :
    expect μ (fun i => c*f i) = c*expect μ f := by
  simp only [expect,Finset.mul_sum,mul_left_comm]
lemma expect_mono (μ : Law ι) {f g : ι → ℝ} (h : ∀ i, f i ≤ g i) :
    expect μ f ≤ expect μ g := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) (μ.nonneg i))
lemma expect_le_const (μ : Law ι) {f : ι → ℝ} {c : ℝ} (h : ∀ i, f i ≤ c) :
    expect μ f ≤ c := (expect_mono μ h).trans_eq (expect_const μ c)
lemma expect_compare (μ ν : Law ι) {f : ι → ℝ} {c : ℝ} (h : ∀ i, |f i| ≤ c) :
    expect μ f ≤ expect ν f+c*l1dist μ ν := by
  have he := expectation_difference μ ν h
  change |expect μ f-expect ν f| ≤ c*l1dist μ ν at he
  have hl := le_abs_self (expect μ f-expect ν f)
  linarith
end FiniteLabels

namespace ActualLabels
open FiniteLabels ConeCoordinates DirectionNeighbors DyadicHats Finset

def comparisonConstant : ℝ := 1280000*((Fintype.card Label:ℝ)+1)
lemma comparisonConstant_ge : 1280000 ≤ comparisonConstant := by
  dsimp [comparisonConstant]
  nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card Label)]
lemma comparisonConstant_pos : 0 < comparisonConstant := lt_of_lt_of_le (by norm_num) comparisonConstant_ge
lemma comparisonConstant_one : 1 ≤ comparisonConstant := by linarith [comparisonConstant_ge]

def rowDerivative (h : ℂ → ℂ) (r : ℝ) (x : ℂ) (n : Label) : ℝ :=
  r*∑ j : Label, ‖gradient (fun y => row h r y n j) x‖
def derivativeCost (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ) : ℕ → ℝ
  | 0 => r 0*∑ j : Label, ‖gradient (fun y => initial h (r 0) y j) x‖
  | i+1 => expect (marginal h r i x) (rowDerivative h (r (i+1)) x)

lemma rowDerivative_nonneg (h : ℂ → ℂ) {r : ℝ} (hr : 0 ≤ r) (x : ℂ) (n : Label) :
    0 ≤ rowDerivative h r x n := mul_nonneg hr (sum_nonneg (fun _ _ => norm_nonneg _))
lemma rowDerivative_uniform (h : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (x : ℂ) (n : Label) :
    rowDerivative h r x n ≤ 16*(Fintype.card Label:ℝ) := by
  have hh := spatialRow_local_derivative n (target h r) (switchChance h r n)
    (switchChance_nonneg h r n) (switchChance_le_one h r n) hr (by norm_num : (0:ℝ) ≤ 1)
    (q := x) (x := x) (by simp only [sub_self,boxNorm]; norm_num; positivity)
    (fun z _ => switchChance_le_one h r n z)
  change rowDerivative h r x n ≤ 16*(Fintype.card Label:ℝ)*1 at hh
  simpa only [mul_one] using hh
lemma initial_distance (h : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (x y : ℂ) :
    l1dist (initial h r x) (initial h r y) ≤ comparisonConstant/r*‖x-y‖ := by
  have he := spatialRow_distance (quantize 1 (by norm_num)) (target h r) (fun _ => 1)
    (fun _ => zero_le_one) (fun _ => le_rfl) hr (by norm_num : (0:ℝ) ≤ 1)
    (fun _ => le_rfl) x y
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hr.le
  dsimp [comparisonConstant]
  nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card Label)]
lemma derivativeCost_uniform (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ) (i : ℕ) (hr : 0 < r i) :
    derivativeCost h r x i ≤ 16*(Fintype.card Label:ℝ) := by
  cases i with
  | zero =>
    have hh := spatialRow_local_derivative (quantize 1 (by norm_num)) (target h (r 0)) (fun _ => 1)
      (fun _ => zero_le_one) (fun _ => le_rfl) hr (by norm_num : (0:ℝ) ≤ 1)
      (q := x) (x := x) (by simp only [sub_self,boxNorm]; norm_num; positivity) (fun _ _ => le_rfl)
    change derivativeCost h r x 0 ≤ 16*(Fintype.card Label:ℝ)*1 at hh
    simpa only [mul_one] using hh
  | succ i => exact expect_le_const _ (rowDerivative_uniform h hr x)

lemma rate_local (h : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (q : ℤ × ℤ) (x y : ℂ)
    (hx : boxNorm (x-point r q) < 199*r) (hy : boxNorm (y-point r q) < 199*r) (n : Label) :
    rate h r x n ≤ comparisonConstant*(rate h r y n+energy h r q) := by
  have he := switchRate_local_compare (by norm_num : (0:ℝ) < 1/100) hr (Theta h r)
    (n:ℂ) (theta h r q) (point r q) x y hx hy (energy_controls hr h q)
  change rate h r x n ≤ 2*rate h r y n+8*((1/100:ℝ)⁻¹)^2*energy h r q at he
  norm_num at he
  have h0 := rate_nonneg h r y n
  have h1 := energy_nonneg h r q
  have hC := comparisonConstant_ge
  nlinarith

lemma row_local_distance (h : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (q : ℤ × ℤ) (x y : ℂ)
    (hx : boxNorm (x-point r q) < 199*r) (hy : boxNorm (y-point r q) < 199*r) (n : Label) :
    l1dist (row h r x n) (row h r y n) ≤
      comparisonConstant*‖x-y‖/r*(rate h r y n+energy h r q) := by
  have he := spatialSwitchRow_local_distance (by norm_num : (0:ℝ) < 1/100) hr (energy_nonneg h r q)
    (fun n : Label => (n:ℂ)) (Theta h r) (target h r) n (theta h r q) (point r q) x y hx hy
    (energy_controls hr h q)
  change l1dist (row h r x n) (row h r y n) ≤
    (Fintype.card Label:ℝ)*(16*(2*rate h r y n+8*((1/100:ℝ)⁻¹)^2*energy h r q)/r)*‖x-y‖ at he
  apply he.trans
  have h0 := rate_nonneg h r y n
  have h1 := energy_nonneg h r q
  have hb : (Fintype.card Label:ℝ)*(16*(2*rate h r y n+8*((1/100:ℝ)⁻¹)^2*energy h r q)) ≤
      comparisonConstant*(rate h r y n+energy h r q) := by
    dsimp [comparisonConstant]
    norm_num
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card Label)) h0,
      mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card Label)) h1]
  have hb' := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb hr.le) (norm_nonneg (x-y))
  convert hb' using 1 <;> ring

lemma row_local_derivative (h : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (q : ℤ × ℤ) (x y : ℂ)
    (hx : boxNorm (x-point r q) < 199*r) (hy : boxNorm (y-point r q) < 199*r) (n : Label) :
    rowDerivative h r x n ≤ comparisonConstant*(rate h r y n+energy h r q) := by
  have he := spatialSwitchRow_local_derivative (by norm_num : (0:ℝ) < 1/100) hr (energy_nonneg h r q)
    (fun n : Label => (n:ℂ)) (Theta h r) (target h r) n (theta h r q) (point r q) x y hx hy
    (energy_controls hr h q)
  change rowDerivative h r x n ≤
    16*(Fintype.card Label:ℝ)*(2*rate h r y n+8*((1/100:ℝ)⁻¹)^2*energy h r q) at he
  apply he.trans
  have h0 := rate_nonneg h r y n
  have h1 := energy_nonneg h r q
  dsimp [comparisonConstant]
  norm_num
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card Label)) h0,
    mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card Label)) h1]

end ActualLabels

namespace AffineDensities
lemma gradient_affine {g : ℂ → ℝ} (hg : Differentiable ℝ g) (p : ℂ) (r : ℝ) (X : ℂ) :
    gradient (fun Y => g (p+r • Y)) X = rescale p r (gradient g) X := by
  have hA : HasFDerivAt (fun Y : ℂ => p+r • Y) (r • ContinuousLinearMap.id ℝ ℂ) X :=
    ((hasFDerivAt_id X).const_smul r).const_add p
  have hc := (hg (p+r • X)).hasFDerivAt.comp X hA
  change HasFDerivAt (fun Y => g (p+r • Y)) _ X at hc
  apply (InnerProductSpace.toDual ℝ ℂ).injective
  simp only [toDual_gradient,rescale,map_smul]
  rw [hc.fderiv]
  ext z
  simp
end AffineDensities

namespace DyadicHats
open Finset
lemma vector_partition_grid {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (x : ℂ) :
    (∑ p : Grid N, hat r p x) • h x = h x := by
  by_cases hx : h x = 0
  · simp only [hx,smul_zero]
  · have he := density_partition_grid hr hN (h := fun y => ‖h y‖)
      (fun y hy => hs y (fun hh => hy (by rw [hh,norm_zero]))) x
    rw [← sum_mul] at he
    have hsum : (∑ p : Grid N, hat r p x) = 1 := by
      apply mul_right_cancel₀ (norm_ne_zero_iff.mpr hx)
      simpa only [one_mul] using he
    rw [hsum,one_smul]
end DyadicHats

namespace CommonPrices
open DyadicHats ConeCoordinates ConeScalar LocalCancellation AffineDensities DirectionNeighbors Finset DiskMoments

lemma hat_mem_cellRoots {N : ℕ} {r : ℝ} (hr : 0 < r) (p : ℤ × ℤ) (X : ℂ) (hX : ‖X‖ ≤ 12)
    (q : Grid N) (hq : hat r q (point r p+r • X) ≠ 0) : q ∈ cellRoots N p := by
  have hl := (hat_ne_zero_iff hr q (point r p+r • X)).mp hq
  have hnorm : boxNorm (r • X) ≤ 12*r := by
    apply (boxNorm_le_norm _).trans
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    nlinarith
  have hh := boxNorm_add_le (point r q-(point r p+r • X)) (r • X)
  rw [boxNorm_sub_comm (point r q)] at hh
  have hie : point r q-(point r p+r • X)+r • X = point r q-point r p := by abel
  rw [hie] at hh
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  rw [mem_window_iff hr 20]
  norm_num
  linarith

lemma cell_partition {N : ℕ} {r R : ℝ} (hr : 0 < r) (hN : R/r+1 ≤ (N:ℝ))
    {h : ℂ → ℂ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (p : ℤ × ℤ) (X : ℂ) (hX : ‖X‖ ≤ 12) :
    (∑ q ∈ cellRoots N p, hat r q (point r p+r • X)) • h (point r p+r • X) = h (point r p+r • X) := by
  have he : (∑ q ∈ cellRoots N p, hat r q (point r p+r • X)) =
      ∑ q : Grid N, hat r q (point r p+r • X) := by
    apply sum_subset (subset_univ _)
    intro q _ hq
    by_contra hh
    exact hq (hat_mem_cellRoots hr p X hX q hh)
  rw [he]
  exact vector_partition_grid hr hN hs _

lemma cell_decomposition_gradient {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {g : ℂ → ℝ} (hg : Differentiable ℝ g)
    (hh : Integrable (gradient g)) (hsupp : ∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R)
    (k : ℕ) (p : ℤ × ℤ) {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (X : ℂ) (hX : ‖X‖ ≤ 12) :
    (goodCone hr hR hN hh hsupp k (point (scale r k) p) (cellRoots N p) hn hs).density X+
      (∑ i, (cellErrors hr hh k (point (scale r k) p) (cellRoots N p) n i).density X) =
      gradient (fun Y => g (point (scale r k) p+scale r k • Y)) X := by
  rw [cell_decomposition hr hR hN hh hsupp k _ _ hn hs,gradient_affine hg]
  simp only [rescale]
  rw [cell_partition (scale_pos hr k) (scale_index_bound hr hR hN k) hsupp p X hX]

/-- The hard directional local price, instantiated with the actual common-price
cone decomposition on the actual neighboring grid roots. -/
theorem directional_cell_price : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) → ∀ (k : ℕ) (p : ℤ × ℤ)
    {n : ℂ}, n ∈ fixedPalette.labels → ∀ {s : ℝ}, (s = 1 ∨ s = -1) →
    ∀ Q : Set ℂ, volume Q ≤ ENNReal.ofReal 1 →
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ X in Q, F X) ≤ ENNReal.ofReal (C*(scale r k)⁻¹*
        (badPrice (gradient g) r k (cellRoots N p) n+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      ∀ X, ‖X‖ ≤ 2 → ∀ t,
        NeighborhoodRadius (fun Y => g (point (scale r k) p+scale r k • Y)) X t →
        ENNReal.ofReal (max 0 (-inner ℝ (axis n s)
          (∫ Y in Metric.ball X t, gradient (fun Z => g (point (scale r k) p+scale r k • Z)) Y))) ≤ F X := by
  obtain ⟨C,hC,hmajor⟩ := direction_majorant (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) < 1/2)
  refine ⟨4*C,by positivity,?_⟩
  intro N r R hr hR hN g hg hh hsupp k p n hn s hs Q hQ
  have hnu := fixedPalette.unit n hn
  let a := goodCone hr hR hN hh hsupp k (point (scale r k) p) (cellRoots N p) hnu hs
  let b := cellErrors hr hh k (point (scale r k) p) (cellRoots N p) n
  have hg' : ContDiff ℝ 1 (fun Y => g (point (scale r k) p+scale r k • Y)) := hg.comp (by fun_prop)
  obtain ⟨F,hFm,hFi,hFb⟩ := hmajor a b (axis_norm hnu (by rcases hs with rfl | rfl <;> norm_num)) _ hg' Q hQ
  refine ⟨F,hFm,?_,?_⟩
  · apply hFi.trans
    apply ENNReal.ofReal_le_ofReal
    have hb := cellErrors_price hr hR hN hh hsupp k (point (scale r k) p) (cellRoots N p) hn
    have hD : 0 ≤ cellPrice N r (gradient g) k (cellRoots N p) :=
      sum_nonneg (fun q _ => rootPrice_nonneg hr hR hN hh hsupp k q)
    change errorPrice b (1/100) ≤ _ at hb
    have hrk := scale_pos hr k
    nlinarith [mul_le_mul_of_nonneg_left hb hC.le,inv_nonneg.mpr hrk.le,
      mul_nonneg (inv_nonneg.mpr hrk.le) hD]
  · intro X hX t ht
    apply hFb X _ t ht
    filter_upwards with Y hY
    apply cell_decomposition_gradient hr hR hN (hg.differentiable one_ne_zero) hh hsupp k p hnu hs
    have hy : ‖Y-X‖ < 3 := by simpa only [Metric.mem_ball,dist_eq_norm] using hY
    have htri := norm_add_le (Y-X) X
    rw [sub_add_cancel] at htri
    linarith

end CommonPrices

end SignedDisk

end

end OAI
