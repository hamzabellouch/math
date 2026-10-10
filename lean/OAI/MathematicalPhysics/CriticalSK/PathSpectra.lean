import OAI.MathematicalPhysics.CriticalSK.MinMax
import OAI.MathematicalPhysics.CriticalSK.PathEnergy

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial
open scoped BigOperators Topology
open Filter
namespace CriticalSK

def edgeTent (m b i : ℕ) : ℝ := (min (min (i - b) m) (4 * m - (i - b)) : ℕ)

lemma edgeTent_nonneg (m b i : ℕ) : 0 ≤ edgeTent m b i := by unfold edgeTent; positivity

lemma edgeTent_le (m b i : ℕ) : edgeTent m b i ≤ m := by
  unfold edgeTent
  exact_mod_cast (min_le_left _ _).trans (min_le_right _ _)

lemma edgeTent_zero_left {m b i : ℕ} (hi : i ≤ b) : edgeTent m b i = 0 := by
  simp [edgeTent, Nat.sub_eq_zero_of_le hi]

lemma edgeTent_zero_right {m b i : ℕ} (hi : b + 4*m ≤ i) : edgeTent m b i = 0 := by
  have h : 4*m ≤ i-b := by omega
  simp [edgeTent, Nat.sub_eq_zero_of_le h]

lemma edgeTent_plateau {m b i : ℕ} (hlo : b+m ≤ i) (hhi : i ≤ b+3*m) :
    edgeTent m b i = m := by
  have h1 : m ≤ i-b := by omega
  have h2 : m ≤ 4*m-(i-b) := by omega
  simp [edgeTent, min_eq_right h1, min_eq_left h2]

lemma edgeTent_lipschitz (m b i : ℕ) : |edgeTent m b (i+1) - edgeTent m b i| ≤ 1 := by
  unfold edgeTent
  rw [abs_le]
  have h1 : min (min (i+1-b) m) (4*m-(i+1-b)) ≤ min (min (i-b) m) (4*m-(i-b)) + 1 := by omega
  have h2 : min (min (i-b) m) (4*m-(i-b)) ≤ min (min (i+1-b) m) (4*m-(i+1-b)) + 1 := by omega
  have hh1 : ((min (min (i+1-b) m) (4*m-(i+1-b)) : ℕ) : ℝ) ≤ ((min (min (i-b) m) (4*m-(i-b)) : ℕ) : ℝ) + 1 := by exact_mod_cast h1
  have hh2 : ((min (min (i-b) m) (4*m-(i-b)) : ℕ) : ℝ) ≤ ((min (min (i+1-b) m) (4*m-(i+1-b)) : ℕ) : ℝ) + 1 := by exact_mod_cast h2
  constructor <;> linarith

lemma edgeTent_gradient_support {m b i : ℕ} (hi : i ∉ Finset.Ico b (b+4*m)) :
    edgeTent m b (i+1) - edgeTent m b i = 0 := by
  simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hi
  rcases hi with hi | hi
  · rw [edgeTent_zero_left (by omega), edgeTent_zero_left (by omega), sub_self]
  · rw [edgeTent_zero_right (by omega), edgeTent_zero_right hi, sub_self]

lemma edgeTent_gradient (m b n : ℕ) :
    (∑ i ∈ Finset.range n, (edgeTent m b (i+1) - edgeTent m b i)^2) ≤ 4 * m := by
  have hpoint (i : ℕ) : (edgeTent m b (i+1) - edgeTent m b i)^2 ≤
      if i ∈ Finset.Ico b (b+4*m) then (1 : ℝ) else 0 := by
    split_ifs with hi
    · have h := edgeTent_lipschitz m b i
      nlinarith [sq_abs (edgeTent m b (i+1) - edgeTent m b i), abs_nonneg (edgeTent m b (i+1) - edgeTent m b i)]
    · rw [edgeTent_gradient_support hi]; norm_num
  calc
    _ ≤ ∑ i ∈ Finset.range n, if i ∈ Finset.Ico b (b+4*m) then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ ≤ ∑ i ∈ Finset.Ico b (b+4*m), (1 : ℝ) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi; exact (Finset.mem_filter.mp hi).2
      · intros; positivity
    _ = 4*m := by simp

lemma edgeTent_mass {m b n : ℕ} (hfit : b+2*m ≤ n+1) :
    (m : ℝ)^3 ≤ ∑ i ∈ Finset.range (n+1), edgeTent m b i ^ 2 := by
  calc
    (m : ℝ)^3 = ∑ i ∈ Finset.Ico (b+m) (b+2*m), (m : ℝ)^2 := by
      have h : b+2*m-(b+m) = m := by omega
      simp only [Finset.sum_const, Nat.card_Ico, h, nsmul_eq_mul]
      ring
    _ = ∑ i ∈ Finset.Ico (b+m) (b+2*m), edgeTent m b i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [edgeTent_plateau (Finset.mem_Ico.mp hi).1 (by have := (Finset.mem_Ico.mp hi).2; omega)]
    _ ≤ ∑ i ∈ Finset.range (n+1), edgeTent m b i ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp only [Finset.mem_range]
        have := (Finset.mem_Ico.mp hi).2
        omega
      · intros; positivity

lemma edgeCoeff_lower (n i : ℕ) (hi : i ≤ n) :
    1 - (i+1 : ℝ)/(n+1) ≤ edgeCoeff n i := by
  have hn : (0 : ℝ) < n+1 := by positivity
  have ht : (i+1 : ℝ) ≤ n+1 := by exact_mod_cast Nat.succ_le_succ hi
  have h0 : 0 ≤ 1 - (i+1 : ℝ)/(n+1) := sub_nonneg.mpr ((div_le_one hn).mpr ht)
  have h1 : 1 - (i+1 : ℝ)/(n+1) ≤ 1 := sub_le_self _ (by positivity)
  dsimp [edgeCoeff]
  have hs := Real.sq_sqrt h0
  nlinarith [Real.sqrt_nonneg (1 - (i+1 : ℝ)/(n+1)), mul_nonneg h0 (sub_nonneg.mpr h1)]

lemma edge_potential_upper {n i : ℕ} (hi : i ≤ n) (hi0 : i ≠ 0) :
    2 - edgeCoeff n i - edgeCoeff n (i-1) ≤ 2*(i+1 : ℝ)/(n+1) := by
  have h1 := edgeCoeff_lower n i hi
  have h2 := edgeCoeff_lower n (i-1) (by omega)
  have h3 : (i-1+1 : ℕ) = i := by omega
  have h4 : ((i-1 : ℕ) : ℝ) + 1 = i := by exact_mod_cast h3
  have h5 : (i : ℝ)/(n+1) ≤ (i+1 : ℝ)/(n+1) := by gcongr; linarith
  rw [h4] at h2
  rw [mul_div_assoc]
  linarith

lemma edgeTent_energy {m b n : ℕ} (_hfit : b+4*m ≤ n) :
    pathEnergy n (edgeTent m b) ≤ 4*m + (2*(b+4*m+1 : ℝ)/(n+1)) *
      (∑ i ∈ Finset.range (n+1), edgeTent m b i ^ 2) := by
  rw [pathEnergy_expansion]
  apply add_le_add
  · calc
      _ ≤ ∑ i ∈ Finset.range n, (edgeTent m b (i+1)-edgeTent m b i)^2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_of_le_one_left (sq_nonneg _) (edgeCoeff_le_one n i (by have := Finset.mem_range.mp hi; omega))
      _ ≤ 4*m := edgeTent_gradient m b n
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    by_cases hi0 : i = 0
    · subst i; rw [edgeTent_zero_left (by omega)]; simp
    · simp only [ite_eq_right hi0]
      by_cases hit : b+4*m ≤ i
      · rw [edgeTent_zero_right hit]; simp
      · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        apply (edge_potential_upper (by have := Finset.mem_range.mp hi; omega) hi0).trans
        gcongr
        exact_mod_cast (show i ≤ b+4*m by omega)

lemma edgeTent_mul_zero {m b d i : ℕ} (hgap : b+4*m ≤ d) :
    edgeTent m b i * edgeTent m d i = 0 := by
  by_cases h : i ≤ d
  · rw [edgeTent_zero_left h, mul_zero]
  · rw [edgeTent_zero_right (by omega), zero_mul]

lemma edgeTent_adj_mul_zero {m b d i : ℕ} (hgap : b+4*m ≤ d) :
    edgeTent m b i * edgeTent m d (i+1) = 0 := by
  by_cases h : i+1 ≤ d
  · rw [edgeTent_zero_left h, mul_zero]
  · rw [edgeTent_zero_right (by omega), zero_mul]

lemma edgeTent_adj_mul_zero' {m b d i : ℕ} (hgap : b+4*m ≤ d) :
    edgeTent m d i * edgeTent m b (i+1) = 0 := by
  by_cases h : i ≤ d
  · rw [edgeTent_zero_left h, zero_mul]
  · rw [edgeTent_zero_right (m := m) (b := b) (i := i+1) (by omega), mul_zero]

lemma separated_tents {m k l i : ℕ} (hkl : k ≠ l) :
    edgeTent m (4*m*k) i * edgeTent m (4*m*l) i = 0 := by
  rcases lt_or_gt_of_ne hkl with h | h
  · apply edgeTent_mul_zero
    nlinarith
  · rw [mul_comm]
    apply edgeTent_mul_zero
    nlinarith

lemma separated_tents_adj {m k l i : ℕ} (hkl : k ≠ l) :
    edgeTent m (4*m*k) i * edgeTent m (4*m*l) (i+1) = 0 := by
  rcases lt_or_gt_of_ne hkl with h | h
  · apply edgeTent_adj_mul_zero
    nlinarith
  · apply edgeTent_adj_mul_zero'
    nlinarith

lemma sum_mul_diagonal {ι : Type*} [Fintype ι] (u v c : ι → ℝ)
    (huv : ∀ i j, i ≠ j → u i * v j = 0) :
    (∑ i, c i * u i) * (∑ i, c i * v i) = ∑ i, c i ^ 2 * u i * v i := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · ring
  · intro j _ hji
    calc
      _ = (c i * c j) * (u i * v j) := by ring
      _ = 0 := by rw [huv i j hji.symm, mul_zero]
  · simp

def tentCombination {r : ℕ} (m : ℕ) (c : Fin r → ℝ) (i : ℕ) : ℝ :=
  ∑ k, c k * edgeTent m (4*m*k.val) i

lemma tentCombination_sq {r : ℕ} (m : ℕ) (c : Fin r → ℝ) (i : ℕ) :
    tentCombination m c i ^ 2 = ∑ k, c k ^ 2 * edgeTent m (4*m*k.val) i ^ 2 := by
  rw [sq, tentCombination, sum_mul_diagonal]
  · apply Finset.sum_congr rfl
    intros
    ring
  · intro k l hkl
    exact separated_tents (fun h => hkl (Fin.ext h))

lemma tentCombination_adj {r : ℕ} (m : ℕ) (c : Fin r → ℝ) (i : ℕ) :
    tentCombination m c i * tentCombination m c (i+1) =
      ∑ k, c k ^ 2 * edgeTent m (4*m*k.val) i * edgeTent m (4*m*k.val) (i+1) := by
  exact sum_mul_diagonal _ _ _ (fun k l hkl => separated_tents_adj (fun h => hkl (Fin.ext h)))

lemma tentCombination_mass {r : ℕ} (m n : ℕ) (c : Fin r → ℝ) :
    (∑ i ∈ Finset.range (n+1), tentCombination m c i ^ 2) =
      ∑ k, c k ^ 2 * ∑ i ∈ Finset.range (n+1), edgeTent m (4*m*k.val) i ^ 2 := by
  simp only [tentCombination_sq, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma tentCombination_energy {r : ℕ} (m n : ℕ) (c : Fin r → ℝ) :
    pathEnergy n (tentCombination m c) =
      ∑ k, c k ^ 2 * pathEnergy n (edgeTent m (4*m*k.val)) := by
  simp only [pathEnergy, tentCombination_sq, tentCombination_adj,
    mul_assoc, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (s := Finset.range (n+1)), Finset.sum_comm (s := Finset.range n)]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro k _
  · apply Finset.sum_congr rfl
    intros
    ring
  · apply Finset.sum_congr rfl
    intros
    ring

lemma edgeTent_rayleigh {m b n : ℕ} (hm : 0 < m) (hfit : b+4*m ≤ n) :
    pathEnergy n (edgeTent m b) ≤
      (4/(m : ℝ)^2 + 2*(b+4*m+1 : ℝ)/(n+1)) *
        ∑ i ∈ Finset.range (n+1), edgeTent m b i ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmass := edgeTent_mass (m := m) (b := b) (n := n) (by omega)
  have h := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 4/(m : ℝ)^2 by positivity)
  have he : 4/(m : ℝ)^2 * (m : ℝ)^3 = 4*m := by field_simp
  rw [he] at h
  have henergy := edgeTent_energy hfit
  nlinarith

lemma tentCombination_rayleigh {m n r : ℕ} (hm : 0 < m) (hfit : 4*m*r ≤ n)
    (c : Fin r → ℝ) :
    pathEnergy n (tentCombination m c) ≤
      (4/(m : ℝ)^2 + 2*(4*m*r+1 : ℝ)/(n+1)) *
        ∑ i ∈ Finset.range (n+1), tentCombination m c i ^ 2 := by
  rw [tentCombination_mass, tentCombination_energy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hk : 4*m*k.val+4*m ≤ 4*m*r := by nlinarith [k.isLt]
  have h := edgeTent_rayleigh hm (hk.trans hfit)
  have h' : 4/(m : ℝ)^2 + 2*(4*m*k.val+4*m+1 : ℝ)/(n+1) ≤
      4/(m : ℝ)^2 + 2*(4*m*r+1 : ℝ)/(n+1) := by
    gcongr
    exact_mod_cast (by nlinarith [k.isLt] : 4*m*k.val+4*m ≤ 4*m*r)
  push_cast at h
  have hmass : 0 ≤ ∑ i ∈ Finset.range (n+1), edgeTent m (4*m*k.val) i ^ 2 := by positivity
  have hbound := h.trans (mul_le_mul_of_nonneg_right h' hmass)
  have hscaled := mul_le_mul_of_nonneg_left hbound (sq_nonneg (c k))
  convert hscaled using 1
  ring

lemma tentCombination_probe {m r : ℕ} (c : Fin r → ℝ) (k : Fin r) :
    tentCombination m c (4*m*k.val+m) = c k * m := by
  classical
  rw [tentCombination, Finset.sum_eq_single k]
  · rw [edgeTent_plateau (by omega) (by omega)]
  · intro l _ hlk
    by_cases hm : m = 0
    · subst m
      simp [edgeTent]
    have h := separated_tents (m := m) (i := 4*m*k.val+m)
      (show l.val ≠ k.val from fun h => hlk (Fin.ext h))
    rw [edgeTent_plateau (m := m) (b := 4*m*k.val) (i := 4*m*k.val+m) (by omega) (by omega)] at h
    have hz : edgeTent m (4*m*l.val) (4*m*k.val+m) = 0 :=
      (mul_eq_zero.mp h).resolve_right (by exact_mod_cast hm)
    rw [hz, mul_zero]
  · simp

def tentMap (m n r : ℕ) : (Fin r → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n+1)) where
  toFun c := WithLp.toLp 2 (fun i => tentCombination m c i.val)
  map_add' c d := by
    ext i
    simp only [tentCombination, Pi.add_apply, PiLp.add_apply,
      add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    ext i
    simp only [tentCombination, Pi.smul_apply, smul_eq_mul,
      PiLp.smul_apply, RingHom.id_apply, mul_assoc, Finset.mul_sum]

lemma tentMap_injective {m n r : ℕ} (hm : 0 < m) (hfit : 4*m*r ≤ n) :
    Function.Injective (tentMap m n r) := by
  intro c d h
  funext k
  have hidx : 4*m*k.val+m < n+1 := by nlinarith [k.isLt]
  have he := congrArg (fun u : EuclideanSpace ℝ (Fin (n+1)) =>
    u ⟨4*m*k.val+m, hidx⟩) h
  change tentCombination m c (4*m*k.val+m) = tentCombination m d (4*m*k.val+m) at he
  rw [tentCombination_probe, tentCombination_probe] at he
  exact mul_right_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hm)) he

lemma tentMap_rank {m n r : ℕ} (hm : 0 < m) (hfit : 4*m*r ≤ n) :
    finrank ℝ (LinearMap.range (tentMap m n r)) = r := by
  rw [← LinearEquiv.finrank_eq (LinearEquiv.ofInjective _ (tentMap_injective hm hfit))]
  simp

lemma tentMap_mass (m n r : ℕ) (c : Fin r → ℝ) :
    (∑ i ∈ Finset.range (n+1), tentCombination m c i ^ 2) = ‖tentMap m n r c‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [tentMap, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply,
    Real.norm_eq_abs, sq_abs]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

lemma eigenvalue_lower_of_subspace {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {n : ℕ} (hn : finrank ℝ E = n)
    (S : Submodule ℝ E) (i : Fin n) {a : ℝ}
    (hdim : i.val < finrank ℝ S)
    (hquad : ∀ x : E, x ∈ S → ‖x‖ = 1 → a ≤ inner ℝ x (T x)) :
    a ≤ hT.eigenvalues hn i := by
  let b := hT.eigenvectorBasis hn
  let U := basisSpan b (Finset.Ici i)
  have hnot : ¬ Disjoint S U := by
    intro hd
    have h := Submodule.finrank_add_finrank_le_of_disjoint hd
    rw [show U = basisSpan b (Finset.Ici i) from rfl, basisSpan_finrank,
      Fin.card_Ici, hn] at h
    omega
  rw [Submodule.disjoint_def] at hnot
  push Not at hnot
  obtain ⟨x, hxS, hxU, hx⟩ := hnot
  let y := ‖x‖⁻¹ • x
  have hy : ‖y‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)
  have hlow := hquad y (S.smul_mem _ hxS) hy
  have hupp := basisQuadratic_le b (hT.eigenvalues hn) (Finset.Ici i)
    (U.smul_mem ‖x‖⁻¹ hxU) hy (fun j hj => hT.eigenvalues_antitone hn (Finset.mem_Ici.mp hj))
  rw [eigenbasisQuadratic_eq] at hupp
  exact hlow.trans hupp

def scaledHermite (a : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | k + 1 => X * scaledHermite a k - C a * derivative (scaledHermite a k)

@[simp] lemma scaledHermite_zero (a : ℝ) : scaledHermite a 0 = 1 := rfl

lemma scaledHermite_succ (a : ℝ) (k : ℕ) :
    scaledHermite a (k + 1) = X * scaledHermite a k - C a * derivative (scaledHermite a k) := rfl

lemma derivative_scaledHermite_succ (a : ℝ) (k : ℕ) :
    derivative (scaledHermite a (k + 1)) = C (k + 1 : ℝ) * scaledHermite a k := by
  induction k with
  | zero => simp [scaledHermite]
  | succ k ih =>
    rw [scaledHermite_succ a (k + 1), derivative_sub, derivative_mul, derivative_X,
      one_mul, ih, derivative_mul, derivative_C, zero_mul, zero_add]
    rw [derivative_mul, derivative_C, zero_mul, zero_add]
    rw [scaledHermite_succ a k]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

lemma scaledHermite_three_term (a : ℝ) (k : ℕ) :
    scaledHermite a (k + 2) = X * scaledHermite a (k + 1) -
      C (a * (k + 1)) * scaledHermite a k := by
  rw [show k + 2 = (k + 1) + 1 by omega, scaledHermite_succ,
    derivative_scaledHermite_succ, map_mul, mul_assoc]

lemma scaledHermite_differential (a : ℝ) (k : ℕ) :
    C a * derivative (derivative (scaledHermite a k)) -
      X * derivative (scaledHermite a k) + C (k : ℝ) * scaledHermite a k = 0 := by
  have h := derivative_scaledHermite_succ a k
  rw [scaledHermite_succ, derivative_sub, derivative_mul, derivative_X,
    one_mul, derivative_mul, derivative_C, zero_mul, zero_add] at h
  simp only [map_add, map_one] at h
  linear_combination -h

lemma scaledHermite_degree_gap (a : ℝ) (p : Polynomial ℝ) (hp : p ≠ 0) :
    (C a * derivative p).degree < (X * p).degree := by
  by_cases ha : a = 0
  · simp only [ha, map_zero, zero_mul, degree_zero]
    exact degree_ne_bot.mpr (mul_ne_zero X_ne_zero hp) |>.bot_lt
  · rw [degree_C_mul ha, mul_comm X p]
    exact degree_derivative_le.trans_lt (degree_lt_degree_mul_X hp)

lemma scaledHermite_monic (a : ℝ) (k : ℕ) : (scaledHermite a k).Monic := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [scaledHermite_succ]
    exact (monic_X.mul ih).sub_of_left (scaledHermite_degree_gap a _ ih.ne_zero)

lemma scaledHermite_degree (a : ℝ) (k : ℕ) : (scaledHermite a k).degree = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [scaledHermite_succ, degree_sub_eq_left_of_degree_lt
      (scaledHermite_degree_gap a _ (scaledHermite_monic a k).ne_zero), mul_comm X _,
      degree_mul_X, ih]
    norm_cast

lemma det_tridiagonal_step {R : Type*} [CommRing R] (k : ℕ)
    (A : Matrix (Fin (k + 2)) (Fin (k + 2)) R)
    (hrow : ∀ j : Fin k, A 0 j.succ.succ = 0)
    (hcol : ∀ i : Fin k, A i.succ.succ 0 = 0) :
    A.det = A 0 0 * (A.submatrix Fin.succ Fin.succ).det -
      A 0 1 * A 1 0 * (A.submatrix (Fin.succ ∘ Fin.succ) (Fin.succ ∘ Fin.succ)).det := by
  have hminor : (A.submatrix Fin.succ (1 : Fin (k + 2)).succAbove).det =
      A 1 0 * (A.submatrix (Fin.succ ∘ Fin.succ) (Fin.succ ∘ Fin.succ)).det := by
    rw [det_succ_column_zero, Fin.sum_univ_succ]
    simp only [Matrix.submatrix_apply, Fin.val_zero, pow_zero, one_mul,
      Fin.succ_zero_eq_one, Fin.one_succAbove_zero, hcol, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero, submatrix_submatrix, Fin.succAbove_zero]
    congr 2
  rw [det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, Fin.val_succ,
    Fin.succ_zero_eq_one, hminor, hrow, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, Fin.val_one, pow_one, neg_one_mul]
  ring

def jacobi (a : ℝ) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ := fun i j =>
  if i.val + 1 = j.val then Real.sqrt (a * ((k : ℝ) - 1 - i.val))
  else if j.val + 1 = i.val then Real.sqrt (a * ((k : ℝ) - 1 - j.val)) else 0

lemma jacobi_diagonal (a : ℝ) (k : ℕ) (i : Fin k) : jacobi a k i i = 0 := by
  simp [jacobi]

lemma jacobi_symmetric (a : ℝ) (k : ℕ) : (jacobi a k).IsSymm := by
  ext i j
  dsimp [jacobi, Matrix.transpose]
  split_ifs with h₁ h₂ h₃ <;> first | rfl | omega

lemma jacobi_tail (a : ℝ) (k : ℕ) :
    (jacobi a (k + 1)).submatrix Fin.succ Fin.succ = jacobi a k := by
  ext i j
  simp only [Matrix.submatrix_apply, jacobi, Fin.val_succ, Nat.add_right_cancel_iff,
    Nat.cast_add, Nat.cast_one]
  split_ifs <;> congr 1 <;> ring

lemma jacobi_row_zero (a : ℝ) (k : ℕ) (j : Fin k) : jacobi a (k + 2) 0 j.succ.succ = 0 := by
  simp [jacobi]

lemma jacobi_col_zero (a : ℝ) (k : ℕ) (i : Fin k) : jacobi a (k + 2) i.succ.succ 0 = 0 := by
  simp [jacobi]

lemma jacobi_first_super (a : ℝ) (k : ℕ) :
    jacobi a (k + 2) 0 1 = Real.sqrt (a * (k + 1)) := by
  simp [jacobi]
  congr 1
  ring

lemma jacobi_first_sub (a : ℝ) (k : ℕ) :
    jacobi a (k + 2) 1 0 = Real.sqrt (a * (k + 1)) := by
  simp [jacobi]
  congr 1
  ring

lemma charmatrix_jacobi_tail (a : ℝ) (k : ℕ) :
    ((jacobi a (k + 1)).charmatrix).submatrix Fin.succ Fin.succ =
      (jacobi a k).charmatrix := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [jacobi_diagonal]
  · simp [hij, charmatrix_apply_ne, ← jacobi_tail a k]

lemma jacobi_charpoly_step {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    (jacobi a (k + 2)).charpoly = X * (jacobi a (k + 1)).charpoly -
      C (a * (k + 1)) * (jacobi a k).charpoly := by
  have hr (j : Fin k) : (jacobi a (k + 2)).charmatrix 0 j.succ.succ = 0 := by
    rw [charmatrix_apply_ne _ _ _ (by simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_succ]; omega), jacobi_row_zero]
    simp
  have hc (i : Fin k) : (jacobi a (k + 2)).charmatrix i.succ.succ 0 = 0 := by
    rw [charmatrix_apply_ne _ _ _ (by simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_succ]; omega), jacobi_col_zero]
    simp
  unfold Matrix.charpoly
  rw [det_tridiagonal_step k _ hr hc, charmatrix_apply_eq, jacobi_diagonal,
    map_zero, sub_zero, charmatrix_jacobi_tail,
    charmatrix_apply_ne _ _ _ (by simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_one]; omega : (0 : Fin (k + 2)) ≠ 1),
    charmatrix_apply_ne _ _ _ (by simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_one]; omega : (1 : Fin (k + 2)) ≠ 0),
    jacobi_first_super, jacobi_first_sub, neg_mul_neg, ← map_mul,
    ← sq, Real.sq_sqrt (by positivity)]
  congr 2
  rw [← submatrix_submatrix, charmatrix_jacobi_tail, charmatrix_jacobi_tail]

lemma jacobi_charpoly {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    (jacobi a k).charpoly = scaledHermite a k := by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one =>
    have hz : jacobi a 1 = 0 := by ext i j; fin_cases i; fin_cases j; simp [jacobi]
    simp [hz, scaledHermite]
  | more k h0 h1 => rw [jacobi_charpoly_step ha, h0, h1, scaledHermite_three_term]

lemma finset_sum_indicator_le_one {ι : Type*} [Fintype ι] (p : ι → Prop)
    [DecidablePred p] (hp : ∀ i j, p i → p j → i = j) :
    (∑ i, if p i then (1 : ℝ) else 0) ≤ 1 := by
  classical
  by_cases hex : ∃ i, p i
  · obtain ⟨i, hi⟩ := hex
    have heq : ∀ j, p j ↔ j = i := fun j => ⟨fun hj => hp j i hj hi, fun h => h ▸ hi⟩
    simp_rw [heq]
    simp
  · simp [not_exists.mp hex]

lemma jacobi_row_norm_bound (n : ℕ) (i : Fin n) :
    ∑ j : Fin n, ‖jacobi (n : ℝ)⁻¹ n i j‖ ≤ 2 := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hentry (k : Fin n) : Real.sqrt ((n : ℝ)⁻¹ * ((n : ℝ) - 1 - k.val)) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    have hk : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    apply (inv_mul_le_iff₀ hn).mpr
    linarith
  have hpoint (j : Fin n) : ‖jacobi (n : ℝ)⁻¹ n i j‖ ≤
      (if i.val + 1 = j.val then 1 else 0) + (if j.val + 1 = i.val then 1 else 0) := by
    unfold jacobi
    split_ifs <;> simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      norm_zero] <;> linarith [hentry i, hentry j]
  have h₁ := finset_sum_indicator_le_one (fun j : Fin n => i.val + 1 = j.val)
    (fun j k hj hk => Fin.ext (by omega))
  have h₂ := finset_sum_indicator_le_one (fun j : Fin n => j.val + 1 = i.val)
    (fun j k hj hk => Fin.ext (by omega))
  have hb := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hpoint j)
  rw [Finset.sum_add_distrib] at hb
  linarith

lemma jacobi_hermitian (a : ℝ) (n : ℕ) : (jacobi a n).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr (jacobi_symmetric a n)

lemma jacobi_eigenvalue_bound (n : ℕ) (i : Fin n) :
    |(jacobi_hermitian (n : ℝ)⁻¹ n).eigenvalues i| ≤ 2 := by
  let hA := jacobi_hermitian (n : ℝ)⁻¹ n
  have he : Module.End.HasEigenvalue (Matrix.toLin' (jacobi (n : ℝ)⁻¹ n))
      (hA.eigenvalues i) := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨Module.End.mem_eigenspace_iff.mpr (hA.mulVec_eigenvectorBasis i), ?_⟩
    intro h
    apply hA.eigenvectorBasis.orthonormal.ne_zero i
    ext j
    exact congrFun h j
  obtain ⟨j, hj⟩ := eigenvalue_mem_ball he
  rw [Metric.mem_closedBall, jacobi_diagonal, dist_zero_right, Real.norm_eq_abs] at hj
  exact hj.trans ((Finset.sum_le_univ_sum_of_nonneg (fun _ => norm_nonneg _)).trans
    (jacobi_row_norm_bound n j))

section

def semicircleResolvent (s : ℝ) : ℝ := (2 + s - Real.sqrt (s * (4 + s))) / 2

def empiricalResolvent {ι : Type*} [Fintype ι] (e : ι → ℝ) (s : ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, (s + e i)⁻¹

def empiricalResolventSquare {ι : Type*} [Fintype ι] (e : ι → ℝ) (s : ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, (s + e i)⁻¹ ^ 2

lemma semicircle_discriminant_pos {s : ℝ} (hs : 0 < s) : 0 < s * (4 + s) := by positivity

lemma semicircleResolvent_pos {s : ℝ} (hs : 0 < s) : 0 < semicircleResolvent s := by
  have hn := Real.sqrt_nonneg (s * (4 + s))
  have hsq := Real.sq_sqrt (semicircle_discriminant_pos hs).le
  unfold semicircleResolvent
  nlinarith

lemma semicircleResolvent_le_one {s : ℝ} (hs : 0 ≤ s) : semicircleResolvent s ≤ 1 := by
  have hn := Real.sqrt_nonneg (s * (4 + s))
  have hsq := Real.sq_sqrt (show 0 ≤ s * (4 + s) by positivity)
  unfold semicircleResolvent
  nlinarith

lemma semicircleResolvent_deficit {s : ℝ} (hs : 0 ≤ s) :
    1 - semicircleResolvent s ≤ Real.sqrt s := by
  have hn := Real.sqrt_nonneg (s * (4 + s))
  have hsq := Real.sq_sqrt (show 0 ≤ s * (4 + s) by positivity)
  have hb := Real.sqrt_nonneg s
  have hb2 := Real.sq_sqrt hs
  unfold semicircleResolvent
  nlinarith [mul_nonneg hs hb]

lemma semicircleResolvent_difference {s : ℝ} (hs : 0 ≤ s) :
    semicircleResolvent (s / 2) - semicircleResolvent s ≤ Real.sqrt s := by
  have := semicircleResolvent_le_one (show 0 ≤ s / 2 by positivity)
  have := semicircleResolvent_deficit hs
  linarith

lemma semicircle_discriminant_lower {s : ℝ} (hs : 0 ≤ s) :
    2 * Real.sqrt s ≤ Real.sqrt (s * (4 + s)) := by
  have hn := Real.sqrt_nonneg (s * (4 + s))
  have hsq := Real.sq_sqrt (show 0 ≤ s * (4 + s) by positivity)
  have hb := Real.sqrt_nonneg s
  have hb2 := Real.sq_sqrt hs
  nlinarith

variable {ι : Type*} [Fintype ι] [Nonempty ι] (e : ι → ℝ) (he : ∀ i, 0 ≤ e i)

include he

lemma empiricalResolvent_pos {s : ℝ} (hs : 0 < s) : 0 < empiricalResolvent e s := by
  unfold empiricalResolvent
  apply mul_pos (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  exact Finset.sum_pos (fun i _ => inv_pos.mpr (add_pos_of_pos_of_nonneg hs (he i))) Finset.univ_nonempty

lemma empiricalResolventSquare_pos {s : ℝ} (hs : 0 < s) : 0 < empiricalResolventSquare e s := by
  unfold empiricalResolventSquare
  apply mul_pos (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  exact Finset.sum_pos (fun i _ => sq_pos_of_pos (inv_pos.mpr
    (add_pos_of_pos_of_nonneg hs (he i)))) Finset.univ_nonempty

lemma empiricalResolvent_le_inv {s : ℝ} (hs : 0 < s) : empiricalResolvent e s ≤ s⁻¹ := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  calc
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, s⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hn.le)
      apply Finset.sum_le_sum
      intro i _
      exact (inv_le_inv₀ (add_pos_of_pos_of_nonneg hs (he i)) hs).mpr (le_add_of_nonneg_right (he i))
    _ = s⁻¹ := by simp [hn.ne']

omit [Nonempty ι] in
lemma empiricalResolvent_continuousOn : ContinuousOn (empiricalResolvent e) (Set.Ioi 0) := by
  apply ContinuousOn.const_mul
  apply continuousOn_finsetSum
  intro i _
  apply ContinuousOn.inv₀ (continuousOn_id.add continuousOn_const)
  intro s hs
  exact ne_of_gt (add_pos_of_pos_of_nonneg hs (he i))

omit [Nonempty ι] in
lemma empiricalResolvent_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt (empiricalResolvent e) (-empiricalResolventSquare e s) s := by
  have h (i : ι) : HasDerivAt (fun u : ℝ => (u + e i)⁻¹) (-(s + e i)⁻¹ ^ 2) s := by
    convert! ((hasDerivAt_id s).add_const (e i)).inv (ne_of_gt
      (add_pos_of_pos_of_nonneg hs (he i))) using 1
    simp only [neg_div, one_div, inv_pow, id_eq]
  convert! (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => h i)).const_mul
    (Fintype.card ι : ℝ)⁻¹ using 1
  simp only [empiricalResolventSquare, Finset.sum_neg_distrib, mul_neg]

lemma empiricalResolvent_square_difference {s : ℝ} (hs : 0 < s) :
    empiricalResolventSquare e s ≤ 2 / s *
      (empiricalResolvent e (s / 2) - empiricalResolvent e s) := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hpoint (i : ι) : (s + e i)⁻¹ ^ 2 ≤ 2 / s * ((s / 2 + e i)⁻¹ - (s + e i)⁻¹) := by
    have hi : 0 < s + e i := by linarith [he i]
    have hi2 : 0 < s / 2 + e i := by linarith [he i]
    have hval : 2 / s * ((s / 2 + e i)⁻¹ - (s + e i)⁻¹) =
        ((s / 2 + e i) * (s + e i))⁻¹ := by
        rw [inv_sub_inv hi2.ne' hi.ne',
          show s + e i - (s / 2 + e i) = s / 2 by ring, ← mul_div_assoc,
          show 2 / s * (s / 2) = 1 by field_simp, one_div]
    rw [hval, inv_pow]
    apply (inv_le_inv₀ (sq_pos_of_pos hi) (mul_pos hi2 hi)).mpr
    nlinarith
  unfold empiricalResolventSquare empiricalResolvent
  calc
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i, 2 / s * ((s / 2 + e i)⁻¹ - (s + e i)⁻¹) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hpoint i)) (inv_nonneg.mpr hn.le)
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_sub_distrib]; ring

lemma empiricalResolvent_lt_midpoint
    (hR : ∀ s : ℝ, 0 < s →
      (empiricalResolvent e s) ^ 2 - (2 + s) * empiricalResolvent e s + 1 =
        empiricalResolventSquare e s / Fintype.card ι)
    {s : ℝ} (hs : 0 < s) : empiricalResolvent e s < (2 + s) / 2 := by
  by_contra hbad
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  let f : ℝ → ℝ := fun u => (2 + u) / 2 - empiricalResolvent e u
  have hfs : f s ≤ 0 := by dsimp [f]; linarith
  have hft : 0 ≤ f (s + 2) := by
    have hb := empiricalResolvent_le_inv e he (show 0 < s + 2 by linarith)
    have hinv : (s + 2)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr (by linarith)
    dsimp [f]
    linarith
  have hc : ContinuousOn f (Set.Icc s (s + 2)) := by
    apply ContinuousOn.sub
    · exact (continuous_const.add continuous_id).continuousOn.div_const 2
    · exact (empiricalResolvent_continuousOn e he).mono (fun u hu => lt_of_lt_of_le hs hu.1)
  obtain ⟨u, hu, hzero⟩ := intermediate_value_Icc (show s ≤ s + 2 by linarith) hc ⟨hfs, hft⟩
  have hu0 : 0 < u := lt_of_lt_of_le hs hu.1
  have hid := hR u hu0
  have ht : 0 < empiricalResolventSquare e u / Fintype.card ι :=
    div_pos (empiricalResolventSquare_pos e he hu0) hn
  dsimp [f] at hzero
  nlinarith

lemma empiricalResolvent_lt_semicircle
    (hR : ∀ s : ℝ, 0 < s →
      (empiricalResolvent e s) ^ 2 - (2 + s) * empiricalResolvent e s + 1 =
        empiricalResolventSquare e s / Fintype.card ι)
    {s : ℝ} (hs : 0 < s) : empiricalResolvent e s < semicircleResolvent s := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hmid := empiricalResolvent_lt_midpoint e he hR hs
  have hid := hR s hs
  have ht : 0 < empiricalResolventSquare e s / Fintype.card ι :=
    div_pos (empiricalResolventSquare_pos e he hs) hn
  have hsq := Real.sq_sqrt (semicircle_discriminant_pos hs).le
  have hpos := Real.sqrt_nonneg (s * (4 + s))
  unfold semicircleResolvent
  nlinarith

lemma empiricalResolvent_root_difference
    (hR : ∀ s : ℝ, 0 < s →
      (empiricalResolvent e s) ^ 2 - (2 + s) * empiricalResolvent e s + 1 =
        empiricalResolventSquare e s / Fintype.card ι)
    {s : ℝ} (hs : 0 < s) :
    0 ≤ semicircleResolvent s - empiricalResolvent e s ∧
      semicircleResolvent s - empiricalResolvent e s ≤
        empiricalResolventSquare e s /
          ((Fintype.card ι : ℝ) * Real.sqrt (s * (4 + s))) := by
  have hd := (empiricalResolvent_lt_semicircle e he hR hs).le
  refine ⟨sub_nonneg.mpr hd, ?_⟩
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hpos : 0 < Real.sqrt (s * (4 + s)) := Real.sqrt_pos.mpr (semicircle_discriminant_pos hs)
  have hsq := Real.sq_sqrt (semicircle_discriminant_pos hs).le
  have hid := hR s hs
  apply (le_div_iff₀ (mul_pos hn hpos)).mpr
  have hid' := (eq_div_iff hn.ne').mp hid
  unfold semicircleResolvent at *
  nlinarith [sq_nonneg ((2 + s - Real.sqrt (s * (4 + s))) / 2 - empiricalResolvent e s)]

lemma empiricalResolventSquare_bound
    (hR : ∀ s : ℝ, 0 < s →
      (empiricalResolvent e s) ^ 2 - (2 + s) * empiricalResolvent e s + 1 =
        empiricalResolventSquare e s / Fintype.card ι)
    {s : ℝ} (hs : 0 < s)
    (hscale : 4 ≤ (Fintype.card ι : ℝ) * s * Real.sqrt (s * (4 + s))) :
    empiricalResolventSquare e s ≤ 4 / Real.sqrt s := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hsp := Real.sqrt_pos.mpr hs
  have hsq := Real.sq_sqrt hs.le
  have hdisc := Real.sqrt_pos.mpr (semicircle_discriminant_pos hs)
  have hd := empiricalResolvent_root_difference e he hR hs
  have hhalf := (empiricalResolvent_lt_semicircle e he hR (show 0 < s / 2 by positivity)).le
  have hdiff := semicircleResolvent_difference hs.le
  have hb := empiricalResolvent_square_difference e he hs
  have hT := (empiricalResolventSquare_pos e he hs).le
  have hd' : 2 * (semicircleResolvent s - empiricalResolvent e s) ≤
      s * empiricalResolventSquare e s / 2 := by
    have hden : 0 < (Fintype.card ι : ℝ) * Real.sqrt (s * (4 + s)) := mul_pos hn hdisc
    have hmul := (le_div_iff₀ hden).mp hd.2
    have hscl : 4 ≤ s * ((Fintype.card ι : ℝ) * Real.sqrt (s * (4 + s))) := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hscl hd.1
    have hm2 := mul_le_mul_of_nonneg_left hmul hs.le
    nlinarith
  have hb' : s * empiricalResolventSquare e s ≤
      2 * (empiricalResolvent e (s / 2) - empiricalResolvent e s) := by
    have := (mul_le_mul_of_nonneg_left hb hs.le)
    field_simp at this
    nlinarith
  apply (le_div_iff₀ hsp).mpr
  have hmain : s * empiricalResolventSquare e s ≤ 4 * Real.sqrt s := by linarith
  have := mul_le_mul_of_nonneg_right hmain hsp.le
  nlinarith

lemma empiricalResolvent_error_bound
    (hR : ∀ s : ℝ, 0 < s →
      (empiricalResolvent e s) ^ 2 - (2 + s) * empiricalResolvent e s + 1 =
        empiricalResolventSquare e s / Fintype.card ι)
    {s : ℝ} (hs : 0 < s)
    (hscale : 4 ≤ (Fintype.card ι : ℝ) * s * Real.sqrt (s * (4 + s))) :
    0 ≤ semicircleResolvent s - empiricalResolvent e s ∧
      semicircleResolvent s - empiricalResolvent e s ≤ 2 / ((Fintype.card ι : ℝ) * s) := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hsp := Real.sqrt_pos.mpr hs
  have hsq := Real.sq_sqrt hs.le
  have hdisc := Real.sqrt_pos.mpr (semicircle_discriminant_pos hs)
  have hd := empiricalResolvent_root_difference e he hR hs
  refine ⟨hd.1, ?_⟩
  have hT := empiricalResolventSquare_bound e he hR hs hscale
  have hlow := semicircle_discriminant_lower hs.le
  have hd' := (le_div_iff₀ (mul_pos hn hdisc)).mp hd.2
  have hT' := (le_div_iff₀ hsp).mp hT
  have hm := mul_le_mul_of_nonneg_right hd' hsp.le
  have hlow' := mul_le_mul_of_nonneg_left hlow (mul_nonneg hd.1 hn.le)
  have hlow'' := mul_le_mul_of_nonneg_right hlow' hsp.le
  apply (le_div_iff₀ (mul_pos hn hs)).mpr
  nlinarith

lemma empiricalResolvent_counting {s : ℝ} (hs : 0 < s) :
    ((Finset.univ.filter (fun i => e i ≤ s)).card : ℝ) ≤
      4 * (Fintype.card ι : ℝ) * s ^ 2 * empiricalResolventSquare e s := by
  classical
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hpoint (i : ι) (hi : e i ≤ s) : 1 ≤ 4 * s ^ 2 * (s + e i)⁻¹ ^ 2 := by
    have hsi : 0 < s + e i := by linarith [he i]
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (sq_pos_of_pos hsi)]
    nlinarith [he i]
  calc
    _ = ∑ _i ∈ Finset.univ.filter (fun i => e i ≤ s), (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => e i ≤ s), 4 * s ^ 2 * (s + e i)⁻¹ ^ 2 :=
      Finset.sum_le_sum (fun i hi => hpoint i (Finset.mem_filter.mp hi).2)
    _ ≤ ∑ i : ι, 4 * s ^ 2 * (s + e i)⁻¹ ^ 2 :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => by positivity)
    _ = _ := by
      unfold empiricalResolventSquare
      rw [← Finset.mul_sum]
      field_simp

end

open Matrix Polynomial Filter

noncomputable def jacobiGaps (n : ℕ) (i : Fin n) : ℝ :=
  2 - (jacobi_hermitian (n : ℝ)⁻¹ n).eigenvalues i

lemma jacobiGaps_nonneg (n : ℕ) (i : Fin n) : 0 ≤ jacobiGaps n i := by
  have := (abs_le.mp (jacobi_eigenvalue_bound n i)).2
  exact sub_nonneg.mpr this

lemma hermitian_charpoly_derivative_ratio {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) {z : ℝ} (hz : A.charpoly.eval z ≠ 0) :
    A.charpoly.derivative.eval z / A.charpoly.eval z = ∑ i, (z - hA.eigenvalues i)⁻¹ := by
  rw [hA.splits_charpoly.eval_derivative_div_eval_of_ne_zero hz,
    hA.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  simp [one_div]

lemma jacobi_charpoly_nonzero {n : ℕ} {s : ℝ} (hs : 0 < s) :
    (jacobi (n : ℝ)⁻¹ n).charpoly.eval (2 + s) ≠ 0 := by
  rw [(jacobi_hermitian (n : ℝ)⁻¹ n).charpoly_eq, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  simp only [eval_sub, eval_X, eval_C, RCLike.ofReal_real_eq_id, id_eq]
  have := jacobiGaps_nonneg n i
  dsimp [jacobiGaps] at this
  linarith

lemma jacobi_logarithmic_ratio {n : ℕ} {s : ℝ} (hs : 0 < s) :
    (jacobi (n : ℝ)⁻¹ n).charpoly.derivative.eval (2 + s) /
      (jacobi (n : ℝ)⁻¹ n).charpoly.eval (2 + s) =
        (n : ℝ) * empiricalResolvent (jacobiGaps n) s := by
  by_cases hn : n = 0
  · subst n
    simp [empiricalResolvent]
  · rw [hermitian_charpoly_derivative_ratio _ (jacobi_hermitian (n : ℝ)⁻¹ n)
      (jacobi_charpoly_nonzero hs)]
    simp only [empiricalResolvent, Fintype.card_fin, ← mul_assoc,
      mul_inv_cancel₀ (show (n : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hn), one_mul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simp [jacobiGaps]
    ring

lemma jacobi_riccati {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s) :
    (empiricalResolvent (jacobiGaps n) s) ^ 2 -
      (2 + s) * empiricalResolvent (jacobiGaps n) s + 1 =
        empiricalResolventSquare (jacobiGaps n) s / n := by
  let : NeZero n := ⟨hn.ne'⟩
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let p := (jacobi (n : ℝ)⁻¹ n).charpoly
  have hp : p.eval (2 + s) ≠ 0 := jacobi_charpoly_nonzero hs
  have hpd : HasDerivAt (fun u : ℝ => p.eval (2 + u)) (p.derivative.eval (2 + s)) s := by
    convert! (p.hasDerivAt (2 + s)).comp s ((hasDerivAt_id s).const_add 2) using 1
    simp only [mul_one]
  have hpdd : HasDerivAt (fun u : ℝ => p.derivative.eval (2 + u))
      (p.derivative.derivative.eval (2 + s)) s := by
    convert! (p.derivative.hasDerivAt (2 + s)).comp s ((hasDerivAt_id s).const_add 2) using 1
    simp only [mul_one]
  have hratio : HasDerivAt (fun u : ℝ => (n : ℝ)⁻¹ *
      (p.derivative.eval (2 + u) / p.eval (2 + u)))
      ((n : ℝ)⁻¹ * ((p.derivative.derivative.eval (2 + s) * p.eval (2 + s) -
        p.derivative.eval (2 + s) * p.derivative.eval (2 + s)) / p.eval (2 + s)^2)) s := by
    convert! (hpdd.div hpd hp).const_mul (n : ℝ)⁻¹ using 1
  have hlocal : (fun u : ℝ => (n : ℝ)⁻¹ *
      (p.derivative.eval (2 + u) / p.eval (2 + u))) =ᶠ[𝓝 s]
        empiricalResolvent (jacobiGaps n) := by
    filter_upwards [Ioi_mem_nhds hs] with u hu
    rw [jacobi_logarithmic_ratio hu, ← mul_assoc, inv_mul_cancel₀ hnR.ne', one_mul]
  have hder := (hratio.congr_of_eventuallyEq hlocal.symm).unique
    (empiricalResolvent_hasDerivAt (jacobiGaps n) (jacobiGaps_nonneg n) hs)
  have hode := congrArg (Polynomial.eval (2 + s)) (scaledHermite_differential (n : ℝ)⁻¹ n)
  rw [← jacobi_charpoly (inv_nonneg.mpr hnR.le) n] at hode
  rw [eval_zero] at hode
  change (C (n : ℝ)⁻¹ * p.derivative.derivative - X * p.derivative + C (n : ℝ) * p).eval (2 + s) = 0 at hode
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X] at hode
  have hv := jacobi_logarithmic_ratio (n := n) hs
  change p.derivative.eval (2 + s) / p.eval (2 + s) =
    (n : ℝ) * empiricalResolvent (jacobiGaps n) s at hv
  change (n : ℝ)⁻¹ * ((p.derivative.derivative.eval (2 + s) * p.eval (2 + s) -
        p.derivative.eval (2 + s) * p.derivative.eval (2 + s)) / p.eval (2 + s)^2) =
      -empiricalResolventSquare (jacobiGaps n) s at hder
  field_simp [hnR.ne', hp] at hode hv hder ⊢
  rw [hv] at hode hder
  have hh : (n : ℝ) * p.eval (2 + s) ^ 2 *
      ((n : ℝ) * (empiricalResolvent (jacobiGaps n) s *
        (empiricalResolvent (jacobiGaps n) s - (2 + s)) + 1) -
        empiricalResolventSquare (jacobiGaps n) s) = 0 := by
    linear_combination p.eval (2 + s) * hode - hder
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left
    (mul_ne_zero hnR.ne' (pow_ne_zero 2 hp)))

lemma jacobi_resolvent_estimates {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s)
    (hscale : 2 ≤ (n : ℝ) * s * Real.sqrt s) :
    empiricalResolventSquare (jacobiGaps n) s ≤ 4 / Real.sqrt s ∧
      0 ≤ semicircleResolvent s - empiricalResolvent (jacobiGaps n) s ∧
      semicircleResolvent s - empiricalResolvent (jacobiGaps n) s ≤ 2 / (n * s) := by
  let : NeZero n := ⟨hn.ne'⟩
  have hR : ∀ u : ℝ, 0 < u →
      (empiricalResolvent (jacobiGaps n) u) ^ 2 -
        (2 + u) * empiricalResolvent (jacobiGaps n) u + 1 =
          empiricalResolventSquare (jacobiGaps n) u / Fintype.card (Fin n) := by
    intro u hu
    simpa using (jacobi_riccati hn hu)
  have hscale' : 4 ≤ (Fintype.card (Fin n) : ℝ) * s * Real.sqrt (s * (4 + s)) := by
    have := mul_le_mul_of_nonneg_left (semicircle_discriminant_lower hs.le)
      (show 0 ≤ (n : ℝ) * s by positivity)
    simp only [Fintype.card_fin]
    nlinarith
  exact ⟨empiricalResolventSquare_bound _ (jacobiGaps_nonneg n) hR hs hscale',
    by simpa using empiricalResolvent_error_bound _ (jacobiGaps_nonneg n) hR hs hscale'⟩

lemma jacobi_gap_counting {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s)
    (hscale : 2 ≤ (n : ℝ) * s * Real.sqrt s) :
    ((Finset.univ.filter (fun i => jacobiGaps n i ≤ s)).card : ℝ) ≤
      16 * (n : ℝ) * s * Real.sqrt s := by
  let : NeZero n := ⟨hn.ne'⟩
  have hc := empiricalResolvent_counting _ (jacobiGaps_nonneg n) hs
  have ht := (jacobi_resolvent_estimates hn hs hscale).1
  have hsp := Real.sqrt_pos.mpr hs
  have hsq := Real.sq_sqrt hs.le
  calc
    _ ≤ 4 * (n : ℝ) * s ^ 2 * empiricalResolventSquare (jacobiGaps n) s := by simpa using hc
    _ ≤ 4 * (n : ℝ) * s ^ 2 * (4 / Real.sqrt s) := by gcongr
    _ = _ := by field_simp; nlinarith

def pathOperator (n : ℕ) : EuclideanSpace ℝ (Fin (n+1)) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin (n+1)) := Matrix.toLpLin 2 2 (jacobi ((n+1 : ℝ)⁻¹) (n+1))

lemma pathOperator_symmetric (n : ℕ) : (pathOperator n).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (jacobi_hermitian _ _)

lemma jacobi_edgeCoeff (n : ℕ) (i j : Fin (n+1)) :
    jacobi (n+1 : ℝ)⁻¹ (n+1) i j =
      (if i.val+1=j.val then edgeCoeff n i.val else 0) +
      (if j.val+1=i.val then edgeCoeff n j.val else 0) := by
  have hs (k : Fin (n+1)) :
      Real.sqrt ((n+1 : ℝ)⁻¹ * ((n+1 : ℝ)-1-k.val)) = edgeCoeff n k.val := by
    unfold edgeCoeff
    congr 1
    field_simp
    ring
  simp only [jacobi, Nat.cast_add, Nat.cast_one, hs]
  split_ifs with h h' h' <;> try rfl
  · omega
  · simp
  · simp
  · simp

lemma directed_neighbor_sum (n : ℕ) (u : ℕ → ℝ) :
    (∑ i : Fin (n+1), ∑ j : Fin (n+1),
      (if i.val+1=j.val then edgeCoeff n i.val else 0) * u i.val * u j.val) =
      ∑ i ∈ Finset.range n, edgeCoeff n i * u i * u (i+1) := by
  rw [Fin.sum_univ_castSucc]
  have hl : (∑ j : Fin (n+1),
      (if (Fin.last n).val+1=j.val then edgeCoeff n (Fin.last n).val else 0) *
        u (Fin.last n).val * u j.val) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [ite_eq_right (by have := j.isLt; simp only [Fin.val_last]; omega), zero_mul, zero_mul]
  rw [hl, add_zero, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i.succ]
  · simp
  · intro j _ hj
    rw [ite_eq_right (fun h => hj (Fin.ext (by simpa using h.symm))), zero_mul, zero_mul]
  · simp

lemma pathOperator_inner (n : ℕ) (u : ℕ → ℝ) :
    inner ℝ (WithLp.toLp 2 (fun i : Fin (n+1) => u i.val))
      (pathOperator n (WithLp.toLp 2 (fun i : Fin (n+1) => u i.val))) =
      2 * ∑ i ∈ Finset.range n, edgeCoeff n i * u i * u (i+1) := by
  simp only [pathOperator, Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct,
    Pi.star_apply, star_trivial, dotProduct, Matrix.mulVec,
    jacobi_edgeCoeff, add_mul, Finset.sum_add_distrib]
  have hlo : (∑ i : Fin (n+1), (∑ j : Fin (n+1),
      (if i.val+1=j.val then edgeCoeff n i.val else 0) * u j.val) * u i.val) =
      ∑ i ∈ Finset.range n, edgeCoeff n i * u i * u (i+1) := by
    convert directed_neighbor_sum n u using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intros
    ring
  have hhi : (∑ i : Fin (n+1), (∑ j : Fin (n+1),
      (if j.val+1=i.val then edgeCoeff n j.val else 0) * u j.val) * u i.val) =
      ∑ i ∈ Finset.range n, edgeCoeff n i * u i * u (i+1) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact directed_neighbor_sum n u
  rw [hlo, hhi]
  ring

lemma pathOperator_tent_rayleigh {m n r : ℕ} (hm : 0 < m) (hfit : 4*m*r ≤ n)
    (c : Fin r → ℝ) :
    (2-(4/(m : ℝ)^2 + 2*(4*m*r+1 : ℝ)/(n+1))) * ‖tentMap m n r c‖^2 ≤
      inner ℝ (tentMap m n r c) (pathOperator n (tentMap m n r c)) := by
  have h := tentCombination_rayleigh hm hfit c
  rw [pathEnergy, tentMap_mass] at h
  change _ ≤ inner ℝ (WithLp.toLp 2 (fun i : Fin (n+1) => tentCombination m c i.val))
    (pathOperator n (WithLp.toLp 2 (fun i : Fin (n+1) => tentCombination m c i.val)))
  rw [pathOperator_inner]
  nlinarith

lemma pathOperator_eigenvalue_lower {m n r : ℕ} (hm : 0 < m) (hfit : 4*m*r ≤ n)
    (i : Fin (n+1)) (hi : i.val < r) :
    2-(4/(m : ℝ)^2 + 2*(4*m*r+1 : ℝ)/(n+1)) ≤
      (pathOperator_symmetric n).eigenvalues (by simp) i := by
  apply eigenvalue_lower_of_subspace (pathOperator_symmetric n) (by simp)
    (LinearMap.range (tentMap m n r)) i
  · rw [tentMap_rank hm hfit]
    exact hi
  · rintro x ⟨c, rfl⟩ hx
    have h := pathOperator_tent_rayleigh hm hfit c
    simpa only [hx, one_pow, mul_one] using h

end CriticalSK

end

end OAI
