import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Nodal.NodalIntersection
import OAI.AlgebraicGeometry.Seshadri.Lattice.InitialWeights

namespace OAI

section
namespace MaximalSeshadri.NodalLocal
noncomputable section
open PowerSeries
open scoped BigOperators

def bivariateCoeff {K : Type*} [Field K] (f : Bivariate K) (e : Exponent) : K :=
  coeff e.1 (coeff e.2 f)

lemma bivariateCoeff_x {K : Type*} [Field K] (f : Bivariate K) (n : ℕ) :
    bivariateCoeff f (n, 0) = coeff n (restrictX K f) := by
  simp [bivariateCoeff, coeff_zero_eq_constantCoeff_apply]

lemma bivariateCoeff_z {K : Type*} [Field K] (f : Bivariate K) (n : ℕ) :
    bivariateCoeff f (0, n) = coeff n (restrictZ K f) := by
  simp [bivariateCoeff, coeff_zero_eq_constantCoeff_apply]

def bivariateCoeffEquiv : Bivariate ℂ ≃ₗ[ℂ] (Exponent → ℂ) where
  toFun := bivariateCoeff
  invFun c := PowerSeries.mk (fun n => PowerSeries.mk (fun k => c (k, n)))
  left_inv f := by
    apply PowerSeries.ext
    intro n
    apply PowerSeries.ext
    intro k
    simp [bivariateCoeff]
  right_inv c := by ext e; simp [bivariateCoeff]
  map_add' f g := by ext e; simp [bivariateCoeff]
  map_smul' a f := by ext e; simp [bivariateCoeff]

theorem nodal_initial_weight_bound (f : Bivariate ℂ) (t : ℝ) (ht : 0 < t)
    (e : Exponent) (he : LexInitial (bivariateCoeff f) t e)
    (hx : restrictX ℂ f ≠ 0) (hz : restrictZ ℂ f ≠ 0) :
    exponentWeight t e * (1 + 1 / t) ≤
      (Module.finrank ℂ (Bivariate ℂ ⧸ intersectionIdeal ℂ f) : ℝ) := by
  have hx' : bivariateCoeff f ((restrictX ℂ f).order.toNat, 0) ≠ 0 := by
    rw [bivariateCoeff_x]
    exact PowerSeries.coeff_order hx
  have hz' : bivariateCoeff f (0, (restrictZ ℂ f).order.toNat) ≠ 0 := by
    rw [bivariateCoeff_z]
    exact PowerSeries.coeff_order hz
  have ha := (he.2 _ hx').1
  have hb := (he.2 _ hz').1
  simp only [exponentWeight, Nat.cast_zero, mul_zero, add_zero, zero_add] at ha hb
  have hc : exponentWeight t e / t ≤ ((restrictZ ℂ f).order.toNat : ℝ) := by
    apply (div_le_iff₀ ht).mpr
    simpa [exponentWeight, mul_comm] using hb
  rw [nodal_intersection_colength ℂ f hx hz, Nat.cast_add]
  dsimp [exponentWeight] at hc ⊢
  have heq : ((e.1 : ℝ) + t * e.2) * (1 + 1 / t) =
      ((e.1 : ℝ) + t * e.2) + ((e.1 : ℝ) + t * e.2) / t := by ring
  rw [heq]
  exact add_le_add ha hc

theorem residual_initial_weight_bound (f : Bivariate ℂ) (d H t n : ℝ)
    (ht : 0 < t) (e : Exponent) (he : LexInitial (bivariateCoeff f) t e)
    (hx : restrictX ℂ f ≠ 0) (hz : restrictZ ℂ f ≠ 0)
    (hcolength : (Module.finrank ℂ (Bivariate ℂ ⧸ intersectionIdeal ℂ f) : ℝ)
      ≤ n * d * H) :
    exponentWeight t e ≤ n * (d * H * t / (1 + t)) := by
  have h := (nodal_initial_weight_bound f t ht e he hx hz).trans hcolength
  have hden : 0 < 1 + t := by positivity
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hden).mpr
  have hs : (1 + 1 / t) * t = 1 + t := by field_simp; ring
  calc
    exponentWeight t e * (1 + t) =
        (exponentWeight t e * (1 + 1 / t)) * t := by rw [mul_assoc, hs]
    _ ≤ (n * d * H) * t := mul_le_mul_of_nonneg_right h ht.le
    _ = n * (d * H * t) := by ring

lemma exponentWeight_add (t : ℝ) (p q : Exponent) :
    exponentWeight t (p + q) = exponentWeight t p + exponentWeight t q := by
  simp only [exponentWeight, Prod.fst_add, Prod.snd_add, Nat.cast_add]
  ring

lemma exponentWeight_pos (t : ℝ) (ht : 0 < t) (p : Exponent) (hp : p ≠ 0) :
    0 < exponentWeight t p := by
  by_cases hx : p.1 = 0
  · have hy : 0 < p.2 := by
      by_contra h
      apply hp
      exact Prod.ext hx (by change p.2 = 0; omega)
    simp only [exponentWeight, hx, Nat.cast_zero, zero_add]
    exact mul_pos ht (by exact_mod_cast hy)
  · have hx' : 0 < p.1 := Nat.pos_of_ne_zero hx
    exact add_pos_of_pos_of_nonneg (by exact_mod_cast hx')
      (mul_nonneg ht.le (Nat.cast_nonneg _))

lemma bivariateCoeff_mul (f g : Bivariate ℂ) (e : Exponent) :
    bivariateCoeff (f * g) e =
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal e.2, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal e.1,
        bivariateCoeff f (p.1, q.1) * bivariateCoeff g (p.2, q.2) := by
  simp only [bivariateCoeff, PowerSeries.coeff_mul, map_sum]

lemma bivariateCoeff_eq_zero_of_weight_lt (f : Bivariate ℂ) (t : ℝ)
    (e p : Exponent) (he : LexInitial (bivariateCoeff f) t e)
    (hp : exponentWeight t p < exponentWeight t e) : bivariateCoeff f p = 0 := by
  by_contra h
  exact (not_lt_of_ge (he.2 p h).1) hp

lemma bivariateCoeff_eq_zero_of_proper_subterm (f : Bivariate ℂ) (t : ℝ) (ht : 0 < t)
    (e p q v : Exponent) (he : LexInitial (bivariateCoeff f) t e)
    (hs : p + q = v) (hp : p ≠ 0)
    (hv : exponentWeight t v ≤ exponentWeight t e) : bivariateCoeff f q = 0 := by
  apply bivariateCoeff_eq_zero_of_weight_lt f t e q he
  have hsum := congrArg (exponentWeight t) hs
  rw [exponentWeight_add] at hsum
  have hpos := exponentWeight_pos t ht p hp
  linarith

lemma bivariateCoeff_mul_of_weight_le (u f : Bivariate ℂ) (t : ℝ) (ht : 0 < t)
    (e v : Exponent) (he : LexInitial (bivariateCoeff f) t e)
    (hv : exponentWeight t v ≤ exponentWeight t e) :
    bivariateCoeff (u * f) v = bivariateCoeff u (0, 0) * bivariateCoeff f v := by
  classical
  rw [bivariateCoeff_mul]
  rw [Finset.sum_eq_single (0, v.2)]
  · rw [Finset.sum_eq_single (0, v.1)]
    · intro p hp hpne
      apply mul_eq_zero_of_right
      apply bivariateCoeff_eq_zero_of_proper_subterm f t ht e (p.1, 0) (p.2, v.2) v he
      · apply Prod.ext
        · exact Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        · simp
      · intro h
        have hp1 : p.1 = 0 := congrArg Prod.fst h
        apply hpne
        apply Prod.ext hp1
        have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        omega
      · exact hv
    · intro h
      exact (h (by simp)).elim
  · intro q hq hqne
    apply Finset.sum_eq_zero
    intro p hp
    apply mul_eq_zero_of_right
    apply bivariateCoeff_eq_zero_of_proper_subterm f t ht e (p.1, q.1) (p.2, q.2) v he
    · exact Prod.ext (Finset.HasAntidiagonal.mem_antidiagonal.mp hp) (Finset.HasAntidiagonal.mem_antidiagonal.mp hq)
    · intro h
      have hq1 : q.1 = 0 := congrArg Prod.snd h
      apply hqne
      apply Prod.ext hq1
      have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
      omega
    · exact hv
  · intro h
    exact (h (by simp)).elim

theorem lexInitial_unit_mul (u f : Bivariate ℂ) (t : ℝ) (ht : 0 < t)
    (e : Exponent) (he : LexInitial (bivariateCoeff f) t e)
    (hu : bivariateCoeff u (0, 0) ≠ 0) :
    LexInitial (bivariateCoeff (u * f)) t e := by
  constructor
  · rw [bivariateCoeff_mul_of_weight_le u f t ht e e he le_rfl]
    exact mul_ne_zero hu he.1
  · intro v hv
    by_cases hle : exponentWeight t v ≤ exponentWeight t e
    · rw [bivariateCoeff_mul_of_weight_le u f t ht e v he hle] at hv
      exact he.2 v (right_ne_zero_of_mul hv)
    · exact ⟨(lt_of_not_ge hle).le, fun h => (hle h.symm.le).elim⟩

lemma bivariateCoeff_node_pow_mul (f : Bivariate ℂ) (j : ℕ) (v : Exponent) :
    bivariateCoeff (nodeEquation ℂ ^ j * f) v =
      if j ≤ v.1 ∧ j ≤ v.2 then bivariateCoeff f (v.1 - j, v.2 - j) else 0 := by
  have heq : nodeEquation ℂ ^ j * f =
      C ((X : PowerSeries ℂ) ^ j) * ((X : Bivariate ℂ) ^ j * f) := by
    rw [nodeEquation, mul_pow, ← map_pow, mul_assoc]
  rw [heq]
  simp only [bivariateCoeff, coeff_C_mul, coeff_X_pow_mul']
  by_cases hx : j ≤ v.1 <;> by_cases hz : j ≤ v.2 <;>
    simp [hx, hz]

lemma bivariateCoeff_node_pow_mul_add (f : Bivariate ℂ) (j : ℕ) (e : Exponent) :
    bivariateCoeff (nodeEquation ℂ ^ j * f) (e + (j, j)) = bivariateCoeff f e := by
  simp [bivariateCoeff_node_pow_mul]

theorem lexInitial_node_pow_mul (f : Bivariate ℂ) (j : ℕ) (t : ℝ)
    (e : Exponent) (he : LexInitial (bivariateCoeff f) t e) :
    LexInitial (bivariateCoeff (nodeEquation ℂ ^ j * f)) t (e + (j, j)) := by
  constructor
  · rw [bivariateCoeff_node_pow_mul_add]
    exact he.1
  · intro p hp
    have hpp : j ≤ p.1 ∧ j ≤ p.2 := by
      by_contra h
      rw [bivariateCoeff_node_pow_mul, ite_eq_right h] at hp
      exact hp rfl
    let q : Exponent := (p.1 - j, p.2 - j)
    have heqp : p = q + (j, j) := by
      apply Prod.ext <;> dsimp [q] <;> omega
    have hq : bivariateCoeff f q ≠ 0 := by
      simpa only [bivariateCoeff_node_pow_mul, ite_eq_left hpp] using hp
    obtain ⟨hw, hb⟩ := he.2 q hq
    constructor
    · rw [heqp, exponentWeight_add, exponentWeight_add]
      linarith
    · intro h
      rw [heqp, exponentWeight_add, exponentWeight_add] at h
      have hb' := hb (add_right_cancel h)
      simpa only [heqp, Prod.snd_add] using Nat.add_le_add_right hb' j

theorem lexInitial_nodal_factor (u f : Bivariate ℂ) (j : ℕ) (t : ℝ) (ht : 0 < t)
    (e : Exponent) (he : LexInitial (bivariateCoeff f) t e)
    (hu : bivariateCoeff u (0, 0) ≠ 0) :
    LexInitial (bivariateCoeff ((u * nodeEquation ℂ) ^ j * f)) t (e + (j, j)) := by
  have huj : bivariateCoeff (u ^ j) (0, 0) ≠ 0 := by
    simpa only [bivariateCoeff, coeff_zero_eq_constantCoeff_apply, map_pow] using
      pow_ne_zero j hu
  have hh := lexInitial_unit_mul (u ^ j) (nodeEquation ℂ ^ j * f) t ht (e + (j, j))
    (lexInitial_node_pow_mul f j t e he) huj
  simpa only [mul_pow, mul_assoc] using hh

end
end MaximalSeshadri.NodalLocal

namespace MaximalSeshadri
noncomputable section
open scoped BigOperators

def nodeQuadrilateral (a b c : ℝ) : Set (ℝ × ℝ) :=
  convexHull ℝ {(0, 0), (a, 0), (c, c), (0, b)}

theorem mem_nodeQuadrilateral_of_residual (a b c k x y j : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hk : 0 < k)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hj : 0 ≤ j)
    (h : x / a + y / b + j / c ≤ k) :
    (x + j, y + j) ∈ nodeQuadrilateral (k * a) (k * b) (k * c) := by
  let w : Fin 4 → ℝ := ![1 - (x / a + y / b + j / c) / k,
    x / (k * a), j / (k * c), y / (k * b)]
  let z : Fin 4 → ℝ × ℝ := ![(0, 0), (k * a, 0), (k * c, k * c), (0, k * b)]
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin 4)), 0 ≤ w i := by
    intro i _
    fin_cases i
    · dsimp [w]
      have hh := (div_le_one hk).mpr h
      linarith
    · exact div_nonneg hx (mul_pos hk ha).le
    · exact div_nonneg hj (mul_pos hk hc).le
    · exact div_nonneg hy (mul_pos hk hb).le
  have hsum : ∑ i : Fin 4, w i = 1 := by
    simp only [Fin.sum_univ_four]
    dsimp [w]
    field_simp
    ring
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin 4)), z i ∈
      nodeQuadrilateral (k * a) (k * b) (k * c) := by
    intro i _
    apply subset_convexHull ℝ _
    fin_cases i <;> simp [z]
  have hm := (convex_convexHull ℝ _).sum_mem hw hsum hz
  have heq : ∑ i : Fin 4, w i • z i = (x + j, y + j) := by
    simp only [Fin.sum_univ_four]
    apply Prod.ext <;> dsimp [w, z] <;> field_simp <;> ring
  rwa [heq] at hm

namespace NodalLocal

theorem nodal_factor_quadrilateral (u f : Bivariate ℂ) (j : ℕ)
    (d H t k n : ℝ) (hd : 0 < d) (hH : 0 < H) (ht : 0 < t) (hk : 0 < k)
    (e : Exponent) (he : LexInitial (bivariateCoeff f) t e)
    (hu : bivariateCoeff u (0, 0) ≠ 0)
    (hx : restrictX ℂ f ≠ 0) (hz : restrictZ ℂ f ≠ 0)
    (hcolength : (Module.finrank ℂ (Bivariate ℂ ⧸ intersectionIdeal ℂ f) : ℝ)
      ≤ n * d * H) (hdegree : n + (j : ℝ) * d = k) :
    ∀ p, LexInitial (bivariateCoeff ((u * nodeEquation ℂ) ^ j * f)) t p →
      ((p.1 : ℝ), (p.2 : ℝ)) ∈ nodeQuadrilateral
        (k * (d * H * t / (1 + t))) (k * (d * H / (1 + t))) (k / d) := by
  intro p hp
  have hpe := hp.unique (lexInitial_nodal_factor u f j t ht e he hu)
  subst p
  have hweight := residual_initial_weight_bound f d H t n ht e he hx hz hcolength
  have hden : 0 < 1 + t := by positivity
  have ha : 0 < d * H * t / (1 + t) := by positivity
  have hb : 0 < d * H / (1 + t) := by positivity
  have hres : (e.1 : ℝ) / (d * H * t / (1 + t)) +
      (e.2 : ℝ) / (d * H / (1 + t)) ≤ n := by
    have heq : (e.1 : ℝ) / (d * H * t / (1 + t)) +
        (e.2 : ℝ) / (d * H / (1 + t)) =
        exponentWeight t e / (d * H * t / (1 + t)) := by
      dsimp [exponentWeight]
      field_simp
    rw [heq]
    exact (div_le_iff₀ ha).mpr hweight
  have hh : (e.1 : ℝ) / (d * H * t / (1 + t)) +
      (e.2 : ℝ) / (d * H / (1 + t)) + (j : ℝ) / (1 / d) ≤ k := by
    simp only [div_div_eq_mul_div, div_one]
    linarith
  have hm := mem_nodeQuadrilateral_of_residual
    (d * H * t / (1 + t)) (d * H / (1 + t)) (1 / d) k e.1 e.2 j
    ha hb (by positivity) hk (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hh
  simpa only [Prod.fst_add, Prod.snd_add, Nat.cast_add, mul_one_div] using hm

end NodalLocal
end
end MaximalSeshadri

end


end OAI
