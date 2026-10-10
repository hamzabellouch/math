import OAI.Combinatorics.MatchingEntropy.Calculus

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

open Matrix

variable {A : Type uA} {I : Type uI} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]

def weightedColumns (p : A → ℝ) (b : A → I → ℝ) : Matrix I A ℝ :=
  fun i a => Real.sqrt (p a) * b a i

def covariance (p : A → ℝ) (b : A → I → ℝ) : Matrix I I ℝ :=
  weightedColumns p b * (weightedColumns p b)ᵀ

omit [DecidableEq A] [DecidableEq I] in
theorem covariance_posSemidef (p : A → ℝ) (b : A → I → ℝ) :
    (covariance p b).PosSemidef := by
  simpa only [covariance, conjTranspose_eq_transpose_of_trivial] using
    posSemidef_self_mul_conjTranspose (weightedColumns p b)

omit [Fintype I] [DecidableEq A] [DecidableEq I] in
theorem covariance_entry {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ) (i j : I) :
    covariance p b i j = ∑ a, p a*b a i*b a j := by
  unfold covariance
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  simp only [weightedColumns, Matrix.transpose_apply]
  calc
    _ = (Real.sqrt (p a))^2 * b a i * b a j := by ring
    _ = _ := by rw [Real.sq_sqrt (hp a)]

omit [DecidableEq A] [DecidableEq I] in
theorem covariance_mulVec {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ)
    (u : I → ℝ) (i : I) :
    (covariance p b *ᵥ u) i = ∑ a, p a*b a i*(b a ⬝ᵥ u) := by
  simp only [Matrix.mulVec, dotProduct, covariance_entry hp, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq A] [DecidableEq I] in
theorem covariance_quadratic {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ)
    (u : I → ℝ) : u ⬝ᵥ (covariance p b *ᵥ u) = ∑ a, p a*(b a ⬝ᵥ u)^2 := by
  rw [dotProduct]
  simp_rw [covariance_mulVec hp, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  calc
    (∑ i, u i*(p a*b a i*(b a ⬝ᵥ u))) =
      (∑ i, b a i*u i)*(p a*(b a ⬝ᵥ u)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = p a*(b a ⬝ᵥ u)^2 := by rw [← dotProduct]; ring

def weightedDirectionSpace (p : A → ℝ) (b : A → I → ℝ) : Submodule ℝ (I → ℝ) :=
  Submodule.span ℝ (Set.range fun a : {a // 0 < p a} => b a.val)

omit [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I] in
theorem weightedColumns_span {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ) :
    Submodule.span ℝ (Set.range (weightedColumns p b).col) = weightedDirectionSpace p b := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    by_cases ha : 0 < p a
    · have hb : b a ∈ weightedDirectionSpace p b := Submodule.subset_span ⟨⟨a,ha⟩,rfl⟩
      exact Submodule.smul_mem _ (Real.sqrt (p a)) hb
    · have hz := le_antisymm (le_of_not_gt ha) (hp a)
      have he : (weightedColumns p b).col a = 0 := by
        ext i
        simp [weightedColumns, Matrix.col, hz]
      rw [he]
      exact (weightedDirectionSpace p b).zero_mem
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    have hb : (weightedColumns p b).col a.val ∈
        Submodule.span ℝ (Set.range (weightedColumns p b).col) := Submodule.subset_span ⟨a.val,rfl⟩
    have hs : Real.sqrt (p a.val) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 a.property)
    have hh := Submodule.smul_mem _ (Real.sqrt (p a.val))⁻¹ hb
    have he : (Real.sqrt (p a.val))⁻¹ • (weightedColumns p b).col a.val = b a.val := by
      ext i
      change (Real.sqrt (p a.val))⁻¹ * (Real.sqrt (p a.val) * b a.val i) = _
      rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
    rw [he] at hh
    exact hh

omit [DecidableEq A] [DecidableEq I] in
theorem covariance_rank {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ) :
    (covariance p b).rank = Module.finrank ℝ (weightedDirectionSpace p b) := by
  rw [covariance, rank_self_mul_transpose, rank_eq_finrank_span_cols, weightedColumns_span hp]

def normalizedCentered (v : A → I → ℝ) (x : I → ℝ) (a : A) (i : I) : ℝ :=
  (v a i-x i)/Real.sqrt (x i)

omit [Fintype I] [DecidableEq A] [DecidableEq I] in
theorem normalizedCentered_mean {p : A → ℝ} (hp : ∑ a, p a = 1)
    (v : A → I → ℝ) (x : I → ℝ) (hx : ∀ i, ∑ a, p a*v a i = x i) (i : I) :
    ∑ a, p a*normalizedCentered v x a i = 0 := by
  simp only [normalizedCentered, ← mul_div_assoc, mul_sub, ← Finset.sum_div,
    Finset.sum_sub_distrib, ← Finset.sum_mul, hp, one_mul, hx, sub_self, zero_div]

omit [Fintype I] [DecidableEq A] [DecidableEq I] in
theorem normalizedCentered_variance {p : A → ℝ} (hp : ∑ a, p a = 1)
    (v : A → I → ℝ) (hv : ∀ a i, (v a i)^2=v a i) (x : I → ℝ)
    (hx : ∀ i, ∑ a, p a*v a i = x i) (hxp : ∀ i, 0 < x i) (i : I) :
    ∑ a, p a*(normalizedCentered v x a i)^2 = 1-x i := by
  have heq : ∀ a, p a*(normalizedCentered v x a i)^2 =
      (p a*v a i-2*x i*(p a*v a i)+(x i)^2*p a)/x i := by
    intro a
    rw [normalizedCentered, div_pow, Real.sq_sqrt (hxp i).le, ← mul_div_assoc]
    congr 1
    calc
      _ = p a*(v a i)^2-2*x i*(p a*v a i)+(x i)^2*p a := by ring
      _ = _ := by rw [hv]
  simp_rw [heq]
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hx, hp, mul_one]
  field_simp [ne_of_gt (hxp i)]
  ring

omit [DecidableEq A] [DecidableEq I] in
theorem normalized_covariance_trace {p : A → ℝ} (hp : p ∈ probabilitySimplex A)
    (v : A → I → ℝ) (hv : ∀ a i, (v a i)^2=v a i) (x : I → ℝ)
    (hx : ∀ i, ∑ a, p a*v a i = x i) (hxp : ∀ i, 0 < x i) :
    (covariance p (normalizedCentered v x)).trace = Fintype.card I - ∑ i, x i := by
  unfold Matrix.trace Matrix.diag
  simp_rw [covariance_entry hp.1]
  have heq : ∀ i, (∑ a, p a*normalizedCentered v x a i*normalizedCentered v x a i) = 1-x i := by
    intro i
    simpa only [pow_two, mul_assoc] using
      normalizedCentered_variance hp.2 v hv x hx hxp i
  simp_rw [heq]
  simp

end MatchingEntropyBounds

end

end OAI
