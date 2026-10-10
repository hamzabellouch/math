import OAI.Combinatorics.PerfectMatching.Simplex

namespace OAI

/-!
Positive semidefinite covariance matrices, rank, trace, and a spectral inequality.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

open Matrix

variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]

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

/-- Spectral form of the second-variation step, using the full (possibly
singular) covariance rather than introducing an inverse on its image. -/
theorem covariance_rank_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {a : ℝ}
    (hsecond : ∀ u : ι → ℝ,
      (a - 1) * ((C *ᵥ u) ⬝ᵥ (C *ᵥ u)) + u ⬝ᵥ (C *ᵥ u) ≤ 0) :
    (C.rank : ℝ) ≤ (1-a) * C.trace := by
  let eig := hC.isHermitian.eigenvalues
  have heig : ∀ i, 0 ≤ eig i := hC.eigenvalues_nonneg
  have hone : ∀ i, eig i ≠ 0 → 1 ≤ (1-a) * eig i := by
    intro i hi
    let v : ι → ℝ := hC.isHermitian.eigenvectorBasis i
    have hv : v ⬝ᵥ v = 1 := by
      have hn := hC.isHermitian.eigenvectorBasis.orthonormal.1 i
      have hi : inner ℝ (hC.isHermitian.eigenvectorBasis i)
          (hC.isHermitian.eigenvectorBasis i) = 1 := by
        rw [real_inner_self_eq_norm_sq, hn]
        norm_num
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hi
    have he : C *ᵥ v = eig i • v := hC.isHermitian.mulVec_eigenvectorBasis i
    have hs := hsecond v
    rw [he] at hs
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, hv, mul_one] at hs
    have hp : 0 < eig i := lt_of_le_of_ne (heig i) (Ne.symm hi)
    nlinarith
  rw [hC.isHermitian.rank_eq_card_non_zero_eigs,
    hC.isHermitian.trace_eq_sum_eigenvalues]
  change (Fintype.card {i // eig i ≠ 0} : ℝ) ≤ (1-a) * ∑ i, eig i
  rw [Finset.mul_sum]
  calc
    _ = ∑ i : {i // eig i ≠ 0}, (1 : ℝ) := by simp
    _ ≤ ∑ i : {i // eig i ≠ 0}, (1-a) * eig i := Finset.sum_le_sum fun i _ => hone i i.property
    _ = ∑ i, (1-a) * eig i := by
      have hz : (∑ i : {i // ¬ eig i ≠ 0}, (1-a) * eig i) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [not_ne_iff.mp i.property, mul_zero]
      simpa only [hz, add_zero] using
        (Fintype.sum_subtype_add_sum_subtype (fun i => eig i ≠ 0)
          (fun i => (1-a) * eig i))

/-- The numerical contradiction following covariance rank and trace. -/
theorem covariance_contradiction {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {a m s : ℝ}
    (hm : 0 < m) (hs : 8*m < s) (hrank : s-4*m ≤ C.rank)
    (htrace : C.trace = s-m) (ha : 8*m/s ≤ a)
    (hsecond : ∀ u : ι → ℝ,
      (a-1) * ((C *ᵥ u) ⬝ᵥ (C *ᵥ u)) + u ⬝ᵥ (C *ᵥ u) ≤ 0) : False := by
  have hb := covariance_rank_bound hC hsecond
  rw [htrace] at hb
  have hsp : 0 < s := by linarith
  have hsmp : 0 < s-m := by linarith
  have hau : a ≤ 3*m/(s-m) := by
    apply (le_div_iff₀ hsmp).mpr
    nlinarith
  have hcross := (div_le_div_iff₀ hsp hsmp).mp (ha.trans hau)
  nlinarith [mul_pos hm (show 0 < 5*s-8*m by linarith)]

end MatchingEntropy

end

end OAI
