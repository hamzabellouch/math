import OAI.Analysis.FactorGeneration.Subfactors

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Quantitative descent for a finite spectral pinching, and actual unitary
displacement from irreducibility. A compatible spectral partition in a
residual corner is not postulated as a local-quantization theorem. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-- Irreducibility supplies displacement for every nonzero centered operator,
without any orthogonality-to-P premise. -/
theorem exists_centered_unitary_displacement
    (P : StarSubalgebra ℂ M.toStarSubalgebra) [CompleteSpace P]
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : P, (a : M.toStarSubalgebra)*c = c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ, c = z • (1 : M.toStarSubalgebra))
    (x : M.toStarSubalgebra) (hx : x ≠ 0) (ht : τ.trace x = 0)
    (r : ℝ) (hr : r < 1) :
    ∃ u : subalgebraUnitaries P, r*τ.norm₂ x < τ.norm₂ (conjugateLinear u.val x-x) := by
  by_contra hn
  push Not at hn
  have h := trace_distance_le_unitary_displacement τ P hirr x (r*τ.norm₂ x) hn
  rw [ht, zero_smul, sub_zero] at h
  have hxpos : 0 < τ.norm₂ x := lt_of_le_of_ne (norm_nonneg _)
    (fun hz => hx ((τ.norm₂_eq_zero_iff x).mp hz.symm))
  nlinarith

/-- The strict displacement used before finite spectral approximation in
Popa A.1.1, Step 1, in the scalar-commutant case. -/
theorem exists_strict_centered_displacement
    (P : StarSubalgebra ℂ M.toStarSubalgebra) [CompleteSpace P]
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : P, (a : M.toStarSubalgebra)*c = c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ, c = z • (1 : M.toStarSubalgebra))
    (x : M.toStarSubalgebra) (hx : x ≠ 0) (ht : τ.trace x = 0) :
    ∃ u : subalgebraUnitaries P, τ.norm₂ x < τ.norm₂ (conjugateLinear u.val x-x) := by
  by_contra hn
  push Not at hn
  let K : Set H := {ξ | τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) ξ).re}
  have hclosed : IsClosed K := isClosed_le continuous_const
    (Complex.continuous_re.comp (continuous_const.inner continuous_id))
  have hconv : Convex ℝ K := by
    intro ξ hξ η hη s t hs ht' hst
    change τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) (s • ξ+t • η)).re
    simp only [inner_add_right, inner_smul_right_eq_smul, Complex.add_re, Complex.smul_re,
      smul_eq_mul]
    change τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) ξ).re at hξ
    change τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) η).re at hη
    nlinarith [mul_le_mul_of_nonneg_left hξ hs, mul_le_mul_of_nonneg_left hη ht']
  have horbit : baseVector τ '' algebraOrbit (subalgebraUnitaries P) x ⊆ K := by
    rintro ξ ⟨a,⟨u,rfl⟩,rfl⟩
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (hn u) 2
    change τ.norm₂ (conjugateLinear u.val x-x)^2 ≤ τ.norm₂ x^2 at hsq
    have hid := norm_sub_sq (𝕜 := ℂ) (baseVector τ (conjugateLinear u.val x)) (baseVector τ x)
    change τ.norm₂ (conjugateLinear u.val x-x)^2 = τ.norm₂ (conjugateLinear u.val x)^2 -
      2*(inner ℂ (baseVector τ (conjugateLinear u.val x)) (baseVector τ x)).re + τ.norm₂ x^2 at hid
    rw [conjugate_norm₂] at hid
    have hisym : (inner ℂ (baseVector τ (conjugateLinear u.val x)) (baseVector τ x)).re =
        (inner ℂ (baseVector τ x) (baseVector τ (conjugateLinear u.val x))).re :=
      inner_re_symm (𝕜 := ℂ) _ _
    rw [hisym] at hid
    change τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) (baseVector τ (conjugateLinear u.val x))).re
    linarith
  have hz : (0 : H) ∈ traceOrbitHull τ (subalgebraUnitaries P) x := by
    simpa only [ht, zero_smul, map_zero] using scalar_mem_traceOrbitHull τ P hirr x
  have hzero := (closure_minimal (convexHull_min horbit hconv) hclosed) hz
  change τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) 0).re at hzero
  rw [inner_zero_right, Complex.zero_re] at hzero
  have hpos : 0 < τ.norm₂ x^2 := sq_pos_of_ne_zero (fun he => hx ((τ.norm₂_eq_zero_iff x).mp he))
  linarith

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

theorem pinch_commutes_diagonal (u : M.toStarSubalgebra) (c : Fin Q.size → ℂ)
    (hl : ∀ i, u*(Q.piece i).val = c i • (Q.piece i).val)
    (hr : ∀ i, (Q.piece i).val*u = c i • (Q.piece i).val) (x : M.toStarSubalgebra) :
    u*Q.pinch x = Q.pinch x*u := by
  simp only [pinch, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [← mul_assoc, hl]
  simp only [mul_assoc, hr, smul_mul_assoc, mul_smul_comm]

theorem pinch_fixed_of_commutes (u : unitary M.toStarSubalgebra) (x : M.toStarSubalgebra)
    (h : (u : M.toStarSubalgebra)*Q.pinch x = Q.pinch x*(u : M.toStarSubalgebra)) :
    conjugateLinear u (Q.pinch x) = Q.pinch x := by
  change (u : M.toStarSubalgebra)*Q.pinch x*star (u : M.toStarSubalgebra) = _
  rw [h, mul_assoc, u.property.2, mul_one]

theorem displacement_le_twice_residual (u : unitary M.toStarSubalgebra)
    (x : M.toStarSubalgebra) (hfixed : conjugateLinear u (Q.pinch x) = Q.pinch x) :
    τ.norm₂ (conjugateLinear u x-x) ≤ 2*τ.norm₂ (x-Q.pinch x) := by
  have he : conjugateLinear u x-x =
      conjugateLinear u (x-Q.pinch x)-(x-Q.pinch x) := by
    rw [map_sub,hfixed]
    abel
  rw [he]
  have h := norm_sub_le (baseVector τ (conjugateLinear u (x-Q.pinch x)))
    (baseVector τ (x-Q.pinch x))
  change τ.norm₂ (conjugateLinear u (x-Q.pinch x)-(x-Q.pinch x)) ≤
    τ.norm₂ (conjugateLinear u (x-Q.pinch x)) + τ.norm₂ (x-Q.pinch x) at h
  rw [conjugate_norm₂] at h
  linarith

/-- The exact squared displacement bound behind the partition descent. -/
theorem displacement_energy_bound (u : unitary M.toStarSubalgebra)
    (x : M.toStarSubalgebra) (hfixed : conjugateLinear u (Q.pinch x) = Q.pinch x) :
    τ.norm₂ (conjugateLinear u x-x)^2 ≤ 4*(τ.norm₂ x^2-τ.norm₂ (Q.pinch x)^2) := by
  have h := Q.displacement_le_twice_residual τ u x hfixed
  have hp := Q.pinch_pythagoras τ x
  nlinarith [show 0 ≤ τ.norm₂ (conjugateLinear u x-x) from norm_nonneg _,
    show 0 ≤ τ.norm₂ (x-Q.pinch x) from norm_nonneg _]

/-- The factor 3/4 in Popa A.1.1, Step 2, for the actual finite spectral
pinching and its displayed displacement estimate. -/
theorem three_quarters_energy (u : unitary M.toStarSubalgebra)
    (x : M.toStarSubalgebra) (hfixed : conjugateLinear u (Q.pinch x) = Q.pinch x)
    (hdisplace : τ.norm₂ x ≤ τ.norm₂ (conjugateLinear u x-x)) :
    (∑ i, τ.norm₂ ((Q.piece i).val*x*(Q.piece i).val)^2) ≤ (3/4 : ℝ)*τ.norm₂ x^2 := by
  rw [← Q.pinch_energy τ]
  have h := Q.displacement_energy_bound τ u x hfixed
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hdisplace 2
  change τ.norm₂ x^2 ≤ τ.norm₂ (conjugateLinear u x-x)^2 at hsq
  nlinarith

/-! Finite spectral approximation yields an actual energy-decreasing partition.
The displacement premise is explicit; no small-energy partition is assumed. -/

theorem spectral_sum_commutes_pinch (c : Fin Q.size → ℂ) (x : M.toStarSubalgebra) :
    projectionSum Q.piece c * Q.pinch x = Q.pinch x * projectionSum Q.piece c := by
  simp only [projectionSum, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, Q.pinch_left, Q.pinch_right]

theorem commutator_le_residual (v x : M.toStarSubalgebra)
    (hc : v*Q.pinch x=Q.pinch x*v) :
    τ.norm₂ (v*x-x*v) ≤ 2*‖v‖*τ.norm₂ (x-Q.pinch x) := by
  have he : v*x-x*v=v*(x-Q.pinch x)-(x-Q.pinch x)*v := by
    simp only [mul_sub,sub_mul]
    rw [hc]
    abel
  rw [he]
  have h := norm_sub_le (baseVector τ (v*(x-Q.pinch x)))
    (baseVector τ ((x-Q.pinch x)*v))
  change τ.norm₂ (v*(x-Q.pinch x)-(x-Q.pinch x)*v) ≤
    τ.norm₂ (v*(x-Q.pinch x))+τ.norm₂ ((x-Q.pinch x)*v) at h
  have hl := τ.norm₂_mul_le v (x-Q.pinch x)
  have hr := τ.norm₂_mul_le_right (x-Q.pinch x) v
  nlinarith

end CornerPartition

theorem commutator_perturbation (u v x : M.toStarSubalgebra) :
    τ.norm₂ (u*x-x*u) ≤ τ.norm₂ (v*x-x*v)+2*‖u-v‖*τ.norm₂ x := by
  have he : u*x-x*u=(v*x-x*v)+((u-v)*x-x*(u-v)) := by noncomm_ring
  rw [he]
  have h := τ.norm₂_add_le (v*x-x*v) ((u-v)*x-x*(u-v))
  have h' := norm_sub_le (baseVector τ ((u-v)*x)) (baseVector τ (x*(u-v)))
  change τ.norm₂ ((u-v)*x-x*(u-v)) ≤ τ.norm₂ ((u-v)*x)+τ.norm₂ (x*(u-v)) at h'
  have hl := τ.norm₂_mul_le (u-v) x
  have hr := τ.norm₂_mul_le_right x (u-v)
  nlinarith

theorem displacement_le_commutator (u : unitary M.toStarSubalgebra)
    (x : M.toStarSubalgebra) :
    τ.norm₂ (conjugateLinear u x-x) ≤ τ.norm₂ ((u : M.toStarSubalgebra)*x-x*(u : M.toStarSubalgebra)) := by
  have he : conjugateLinear u x-x=
      ((u : M.toStarSubalgebra)*x-x*(u : M.toStarSubalgebra))*star (u : M.toStarSubalgebra) := by
    change (u : M.toStarSubalgebra)*x*star (u : M.toStarSubalgebra)-x=_
    rw [sub_mul,mul_assoc x,u.property.2,mul_one]
  rw [he]
  exact (τ.norm₂_mul_le_right _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _)
      (unitary_norm_le _ (by simp)))

/-- Energy decrease from a spectral approximation, with the actual
partition and approximation error exposed. -/
theorem CornerPartition.energy_descent_of_spectral_approximation
    {p : AlgebraProjection M} (Q : CornerPartition p)
    (u : unitary M.toStarSubalgebra) (x : M.toStarSubalgebra) (c : Fin Q.size → ℂ)
    (hd : τ.norm₂ x ≤ τ.norm₂ (conjugateLinear u x-x))
    (hclose : ‖(u : M.toStarSubalgebra)-∑ i,c i • (Q.piece i).val‖ < 1/4) :
    (∑ i,τ.norm₂ ((Q.piece i).val*x*(Q.piece i).val)^2) ≤
      (63/64 : ℝ)*τ.norm₂ x^2 := by
  let v := projectionSum Q.piece c
  change ‖(u : M.toStarSubalgebra)-v‖ < 1/4 at hclose
  have hv : ‖v‖ ≤ 2 := by
    have h := norm_sub_le (u : M.toStarSubalgebra) ((u : M.toStarSubalgebra)-v)
    rw [sub_sub_cancel] at h
    have hu := unitary_norm_le (u : M.toStarSubalgebra) (by simp)
    linarith
  have he := Q.commutator_le_residual τ v x (Q.spectral_sum_commutes_pinch c x)
  have hp := commutator_perturbation τ (u : M.toStarSubalgebra) v x
  have hd' := displacement_le_commutator τ u x
  have hn : 0 ≤ τ.norm₂ x := norm_nonneg _
  have hr : 0 ≤ τ.norm₂ (x-Q.pinch x) := norm_nonneg _
  have hres : τ.norm₂ x/8 ≤ τ.norm₂ (x-Q.pinch x) := by
    have hv' := mul_le_mul_of_nonneg_right hv hr
    have hc' := mul_le_mul_of_nonneg_right hclose.le hn
    nlinarith
  rw [← Q.pinch_energy τ]
  have hpy := Q.pinch_pythagoras τ x
  nlinarith [sq_nonneg (τ.norm₂ (x-Q.pinch x)-τ.norm₂ x/8)]

/-- A displaced operator has a genuinely constructed finite partition with
energy at most 63/64 of its original energy. This is one step, not iteration. -/
theorem exists_partition_energy_descent (u : unitary M.toStarSubalgebra)
    (x : M.toStarSubalgebra)
    (hd : τ.norm₂ x ≤ τ.norm₂ (conjugateLinear u x-x)) :
    ∃ Q : CornerPartition (identityProjection M),
      (∑ i, τ.norm₂ ((Q.piece i).val*x*(Q.piece i).val)^2) ≤
        (63/64 : ℝ)*τ.norm₂ x^2 := by
  obtain ⟨Q,c,hclose⟩ := exists_unitary_spectral_approximation u (1/4) (by norm_num)
  exact ⟨Q,Q.energy_descent_of_spectral_approximation τ u x c hd hclose⟩

end

/-! The one-step energy decrease has pieces in the prescribed von Neumann
subalgebra. Irreducibility supplies the unitary, not an assumed energy budget. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_subalgebra_partition_energy_descent (h : N ≤ M)
    (u : unitary M.toStarSubalgebra) (hu : (u : M.toStarSubalgebra).val ∈ N)
    (x : M.toStarSubalgebra) (hd : τ.norm₂ x ≤ τ.norm₂ (conjugateLinear u x-x)) :
    ∃ Q : CornerPartition (identityProjection M),
      (∀ i,(Q.piece i).val.val ∈ N) ∧
      (∑ i,τ.norm₂ ((Q.piece i).val*x*(Q.piece i).val)^2) ≤
        (63/64 : ℝ)*τ.norm₂ x^2 := by
  obtain ⟨Q,c,hQ,hc⟩ := exists_unitary_subalgebra_spectral_approximation h u hu (1/4) (by norm_num)
  exact ⟨Q,hQ,Q.energy_descent_of_spectral_approximation τ u x c hd hc⟩

/-- One actual finite partition decreases every given nonzero centered
operator's energy. This does not assert an arbitrary target budget or permit
iteration through uncentered residual blocks. -/
theorem exists_irreducible_partition_energy_descent (h : N ≤ M)
    (P : StarSubalgebra ℂ M.toStarSubalgebra) [CompleteSpace P]
    (hP : ∀ a : M.toStarSubalgebra,a ∈ P ↔ a.val ∈ N)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : P,(a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (x : M.toStarSubalgebra) (hx : x ≠ 0) (ht : τ.trace x=0) :
    ∃ Q : CornerPartition (identityProjection M),
      (∀ i,(Q.piece i).val ∈ P) ∧
      (∑ i,τ.norm₂ ((Q.piece i).val*x*(Q.piece i).val)^2) < τ.norm₂ x^2 := by
  obtain ⟨u,hu⟩ := exists_strict_centered_displacement τ P hirr x hx ht
  obtain ⟨Q,hQ,he⟩ := exists_subalgebra_partition_energy_descent τ h u.val
    ((hP _).mp u.property) x hu.le
  refine ⟨Q,fun i => (hP _).mpr (hQ i),?_⟩
  have hp : 0 < τ.norm₂ x^2 := sq_pos_of_ne_zero
    (fun hz => hx ((τ.norm₂_eq_zero_iff x).mp hz))
  linarith

end

/-! Strict displacement from zero in the actual closed convex orbit hull,
without imposing a scalar commutant on a block diagonal algebra. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_strict_displacement_of_zero_orbitHull
    (G : Subgroup (unitary M.toStarSubalgebra))
    (x : M.toStarSubalgebra) (hx : x ≠ 0)
    (hzero : (0 : H) ∈ traceOrbitHull τ G x) :
    ∃ u : G, τ.norm₂ x < τ.norm₂ (conjugateLinear u.val x-x) := by
  by_contra hn
  push Not at hn
  let K : Set H := {ξ | τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) ξ).re}
  have hclosed : IsClosed K := isClosed_le continuous_const
    (Complex.continuous_re.comp (continuous_const.inner continuous_id))
  have hconv : Convex ℝ K := by
    intro ξ hξ η hη s t hs ht' hst
    change τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) (s • ξ+t • η)).re
    simp only [inner_add_right, inner_smul_right_eq_smul, Complex.add_re, Complex.smul_re,
      smul_eq_mul]
    change τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) ξ).re at hξ
    change τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) η).re at hη
    nlinarith [mul_le_mul_of_nonneg_left hξ hs, mul_le_mul_of_nonneg_left hη ht']
  have horbit : baseVector τ '' algebraOrbit G x ⊆ K := by
    rintro ξ ⟨a,⟨u,rfl⟩,rfl⟩
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (hn u) 2
    change τ.norm₂ (conjugateLinear u.val x-x)^2 ≤ τ.norm₂ x^2 at hsq
    have hid := norm_sub_sq (𝕜 := ℂ) (baseVector τ (conjugateLinear u.val x)) (baseVector τ x)
    change τ.norm₂ (conjugateLinear u.val x-x)^2 = τ.norm₂ (conjugateLinear u.val x)^2 -
      2*(inner ℂ (baseVector τ (conjugateLinear u.val x)) (baseVector τ x)).re + τ.norm₂ x^2 at hid
    rw [conjugate_norm₂] at hid
    have hisym : (inner ℂ (baseVector τ (conjugateLinear u.val x)) (baseVector τ x)).re =
        (inner ℂ (baseVector τ x) (baseVector τ (conjugateLinear u.val x))).re :=
      inner_re_symm (𝕜 := ℂ) _ _
    rw [hisym] at hid
    change τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) (baseVector τ (conjugateLinear u.val x))).re
    linarith
  have hzero := (closure_minimal (convexHull_min horbit hconv) hclosed) hzero
  change τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) 0).re at hzero
  rw [inner_zero_right, Complex.zero_re] at hzero
  have hpos : 0 < τ.norm₂ x^2 := sq_pos_of_ne_zero (fun he => hx ((τ.norm₂_eq_zero_iff x).mp he))
  linarith

end

/-! Actual compatible 63/64 descent for the orthogonal component of Popa
A.1.1 in an irreducible inclusion. Both displacement and finite spectral
partitions are constructed, and all pieces remain in the prescribed N. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
namespace CornerPartition
variable (Q : CornerPartition (identityProjection M))

theorem exists_compatible_orthogonal_descent (hNM : N ≤ M)
    (hN : ∀ i,(Q.piece i).val.val ∈ N)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : insideAlgebra (M := M) (P := N),
        (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (x : M.toStarSubalgebra) (hx : TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) x) :
    ∃ R : CornerPartition (identityProjection M), Q.Refines R ∧
      (∀ i,(R.piece i).val.val ∈ N) ∧
      τ.norm₂ (R.pinch x)^2 ≤ (63/64 : ℝ)*τ.norm₂ (Q.pinch x)^2 := by
  by_cases hz : Q.pinch x=0
  · refine ⟨Q,Q.refines_refl,hN,?_⟩
    rw [hz]
    change ‖(0 : H)‖^2 ≤ (63/64 : ℝ)*‖(0 : H)‖^2
    simp
  let B := Q.blockVonNeumann N
  let P := insideAlgebra (M := M) (P := N)
  let D := insideAlgebra (M := M) (P := B)
  have hDP : ∀ a : M.toStarSubalgebra,a ∈ D → a ∈ P :=
    fun a ha => (Q.blockVonNeumann_le N) ha
  have hzero : (0 : H) ∈ traceOrbitHull τ (subalgebraUnitaries D) (Q.pinch x) := by
    apply zero_mem_orbitHull_of_orthogonal τ P (subalgebraUnitaries D)
      (fun u => hDP _ u.property)
    · intro c hc
      exact Q.block_commutant_mem_subalgebra τ hN hirr c
        (commutes_of_fixed_unitaries D c hc)
    · exact hx.pinch τ Q hN
  obtain ⟨u,hu⟩ := exists_strict_displacement_of_zero_orbitHull τ
    (subalgebraUnitaries D) (Q.pinch x) hz hzero
  obtain ⟨S,hS,he⟩ := exists_subalgebra_partition_energy_descent τ
    ((Q.blockVonNeumann_le N).trans hNM) u.val u.property (Q.pinch x) hu.le
  have hcross (i : Fin Q.size) (j : Fin S.size) :
      Commute (Q.piece i).val (S.piece j).val :=
    ((Q.blockVonNeumann_mem_iff N _).mp (hS j)).2 i
  let R := Q.joint S hcross
  have hQR : Q.Refines R := Q.joint_refines_left S hcross
  have hSR : S.Refines R := Q.joint_refines_right S hcross
  refine ⟨R,hQR,?_,?_⟩
  · intro i
    let a := (Fintype.equivFin (Fin Q.size × Fin S.size)).symm i
    change ((Q.piece a.1).val*(S.piece a.2).val).val ∈ N
    exact N.mul_mem (hN a.1) ((Q.blockVonNeumann_le N) (hS a.2))
  · have hh := S.refinement_energy_le τ R hSR (Q.pinch x)
    rw [← R.pinch_energy τ,← S.pinch_energy τ,Q.pinch_refinement R hQR] at hh
    rw [← S.pinch_energy τ] at he
    exact hh.trans he

end CornerPartition

end

/-! Geometric iteration and finite-family small-energy partitions for the
orthogonal component. No energy budget or block displacement is assumed. -/
section
open scoped BigOperators Topology
open Filter
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
namespace CornerPartition
variable (hNM : N ≤ M)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : insideAlgebra (M := M) (P := N),
    (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
include hNM hirr

theorem exists_orthogonal_geometric_refinement
    (Q : CornerPartition (identityProjection M))
    (hN : ∀ i,(Q.piece i).val.val ∈ N)
    (x : M.toStarSubalgebra) (hx : TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) x)
    (n : ℕ) :
    ∃ R : CornerPartition (identityProjection M), Q.Refines R ∧
      (∀ i,(R.piece i).val.val ∈ N) ∧
      τ.norm₂ (R.pinch x)^2 ≤ (63/64 : ℝ)^n*τ.norm₂ (Q.pinch x)^2 := by
  induction n with
  | zero => exact ⟨Q,Q.refines_refl,hN,by simp⟩
  | succ n ih =>
    obtain ⟨R,hQR,hR,hE⟩ := ih
    obtain ⟨S,hRS,hS,hSenergy⟩ := R.exists_compatible_orthogonal_descent τ hNM hR hirr x hx
    refine ⟨S,Q.refines_trans hQR hRS,hS,?_⟩
    calc τ.norm₂ (S.pinch x)^2 ≤ (63/64 : ℝ)*τ.norm₂ (R.pinch x)^2 := hSenergy
      _ ≤ (63/64 : ℝ)*((63/64 : ℝ)^n*τ.norm₂ (Q.pinch x)^2) :=
        mul_le_mul_of_nonneg_left hE (by norm_num)
      _ = (63/64 : ℝ)^(n+1)*τ.norm₂ (Q.pinch x)^2 := by ring

theorem exists_orthogonal_refinement_budget
    (Q : CornerPartition (identityProjection M))
    (hN : ∀ i,(Q.piece i).val.val ∈ N)
    (x : M.toStarSubalgebra) (hx : TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) x)
    (b : ℝ) (hb : 0 < b) :
    ∃ R : CornerPartition (identityProjection M), Q.Refines R ∧
      (∀ i,(R.piece i).val.val ∈ N) ∧ τ.norm₂ (R.pinch x)^2 < b := by
  have ht : Tendsto (fun n : ℕ => (63/64 : ℝ)^n*τ.norm₂ (Q.pinch x)^2) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 63/64)
        (by norm_num : (63/64 : ℝ) < 1)).mul_const (τ.norm₂ (Q.pinch x)^2)
  obtain ⟨n,hn⟩ := (ht.eventually (Iio_mem_nhds hb)).exists
  obtain ⟨R,hQR,hR,hE⟩ := exists_orthogonal_geometric_refinement τ hNM hirr Q hN x hx n
  exact ⟨R,hQR,hR,hE.trans_lt hn⟩

/-- One actual finite compatible partition gives an arbitrarily small SUM
of energies for the whole finite orthogonal family. -/
theorem exists_finite_orthogonal_refinement_budget
    (Q : CornerPartition (identityProjection M))
    (hN : ∀ i,(Q.piece i).val.val ∈ N)
    (F : Finset M.toStarSubalgebra)
    (hF : ∀ x ∈ F,TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) x)
    (b : ℝ) (hb : 0 < b) :
    ∃ R : CornerPartition (identityProjection M), Q.Refines R ∧
      (∀ i,(R.piece i).val.val ∈ N) ∧ (∑ x ∈ F,τ.norm₂ (R.pinch x)^2) < b := by
  classical
  induction F using Finset.induction_on generalizing Q b with
  | empty => exact ⟨Q,Q.refines_refl,hN,by simpa using hb⟩
  | @insert x F hxF ih =>
    obtain ⟨R,hQR,hR,hx⟩ := exists_orthogonal_refinement_budget τ hNM hirr Q hN x
      (hF x (Finset.mem_insert_self x F)) (b/2) (half_pos hb)
    obtain ⟨S,hRS,hS,hFS⟩ := ih R hR
      (fun y hy => hF y (Finset.mem_insert_of_mem hy)) (b/2) (half_pos hb)
    refine ⟨S,Q.refines_trans hQR hRS,hS,?_⟩
    have hxS := R.refinement_energy_le τ S hRS x
    rw [← R.pinch_energy τ,← S.pinch_energy τ] at hxS
    rw [Finset.sum_insert hxF]
    linarith

theorem exists_indexed_orthogonal_refinement_budget
    (Q : CornerPartition (identityProjection M))
    (hN : ∀ i,(Q.piece i).val.val ∈ N)
    {ι : Type*} (F : Finset ι) (v : ι → M.toStarSubalgebra)
    (hF : ∀ x ∈ F,TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (v x))
    (b : ℝ) (hb : 0 < b) :
    ∃ R : CornerPartition (identityProjection M), Q.Refines R ∧
      (∀ i,(R.piece i).val.val ∈ N) ∧ (∑ x ∈ F,τ.norm₂ (R.pinch (v x))^2) < b := by
  classical
  induction F using Finset.induction_on generalizing Q b with
  | empty => exact ⟨Q,Q.refines_refl,hN,by simpa using hb⟩
  | @insert x F hxF ih =>
    obtain ⟨R,hQR,hR,hx⟩ := exists_orthogonal_refinement_budget τ hNM hirr Q hN (v x)
      (hF x (Finset.mem_insert_self x F)) (b/2) (half_pos hb)
    obtain ⟨S,hRS,hS,hFS⟩ := ih R hR
      (fun y hy => hF y (Finset.mem_insert_of_mem hy)) (b/2) (half_pos hb)
    refine ⟨S,Q.refines_trans hQR hRS,hS,?_⟩
    have hxS := R.refinement_energy_le τ S hRS (v x)
    rw [← R.pinch_energy τ,← S.pinch_energy τ] at hxS
    rw [Finset.sum_insert hxF]
    linarith

end CornerPartition

end

/-! Assembly of the orthogonal budget with an explicitly controlled
subalgebra component. This constructs the further refinement; constructing
the initial subalgebra-component budget is not asserted here. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-- Any previously established coarse component budget survives the actual
finite-family quantization of the orthogonal residual. -/
theorem exists_component_controlled_refinement (hNM : N ≤ M)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : insideAlgebra (M := M) (P := N),
        (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (Q : CornerPartition (identityProjection M))
    (hQ : ∀ i,(Q.piece i).val.val ∈ N)
    {ι : Type*} (F : Finset ι) (x y : ι → M.toStarSubalgebra)
    (hy : ∀ i ∈ F,(y i).val ∈ N)
    (hxy : ∀ i ∈ F,TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (x i-y i))
    (b η : ℝ) (hη : 0 < η) (hb : (∑ i ∈ F,τ.norm₂ (Q.pinch (y i))^2) ≤ b) :
    ∃ R : CornerPartition (identityProjection M),Q.Refines R ∧
      (∀ i,(R.piece i).val.val ∈ N) ∧
      (∑ i ∈ F,τ.norm₂ (R.pinch (x i))^2) < b+η ∧
      ∀ i ∈ F,R.scalarEnergy τ (x i) ≤ τ.norm₂ (Q.pinch (y i))^2 := by
  obtain ⟨R,hQR,hR,hE⟩ := CornerPartition.exists_indexed_orthogonal_refinement_budget τ hNM hirr
    Q hQ F (fun i => x i-y i) hxy η hη
  refine ⟨R,hQR,hR,?_,fun i hi => Q.refinement_scalarEnergy_le_component τ
    (insideAlgebra (M := M) (P := N)) R hR hQR (x i) (y i) (hxy i hi)⟩
  have hid : (∑ i ∈ F,τ.norm₂ (R.pinch (x i))^2)=
      (∑ i ∈ F,τ.norm₂ (R.pinch (x i-y i))^2)+(∑ i ∈ F,τ.norm₂ (R.pinch (y i))^2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i hi => R.orthogonal_component_energy τ
      (insideAlgebra (M := M) (P := N)) hR (x i) (y i) (hy i hi) (hxy i hi))
  have hcomp : (∑ i ∈ F,τ.norm₂ (R.pinch (y i))^2) ≤
      ∑ i ∈ F,τ.norm₂ (Q.pinch (y i))^2 := by
    apply Finset.sum_le_sum
    intro i hi
    have h := Q.refinement_energy_le τ R hQR (y i)
    rwa [← Q.pinch_energy τ,← R.pinch_energy τ] at h
  rw [hid]
  linarith

end Generator.Tracial

end

end OAI
