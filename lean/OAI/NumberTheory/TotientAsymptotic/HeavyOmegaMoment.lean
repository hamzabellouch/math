import OAI.NumberTheory.TotientAsymptotic.FullOmegaMoment

namespace OAI

/-! The fixed 15/8 moment needed for the large-Omega nice-value exception. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def heavyOmegaReciprocal : ℕ →* ℝ where
  toFun n := (15/8:ℝ)^n.primeFactorsList.length/(n:ℝ)
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m=0
    · subst m; simp
    by_cases hn : n=0
    · subst n; simp
    have hh := (Nat.perm_primeFactorsList_mul hm hn).length_eq
    rw [List.length_append] at hh
    simp only [hh,Nat.cast_mul,pow_add]
    ring

lemma heavyOmegaReciprocal_nonneg (n : ℕ) : 0 ≤ heavyOmegaReciprocal n := by
  change 0 ≤ (15/8:ℝ)^n.primeFactorsList.length/(n:ℝ)
  positivity

lemma heavyOmegaReciprocal_prime {p : ℕ} (hp : p.Prime) :
    heavyOmegaReciprocal p=(15/8:ℝ)/p := by
  simp [heavyOmegaReciprocal,Nat.primeFactorsList_prime hp]

lemma heavyOmegaReciprocal_norm {p : ℕ} (hp : p.Prime) :
    ‖heavyOmegaReciprocal p‖ < 1 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (heavyOmegaReciprocal_nonneg p),heavyOmegaReciprocal_prime hp]
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  exact (div_lt_one (by linarith)).mpr (by linarith)

lemma heavy_omega_euler_log {p : ℕ} (hp : p.Prime) :
    Real.log ((1-heavyOmegaReciprocal p)⁻¹) ≤ (15/8:ℝ)/p+64/(p:ℝ)^2 := by
  rw [heavyOmegaReciprocal_prime hp]
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0:ℝ) < p := by linarith
  have hx0 : 0 ≤ (15/8:ℝ)/p := by positivity
  have hx : (15/8:ℝ)/p ≤ 15/16 := (div_le_iff₀ hp0).mpr (by linarith)
  have hTaylor := Real.abs_log_sub_add_sum_range_le
    (show |(15/8:ℝ)/p| < 1 by rw [abs_of_nonneg hx0]; linarith) 1
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.cast_zero,
    zero_add,pow_one,div_one,abs_of_nonneg hx0] at hTaylor
  have hquad : ((15/8:ℝ)/p)^2/(1-(15/8:ℝ)/p) ≤ 64/(p:ℝ)^2 := by
    have hden : (1/16:ℝ) ≤ 1-(15/8:ℝ)/p := by linarith
    calc
      _ ≤ ((15/8:ℝ)/p)^2/(1/16) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hden
      _ = (225/4:ℝ)/(p:ℝ)^2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)
  rw [Real.log_inv]
  linarith [(abs_le.mp hTaylor).1]

lemma heavy_omega_euler_product (N : ℕ) :
    (∏ p ∈ (Finset.Icc 2 N).filter Nat.Prime,(1-heavyOmegaReciprocal p)⁻¹) ≤
      Real.exp ((15/8:ℝ)*primeReciprocalLE N+64) := by
  classical
  let P := (Finset.Icc 2 N).filter Nat.Prime
  have hpos (p : ℕ) (hp : p ∈ P) : 0 < (1-heavyOmegaReciprocal p)⁻¹ := by
    have hh := heavyOmegaReciprocal_norm (Finset.mem_filter.mp hp).2
    rw [Real.norm_eq_abs,abs_of_nonneg (heavyOmegaReciprocal_nonneg p)] at hh
    exact inv_pos.mpr (by linarith)
  apply (Real.log_le_iff_le_exp (Finset.prod_pos hpos)).mp
  rw [Real.log_prod (fun p hp => (hpos p hp).ne')]
  calc
    _ ≤ ∑ p ∈ P,((15/8:ℝ)/p+64/(p:ℝ)^2) :=
      Finset.sum_le_sum (fun p hp => heavy_omega_euler_log (Finset.mem_filter.mp hp).2)
    _ = (15/8:ℝ)*(∑ p ∈ P,(p:ℝ)⁻¹)+64*(∑ p ∈ P,1/(p:ℝ)^2) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ (15/8:ℝ)*primeReciprocalLE N+64 := by
      have he : (∑ p ∈ P,(p:ℝ)⁻¹)=primeReciprocalLE N := by
        simp only [P,primeReciprocalLE,primesUpTo,Nat.floor_natCast]
      rw [he]
      linarith [prime_reciprocal_squares_le N]

theorem heavy_omega_moment_bound : ∃ C : ℝ,0 < C ∧ ∀ N : ℕ,2 ≤ N →
    ∀ Q : Finset ℕ,(∀ n ∈ Q,0 < n ∧ n ≤ N) →
    (∑ n ∈ Q,heavyOmegaReciprocal n) ≤ C*(Real.log N)^(15/8:ℝ) := by
  classical
  obtain ⟨D,hD,herr⟩ := primeReciprocalLE_bounded_error
  refine ⟨Real.exp ((15/8:ℝ)*D+64),Real.exp_pos _,?_⟩
  intro N hN Q hQ
  let S := Finset.Icc 2 N
  have hm (n : ℕ) (hn : n ∈ Q) : n ∈ Nat.factoredNumbers S := by
    refine ⟨(hQ n hn).1.ne',?_⟩
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactorsList hp).two_le,
      (Nat.le_of_mem_primeFactorsList hp).trans (hQ n hn).2⟩
  let e : {n // n ∈ Q} → Nat.factoredNumbers S := fun n => ⟨n.1,hm n.1 n.2⟩
  let T : Finset (Nat.factoredNumbers S) := Q.attach.image e
  have he : Function.Injective e := by
    intro n m h
    apply Subtype.ext
    exact congrArg (fun z : Nat.factoredNumbers S => z.val) h
  have hsum : (∑ n ∈ Q,heavyOmegaReciprocal n) = ∑ n ∈ T,heavyOmegaReciprocal n := by
    dsimp only [T]
    rw [Finset.sum_image (fun n _ m _ h => he h)]
    exact (Finset.sum_attach Q (fun n : ℕ => heavyOmegaReciprocal n)).symm
  have hs := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f:=heavyOmegaReciprocal) (fun {_} hp => heavyOmegaReciprocal_norm hp) S
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have herror := (abs_le.mp (herr N (by exact_mod_cast hN))).2
  calc
    _ = ∑ n ∈ T,heavyOmegaReciprocal n := hsum
    _ ≤ ∑' n : Nat.factoredNumbers S,heavyOmegaReciprocal n :=
      hs.1.of_norm.sum_le_tsum T (fun n _ => heavyOmegaReciprocal_nonneg n)
    _ = ∏ p ∈ S with p.Prime,(1-heavyOmegaReciprocal p)⁻¹ := hs.2.tsum_eq
    _ ≤ Real.exp ((15/8:ℝ)*primeReciprocalLE N+64) := heavy_omega_euler_product N
    _ ≤ Real.exp (((15/8:ℝ)*D+64)+(15/8:ℝ)*B N) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = _ := by
      rw [Real.exp_add,Real.rpow_def_of_pos hlog]
      congr 1
      unfold B
      congr 1
      ring

end TotientAsymptotic

end

end OAI
