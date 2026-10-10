import OAI.NumberTheory.TotientAsymptotic.SmoothResidualMass

namespace OAI

/-! A concrete Euler-product moment for the remaining-factor exclusion.
The exponent three is sufficient for the application. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def omegaReciprocal : ℕ →* ℝ where
  toFun n := (3/2 : ℝ)^n.primeFactorsList.length/(n : ℝ)
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

lemma omegaReciprocal_nonneg (n : ℕ) : 0 ≤ omegaReciprocal n := by
  change 0 ≤ (3/2 : ℝ)^n.primeFactorsList.length/(n : ℝ)
  positivity

lemma omegaReciprocal_prime {p : ℕ} (hp : p.Prime) : omegaReciprocal p=(3/2 : ℝ)/p := by
  simp [omegaReciprocal,Nat.primeFactorsList_prime hp]

lemma omegaReciprocal_prime_norm {p : ℕ} (hp : p.Prime) : ‖omegaReciprocal p‖ < 1 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (omegaReciprocal_nonneg p),omegaReciprocal_prime hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  exact (div_lt_one (by linarith)).mpr (by linarith)

lemma omega_euler_factor_le {p : ℕ} (hp : p.Prime) :
    (1-omegaReciprocal p)⁻¹ ≤ ((p : ℝ)/(p-1))^3 := by
  rw [omegaReciprocal_prime hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hs : (0 : ℝ) < p-1 := by linarith
  have ht : (0 : ℝ) < p-3/2 := by linarith
  have he : (1-(3/2 : ℝ)/(p : ℝ))⁻¹=(p : ℝ)/(p-3/2) := by field_simp
  rw [he,div_pow]
  apply (div_le_div_iff₀ ht (pow_pos hs 3)).mpr
  nlinarith [sq_nonneg ((p : ℝ)-2)]

/-- A finite moment over all positive integers below the endpoint; no sieve
or distribution theorem is added to the published hypotheses. -/
theorem omega_reciprocal_mass (N : ℕ) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q, 0 < n ∧ n ≤ N) :
    (∑ n ∈ Q, omegaReciprocal n) ≤ (primeEulerProduct N)^3 := by
  classical
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
  have hsum : (∑ n ∈ Q, omegaReciprocal n) = ∑ n ∈ T, omegaReciprocal n := by
    dsimp only [T]
    rw [Finset.sum_image (fun n _ m _ h => he h)]
    exact (Finset.sum_attach Q (fun n : ℕ => omegaReciprocal n)).symm
  have hs := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := omegaReciprocal) (fun {_} hp => omegaReciprocal_prime_norm hp) S
  calc
    _ = ∑ n ∈ T, omegaReciprocal n := hsum
    _ ≤ ∑' n : Nat.factoredNumbers S, omegaReciprocal n :=
      hs.1.of_norm.sum_le_tsum T (fun n _ => omegaReciprocal_nonneg n)
    _ = ∏ p ∈ S with p.Prime, (1-omegaReciprocal p)⁻¹ := hs.2.tsum_eq
    _ ≤ ∏ p ∈ S with p.Prime, ((p : ℝ)/(p-1))^3 := by
      apply Finset.prod_le_prod₀
      · intro p hp
        have hpn := omegaReciprocal_prime_norm (Finset.mem_filter.mp hp).2
        rw [Real.norm_eq_abs,abs_of_nonneg (omegaReciprocal_nonneg p)] at hpn
        exact inv_nonneg.mpr (by linarith)
      · intro p hp
        exact omega_euler_factor_le (Finset.mem_filter.mp hp).2
    _ = _ := by rw [Finset.prod_pow]; rfl

lemma omega_exceptional_mass {N : ℕ} {T : ℝ} (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q, 0 < n ∧ n ≤ N ∧ T ≤ (n.primeFactorsList.length : ℝ)) :
    (∑ n ∈ Q, (n : ℝ)⁻¹) ≤ (3/2 : ℝ)^(-T)*(primeEulerProduct N)^3 := by
  have ht : 0 < (3/2 : ℝ)^(-T) := Real.rpow_pos_of_pos (by norm_num) _
  calc
    _ ≤ (3/2 : ℝ)^(-T)*∑ n ∈ Q, omegaReciprocal n := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      have hc := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3/2) (hQ n hn).2.2
      rw [Real.rpow_natCast] at hc
      have hmul : (1 : ℝ) ≤ (3/2 : ℝ)^(-T)*(3/2 : ℝ)^n.primeFactorsList.length := by
        calc
          1 = (3/2 : ℝ)^(-T)*(3/2 : ℝ)^T := by rw [← Real.rpow_add (by norm_num)]; simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hc ht.le
      have hh := mul_le_mul_of_nonneg_right hmul (show 0 ≤ (n : ℝ)⁻¹ by positivity)
      simpa only [omegaReciprocal,MonoidHom.coe_mk,OneHom.coe_mk,div_eq_mul_inv,mul_assoc,one_mul] using hh
    _ ≤ _ := mul_le_mul_of_nonneg_left (omega_reciprocal_mass N Q (fun n hn => ⟨(hQ n hn).1,(hQ n hn).2.1⟩)) ht.le

end TotientAsymptotic

end

end OAI
