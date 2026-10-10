import OAI.NumberTheory.TotientAsymptotic.OmegaReciprocal
import OAI.NumberTheory.TotientAsymptotic.PublishedComparison

namespace OAI

/-! Exact multiplicative moments for the number of prime factors in an interval. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def intervalOmegaWeight (a U T : ℝ) : ℕ →* ℝ where
  toFun n := a^(omegaIn n U T)/(n:ℝ)
  map_one' := by simp [omegaIn]
  map_mul' m n := by
    by_cases hm : m=0
    · subst m; simp
    by_cases hn : n=0
    · subst n; simp
    simp only [omegaIn_mul hm hn,Nat.cast_mul,pow_add]
    ring

lemma intervalOmegaWeight_nonneg {a : ℝ} (ha : 0≤a) (U T : ℝ) (n : ℕ) :
    0 ≤ intervalOmegaWeight a U T n := by
  change 0≤a^omegaIn n U T/(n:ℝ)
  positivity

lemma intervalOmegaWeight_prime (a U T : ℝ) {p : ℕ} (hp : p.Prime) :
    intervalOmegaWeight a U T p = (if U<(p:ℝ) ∧ (p:ℝ)≤T then a else 1)/(p:ℝ) := by
  classical
  by_cases h : U<(p:ℝ) ∧ (p:ℝ)≤T
  · simp [intervalOmegaWeight,omegaIn,Nat.primeFactorsList_prime hp,h]
  · simp only [intervalOmegaWeight,MonoidHom.coe_mk,OneHom.coe_mk,omegaIn,
      Nat.primeFactorsList_prime hp,List.filter_cons,List.filter_nil]
    simp [h,-Bool.decide_and]

lemma intervalOmegaWeight_norm {a : ℝ} (ha : 0≤a) (ha' : a≤3/2) (U T : ℝ)
    {p : ℕ} (hp : p.Prime) : ‖intervalOmegaWeight a U T p‖<1 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (intervalOmegaWeight_nonneg ha U T p),
    intervalOmegaWeight_prime a U T hp]
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  apply (div_lt_one (by linarith : (0:ℝ)<p)).mpr
  split_ifs <;> linarith

/-- The exact finite Euler product; concentration bounds are proved separately. -/
lemma interval_omega_moment_product {a : ℝ} (ha : 0≤a) (ha' : a≤3/2)
    (U T : ℝ) (N : ℕ) (Q : Finset ℕ) (hQ : ∀ n ∈ Q,0<n ∧ n≤N) :
    (∑ n ∈ Q,intervalOmegaWeight a U T n) ≤
      ∏ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
        (1-(if U<(p:ℝ) ∧ (p:ℝ)≤T then a else 1)/(p:ℝ))⁻¹ := by
  classical
  let S := Finset.Icc 2 N
  have hm (n : ℕ) (hn : n∈Q) : n∈Nat.factoredNumbers S := by
    refine ⟨(hQ n hn).1.ne',?_⟩
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactorsList hp).two_le,
      (Nat.le_of_mem_primeFactorsList hp).trans (hQ n hn).2⟩
  let e : {n // n∈Q} → Nat.factoredNumbers S := fun n => ⟨n.1,hm n.1 n.2⟩
  let F : Finset (Nat.factoredNumbers S) := Q.attach.image e
  have he : Function.Injective e := by
    intro n m h
    apply Subtype.ext
    exact congrArg (fun z : Nat.factoredNumbers S => z.val) h
  have hsum : (∑ n ∈ Q,intervalOmegaWeight a U T n) =
      ∑ n ∈ F,intervalOmegaWeight a U T n := by
    dsimp only [F]
    rw [Finset.sum_image (fun n _ m _ h => he h)]
    exact (Finset.sum_attach Q _).symm
  have hs := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f:=intervalOmegaWeight a U T) (fun {_} hp => intervalOmegaWeight_norm ha ha' U T hp) S
  calc
    _ = ∑ n ∈ F,intervalOmegaWeight a U T n := hsum
    _ ≤ ∑' n : Nat.factoredNumbers S,intervalOmegaWeight a U T n :=
      hs.1.of_norm.sum_le_tsum F (fun n _ => intervalOmegaWeight_nonneg ha U T n)
    _ = ∏ p ∈ S with p.Prime,(1-intervalOmegaWeight a U T p)⁻¹ := hs.2.tsum_eq
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [intervalOmegaWeight_prime a U T (Finset.mem_filter.mp hp).2]

end TotientAsymptotic

end

end OAI
