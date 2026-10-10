import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ScalarScaleBudgets

namespace OAI

/-! Physical amplification of the full complement error. The singular
nuclear form enters quadratically, as proved by the complement theorem. -/

noncomputable section
namespace ContinuumCoulomb

theorem singular_complement_scaled_identity {R a g : ℝ}
    (hR : R ≠ 0) (ha : a ≠ 0) (hg : g ≠ 0) (n K b : ℝ) :
    (a*R^30)*(3*((2*n*(R^19)⁻¹)^2+(a*R^30)⁻¹^2*(8*n^3*K)+
      (b/R^20)^2*(n+2*K)*n)/g) =
      (12*a*n^2/R^8+24*n^3*K/(a*R^30)+3*a*b^2*(n+2*K)*n/R^10)/g := by
  field_simp [hR,ha,hg]
  ring

theorem exists_complement_error_scale {a b : ℝ} (ha : 0 < a) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ r q s p k : ℕ, k₀+3*r+q+s+p ≤ k →
      ∀ N : ℝ, 2 ≤ N → ∀ n K g : ℝ, 0 ≤ n → n ≤ N^r → 0 ≤ K → K ≤ N^q →
      (N^s)⁻¹ ≤ g →
      (a*(N^k)^30)*(3*((2*n*((N^k)^19)⁻¹)^2+
        (a*(N^k)^30)⁻¹^2*(8*n^3*K)+(b/(N^k)^20)^2*(n+2*K)*n)/g) ≤
        (N^p)⁻¹ := by
  let C := 12*a+24/a+9*a*b^2
  obtain ⟨c,hc,hconst⟩ := exists_polynomial_constant_bounds
    (show (0:ℝ)<1 by norm_num) C
  refine ⟨c+1,by omega,fun r q s p k hk N hN n K g hn hnN hK hKN hg => ?_⟩
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hR0 : 0 < N^k := pow_pos hN0 _
  have hR1 : 1 ≤ N^k := one_le_pow₀ hN1
  have hg0 : 0 < g := (inv_pos.mpr (pow_pos hN0 s)).trans_le hg
  have hNs : 1/g ≤ N^s := by
    apply (div_le_iff₀ hg0).mpr
    have h := mul_le_mul_of_nonneg_left hg (pow_nonneg hN0.le s)
    simpa only [mul_inv_cancel₀ (ne_of_gt (pow_pos hN0 s))] using h
  let E := 3*r+q
  have hn2 : n^2 ≤ N^E := by
    calc
      _ ≤ (N^r)^2 := pow_le_pow_left₀ hn hnN 2
      _ = N^(r*2) := (pow_mul _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hN1 (by dsimp [E]; omega)
  have hn3K : n^3*K ≤ N^E := by
    calc
      _ ≤ (N^r)^3*N^q := mul_le_mul (pow_le_pow_left₀ hn hnN 3) hKN hK (by positivity)
      _ = _ := by dsimp [E]; rw [← pow_mul,← pow_add]; congr 1; omega
  have hnK : (n+2*K)*n ≤ 3*N^E := by
    have hn' : n ≤ N^(r+q) := hnN.trans (pow_le_pow_right₀ hN1 (by omega))
    have hK' : K ≤ N^(r+q) := hKN.trans (pow_le_pow_right₀ hN1 (by omega))
    have hh : n+2*K ≤ 3*N^(r+q) := by linarith
    calc
      _ ≤ (3*N^(r+q))*N^r := mul_le_mul hh hnN hn (by positivity)
      _ = 3*N^(r+q+r) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hN1 (by dsimp [E]; omega)) (by norm_num)
  have ht1 : 12*a*n^2/(N^k)^8 ≤ 12*a*N^E/(N^k)^8 := by gcongr
  have ht2 : 24*n^3*K/(a*(N^k)^30) ≤ (24/a)*N^E/(N^k)^8 := by
    calc
      _ = (24/a)*(n^3*K)/(N^k)^30 := by ring
      _ ≤ (24/a)*N^E/(N^k)^30 := by gcongr
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ hR1 (by decide : 8 ≤ 30))
  have ht3 : 3*a*b^2*(n+2*K)*n/(N^k)^10 ≤ 9*a*b^2*N^E/(N^k)^8 := by
    calc
      _ = (3*a*b^2)*((n+2*K)*n)/(N^k)^10 := by ring
      _ ≤ (3*a*b^2)*(3*N^E)/(N^k)^10 := by gcongr
      _ = (9*a*b^2)*N^E/(N^k)^10 := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ hR1 (by decide : 8 ≤ 10))
  rw [singular_complement_scaled_identity (ne_of_gt hR0) (ne_of_gt ha) (ne_of_gt hg0)]
  calc
    _ ≤ (C*N^E/(N^k)^8)/g := by
      apply div_le_div_of_nonneg_right _ hg0.le
      calc
        _ ≤ 12*a*N^E/(N^k)^8+(24/a)*N^E/(N^k)^8+9*a*b^2*N^E/(N^k)^8 :=
          add_le_add (add_le_add ht1 ht2) ht3
        _ = _ := by dsimp [C]; ring
    _ ≤ (C*N^E/(N^k)^8)*N^s := by
      simpa only [div_eq_mul_inv,one_mul] using
        mul_le_mul_of_nonneg_left hNs (show 0 ≤ C*N^E/(N^k)^8 by dsimp [C]; positivity)
    _ = C*N^(E+s)/(N^k)^8 := by rw [pow_add]; ring
    _ ≤ N^c*N^(E+s)/(N^k)^8 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (hconst N hN).2 (by positivity)
    _ ≤ (N^p)⁻¹ := by
      rw [← pow_add,← pow_mul,inv_eq_one_div,
        div_le_div_iff₀ (pow_pos hN0 _) (pow_pos hN0 _),one_mul,← pow_add]
      exact pow_le_pow_right₀ hN1 (by dsimp [E]; omega)

end ContinuumCoulomb

end

end OAI
