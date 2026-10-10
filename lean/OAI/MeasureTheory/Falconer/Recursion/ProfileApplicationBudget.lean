import OAI.MeasureTheory.Falconer.Recursion.ProfileUniformIterationBudget
import OAI.MeasureTheory.Falconer.Incidence.BlockCellPower

namespace OAI

/-! One block width and one weak initial constant control all profile-cell
estimates and every step of a bounded-length interval composition. -/
namespace Falconer

theorem profile_label_le_first_iterate {H W : ℝ} (hH : 1 ≤ H) (hW : 1 ≤ W)
    (B K : ℕ) :
    (2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K ≤
      profileBudgetSequence H ((2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K) W 1 := by
  rw [profileBudgetSequence]
  change _ ≤ 1024*W^2*H^3*((2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K)
  apply le_mul_of_one_le_left (by positivity)
  have hw : (1:ℝ) ≤ W^2 := one_le_pow₀ hW
  have hh : (1:ℝ) ≤ H^3 := one_le_pow₀ hH
  nlinarith only [mul_le_mul hw hh (by norm_num) (sq_nonneg W)]

theorem profile_sixth_power_le_label_square (B K : ℕ) :
    (2:ℝ)^(6*K) ≤ ((2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K)^2 := by
  have hb : (1:ℝ) ≤ ((2*B+1:ℕ):ℝ)^K := by
    apply one_le_pow₀
    exact_mod_cast (show 1 ≤ 2*B+1 by omega)
  have hh := le_mul_of_one_le_right (show 0 ≤ (2:ℝ)^(3*K) by positivity) hb
  have hpow := pow_le_pow_left₀ (show 0 ≤ (2:ℝ)^(3*K) by positivity) hh 2
  convert hpow using 1
  rw [← pow_mul]
  congr 1
  omega

theorem exists_profile_application_budget {ε : ℝ} (hε : 0 < ε) (J : ℕ) :
    ∃ B : ℕ, 0 < B ∧ Even B ∧ ∃ lam : ℝ, 0 < lam ∧ ∃ N0 : ℕ, 0 < N0 ∧
    ∀ m : ℕ, 0 < m → N0 ≤ B*m →
      let N := B*m
      let H : ℝ := (4*(N+2)+11:ℕ)
      let G := (2:ℝ)^(3*(m+1))*((2*B+1:ℕ):ℝ)^(m+1)
      let W := profileBudgetSequence H G ((2:ℝ)^(lam*(N:ℝ)))
      (∀ j ≤ 2*J+1, W j ≤ (2:ℝ)^(ε*(N:ℝ))) ∧
      (∀ j ≤ 2*J, ∀ A : ℝ,
        profileGeometryConstant (m+1) B (W j) A ≤ (2:ℝ)^((4*ε)*(N:ℝ)+A)) ∧
      640*((N:ℝ)+3) ≤ (2:ℝ)^(ε*(N:ℝ)) ∧
      (43264*H^4)^(2*J) ≤ (2:ℝ)^(ε*(N:ℝ)) ∧
      G ≤ (2:ℝ)^((lam/4)*(N:ℝ)) := by
  obtain ⟨B,hB,hBeven,lam,hlam,N1,hN1,hiter⟩ := exists_uniform_profile_iteration_budget hε (2*J+1)
  obtain ⟨N2,hN2,hfixed⟩ := dyadic_polynomial_loss hε
    (show 0 ≤ 100000*(2:ℝ)^(2*B) by positivity) 0
  obtain ⟨N3,hN3,hpoly⟩ := dyadic_polynomial_loss hε (show 0 ≤ (1920:ℝ) by norm_num) 1
  obtain ⟨N4,hN4,hcomp⟩ := dyadic_polynomial_loss hε
    (show 0 ≤ ((43264:ℝ)*19^4)^(2*J) by positivity) (8*J)
  refine ⟨B,hB,hBeven,lam,hlam,max N1 (max N2 (max N3 N4)),by omega,?_⟩
  intro m hm hN
  dsimp only
  let N := B*m
  let H : ℝ := (4*(N+2)+11:ℕ)
  let G := (2:ℝ)^(3*(m+1))*((2*B+1:ℕ):ℝ)^(m+1)
  let W := profileBudgetSequence H G ((2:ℝ)^(lam*(N:ℝ)))
  have h1 : N1 ≤ N := by dsimp [N]; omega
  have h2 : N2 ≤ N := by dsimp [N]; omega
  have h3 : N3 ≤ N := by dsimp [N]; omega
  have h4 : N4 ≤ N := by dsimp [N]; omega
  have exp_eq (a : ℝ) : Real.exp (a*(N:ℝ)*Real.log 2) = (2:ℝ)^(a*(N:ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  have hW (j : ℕ) (hj : j ≤ 2*J+1) : W j ≤ (2:ℝ)^(ε*(N:ℝ)) := (hiter m hm h1 j hj).1
  have hH : 1 ≤ H := by dsimp [H]; exact_mod_cast (show 1 ≤ 4*(N+2)+11 by omega)
  have hW0 : 1 ≤ (2:ℝ)^(lam*(N:ℝ)) := Real.one_le_rpow (by norm_num) (by positivity)
  have hG : G ≤ (2:ℝ)^(ε*(N:ℝ)) :=
    (profile_label_le_first_iterate hH hW0 B (m+1)).trans (hW 1 (by omega))
  have hK : (2:ℝ)^(6*(m+1)) ≤ (2:ℝ)^((2*ε)*(N:ℝ)) := by
    calc
      _ ≤ G^2 := profile_sixth_power_le_label_square B (m+1)
      _ ≤ ((2:ℝ)^(ε*(N:ℝ)))^2 := pow_le_pow_left₀ (by positivity) hG 2
      _ = _ := by
        rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
        congr 1
        norm_num
        ring
  have hfixed' : 100000*(2:ℝ)^(2*B) ≤ (2:ℝ)^(ε*(N:ℝ)) := by
    simpa only [pow_zero,mul_one,exp_eq] using hfixed N h2
  refine ⟨hW,?_,?_,?_,(hiter m hm h1 0 (by omega)).2⟩
  · intro j hj A
    have hWj := hW j (show j ≤ 2*J+1 by omega)
    have hWj0 : 0 ≤ W j := zero_le_one.trans
      (profileBudgetSequence_one_le hH (profile_label_cost_one_le B (m+1)) hW0 j)
    calc
      _ = (100000*(2:ℝ)^(2*B))*(W j)*(2:ℝ)^(6*(m+1))*(2:ℝ)^A := by
        dsimp [profileGeometryConstant]
        ring
      _ ≤ (2:ℝ)^(ε*(N:ℝ))*(2:ℝ)^(ε*(N:ℝ))*(2:ℝ)^((2*ε)*(N:ℝ))*(2:ℝ)^A := by
        gcongr
      _ = _ := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2),
          ← Real.rpow_add (by norm_num : (0:ℝ) < 2),
          ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 1
        ring
  · calc
      _ ≤ 1920*((N:ℝ)+1)^1 := by
        change 640*((N:ℝ)+3) ≤ 1920*((N:ℝ)+1)^1
        rw [pow_one]
        nlinarith only [Nat.cast_nonneg (α := ℝ) N]
      _ ≤ Real.exp (ε*(N:ℝ)*Real.log 2) := hpoly N h3
      _ = _ := exp_eq ε
  · have hHle : H ≤ 19*((N:ℝ)+1) := by
      dsimp [H]
      push_cast
      nlinarith only [Nat.cast_nonneg (α := ℝ) N]
    calc
      _ ≤ (43264*(19*((N:ℝ)+1))^4)^(2*J) := by gcongr
      _ = ((43264:ℝ)*19^4)^(2*J)*((N:ℝ)+1)^(8*J) := by
        simp only [mul_pow,← pow_mul]
        rw [show 4*(2*J) = 8*J by omega]
        ring
      _ ≤ Real.exp (ε*(N:ℝ)*Real.log 2) := hcomp N h4
      _ = _ := exp_eq ε

end Falconer

end OAI
