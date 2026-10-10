import OAI.NumberTheory.DirichletL.CubicSieve.AnnularImprovement

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
open CanonicalQuadraticSieve (columnDyadicLength)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma improved_shape_shell (M N Y ξ : ℝ) (hM : 0 < M) (hN : 0 < N) (hY : 0 ≤ Y)
    (hYN : Y ≤ 2*N) (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2) :
    M+(M*Y)^(2/3 : ℝ)+M^(1-ξ)*Y^(2*ξ-1) ≤
      8*(M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)) := by
  have hp : (2:ℝ)^(2/3 : ℝ) ≤ 8 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (by norm_num : (2/3 : ℝ)≤3)
    norm_num at hh ⊢
    exact hh
  have hq : (2:ℝ)^(2*ξ-1) ≤ 8 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show 2*ξ-1 ≤ 3 by linarith)
    norm_num at hh
    exact hh
  have hcross := Real.rpow_le_rpow (mul_nonneg hM.le hY)
    (mul_le_mul_of_nonneg_left hYN hM.le) (by norm_num : (0:ℝ)≤2/3)
  have hsec := Real.rpow_le_rpow hY hYN (show 0 ≤ 2*ξ-1 by linarith)
  rw [show M*(2*N) = 2*(M*N) by ring, Real.mul_rpow (by norm_num) (mul_pos hM hN).le] at hcross
  rw [Real.mul_rpow (by norm_num) hN.le] at hsec
  have hx := (hcross.trans (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg (mul_pos hM hN).le _)))
  have hy := mul_le_mul_of_nonneg_left
    (hsec.trans (mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hN.le _)))
      (Real.rpow_nonneg hM.le (1-ξ))
  nlinarith

lemma improved_loss_shell (N Y θ : ℝ) (hN : 0 ≤ N) (hY : 0 ≤ Y) (hYN : Y ≤ 2*N)
    (hθ : 0 ≤ θ) (hθsmall : θ ≤ 1/2) : Y^(6*θ) ≤ 8*N^(6*θ) := by
  have hh := Real.rpow_le_rpow hY hYN (show 0 ≤ 6*θ by positivity)
  rw [Real.mul_rpow (by norm_num) hN] at hh
  have hp : (2:ℝ)^(6*θ) ≤ 8 := by
    have he := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show 6*θ ≤ 3 by linarith)
    norm_num at he
    exact he
  exact hh.trans (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hN _))

theorem HasCubicExponent.full_improved {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) ≤ ξ) (hξ2 : ξ ≤ 2)
    (θ : ℝ) (hθ : 0 < θ) (hθsmall : θ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      elementSieveNorm M N ≤ C*N^(7*θ)*
        (M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)) := by
  obtain ⟨K,hK,hb⟩ := h.annular_improved hξ hξ2 θ hθ hθsmall
  let D : ℝ := 2+1/(θ*Real.log 2)
  have hD : 0 < D := by
    dsimp [D]
    have := Real.log_pos (by norm_num : (1:ℝ)<2)
    positivity
  refine ⟨64*K*D, by positivity, ?_⟩
  intro M N hM hN
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  let cols : idealRange N → Ideal O := fun j => j.val
  have hc (j : idealRange N) : Admissible (cols j) := (mem_idealRange.mp j.property).1
  have hn (j : idealRange N) : (Ideal.absNorm (cols j) : ℝ) ≤ N := (mem_idealRange.mp j.property).2
  let R := elementRange M
  have hR (z : O) (hz : z ∈ R) : (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M :=
    ((mem_elementRange M z).mp hz).2
  let S := M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  apply FiniteSieveOperator.squared_norm_le_of_energy (elementMatrix M N)
  · positivity
  intro a
  have hsector (l : Fin (columnDyadicLength N + 1)) :
      (∑ z ∈ R, ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖^2) ≤
        (64*K*N^(6*θ)*S)*∑ j : CubicColumnShell cols N l, ‖a j.val‖^2 := by
    by_cases hne : Nonempty (CubicColumnShell cols N l)
    · obtain ⟨j₀⟩ := hne
      have hYN := cubicColumnShell_scale_le cols N hc hn l j₀
      have hY1 : 1 ≤ (2:ℝ)^l.val := one_le_pow₀ (by norm_num)
      have hs := hb M ((2:ℝ)^l.val) hM hY1
        (fun j : CubicColumnShell cols N l => cols j.val)
        (fun j k he => Subtype.ext (Subtype.ext he)) (fun j => hc j.val)
        (fun j => cubicColumnShell_bounds cols N hc hn l j)
        (fun j => a j.val) R hR
      have hl := improved_loss_shell N ((2:ℝ)^l.val) θ hN0.le (by positivity) hYN hθ.le hθsmall.le
      have ht := improved_shape_shell M N ((2:ℝ)^l.val) ξ hM0 hN0 (by positivity) hYN
        (by linarith) hξ2
      apply hs.trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hh := mul_le_mul (mul_le_mul_of_nonneg_left hl hK.le) ht (by positivity) (by positivity)
      convert hh using 1; dsimp only [S]; ring
    · let : IsEmpty (CubicColumnShell cols N l) := not_nonempty_iff.mp hne
      simp
  have hsum := cubic_energy_column_shells cols N a R
  have hle := Finset.sum_le_sum (s := Finset.univ) (fun l hl => hsector l)
  rw [← Finset.mul_sum, cubicColumnShell_energy cols N a] at hle
  have he := hsum.trans (mul_le_mul_of_nonneg_left hle (by positivity))
  have hlog := CanonicalQuadraticSieve.columnDyadicLength_small_power θ hθ N hN
  have he' := he.trans (mul_le_mul_of_nonneg_right hlog
    (show 0 ≤ (64*K*N^(6*θ)*S)*∑ j, ‖a j‖^2 by positivity))
  have hp : N^θ*N^(6*θ) = N^(7*θ) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  rw [← Finset.sum_coe_sort] at he'
  change (∑ z : elementRange M, ‖∑ j : idealRange N, cubicRow j.val z.val*a j‖^2) ≤ _
  apply he'.trans_eq
  calc
    _ = (64*K*D)*(N^θ*N^(6*θ))*S*∑ j, ‖a j‖^2 := by dsimp [D]; ring
    _ = _ := by rw [hp]

end
end SevenEighths.CubicSieve

end OAI
