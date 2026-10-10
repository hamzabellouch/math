import OAI.NumberTheory.Ostmann.QuadraticSieveCoprimePoisson

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap

theorem poisson_window_parameters {X X₀ T : ℝ} (hX₀ : 0 < X₀) (hT : 1 ≤ T)
    (hlo : X₀/2 ≤ X) (hhi : X ≤ 2*X₀) :
    0 < X₀/(2*T) ∧ X₀/(2*T) ≤ X ∧ X ≤ 2*T*X₀ ∧
      0 < T ∧ T ≤ min (X/(X₀/(2*T))) ((2*T*X₀)/X) ∧
      ((2*T*X₀)/X)^2 ≤ 16*T^2 := by
  have hTp : 0 < T := by linarith
  have hX : 0 < X := (by positivity : 0 < X₀/2).trans_le hlo
  have hlow : X₀/(2*T) ≤ X₀/2 := by
    apply div_le_div_of_nonneg_left hX₀.le (by norm_num)
    linarith
  have hhigh : 2*X₀ ≤ 2*T*X₀ := by nlinarith
  refine ⟨by positivity,hlow.trans hlo,hhi.trans hhigh,hTp,le_min ?_ ?_,?_⟩
  · apply (le_div_iff₀ (by positivity : 0 < X₀/(2*T))).mpr
    have heq : T*(X₀/(2*T)) = X₀/2 := by field_simp
    rwa [heq]
  · apply (le_div_iff₀ hX).mpr
    nlinarith
  · have hquot : (2*T*X₀)/X ≤ 4*T := by
      apply (div_le_iff₀ hX).mpr
      nlinarith
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (2*T*X₀)/X) hquot 2
    nlinarith

theorem coprime_poisson_window (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (X X₀ T : ℝ),
      2 ≤ k → 0 < X₀ → 1 ≤ T → X₀/2 ≤ X → X ≤ 2*X₀ →
      ‖(∑' n : ℤ, if Nat.Coprime n.natAbs k then ψ ((n : ℝ)/X) else 0) -
        coprimePoissonMain ψ k X (X₀/(2*T)) (2*T*X₀) (16*T^2)‖ ≤ C*X/T^A := by
  obtain ⟨C,hC,hbound⟩ := coprime_poisson_truncated ψ A
  refine ⟨C,hC,?_⟩
  intro k X X₀ T hk hX₀ hT hlo hhi
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := poisson_window_parameters hX₀ hT hlo hhi
  exact hbound k X (X₀/(2*T)) (2*T*X₀) T (16*T^2) hk h1 h2 h3 h4 h5 h6

theorem complementary_square_scale_window {M B v : ℝ} (hM : 0 < M) (hB : 0 < B)
    (hlo : B ≤ v) (hhi : v ≤ 2*B) :
    Real.sqrt (M/B)/2 ≤ Real.sqrt (M/v) ∧ Real.sqrt (M/v) ≤ 2*Real.sqrt (M/B) := by
  have hv : 0 < v := hB.trans_le hlo
  have hsqB := Real.sq_sqrt (show 0 ≤ M/B by positivity)
  have hsqv := Real.sq_sqrt (show 0 ≤ M/v by positivity)
  have hlow : M/B/4 ≤ M/v := by
    have h := div_le_div_of_nonneg_left hM.le hv (show v ≤ 4*B by linarith)
    convert h using 1
    ring
  have hhigh := Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hM.le hB hlo)
  constructor
  · nlinarith [Real.sqrt_nonneg (M/B),Real.sqrt_nonneg (M/v)]
  · nlinarith [Real.sqrt_nonneg (M/B)]

theorem dual_square_scale_window {e M B b H q : ℝ}
    (he : 0 < e) (hM : 0 < M) (hB : 0 < B) (hH : 0 < H)
    (hblo : B ≤ b) (hbhi : b ≤ 2*B) (hqlo : H^2 ≤ q) (hqhi : q ≤ 4*H^2) :
    Real.sqrt (e*H^2/(M*B))/2 ≤ Real.sqrt (e*q/(M*b)) ∧
      Real.sqrt (e*q/(M*b)) ≤ 2*Real.sqrt (e*H^2/(M*B)) := by
  have hb : 0 < b := hB.trans_le hblo
  have hq : 0 < q := (sq_pos_of_pos hH).trans_le hqlo
  have hlow : (e*H^2/(M*B))/4 ≤ e*q/(M*b) := by
    have h1 : e*H^2/(4*(M*B)) ≤ e*H^2/(M*b) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    have h2 : e*H^2/(M*b) ≤ e*q/(M*b) := by gcongr
    convert h1.trans h2 using 1
    ring
  have hhigh : e*q/(M*b) ≤ 4*(e*H^2/(M*B)) := by
    calc
      _ ≤ e*(4*H^2)/(M*b) := by gcongr
      _ ≤ e*(4*H^2)/(M*B) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        gcongr
      _ = _ := by ring
  have hs1 := Real.sq_sqrt (show 0 ≤ e*H^2/(M*B) by positivity)
  have hs2 := Real.sq_sqrt (show 0 ≤ e*q/(M*b) by positivity)
  constructor <;> nlinarith [Real.sqrt_nonneg (e*H^2/(M*B)),Real.sqrt_nonneg (e*q/(M*b))]

end Ostmann.QuadraticSieve

end OAI
