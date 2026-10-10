import OAI.Probability.RadialTransition.LinearInteractions

namespace OAI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff BigOperators ENNReal NNReal

namespace RadialTransition

lemma finite_term_le_grand {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t L β : ℝ} (hst : StableWith φ B) (ht : 0 < t) (hL : 0 < L) (hβ : 0 ≤ β) (h : ℝ) (n : ℕ) :
    h*((n:ℝ)/L^3)-finiteCanonical φ t L n β ≤ finiteGrandPressure φ t L β h := by
  have hterm := (grandPartition_summable hφ hb hst hL.le hβ t h).le_tsum n
    (fun N _ => mul_nonneg (Real.exp_pos _).le (partition_nonneg L N β))
  have hh := Real.log_le_log (mul_pos (Real.exp_pos _) (partition_pos hφ hb hL n β)) hterm
  rw [Real.log_mul (Real.exp_ne_zero _) (partition_pos hφ hb hL n β).ne', Real.log_exp] at hh
  dsimp only [finiteGrandPressure, finiteCanonical]
  apply (le_div_iff₀ (by positivity : 0 < t*L^3)).mpr
  convert hh using 1 <;> first | rfl | (try field_simp [ht.ne', hL.ne']; ring)

lemma log_quadraticTerm_eq {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {t L : ℝ} (ht : 0 < t) (hL : 0 < L) (β h a eta : ℝ) (n : ℕ) :
    Real.log (quadraticTerm φ L β (t*h) (β*t*a*(1+eta)/2) n)/(t*L^3) =
      (h+β*a*((n:ℝ)/L^3))*((n:ℝ)/L^3)-finiteCanonical φ t L n β -
      β*a/2*((n:ℝ)/L^3)^2+β*a*eta/2*((n:ℝ)/L^3)^2 := by
  rw [quadraticTerm, Real.log_mul (mul_ne_zero (Real.exp_ne_zero _) (partition_pos hφ hb hL n β).ne') (Real.exp_ne_zero _),
    Real.log_mul (Real.exp_ne_zero _) (partition_pos hφ hb hL n β).ne', Real.log_exp, Real.log_exp]
  unfold finiteCanonical
  field_simp
  ring

lemma log_quadraticTerm_bound {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t L β : ℝ} (hst : StableWith φ B) (ht : 0 < t) (hL : 0 < L) (hβ : 0 ≤ β)
    (h a eta : ℝ) (n : ℕ) :
    Real.log (quadraticTerm φ L β (t*h) (β*t*a*(1+eta)/2) n)/(t*L^3) ≤
      finiteGrandPressure φ t L β (h+β*a*((n:ℝ)/L^3)) -
      β*a/2*((n:ℝ)/L^3)^2+β*a*eta/2*((n:ℝ)/L^3)^2 := by
  rw [log_quadraticTerm_eq hφ hb ht hL]
  linarith [finite_term_le_grand hφ hb hst ht hL hβ (h+β*a*((n:ℝ)/L^3)) n]

lemma quadratic_sum_pressure_bound {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t L β h a eta c B₀ κ D P : ℝ} (hst : StableWith φ B) (ht : 0 < t) (hL : 1 ≤ L)
    (hβ : 0 ≤ β) (ha : 0 ≤ a) (heta : 0 ≤ eta) (hκ : 0 < κ)
    (hc : κ ≤ β*c-β*t*a*(1+eta)/2) (hD : 1 ≤ D) (hcut : t*h+β*B₀+2 ≤ κ*D)
    (hE : ∀ n x, x ∈ configurationCube L n → c*(n:ℝ)^2/L^3-B₀*n ≤ energy φ x)
    (hP : 0 ≤ P) (hbound : ∀ d ∈ Icc (0:ℝ) D, finiteGrandPressure φ t L β (h+β*a*d)-β*a/2*d^2 ≤ P) :
    Summable (quadraticTerm φ L β (t*h) (β*t*a*(1+eta)/2)) ∧
    Real.log (∑' n, quadraticTerm φ L β (t*h) (β*t*a*(1+eta)/2) n)/(t*L^3) ≤
      P+β*a*eta/2*D^2+Real.log ((D+2)*L^3)/(t*L^3) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hV : 0 < t*L^3 := by positivity
  let N := ⌊D*L^3⌋₊
  let F := quadraticTerm φ L β (t*h) (β*t*a*(1+eta)/2)
  have hFp (n : ℕ) : 0 < F n := quadraticTerm_pos hφ hb hL0 _ _ _ n
  have htail (n : ℕ) (hn : N < n) : F n ≤ Real.exp (-(n:ℝ)) := by
    apply quadraticTerm_tail_bound hφ hb hL0 hβ hκ hc hD hcut hE
    exact (Nat.floor_lt (by positivity : 0 ≤ D*L^3)).mp hn
  have hs : Summable F := summable_of_tail_exp (fun n => (hFp n).le) N htail
  let M := Real.exp (t*L^3*(P+β*a*eta/2*D^2))
  have hM : 1 ≤ M := Real.one_le_exp_iff.mpr (by positivity)
  have hsmall (n : ℕ) (hn : n ≤ N) : F n ≤ M := by
    have hnD : (n:ℝ)/L^3 ≤ D := by
      apply (div_le_iff₀ (by positivity : 0 < L^3)).mpr
      exact (by exact_mod_cast hn : (n:ℝ) ≤ N).trans (Nat.floor_le (by positivity))
    have hd0 : 0 ≤ (n:ℝ)/L^3 := by positivity
    have hbnd := hbound ((n:ℝ)/L^3) ⟨hd0, hnD⟩
    have hh := log_quadraticTerm_bound hφ hb hst ht hL0 hβ h a eta n
    have he : β*a*eta/2*((n:ℝ)/L^3)^2 ≤ β*a*eta/2*D^2 := by
      apply mul_le_mul_of_nonneg_left (sq_le_sq₀ hd0 (by positivity) |>.mpr hnD)
      positivity
    have hl : Real.log (F n)/(t*L^3) ≤ P+β*a*eta/2*D^2 := by linarith
    have hl' := (div_le_iff₀ hV).mp hl
    calc
      _ = Real.exp (Real.log (F n)) := (Real.exp_log (hFp n)).symm
      _ ≤ M := Real.exp_le_exp.mpr (by nlinarith)
  have hsum := truncated_sum_bound hs hM (tail_le_one_of_exp (fun n => (hFp n).le) N htail) hsmall
  have hnV : (N:ℝ)+2 ≤ (D+2)*L^3 := by
    have hfloor := Nat.floor_le (show 0 ≤ D*L^3 by positivity)
    have hV1 : 1 ≤ L^3 := one_le_pow₀ hL
    dsimp only [N]
    nlinarith
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_right hnV (by positivity : 0 ≤ M))
  have hpos : 0 < ∑' n, F n := lt_of_lt_of_le (hFp 0) (hs.le_tsum 0 (fun n _ => (hFp n).le))
  have hl := Real.log_le_log hpos hsum'
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp] at hl
  refine ⟨hs, ?_⟩
  apply (div_le_iff₀ hV).mpr
  convert hl using 1; first | rfl | (try field_simp [ht.ne', hL0.ne']; ring)

end RadialTransition

end

end OAI
