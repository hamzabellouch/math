import OAI.NumberTheory.Jacobsthal.Primes.PrincipalPrimePowers

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma eventually_pnt_exp_le_log_power (c M : ℝ) (hc : 0 < c) (_hM : 0 < M) :
    ∀ᶠ X : ℝ in atTop,
      Real.exp (-c*(Real.log X)^(1/2:ℝ)) ≤ (Real.log X)^(-M) := by
  have he := Real.tendsto_log_atTop.eventually (eventually_log_rpow_le_self (4:ℝ))
  have he2 := Real.tendsto_log_atTop.eventually
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (M/c)))
  filter_upwards [he,he2] with X hX hsize
  let L : ℝ := Real.log X
  have hL : 3 ≤ L := hX.1
  have hLp : 0 < L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have h4 : (Real.log L)^4 ≤ L := by simpa only [Real.rpow_ofNat] using hX.2
  have hroot := Real.sqrt_le_sqrt h4
  rw [show (Real.log L)^4 = ((Real.log L)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)] at hroot
  have hMbound : M ≤ c*Real.log L := by
    have h := (div_le_iff₀ hc).mp hsize
    nlinarith only [h]
  have h1 := mul_le_mul_of_nonneg_right hMbound hlogL
  have h2 := mul_le_mul_of_nonneg_left hroot hc.le
  have hsave : M*Real.log L ≤ c*L^(1/2:ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    nlinarith only [h1,h2]
  change Real.exp (-c*L^(1/2:ℝ)) ≤ L^(-M)
  conv_rhs => rw [Real.rpow_def_of_pos hLp]
  apply Real.exp_le_exp.mpr
  nlinarith only [hsave]

lemma sharpSum_vonMangoldt_eq {X : ℝ} (hX : 0 ≤ X) :
    sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X = (_root_.Erdos970.ChebyshevPsi X:ℂ) := by
  unfold sharpSum _root_.Erdos970.ChebyshevPsi
  rw [Nat.floor_add_one hX,Complex.ofReal_sum]

theorem ordinary_psi_log_power (M : ℝ) (hM : 0 < M) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ‖sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X-(X:ℂ)‖ ≤
        K*X/(Real.log X)^M := by
  obtain ⟨c,hc,hPNT⟩ := _root_.Erdos970.Strong_PNT
  obtain ⟨K,hK,hbound⟩ := hPNT.exists_pos
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound.bound,eventually_pnt_exp_le_log_power c M hc hM,
    eventually_ge_atTop (3:ℝ)] with X hb he hX
  have hXp : 0 < X := by linarith
  have hLp : 0 < Real.log X := Real.log_pos (by linarith)
  have hnonneg : 0 ≤ X*Real.exp (-c*(Real.log X)^(1/2:ℝ)) := by positivity
  change ‖_root_.Erdos970.ChebyshevPsi X-X‖ ≤ K*‖X*Real.exp (-c*(Real.log X)^(1/2:ℝ))‖ at hb
  rw [sharpSum_vonMangoldt_eq hXp.le,← Complex.ofReal_sub,Complex.norm_real]
  simp only [Real.norm_eq_abs] at hb ⊢
  rw [abs_of_nonneg hnonneg] at hb
  calc
    _ ≤ K*(X*Real.exp (-c*(Real.log X)^(1/2:ℝ))) := hb
    _ ≤ K*(X*(Real.log X)^(-M)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left he hXp.le) hK.le
    _ = _ := by rw [Real.rpow_neg hLp.le,div_eq_mul_inv]; ring

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma principal_difference_log_power (A M : ℝ) (hA : 0 < A) (_hM : 0 < M) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q],
      (q:ℝ) ≤ (Real.log X)^A →
      ‖sharpSum (fun n:ℕ => (1:DirichletCharacter ℂ q) n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X‖ ≤ K*X/(Real.log X)^M := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨A/Real.log 2,div_pos hA hlog2,?_⟩
  filter_upwards [eventually_log_rpow_le_self (M+2)] with X hX
  intro q _ hq
  obtain ⟨hX3,hpow⟩ := hX
  let L : ℝ := Real.log X
  have hXp : 0 < X := by linarith
  have hL1 : 1 ≤ L := ((Real.lt_log_iff_exp_lt hXp).mpr (Real.exp_one_lt_three.trans_le hX3)).le
  have hLp : 0 < L := by linarith
  have hqpos : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  have hlogq := Real.log_le_log hqpos hq
  rw [Real.log_rpow hLp] at hlogq
  have hlogL : Real.log L ≤ L := by linarith [Real.log_le_sub_one_of_pos hLp]
  have h2eq : L^(2:ℝ) = L^2 := Real.rpow_natCast L 2
  change L^(M+2) ≤ X at hpow
  rw [Real.rpow_add hLp,h2eq] at hpow
  have hL2 : L^2 ≤ X/L^M := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hLp M)).mpr
    calc
      _ = L^M*L^2 := mul_comm _ _
      _ ≤ X := hpow
  have hprod : L*Real.log L ≤ L^2 := by
    have h := mul_le_mul_of_nonneg_left hlogL hLp.le
    nlinarith only [h]
  calc
    _ ≤ (L/Real.log 2)*Real.log (q:ℝ) := norm_principal_sharp_difference_real q (by linarith)
    _ ≤ (L/Real.log 2)*(A*Real.log L) :=
      mul_le_mul_of_nonneg_left hlogq (div_nonneg hLp.le hlog2.le)
    _ = (A/Real.log 2)*(L*Real.log L) := by ring
    _ ≤ (A/Real.log 2)*(X/L^M) :=
      mul_le_mul_of_nonneg_left (hprod.trans hL2) (div_nonneg hA.le hlog2.le)
    _ = _ := by ring

theorem principal_character_log_power (A M : ℝ) (hA : 0 < A) (hM : 0 < M) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q],
      (q:ℝ) ≤ (Real.log X)^A →
      ‖sharpSum (fun n:ℕ => (1:DirichletCharacter ℂ q) n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-(X:ℂ)‖ ≤
        K*X/(Real.log X)^M := by
  obtain ⟨C,hC,hDiff⟩ := principal_difference_log_power A M hA hM
  obtain ⟨D,hD,hOrd⟩ := ordinary_psi_log_power M hM
  refine ⟨C+D,by positivity,?_⟩
  filter_upwards [hDiff,hOrd] with X hDiff hOrd
  intro q _ hq
  have hd := hDiff q hq
  have hn := norm_add_le
    (sharpSum (fun n:ℕ => (1:DirichletCharacter ℂ q) n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
      sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X)
    (sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X-(X:ℂ))
  rw [sub_add_sub_cancel] at hn
  apply (hn.trans (add_le_add hd hOrd)).trans_eq
  ring

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
