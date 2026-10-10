import OAI.MeasureTheory.Falconer.Incidence.RegularProductIncidence
import OAI.MeasureTheory.Falconer.Measures.RegularProductParameters

namespace OAI

/-! Uniform power gain for the regular product intervals used by the
planar profile decomposition. No incidence estimate is assumed. -/
namespace Falconer

 theorem regular_product_power {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < η ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let δ := (1/2:ℝ)^N
      let D := Real.exp (ε*(N:ℝ)*Real.log 2)
      ∀ (s : ℝ) (Y : Finset ℝ) (P : ℝ → Finset (Space 2))
        (T : Space 2 → Finset (Space 2)) (NP : ℕ),
      let L := Real.exp ((s-ε)*(N:ℝ)*Real.log 2)
      let U := Real.exp ((s+ε)*(N:ℝ)*Real.log 2)
      κ ≤ s → s ≤ 1-8*κ → Y.Nonempty → 0 < NP → (NP:ℝ) ≤ U →
      (∀ y ∈ Y, |y| ≤ 1 ∧ FiniteSeparatedAt δ (P y) ∧
        NormalizedFiniteBallBound δ s D (P y) ∧ L ≤ ((P y).card:ℝ) ∧
        (P y).card ≤ NP ∧ ∀ x ∈ P y, x 0 = y) →
      (∀ y ∈ Y, ∀ x ∈ P y, InBoundedLineChart (T x) ∧
        NormalizedFiniteBallBound δ s D (T x) ∧ L ≤ ((T x).card:ℝ) ∧
        ((T x).card:ℝ) ≤ U ∧ ∀ l ∈ T x, TubeIncident δ x l) →
      FiniteSeparatedAt δ (Y.biUnion fun y => (P y).biUnion T) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass Y u r ≤ D*r^(2*κ)*(Y.card:ℝ)) →
      Real.exp ((2*s+η)*(N:ℝ)*Real.log 2) ≤ ((Y.biUnion fun y => (P y).biUnion T).card:ℝ) := by
  obtain ⟨θ,Nmin,hθ,_,hmain⟩ := regular_product_incidence hκ hκ1
  obtain ⟨ε,η,Np,hε,hη,hNp,hparams⟩ := regular_product_parameters hθ hκ
  refine ⟨ε,η/2,max Nmin Np,hε,by positivity,lt_of_lt_of_le hNp (le_max_right _ _),?_⟩
  intro N hN
  dsimp only
  intro s Y P T NP hs hs1 hY hNP hNPupper hrows hpencils hsep hYball
  let x := (N:ℝ)*Real.log 2
  let δ := (1/2:ℝ)^N
  let D := Real.exp (ε*x)
  let R := Real.exp (η*x)
  let W := Real.exp (θ*x)
  let L := Real.exp ((s-ε)*x)
  let U := Real.exp ((s+ε)*x)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hDpos : 0 < D := Real.exp_pos _
  have hLpos : 0 < L := Real.exp_pos _
  have hUpos : 0 < U := Real.exp_pos _
  have hRpos : 0 < R := Real.exp_pos _
  obtain ⟨hD,hR,hRc,hRD,hGc,hPc,hlogc,h25⟩ := hparams N ((le_max_right _ _).trans hN)
  have hUL : U/L = D^2 := by
    change Real.exp ((s+ε)*x)/Real.exp ((s-ε)*x) = (Real.exp (ε*x))^2
    rw [← Real.exp_sub,← Real.exp_nat_mul]
    congr 1
    ring
  have hUeq : U = D^2*L := (div_eq_iff hLpos.ne').1 hUL
  have h4s : (4:ℝ)^s ≤ 4 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4)
      (show s ≤ 1 by linarith only [hs1,hκ])
    simpa only [Real.rpow_one] using hh
  have h42s : (4:ℝ)^(2*s) ≤ 16 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4)
      (show 2*s ≤ 2 by linarith only [hs1,hκ])
    norm_num only [Real.rpow_two,Nat.reducePow] at hh
    exact hh
  have hKrow : (4:ℝ)^(2*s)+25*D*D*(U/L)*(4:ℝ)^s ≤ 16+400*D^4 := by
    rw [hUL]
    have hm := mul_le_mul_of_nonneg_left h4s (show 0 ≤ 25*D*D*D^2 by positivity)
    have hcalc : 25*D*D*D^2*4 = 100*D^4 := by ring
    rw [hcalc] at hm
    have hpow : 0 ≤ D^4 := pow_nonneg hDpos.le _
    nlinarith only [hm,h42s,hpow]
  have hGcost : 4*R^2*((4:ℝ)^(2*s)+25*D*D*(U/L)*(4:ℝ)^s) ≤ W :=
    (mul_le_mul_of_nonneg_left hKrow (by positivity)).trans hGc
  have hPupper : ((7*NP:ℕ):ℝ) ≤ 7*U := by
    have hh := mul_le_mul_of_nonneg_left hNPupper (by norm_num : (0:ℝ) ≤ 7)
    simpa only [Nat.cast_mul,Nat.cast_ofNat,U,x,mul_assoc] using hh
  have hPcost : ((7*NP:ℕ):ℝ)^2 ≤ W*(L*L/50) := by
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (7*NP)) hPupper 2
    have hm := mul_le_mul_of_nonneg_right hPc (sq_nonneg L)
    calc
      _ ≤ (7*U)^2 := hsq
      _ = (2450*D^4)*L^2/50 := by rw [hUeq]; ring
      _ ≤ W*L^2/50 := div_le_div_of_nonneg_right hm (by norm_num)
      _ = _ := by ring
  have hlogNP : Real.log (NP:ℝ) ≤ (s+ε)*x := by
    have hh := Real.log_le_log (Nat.cast_pos.mpr hNP) hNPupper
    simpa only [U,x,Real.log_exp,mul_assoc] using hh
  have hlog : Real.log ((7*NP:ℕ):ℝ) ≤ (1-4*κ)*x := by
    rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num) (Nat.cast_pos.mpr hNP).ne']
    have hsx := mul_le_mul_of_nonneg_right hs1 hx
    nlinarith only [hlogNP,hlogc,hsx]
  have hgrowth := hmain N ((le_max_left _ _).trans hN) Y P T s D D D L L U R NP
    hY hs (by linarith only [hs1,hκ]) hDpos.le hDpos.le hDpos.le hLpos hLpos hUpos.le hRpos hNP
    (by simpa only [D,L,x,mul_assoc] using hrows)
    (by simpa only [D,L,U,x,mul_assoc] using hpencils) hsep
    (by simpa only [D,x,mul_assoc] using hYball)
    (by simpa only [W,x,mul_assoc] using hRc)
    (by simpa only [W,x,mul_assoc] using hRD)
    (by simpa only [W,x,mul_assoc] using hGcost)
    (by simpa only [W,x,mul_assoc] using hPcost)
    (by simpa only [x,mul_assoc] using hlog)
  have hfinal : Real.exp ((2*s+η/2)*x) ≤ R*(L*L/25) := by
    apply (Real.log_le_log_iff (Real.exp_pos _) (by positivity)).1
    have hh := Real.log_le_log (by positivity : 0 < 25*D^2) h25
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hh
    simp only [D,Real.log_exp] at hh
    change Real.log (Real.exp ((2*s+η/2)*x)) ≤ Real.log (R*(L*L/25))
    rw [Real.log_exp,Real.log_mul hRpos.ne' (by positivity),Real.log_div (by positivity) (by norm_num),
      Real.log_mul hLpos.ne' hLpos.ne']
    simp only [R,L,Real.log_exp]
    norm_num only [Nat.cast_ofNat] at hh
    nlinarith only [hh]
  simpa only [x,mul_assoc] using hfinal.trans hgrowth.le

end Falconer

end OAI
