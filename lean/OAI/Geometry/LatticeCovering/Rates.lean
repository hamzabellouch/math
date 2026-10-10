import OAI.Geometry.LatticeCovering.Sections

namespace OAI

section
section
noncomputable section
open Real Filter Topology Asymptotics

namespace SingleLatticeCovering.FinalRates

def firstSize (n : ℕ) : ℕ := ⌈(Real.log (Real.log (n : ℝ)))^2⌉₊

lemma loglog_nat_atTop : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

lemma log_nat_atTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma loglog_sq_littleO :
    (fun n : ℕ => (Real.log (Real.log (n : ℝ)))^2) =o[atTop]
      (fun n : ℕ => Real.log (n : ℝ)) := by
  simpa only [Function.comp_def,Real.rpow_two,Real.rpow_one] using
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1)).comp_tendsto log_nat_atTop

lemma firstSize_tendsto : Tendsto firstSize atTop atTop := by
  apply tendsto_nat_ceil_atTop.comp
  simpa only [Function.comp_def,Real.rpow_two] using (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp loglog_nat_atTop

lemma eventually_firstSize_le_log {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (firstSize n : ℝ)+1 ≤ c*Real.log (n : ℝ) := by
  filter_upwards [loglog_sq_littleO.bound (half_pos hc),
    log_nat_atTop.eventually (eventually_ge_atTop (4/c))] with n hs hl
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (Real.log_natCast_nonneg n)] at hs
  have hceil := Nat.ceil_lt_add_one (sq_nonneg (Real.log (Real.log (n : ℝ))))
  have he : 4 ≤ c*Real.log (n : ℝ) := by simpa only [mul_comm] using (div_le_iff₀ hc).mp hl
  change (firstSize n : ℝ) < (Real.log (Real.log (n : ℝ)))^2+1 at hceil
  linarith



lemma eventually_dimension_power {C a r : ℝ} (hC : 0 < C) (ha : 1 < a) (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, (D : ℝ) ≤ C*((firstSize n : ℝ)+1) →
      a^D ≤ (n : ℝ)^r := by
  have hal : 0 < Real.log a := Real.log_pos ha
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  filter_upwards [eventually_firstSize_le_log (div_pos hr (mul_pos hC hal)),
    eventually_ge_atTop (1 : ℕ)] with n hn hn1 D hD
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  apply (Real.log_le_log_iff (pow_pos ha0 _) (Real.rpow_pos_of_pos hn0 r)).mp
  rw [Real.log_pow,Real.log_rpow hn0]
  calc
    (D : ℝ)*Real.log a ≤ C*((firstSize n : ℝ)+1)*Real.log a :=
      mul_le_mul_of_nonneg_right hD hal.le
    _ = (C*Real.log a)*((firstSize n : ℝ)+1) := by ring
    _ ≤ (C*Real.log a)*(r/(C*Real.log a)*Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hn (mul_pos hC hal).le
    _ = r*Real.log (n : ℝ) := by field_simp

lemma eventually_superlinear_power {k : ℝ} (hk : 0 < k) :
    ∀ᶠ s : ℝ in atTop, 2*s ≤ k*s^(7/5 : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2/5)).eventually
      (eventually_ge_atTop (2/k))] with s hs hpow
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hmul : 2 ≤ k*s^(2/5 : ℝ) := by simpa only [mul_comm] using (div_le_iff₀ hk).mp hpow
  have he : s^(7/5 : ℝ)=s*s^(2/5 : ℝ) := by
    rw [show (7/5 : ℝ)=1+2/5 by norm_num,Real.rpow_add hs0,Real.rpow_one]
  rw [he]
  nlinarith [mul_nonneg hs0.le (sub_nonneg.mpr hmul)]



lemma cap_log_tendsto {k : ℝ} (hk : 0 < k) :
    Tendsto (fun n : ℕ => Real.log (n : ℝ)*
      Real.exp (-k*(firstSize n : ℝ)^(70/100 : ℝ))) atTop (𝓝 0) := by
  have hexp : Tendsto (fun n : ℕ => Real.exp (-Real.log (Real.log (n : ℝ)))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp loglog_nat_atTop)
  apply squeeze_zero' (Eventually.of_forall (fun n =>
    mul_nonneg (Real.log_natCast_nonneg n) (Real.exp_pos _).le)) ?_ hexp
  filter_upwards [loglog_nat_atTop.eventually (eventually_superlinear_power hk),
    loglog_nat_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (2 : ℕ)] with n hpow hs hn
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hs0 : 0 ≤ Real.log (Real.log (n : ℝ)) := le_trans zero_le_one hs
  have hceil := Nat.le_ceil ((Real.log (Real.log (n : ℝ)))^2)
  have hcappow : (Real.log (Real.log (n : ℝ)))^(7/5 : ℝ) ≤
      (firstSize n : ℝ)^(70/100 : ℝ) := by
    have hh := Real.rpow_le_rpow (sq_nonneg (Real.log (Real.log (n : ℝ)))) hceil
      (by norm_num : (0 : ℝ) ≤ 70/100)
    rw [←Real.rpow_natCast _ 2,←Real.rpow_mul hs0] at hh
    norm_num at hh
    simpa only [firstSize,show (70/100 : ℝ)=(7/10 : ℝ) by norm_num] using hh
  conv_lhs => rw [←Real.exp_log hnlog,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hcappow hk.le]



end SingleLatticeCovering.FinalRates
noncomputable section

namespace SingleLatticeCovering.FinalRates
open Real Filter Topology Asymptotics

lemma eventually_log_power_bound (k : ℕ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (Real.log (n : ℝ))^k ≤ ε*(n : ℝ)^r := by
  have h : (fun n : ℕ => (Real.log (n : ℝ))^k) =o[atTop]
      (fun n : ℕ => (n : ℝ)^r) := by
    simpa only [Function.comp_def,Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (k : ℝ) hr).comp_tendsto tendsto_natCast_atTop_atTop
  filter_upwards [h.bound hε] with n hn
  simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (Real.log_natCast_nonneg n) _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] using hn

lemma eventually_dimension_small {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, (D : ℝ) ≤ C*((firstSize n : ℝ)+1) →
      (D : ℝ) ≤ Real.log (n : ℝ) ∧ (D : ℝ) ≤ (n : ℝ)/2 := by
  filter_upwards [eventually_firstSize_le_log (inv_pos.mpr hC),
    eventually_log_power_bound 1 (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1/2)] with n hn hlog D hD
  have hDl : (D : ℝ) ≤ Real.log (n : ℝ) := by
    calc
      _ ≤ C*((firstSize n : ℝ)+1) := hD
      _ ≤ C*(C⁻¹*Real.log (n : ℝ)) := mul_le_mul_of_nonneg_left hn hC.le
      _ = Real.log (n : ℝ) := by field_simp
  refine ⟨hDl,hDl.trans ?_⟩
  simpa only [pow_one,Real.rpow_one,one_div,mul_comm,div_eq_mul_inv,one_mul] using hlog

def eta (m : ℕ) : ℝ := (m : ℝ)/4*Real.log (27/16 : ℝ)-3*Real.log (m : ℝ)

lemma eta_linear_lower :
    ∀ᶠ m : ℕ in atTop, (Real.log (27/16 : ℝ)/8)*(m : ℝ) ≤ eta m := by
  have hlog : 0 < Real.log (27/16 : ℝ) := Real.log_pos (by norm_num)
  filter_upwards [eventually_log_power_bound 1 (by norm_num : (0 : ℝ) < 1)
    (div_pos hlog (by norm_num : (0 : ℝ) < 24))] with m hm
  simp only [pow_one,Real.rpow_one] at hm
  dsimp [eta]
  linarith

lemma eventually_cap_linear {k H ε : ℝ} (hk : 0 < k) (hH : 0 ≤ H) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, (n : ℝ)/2 ≤ m →
      H*(n : ℝ)*Real.log (n : ℝ)*Real.exp (-k*(firstSize n : ℝ)^(70/100 : ℝ)) ≤ ε*m := by
  have _ := hH
  have ht : Tendsto (fun n : ℕ => H*(Real.log (n : ℝ)*
      Real.exp (-k*(firstSize n : ℝ)^(70/100 : ℝ)))) atTop (𝓝 0) :=
    by simpa only [mul_zero] using (cap_log_tendsto hk).const_mul H
  filter_upwards [ht.eventually (gt_mem_nhds (half_pos hε))] with n hn m hm
  calc
    _ = (n : ℝ)*(H*(Real.log (n : ℝ)*Real.exp (-k*(firstSize n : ℝ)^(70/100 : ℝ)))) := by ring
    _ ≤ (n : ℝ)*(ε/2) := mul_le_mul_of_nonneg_left hn.le (Nat.cast_nonneg n)
    _ ≤ ε*m := by nlinarith



lemma eventually_cap_eta {C k H : ℝ} (hC : 0 < C) (hk : 0 < k) (hH : 0 ≤ H) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, (D : ℝ) ≤ C*((firstSize n : ℝ)+1) →
      D ≤ n ∧ H*(n : ℝ)*Real.log (n : ℝ)*
        Real.exp (-k*(firstSize n : ℝ)^(70/100 : ℝ)) ≤ eta (n-D) := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp eta_linear_lower
  have hlog : 0 < Real.log (27/16 : ℝ) := Real.log_pos (by norm_num)
  filter_upwards [eventually_dimension_small hC,
    eventually_cap_linear hk hH (div_pos hlog (by norm_num : (0 : ℝ) < 8)),
    eventually_ge_atTop (2*M)] with n hD hn hnM D hdim
  have hhalf := (hD D hdim).2
  have hDn : D ≤ n := by exact_mod_cast (show (D : ℝ) ≤ n by linarith)
  have hm : (n : ℝ)/2 ≤ (n-D : ℕ) := by rw [Nat.cast_sub hDn]; linarith
  have hMm : M ≤ n-D := by
    have hnMr : (2 : ℝ)*M ≤ n := by exact_mod_cast hnM
    exact_mod_cast (show (M : ℝ) ≤ (n-D : ℕ) from by linarith)
  exact ⟨hDn,(hn (n-D) hm).trans (hM _ hMm)⟩

lemma eventually_rpow_bound {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ)^a ≤ ε*(n : ℝ)^b := by
  filter_upwards [((tendsto_rpow_atTop (sub_pos.mpr hab)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1/ε)),
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hm : 1 ≤ ε*(n : ℝ)^(b-a) := by
    simpa only [Function.comp_def,mul_comm] using (div_le_iff₀ hε).mp hn
  have he : (n : ℝ)^b=(n : ℝ)^a*(n : ℝ)^(b-a) := by
    rw [←Real.rpow_add hn0]; congr 1; ring
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hm (Real.rpow_pos_of_pos hn0 a).le]

lemma sqrt_nat_atTop : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop := by
  simpa only [Function.comp_def,Real.sqrt_eq_rpow] using
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).comp tendsto_natCast_atTop_atTop

lemma sqrt_half_bound {n m : ℕ} (hm : (n : ℝ)/2 ≤ m) :
    Real.sqrt (n : ℝ) ≤ 2*Real.sqrt (m : ℝ) := by
  have hn0 := Real.sqrt_nonneg (n : ℝ)
  have hm0 := Real.sqrt_nonneg (m : ℝ)
  have hn2 := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hm2 := Real.sq_sqrt (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  nlinarith


lemma eventually_discard_bound {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ D m : ℕ, (D : ℝ) ≤ C*((firstSize n : ℝ)+1) → m ≤ n →
      (2 : ℝ)^D*Real.sqrt (m : ℝ) ≤ ε*(n : ℝ)*Real.log (n : ℝ) := by
  filter_upwards [eventually_dimension_power hC (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 1/4),
    eventually_rpow_bound (by norm_num : (3/4 : ℝ) < 1) hε,
    log_nat_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with n hp hr hlog hn1 D m hD hmn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  calc
    _ ≤ (n : ℝ)^(1/4 : ℝ)*Real.sqrt (n : ℝ) :=
      mul_le_mul (hp D hD) (Real.sqrt_le_sqrt (by exact_mod_cast hmn))
        (Real.sqrt_nonneg _) (Real.rpow_pos_of_pos hn0 _).le
    _ = (n : ℝ)^(3/4 : ℝ) := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_add hn0]; norm_num
    _ ≤ ε*(n : ℝ) := by simpa only [Real.rpow_one] using hr
    _ ≤ ε*(n : ℝ)*Real.log (n : ℝ) := le_mul_of_one_le_right (by positivity) hlog



lemma eventually_label_criterion {C Cs CR : ℝ} (hC : 0 < C) (hCs : 1 ≤ Cs) (hCR : 0 ≤ CR) :
    ∀ᶠ n : ℕ in atTop, ∀ D m : ℕ, (D : ℝ) ≤ C*((firstSize n : ℝ)+1) →
      (n : ℝ)/2 ≤ m → m ≤ n →
      (1+CR)*(Cs*(m : ℝ)^2)^D*Real.exp (-Real.sqrt (m : ℝ)/2) < 1 := by
  have hCR1 : 0 < 1+CR := by linarith
  have hCs0 : 0 < Cs := lt_of_lt_of_le zero_lt_one hCs
  filter_upwards [eventually_dimension_small hC,
    eventually_log_power_bound 2 (by norm_num : (0 : ℝ) < 1/2)
      (by norm_num : (0 : ℝ) < 1/48),
    sqrt_nat_atTop.eventually (eventually_ge_atTop (16*(Real.log (1+CR)+1))),
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop Cs),
    eventually_ge_atTop (2 : ℕ)] with n hdim hpoly hsqrt hCsn hn2 D m hD hm hmn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hm1 : (1 : ℝ) ≤ m := by
    have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hm1
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hDl := (hdim D hD).1
  have hlogm : Real.log (m : ℝ) ≤ Real.log (n : ℝ) := Real.log_le_log hm0 (by exact_mod_cast hmn)
  have hlogC : Real.log Cs ≤ Real.log (n : ℝ) := Real.log_le_log hCs0 hCsn
  have hlogm0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  have hlogC0 : 0 ≤ Real.log Cs := Real.log_nonneg hCs
  have hlogs : (D : ℝ)*(Real.log Cs+2*Real.log (m : ℝ)) ≤ 3*(Real.log (n : ℝ))^2 := by
    calc
      _ ≤ Real.log (n : ℝ)*(Real.log Cs+2*Real.log (m : ℝ)) :=
        mul_le_mul_of_nonneg_right hDl (by linarith)
      _ ≤ Real.log (n : ℝ)*(3*Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.log_natCast_nonneg n)
      _ = _ := by ring
  rw [←Real.sqrt_eq_rpow] at hpoly
  have hs := sqrt_half_bound hm
  have hneg : Real.log (1+CR)+(D : ℝ)*(Real.log Cs+2*Real.log (m : ℝ))-
      Real.sqrt (m : ℝ)/2 < 0 := by linarith [Real.sqrt_nonneg (m : ℝ)]
  have he : (1+CR)*(Cs*(m : ℝ)^2)^D*Real.exp (-Real.sqrt (m : ℝ)/2) =
      Real.exp (Real.log (1+CR)+(D : ℝ)*(Real.log Cs+2*Real.log (m : ℝ))-
      Real.sqrt (m : ℝ)/2) := by
    have hp : (Cs*(m : ℝ)^2)^D =
        Real.exp ((D : ℝ)*(Real.log Cs+2*Real.log (m : ℝ))) := by
      rw [Real.exp_nat_mul,Real.exp_add,Real.exp_log hCs0]
      rw [show (2 : ℝ)*Real.log (m : ℝ)=Real.log ((m : ℝ)^2) by rw [Real.log_pow]; norm_num,
        Real.exp_log (pow_pos hm0 2)]
    calc
      _ = Real.exp (Real.log (1+CR))*
          Real.exp ((D : ℝ)*(Real.log Cs+2*Real.log (m : ℝ)))*
          Real.exp (-Real.sqrt (m : ℝ)/2) := by rw [Real.exp_log hCR1,hp]
      _ = _ := by rw [←Real.exp_add,←Real.exp_add]; congr 1; ring
  rw [he]
  exact Real.exp_lt_one_iff.mpr hneg




end SingleLatticeCovering.FinalRates

end
end
end

section

noncomputable section
namespace SingleLatticeCovering.Shear
open Real Filter Topology
open scoped BigOperators



def pointBudget {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α) (D : ℕ) : ℕ :=
  (s.card+1)*∏ j ∈ Finset.range D, ((A j).card+1)

lemma pointBudget_pos {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α) (D : ℕ) :
    0 < pointBudget A s D := by
  dsimp [pointBudget]
  exact Nat.mul_pos (by omega) (Finset.prod_pos (fun j hj => by omega))

lemma alphabetPoints_card_le_budget {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α)
    {q D : ℕ} (hq : q ≤ D) : (alphabetPoints A s q).card ≤ pointBudget A s D := by
  classical
  have hp : ∏ j ∈ Finset.range q, (A j).card ≤
      ∏ j ∈ Finset.range D, ((A j).card+1) := by
    calc
      _ ≤ ∏ j ∈ Finset.range q, ((A j).card+1) := Finset.prod_le_prod₀ (fun j hj => Nat.zero_le _) (fun j hj => Nat.le_succ _)
      _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.range_mono hq) (fun j hj => Nat.zero_le _) (fun j hj _ => Nat.succ_pos _)
  dsimp [alphabetPoints,pointBudget]
  rw [Finset.card_product,Fintype.card_piFinset]
  have he : (∏ i : Fin q, (A i.val).card) = ∏ j ∈ Finset.range q, (A j).card :=
    Fin.prod_univ_eq_prod_range (fun j => (A j).card) q
  rw [he]
  exact le_trans (Nat.mul_le_mul_right s.card hp) (by simp [mul_comm])

def patternTotal {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α) (D : ℕ) : ℕ :=
  ∑ q ∈ Finset.range (D+1), (allPatterns A s q).card

lemma patternTotal_bound {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α) (D : ℕ) :
    patternTotal A s D ≤ (D+1)*(pointBudget A s D+1)^(2^D) :=
  allPatterns_total_bound A s D (pointBudget A s D) (fun _ hq => alphabetPoints_card_le_budget A s hq)

lemma log_pointBudget {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α) (D : ℕ) :
    Real.log (pointBudget A s D : ℝ) = Real.log (s.card+1 : ℝ)+
      ∑ j ∈ Finset.range D, Real.log ((A j).card+1 : ℝ) := by
  simp only [pointBudget,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_prod]
  rw [Real.log_mul (by positivity) (by positivity),Real.log_prod]
  intro j hj; positivity

lemma scalar_pattern_cost (D N Q : ℕ) (hN : 0 < N)
    (hQ : Q ≤ (D+1)*(N+1)^(2^D)) :
    (2 : ℝ)^D*Real.log (2*((Q : ℝ)+1)) ≤
      (4 : ℝ)^D*(Real.log 8+Real.log ((D : ℝ)+1)+Real.log (N : ℝ)) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNr
  have hD : (0 : ℝ) < (D : ℝ)+1 := by positivity
  have hbase : (1 : ℝ) ≤ ((D : ℝ)+1)*((N : ℝ)+1)^(2^D) :=
    one_le_mul_of_one_le_of_one_le (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)]) (one_le_pow₀ (by linarith))
  have hQr : (Q : ℝ) ≤ ((D : ℝ)+1)*((N : ℝ)+1)^(2^D) := by exact_mod_cast hQ
  have hl : Real.log (2*((Q : ℝ)+1)) ≤ Real.log 4+Real.log ((D : ℝ)+1)+
      (2^D : ℕ)*Real.log ((N : ℝ)+1) := by
    calc
      _ ≤ Real.log (4*(((D : ℝ)+1)*((N : ℝ)+1)^(2^D))) :=
        Real.log_le_log (by positivity) (by linarith)
      _ = _ := by rw [Real.log_mul (by norm_num) (by positivity),
        Real.log_mul hD.ne' (by positivity),Real.log_pow]; ring
  have hNl : Real.log ((N : ℝ)+1) ≤ Real.log 2+Real.log (N : ℝ) := by
    rw [←Real.log_mul (by norm_num) hNp.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have h2 : (1 : ℝ) ≤ (2 : ℝ)^D := one_le_pow₀ (by norm_num)
  have hDl : 0 ≤ Real.log ((D : ℝ)+1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
  have hNlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNr
  have h4log : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h2log : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hcast : ((2^D : ℕ) : ℝ)=(2 : ℝ)^D := by norm_cast
  rw [hcast] at hl
  have h24 : (2 : ℝ)^D*(2 : ℝ)^D=(4 : ℝ)^D := by rw [←mul_pow]; norm_num
  have h8 : Real.log 8=Real.log 4+Real.log 2 := by
    rw [←Real.log_mul (by norm_num) (by norm_num)]; norm_num
  calc
    _ ≤ (2 : ℝ)^D*(Real.log 4+Real.log ((D : ℝ)+1)+(2 : ℝ)^D*Real.log ((N : ℝ)+1)) :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    _ ≤ (2 : ℝ)^D*((2 : ℝ)^D*(Real.log 4+Real.log ((D : ℝ)+1))+
        (2 : ℝ)^D*(Real.log 2+Real.log (N : ℝ))) := by gcongr; nlinarith
    _ = _ := by rw [h8,←h24]; ring

lemma all_pattern_cost {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α) (D : ℕ) :
    (2 : ℝ)^D*Real.log (2*((patternTotal A s D : ℝ)+1)) ≤
      (4 : ℝ)^D*(Real.log 8+Real.log ((D : ℝ)+1)+Real.log (s.card+1 : ℝ)+
        ∑ j ∈ Finset.range D, Real.log ((A j).card+1 : ℝ)) := by
  have h := scalar_pattern_cost D (pointBudget A s D) (patternTotal A s D)
    (pointBudget_pos A s D) (patternTotal_bound A s D)
  rw [log_pointBudget] at h
  convert h using 1 ; ring


end SingleLatticeCovering.Shear

noncomputable section
namespace SingleLatticeCovering.Shear
open Real Filter Topology
open scoped BigOperators

lemma polynomial_pattern_cost {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α)
    (D : ℕ) {L CL CA : ℝ} (hL : 1 ≤ L) (hCL : 0 ≤ CL) (hCA : 0 ≤ CA)
    (hD : (D : ℝ) ≤ L)
    (hlabel : Real.log (s.card+1 : ℝ) ≤ CL*L^2)
    (halphabet : ∀ j < D, Real.log ((A j).card+1 : ℝ) ≤ CA*L^2) :
    (2 : ℝ)^D*Real.log (2*((patternTotal A s D : ℝ)+1)) ≤
      (4 : ℝ)^D*(Real.log 8+1+CL+CA)*L^3 := by
  have hs : ∑ j ∈ Finset.range D, Real.log ((A j).card+1 : ℝ) ≤ (D : ℝ)*(CA*L^2) := by
    calc
      _ ≤ ∑ j ∈ Finset.range D, CA*L^2 := Finset.sum_le_sum (fun j hj => halphabet j (Finset.mem_range.mp hj))
      _ = _ := by simp [nsmul_eq_mul]
  have hlogD : Real.log ((D : ℝ)+1) ≤ L := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < D+1 by positivity)
    linarith
  have h12 : L ≤ L^2 := by nlinarith
  have h23 : L^2 ≤ L^3 := by nlinarith [sq_nonneg (L-1)]
  have h01 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hterm : Real.log 8+Real.log ((D : ℝ)+1)+Real.log (s.card+1 : ℝ)+
      ∑ j ∈ Finset.range D, Real.log ((A j).card+1 : ℝ) ≤ (Real.log 8+1+CL+CA)*L^3 := by
    have hsd := mul_le_mul_of_nonneg_right hD (show 0 ≤ CA*L^2 by positivity)
    have hlab := mul_le_mul_of_nonneg_left h23 hCL
    have hc := mul_le_mul_of_nonneg_left (show 1 ≤ L^3 by nlinarith) h01
    nlinarith
  calc
    _ ≤ (4 : ℝ)^D*(Real.log 8+Real.log ((D : ℝ)+1)+Real.log (s.card+1 : ℝ)+
      ∑ j ∈ Finset.range D, Real.log ((A j).card+1 : ℝ)) := all_pattern_cost A s D
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hterm (show 0 ≤ (4 : ℝ)^D by positivity)]

lemma log_label_count {α : Type*} (s : Finset α) {D n : ℕ} {Cs : ℝ}
    (hn : 1 ≤ Real.log (n : ℝ)) (hCs : 1 ≤ Cs) (hD : (D : ℝ) ≤ Real.log (n : ℝ))
    (hs : (s.card : ℝ) ≤ (Cs*(n : ℝ)^2)^D) :
    Real.log (s.card+1 : ℝ) ≤ (Real.log 2+Real.log Cs+2)*(Real.log (n : ℝ))^2 := by
  have hn0 : (0 : ℝ) < n := by
    by_contra h; have h0 : n=0 := by exact_mod_cast le_antisymm (le_of_not_gt h) (Nat.cast_nonneg n)
    subst n; norm_num at hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by exact_mod_cast (Nat.succ_le_iff.mpr (by exact_mod_cast hn0)))
  have hp : 0 < Cs*(n : ℝ)^2 := by positivity
  have hp1 : 1 ≤ (Cs*(n : ℝ)^2)^D := one_le_pow₀ (by nlinarith [sq_nonneg ((n : ℝ)-1)])
  have hl : Real.log (s.card+1 : ℝ) ≤ Real.log 2+(D : ℝ)*(Real.log Cs+2*Real.log (n : ℝ)) := by
    calc
      _ ≤ Real.log (2*(Cs*(n : ℝ)^2)^D) := Real.log_le_log (by positivity) (by linarith)
      _ = _ := by rw [Real.log_mul (by norm_num) (pow_pos hp _).ne',Real.log_pow,
        Real.log_mul (by positivity) (by positivity),Real.log_pow]; ring
  have hc : 0 ≤ Real.log Cs := Real.log_nonneg hCs
  have hl2 : Real.log (n : ℝ) ≤ (Real.log (n : ℝ))^2 := by nlinarith
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hh := mul_le_mul_of_nonneg_right hD (show 0 ≤ Real.log Cs+2*Real.log (n : ℝ) by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hl2 hc,
    mul_le_mul_of_nonneg_left (show 1 ≤ (Real.log (n : ℝ))^2 by nlinarith) h2]

lemma log_alphabet_bound {b D : ℕ} {L : ℝ} (hL : 1 ≤ L)
    (hD : (D : ℝ) ≤ L) (hb : (b : ℝ) ≤ L) :
    Real.log 8+(D : ℝ)*Real.log ((D : ℝ)+2)+(b : ℝ)^2 ≤
      (Real.log 8+3)*L^2 := by
  have hlog : Real.log ((D : ℝ)+2) ≤ 2*L := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < D+2 by positivity)
    linarith
  have hp := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg D)
  have hD' := mul_le_mul_of_nonneg_right hD (show 0 ≤ 2*L by linarith)
  have hb2 := pow_le_pow_left₀ (Nat.cast_nonneg b) hb 2
  have hc := mul_le_mul_of_nonneg_left (show 1 ≤ L^2 by nlinarith)
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8))
  nlinarith



lemma eventually_pattern_cost {C Cs ε : ℝ} (hC : 0 < C) (hCs : 1 ≤ Cs) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, (D : ℝ) ≤ C*((FinalRates.firstSize n : ℝ)+1) →
      ∀ {α : Type*} (s : Finset α) (A : ℕ → Finset ℝ),
      (s.card : ℝ) ≤ (Cs*(n : ℝ)^2)^D →
      (∀ j < D, Real.log ((A j).card+1 : ℝ) ≤
        Real.log 8+(D : ℝ)*Real.log ((D : ℝ)+2)+(FinalRates.firstSize n : ℝ)^2) →
      (2 : ℝ)^D*Real.log (2*((patternTotal A s D : ℝ)+1)) ≤ ε*(n : ℝ)*Real.log (n : ℝ) := by
  let H := Real.log 8+1+(Real.log 2+Real.log Cs+2)+(Real.log 8+3)
  have hH : 0 < H := by
    dsimp [H]
    linarith [Real.log_nonneg hCs,Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8),
      Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  filter_upwards [FinalRates.eventually_dimension_small hC,
    FinalRates.eventually_dimension_power (C := C) (a := 4) (r := 1/2) hC (by norm_num) (by norm_num),
    FinalRates.eventually_firstSize_le_log (c := 1) (by norm_num),
    FinalRates.eventually_log_power_bound 3 (r := 1/2) (by norm_num) (div_pos hε hH),
    FinalRates.log_nat_atTop.eventually (eventually_ge_atTop (1 : ℝ)),eventually_ge_atTop (1 : ℕ)]
    with n hdim hpow hb hlog hn hn1
  intro D hD α s A hs hA
  have hDL := (hdim D hD).1
  have hbL : (FinalRates.firstSize n : ℝ) ≤ Real.log (n : ℝ) := by linarith
  have hc := polynomial_pattern_cost A s D hn
    (show 0 ≤ Real.log 2+Real.log Cs+2 by linarith [Real.log_nonneg hCs,Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])
    (show 0 ≤ Real.log 8+3 by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)]) hDL
    (log_label_count s hn hCs hDL hs)
    (fun j hj => (hA j hj).trans (log_alphabet_bound hn hDL hbL))
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have he : (n : ℝ)^(1/2 : ℝ)*(n : ℝ)^(1/2 : ℝ)=(n : ℝ) := by
    rw [←Real.rpow_add (show (0 : ℝ) < n by exact_mod_cast hn1)]
    norm_num
  calc
    _ ≤ (4 : ℝ)^D*H*(Real.log (n : ℝ))^3 := hc
    _ ≤ (n : ℝ)^(1/2 : ℝ)*H*((ε/H)*(n : ℝ)^(1/2 : ℝ)) := by gcongr; exact hpow D hD
    _ = ε*(n : ℝ) := by calc
      _ = ε*((n : ℝ)^(1/2 : ℝ)*(n : ℝ)^(1/2 : ℝ)) := by field_simp
      _ = _ := by rw [he]
    _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hε.le hn0) hn


end SingleLatticeCovering.Shear

end
end
end

section



noncomputable section
namespace SingleLatticeCovering.FinalRates
open Real Filter Topology Shear
open scoped BigOperators



lemma exp_error {n : ℕ} (hn : 2 ≤ n) {cost : ℝ}
    (hcost : cost ≤ (n : ℝ)*Real.log (n : ℝ)) :
    Real.exp (cost-(8*(n : ℝ)*Real.log (n : ℝ))/2) ≤
      1/(n : ℝ)^(2*n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hemp : cost-(8*(n : ℝ)*Real.log (n : ℝ))/2 ≤ -((2*n : ℕ) : ℝ)*Real.log (n : ℝ) := by
    push_cast; nlinarith [mul_nonneg (Nat.cast_nonneg n) hlog]
  apply (Real.exp_le_exp.mpr hemp).trans_eq
  rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log hn0,one_div]




theorem final_conditions {C k csec Csec κ Cs CR : ℝ}
    (hC : 0 < C) (hk : 0 < k) (hcsec : 0 < csec) (hCsec : 0 ≤ Csec)
    (hκ : 0 < κ) (hCs : 1 ≤ Cs) (hCR : 0 ≤ CR) :
    ∃ Cstar : ℝ, 0 < Cstar ∧ ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ ∀ D : ℕ, (D : ℝ) ≤ C*((firstSize n : ℝ)+1) →
        D ≤ n ∧ 2 ≤ n-D ∧
        Csec*(Cstar*(n : ℝ)*Real.log (n : ℝ))*Real.exp (-k*(firstSize n : ℝ)^(70/100 : ℝ)) ≤ eta (n-D) ∧
        8*(n : ℝ)*Real.log (n : ℝ)+(2 : ℝ)^D*Real.sqrt ((n-D : ℕ) : ℝ) ≤
          csec*κ*(Cstar*(n : ℝ)*Real.log (n : ℝ)) ∧
        (1+CR)*(Cs*((n-D : ℕ) : ℝ)^2)^D*Real.exp (-Real.sqrt ((n-D : ℕ) : ℝ)/2)<1 ∧
        ∀ {α : Type*} (s : Finset α) (A : ℕ → Finset ℝ),
          (s.card : ℝ) ≤ (Cs*(n : ℝ)^2)^D →
          (∀ j < D, Real.log ((A j).card+1 : ℝ) ≤
            Real.log 8+(D : ℝ)*Real.log ((D : ℝ)+2)+(firstSize n : ℝ)^2) →
          let Lstar := 2*((patternTotal A s D : ℝ)+1)
          1 ≤ Lstar ∧ (patternTotal A s D : ℝ)<Lstar ∧
          Real.exp ((2 : ℝ)^D*Real.log Lstar-(8*(n : ℝ)*Real.log (n : ℝ))/2) ≤
            1/(n : ℝ)^(2*n) := by
  let Cstar : ℝ := 16/(csec*κ)
  have hstar : 0 < Cstar := div_pos (by norm_num) (mul_pos hcsec hκ)
  have hprod : csec*κ*Cstar=16 := by dsimp [Cstar]; field_simp
  refine ⟨Cstar,hstar,?_⟩
  filter_upwards [eventually_cap_eta (C := C) (H := Csec*Cstar) hC hk (mul_nonneg hCsec hstar.le),
    eventually_discard_bound (C := C) (ε := 8) hC (by norm_num),
    eventually_label_criterion hC hCs hCR,
    eventually_pattern_cost (C := C) (Cs := Cs) (ε := 1) hC hCs (by norm_num),
    eventually_dimension_small hC,eventually_ge_atTop (4 : ℕ)] with n hcap hdiscard hlabel hpat hdim hn
  refine ⟨by omega,?_⟩
  intro D hD
  have hDn := (hcap D hD).1
  have hm : (n : ℝ)/2 ≤ ((n-D : ℕ) : ℝ) := by rw [Nat.cast_sub hDn]; linarith [(hdim D hD).2]
  have hmn : n-D ≤ n := Nat.sub_le _ _
  have hmh : (2 : ℝ) ≤ ((n-D : ℕ) : ℝ) := by
    have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨hDn,by exact_mod_cast hmh,?_,?_,?_,?_⟩
  · convert (hcap D hD).2 using 1 ; ring
  · have hh := hdiscard D (n-D) hD hmn
    have he : csec*κ*(Cstar*(n : ℝ)*Real.log (n : ℝ))=16*(n : ℝ)*Real.log (n : ℝ) := by
      calc
        _ = (csec*κ*Cstar)*(n : ℝ)*Real.log (n : ℝ) := by ring
        _ = _ := by rw [hprod]
    rw [he]; linarith
  · exact hlabel D (n-D) hD hm hmn
  · intro α s A hs hA
    have hQ : 0 ≤ (patternTotal A s D : ℝ) := Nat.cast_nonneg _
    refine ⟨by linarith,by linarith,?_⟩
    exact exp_error (by omega) (by simpa using hpat D hD s A hs hA)


end SingleLatticeCovering.FinalRates

end
end

section




namespace SingleLatticeCovering.Horizontal
open MeasureTheory Filter
open scoped BigOperators ENNReal


lemma finite_threshold_selection {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (s : Finset I) (f : I → X → ℝ≥0∞) (t b : I → ℝ≥0∞)
    (hf : ∀ i ∈ s, Measurable (f i))
    (ht0 : ∀ i ∈ s, t i ≠ 0) (htt : ∀ i ∈ s, t i ≠ ∞)
    (hint : ∀ i ∈ s, ∫⁻ x, f i x ∂μ ≤ t i*b i)
    (hsum : ∑ i ∈ s, b i < 1) :
    ∃ x, ∀ i ∈ s, f i x ≤ t i := by
  classical
  let F : X → ℝ≥0∞ := fun x => ∑ i ∈ s, (t i)⁻¹*f i x
  have hF : ∫⁻ x, F x ∂μ < 1 := by
    dsimp [F]
    rw [lintegral_finsetSum s (fun i hi => (hf i hi).const_mul _)]
    apply lt_of_le_of_lt _ hsum
    apply Finset.sum_le_sum
    intro i hi
    rw [lintegral_const_mul _ (hf i hi)]
    calc
      _ ≤ (t i)⁻¹*(t i*b i) := mul_le_mul' le_rfl (hint i hi)
      _ = b i := by rw [←mul_assoc,ENNReal.inv_mul_cancel (ht0 i hi) (htt i hi),one_mul]
  have hsome : ∃ x, F x < 1 := by
    by_contra h
    push Not at h
    have hh : (1 : ℝ≥0∞) ≤ ∫⁻ x, F x ∂μ := by
      simpa using lintegral_mono (μ := μ) (fun x => h x)
    exact (not_le_of_gt hF) hh
  obtain ⟨x,hx⟩ := hsome
  refine ⟨x,fun i hi => ?_⟩
  have hix : (t i)⁻¹*f i x ≤ F x := by
    exact Finset.single_le_sum (f := fun i => (t i)⁻¹*f i x) (fun j _ => bot_le) hi
  have hmul : (t i)⁻¹*f i x ≤ 1 := hix.trans hx.le
  have hm := mul_le_mul' (le_refl (t i)) hmul
  simpa only [←mul_assoc,ENNReal.mul_inv_cancel (ht0 i hi) (htt i hi),one_mul,mul_one] using hm




lemma common_hole_sample {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (s : Finset I)
    (hole : I → X → ℝ≥0∞) (u : I → ℝ) (C η : ℝ) (hC : 0 ≤ C)
    (hhole : ∀ i ∈ s, Measurable (hole i))
    (hu : ∀ i ∈ s, u i ≤ η)
    (hmean : ∀ i ∈ s, ∫⁻ x, hole i x ∂μ ≤
      ENNReal.ofReal (Real.exp (-u i)+C*Real.exp (-η)))
    (hsum : (1+C)*(∑ i ∈ s, Real.exp (-u i/2)) < 1) :
    ∃ x, ∀ i ∈ s, hole i x ≤ ENNReal.ofReal (Real.exp (-u i/2)) := by
  apply finite_threshold_selection μ s hole
    (fun i => ENNReal.ofReal (Real.exp (-u i/2)))
    (fun i => ENNReal.ofReal ((1+C)*Real.exp (-u i/2))) hhole
    (fun _ _ => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
    (fun _ _ => ENNReal.ofReal_ne_top)
  · intro i hi
    apply (hmean i hi).trans
    rw [←ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    have he : Real.exp (-η) ≤ Real.exp (-u i) := Real.exp_le_exp.mpr (neg_le_neg (hu i hi))
    have hsq : Real.exp (-u i/2)*Real.exp (-u i/2)=Real.exp (-u i) := by
      rw [←Real.exp_add]; congr 1; ring
    nlinarith [mul_le_mul_of_nonneg_left he hC]
  · rw [←ENNReal.ofReal_sum_of_nonneg (fun i hi => mul_nonneg (by linarith) (Real.exp_pos _).le)]
    rw [←Finset.mul_sum]
    exact ENNReal.ofReal_lt_one.mpr hsum


end SingleLatticeCovering.Horizontal

end

section

noncomputable section

end
end
end

end OAI
