import OAI.Combinatorics.ListHadwiger.Eligibility

namespace OAI

namespace LinearListHadwiger.Sampling
open Filter

theorem complement_numeric_cutoff :
    ∀ᶠ t : ℝ in atTop, ∀ n k : ℝ, 1 ≤ n → n ≤ t^(11/10:ℝ) → t ≤ k →
      (n+(n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1)) *
        (2*Real.exp (-t^(7/10:ℝ))) ≤ 1/100 := by
  have hlog := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/10 by norm_num)).bound
    (show (0:ℝ)<1/100 by norm_num)
  have hp := (tendsto_rpow_atTop (show (0:ℝ)<1/10 by norm_num)).eventually
    (eventually_ge_atTop (100:ℝ))
  filter_upwards [eventually_gt_atTop (1:ℝ),hlog,hp] with t ht hlog hp
  intro n k hn hnt htk
  let p : ℝ := t^(1/10:ℝ)
  have htpos : 0 < t := by linarith
  have hkpos : 0 < k := by linarith
  have hp100 : 100 ≤ p := hp
  have hppos : 0 < p := by linarith
  have hlogt : Real.log t ≤ p/100 := by
    have hh : Real.log t ≤ (1/100:ℝ)*p := by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg ht.le),
        abs_of_nonneg (Real.rpow_nonneg htpos.le (1/10:ℝ))] using hlog
    linarith
  have hlo2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    exact hh
  have horder : 0 < t^(11/10:ℝ) := Real.rpow_pos_of_pos htpos _
  have hlog2n : Real.log (2*n) ≤ p := by
    calc
      _ ≤ Real.log (2*t^(11/10:ℝ)) := Real.log_le_log (by positivity) (by nlinarith)
      _ = Real.log 2+(11/10:ℝ)*Real.log t := by
        rw [Real.log_mul (by norm_num) horder.ne',Real.log_rpow htpos]
      _ ≤ p := by linarith
  have hlognp : Real.log (n+1) ≤ p := by
    exact (Real.log_le_log (by positivity) (by linarith : n+1 ≤ 2*n)).trans hlog2n
  have hratio : n/k ≤ p := by
    apply (div_le_iff₀ hkpos).mpr
    have he : t^(11/10:ℝ)=p*t := by
      dsimp [p]
      rw [←Real.rpow_add_one htpos.ne']
      norm_num
    rw [he] at hnt
    nlinarith
  have hceil : (⌈10*(n/k)*Real.log (2*n)⌉₊ : ℝ)+1 ≤ 12*p^2 := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 10*(n/k)*Real.log (2*n) by
      have hh : 0 ≤ Real.log (2*n) := Real.log_nonneg (by linarith)
      positivity)
    have hm : 10*(n/k)*Real.log (2*n) ≤ 10*p*p := by
      have hh : 0 ≤ Real.log (2*n) := Real.log_nonneg (by linarith)
      gcongr
    nlinarith [sq_nonneg (p-1)]
  have hpow : (n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1) ≤ Real.exp (12*p^3) := by
    have he : (n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1) =
        Real.exp ((⌈10*(n/k)*Real.log (2*n)⌉₊+1:ℕ)*Real.log (n+1)) := by
      rw [Real.exp_nat_mul,Real.exp_log (by positivity)]
    rw [he]
    apply Real.exp_le_exp.mpr
    have hnlog : 0 ≤ Real.log (n+1) := Real.log_nonneg (by linarith)
    calc
      _ ≤ (12*p^2)*p := by push_cast; gcongr
      _ = _ := by ring
  have hp7 : t^(7/10:ℝ)=p^7 := by
    dsimp [p]
    rw [←Real.rpow_natCast,←Real.rpow_mul htpos.le]
    norm_num
  have hp4 : 24 ≤ p^4 := by
    calc
      _ ≤ (100:ℝ)^4 := by norm_num
      _ ≤ p^4 := by gcongr
  have hhalf : 12*p^3 ≤ t^(7/10:ℝ)/2 := by
    rw [hp7]
    have hh := mul_le_mul_of_nonneg_left hp4 (show 0 ≤ p^3 by positivity)
    nlinarith [show p^3*p^4=p^7 by ring]
  have hnexp : n ≤ Real.exp (t^(7/10:ℝ)/2) := by
    have he : n+1 ≤ Real.exp p := by
      calc
        n+1 = Real.exp (Real.log (n+1)) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp p := Real.exp_le_exp.mpr hlognp
    have hple : p ≤ 12*p^3 := by
      have hp2 : 1 ≤ p^2 := by nlinarith [sq_nonneg (p-1)]
      have hh := mul_le_mul_of_nonneg_left hp2 hppos.le
      nlinarith
    exact (by linarith : n ≤ Real.exp p).trans
      (Real.exp_le_exp.mpr (hple.trans hhalf))
  have htests := hpow.trans (Real.exp_le_exp.mpr hhalf)
  have hlarge : 10000 ≤ t^(7/10:ℝ) := by
    rw [hp7]
    calc
      _ ≤ (100:ℝ)^7 := by norm_num
      _ ≤ p^7 := by gcongr
  have hdecay : 4*Real.exp (-(t^(7/10:ℝ)/2)) ≤ 1/100 := by
    have hexp := Real.add_one_le_exp (t^(7/10:ℝ)/2)
    rw [Real.exp_neg,←div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith
  calc
    _ ≤ (2*Real.exp (t^(7/10:ℝ)/2))*(2*Real.exp (-t^(7/10:ℝ))) := by
      gcongr
      linarith
    _ = 4*Real.exp (-(t^(7/10:ℝ)/2)) := by
      rw [show (2*Real.exp (t^(7/10:ℝ)/2))*(2*Real.exp (-t^(7/10:ℝ))) =
        4*(Real.exp (t^(7/10:ℝ)/2)*Real.exp (-t^(7/10:ℝ))) by ring,
        ←Real.exp_add]
      congr 2
      ring
    _ ≤ _ := hdecay

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling
open Filter Finset

theorem source_complement {B : ℕ} (hB : 1 ≤ B) :
    ∃ T : ℝ, ∀ t n r : ℝ, T ≤ t → 1 ≤ n → n ≤ t^(11/10:ℝ) →
      t/Real.log t ≤ r → r ≤ 4*t →
      let y := max 1 (t/r)
      let N := ⌈B*r*Real.log (2*y)⌉₊
      let M := ⌈n/r⌉₊
      let q := ⌈t/(⌊r/200⌋₊ : ℝ)⌉₊^2
      ∀ (V ι Ω : Type) [Fintype V] [DecidableEq V] [Fintype ι] [Fintype Ω]
        [DecidableEq ι],
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
      64 ≤ k → r ≤ k → t ≤ k → (Fintype.card V : ℝ) ≤ n → KConnectedOn G univ k →
      1 ≤ Fintype.card ι → Fintype.card ι ≤ q*N →
      ∀ (μ : ι → Ω → ℝ), (∀ i ω, 0 ≤ μ i ω) → (∀ i, ∑ ω, μ i ω=1) →
      ∀ U : (ι → Ω) → Finset V,
      (∀ v, probability (productMass μ) (fun x => v∈U x) ≤ 1/10000) →
      (∀ (A : Finset V) i x x', (∀ j, j ≠ i → x j=x' j) →
        |((A ∩ U x).card : ℝ)-(A ∩ U x').card| ≤ 2*M) →
      probability (productMass μ) (fun x =>
        ¬((∀ v, k ≤ 2*((univ \ U x).filter (G.Adj v)).card) ∧
          KConnectedOn G (univ \ U x) (k/32))) ≤ 1/100 := by
  classical
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp parameter_range_cutoff
  obtain ⟨T₁,hT₁⟩ := source_uniform_concentration hB (show (0:ℝ)<1/100 by norm_num)
  obtain ⟨T₂,hT₂⟩ := eventually_atTop.mp complement_numeric_cutoff
  refine ⟨max T₀ (max T₁ T₂),?_⟩
  intro t n r ht hn hnt hrl hru
  dsimp only
  intro V ι Ω _ _ _ _ _ G _ k hk hrk htk hord hconn hi hiq μ hμ hs U hsurv hchange
  have hr := (hT₀ t ((le_max_left _ _).trans ht)).2.2 r hrl hru
  have hconc := hT₁ t n r ((le_max_left _ _).trans ((le_max_right _ _).trans ht))
    hn hnt hrl hru ι Ω hi hiq μ hμ hs
  have htail (A : Finset V) : probability (productMass μ) (fun x => r/100 ≤
      |((U x ∩ A).card : ℝ)-expectation (productMass μ)
        (fun z => ((U z ∩ A).card : ℝ))|) ≤ 2*Real.exp (-t^(7/10:ℝ)) := by
    have hh := hconc (fun z => ((A ∩ U z).card : ℝ)) (hchange A)
    simpa only [inter_comm,show (1/100:ℝ)*r=r/100 by ring] using hh
  have hh := complement_failure G hk (by linarith [hr.1]) hrk hord hconn
    (productMass_nonneg hμ) U hsurv (by positivity) htail
  exact hh.trans (hT₂ t ((le_max_right _ _).trans ((le_max_right _ _).trans ht)) n k hn hnt htk)

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling

lemma source_B_choice : (16:ℕ) ≤ 192 ∧
    (2000*((1000000:ℕ)*65536+1) ≤ 2^48) ∧
    (10000*(401^2)^2 ≤ (2:ℕ)^48) := by norm_num

lemma survival_log_bound {r y : ℝ} (hr : 0 < r) (hy : 1 ≤ y) :
    Real.exp (-((⌈192*r*Real.log (2*y)⌉₊ : ℝ)/(4*r))) * y^4 ≤ 1/(2:ℝ)^48 := by
  have hypos : 0 < y := by linarith
  have hlog : 0 ≤ Real.log (2*y) := Real.log_nonneg (by linarith)
  have hN := Nat.le_ceil (192*r*Real.log (2*y))
  have he : 48*Real.log (2*y) ≤ (⌈192*r*Real.log (2*y)⌉₊ : ℝ)/(4*r) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*r)).mpr
    nlinarith
  have hpexp : Real.exp (-((⌈192*r*Real.log (2*y)⌉₊ : ℝ)/(4*r))) ≤
      1/(2*y)^48 := by
    calc
      _ ≤ Real.exp (-(48*Real.log (2*y))) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by
        rw [Real.exp_neg,show (48:ℝ)*Real.log (2*y)=(48:ℕ)*Real.log (2*y) by norm_num,
          Real.exp_nat_mul,Real.exp_log (by positivity)]
        simp only [one_div]
  have hpow : y^4 ≤ y^48 := by
    exact pow_le_pow_right₀ hy (by norm_num)
  calc
    _ ≤ (1/(2*y)^48)*y^4 := mul_le_mul_of_nonneg_right hpexp (by positivity)
    _ ≤ (1/(2*y)^48)*y^48 := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by rw [mul_pow]; field_simp

theorem source_sparseness {t r : ℝ} (ht : 1 ≤ t) (hr : 400 ≤ r) (hru : r ≤ 4*t) :
    let y := max 1 (t/r)
    let p := Real.exp (-((⌈192*r*Real.log (2*y)⌉₊ : ℝ)/(4*r)))
    let q := ⌈t/(⌊r/200⌋₊ : ℝ)⌉₊^2
    let k := ⌈(1000000*65536:ℝ)*t*y⌉₊
    2*k*p ≤ r/1000 ∧ (q:ℝ)^2*p ≤ 1/10000 ∧ (q:ℝ)*p ≤ 1/10000 := by
  dsimp only
  let y := max 1 (t/r)
  let p := Real.exp (-((⌈192*r*Real.log (2*y)⌉₊ : ℝ)/(4*r)))
  let q := ⌈t/(⌊r/200⌋₊ : ℝ)⌉₊^2
  let k := ⌈(1000000*65536:ℝ)*t*y⌉₊
  have htpos : 0 < t := by linarith
  have hrpos : 0 < r := by linarith
  have hy : 1 ≤ y := le_max_left _ _
  have hy' : t/r ≤ y := le_max_right _ _
  have hty : t ≤ r*y := by simpa only [mul_comm] using (div_le_iff₀ hrpos).mp hy'
  have hp : 0 < p := Real.exp_pos _
  have hpy : p*y^4 ≤ 1/(2:ℝ)^48 := survival_log_bound hrpos hy
  have hkc : (k:ℝ) ≤ (1000000*65536+1:ℝ)*t*y := by
    have hh := Nat.ceil_lt_add_one
      (show 0 ≤ (1000000*65536:ℝ)*t*y by positivity)
    have hty1 : 1 ≤ t*y := by nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hy)]
    dsimp [k]
    nlinarith
  obtain ⟨hx,hxl,hq⟩ := floor_parameter htpos hr hy hy'
  have hqc : (q:ℝ) ≤ 401^2*y^2 := by
    dsimp [q]
    push_cast
    have hh := (sq_le_sq₀ (by positivity : (0:ℝ) ≤ (⌈t/(⌊r/200⌋₊ : ℝ)⌉₊:ℝ))
      (by positivity : (0:ℝ) ≤ 401*y)).mpr hq
    nlinarith
  have hqpos : 1 ≤ q := by
    have hxpos : (0:ℝ) < (⌊r/200⌋₊:ℝ) := by exact_mod_cast (by omega : 0 < ⌊r/200⌋₊)
    have hh := Nat.le_ceil (t/(⌊r/200⌋₊:ℝ))
    have hc : 1 ≤ ⌈t/(⌊r/200⌋₊:ℝ)⌉₊ := by
      by_contra h
      have he : ⌈t/(⌊r/200⌋₊:ℝ)⌉₊=0 := by omega
      rw [he,Nat.cast_zero] at hh
      exact (not_le_of_gt (div_pos htpos hxpos)) hh
    exact one_le_pow₀ hc
  have hpy2 : p*y^2 ≤ 1/(2:ℝ)^48 := by
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy (by norm_num : 2 ≤ 4)) hp.le).trans hpy
  have hkbound : 2*(k:ℝ)*p ≤ r/1000 := by
    calc
      _ ≤ 2*((1000000*65536+1:ℝ)*t*y)*p := by gcongr
      _ ≤ 2*((1000000*65536+1:ℝ)*(r*y)*y)*p := by gcongr
      _ = (2*(1000000*65536+1:ℝ)*r)*(p*y^2) := by ring
      _ ≤ (2*(1000000*65536+1:ℝ)*r)*(1/(2:ℝ)^48) := by gcongr
      _ ≤ r/1000 := by norm_num; nlinarith
  have hqbound : (q:ℝ)^2*p ≤ 1/10000 := by
    calc
      _ ≤ (401^2*y^2)^2*p := by gcongr
      _ = (401:ℝ)^4*(p*y^4) := by ring
      _ ≤ (401:ℝ)^4*(1/(2:ℝ)^48) := by gcongr
      _ ≤ _ := by norm_num
  refine ⟨hkbound,hqbound,?_⟩
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hqpos
  have hh : (q:ℝ) ≤ (q:ℝ)^2 := by nlinarith
  exact (mul_le_mul_of_nonneg_right hh hp.le).trans hqbound

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling
open Filter

theorem polynomial_tail_cutoff (C d : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t : ℝ in atTop, C*t^d*(2*Real.exp (-t^(7/10:ℝ))) < η := by
  have ht := tendsto_rpow_atTop (show (0:ℝ)<7/10 by norm_num)
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (d/(7/10:ℝ))
    1 (by norm_num)).comp ht
  have hl : Tendsto (fun t : ℝ => t^d*Real.exp (-t^(7/10:ℝ))) atTop (nhds 0) := by
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    dsimp
    rw [←Real.rpow_mul ht.le]
    congr 2 <;> ring
  have hm := hl.const_mul (2*C)
  have he := hm.eventually (eventually_lt_nhds (show (2*C)*0 < η by simpa using hη))
  filter_upwards [he] with t ht
  rw [show C*t^d*(2*Real.exp (-t^(7/10:ℝ))) =
    (2*C)*(t^d*Real.exp (-t^(7/10:ℝ))) by ring]
  exact ht

lemma decomposition_tail_cutoff :
    ∀ᶠ t : ℝ in atTop, ∀ n : ℝ, 1 ≤ n → n ≤ t^(11/10:ℝ) →
      (n+1)^2*(2*Real.exp (-t^(7/10:ℝ))) < 1 := by
  have hh := polynomial_tail_cutoff 4 (22/10) (show (0:ℝ)<1 by norm_num)
  filter_upwards [eventually_gt_atTop (1:ℝ),hh] with t ht hh
  intro n hn hnt
  have hp : (t^(11/10:ℝ))^2=t^(22/10:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by linarith : (0:ℝ) ≤ t)]
    norm_num
  calc
    _ ≤ (2*t^(11/10:ℝ))^2*(2*Real.exp (-t^(7/10:ℝ))) := by
      gcongr
      linarith
    _ = 4*t^(22/10:ℝ)*(2*Real.exp (-t^(7/10:ℝ))) := by rw [mul_pow,hp]; ring
    _ < _ := hh

lemma private_tail_cutoff :
    ∀ᶠ t : ℝ in atTop, ∀ r : ℝ, t/Real.log t ≤ r → r ≤ 4*t →
      ((⌈t/(⌊r/200⌋₊ : ℝ)⌉₊^2 : ℕ) : ℝ)*(2*Real.exp (-t^(7/10:ℝ))) < 1/100 := by
  have hh := polynomial_tail_cutoff (401^2) 2 (show (0:ℝ)<1/100 by norm_num)
  filter_upwards [parameter_range_cutoff,hh] with t ht hh
  intro r hrl hru
  obtain ⟨hr,hy,hyt,hry,hry'⟩ := ht.2.2 r hrl hru
  have htpos : 0 < t := by linarith [ht.1]
  have hq := (floor_parameter (by linarith [ht.1]) hr hy (le_max_right 1 (t/r))).2.2
  have hlogt : Real.log t ≤ t := Real.log_le_self (by linarith [ht.1])
  have hqc : ((⌈t/(⌊r/200⌋₊ : ℝ)⌉₊^2 : ℕ) : ℝ) ≤ 401^2*t^2 := by
    push_cast
    have hh : (⌈t/(⌊r/200⌋₊ : ℝ)⌉₊ : ℝ) ≤ 401*t := by linarith
    have hp := (sq_le_sq₀ (by positivity : (0:ℝ) ≤ (⌈t/(⌊r/200⌋₊ : ℝ)⌉₊ : ℝ))
      (by positivity : (0:ℝ) ≤ 401*t)).mpr hh
    nlinarith
  calc
    _ ≤ 401^2*t^2*(2*Real.exp (-t^(7/10:ℝ))) := by gcongr
    _ < _ := by simpa only [Real.rpow_ofNat] using hh

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling
open Finset Fractional Filter

lemma source_q_pos {t r : ℝ} (ht : 0 < t) (hr : 400 ≤ r) :
    1 ≤ ⌈t/(⌊r/200⌋₊:ℝ)⌉₊^2 := by
  have hx : 1 ≤ ⌊r/200⌋₊ := (Nat.one_le_floor_iff _).mpr (by linarith)
  have hxpos : (0:ℝ) < (⌊r/200⌋₊:ℝ) := by exact_mod_cast (by omega : 0 < ⌊r/200⌋₊)
  have hh : 0 < ⌈t/(⌊r/200⌋₊:ℝ)⌉₊ := Nat.ceil_pos.mpr (div_pos ht hxpos)
  exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))

theorem source_fixed_region :
    ∃ T : ℝ, ∀ t n r : ℝ, T ≤ t → 1 ≤ n → n ≤ t^(11/10:ℝ) →
      t/Real.log t ≤ r → r ≤ 4*t →
      let y := max 1 (t/r)
      let N := ⌈192*r*Real.log (2*y)⌉₊
      let M := ⌈n/r⌉₊
      let k := ⌈(1000000*65536:ℝ)*t*y⌉₊
      ∀ (V Ω : Type) [Fintype V] [DecidableEq V] [Fintype Ω],
      ∀ G : SimpleGraph V, (Fintype.card V : ℝ) ≤ n →
      ∀ π : Ω → ℝ, (∀ ω, 0 ≤ π ω) → (∑ ω, π ω=1) →
      ∀ (I : Ω → Finset V) (E : Fin N → Finset V),
      (∀ ω, (I ω).card ≤ M) →
      (∀ v, probability π (fun ω => v∈I ω)=1/(2*r)) →
      (∀ v, (N:ℝ)/2 ≤ (univ.filter (fun j => v∈E j)).card) →
      (∀ x, 0 < productMass (fun _ : Fin N => π) x →
        r/2 < number (G.induce (↑(remainder E I x) : Set V))) →
      ∃ H : Finset V, KConnectedOn G H k ∧
        r/4 < expectation (productMass (fun _ : Fin N => π))
          (fun x => number (G.induce (↑(remainder E I x ∩ H) : Set V))) := by
  classical
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp parameter_range_cutoff
  obtain ⟨T₁,hT₁⟩ := source_uniform_concentration (by norm_num : (1:ℕ)≤192)
    (by norm_num : (0:ℝ)<1/200)
  obtain ⟨T₂,hT₂⟩ := source_uniform_concentration (by norm_num : (1:ℕ)≤192)
    (by norm_num : (0:ℝ)<1/20)
  obtain ⟨T₃,hT₃⟩ := eventually_atTop.mp decomposition_tail_cutoff
  refine ⟨max (max T₀ T₁) (max T₂ T₃),?_⟩
  intro t n r ht hn hnt hrl hru
  dsimp only
  intro V Ω _ _ _ G hord π hπ hs I E hI hmarg hE hfail
  have hp := hT₀ t ((le_max_left _ _).trans ((le_max_left _ _).trans ht))
  obtain ⟨hr,hy,hyt,hry,hry'⟩ := hp.2.2 r hrl hru
  have htpos : 0 < t := by linarith [hp.1]
  obtain ⟨hN,hN',hM,hM'⟩ := sample_size_parameters hp.1 hn hnt hr hy hry
    (by norm_num : (1:ℕ)≤192)
  have hq := source_q_pos htpos hr
  let N := ⌈192*r*Real.log (2*max 1 (t/r))⌉₊
  let q := ⌈t/(⌊r/200⌋₊:ℝ)⌉₊^2
  have hcard : Fintype.card (Fin N) ≤ q*N := by
    rw [Fintype.card_fin]
    simpa only [one_mul] using Nat.mul_le_mul_right N hq
  have hNcard : 1 ≤ Fintype.card (Fin N) := by simpa [N] using hN
  have hc := hT₁ t n r ((le_max_right _ _).trans ((le_max_left _ _).trans ht))
    hn hnt hrl hru (Fin N) Ω hNcard hcard (fun _ => π) (fun _ => hπ) (fun _ => hs)
  have hf := hT₂ t n r ((le_max_left _ _).trans ((le_max_right _ _).trans ht))
    hn hnt hrl hru (Fin N) Ω hNcard hcard (fun _ => π) (fun _ => hπ) (fun _ => hs)
  have hsurv (v : V) := remainder_survival_bound (fun _ : Fin N => hs) E I
    (by linarith : 1 ≤ r) (fun _ => hmarg) (by simpa [N] using hE) v
  have hsparse := (source_sparseness hp.1.le hr hru).1
  have htailCard (A : Finset V) := hc (fun x => ((A ∩ remainder E I x).card : ℝ))
    (remainder_card_bounded_changes E I hI A)
  have htailFrac (A : Finset V) := hf
    (fun x => number (G.induce (↑(A ∩ remainder E I x) : Set V)))
    (remainder_fractional_bounded_changes G E I hI A)
  have hcomm (A : Finset V) (x : Fin N → Ω) :
      number (G.induce (↑(A ∩ remainder E I x) : Set V)) =
      number (G.induce (↑(remainder E I x ∩ A) : Set V)) :=
    congrArg (fun S : Finset V => number (G.induce (↑S : Set V))) (Finset.inter_comm _ _)
  have hsmall := hT₃ t ((le_max_right _ _).trans ((le_max_right _ _).trans ht)) n hn hnt
  obtain ⟨H,hH,hconn,hmean⟩ := fixed_region (G := G) (S := univ)
    (productMass_nonneg (fun _ : Fin N => hπ)) (productMass_sum (fun _ : Fin N => hs))
    (remainder E I) (fun _ => subset_univ _) (by linarith : 0 < r)
    (Real.exp_pos _).le (by positivity : (0:ℝ) ≤ 2*Real.exp (-t^(7/10:ℝ)))
    (by simpa only [Fintype.card_fin,N,neg_div] using hsurv)
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hsparse)
    (by intro A; simpa only [Finset.inter_comm A,show (1/200:ℝ)*r=r/200 by ring] using htailCard A)
    (by intro A; simpa only [hcomm,show (1/20:ℝ)*r=r/20 by ring] using htailFrac A)
    (lt_of_le_of_lt (by push_cast; simp only [card_univ]; gcongr) hsmall)
    hfail
  exact ⟨H,hconn,hmean⟩

end LinearListHadwiger.Sampling

end OAI
