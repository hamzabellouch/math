import OAI.NumberTheory.SingleFold.Torsion

namespace OAI

namespace SingleFold.GrowthEstimate
open Filter
open scoped Topology

variable {W : ℕ → ℕ} {a c : ℝ}

lemma sequence_strict (hW : ∀ j, 0<W j) (hzero : W 0=1) (hc : 0≤c) (ha : 2*c<a)
    (happrox : ∀ j, 1≤j → |Real.log (W j:ℝ)-a*(j:ℝ)^2|≤c) : StrictMono W := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hp (j : ℕ) : (0:ℝ)<W j := by exact_mod_cast hW j
  apply_mod_cast (Real.log_lt_log_iff (hp n) (hp (n+1))).mp (show Real.log (W n:ℝ)<Real.log (W (n+1):ℝ) from ?_)
  have ha' : 0<a := by linarith
  rcases n with _|n
  · have hh := (abs_le.mp (happrox 1 (by omega))).1
    simpa only [hzero,Nat.cast_one,Real.log_one,one_pow,mul_one] using (show (0:ℝ)<Real.log (W 1:ℝ) by
      norm_num at hh
      linarith)
  · have hh := abs_le.mp (happrox (n+1) (by omega))
    have hh' := abs_le.mp (happrox (n+1+1) (by omega))
    push_cast at hh hh'
    nlinarith [show (0:ℝ)≤n by positivity]

lemma sequence_unbounded (hW : ∀ j, 0<W j) (ha : 0<a)
    (happrox : ∀ j, 1≤j → |Real.log (W j:ℝ)-a*(j:ℝ)^2|≤c) (U : ℕ) : ∃ j, U<W j := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max ((U+c+1)/a+1) 1)
  have hn1 : 1<n := by exact_mod_cast lt_of_le_of_lt (le_max_right _ _) hn
  have hn' : (U+c+1)/a+1 < (n:ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hh := (abs_le.mp (happrox n (by omega))).1
  have hlog := Real.log_le_sub_one_of_pos (by exact_mod_cast hW n : (0:ℝ)<W n)
  have hn2 : (1:ℝ)<n := by exact_mod_cast hn1
  have hdiv : (U:ℝ)+c+1 < (n-1:ℝ)*a := (div_lt_iff₀ ha).mp (show ((U:ℝ)+c+1)/a < (n:ℝ)-1 by linarith)
  have hn3 : (n-1:ℝ)*a < a*(n:ℝ)^2 := by nlinarith [mul_lt_mul_of_pos_left (show (n:ℝ)-1 < (n:ℝ)^2 by nlinarith) ha]
  have hu : (U:ℝ)<W n := by linarith
  exact ⟨n,by exact_mod_cast hu⟩

lemma bracket_unique (hW : StrictMono W) (hunb : ∀ U, ∃ j, U<W j) (u : ℕ) :
    ∃! k : ℕ, 1≤k ∧ W k≤u+W 1 ∧ u+W 1<W (k+1) := by
  let j := Nat.find (hunb (u+W 1))
  have hj : u+W 1<W j := Nat.find_spec (hunb (u+W 1))
  have hj2 : 2≤j := by
    by_contra hn
    have hj1 : j≤1 := by omega
    have hh := hW.monotone hj1
    omega
  have hprev : W (j-1)≤u+W 1 := by
    by_contra h
    have : j≤j-1 := Nat.find_min' (hunb (u+W 1)) (m:=j-1) (by omega)
    omega
  refine ⟨j-1,⟨by omega,hprev,by simpa only [show j-1+1=j by omega] using hj⟩,?_⟩
  rintro k ⟨_,hk,hk'⟩
  apply le_antisymm
  · by_contra hn
    have hjk : j≤k := by omega
    have hh := hW.monotone hjk
    omega
  · by_contra hn
    have hkj : k+1≤j-1 := by omega
    have hh := hW.monotone hkj
    omega

lemma bracket_log {u k : ℕ} (hW : ∀ j, 0<W j) (ha : 0<a)
    (happrox : ∀ j, 1≤j → |Real.log (W j:ℝ)-a*(j:ℝ)^2|≤c)
    (hk : 1≤k) (hb : W k≤u+W 1 ∧ u+W 1<W (k+1)) :
      a*(k:ℝ)^2-c ≤ Real.log (u+W 1:ℕ) ∧
      Real.log (u+W 1:ℕ) < 4*a*(k:ℝ)^2+c := by
  have hp : (0:ℝ)<W k := by exact_mod_cast hW k
  have hU : (0:ℝ)<(u+W 1:ℕ) := by exact_mod_cast (show 0<u+W 1 by have := hW 1; omega)
  have hlo : Real.log (W k:ℝ)≤Real.log (u+W 1:ℕ) := Real.log_le_log hp (by exact_mod_cast hb.1)
  have hhi : Real.log (u+W 1:ℕ)<Real.log (W (k+1):ℝ) := Real.log_lt_log hU (by exact_mod_cast hb.2)
  have ha₁ := abs_le.mp (happrox k hk)
  have ha₂ := abs_le.mp (happrox (k+1) (by omega))
  have hk' : (1:ℝ)≤k := by exact_mod_cast hk
  constructor
  · linarith
  · have : ((k:ℝ)+1)^2≤4*(k:ℝ)^2 := by nlinarith
    push_cast at ha₂
    nlinarith [mul_le_mul_of_nonneg_left this ha.le]

lemma output_upper {u k : ℕ} (hW : ∀ j, 0<W j) (ha : 0<a) (_hc : 0≤c)
    (happrox : ∀ j, 1≤j → |Real.log (W j:ℝ)-a*(j:ℝ)^2|≤c)
    (hk : 1≤k) (hb : W k≤u+W 1 ∧ u+W 1<W (k+1)) :
      Real.log (W (k^2):ℝ) ≤ ((Real.log (u+W 1:ℕ)+c)^2)/a+c := by
  obtain ⟨hlo,_⟩ := bracket_log hW ha happrox hk hb
  have hg := (abs_le.mp (happrox (k^2) (by nlinarith))).2
  have hlog : 0≤Real.log (u+W 1:ℕ) := Real.log_natCast_nonneg _
  have hh : a*(k:ℝ)^2≤Real.log (u+W 1:ℕ)+c := by linarith
  have hsq := pow_le_pow_left₀ (by positivity : 0≤a*(k:ℝ)^2) hh 2
  have hmul := mul_le_mul_of_nonneg_right hg ha.le
  suffices Real.log (W (k^2):ℝ)-c ≤ (Real.log (u+W 1:ℕ)+c)^2/a by linarith
  apply (le_div_iff₀ ha).mpr
  push_cast at hmul
  nlinarith only [hmul,hsq]

lemma output_lower {u k : ℕ} (hW : ∀ j, 0<W j) (ha : 0<a) (hc : 0≤c)
    (happrox : ∀ j, 1≤j → |Real.log (W j:ℝ)-a*(j:ℝ)^2|≤c)
    (hk : 1≤k) (hb : W k≤u+W 1 ∧ u+W 1<W (k+1))
    (hu : 0<u) (hlarge : 9*c<Real.log (u:ℝ)) :
      (1/(128*a))*(Real.log (u:ℝ))^2 < Real.log (W (k^2):ℝ) := by
  have hlog := Real.log_natCast_nonneg u
  have huU : Real.log (u:ℝ) ≤ Real.log (u+W 1:ℕ) :=
    Real.log_le_log (by exact_mod_cast hu) (by exact_mod_cast (Nat.le_add_right u (W 1)))
  have hh := (bracket_log hW ha happrox hk hb).2
  have hu' : Real.log (u:ℝ) < 4*a*(k:ℝ)^2+c := lt_of_le_of_lt huU hh
  have hh' : 2*c<a*(k:ℝ)^2 := by linarith
  have hk' : (1:ℝ)≤k := by exact_mod_cast hk
  have hk2 : (1:ℝ)≤(k:ℝ)^2 := by nlinarith
  have hk4 : (k:ℝ)^2≤((k:ℝ)^2)^2 := by nlinarith
  have hl : Real.log (u:ℝ) < 8*a*(k:ℝ)^2 := by linarith
  have hsq := pow_lt_pow_left₀ hl hlog (by norm_num : (2:ℕ)≠0)
  have hg := (abs_le.mp (happrox (k^2) (by nlinarith))).1
  push_cast at hg
  have hc' : c<a*((k:ℝ)^2)^2/2 := by
    nlinarith [mul_le_mul_of_nonneg_left hk4 ha.le]
  have h128 : 0<128*a := by positivity
  have hcq : (Real.log (u:ℝ))^2/(128*a) < a*((k:ℝ)^2)^2/2 := by
    apply (div_lt_iff₀ h128).mpr
    nlinarith only [hsq]
  rw [one_div_mul_eq_div]
  linarith

lemma output_upper_log {u k : ℕ} (hW : ∀ j, 0<W j) (ha : 0<a) (hc : 0≤c)
    (happrox : ∀ j, 1≤j → |Real.log (W j:ℝ)-a*(j:ℝ)^2|≤c)
    (hk : 1≤k) (hb : W k≤u+W 1 ∧ u+W 1<W (k+1))
    (hu : 2≤u) (hWu : W 1≤u) (hcL : c≤Real.log (u:ℝ)) (hL : 1≤Real.log (u:ℝ)) :
      Real.log (W (k^2):ℝ) ≤ (9/a+1)*(Real.log (u:ℝ))^2 := by
  have hp : (0:ℝ)<u := by exact_mod_cast (show 0<u by omega)
  have huU : Real.log (u+W 1:ℕ)≤Real.log (2*(u:ℝ)) :=
    Real.log_le_log (by exact_mod_cast (show 0<u+W 1 by omega)) (by push_cast; exact_mod_cast (show u+W 1≤2*u by omega))
  have htwo : Real.log 2≤Real.log (u:ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hu)
  rw [Real.log_mul (by norm_num) hp.ne'] at huU
  have hh : Real.log (u+W 1:ℕ)+c ≤ 3*Real.log (u:ℝ) := by linarith
  have hsq := pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg (u+W 1)] : 0≤Real.log (u+W 1:ℕ)+c) hh 2
  have hh' := output_upper hW ha hc happrox hk hb
  have hl2 : c≤(Real.log (u:ℝ))^2 := by nlinarith
  have hdiv := (div_le_div_iff_of_pos_right ha).mpr hsq
  nlinarith only [hh',hdiv,hl2,show (3*Real.log (u:ℝ))^2/a=9/a*(Real.log (u:ℝ))^2 by ring]

theorem eventual_output (hW : ∀ j, 0<W j) (ha : 0<a) (hc : 0≤c)
    (happrox : ∀ j, 1≤j → |Real.log (W j:ℝ)-a*(j:ℝ)^2|≤c) :
    ∃ u₀ : ℕ, 4≤u₀ ∧ ∀ u≥u₀, ∀ k, 1≤k →
      W k≤u+W 1 ∧ u+W 1<W (k+1) →
      (1/(128*a))*(Real.log (u:ℝ))^2 < Real.log (W (k^2):ℝ) ∧
      Real.log (W (k^2):ℝ) < (u:ℝ)*Real.log (u:ℝ) := by
  let B : ℝ := 9/a+1
  have hB : 0<B := by dsimp [B]; positivity
  have hε : 0<1/(2*B) := by positivity
  have hsmall := Real.isLittleO_log_id_atTop.bound hε
  have hsmallN := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually hsmall
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_gt_atTop (max (9*c) 1)
  have he : ∀ᶠ u : ℕ in Filter.atTop,
      4≤u ∧ W 1≤u ∧ 9*c<Real.log (u:ℝ) ∧ 1<Real.log (u:ℝ) ∧
      B*Real.log (u:ℝ)<u := by
    filter_upwards [hsmallN,hlog,Filter.eventually_ge_atTop 4,Filter.eventually_ge_atTop (W 1)] with u hs hl hu hw
    have hl0 : 0≤Real.log (u:ℝ) := Real.log_natCast_nonneg u
    simp only [Real.norm_eq_abs,abs_of_nonneg hl0,abs_of_nonneg (show (0:ℝ)≤(u:ℝ) by positivity),id_eq] at hs
    have hm := mul_le_mul_of_nonneg_left hs hB.le
    have hb : B*(1/(2*B)*(u:ℝ))=(u:ℝ)/2 := by field_simp
    rw [hb] at hm
    refine ⟨hu,hw,lt_of_le_of_lt (le_max_left _ _) hl,lt_of_le_of_lt (le_max_right _ _) hl,?_⟩
    have hu' : (0:ℝ)<u := by exact_mod_cast (show 0<u by omega)
    linarith
  obtain ⟨u₀,hu₀⟩ := Filter.eventually_atTop.mp he
  refine ⟨max 4 u₀,le_max_left _ _,?_⟩
  intro u hu k hk hb
  obtain ⟨hu4,hw,hl,hL,hsmall⟩ := hu₀ u ((le_max_right _ _).trans hu)
  refine ⟨output_lower hW ha hc happrox hk hb (by omega) hl,?_⟩
  have he := output_upper_log hW ha hc happrox hk hb (by omega) hw (by linarith) hL.le
  have hh := mul_lt_mul_of_pos_right hsmall (by linarith : 0<Real.log (u:ℝ))
  dsimp [B] at hh
  nlinarith only [he,hh]

end SingleFold.GrowthEstimate

namespace SingleFold.HeightWindow

lemma index_separation {k r : ℕ} (h : r ≠ k ^ 2) :
    1 ≤ |(k : ℝ) ^ 2 - (r : ℝ)| := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have : (r : ℝ) + 1 ≤ (k : ℝ) ^ 2 := by exact_mod_cast hlt
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have : (k : ℝ) ^ 2 + 1 ≤ (r : ℝ) := by exact_mod_cast hgt
    rw [abs_of_nonpos (by linarith)]
    linarith

lemma separated_window {a c K e : ℝ} {k r : ℕ}
    (hc : 0 ≤ c) (hK : 6 * c < K) (ha : K < 2 * a - 6 * c)
    (he : |e| ≤ 6 * c) :
    |2 * a * ((k : ℝ) ^ 2 - (r : ℝ)) + e| ≤ K ↔ r = k ^ 2 := by
  have ha0 : 0 < a := by linarith
  constructor
  · intro hwin
    by_contra hne
    have hsep := index_separation hne
    have htri := abs_add_le ((2 * a * ((k : ℝ) ^ 2 - (r : ℝ))) + e) (-e)
    have hb : |2 * a * ((k : ℝ) ^ 2 - (r : ℝ))| ≤ K + 6 * c := by
      calc
        |2 * a * ((k : ℝ) ^ 2 - (r : ℝ))| =
            |(2 * a * ((k : ℝ) ^ 2 - (r : ℝ)) + e) + -e| := by congr 1; ring
        _ ≤ |2 * a * ((k : ℝ) ^ 2 - (r : ℝ)) + e| + |-e| := htri
        _ ≤ K + 6 * c := by rw [abs_neg]; linarith
    rw [abs_mul, abs_of_pos (show 0 < 2 * a by positivity)] at hb
    nlinarith
  · intro h
    subst r
    simp only [Nat.cast_pow, sub_self, mul_zero, zero_add]
    exact he.trans hK.le

lemma multiplicative_window {L D K : ℝ} (hL : 0 < L) (hD : 0 < D) (hK : 0 < K) :
    (L ≤ K * D ∧ D ≤ K * L) ↔ |Real.log L - Real.log D| ≤ Real.log K := by
  rw [abs_sub_le_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    have h₁' := Real.log_le_log hL h₁
    have h₂' := Real.log_le_log hD h₂
    rw [Real.log_mul hK.ne' hD.ne'] at h₁'
    rw [Real.log_mul hK.ne' hL.ne'] at h₂'
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    constructor
    · apply (Real.log_le_log_iff hL (mul_pos hK hD)).mp
      rw [Real.log_mul hK.ne' hD.ne']
      linarith
    · apply (Real.log_le_log_iff hD (mul_pos hK hL)).mp
      rw [Real.log_mul hK.ne' hL.ne']
      linarith

theorem square_window {W : ℕ → ℕ} {a c : ℝ} {κ k r : ℕ}
    (hW : ∀ j, 0 < W j)
    (happrox : ∀ j, 1 ≤ j → |Real.log (W j : ℝ) - a * (j : ℝ) ^ 2| ≤ c)
    (hc : 0 ≤ c) (hκ : 0 < κ) (h₁ : 6 * c < Real.log κ)
    (h₂ : Real.log κ < 2 * a - 6 * c) (hk : 1 ≤ k) (hr : 1 ≤ r) :
    (W (2 * k) * W r * W 1 ≤ κ * (W k ^ 2 * W (r + 1)) ∧
      W k ^ 2 * W (r + 1) ≤ κ * (W (2 * k) * W r * W 1)) ↔ r = k ^ 2 := by
  have pos (j : ℕ) : (0 : ℝ) < W j := by exact_mod_cast hW j
  let L : ℝ := (W (2 * k) : ℝ) * W r * W 1
  let D : ℝ := (W k : ℝ) ^ 2 * W (r + 1)
  have hL : 0 < L := mul_pos (mul_pos (pos _) (pos _)) (pos _)
  have hD : 0 < D := mul_pos (pow_pos (pos _) _) (pos _)
  have prod_iff :
      (W (2 * k) * W r * W 1 ≤ κ * (W k ^ 2 * W (r + 1)) ∧
        W k ^ 2 * W (r + 1) ≤ κ * (W (2 * k) * W r * W 1)) ↔
      (L ≤ (κ : ℝ) * D ∧ D ≤ (κ : ℝ) * L) := by
    dsimp [L, D]
    constructor <;> rintro ⟨h, h'⟩
    · exact ⟨by exact_mod_cast h, by exact_mod_cast h'⟩
    · exact ⟨by exact_mod_cast h, by exact_mod_cast h'⟩
  rw [prod_iff, multiplicative_window hL hD (by exact_mod_cast hκ)]
  let err (j : ℕ) := Real.log (W j : ℝ) - a * (j : ℝ) ^ 2
  have herr (j : ℕ) (hj : 1 ≤ j) : -c ≤ err j ∧ err j ≤ c :=
    abs_le.mp (happrox j hj)
  have herr2k := herr (2 * k) (by omega)
  have herrr := herr r hr
  have herr1 := herr 1 (by omega)
  have herrk := herr k hk
  have herrr1 := herr (r + 1) (by omega)
  let e := err (2 * k) + err r + err 1 - 2 * err k - err (r + 1)
  have he : |e| ≤ 6 * c := by
    apply abs_le.mpr
    dsimp [e]
    constructor <;> linarith [herr2k.1, herr2k.2, herrr.1, herrr.2,
      herr1.1, herr1.2, herrk.1, herrk.2, herrr1.1, herrr1.2]
  have formula : Real.log L - Real.log D =
      2 * a * ((k : ℝ) ^ 2 - (r : ℝ)) + e := by
    dsimp [L, D, e, err]
    rw [Real.log_mul (mul_pos (pos _) (pos _)).ne' (pos _).ne',
      Real.log_mul (pos _).ne' (pos _).ne',
      Real.log_mul (pow_pos (pos _) _).ne' (pos _).ne', Real.log_pow]
    push_cast
    ring
  rw [formula]
  exact separated_window hc h₁ h₂ he

end SingleFold.HeightWindow

end OAI
