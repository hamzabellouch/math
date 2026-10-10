import OAI.Combinatorics.ListHadwiger.ColorBins

namespace OAI

namespace LinearListHadwiger.Sampling
open Filter

theorem parameter_range_cutoff : ∀ᶠ t : ℝ in atTop,
    1 < t ∧ 1 ≤ Real.log t ∧ ∀ r : ℝ,
      t/Real.log t ≤ r → r ≤ 4*t →
      400 ≤ r ∧ 1 ≤ max 1 (t/r) ∧ max 1 (t/r) ≤ Real.log t ∧
      t ≤ r*max 1 (t/r) ∧ r*max 1 (t/r) ≤ 4*t := by
  have hl := (Real.isLittleO_log_id_atTop).bound (show (0:ℝ)<1/400 by norm_num)
  have hg := (Real.tendsto_log_atTop).eventually (eventually_ge_atTop (1:ℝ))
  filter_upwards [eventually_gt_atTop (1:ℝ),hl,hg] with t ht hl hg
  have htpos : 0 < t := by linarith
  have hlog : 0 < Real.log t := by linarith
  have hl' : Real.log t ≤ (1/400:ℝ)*t := by
    simpa only [id_eq,Real.norm_eq_abs,abs_of_pos hlog,abs_of_pos htpos] using hl
  have hr0 : 400 ≤ t/Real.log t := by
    apply (le_div_iff₀ hlog).mpr
    linarith
  refine ⟨ht,hg,?_⟩
  intro r hr hr'
  have hr400 := hr0.trans hr
  have hrpos : 0 < r := by linarith
  have htr : t/r ≤ Real.log t := by
    apply (div_le_iff₀ hrpos).mpr
    have hh := (div_le_iff₀ hlog).mp hr
    nlinarith
  refine ⟨hr400,le_max_left _ _,max_le hg htr,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left (le_max_right (1:ℝ) (t/r)) hrpos.le
    field_simp at hh
    nlinarith
  · rw [mul_max_of_nonneg _ _ hrpos.le]
    simp only [mul_one,mul_div_cancel₀ _ hrpos.ne']
    exact max_le hr' (by linarith)

lemma floor_parameter {t r y : ℝ} (ht : 0 < t) (hr : 400 ≤ r)
    (hy : 1 ≤ y) (hy' : t/r ≤ y) :
    1 ≤ ⌊r/200⌋₊ ∧ r/400 ≤ (⌊r/200⌋₊ : ℝ) ∧
    (⌈t/(⌊r/200⌋₊ : ℝ)⌉₊ : ℝ) ≤ 401*y := by
  have hrpos : 0 < r := by linarith
  have hfloor := Nat.lt_floor_add_one (r/200)
  have hfloorle := Nat.floor_le (by positivity : 0 ≤ r/200)
  have hx : 1 ≤ ⌊r/200⌋₊ := by
    apply (Nat.one_le_floor_iff _).mpr
    linarith
  have hx' : r/400 ≤ (⌊r/200⌋₊ : ℝ) := by linarith
  have hxpos : (0:ℝ) < ⌊r/200⌋₊ := by exact_mod_cast (by omega : 0 < ⌊r/200⌋₊)
  refine ⟨hx,hx',?_⟩
  have hd : t/(⌊r/200⌋₊ : ℝ) ≤ 400*(t/r) := by
    apply (div_le_iff₀ hxpos).mpr
    apply (le_of_mul_le_mul_right ?_ hrpos)
    field_simp
    nlinarith
  have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ t/(⌊r/200⌋₊ : ℝ))
  nlinarith

lemma sample_size_parameters {t n r y : ℝ} {B : ℕ}
    (ht : 1 < t) (hn : 1 ≤ n) (hnt : n ≤ t^(11/10:ℝ))
    (hr : 400 ≤ r) (hy : 1 ≤ y) (hry : t ≤ r*y) (hB : 1 ≤ B) :
    1 ≤ ⌈B*r*Real.log (2*y)⌉₊ ∧
    (⌈B*r*Real.log (2*y)⌉₊ : ℝ) ≤ (B+1)*r*Real.log (2*y) ∧
    1 ≤ ⌈n/r⌉₊ ∧ (⌈n/r⌉₊ : ℝ) ≤ 2*t^(1/10:ℝ)*y := by
  have htpos : 0 < t := by linarith
  have hrpos : 0 < r := by linarith
  have hypos : 0 < y := by linarith
  have hB' : (1:ℝ) ≤ B := by exact_mod_cast hB
  have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  have hlog : (1/2:ℝ) ≤ Real.log (2*y) := by
    have hh : Real.log 2 ≤ Real.log (2*y) := Real.log_le_log (by norm_num) (by linarith)
    norm_num at htwo
    linarith
  have hlarge : 1 ≤ r*Real.log (2*y) := by nlinarith
  have hsample : 0 < (B:ℝ)*r*Real.log (2*y) := by positivity
  have hN : 1 ≤ ⌈B*r*Real.log (2*y)⌉₊ := by
    have hh := Nat.le_ceil ((B:ℝ)*r*Real.log (2*y))
    by_contra h
    have hh' : ⌈B*r*Real.log (2*y)⌉₊=0 := by omega
    simp only [hh',Nat.cast_zero] at hh
    linarith
  have hM : 1 ≤ ⌈n/r⌉₊ := by
    have hh := Nat.le_ceil (n/r)
    have hnr : 0 < n/r := div_pos (by linarith) hrpos
    by_contra h
    have hh' : ⌈n/r⌉₊=0 := by omega
    simp only [hh',Nat.cast_zero] at hh
    linarith
  refine ⟨hN,?_,hM,?_⟩
  · have hh := Nat.ceil_lt_add_one hsample.le
    nlinarith
  · have hpow : t^(11/10:ℝ)=t^(1/10:ℝ)*t := by
      rw [←Real.rpow_add_one htpos.ne']
      norm_num
    have hp : 1 ≤ t^(1/10:ℝ) := Real.one_le_rpow ht.le (by norm_num)
    have hnratio : n/r ≤ t^(1/10:ℝ)*y := by
      apply (div_le_iff₀ hrpos).mpr
      calc
        n ≤ t^(11/10:ℝ) := hnt
        _ = t^(1/10:ℝ)*t := hpow
        _ ≤ t^(1/10:ℝ)*(r*y) := mul_le_mul_of_nonneg_left hry (by positivity)
        _ = _ := by ring
    have hh := Nat.ceil_lt_add_one (by positivity : 0 ≤ n/r)
    have hone : 1 ≤ t^(1/10:ℝ)*y := by nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hy)]
    nlinarith

lemma trial_count_parameters {t r y : ℝ} {B : ℕ}
    (ht : 0 < t) (hr : 400 ≤ r) (hy : 1 ≤ y) (hy' : t/r ≤ y)
    (hry : r*y ≤ 4*t)
    (hN : (⌈B*r*Real.log (2*y)⌉₊ : ℝ) ≤ (B+1)*r*Real.log (2*y)) :
    ((⌈t/(⌊r/200⌋₊ : ℝ)⌉₊^2 * ⌈B*r*Real.log (2*y)⌉₊ : ℕ) : ℝ) ≤
      (4*401^2*(B+1):ℝ)*t*y*Real.log (2*y) := by
  have hlog : 0 ≤ Real.log (2*y) := Real.log_nonneg (by linarith)
  have hq := (floor_parameter ht hr hy hy').2.2
  have hq' : (⌈t/(⌊r/200⌋₊ : ℝ)⌉₊ : ℝ)^2 ≤ 401^2*y^2 := by
    calc
      _ ≤ (401*y)^2 := by gcongr
      _ = _ := by ring
  push_cast at hN ⊢
  calc
    _ ≤ (401^2*y^2)*((B+1)*r*Real.log (2*y)) := by gcongr
    _ = (401^2*(B+1)*y*Real.log (2*y))*(r*y) := by ring
    _ ≤ (401^2*(B+1)*y*Real.log (2*y))*(4*t) := by gcongr
    _ = _ := by ring

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling
open Filter

theorem concentration_numeric_cutoff {A δ : ℝ} (hA : 0 < A) (hδ : 0 < δ) :
    ∀ᶠ t : ℝ in atTop, 1 < t ∧ ∀ y r s M : ℝ,
      1 ≤ y → y ≤ Real.log t → t/y ≤ r →
      0 < s → s ≤ A*t*y*Real.log (2*y) →
      0 < M → M ≤ 2*t^(1/10:ℝ)*y →
      t^(7/10:ℝ) ≤ (δ*r)^2/(2*s*(2*M)^2) := by
  have heps : 0 < δ^2/(64*A) := by positivity
  have hlog := (isLittleO_log_rpow_rpow_atTop (6:ℝ)
    (show (0:ℝ)<1/10 by norm_num)).bound heps
  filter_upwards [eventually_gt_atTop (1:ℝ),hlog] with t ht hlog
  have htpos : 0 < t := by linarith
  have hln : 0 ≤ Real.log t := Real.log_nonneg ht.le
  have hp : 0 < t^(1/10:ℝ) := Real.rpow_pos_of_pos htpos _
  have hu : 0 < t^(7/10:ℝ) := Real.rpow_pos_of_pos htpos _
  have hh : (Real.log t)^6 ≤ δ^2/(64*A)*t^(1/10:ℝ) := by
    rw [←Real.rpow_natCast (Real.log t) 6]
    simpa only [Nat.cast_ofNat,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hln (6:ℝ)),
      abs_of_nonneg hp.le] using hlog
  refine ⟨ht,?_⟩
  intro y r s M hy hyt hyr hs hs' hM hM'
  have hypos : 0 < y := by linarith
  have hr : 0 < r := lt_of_lt_of_le (div_pos htpos hypos) hyr
  have hly : 0 ≤ Real.log (2*y) := Real.log_nonneg (by linarith)
  have hl : Real.log (2*y) ≤ 2*y := Real.log_le_self (by positivity)
  have hy6 : y^6 ≤ (Real.log t)^6 := by gcongr
  have hnum : 64*A*y^6 ≤ δ^2*t^(1/10:ℝ) := by
    have hh' := hy6.trans hh
    have h64 : 0 < 64*A := by positivity
    have hh'' := (mul_le_mul_of_nonneg_left hh' h64.le)
    field_simp at hh'' ⊢
    nlinarith
  have hry : t ≤ r*y := (div_le_iff₀ hypos).mp hyr
  have hsq : t^2 ≤ r^2*y^2 := by
    calc
      t^2 ≤ (r*y)^2 := by gcongr
      _ = _ := by ring
  have hpow : t*(t^(1/10:ℝ))^3*t^(7/10:ℝ)=t^2 := by
    have hh : (t^(1/10:ℝ))^3=t^(3/10:ℝ) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul htpos.le]
      norm_num
    rw [hh]
    calc
      _ = t^(1:ℝ)*t^(3/10:ℝ)*t^(7/10:ℝ) := by rw [Real.rpow_one]
      _ = t^(2:ℝ) := by rw [←Real.rpow_add htpos,←Real.rpow_add htpos]; norm_num
      _ = _ := by rw [Real.rpow_two]
  have hb : 2*s*(2*M)^2*t^(7/10:ℝ)*y^2 ≤ δ^2*t^2 := by
    calc
      _ ≤ 2*(A*t*y*Real.log (2*y))*(2*(2*t^(1/10:ℝ)*y))^2*t^(7/10:ℝ)*y^2 := by
        gcongr
      _ ≤ 2*(A*t*y*(2*y))*(2*(2*t^(1/10:ℝ)*y))^2*t^(7/10:ℝ)*y^2 := by gcongr
      _ = (64*A*y^6)*(t*(t^(1/10:ℝ))^2*t^(7/10:ℝ)) := by ring
      _ ≤ (δ^2*t^(1/10:ℝ))*(t*(t^(1/10:ℝ))^2*t^(7/10:ℝ)) := by gcongr
      _ = δ^2*(t*(t^(1/10:ℝ))^3*t^(7/10:ℝ)) := by ring
      _ = δ^2*t^2 := by rw [hpow]
  have hb' : (2*s*(2*M)^2*t^(7/10:ℝ))*y^2 ≤ (δ*r)^2*y^2 := by
    calc
      _ ≤ δ^2*t^2 := hb
      _ ≤ δ^2*(r^2*y^2) := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = _ := by ring
  have hc := (mul_le_mul_iff_left₀ (sq_pos_of_pos hypos)).mp hb'
  apply (le_div_iff₀ (by positivity : 0 < 2*s*(2*M)^2)).mpr
  nlinarith

theorem uniform_bounded_differences {A δ : ℝ} (hA : 0 < A) (hδ : 0 < δ) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ y r M : ℝ,
      1 ≤ y → y ≤ Real.log t → t/y ≤ r → 0 < M →
      M ≤ 2*t^(1/10:ℝ)*y →
      ∀ (ι Ω : Type) [Fintype ι] [Fintype Ω] [DecidableEq ι],
      1 ≤ Fintype.card ι → (Fintype.card ι : ℝ) ≤ A*t*y*Real.log (2*y) →
      ∀ (μ : ι → Ω → ℝ), (∀ i ω, 0 ≤ μ i ω) → (∀ i, ∑ ω, μ i ω=1) →
      ∀ f : (ι → Ω) → ℝ,
      (∀ i x x', (∀ j, j ≠ i → x j=x' j) → |f x-f x'| ≤ 2*M) →
      probability (productMass μ) (fun x => δ*r ≤ |f x-expectation (productMass μ) f|)
        ≤ 2*Real.exp (-t^(7/10:ℝ)) := by
  classical
  obtain ⟨T,hT⟩ := eventually_atTop.mp (concentration_numeric_cutoff hA hδ)
  refine ⟨T,?_⟩
  intro t ht y r M hy hyt hyr hM hM' ι Ω _ _ _ hn hs μ hμ hsum f hf
  have htc := hT t ht
  have hr : 0 < r := lt_of_lt_of_le (div_pos (by linarith [htc.1]) (by linarith)) hyr
  have hn' : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast (by omega : 0 < Fintype.card ι)
  have hc := htc.2 y r (Fintype.card ι) M hy hyt hyr hn' hs hM hM'
  have hb := bounded_differences_general hn μ hμ hsum f
    (by positivity : 0 < 2*M) (mul_pos hδ hr) hf
  refine hb.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
  apply Real.exp_le_exp.mpr
  rw [neg_div]
  exact neg_le_neg hc

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling
open Filter

theorem source_uniform_concentration {B : ℕ} (hB : 1 ≤ B) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℝ, ∀ t n r : ℝ, T ≤ t → 1 ≤ n → n ≤ t^(11/10:ℝ) →
      t/Real.log t ≤ r → r ≤ 4*t →
      let y := max 1 (t/r)
      let N := ⌈B*r*Real.log (2*y)⌉₊
      let M := ⌈n/r⌉₊
      let q := ⌈t/(⌊r/200⌋₊ : ℝ)⌉₊^2
      ∀ (ι Ω : Type) [Fintype ι] [Fintype Ω] [DecidableEq ι],
      1 ≤ Fintype.card ι → Fintype.card ι ≤ q*N →
      ∀ (μ : ι → Ω → ℝ), (∀ i ω, 0 ≤ μ i ω) → (∀ i, ∑ ω, μ i ω=1) →
      ∀ f : (ι → Ω) → ℝ,
      (∀ i x x', (∀ j, j ≠ i → x j=x' j) → |f x-f x'| ≤ 2*M) →
      probability (productMass μ) (fun x => δ*r ≤ |f x-expectation (productMass μ) f|)
        ≤ 2*Real.exp (-t^(7/10:ℝ)) := by
  classical
  let A : ℝ := 4*401^2*(B+1)
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨T₁,hT₁⟩ := eventually_atTop.mp parameter_range_cutoff
  obtain ⟨T₂,hT₂⟩ := uniform_bounded_differences hA hδ
  refine ⟨max T₁ T₂,?_⟩
  intro t n r ht hn hnt hrl hru
  dsimp only
  intro ι Ω _ _ _ hi hiq μ hμ hsum f hf
  have hp := hT₁ t ((le_max_left _ _).trans ht)
  obtain ⟨hr,hy,hyt,hry,hry'⟩ := hp.2.2 r hrl hru
  obtain ⟨hN,hN',hM,hM'⟩ := sample_size_parameters hp.1 hn hnt hr hy hry hB
  have hs := trial_count_parameters (by linarith [hp.1]) hr hy
    (le_max_right (1:ℝ) (t/r)) hry' hN'
  have hypos : 0 < max 1 (t/r) := by linarith
  have hyr : t/max 1 (t/r) ≤ r := (div_le_iff₀ hypos).mpr (by nlinarith [hry])
  apply hT₂ t ((le_max_right _ _).trans ht) (max 1 (t/r)) r ⌈n/r⌉₊ hy hyt hyr
    (by exact_mod_cast (by omega : 0 < ⌈n/r⌉₊)) hM' ι Ω hi
  · exact (show (Fintype.card ι : ℝ) ≤
      ((⌈t/(⌊r/200⌋₊ : ℝ)⌉₊^2*⌈B*r*Real.log (2*max 1 (t/r))⌉₊ : ℕ) : ℝ)
      by exact_mod_cast hiq).trans hs
  · exact hμ
  · exact hsum
  · exact hf

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling

lemma attachment_size_parameters {t r y : ℝ} (ht : 0 < t) (hr : 400 ≤ r)
    (hru : r ≤ 4*t) (hy : 1 ≤ y) (hy' : t/r ≤ y) :
    ((⌊r/200⌋₊ * ⌈t/(⌊r/200⌋₊ : ℝ)⌉₊^2 : ℕ) : ℝ) ≤ 403*t*y := by
  have hrpos : 0 < r := by linarith
  obtain ⟨hxp,hxlow,hceil⟩ := floor_parameter ht hr hy hy'
  let x : ℝ := ⌊r/200⌋₊
  have hxpos : 0 < x := by dsimp [x]; exact_mod_cast (by omega : 0 < ⌊r/200⌋₊)
  have hxup : x ≤ r/200 := Nat.floor_le (by positivity)
  have hc := Nat.ceil_lt_add_one (show 0 ≤ t/x by positivity)
  have htf : t^2/x ≤ 400*t*(t/r) := by
    apply (div_le_iff₀ hxpos).mpr
    apply le_of_mul_le_mul_right ?_ hrpos
    dsimp [x] at *
    field_simp
    nlinarith [mul_nonneg (show 0 ≤ t^2 by positivity) (show 0 ≤ 400*(⌊r/200⌋₊:ℝ)-r by linarith)]
  have hc' : (⌈t/x⌉₊ : ℝ)^2 ≤ (t/x+1)^2 := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).mpr hc.le
  have he : x*(t/x+1)^2=t^2/x+2*t+x := by field_simp; ring
  push_cast
  change x*(⌈t/x⌉₊ : ℝ)^2 ≤ _
  calc
    _ ≤ x*(t/x+1)^2 := mul_le_mul_of_nonneg_left hc' hxpos.le
    _ = t^2/x+2*t+x := he
    _ ≤ 400*t*(t/r)+2*t+r/200 := by gcongr
    _ ≤ 403*t*y := by nlinarith

lemma attachment_budget {t r y : ℝ} {γ : ℕ} (ht : 0 < t) (hr : 400 ≤ r)
    (hru : r ≤ 4*t) (hy : 1 ≤ y) (hy' : t/r ≤ y) (hγ : 1 ≤ γ) :
    let x := ⌊r/200⌋₊
    let q := ⌈t/(x:ℝ)⌉₊^2
    let k := ⌈(1000000*γ:ℝ)*t*y⌉₊
    r ≤ k ∧ 64*(2*x*q) < k ∧ γ*(2*x*q) ≤ k/32 := by
  dsimp only
  have hxq := attachment_size_parameters ht hr hru hy hy'
  have hypos : 0 < y := by linarith
  have hγ' : (1:ℝ) ≤ γ := by exact_mod_cast hγ
  have hty : 0 < t*y := mul_pos ht hypos
  have hk := Nat.le_ceil ((1000000*γ:ℝ)*t*y)
  have hkR : 64*((2*⌊r/200⌋₊*⌈t/(⌊r/200⌋₊:ℝ)⌉₊^2:ℕ):ℝ) <
      ⌈(1000000*γ:ℝ)*t*y⌉₊ := by
    push_cast at hxq ⊢
    nlinarith [mul_nonneg (show 0 ≤ (γ:ℝ)-1 by linarith) hty.le]
  have hkG : (32*(γ*(2*⌊r/200⌋₊*⌈t/(⌊r/200⌋₊:ℝ)⌉₊^2)):ℕ) ≤
      ⌈(1000000*γ:ℝ)*t*y⌉₊ := by
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    push_cast at hxq
    have hh := mul_le_mul_of_nonneg_left hxq (show (0:ℝ)≤64*γ by positivity)
    nlinarith
  refine ⟨?_,by exact_mod_cast hkR,?_⟩
  · nlinarith [mul_nonneg (show 0 ≤ (γ:ℝ)-1 by linarith) hty.le]
  · exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by simpa [Nat.mul_comm] using hkG)

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling
open Finset ConnectivityTests
variable {V Ω : Type} [Fintype V] [DecidableEq V] [Fintype Ω]

theorem complement_failure (G : SimpleGraph V) [DecidableRel G.Adj]
    {n r ε : ℝ} {k : ℕ} (hk : 64 ≤ k) (hr : 0 < r) (hrk : r ≤ k)
    (hord : (Fintype.card V : ℝ) ≤ n) (hconn : KConnectedOn G univ k)
    {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (U : Ω → Finset V)
    (hsurv : ∀ v, probability μ (fun ω => v ∈ U ω) ≤ 1/10000)
    (hε : 0 ≤ ε)
    (htail : ∀ A : Finset V, probability μ (fun ω => r/100 ≤
      |((U ω ∩ A).card : ℝ)-expectation μ (fun z => ((U z ∩ A).card : ℝ))|) ≤ ε) :
    probability μ (fun ω => ¬((∀ v, k ≤ 2*((univ \ U ω).filter (G.Adj v)).card) ∧
      KConnectedOn G (univ \ U ω) (k/32))) ≤
      (n+(n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1))*ε := by
  classical
  obtain ⟨F,hFcard,hF,hFtest⟩ := cut_test G hk hord hconn
  have hD (v : V) : ∃ D ⊆ Density.neighbors G univ v, D.card=k :=
    exists_subset_card_eq (Knitting.min_degree G hconn (mem_univ v))
  choose D hD hDc using hD
  let Idx := V ⊕ ↥F
  let A : Idx → Finset V := fun i => match i with
    | .inl v => D v
    | .inr E => endpoints E.val
  let bad : Idx → Ω → Prop := fun i ω => r/100 ≤
    |((U ω ∩ A i).card : ℝ)-expectation μ (fun z => ((U z ∩ A i).card : ℝ))|
  have hbad (i : Idx) : probability μ (bad i) ≤ ε := htail (A i)
  have hgood (ω : Ω) (havoid : ∀ i, ¬bad i ω) :
      (∀ v, k ≤ 2*((univ \ U ω).filter (G.Adj v)).card) ∧
      KConnectedOn G (univ \ U ω) (k/32) := by
    have hsmall (i : Idx) (hAk : (A i).card ≤ k) : 32*(U ω ∩ A i).card < k := by
      have he := expectation_inter_card_le U hsurv (A i)
      have hAc : ((A i).card : ℝ) ≤ k := by exact_mod_cast hAk
      have hm : expectation μ (fun z => ((U z ∩ A i).card : ℝ)) ≤ (k:ℝ)/10000 := by
        nlinarith
      have hdev := (abs_lt.mp (lt_of_not_ge (havoid i))).2
      have hkpos : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hh : (32:ℝ)*((U ω ∩ A i).card : ℝ) < k := by
        nlinarith
      exact_mod_cast hh
    have hneigh (v : V) : k ≤ 2*((univ \ U ω).filter (G.Adj v)).card := by
      have hc := hsmall (.inl v) (by dsimp [A]; exact (hDc v).le)
      have hd : (D v \ U ω).card+(D v ∩ U ω).card=k := by
        rw [card_sdiff_add_card_inter,hDc]
      have hsub : D v \ U ω ⊆ (univ \ U ω).filter (G.Adj v) := by
        intro w hw
        obtain ⟨hwD,hwU⟩ := mem_sdiff.mp hw
        have hadj := hD v hwD
        simp only [Density.neighbors,mem_filter,mem_univ,true_and] at hadj
        exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,hwU⟩,hadj⟩
      have hcard := card_le_card hsub
      dsimp [A] at hc
      rw [inter_comm] at hc
      omega
    refine ⟨hneigh,hFtest (U ω) hneigh ?_⟩
    intro E hE
    have he := (hF E hE).1
    have hcard : (endpoints E).card ≤ k := by
      have hb := endpoints_card_le E
      have hd := Nat.div_mul_le_self k 8
      omega
    have hc := hsmall (.inr ⟨E,hE⟩) hcard
    simpa [A,inter_comm] using hc
  have hprob : probability μ (fun ω => ¬((∀ v, k ≤ 2*((univ \ U ω).filter (G.Adj v)).card) ∧
      KConnectedOn G (univ \ U ω) (k/32))) ≤ probability μ (fun ω => ∃ i, bad i ω) := by
    apply probability_mono hμ
    intro ω h
    by_contra hn
    push Not at hn
    exact h (hgood ω hn)
  calc
    _ ≤ probability μ (fun ω => ∃ i, bad i ω) := hprob
    _ ≤ ∑ i, probability μ (bad i) := probability_union_le hμ bad
    _ ≤ ∑ _ : Idx, ε := sum_le_sum (fun i _ => hbad i)
    _ = ((Fintype.card V : ℝ)+F.card)*ε := by simp [Idx]
    _ ≤ _ := by gcongr

end LinearListHadwiger.Sampling

end OAI
