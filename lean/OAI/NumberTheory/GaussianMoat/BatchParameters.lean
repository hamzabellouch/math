import OAI.NumberTheory.GaussianMoat.WindowParameters

namespace OAI

namespace GaussianMoat
open scoped BigOperators Classical

theorem one_step_coverage (s : SplitSieve) (D : ℝ) (N : ℕ)
    (mid bot : List ℕ) (b q n : ℕ) (e ebase : ℝ)
    (u : s.SignedIndex → ℝ)
    (hm : EntropyBand s D mid 0 b e)
    (hb : EntropyBand s D bot N q ebase)
    (hb0 : 0<b) (hbk : b≤ s.primes.card) (hq0 : 0<q) (hqk : q≤ s.primes.card)
    (hN : 1≤bot.sum+N) (hn : 0<n)
    (hprime : ∀ i, Real.exp 100≤(s.signedPrime i:ℝ))
    (hu : ∀ i, 0<u i)
    (hbase : ebase*s.meanLog≤Real.exp (-100)/(512*640000))
    (hgap : e*s.meanLog+n*(Real.log 36+2*Real.log (D*(bot.sum+N)))/b<1/256)
    (herr : ∀ i, (s.signedPrime i:ℝ)*Real.exp
      (-(n:ℝ)*(1/64)^2*u i/(2*(s.signedPrime i:ℝ)))≤1/640000) :
    CoverageDerivation s D N (mid++bot) (1/4) u (1/100) := by
  let c : ℝ := Real.exp (-100)/512
  let u' : s.SignedIndex → ℝ := fun i => Real.exp (-100)/64*(s.signedPrime i:ℝ)
  let C : s.SignedIndex → ℝ := fun i => Real.exp (-100)*(s.signedPrime i:ℝ)
  have hc : 0<c := by dsimp [c]; positivity
  have htail : CoverageDerivation s D N bot (1/4+4*(1/64)) u' (1/640000) := by
    apply CoverageDerivation.base bot q (1/4+4*(1/64)) c ebase (1/640000) u' hb hq0 hqk
    · norm_num
    · exact hc
    · intro i; dsimp [c,u']; ring_nf; exact le_rfl
    · apply (div_le_iff₀ hc).mpr
      dsimp [c]
      linarith only [hbase]
  apply CoverageDerivation.step mid bot b n (1/4) (1/64) (1/640000) (1/100)
    (1/640000) e 100 u u' C hm htail hN hn hb0 hbk
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hu
  · norm_num
  · norm_num only [mul_one,one_mul,div_div]
    have hl2 : Real.log 2≤1 := by simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    have hl : Real.log (12800:ℝ)≤14 := by
      have hh := Real.log_le_log (by norm_num : (0:ℝ)<12800) (by norm_num : (12800:ℝ)≤2^14)
      rw [Real.log_pow] at hh
      norm_num at hh
      linarith only [hh,hl2]
    rw [show (1:ℝ)/12800=(12800:ℝ)⁻¹ by rw [one_div],Real.log_inv]
    linarith only [hl]
  · norm_num only [Nat.cast_ofNat] at hgap ⊢
    convert hgap using 1
  · intro i
    have hh := mul_le_mul_of_nonneg_left (hprime i) (Real.exp_nonneg (-100))
    dsimp [C]
    rw [←Real.exp_add] at hh
    norm_num at hh
    exact hh
  · intro i
    dsimp [C]
    rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt ((Real.exp_pos 100).trans_le (hprime i))),Real.log_exp]
    linarith
  · intro i; dsimp [u',C]; ring_nf; exact le_rfl
  · exact herr

lemma package_list_arithmetic {X T p L n : ℝ} (hX : 1600≤X)
    (hT : Real.exp X≤T) (hp0 : 0<p) (hp : p≤2*T)
    (hn : 256*T*Real.log (2*T)≤n*L) :
    Real.log (4*(p*Real.exp (-X/200))+p*Real.exp (-(n:ℝ)*(L*((1/4)/p)/2)/4))≤
      Real.log p-X/400 := by
  have hX0 : 0≤X := by linarith only [hX]
  have hT0 : 0<T := (Real.exp_pos X).trans_le hT
  have hlog : X≤Real.log T := by
    exact (Real.log_exp X).symm ▸ Real.log_le_log (Real.exp_pos X) hT
  have hlog2 : X≤Real.log (2*T) := hlog.trans (Real.log_le_log hT0 (by linarith only [hT0]))
  have hl8 : Real.log 8≤3 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    rw [show (8:ℝ)=2^3 by norm_num,Real.log_pow]
    norm_num at hh ⊢
    linarith only [hh]
  have hhalf : 4*Real.exp (-X/200)≤Real.exp (-X/400)/2 := by
    have he : -X/200≤-X/400-Real.log 8 := by linarith only [hX,hl8]
    have hh := Real.exp_le_exp.mpr he
    rw [Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<8)] at hh
    linarith only [hh]
  have hlarge : 4*Real.log (2*T)≤n*L/(32*p) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hp' := mul_le_mul_of_nonneg_right hp (show 0≤128*Real.log (2*T) by linarith only [hlog2,hX0])
    nlinarith only [hn,hp']
  have hsmall : Real.exp (-n*(L*((1/4)/p)/2)/4)≤Real.exp (-X/400)/2 := by
    have hl2 : Real.log 2≤1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      linarith only [hh]
    have he : -n*(L*((1/4)/p)/2)/4≤-X/400-Real.log 2 := by
      have heq : -n*(L*((1/4)/p)/2)/4= -(n*L/(32*p)) := by ring
      rw [heq]
      linarith only [hlarge,hlog2,hX,hl2]
    have hh := Real.exp_le_exp.mpr he
    rwa [Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<2)] at hh
  have harg : 4*(p*Real.exp (-X/200))+p*Real.exp (-n*(L*((1/4)/p)/2)/4)≤
      p*Real.exp (-X/400) := by
    have h1 := mul_le_mul_of_nonneg_left hhalf hp0.le
    have h2 := mul_le_mul_of_nonneg_left hsmall hp0.le
    nlinarith only [h1,h2]
  have hh := Real.log_le_log (by positivity : 0<4*(p*Real.exp (-X/200))+p*Real.exp (-n*(L*((1/4)/p)/2)/4)) harg
  rw [Real.log_mul hp0.ne' (Real.exp_ne_zero _),Real.log_exp] at hh
  linarith only [hh]

lemma package_rate_arithmetic {X T L n b H E c mean : ℝ}
    (hX : 1≤X) (hT : 0<T) (hc : 0<c)
    (hlog : X≤Real.log T) (hlog' : Real.log T≤21/20*X)
    (hmean : mean≤2*X) (hb : c*T/Real.log T≤b)
    (hn : n*L≤1024*T*Real.log T)
    (hshift : 2*n*H≤c*T/5000) (hE : E≤c*T/10000) :
    n*(L*(c/(10000000*Real.log T))+2*H)≤
      b*((X/400)*(1-2*(1/100))-(1/10000)*mean)-E := by
  have hlog0 : 0<Real.log T := by linarith only [hX,hlog]
  have hb0 : 0<b := (div_pos (mul_pos hc hT) hlog0).trans_le hb
  have hbg : c*T≤b*Real.log T := (div_le_iff₀ hlog0).mp hb
  have hbg' : c*T≤b*(21/20*X) := hbg.trans (mul_le_mul_of_nonneg_left hlog' hb0.le)
  have hgain : X/500≤(X/400)*(1-2*(1/100))-(1/10000)*mean := by
    nlinarith only [hmean,hX]
  have hrev := mul_le_mul_of_nonneg_left hgain hb0.le
  have hcost := mul_le_mul_of_nonneg_right hn (show 0≤c/(10000000*Real.log T) by positivity)
  have heq : (1024*T*Real.log T)*(c/(10000000*Real.log T))=1024*c*T/10000000 := by
    field_simp
  rw [heq] at hcost
  nlinarith only [hbg',hrev,hcost,hshift,hE,mul_pos hc hT]

open scoped BigOperators Classical
open Filter

lemma eventually_poly_le_exp_linear (C : ℝ) {a : ℝ} (ha : 0<a) (d : ℕ) :
    ∀ᶠ X : ℝ in atTop, C*X^d≤Real.exp (a*X) := by
  have h := eventually_poly_le_exp (C/a^d) (a := 1) (by norm_num) d
  have ht : Tendsto (fun x : ℝ => a*x) atTop atTop := tendsto_id.const_mul_atTop ha
  filter_upwards [ht.eventually h] with X hX
  simp only [one_mul,mul_pow] at hX
  convert hX using 1; field_simp

lemma eventually_mul_exp_le_exp {a b : ℝ} (hab : a<b) (C : ℝ) :
    ∀ᶠ X : ℝ in atTop, C*Real.exp (a*X)≤Real.exp (b*X) := by
  have h := eventually_poly_le_exp_linear C (sub_pos.mpr hab) 0
  filter_upwards [h] with X hX
  simp only [pow_zero,mul_one] at hX
  have hh := mul_le_mul_of_nonneg_right hX (Real.exp_nonneg (a*X))
  rw [←Real.exp_add] at hh
  convert hh using 1
  congr 1
  ring_nf

noncomputable def batchWordLength (j : ℕ) : ℕ := 2^(2*j/5)
noncomputable def packageRepetitions (j : ℕ) : ℕ :=
  ⌈256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j)/batchWordLength j⌉₊

lemma batchWordLength_pos (j : ℕ) : 0<batchWordLength j := by
  unfold batchWordLength; positivity

lemma batchWordLength_dvd {i j : ℕ} (hij : i≤j) : batchWordLength i∣batchWordLength j := by
  exact pow_dvd_pow 2 (Nat.div_le_div_right (Nat.mul_le_mul_left 2 hij))

lemma batchWordLength_log (j : ℕ) :
    (2/5:ℝ)*(j*Real.log 2)-Real.log 2≤Real.log (batchWordLength j:ℝ) ∧
    Real.log (batchWordLength j:ℝ)≤(2/5:ℝ)*(j*Real.log 2) := by
  have hp : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have h1 : 5*(2*j/5)≤2*j := Nat.mul_div_le _ _
  have h2 : 2*j<5*(2*j/5+1) := Nat.lt_mul_div_succ _ (by norm_num)
  have h1' : 5*(2*j/5:ℕ)≤(2:ℝ)*j := by exact_mod_cast h1
  have h2' : (2:ℝ)*j<5*((2*j/5:ℕ)+1) := by exact_mod_cast h2
  have hh1 := mul_le_mul_of_nonneg_right h1' hp.le
  have hh2 := mul_lt_mul_of_pos_right h2' hp
  simp only [batchWordLength,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  constructor <;> nlinarith only [hh1,hh2]

lemma batchWordLength_le_scale (j : ℕ) : (batchWordLength j:ℝ)≤(2:ℝ)^j := by
  unfold batchWordLength
  push_cast
  apply pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
  omega

theorem eventually_integer_batch_bounds {D : ℝ} (hD : 1≤D) :
    ∀ᶠ X : ℝ in atTop, ∀ j : ℕ,
      X≤j*Real.log 2 → j*Real.log 2≤21/20*X →
      0<packageRepetitions j ∧
      (D*(batchWordLength j:ℝ))^2<(2:ℝ)^j ∧
      256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j)≤
        (packageRepetitions j:ℝ)*batchWordLength j ∧
      (packageRepetitions j:ℝ)*batchWordLength j≤1024*(2:ℝ)^j*Real.log ((2:ℝ)^j) ∧
      (packageRepetitions j:ℝ)≤Real.exp (7/10*X) ∧
      (batchWordLength j:ℝ)≤Real.exp (21/50*X) := by
  have hpoly := eventually_poly_le_exp_linear (1024:ℝ) (a := 1/100) (by norm_num) 1
  have hshort' := eventually_mul_exp_le_exp (a := 0) (b := 4/25) (by norm_num) (2*D^2)
  filter_upwards [hpoly,hshort',eventually_ge_atTop (100:ℝ)] with X hpoly hshort' hX
  intro j hlo hhi
  have hl2 : Real.log (2:ℝ)≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith only [hh]
  have hT : Real.log ((2:ℝ)^j)=(j:ℝ)*Real.log 2 := Real.log_pow _ _
  have hTpos : 0<(2:ℝ)^j := by positivity
  have hLpos : 0<(batchWordLength j:ℝ) := by exact_mod_cast batchWordLength_pos j
  have hLlog := batchWordLength_log j
  have hLlo : Real.exp (39/100*X)≤(batchWordLength j:ℝ) := by
    rw [←Real.exp_log hLpos]
    apply Real.exp_le_exp.mpr
    nlinarith only [hLlog.1,hlo,hl2,hX]
  have hLhi : (batchWordLength j:ℝ)≤Real.exp (21/50*X) := by
    rw [←Real.exp_log hLpos]
    apply Real.exp_le_exp.mpr
    nlinarith only [hLlog.2,hhi]
  have hThe : (2:ℝ)^j≤Real.exp (21/20*X) := by
    rw [←Real.exp_log hTpos,hT]
    exact Real.exp_le_exp.mpr hhi
  have hTel : Real.exp X≤(2:ℝ)^j := by
    rw [←Real.exp_log hTpos,hT]
    exact Real.exp_le_exp.mpr hlo
  have hlogT : 1≤Real.log ((2:ℝ)^j) := by rw [hT]; linarith only [hlo,hX]
  have hlog2T : Real.log (2*(2:ℝ)^j)=Real.log 2+Real.log ((2:ℝ)^j) :=
    Real.log_mul (by norm_num) hTpos.ne'
  have hnum : 0<256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j) := by
    rw [hlog2T]; positivity
  have hnlo : 256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j)≤
      (packageRepetitions j:ℝ)*batchWordLength j := by
    exact (div_le_iff₀ hLpos).mp (Nat.le_ceil _)
  have hnhi : (packageRepetitions j:ℝ)*batchWordLength j≤
      256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j)+(batchWordLength j:ℝ) := by
    have hh := (Nat.ceil_lt_add_one (show 0≤256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j)/batchWordLength j by positivity)).le
    have hm := mul_le_mul_of_nonneg_right hh hLpos.le
    rw [add_mul,one_mul,div_mul_cancel₀ _ hLpos.ne'] at hm
    exact hm
  have hprod : (packageRepetitions j:ℝ)*batchWordLength j≤1024*(2:ℝ)^j*Real.log ((2:ℝ)^j) := by
    have hL := batchWordLength_le_scale j
    rw [hlog2T] at hnhi
    have hh := mul_le_mul_of_nonneg_left hl2 (show 0≤256*(2:ℝ)^j by positivity)
    have hh' := mul_le_mul_of_nonneg_left hlogT (show 0≤(2:ℝ)^j by positivity)
    nlinarith only [hnhi,hL,hh,hh',hTpos]
  have hnbound : (packageRepetitions j:ℝ)≤Real.exp (7/10*X) := by
    have hrough : (packageRepetitions j:ℝ)*(batchWordLength j:ℝ)≤
        1024*Real.exp (21/20*X)*(21/20*X) := by
      apply hprod.trans
      gcongr
      rw [hT]; exact hhi
    have hn' := mul_le_mul_of_nonneg_left hLlo (Nat.cast_nonneg (packageRepetitions j))
    have hc : 1024*(21/20*X)≤Real.exp (4/100*X) := by
      have he := Real.add_one_le_exp (3/100*X)
      have he' : (21/20:ℝ)≤Real.exp (3/100*X) := by linarith only [he,hX]
      have hm := mul_le_mul hpoly he' (by norm_num) (Real.exp_nonneg _)
      simp only [pow_one] at hm
      rw [←Real.exp_add] at hm
      rw [show 1/100*X+3/100*X=4/100*X by ring] at hm
      linarith only [hm]
    have hh := mul_le_mul_of_nonneg_right hc (Real.exp_nonneg (21/20*X))
    rw [←Real.exp_add] at hh
    have hlast : (packageRepetitions j:ℝ)*Real.exp (39/100*X)≤
        Real.exp (7/10*X)*Real.exp (39/100*X) := by
      apply hn'.trans (hrough.trans _)
      rw [←Real.exp_add]
      rw [show 4/100*X+21/20*X=7/10*X+39/100*X by ring] at hh
      nlinarith only [hh]
    nlinarith only [hlast,Real.exp_pos (39/100*X)]
  refine ⟨?_,?_,hnlo,hprod,hnbound,hLhi⟩
  · exact Nat.ceil_pos.mpr (div_pos hnum hLpos)
  · have hsquare := mul_le_mul hLhi hLhi hLpos.le (Real.exp_nonneg _)
    rw [←Real.exp_add] at hsquare
    have hh := mul_le_mul_of_nonneg_left hsquare (sq_nonneg D)
    have hstrict : D^2<Real.exp (4/25*X) := by
      simp only [zero_mul,Real.exp_zero,mul_one] at hshort'
      have hDpos : 0<D^2 := sq_pos_of_pos (by linarith only [hD])
      linarith only [hshort',hDpos]
    have hs := mul_lt_mul_of_pos_right hstrict (Real.exp_pos (21/50*X+21/50*X))
    rw [←Real.exp_add] at hs
    have he : 4/25*X+(21/50*X+21/50*X)=X := by ring
    rw [he] at hs
    have hsq : (D*(batchWordLength j:ℝ))^2≤D^2*Real.exp (21/50*X+21/50*X) := by
      nlinarith only [hh]
    exact (hsq.trans_lt hs).trans_le hTel

end GaussianMoat

end OAI
