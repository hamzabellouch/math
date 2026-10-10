import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.RadialSummation

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma relativeRepresentative_source_angle {T w : ℝ} {k : Fin 4→ℕ} {j : ℕ}
    {v n a : Vec} (hn : ‖n‖=1)
    (hv : v∈coneBinMomentumSet (relativeRepresentativeClosedBin T w k j) n a) :
    1 ≤ sourceRepresentative (k 0)*cappedRepresentative (k 1) := by
  have he := source_angle_coordinate_lower v n hn
  have hθ := cappedRepresentative_pos (k 1)
  have hq := q_pos v
  have hhi : 1-dot n (velocity v)≤8*(cappedRepresentative (k 1))^2 := hv.2.1.2
  have hroot : Real.sqrt ((1-dot n (velocity v))/2)≤2*cappedRepresentative (k 1) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    linarith only [hhi]
  have hqθ : 1/2≤2*q v*cappedRepresentative (k 1) :=
    he.trans (by nlinarith only [mul_le_mul_of_nonneg_left hroot hq.le])
  have hp : q v ≤ sourceRepresentative (k 0)/32 := hv.1.2
  nlinarith only [mul_le_mul_of_nonneg_right hp hθ.le,hqθ]

lemma cone_relative_bin_small {v w n : Vec} {θ φ σ : ℝ}
    (hn : ‖n‖=1) (hθ : 0≤θ) (hφ : 0≤φ) (hσ : 0≤σ) (hsep : 16*θ≤φ)
    (hdlo : θ^2/2≤1-dot n (velocity v)) (hdhi : 1-dot n (velocity v)≤8*θ^2)
    (hDlo : φ^2/2≤1-dot n (velocity w)) (hDhi : 1-dot n (velocity w)≤8*φ^2)
    (helo : σ^2/2≤1-dot (velocity w) (velocity v))
    (hehi : 1-dot (velocity w) (velocity v)≤8*σ^2) : φ/8≤σ ∧ σ≤8*φ := by
  obtain ⟨he,_,hD⟩ := cone_relative_bin_triangle hn hdlo hdhi hDlo hDhi helo hehi
  have hsq := mul_self_le_mul_self (show 0≤16*θ by positivity) hsep
  constructor <;> nlinarith

lemma small_good_balance_scalar {I p θ φ σ R B : ℝ}
    (hI : 0≤I) (hp : 0<p) (hθ : 0<θ) (hφ : 0≤φ) (hφ1 : φ≤1)
    (hσ : 0<σ) (hR : 0≤R) (hφσ : φ≤8*σ) (hpθ : 1≤p*θ)
    (hB : Real.sqrt I*R*p*σ≤B) :
    (I*p^2*(min θ σ)^2*φ^2/θ^2)*
      (Real.sqrt I*R*min θ σ*Real.sqrt (1+φ/σ)/θ^2) ≤ 24*B*(I*p^2) := by
  have hν : 0 ≤ min θ σ := le_min hθ.le hσ.le
  have hκ : Real.sqrt (1+φ/σ)≤3 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    have hh := (div_le_iff₀ hσ).mpr hφσ
    linarith only [hh]
  have hν3 : (min θ σ)^3≤θ^3 := pow_le_pow_left₀ hν (min_le_left _ _) 3
  have hφ2 : φ^2≤8*σ := by
    calc
      _ ≤ φ := by nlinarith only [hφ,hφ1]
      _ ≤ _ := hφσ
  have hB0 : 0≤B := (show 0≤Real.sqrt I*R*p*σ by positivity).trans hB
  have hfact : (min θ σ)^3*φ^2*Real.sqrt (1+φ/σ) ≤ 24*p*θ^4*σ := by
    calc
      _ ≤ θ^3*(8*σ)*3 := mul_le_mul
        (mul_le_mul hν3 hφ2 (sq_nonneg _) (by positivity)) hκ (Real.sqrt_nonneg _) (by positivity)
      _ = 24*θ^3*σ := by ring
      _ ≤ (24*θ^3*σ)*(p*θ) := le_mul_of_one_le_right (by positivity) hpθ
      _ = _ := by ring
  have hratio : (min θ σ)^3*φ^2*Real.sqrt (1+φ/σ)/(θ^4*σ)≤24*p :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hfact])
  calc
    _ = (Real.sqrt I*R*p*σ)*(I*p)*
        ((min θ σ)^3*φ^2*Real.sqrt (1+φ/σ)/(θ^4*σ)) := by field_simp
    _ ≤ B*(I*p)*(24*p) := mul_le_mul (mul_le_mul_of_nonneg_right hB (by positivity))
      hratio (by positivity) (by positivity)
    _ = _ := by ring

lemma small_magnetic_balance_scalar {I p θ φ σ R B : ℝ}
    (hI : 0≤I) (hp : 0<p) (hθ : 0<θ) (hθ1 : θ≤1) (hφ : 0<φ)
    (hσ : 0<σ) (hR : 0≤R) (hφσ : φ≤8*σ) (hθφ : θ≤φ)
    (hB : Real.sqrt I*R*p*σ≤B) :
    (I*p^2*(min θ σ)^2*φ)*
      (Real.sqrt I*R*min θ σ*Real.sqrt (1+φ/σ)/φ) ≤ 24*B*(I*p) := by
  have hν : 0 ≤ min θ σ := le_min hθ.le hσ.le
  have hκ : Real.sqrt (1+φ/σ)≤3 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    have hh := (div_le_iff₀ hσ).mpr hφσ
    linarith only [hh]
  have hν3 : (min θ σ)^3≤θ^3 := pow_le_pow_left₀ hν (min_le_left _ _) 3
  have hθ3 : θ^3≤8*σ := by
    have hh : θ^2≤1 := pow_le_one₀ hθ.le hθ1
    calc
      _ = θ^2*θ := by ring
      _ ≤ 1*θ := mul_le_mul_of_nonneg_right hh hθ.le
      _ ≤ 8*σ := by simpa only [one_mul] using hθφ.trans hφσ
  have hB0 : 0≤B := (show 0≤Real.sqrt I*R*p*σ by positivity).trans hB
  have hratio : (min θ σ)^3*Real.sqrt (1+φ/σ)/σ≤24 := by
    apply (div_le_iff₀ hσ).mpr
    calc
      _ ≤ (8*σ)*3 := mul_le_mul (hν3.trans hθ3) hκ (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by ring
  calc
    _ = (Real.sqrt I*R*p*σ)*(I*p)*
        ((min θ σ)^3*Real.sqrt (1+φ/σ)/σ) := by field_simp
    _ ≤ B*(I*p)*24 := mul_le_mul (mul_le_mul_of_nonneg_right hB (by positivity))
      hratio (by positivity) (by positivity)
    _ = _ := by ring

lemma general_good_large_balance {I p ν θ φ W : ℝ}
    (hI : 0<I) (hp : 0<p) (hν : 0≤ν) (hθ : 0<θ)
    (hνθ : ν≤θ) (hφ : 0≤φ) (hφ1 : φ≤1) (hpθ : 1≤p*θ)
    (hW : Real.sqrt I*p≤W) :
    Real.sqrt ((I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*ν/θ^2)) ≤ W*Real.sqrt W := by
  have hW0 : 0≤W := (by positivity : 0≤Real.sqrt I*p).trans hW
  have hν3 : ν^3≤θ^3 := pow_le_pow_left₀ hν hνθ 3
  have hφ2 : φ^2≤1 := pow_le_one₀ hφ hφ1
  have hnum : ν^3*φ^2≤p*θ^4 := by
    calc
      _ ≤ θ^3*1 := mul_le_mul hν3 hφ2 (sq_nonneg _) (by positivity)
      _ ≤ θ^3*(p*θ) := mul_le_mul_of_nonneg_left hpθ (by positivity)
      _ = _ := by ring
  have hratio : ν^3*φ^2/θ^4≤p := (div_le_iff₀ (pow_pos hθ 4)).mpr hnum
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  calc
    _ = I*Real.sqrt I*p^2*(ν^3*φ^2/θ^4) := by ring
    _ ≤ I*Real.sqrt I*p^2*p := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = (Real.sqrt I*p)^3 := by rw [show (Real.sqrt I*p)^3=(Real.sqrt I)^2*Real.sqrt I*p^3 by ring,Real.sq_sqrt hI.le]; ring
    _ ≤ W^3 := pow_le_pow_left₀ (by positivity) hW 3
    _ = (W*Real.sqrt W)^2 := by rw [mul_pow,Real.sq_sqrt hW0]; ring

lemma Admissible.direct_source_general_large_sum {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b I w : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ I → 0 < I →
      1 ≤ sourceRepresentative np*cappedRepresentative nθ →
      let p := sourceRepresentative np
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Kg := relativeCauchyConstant Cg E (20*E)
      let Kb := relativeCauchyConstant Cb E (120*E)
      (∑'nr : ℕ,if I ≤ max 1 T*cappedRepresentative nr then
        ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
          ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
      ENNReal.ofReal (Kg*dyadicBalanceConstant (1/2) (1/2)*(Real.sqrt I*p)*Real.sqrt (Real.sqrt I*p)+
        Kb*dyadicBalanceConstant 1 (1/2)*Real.sqrt I*p) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_large_radius
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b I w hS hS0 ha hb hJI hI hpθ
  dsimp only
  let p := sourceRepresentative np
  let θ := cappedRepresentative nθ
  let φ := cappedRepresentative nφ
  let σ := cappedRepresentative j
  let ν := min θ σ
  let E := ∫x : Vec,totalEnergy s (0,x)
  let Kg := relativeCauchyConstant Cg E (20*E)
  let Kb := relativeCauchyConstant Cb E (120*E)
  let ag := I*p^2*ν^2*φ^2/θ^2
  let bg := Real.sqrt I*ν/θ^2
  let G := fun n=>ENNReal.ofReal (Kg*min (ag*Real.sqrt (max 1 T*cappedRepresentative n))
    (bg/Real.sqrt (max 1 T*cappedRepresentative n)))
  let Bm := fun n=>ENNReal.ofReal (Kb*Real.sqrt I*min
    (max 1 T*cappedRepresentative n*p^2*ν^2*φ)
    (Real.sqrt p*ν/(θ*Real.sqrt (max 1 T*cappedRepresentative n))))
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hν : 0<ν := lt_min hθ (cappedRepresentative_pos _)
  have hKg : 0≤Kg := relativeCauchyConstant_nonneg hCg
  have hKb : 0≤Kb := relativeCauchyConstant_nonneg hCb
  have hH : 0 < max 1 T := zero_lt_one.trans_le (le_max_left _ _)
  have hg := capped_sqrt_radius_ennreal_sum (show 0≤ag by dsimp [ag]; positivity)
    (show 0≤bg by dsimp [bg]; positivity) hH hKg
  have hm := capped_large_magnetic_ennreal_sum hH hp hν.le hθ (min_le_left _ _)
    ((min_le_left _ _).trans (cappedRepresentative_le_one _)) hφ.le
    (cappedRepresentative_le_one _) (mul_nonneg hKb (Real.sqrt_nonneg I))
  have hc := general_good_large_balance hI hp hν.le hθ (min_le_left _ _)
    hφ.le (cappedRepresentative_le_one _) hpθ (le_refl (Real.sqrt I*p))
  have hDs : 0≤dyadicBalanceConstant (1/2) (1/2) :=
    (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hDm : 0≤dyadicBalanceConstant 1 (1/2) :=
    (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  calc
    _ ≤ ∑'n : ℕ,(G n+Bm n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      split_ifs with hIr
      · have h := hsource s T F hs hT h0 zX S ![np,nθ,nφ,n] j a b I w hS hS0 ha hb hJI hI hIr
        dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Matrix.cons_val,Fin.reduceFinMk] at h
        have hrad : 0 < max 1 T*cappedRepresentative n := mul_pos hH (cappedRepresentative_pos _)
        refine h.trans_eq ?_
        exact ENNReal.ofReal_add
          (mul_nonneg hKg (by positivity))
          (mul_nonneg (mul_nonneg hKb (Real.sqrt_nonneg I)) (le_min (by positivity) (by positivity)))
      · exact bot_le
    _ = (∑'n : ℕ,G n)+(∑'n : ℕ,Bm n) := ENNReal.tsum_add
    _ ≤ ENNReal.ofReal (Kg*dyadicBalanceConstant (1/2) (1/2)*Real.sqrt (ag*bg))+
        ENNReal.ofReal (Kb*Real.sqrt I*dyadicBalanceConstant 1 (1/2)*p) := add_le_add hg hm
    _ = ENNReal.ofReal (Kg*dyadicBalanceConstant (1/2) (1/2)*Real.sqrt (ag*bg)+
        Kb*Real.sqrt I*dyadicBalanceConstant 1 (1/2)*p) :=
      (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ Kg*dyadicBalanceConstant (1/2) (1/2)*((Real.sqrt I*p)*Real.sqrt (Real.sqrt I*p))+
            Kb*Real.sqrt I*dyadicBalanceConstant 1 (1/2)*p :=
          add_le_add (mul_le_mul_of_nonneg_left hc (mul_nonneg hKg hDs)) le_rfl
        _ = _ := by dsimp only [Kg,Kb,p,E]; ring

lemma Admissible.direct_source_small_short_sum {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → b-a ≤ (w/P)^2 →
      0 < M → 0 ≤ A → 0 < P → 1 ≤ Real.log (2+P) → 0 < w → w≤P →
      sourceRepresentative np≤128*P → 1≤w →
      cappedRepresentative nθ≤cappedRepresentative nφ →
      cappedRepresentative nφ≤8*cappedRepresentative j →
      1 ≤ sourceRepresentative np*cappedRepresentative nθ →
      512 ≤ cappedRepresentative j*sourceRepresentative np →
      32 ≤ cappedRepresentative j*w →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Kg := relativeCauchyConstant Cg E (20*E)
      let Kb := relativeCauchyConstant Cb E (120*E)
      (∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤(w/P)^2 then
        ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
          ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
      ENNReal.ofReal ((Kg+Kb)*dyadicBalanceConstant (1/2) (1/2)*
        Real.sqrt (24*256*16384*(1+16384*(M+Real.sqrt A))*w^3*Real.sqrt (Real.log (2+P)))) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_relative_short_radial_sum
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b w M A P hS hS0 ha hb hab hJI
    hM hA hP hL hw hwP hpP hw1 hθφ hφσ hpθ hpσ hwσ HX HZ
  dsimp only
  let p := sourceRepresentative np
  let θ := cappedRepresentative nθ
  let φ := cappedRepresentative nφ
  let σ := cappedRepresentative j
  let L := Real.log (2+P)
  let I := (w/P)^2
  let lam := stabilityLength P 16384 M A p w σ
  let len := min I (lam/2)
  let m := min p w/128
  let E := ∫x : Vec,totalEnergy s (0,x)
  let R := Real.sqrt (1+I/len)
  let ν := min θ σ
  let Kg := relativeCauchyConstant Cg E (20*E)
  let Kb := relativeCauchyConstant Cb E (120*E)
  let D := dyadicBalanceConstant (1/2) (1/2)
  let U := 24*256*16384*(1+16384*(M+Real.sqrt A))*w^3*Real.sqrt L
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hσ : 0<σ := cappedRepresentative_pos _
  have hI : 0<I := sq_pos_of_pos (div_pos hw hP)
  have hlam : 0<lam := stabilityLength_pos hP (by norm_num) hM hp hw hσ
  have hlen : 0<len := lt_min hI (by positivity)
  have hlenI : len≤I := min_le_left _ _
  have hlenlam : 2*len≤lam := by
    have hh : len≤lam/2 := min_le_right _ _
    linarith only [hh]
  have hm : 0 < m := div_pos (lt_min hp hw) (by norm_num)
  have hmq : m≤p/128 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hmw : m≤w/8 := by
    have hh : min p w≤w := min_le_right _ _
    dsimp [m]
    linarith only [hh,hw]
  have hstable : 2*len≤(128*(P/m)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2 := by
    dsimp only [m,L]
    rw [stability_massScale_identity]
    convert hlenlam using 1
    norm_num [lam]
  have hn := hsource s T F hs hT h0 zX S np nθ nφ j a b I len w M A P L m 128
    hS hS0 ha hb hab hlen hlenI hJI hM hA hP (by dsimp [L]; linarith only [hL]) hm hw
    (by norm_num) hmq hmw hpσ hwσ hstable HX HZ
  have hp1 : 1≤p := by
    have hh : 1≤(2:ℝ)^np := one_le_pow₀ (by norm_num)
    dsimp only [p,sourceRepresentative]
    linarith only [hh]
  have hIp : I*p^2≤16384*w^2 := by
    have hp2 : p^2≤16384*P^2 := by nlinarith only [sq_nonneg (128*P-p),hpP,hp,hP]
    calc
      _ ≤ I*(16384*P^2) := mul_le_mul_of_nonneg_left hp2 hI.le
      _ = _ := by dsimp only [I]; field_simp
  have hIp' : I*p≤I*p^2 := mul_le_mul_of_nonneg_left (by nlinarith only [hp1]) hI.le
  have hB := direction_clipped_baseline_R_log_bound128 hP hL (by norm_num : (0:ℝ)<16384)
    hM hA hp hw hσ (cappedRepresentative_le_one _) hpP hwP
  change Real.sqrt I*R*p*σ ≤ 256*(1+16384*(M+Real.sqrt A))*w*Real.sqrt L at hB
  have hg := small_good_balance_scalar hI.le hp hθ hφ.le (cappedRepresentative_le_one _)
    hσ (Real.sqrt_nonneg _) hφσ hpθ hB
  have hb' := small_magnetic_balance_scalar hI.le hp hθ (cappedRepresentative_le_one _) hφ
    hσ (Real.sqrt_nonneg _) hφσ hθφ hB
  have hbig : 0≤256*(1+16384*(M+Real.sqrt A))*w*Real.sqrt L := by positivity
  have hprod : 24*(256*(1+16384*(M+Real.sqrt A))*w*Real.sqrt L)*(I*p^2)≤U := by
    calc
      _ ≤ 24*(256*(1+16384*(M+Real.sqrt A))*w*Real.sqrt L)*(16384*w^2) :=
        mul_le_mul_of_nonneg_left hIp (by positivity)
      _ = _ := by dsimp only [U]; ring
  have hg' : (I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*R*ν*Real.sqrt (1+φ/σ)/θ^2)≤U :=
    hg.trans hprod
  have hb'' : (I*p^2*ν^2*φ)*(Real.sqrt I*R*ν*Real.sqrt (1+φ/σ)/φ)≤U :=
    hb'.trans ((mul_le_mul_of_nonneg_left hIp' (by positivity)).trans hprod)
  have hKg : 0≤Kg := relativeCauchyConstant_nonneg hCg
  have hKb : 0≤Kb := relativeCauchyConstant_nonneg hCb
  have hD : 0≤D := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  apply hn.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Kg*D*Real.sqrt U+Kb*D*Real.sqrt U :=
      add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hg') (mul_nonneg hKg hD))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb'') (mul_nonneg hKb hD))
    _ = _ := by dsimp [Kg,Kb,D,U,E,L]; ring

lemma small_deficit_short_source_coefficient {I P p w θ φ σ Kg Kb : ℝ}
    (hI : 0<I) (hI1 : I≤1) (hP : 0<P) (hp : 0<p) (hw : 0<w)
    (hθ : 0<θ) (hφ : 0≤φ) (hφ1 : φ≤1) (hσ : 0≤σ)
    (hφσ : φ≤8*σ) (hpP : p≤128*P) (hIP : I≤(w/P)^2)
    (hdeficit : σ*p≤512 ∨ σ*w≤32) (hKg : 0≤Kg) (hKb : 0≤Kb) :
    Kg*(I*p^2*(min θ σ)^2*φ^2/θ^2)+Kb*(I*p^2*(min θ σ)^2*φ) ≤
      (64*Kg+Kb)*16777216 := by
  have hν : 0 ≤ min θ σ := le_min hθ.le hσ
  have hσsq : (min θ σ)^2≤σ^2 := pow_le_pow_left₀ hν (min_le_right _ _) 2
  have hIpp : I*p^2≤16384*w^2 := by
    have hp2 : p^2≤16384*P^2 := by nlinarith only [sq_nonneg (128*P-p),hpP,hp,hP]
    have h := mul_le_mul hIP hp2 (sq_nonneg _) (by positivity : 0≤(w/P)^2)
    have he : (w/P)^2*(16384*P^2)=16384*w^2 := by field_simp
    exact h.trans_eq he
  have hbase : I*p^2*(min θ σ)^2≤16777216 := by
    calc
      _ ≤ I*p^2*σ^2 := mul_le_mul_of_nonneg_left hσsq (by positivity)
      _ ≤ 16777216 := by
        rcases hdeficit with hd | hd
        · have hsq : (σ*p)^2≤512^2 := pow_le_pow_left₀ (mul_nonneg hσ hp.le) hd 2
          have he : I*p^2*σ^2=I*(σ*p)^2 := by ring
          rw [he]
          calc
            _ ≤ 1*(512:ℝ)^2 := mul_le_mul hI1 hsq (sq_nonneg _) (by norm_num)
            _ ≤ _ := by norm_num
        · have hsq : (σ*w)^2≤32^2 := pow_le_pow_left₀ (mul_nonneg hσ hw.le) hd 2
          calc
            _ ≤ (16384*w^2)*σ^2 := mul_le_mul_of_nonneg_right hIpp (sq_nonneg _)
            _ = 16384*(σ*w)^2 := by ring
            _ ≤ 16384*(32:ℝ)^2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
            _ = _ := by norm_num
  have hθsq : (min θ σ)^2/θ^2≤1 := by
    apply (div_le_one (pow_pos hθ 2)).mpr
    exact pow_le_pow_left₀ hν (min_le_left _ _) 2
  have hφsq : φ^2≤64*σ^2 := by
    have hh := pow_le_pow_left₀ hφ hφσ 2
    nlinarith only [hh]
  have hraw : I*p^2*σ^2≤16777216 := by
    rcases hdeficit with hd | hd
    · have hsq : (σ*p)^2≤512^2 := pow_le_pow_left₀ (mul_nonneg hσ hp.le) hd 2
      calc
        _ = I*(σ*p)^2 := by ring
        _ ≤ 1*(512:ℝ)^2 := mul_le_mul hI1 hsq (sq_nonneg _) (by norm_num)
        _ ≤ _ := by norm_num
    · have hsq : (σ*w)^2≤32^2 := pow_le_pow_left₀ (mul_nonneg hσ hw.le) hd 2
      calc
        _ ≤ (16384*w^2)*σ^2 := mul_le_mul_of_nonneg_right hIpp (sq_nonneg _)
        _ = 16384*(σ*w)^2 := by ring
        _ ≤ 16384*(32:ℝ)^2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
        _ = _ := by norm_num
  have hgood : I*p^2*(min θ σ)^2*φ^2/θ^2≤16777216*64 := by
    calc
      _ = I*p^2*((min θ σ)^2/θ^2)*φ^2 := by ring
      _ ≤ I*p^2*1*(64*σ^2) := mul_le_mul
        (mul_le_mul_of_nonneg_left hθsq (by positivity)) hφsq (sq_nonneg _) (by positivity)
      _ = (I*p^2*σ^2)*64 := by ring
      _ ≤ 16777216*64 := mul_le_mul_of_nonneg_right hraw (by norm_num)
  have hmag : I*p^2*(min θ σ)^2*φ≤16777216 := by
    have h := mul_le_mul hbase hφ1 hφ (by norm_num : (0:ℝ)≤16777216)
    simpa only [mul_one] using h
  calc
    _ ≤ Kg*(16777216*64)+Kb*16777216 := add_le_add
      (mul_le_mul_of_nonneg_left hgood hKg) (mul_le_mul_of_nonneg_left hmag hKb)
    _ = _ := by ring

lemma Admissible.direct_source_small_deficit_short_sum {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b I w P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ I → 0 < I → I≤1 → 0<w → 0<P →
      sourceRepresentative np≤128*P → I≤(w/P)^2 →
      cappedRepresentative nφ≤8*cappedRepresentative j →
      (cappedRepresentative j*sourceRepresentative np≤512 ∨ cappedRepresentative j*w≤32) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Kg := relativeCauchyConstant Cg E (20*E)
      let Kb := relativeCauchyConstant Cb E (120*E)
      (∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤I then
        ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
          ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
      ENNReal.ofReal ((64*Kg+Kb)*16777216*(1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹*Real.sqrt I) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_short_near_sum
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b I w P hS hS0 ha hb hJI hI hI1 hw hP hpP hIP hsector hdeficit
  dsimp only
  have hn := hsource s T F hs hT h0 zX S np nθ nφ j a b I w hS hS0 ha hb hJI hI
  have hp : 0<sourceRepresentative np := by dsimp [sourceRepresentative]; positivity
  have hθ := cappedRepresentative_pos nθ
  have hφ := cappedRepresentative_pos nφ
  have hKg := relativeCauchyConstant_nonneg (E:=∫x : Vec,totalEnergy s (0,x)) (Z:=20*(∫x : Vec,totalEnergy s (0,x))) hCg
  have hKb := relativeCauchyConstant_nonneg (E:=∫x : Vec,totalEnergy s (0,x)) (Z:=120*(∫x : Vec,totalEnergy s (0,x))) hCb
  have hc := small_deficit_short_source_coefficient hI hI1 hP hp hw hθ hφ.le (cappedRepresentative_le_one _)
    (cappedRepresentative_pos j).le hsector hpP hIP hdeficit hKg hKb
  exact hn.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc shortSqrtConstant_pos.le) (Real.sqrt_nonneg I)))

lemma small_stability_sqrt_coarse {M A w L : ℝ} (hM : 0<M) (hA : 0≤A)
    (hw : 0≤w) (hL : 1≤L) :
    Real.sqrt (24*256*16384*(1+16384*(M+Real.sqrt A))*w^3*Real.sqrt L) ≤
      (24*256*16384*16384)*(1+M+Real.sqrt A)*w*Real.sqrt w*L := by
  let Z := (24*256*16384*16384)*(1+M+Real.sqrt A)
  have hsqrt : 0≤Real.sqrt A := by simpa only [Real.sqrt_zero] using Real.sqrt_le_sqrt hA
  have hZ : 1≤Z := by dsimp [Z]; nlinarith only [hM,hsqrt]
  have hcoeff : 24*256*16384*(1+16384*(M+Real.sqrt A))≤Z^2 := by
    have hb : 24*256*16384*(1+16384*(M+Real.sqrt A))≤Z := by dsimp [Z]; nlinarith
    exact hb.trans (by nlinarith only [hZ])
  have hroot : Real.sqrt L≤L^2 := by
    have h := (Real.sqrt_le_iff).mpr (And.intro (by linarith : 0≤L) (by nlinarith only [hL] : L≤L^2))
    exact h.trans (by nlinarith only [hL])
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  change _≤(Z*w*Real.sqrt w*L)^2
  calc
    _ ≤ Z^2*w^3*L^2 := mul_le_mul
      (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hw 3)) hroot (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by rw [show (Z*w*Real.sqrt w*L)^2=Z^2*w^2*(Real.sqrt w)^2*L^2 by ring,Real.sq_sqrt hw]; ring

lemma Admissible.direct_source_small_all_radii {d : Datum} (hd₀ : Admissible d) :
    ∃ C : ℝ, 0≤C ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → b-a ≤ (w/P)^2 →
      0 < M → 0 ≤ A → 1 ≤ P → 1 ≤ Real.log (2+P) → 1 ≤ w → w≤P →
      sourceRepresentative np≤128*P →
      cappedRepresentative nθ≤cappedRepresentative nφ →
      cappedRepresentative nφ≤8*cappedRepresentative j →
      1 ≤ sourceRepresentative np*cappedRepresentative nθ →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
        ∂physicalBinMeasure V (B nr) (Icc a b)) ≤
      ENNReal.ofReal (C*(1+E)*(1+M+Real.sqrt A)*w*Real.sqrt w*Real.log (2+P)) := by
  obtain ⟨Cgs,Cbs,hCgs,hCbs,hshort⟩ := hd₀.direct_source_small_short_sum
  obtain ⟨Cgd,Cbd,hCgd,hCbd,hdef⟩ := hd₀.direct_source_small_deficit_short_sum
  obtain ⟨Cgl,Cbl,hCgl,hCbl,hlong⟩ := hd₀.direct_source_general_large_sum
  let Ds := dyadicBalanceConstant (1/2) (1/2)
  let Dm := dyadicBalanceConstant 1 (1/2)
  let Dn := (1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹
  let gs := relativeCauchyConstant Cgs 1 20
  let bs := relativeCauchyConstant Cbs 1 120
  let gd := relativeCauchyConstant Cgd 1 20
  let bd := relativeCauchyConstant Cbd 1 120
  let gl := relativeCauchyConstant Cgl 1 20
  let bl := relativeCauchyConstant Cbl 1 120
  let Cs := (gs+bs)*Ds*(24*256*16384*16384)
  let Cd := (64*gd+bd)*16777216*Dn
  let Cl := (gl*Ds*Real.sqrt 128+bl*Dm)*128
  have hDs : 0≤Ds := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hDm : 0≤Dm := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hDn : 0≤Dn := shortSqrtConstant_pos.le
  have hgs : 0≤gs := relativeCauchyConstant_nonneg hCgs
  have hbs : 0≤bs := relativeCauchyConstant_nonneg hCbs
  have hgd : 0≤gd := relativeCauchyConstant_nonneg hCgd
  have hbd : 0≤bd := relativeCauchyConstant_nonneg hCbd
  have hgl : 0≤gl := relativeCauchyConstant_nonneg hCgl
  have hbl : 0≤bl := relativeCauchyConstant_nonneg hCbl
  have hCs : 0≤Cs := by dsimp only [Cs]; positivity
  have hCd : 0≤Cd := by dsimp only [Cd]; positivity
  have hCl : 0≤Cl := by dsimp only [Cl]; positivity
  refine ⟨Cs+Cd+Cl,by positivity,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b w M A P hS hS0 ha hb hab hJI
    hM hA hP1 hL hw1 hwP hpP hθφ hφσ hpθ HX HZ
  dsimp only
  let I := (w/P)^2
  let L := Real.log (2+P)
  let E := ∫x : Vec,totalEnergy s (0,x)
  let p := sourceRepresentative np
  let θ := cappedRepresentative nθ
  let φ := cappedRepresentative nφ
  let σ := cappedRepresentative j
  let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
  let J : ℕ→ℝ≥0∞ := fun nr=>∫⁻z : ConeCoordinate,
    physicalDirectSourceDensity s (fun t=>(prefixFlow F.flow T zX t).1)
      (fun t=>(prefixFlow F.flow T zX t).2) (B nr) z
      ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (B nr) (Icc a b)
  let Jshort : ℕ→ℝ≥0∞ := fun nr=>if max 1 T*cappedRepresentative nr≤I then J nr else 0
  let Jlong : ℕ→ℝ≥0∞ := fun nr=>if I ≤ max 1 T*cappedRepresentative nr then J nr else 0
  let U := (1+E)*(1+M+Real.sqrt A)*w*Real.sqrt w*L
  have hw : 0<w := zero_lt_one.trans_le hw1
  have hP : 0<P := zero_lt_one.trans_le hP1
  have hI : 0<I := sq_pos_of_pos (div_pos hw hP)
  have hI1 : I≤1 := by dsimp only [I]; exact pow_le_one₀ (div_pos hw hP).le ((div_le_one hP).mpr hwP)
  have hp : 0<p := by dsimp only [p,sourceRepresentative]; positivity
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hL0 : 0≤L := zero_le_one.trans hL
  have hU : 0≤U := by dsimp only [U]; positivity
  have hMA : 1≤1+M+Real.sqrt A := by linarith [Real.sqrt_nonneg A]
  have hsqrtw : 1≤Real.sqrt w := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hw1
  have hbaseUs : (1+E)*w*Real.sqrt w≤U := by
    calc
      _ = (1+E)*1*w*Real.sqrt w*1 := by ring
      _ ≤ (1+E)*(1+M+Real.sqrt A)*w*Real.sqrt w*L := by gcongr
  have hbaseU : (1+E)*w≤U := by
    calc
      _ = (1+E)*1*w*1*1 := by ring
      _ ≤ (1+E)*(1+M+Real.sqrt A)*w*Real.sqrt w*L := by gcongr
  have hIsqrt : Real.sqrt I=w/P := Real.sqrt_sq (div_pos hw hP).le
  have hIw : Real.sqrt I≤w := by rw [hIsqrt]; exact (div_le_self hw.le hP1)
  have hgse := relativeCauchyConstant_energy_le hCgs hE (by norm_num : (0:ℝ)≤20)
  have hbse := relativeCauchyConstant_energy_le hCbs hE (by norm_num : (0:ℝ)≤120)
  have hgde := relativeCauchyConstant_energy_le hCgd hE (by norm_num : (0:ℝ)≤20)
  have hbde := relativeCauchyConstant_energy_le hCbd hE (by norm_num : (0:ℝ)≤120)
  have hgle := relativeCauchyConstant_energy_le hCgl hE (by norm_num : (0:ℝ)≤20)
  have hble := relativeCauchyConstant_energy_le hCbl hE (by norm_num : (0:ℝ)≤120)
  have hshortBound : (∑'n,Jshort n)≤ENNReal.ofReal ((Cs+Cd)*U) := by
    by_cases hdeficit : σ*p≤512 ∨ σ*w≤32
    · have hn := hdef s T F hs hT h0 zX S np nθ nφ j a b I w P hS hS0 ha hb hJI
        hI hI1 hw hP hpP le_rfl hφσ hdeficit
      apply hn.trans
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ ((64*(gd*(1+E))+bd*(1+E))*16777216*Dn)*w := by
          dsimp only [Dn,gd,bd]
          gcongr
        _ = Cd*((1+E)*w) := by dsimp only [Cd]; ring
        _ ≤ Cd*U := mul_le_mul_of_nonneg_left hbaseU hCd
        _ ≤ (Cs+Cd)*U := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCs) hU
    · have hh := not_or.mp hdeficit
      have hn := hshort s T F hs hT h0 zX S np nθ nφ j a b w M A P hS hS0 ha hb hab hJI
        hM hA hP hL hw hwP hpP hw1 hθφ hφσ hpθ (le_of_lt (lt_of_not_ge hh.1)) (le_of_lt (lt_of_not_ge hh.2)) HX HZ
      have hc := small_stability_sqrt_coarse hM hA hw.le hL
      apply hn.trans
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (gs*(1+E)+bs*(1+E))*Ds*
            ((24*256*16384*16384)*(1+M+Real.sqrt A)*w*Real.sqrt w*L) := by
          dsimp only [gs,bs,Ds,L]
          gcongr
        _ = Cs*U := by dsimp only [Cs,U]; ring
        _ ≤ (Cs+Cd)*U := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCd) hU
  have hlongBound : (∑'n,Jlong n)≤ENNReal.ofReal (Cl*U) := by
    have hn := hlong s T F hs hT h0 zX S np nθ nφ j a b I w hS hS0 ha hb hJI hI hpθ
    apply hn.trans
    apply ENNReal.ofReal_le_ofReal
    have hip : Real.sqrt I*p≤128*w := by
      rw [hIsqrt]
      calc
        _ ≤ w/P*(128*P) := mul_le_mul_of_nonneg_left hpP (div_nonneg hw.le hP.le)
        _ = _ := by field_simp
    have hiw : Real.sqrt I*p≤(128*w)*Real.sqrt w := hip.trans
      (le_mul_of_one_le_right (by positivity) hsqrtw)
    calc
      _ ≤ (gl*(1+E))*Ds*(128*w)*Real.sqrt (128*w)+
          (bl*(1+E))*Dm*((128*w)*Real.sqrt w) := by
        apply add_le_add
        · dsimp only [gl,Ds]
          gcongr
        · rw [mul_assoc]
          exact mul_le_mul (mul_le_mul_of_nonneg_right hble hDm) hiw
            (mul_nonneg (Real.sqrt_nonneg I) hp.le) (by positivity)
      _ = Cl*((1+E)*w*Real.sqrt w) := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤128)]
        dsimp only [Cl]
        ring
      _ ≤ Cl*U := mul_le_mul_of_nonneg_left hbaseUs hCl
  calc
    _ = ∑'n,J n := rfl
    _ ≤ ∑'n,(Jshort n+Jlong n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      dsimp only [Jshort,Jlong]
      by_cases hrI : max 1 T*cappedRepresentative n≤I
      · rw [ite_eq_left hrI]
        exact le_add_of_nonneg_right (bot_le : (0 : ℝ≥0∞) ≤ _)
      · rw [ite_eq_right hrI,ite_eq_left (le_of_lt (lt_of_not_ge hrI)),zero_add]
    _ = (∑'n,Jshort n)+(∑'n,Jlong n) := ENNReal.tsum_add
    _ ≤ ENNReal.ofReal ((Cs+Cd)*U)+ENNReal.ofReal (Cl*U) := add_le_add hshortBound hlongBound
    _ = _ := by
      rw [←ENNReal.ofReal_add (mul_nonneg (add_nonneg hCs hCd) hU) (mul_nonneg hCl hU)]
      congr 1
      dsimp only [U,E,L]
      ring

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma relativeRepresentative_nonempty_geometry {T w : ℝ} {V : ℝ→Vec}
    {J : Set ℝ} {k : Fin 4→ℕ} {j : ℕ} {z : ConeCoordinate} {v : Vec}
    (hz : z∈physicalBinBase V (relativeRepresentativeClosedBin T w k j) J)
    (hv : v∈coneBinMomentumSet (relativeRepresentativeClosedBin T w k j) z.2.2.1 (velocity (V z.1))) :
    1≤ sourceRepresentative (k 0)*cappedRepresentative (k 1) ∧
      (16*cappedRepresentative (k 1)≤cappedRepresentative (k 2) →
        cappedRepresentative (k 2)≤8*cappedRepresentative j) := by
  refine ⟨relativeRepresentative_source_angle (sphere_norm z.2.2) hv,?_⟩
  intro hsep
  have h := cone_relative_bin_small (sphere_norm z.2.2)
    (cappedRepresentative_pos (k 1)).le (cappedRepresentative_pos (k 2)).le
    (cappedRepresentative_pos j).le hsep hv.2.1.1 hv.2.1.2
    hz.2.2.2.2.1 hz.2.2.2.2.2 hv.2.2.1 hv.2.2.2
  linarith only [h.1]

lemma physicalDirectSource_integral_geometry_zero (s : Solution) {T w : ℝ}
    {X V : ℝ→Vec} (hV : Measurable V) {J : Set ℝ} (hJ : MeasurableSet J)
    {k : Fin 4→ℕ} {j : ℕ}
    (hbad : ¬(1≤ sourceRepresentative (k 0)*cappedRepresentative (k 1) ∧
      (16*cappedRepresentative (k 1)≤cappedRepresentative (k 2) →
        cappedRepresentative (k 2)≤8*cappedRepresentative j))) :
    (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (relativeRepresentativeClosedBin T w k j) z
      ∂physicalBinMeasure V (relativeRepresentativeClosedBin T w k j) J)=0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV _ hJ)] with z hz
  have hempty : coneBinMomentumSet (relativeRepresentativeClosedBin T w k j) z.2.2.1 (velocity (V z.1))=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    exact hbad (relativeRepresentative_nonempty_geometry hz hv)
  simp only [physicalDirectSourceDensity,hempty,Measure.restrict_empty,lintegral_zero_measure,mul_zero,Pi.zero_apply]

lemma Admissible.direct_source_all_radii {d : Datum} (hd₀ : Admissible d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → b-a ≤ (w/P)^2 →
      0 < M → 0 ≤ A → 1≤P → 1 ≤ Real.log (2+P) → 1≤w → w≤P →
      sourceRepresentative np≤128*P →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
        ∂physicalBinMeasure V (B nr) (Icc a b)) ≤
      ENNReal.ofReal (C*(1+E)*(1+M+Real.sqrt A)*w*Real.sqrt w*Real.log (2+P)) := by
  obtain ⟨Cr,hCr,hr⟩ := hd₀.direct_source_remaining_all_radii
  obtain ⟨Cs,hCs,hs'⟩ := hd₀.direct_source_small_all_radii
  refine ⟨Cr+Cs,add_nonneg hCr hCs,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b w M A P hS hS0 ha hb hab hJI
    hM hA hP hL hw hwP hpP HX HZ
  dsimp only
  have hE : 0≤∫x : Vec,totalEnergy s (0,x) := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hw0 : 0<w := zero_lt_one.trans_le hw
  have hL0 : 0≤Real.log (2+P) := zero_le_one.trans hL
  by_cases hremaining : cappedRepresentative nφ≤16*cappedRepresentative nθ
  · have hn := hr s T F hs hT h0 zX S np nθ nφ j a b w M A P hS hS0 ha hb hab hJI
      hM hA hP hL hw0 hwP hpP hremaining HX HZ
    apply hn.trans
    apply ENNReal.ofReal_le_ofReal
    have hroot : 1≤Real.sqrt w := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hw
    calc
      _ = Cr*(1+∫x : Vec,totalEnergy s (0,x))*(1+M+Real.sqrt A)*w*1*Real.log (2+P) := by ring
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_right hCs
  · have hsep : 16*cappedRepresentative nθ≤cappedRepresentative nφ := le_of_lt (lt_of_not_ge hremaining)
    by_cases hgeometry : 1≤ sourceRepresentative np*cappedRepresentative nθ ∧ cappedRepresentative nφ≤8*cappedRepresentative j
    · have hθφ : cappedRepresentative nθ≤cappedRepresentative nφ := by
        linarith [cappedRepresentative_pos nθ]
      have hn := hs' s T F hs hT h0 zX S np nθ nφ j a b w M A P hS hS0 ha hb hab hJI
        hM hA hP hL hw hwP hpP hθφ hgeometry.2 hgeometry.1 HX HZ
      apply hn.trans
      apply ENNReal.ofReal_le_ofReal
      gcongr
      exact le_add_of_nonneg_left hCr
    · have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
        ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
      have hz (nr : ℕ) : (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s
          (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>(prefixFlow F.flow T zX t).2)
          (relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j) z
          ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2)
            (relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j) (Icc a b))=0 := by
        apply physicalDirectSource_integral_geometry_zero s hV measurableSet_Icc
        intro h
        exact hgeometry ⟨h.1,h.2 hsep⟩
      simp_rw [hz,tsum_zero]
      exact bot_le

end RVM

end

end OAI
