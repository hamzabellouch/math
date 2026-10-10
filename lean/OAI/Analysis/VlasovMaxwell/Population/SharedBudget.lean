import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.TransportRemainder

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.direct_source_shared_short_radius {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (k : Fin 4→ℕ) (j : ℕ)
      (a b I len w M A P L massScale Cs : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → 0 < len → len ≤ I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
      massScale ≤ sourceRepresentative (k 0)/128 → massScale ≤ w/8 →
      512 ≤ cappedRepresentative j*sourceRepresentative (k 0) →
      32 ≤ cappedRepresentative j*w →
      2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative j+
        Real.sqrt (A*L/cappedRepresentative j)))⁻¹^2 →
      max 1 T*cappedRepresentative (k 3) ≤ I →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let σ := cappedRepresentative j
      let r := max 1 T*cappedRepresentative (k 3)
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := relativeRepresentativeClosedBin T w k j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let R := Real.sqrt (1+I/len)
      let ν := min θ σ
      let κ := 1+φ/σ
      let G := (goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I (k 2)).toReal
      let Hf := (magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I (k 2)).toReal
      let Kg := relativeCauchyConstant Cg E G
      let Kb := relativeCauchyConstant Cb E (2*Hf)
      (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z
        ∂physicalBinMeasure V B (Icc a b)) ≤
      ENNReal.ofReal (Kg*min ((I*p^2*ν^2*φ^2/θ^2)*Real.sqrt r)
        ((Real.sqrt I*R*ν*Real.sqrt κ/θ^2)/Real.sqrt r)+
      Kb*min ((I*p^2*ν^2*φ)*Real.sqrt r)
        ((Real.sqrt I*R*ν*Real.sqrt κ/φ)/Real.sqrt r)) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_shared_radius_budget
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S k j a b I len w M A P L massScale Cs hS hS0
    ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable hrI HX HZ
  have hn := hsource s T F hs hT h0 zX S k j a b I len w M A P L massScale Cs
    hS hS0 ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable hrI HX HZ
  dsimp only at hn ⊢
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let σ := cappedRepresentative j
  let r := max 1 T*cappedRepresentative (k 3)
  let ν := min θ σ
  let κ := 1+φ/σ
  let E := ∫x : Vec,totalEnergy s (0,x)
  let R := Real.sqrt (1+I/len)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hσ : 0<σ := cappedRepresentative_pos _
  have hν : 0<ν := lt_min hθ hσ
  have hκ : 0≤κ := by dsimp [κ]; positivity
  have hr : 0<r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hI : 0<I := hlen.trans_le hlenI
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hR : 0≤R := Real.sqrt_nonneg _
  have hRsq : R^2=1+I/len := Real.sq_sqrt (by positivity)
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let G := goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I (k 2)
  let Hf := magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I (k 2)
  have hG : G≠⊤ := ne_top_of_le_ne_top
    (hs.goodFieldBudget_finite X (fun t=>velocity (V t)) 1 (Icc_subset_Icc ha hb) hI)
    (ENNReal.le_tsum (f := fun index=>goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I index) (k 2))
  have hF : Hf≠⊤ := by
    apply ne_top_of_le_ne_top _ ((ENNReal.le_tsum (k 2)).trans
      (hs.shared_magneticFieldBudget F.flow zX 1 hI (by norm_num : (0:ℝ)≤2) hJI))
    finiteness
  have hGe : ENNReal.ofReal (G.toReal*I)=ENNReal.ofReal I*G := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal hG,mul_comm]
  have hFe : ENNReal.ofReal ((2*Hf.toReal)*I)=ENNReal.ofReal (2*I)*Hf := by
    rw [show (2*Hf.toReal)*I=(2*I)*Hf.toReal by ring,
      ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_toReal hF]
  have hg := relative_radius_cauchy_scalar hCg hE ENNReal.toReal_nonneg hI hp hν hR hr hφ hκ
    (show 0≤φ/θ^2 by positivity) (Z:=G.toReal)
  dsimp only at hg
  have heγ : 10240*(φ/θ^2)/p=10240*φ/(p*θ^2) := by ring
  have hea : I*p^2*ν^2*φ*(φ/θ^2)=I*p^2*ν^2*φ^2/θ^2 := by ring
  have heb : Real.sqrt I*R*ν*Real.sqrt κ*(φ/θ^2)/φ=Real.sqrt I*R*ν*Real.sqrt κ/θ^2 := by
    field_simp [hφ.ne']
  rw [heγ,hea,heb,hGe,hRsq] at hg
  have hbnd := relative_radius_cauchy_scalar hCb hE (show 0≤2*Hf.toReal by positivity) hI hp hν hR hr hφ hκ
    (show 0≤(1:ℝ) by norm_num)
  dsimp only at hbnd
  simp only [mul_one] at hbnd
  rw [hFe,hRsq] at hbnd
  apply hn.trans
  calc
    _ ≤ ENNReal.ofReal (relativeCauchyConstant Cg E G.toReal*
          min ((I*p^2*ν^2*φ^2/θ^2)*Real.sqrt r)
            ((Real.sqrt I*R*ν*Real.sqrt κ/θ^2)/Real.sqrt r))+
        ENNReal.ofReal (relativeCauchyConstant Cb E (2*Hf.toReal)*
          min ((I*p^2*ν^2*φ)*Real.sqrt r)
            ((Real.sqrt I*R*ν*Real.sqrt κ/φ)/Real.sqrt r)) := by
      exact add_le_add hg hbnd
    _ = _ := by
      rw [←ENNReal.ofReal_add
        (mul_nonneg (relativeCauchyConstant_nonneg hCg) (by positivity))
        (mul_nonneg (relativeCauchyConstant_nonneg hCb) (by positivity))]

lemma Admissible.direct_source_shared_short_radial_sum {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ)
      (a b I len w M A P L massScale Cs : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → 0 < len → len ≤ I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
      massScale ≤ sourceRepresentative np/128 → massScale ≤ w/8 →
      512 ≤ cappedRepresentative j*sourceRepresentative np →
      32 ≤ cappedRepresentative j*w →
      2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative j+
        Real.sqrt (A*L/cappedRepresentative j)))⁻¹^2 →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
      let p := sourceRepresentative np
      let θ := cappedRepresentative nθ
      let φ := cappedRepresentative nφ
      let σ := cappedRepresentative j
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let R := Real.sqrt (1+I/len)
      let ν := min θ σ
      let κ := 1+φ/σ
      let Kg := relativeCauchyConstant Cg E
        (goodFieldBudget s (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>velocity (prefixFlow F.flow T zX t).2) 1 a b I nφ).toReal
      let Kb := relativeCauchyConstant Cb E
        (2*(magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I nφ).toReal)
      let D := dyadicBalanceConstant (1/2) (1/2)
      (∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤I then
        ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
          ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
      ENNReal.ofReal (Kg*D*Real.sqrt
        ((I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*R*ν*Real.sqrt κ/θ^2))+
        Kb*D*Real.sqrt ((I*p^2*ν^2*φ)*(Real.sqrt I*R*ν*Real.sqrt κ/φ))) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_shared_short_radius
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b I len w M A P L massScale Cs hS hS0
    ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable HX HZ
  dsimp only
  let p := sourceRepresentative np
  let θ := cappedRepresentative nθ
  let φ := cappedRepresentative nφ
  let σ := cappedRepresentative j
  let ν := min θ σ
  let κ := 1+φ/σ
  let E := ∫x : Vec,totalEnergy s (0,x)
  let R := Real.sqrt (1+I/len)
  let Kg := relativeCauchyConstant Cg E
        (goodFieldBudget s (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>velocity (prefixFlow F.flow T zX t).2) 1 a b I nφ).toReal
  let Kb := relativeCauchyConstant Cb E
        (2*(magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I nφ).toReal)
  let ag := I*p^2*ν^2*φ^2/θ^2
  let bg := Real.sqrt I*R*ν*Real.sqrt κ/θ^2
  let ab := I*p^2*ν^2*φ
  let bb := Real.sqrt I*R*ν*Real.sqrt κ/φ
  let D := dyadicBalanceConstant (1/2) (1/2)
  have hI : 0<I := hlen.trans_le hlenI
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hσ : 0<σ := cappedRepresentative_pos _
  have hν : 0≤ν := (lt_min hθ hσ).le
  have hag : 0≤ag := by dsimp [ag]; positivity
  have hbg : 0≤bg := by dsimp [bg,R,κ]; positivity
  have hab' : 0≤ab := by dsimp [ab]; positivity
  have hbb : 0≤bb := by dsimp [bb,R,κ]; positivity
  have hKg : 0≤Kg := relativeCauchyConstant_nonneg hCg
  have hKb : 0≤Kb := relativeCauchyConstant_nonneg hCb
  have hD : 0≤D := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hH : 0 < max 1 T := zero_lt_one.trans_le (le_max_left _ _)
  have hpoint (nr : ℕ) := hsource s T F hs hT h0 zX S ![np,nθ,nφ,nr] j
    a b I len w M A P L massScale Cs hS hS0 ha hb hab hlen hlenI hJI
    hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable
  calc
    _ ≤ ∑'nr : ℕ, (ENNReal.ofReal (Kg*min (ag*Real.sqrt (max 1 T*cappedRepresentative nr))
        (bg/Real.sqrt (max 1 T*cappedRepresentative nr)))+
      ENNReal.ofReal (Kb*min (ab*Real.sqrt (max 1 T*cappedRepresentative nr))
        (bb/Real.sqrt (max 1 T*cappedRepresentative nr)))) := by
      apply ENNReal.tsum_le_tsum
      intro nr
      split_ifs with hnr
      · have hn := hpoint nr hnr HX HZ
        dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
          Matrix.cons_val,Fin.reduceFinMk] at hn
        refine hn.trans_eq ?_
        exact ENNReal.ofReal_add (mul_nonneg hKg (by positivity)) (mul_nonneg hKb (by positivity))
      · exact bot_le
    _ ≤ ENNReal.ofReal (Kg*D*Real.sqrt (ag*bg))+
        ENNReal.ofReal (Kb*D*Real.sqrt (ab*bb)) := by
      rw [ENNReal.tsum_add]
      exact add_le_add (capped_sqrt_radius_ennreal_sum hag hbg hH hKg)
        (capped_sqrt_radius_ennreal_sum hab' hbb hH hKb)
    _ = _ := (ENNReal.ofReal_add (by positivity) (by positivity)).symm

lemma relativeCauchyConstant_factor (C E Z : ℝ) :
    relativeCauchyConstant C E Z=relativeCauchyConstant C E 1*Real.sqrt Z := by
  simp only [relativeCauchyConstant,Real.sqrt_one,mul_one]
  ring

lemma relative_source_balance_factor {I p ν R κ φ γ : ℝ}
    (hI : 0<I) (hp : 0≤p) (hν : 0≤ν) (hR : 0≤R) (hκ : 0≤κ)
    (hφ : 0<φ) (hγ : 0≤γ) :
    Real.sqrt ((I*p^2*ν^2*φ*γ)*(Real.sqrt I*R*ν*Real.sqrt κ*γ/φ))=
      (I : ℝ)^(3/4:ℝ)*p*ν^(3/2:ℝ)*Real.sqrt R*κ^(1/4:ℝ)*γ := by
  have he : (I*p^2*ν^2*φ*γ)*(Real.sqrt I*R*ν*Real.sqrt κ*γ/φ)=
      (I*Real.sqrt I)*p^2*ν^3*R*Real.sqrt κ*γ^2 := by field_simp
  have hIs : Real.sqrt (I*Real.sqrt I)=(I : ℝ)^(3/4:ℝ) := by
    rw [Real.sqrt_mul hI.le,Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul hI.le,
      ←Real.rpow_add hI]
    congr 1
    norm_num
  have hνs : Real.sqrt (ν^3)=ν^(3/2:ℝ) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_natCast_mul hν]
    norm_num
  have hκs : Real.sqrt (Real.sqrt κ)=κ^(1/4:ℝ) := by
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul hκ]
    congr 1
    norm_num
  rw [he,Real.sqrt_mul (by positivity : 0≤(I*Real.sqrt I)*p^2*ν^3*R*Real.sqrt κ),
    Real.sqrt_mul (by positivity : 0≤(I*Real.sqrt I)*p^2*ν^3*R),
    Real.sqrt_mul (by positivity : 0≤(I*Real.sqrt I)*p^2*ν^3),
    Real.sqrt_mul (by positivity : 0≤(I*Real.sqrt I)*p^2),
    Real.sqrt_mul (by positivity : 0≤I*Real.sqrt I),Real.sqrt_sq hp,Real.sqrt_sq hγ,hIs,hνs,hκs]

lemma relative_source_good_balance_factor {I p ν R κ φ θ : ℝ}
    (hI : 0<I) (hp : 0≤p) (hν : 0≤ν) (hR : 0≤R) (hκ : 0≤κ)
    (hφ : 0<φ) (hθ : 0<θ) :
    Real.sqrt ((I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*R*ν*Real.sqrt κ/θ^2))=
      (I : ℝ)^(3/4:ℝ)*p*ν^(3/2:ℝ)*Real.sqrt R*κ^(1/4:ℝ)*(φ/θ^2) := by
  have he : (I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*R*ν*Real.sqrt κ/θ^2)=
      (I*p^2*ν^2*φ*(φ/θ^2))*(Real.sqrt I*R*ν*Real.sqrt κ*(φ/θ^2)/φ) := by
    field_simp
  rw [he]
  exact relative_source_balance_factor hI hp hν hR hκ hφ (by positivity)

lemma Admissible.direct_source_shared_short_radial_factored {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ)
      (a b I len w M A P L massScale Cs : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → 0 < len → len ≤ I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
      massScale ≤ sourceRepresentative np/128 → massScale ≤ w/8 →
      512 ≤ cappedRepresentative j*sourceRepresentative np →
      32 ≤ cappedRepresentative j*w →
      2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative j+
        Real.sqrt (A*L/cappedRepresentative j)))⁻¹^2 →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
      let p := sourceRepresentative np
      let θ := cappedRepresentative nθ
      let φ := cappedRepresentative nφ
      let σ := cappedRepresentative j
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let R := Real.sqrt (1+I/len)
      let _ν := min θ σ
      let _κ := 1+φ/σ
      let Kg := relativeCauchyConstant Cg E
        (goodFieldBudget s (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>velocity (prefixFlow F.flow T zX t).2) 1 a b I nφ).toReal
      let Kb := relativeCauchyConstant Cb E
        (2*(magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I nφ).toReal)
      let D := dyadicBalanceConstant (1/2) (1/2)
      (∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤I then
        ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
          ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
      ENNReal.ofReal (D*(I : ℝ)^(3/4:ℝ)*p*Real.sqrt R*
        relativeSourceAngle θ φ σ*(Kg*(φ/θ^2)+Kb)) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_shared_short_radial_sum
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b I len w M A P L massScale Cs hS hS0
    ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable HX HZ
  dsimp only
  have hn := hsource s T F hs hT h0 zX S np nθ nφ j a b I len w M A P L massScale Cs
    hS hS0 ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable HX HZ
  dsimp only at hn
  have hp : 0 ≤ sourceRepresentative np := by dsimp [sourceRepresentative]; positivity
  have hθ := cappedRepresentative_pos nθ
  have hφ := cappedRepresentative_pos nφ
  have hσ := cappedRepresentative_pos j
  have hκ : 0≤1+cappedRepresentative nφ/cappedRepresentative j := by positivity
  have hb := relative_source_balance_factor (hlen.trans_le hlenI) hp (le_min hθ.le hσ.le)
    (Real.sqrt_nonneg (1+I/len)) hκ hφ (by norm_num : (0:ℝ)≤1)
  simp only [mul_one] at hb
  rw [relative_source_good_balance_factor (hlen.trans_le hlenI) hp (le_min hθ.le hσ.le)
    (Real.sqrt_nonneg _) hκ hφ hθ,hb] at hn
  convert hn using 1
  congr 1
  dsimp [relativeSourceAngle]
  ring

lemma Admissible.direct_source_shared_short_clipped {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ)
      (a b I w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → 0 < I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 < w →
      512 ≤ cappedRepresentative j*sourceRepresentative np →
      32 ≤ cappedRepresentative j*w →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let p := sourceRepresentative np
      let θ := cappedRepresentative nθ
      let φ := cappedRepresentative nφ
      let σ := cappedRepresentative j
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let R := Real.sqrt (1+I/min I (stabilityLength P 16384 M A p w σ/2))
      let _ν := min θ σ
      let _κ := 1+φ/σ
      let Kg := relativeCauchyConstant Cg E
        (goodFieldBudget s (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>velocity (prefixFlow F.flow T zX t).2) 1 a b I nφ).toReal
      let Kb := relativeCauchyConstant Cb E
        (2*(magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I nφ).toReal)
      let D := dyadicBalanceConstant (1/2) (1/2)
      (∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤I then
        ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
          ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
      ENNReal.ofReal (D*(I : ℝ)^(3/4:ℝ)*p*Real.sqrt R*
        relativeSourceAngle θ φ σ*(Kg*(φ/θ^2)+Kb)) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_shared_short_radial_factored
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b I w M A P hS hS0 ha hb hab hI hJI
    hM hA hP hw hpσ hwσ HX HZ
  dsimp only
  let p := sourceRepresentative np
  let σ := cappedRepresentative j
  let L := Real.log (2+P)
  let lam := stabilityLength P 16384 M A p w σ
  let len := min I (lam/2)
  let m := min p w/128
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hσ : 0<σ := cappedRepresentative_pos _
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
    convert hlenlam using 1; norm_num [lam]
  exact hsource s T F hs hT h0 zX S np nθ nφ j a b I len w M A P L m 128
    hS hS0 ha hb hab hlen hlenI hJI hM hA hP (Real.log_nonneg (by linarith)) hm hw
    (by norm_num) hmq hmw hpσ hwσ hstable HX HZ

def directReceiverGoodBudget {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (a b I : ℝ) (nφ : ℕ) : ℝ :=
  (goodFieldBudget s (fun t=>(prefixFlow F.flow T zX t).1)
    (fun t=>velocity (prefixFlow F.flow T zX t).2) 1 a b I nφ).toReal

def directReceiverMagneticBudget {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (a b I : ℝ) (nφ : ℕ) : ℝ :=
  2*(magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I nφ).toReal

lemma SmoothClassicalPrefix.directReceiverGoodBudget_sum {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hd : Admissible d) (F : PhaseFlowOn s.E s.B T) (zX : Phase)
    {a b I : ℝ} (ha : 0≤a) (hb : b≤T) (hI : 0<I) (hJI : b-a≤I) :
    Summable (directReceiverGoodBudget s F zX a b I) ∧
    (∑'n,directReceiverGoodBudget s F zX a b I n)≤20*datumEnergyNumber d := by
  have hJ : Icc a b⊆Icc (0:ℝ) T := fun _ ht=>⟨ha.trans ht.1,ht.2.trans hb⟩
  have hh := hs.energyPrefix.goodFieldBudget_uniform (fun t=>(prefixFlow F.flow T zX t).1)
    (fun t=>velocity (prefixFlow F.flow T zX t).2) 1 hJ hI hJI
  rw [hs.initial_energy_eq] at hh
  norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat] at hh
  have he : (5:ℝ≥0∞)*ENNReal.ofReal (4*datumEnergyNumber d)=ENNReal.ofReal (20*datumEnergyNumber d) := by
    rw [←ENNReal.ofReal_ofNat (n:=5),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤5)]
    congr 1
    ring
  rw [he] at hh
  have hf := ne_of_lt (lt_of_le_of_lt hh ENNReal.ofReal_lt_top)
  have hn := ENNReal.ne_top_of_tsum_ne_top hf
  refine ⟨ENNReal.summable_toReal hf,?_⟩
  dsimp only [directReceiverGoodBudget]
  rw [←ENNReal.tsum_toReal_eq hn]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  rwa [ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hd.datumEnergyNumber_nonneg)] at h

lemma SmoothClassicalPrefix.directReceiverMagneticBudget_sum {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hd : Admissible d) (F : PhaseFlowOn s.E s.B T) (zX : Phase)
    {a b I : ℝ} (hI : 0<I) (hJI : b-a≤I) :
    Summable (directReceiverMagneticBudget s F zX a b I) ∧
    (∑'n,directReceiverMagneticBudget s F zX a b I n)≤120*datumEnergyNumber d := by
  have hJ : Icc (max 0 (a-2*I)) (min T b)⊆Icc (0:ℝ) T :=
    fun _ ht=>⟨(le_max_left _ _).trans ht.1,ht.2.trans (min_le_left _ _)⟩
  have hlen : min T b-max 0 (a-2*I)≤3*I := by
    have h1 := min_le_right T b
    have h2 := le_max_right 0 (a-2*I)
    linarith
  have hh := hs.energyPrefix.magneticFieldBudget_uniform F.flow zX 1 hJ hI
    (by norm_num : (0:ℝ)≤3) hlen
  rw [hs.initial_energy_eq] at hh
  norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat] at hh
  have he : (10:ℝ≥0∞)*ENNReal.ofReal 3*ENNReal.ofReal (2*datumEnergyNumber d)=
      ENNReal.ofReal (60*datumEnergyNumber d) := by
    rw [←ENNReal.ofReal_ofNat (n:=10),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10),
      ←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10*3)]
    congr 1
    ring
  rw [he] at hh
  have hf := ne_of_lt (lt_of_le_of_lt hh ENNReal.ofReal_lt_top)
  have hn := ENNReal.ne_top_of_tsum_ne_top hf
  have hsum := ENNReal.summable_toReal hf
  refine ⟨hsum.mul_left 2,?_⟩
  dsimp only [directReceiverMagneticBudget]
  rw [tsum_mul_left,←ENNReal.tsum_toReal_eq hn]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  rw [ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hd.datumEnergyNumber_nonneg)] at h
  linarith

lemma budget_sqrt_weight_sum {ι : Type*} (S : Finset ι) (G W : ι→ℝ) {E N : ℝ}
    (hG : ∀i∈S,0≤G i) (hW : ∀i∈S,0≤W i) (hE : 0≤E) (hN : 0≤N)
    (hbudget : ∑i∈S,G i≤E) (hweight : ∑i∈S,W i≤N) :
    ∑i∈S,Real.sqrt (G i)*Real.sqrt (W i)≤Real.sqrt E*Real.sqrt N := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq S (fun i=>Real.sqrt (G i)) (fun i=>Real.sqrt (W i))
  have he : (∑i∈S,(Real.sqrt (G i))^2)=∑i∈S,G i := Finset.sum_congr rfl (fun i hi=>Real.sq_sqrt (hG i hi))
  have hn : (∑i∈S,(Real.sqrt (W i))^2)=∑i∈S,W i := Finset.sum_congr rfl (fun i hi=>Real.sq_sqrt (hW i hi))
  rw [he,hn] at hc
  have hu := mul_le_mul hbudget hweight (Finset.sum_nonneg hW) hE
  have hp : 0≤Real.sqrt E*Real.sqrt N := by positivity
  have hs : (Real.sqrt E*Real.sqrt N)^2=E*N := by rw [mul_pow,Real.sq_sqrt hE,Real.sq_sqrt hN]
  nlinarith

lemma budget_sqrt_sum {ι : Type*} (S : Finset ι) (G : ι→ℝ) {E N : ℝ}
    (hG : ∀i∈S,0≤G i) (hE : 0≤E) (hN : 0≤N)
    (hbudget : ∑i∈S,G i≤E) (hcard : (S.card:ℝ)≤N) :
    ∑i∈S,Real.sqrt (G i)≤Real.sqrt E*Real.sqrt N := by
  have hh := budget_sqrt_weight_sum S G (fun _=>1) hG (by intros; norm_num) hE hN hbudget
    (by simpa using hcard)
  simpa only [Real.sqrt_one,mul_one] using hh

lemma source_sqrt_sum_bound {x : ℝ} (_hx : 0≤x) (S : Finset ℕ)
    (hS : ∀n∈S,sourceRepresentative n≤x) : ∑n∈S,Real.sqrt (sourceRepresentative n)≤4*Real.sqrt x := by
  have hp (n : ℕ) : 0 ≤ sourceRepresentative n := by dsimp [sourceRepresentative]; positivity
  have hgeom (N : ℕ) : ∑n∈Finset.range (N+1),Real.sqrt (sourceRepresentative n)≤4*Real.sqrt (sourceRepresentative N) := by
    induction N with
    | zero => norm_num [sourceRepresentative,Finset.sum_range_succ]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have he : sourceRepresentative (N+1)=2*sourceRepresentative N := by
        dsimp only [sourceRepresentative]
        rw [pow_succ]
        ring
      rw [he,Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
      have hs : (4:ℝ)≤3*Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]
      nlinarith [mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (sourceRepresentative N))]
  by_cases hne : S.Nonempty
  · let N := S.max' hne
    have hsub : S⊆Finset.range (N+1) := by
      intro n hn
      apply Finset.mem_range.mpr
      have hh := S.le_max' n hn
      change n≤N at hh
      omega
    have hs : (∑n∈S,Real.sqrt (sourceRepresentative n))≤∑n∈Finset.range (N+1),Real.sqrt (sourceRepresentative n) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>Real.sqrt_nonneg _)
    exact hs.trans ((hgeom N).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hS N (S.max'_mem hne))) (by norm_num)))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty]
    positivity

lemma source_stability_sqrt_sum {P w : ℝ} (hP : 0<P) (hw : 0<w) (hwP : w≤P)
    (S : Finset ℕ) (hS : ∀n∈S,sourceRepresentative n≤P) :
    ∑n∈S,sourceRepresentative n*Real.sqrt (P/min (sourceRepresentative n) w)≤
      4*P*Real.sqrt (P/w) := by
  have hp (n : ℕ) : 0<sourceRepresentative n := by dsimp [sourceRepresentative]; positivity
  have hpoint (n : ℕ) (hn : n∈S) :
      sourceRepresentative n*Real.sqrt (P/min (sourceRepresentative n) w)≤
        Real.sqrt P*Real.sqrt (P/w)*Real.sqrt (sourceRepresentative n) := by
    let p := sourceRepresentative n
    have hm : 0 < min p w := lt_min (hp n) hw
    have hprod := product_le_min_scale (hp n).le hw.le (hS n hn) hwP
    have hratio : p/min p w≤P/w := (div_le_div_iff₀ hm hw).mpr (by simpa only [p,mul_comm] using hprod)
    have hq : p^2*(P/min p w)≤P*(P/w)*p := by
      calc
        _=(P*p)*(p/min p w) := by ring
        _≤(P*p)*(P/w) := mul_le_mul_of_nonneg_left hratio (mul_nonneg hP.le (hp n).le)
        _=_ := by ring
    have heL : (p*Real.sqrt (P/min p w))^2=p^2*(P/min p w) := by
      rw [mul_pow,Real.sq_sqrt (div_nonneg hP.le hm.le)]
    have heR : (Real.sqrt P*Real.sqrt (P/w)*Real.sqrt p)^2=P*(P/w)*p := by
      simp only [mul_pow,Real.sq_sqrt hP.le,Real.sq_sqrt (div_nonneg hP.le hw.le),Real.sq_sqrt (show 0≤p from (hp n).le)]
    have hpos : 0≤Real.sqrt P*Real.sqrt (P/w)*Real.sqrt p := by positivity
    nlinarith
  calc
    _≤∑n∈S,Real.sqrt P*Real.sqrt (P/w)*Real.sqrt (sourceRepresentative n) := Finset.sum_le_sum hpoint
    _=(Real.sqrt P*Real.sqrt (P/w))*(∑n∈S,Real.sqrt (sourceRepresentative n)) := (Finset.mul_sum ..).symm
    _≤(Real.sqrt P*Real.sqrt (P/w))*(4*Real.sqrt P) :=
      mul_le_mul_of_nonneg_left (source_sqrt_sum_bound hP.le S hS) (by positivity)
    _=4*(Real.sqrt P)^2*Real.sqrt (P/w) := by ring
    _=4*P*Real.sqrt (P/w) := by rw [Real.sq_sqrt hP.le]

lemma receiver_scale_card {P w : ℝ} (hP : 1≤P) (hw : 0<w) (hwP : w≤P)
    (hL : 1≤Real.log (2+P)) (S : Finset ℕ)
    (hS : ∀n∈S,1/w≤cappedRepresentative n) :
    (S.card:ℝ)≤pairCountConstant*Real.log (2+P) := by
  obtain ⟨N,hN,hcard⟩ := exists_dyadic_count_log hP
  have hsub : S⊆Finset.range N := by
    intro n hn
    apply Finset.mem_range.mpr
    apply index_lt_of_two_pow_le _ hN
    have hh := mul_le_mul_of_nonneg_right (hS n hn) (show 0≤(2:ℝ)^n by positivity)
    rw [cappedRepresentative_mul_pow] at hh
    have hh' : (2:ℝ)^n≤w := by
      have he : (1/w)*(2:ℝ)^n=(2:ℝ)^n/w := by ring
      rw [he] at hh
      exact (div_le_iff₀ hw).mp hh |>.trans_eq (one_mul w)
    exact hh'.trans hwP
  have hc : (S.card:ℝ)≤(N:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range N)
  apply hc.trans (hcard.trans _)
  have hd := div_le_div_of_nonneg_right
    (Real.log_le_log (zero_lt_one.trans_le hP) (by linarith : P≤2+P))
    (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  unfold pairCountConstant
  simp only [div_eq_mul_inv,one_mul] at hd ⊢
  nlinarith

lemma receiver_good_sqrt_sum (S : Finset ℕ) (G : ℕ→ℝ) {E : ℝ}
    (hG : ∀n∈S,0≤G n) (hE : 0≤E) (hbudget : ∑n∈S,G n≤E) :
    ∑n∈S,Real.sqrt (G n)*Real.sqrt (cappedRepresentative n)≤Real.sqrt E*Real.sqrt 2 := by
  apply budget_sqrt_weight_sum S G cappedRepresentative hG
    (fun n _=>(cappedRepresentative_pos n).le) hE (by norm_num) hbudget
  have hh := capped_positive_power_sum_unscaled (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)<1) S (fun n _=>cappedRepresentative_le_one n)
  norm_num at hh
  exact hh

lemma momentum_affine_stability_sum {P w a b : ℝ} (hP : 0<P) (hw : 0<w) (hwP : w≤P)
    (ha : 0≤a) (hb : 0≤b) (S : Finset ℕ) (hS : ∀n∈S,sourceRepresentative n≤P) :
    ∑n∈S,sourceRepresentative n*(a+b*Real.sqrt (P/min (sourceRepresentative n) w))≤
      2*P*a+4*P*Real.sqrt (P/w)*b := by
  calc
    _=(∑n∈S,sourceRepresentative n)*a+(∑n∈S,sourceRepresentative n*Real.sqrt (P/min (sourceRepresentative n) w))*b := by
      simp only [Finset.sum_mul,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _≤_ := add_le_add
      (mul_le_mul_of_nonneg_right (sourceRepresentative_sum_bound hP.le S hS) ha)
      (mul_le_mul_of_nonneg_right (source_stability_sqrt_sum hP hw hwP S hS) hb)

lemma source_stability_sqrt_sum_upper {P Q w : ℝ} (hP : 0<P) (hQ : 0<Q) (hw : 0<w) (hwQ : w≤Q)
    (S : Finset ℕ) (hS : ∀n∈S,sourceRepresentative n≤Q) :
    ∑n∈S,sourceRepresentative n*Real.sqrt (P/min (sourceRepresentative n) w)≤
      4*Q*Real.sqrt (P/w) := by
  have hp (n : ℕ) : 0<sourceRepresentative n := by dsimp [sourceRepresentative]; positivity
  have hpoint (n : ℕ) (hn : n∈S) :
      sourceRepresentative n*Real.sqrt (P/min (sourceRepresentative n) w)≤
        Real.sqrt Q*Real.sqrt (P/w)*Real.sqrt (sourceRepresentative n) := by
    let p := sourceRepresentative n
    have hm : 0 < min p w := lt_min (hp n) hw
    have hprod := product_le_min_scale (hp n).le hw.le (hS n hn) hwQ
    have hratio : p/min p w≤Q/w := (div_le_div_iff₀ hm hw).mpr (by simpa only [p,mul_comm] using hprod)
    have hq : p^2*(P/min p w)≤Q*(P/w)*p := by
      calc
        _=(P*p)*(p/min p w) := by ring
        _≤(P*p)*(Q/w) := mul_le_mul_of_nonneg_left hratio (mul_nonneg hP.le (hp n).le)
        _=_ := by ring
    have heL : (p*Real.sqrt (P/min p w))^2=p^2*(P/min p w) := by
      rw [mul_pow,Real.sq_sqrt (div_nonneg hP.le hm.le)]
    have heR : (Real.sqrt Q*Real.sqrt (P/w)*Real.sqrt p)^2=Q*(P/w)*p := by
      simp only [mul_pow,Real.sq_sqrt hQ.le,Real.sq_sqrt (div_nonneg hP.le hw.le),Real.sq_sqrt (show 0≤p from (hp n).le)]
    have hpos : 0≤Real.sqrt Q*Real.sqrt (P/w)*Real.sqrt p := by positivity
    nlinarith
  calc
    _≤∑n∈S,Real.sqrt Q*Real.sqrt (P/w)*Real.sqrt (sourceRepresentative n) := Finset.sum_le_sum hpoint
    _=(Real.sqrt Q*Real.sqrt (P/w))*(∑n∈S,Real.sqrt (sourceRepresentative n)) := (Finset.mul_sum ..).symm
    _≤(Real.sqrt Q*Real.sqrt (P/w))*(4*Real.sqrt Q) :=
      mul_le_mul_of_nonneg_left (source_sqrt_sum_bound hQ.le S hS) (by positivity)
    _=4*(Real.sqrt Q)^2*Real.sqrt (P/w) := by ring
    _=4*Q*Real.sqrt (P/w) := by rw [Real.sq_sqrt hQ.le]

lemma rpow_three_quarters_le_sqrt {I : ℝ} (hI : 0<I) (hI1 : I≤1) :
    (I : ℝ)^(3/4:ℝ)≤Real.sqrt I := by
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_ge hI hI1 (by norm_num)

lemma plain_magnetic_three_quarters {I L : ℝ} (hI : 0<I) (hL : 0≤L) :
    (I : ℝ)^(3/4:ℝ)*Real.sqrt L≤Real.sqrt I+I*L := by
  have he : (I : ℝ)^(3/4:ℝ)=Real.sqrt I*(I : ℝ)^(1/4:ℝ) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hI]
    congr 1
    norm_num
  have he' : Real.sqrt I*((I : ℝ)^(1/4:ℝ)*Real.sqrt L)^2=I*L := by
    rw [mul_pow,Real.sq_sqrt hL,←Real.rpow_natCast,←Real.rpow_mul hI.le,
      Real.sqrt_eq_rpow]
    rw [←mul_assoc,←Real.rpow_add hI]
    norm_num
  have hx : (I : ℝ)^(1/4:ℝ)*Real.sqrt L≤1+((I : ℝ)^(1/4:ℝ)*Real.sqrt L)^2 := by
    nlinarith [sq_nonneg ((I : ℝ)^(1/4:ℝ)*Real.sqrt L-1/2)]
  have hh := mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg I)
  rw [mul_add,mul_one,he'] at hh
  calc
    _=Real.sqrt I*((I : ℝ)^(1/4:ℝ)*Real.sqrt L) := by rw [he]; ring
    _≤_ := hh

lemma source_parameter_scalar {M A L X : ℝ} (hM : 1≤M) (hA : 1≤A) (hL : 1≤L) (hX : 1≤X) :
    (Real.sqrt M+Real.sqrt (Real.sqrt (A*L)))*Real.sqrt X*Real.sqrt L≤
      (M+Real.sqrt A)*X*L := by
  have hM0 : 0≤M := zero_le_one.trans hM
  have hA0 : 0≤A := zero_le_one.trans hA
  have hL0 : 0≤L := zero_le_one.trans hL
  have hX0 : 0≤X := zero_le_one.trans hX
  have hrootM : Real.sqrt M≤M := Real.sqrt_le_self_iff.mpr (Or.inr hM)
  have hrootL : Real.sqrt L≤L := Real.sqrt_le_self_iff.mpr (Or.inr hL)
  have hrootX : Real.sqrt X≤X := Real.sqrt_le_self_iff.mpr (Or.inr hX)
  have hAL : 1≤A*L := one_le_mul_of_one_le_of_one_le hA hL
  have hrootAL : 1≤Real.sqrt (A*L) := by simpa using Real.sqrt_le_sqrt hAL
  have hdouble : Real.sqrt (Real.sqrt (A*L))≤Real.sqrt A*Real.sqrt L := by
    rw [←Real.sqrt_mul hA0]
    exact Real.sqrt_le_self_iff.mpr (Or.inr hrootAL)
  have hU : (Real.sqrt M+Real.sqrt (Real.sqrt (A*L)))*Real.sqrt L≤(M+Real.sqrt A)*L := by
    calc
      _≤(M+Real.sqrt A*Real.sqrt L)*Real.sqrt L :=
        mul_le_mul_of_nonneg_right (add_le_add hrootM hdouble) (Real.sqrt_nonneg L)
      _=M*Real.sqrt L+Real.sqrt A*L := by
        rw [add_mul]
        rw [mul_assoc,←pow_two,Real.sq_sqrt hL0]
      _≤M*L+Real.sqrt A*L := add_le_add (mul_le_mul_of_nonneg_left hrootL hM0) le_rfl
      _=_ := by ring
  calc
    _=((Real.sqrt M+Real.sqrt (Real.sqrt (A*L)))*Real.sqrt L)*Real.sqrt X := by ring
    _≤((M+Real.sqrt A)*L)*X := mul_le_mul hU hrootX (Real.sqrt_nonneg X) (by positivity)
    _=_ := by ring

lemma remaining_source_uniform_numerics {I P w M A L a b c : ℝ}
    (hI : 0<I) (hI1 : I≤1) (hP : 0<P) (hw : 0<w) (hwP : w≤P)
    (hM : 1≤M) (hA : 1≤A) (hL : 1≤L) (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) :
    2*P*(I : ℝ)^(3/4:ℝ)*(a+b*Real.sqrt L)+
      4*I*P*Real.sqrt (P/w)*(Real.sqrt M+Real.sqrt (Real.sqrt (A*L)))*c*Real.sqrt L≤
      (2*a+2*b+4*c)*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*L/w) := by
  let Q := P*Real.sqrt I
  let V := (M+Real.sqrt A)*I*P^2*L/w
  have hM0 : 0≤M := zero_le_one.trans hM
  have hA0 : 0≤A := zero_le_one.trans hA
  have hL0 : 0≤L := zero_le_one.trans hL
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hV : 0≤V := by dsimp [V]; positivity
  have hX : 1≤P/w := (le_div_iff₀ hw).mpr (by simpa using hwP)
  have hplain := rpow_three_quarters_le_sqrt hI hI1
  have hmag := plain_magnetic_three_quarters hI hL0
  have hPL : I*P*L≤V := by
    have hM1 : 1≤M+Real.sqrt A := by linarith [Real.sqrt_nonneg A]
    have hx : 1≤(M+Real.sqrt A)*(P/w) := one_le_mul_of_one_le_of_one_le hM1 hX
    have hh := mul_le_mul_of_nonneg_left hx (show 0≤I*P*L by positivity)
    calc
      _=(I*P*L)*1 := (mul_one _).symm
      _≤(I*P*L)*((M+Real.sqrt A)*(P/w)) := hh
      _=V := by dsimp [V]; ring
  have hg : 2*P*(I : ℝ)^(3/4:ℝ)*a≤2*a*Q := by
    have hh := mul_le_mul_of_nonneg_left hplain (show 0≤2*P*a by positivity)
    dsimp only [Q]
    nlinarith only [hh]
  have hb' : 2*P*(I : ℝ)^(3/4:ℝ)*b*Real.sqrt L≤2*b*(Q+V) := by
    have hh := mul_le_mul_of_nonneg_left hmag (show 0≤2*P*b by positivity)
    have hh' := mul_le_mul_of_nonneg_left hPL (show 0≤2*b by positivity)
    dsimp only [Q] at *
    nlinarith only [hh,hh']
  have hp' : 4*I*P*Real.sqrt (P/w)*(Real.sqrt M+Real.sqrt (Real.sqrt (A*L)))*c*Real.sqrt L≤4*c*V := by
    calc
      _=(4*I*P*c)*((Real.sqrt M+Real.sqrt (Real.sqrt (A*L)))*Real.sqrt (P/w)*Real.sqrt L) := by ring
      _≤(4*I*P*c)*((M+Real.sqrt A)*(P/w)*L) :=
        mul_le_mul_of_nonneg_left (source_parameter_scalar hM hA hL hX) (by positivity)
      _=4*c*V := by dsimp [V]; ring
  dsimp only [Q,V] at hg hb' hp' hQ hV ⊢
  nlinarith [mul_nonneg ha hV,mul_nonneg hc hQ]

lemma receiver_shared_two_budget_sum (S : Finset ℕ) (G B : ℕ→ℝ)
    {Eg Eb N g b g₀ g₁ b₀ b₁ x : ℝ}
    (hG : ∀n∈S,0≤G n) (hB : ∀n∈S,0≤B n)
    (hEg : 0≤Eg) (hEb : 0≤Eb) (hN : 0≤N)
    (hg : 0≤g) (hb : 0≤b) (hg₀ : 0≤g₀) (hg₁ : 0≤g₁)
    (hb₀ : 0≤b₀) (hb₁ : 0≤b₁) (hx : 0≤x)
    (hbudgetG : ∑n∈S,G n≤Eg) (hbudgetB : ∑n∈S,B n≤Eb) (hcard : (S.card:ℝ)≤N) :
    ∑n∈S,(g*Real.sqrt (G n)*(g₀*Real.sqrt (cappedRepresentative n)+x*g₁)+
      b*Real.sqrt (B n)*(b₀+x*b₁))≤
      g*g₀*Real.sqrt Eg*Real.sqrt 2+b*b₀*Real.sqrt Eb*Real.sqrt N+
        x*(g*g₁*Real.sqrt Eg+b*b₁*Real.sqrt Eb)*Real.sqrt N := by
  have hgw := receiver_good_sqrt_sum S G hG hEg hbudgetG
  have hgs := budget_sqrt_sum S G hG hEg hN hbudgetG hcard
  have hbs := budget_sqrt_sum S B hB hEb hN hbudgetB hcard
  calc
    _=(g*g₀)*(∑n∈S,Real.sqrt (G n)*Real.sqrt (cappedRepresentative n))+
        (b*b₀)*(∑n∈S,Real.sqrt (B n))+
        (x*g*g₁)*(∑n∈S,Real.sqrt (G n))+(x*b*b₁)*(∑n∈S,Real.sqrt (B n)) := by
      simp only [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _≤(g*g₀)*(Real.sqrt Eg*Real.sqrt 2)+(b*b₀)*(Real.sqrt Eb*Real.sqrt N)+
        (x*g*g₁)*(Real.sqrt Eg*Real.sqrt N)+(x*b*b₁)*(Real.sqrt Eb*Real.sqrt N) := by
      exact add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hgw (by positivity))
        (mul_le_mul_of_nonneg_left hbs (by positivity)))
        (mul_le_mul_of_nonneg_left hgs (by positivity)))
        (mul_le_mul_of_nonneg_left hbs (by positivity))
    _=_ := by ring

lemma momentum_affine_stability_sum_upper {P Q w a b : ℝ}
    (hP : 0<P) (hQ : 0<Q) (hw : 0<w) (hwQ : w≤Q)
    (ha : 0≤a) (hb : 0≤b) (S : Finset ℕ) (hS : ∀n∈S,sourceRepresentative n≤Q) :
    ∑n∈S,sourceRepresentative n*(a+b*Real.sqrt (P/min (sourceRepresentative n) w))≤
      2*Q*a+4*Q*Real.sqrt (P/w)*b := by
  calc
    _=(∑n∈S,sourceRepresentative n)*a+(∑n∈S,sourceRepresentative n*Real.sqrt (P/min (sourceRepresentative n) w))*b := by
      simp only [Finset.sum_mul,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _≤_ := add_le_add
      (mul_le_mul_of_nonneg_right (sourceRepresentative_sum_bound hQ.le S hS) ha)
      (mul_le_mul_of_nonneg_right (source_stability_sqrt_sum_upper hP hQ hw hwQ S hS) hb)

lemma remaining_source_budget_total (Sp Sφ : Finset ℕ) (G B : ℕ→ℝ)
    {I P w M A L Eg Eb N g b g₀ g₁ b₀ b₁ H : ℝ}
    (hI : 0<I) (hI1 : I≤1) (hP : 0<P) (hw : 0<w) (hwP : w≤P)
    (hM : 1≤M) (hA : 1≤A) (hL : 1≤L)
    (hG : ∀n∈Sφ,0≤G n) (hB : ∀n∈Sφ,0≤B n)
    (hEg : 0≤Eg) (hEb : 0≤Eb) (hN : 0≤N)
    (hg : 0≤g) (hb : 0≤b) (hg₀ : 0≤g₀) (hg₁ : 0≤g₁)
    (hb₀ : 0≤b₀) (hb₁ : 0≤b₁) (hH : 0≤H)
    (hbudgetG : ∑n∈Sφ,G n≤Eg) (hbudgetB : ∑n∈Sφ,B n≤Eb)
    (hcard : (Sφ.card:ℝ)≤N*L) (hp : ∀n∈Sp,sourceRepresentative n≤128*P) :
    let U := Real.sqrt M+Real.sqrt (Real.sqrt (A*L))
    let a := g*g₀*Real.sqrt Eg*Real.sqrt 2
    let b' := b*b₀*Real.sqrt Eb*Real.sqrt N
    let c := H*(g*g₁*Real.sqrt Eg+b*b₁*Real.sqrt Eb)*Real.sqrt N
    (∑np∈Sp,∑nf∈Sφ,(I : ℝ)^(3/4:ℝ)*sourceRepresentative np*
      (g*Real.sqrt (G nf)*(g₀*Real.sqrt (cappedRepresentative nf)+
          H*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min (sourceRepresentative np) w)*U*g₁)+
       b*Real.sqrt (B nf)*(b₀+
          H*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min (sourceRepresentative np) w)*U*b₁)))≤
      128*(2*a+2*b'+4*c)*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*L/w) := by
  dsimp only
  let U := Real.sqrt M+Real.sqrt (Real.sqrt (A*L))
  let a := g*g₀*Real.sqrt Eg*Real.sqrt 2
  let b' := b*b₀*Real.sqrt Eb*Real.sqrt N
  let c := H*(g*g₁*Real.sqrt Eg+b*b₁*Real.sqrt Eb)*Real.sqrt N
  have hU : 0≤U := by dsimp [U]; positivity
  have ha : 0≤a := by dsimp [a]; positivity
  have hb' : 0≤b' := by dsimp [b']; positivity
  have hc : 0≤c := by dsimp [c]; positivity
  have hL0 : 0≤L := zero_le_one.trans hL
  have hquarter : (I : ℝ)^(3/4:ℝ)*(I : ℝ)^(1/4:ℝ)=I := by
    rw [←Real.rpow_add hI]
    norm_num
  have hinner (np : ℕ) :
      (∑nf∈Sφ,(I : ℝ)^(3/4:ℝ)*sourceRepresentative np*
        (g*Real.sqrt (G nf)*(g₀*Real.sqrt (cappedRepresentative nf)+
            H*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min (sourceRepresentative np) w)*U*g₁)+
         b*Real.sqrt (B nf)*(b₀+
            H*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min (sourceRepresentative np) w)*U*b₁)))≤
      (I : ℝ)^(3/4:ℝ)*sourceRepresentative np*
        (a+b'*Real.sqrt L+((I : ℝ)^(1/4:ℝ)*U*c*Real.sqrt L)*Real.sqrt (P/min (sourceRepresentative np) w)) := by
    rw [←Finset.mul_sum]
    have hs := receiver_shared_two_budget_sum Sφ G B hG hB hEg hEb
      (mul_nonneg hN hL0) hg hb hg₀ hg₁ hb₀ hb₁
      (show 0≤H*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min (sourceRepresentative np) w)*U by positivity)
      hbudgetG hbudgetB hcard
    apply mul_le_mul_of_nonneg_left _ (by dsimp [sourceRepresentative]; positivity)
    calc
      _≤_ := hs
      _=_ := by rw [Real.sqrt_mul hN]; dsimp [a,b',c]; ring
  calc
    _≤∑np∈Sp,(I : ℝ)^(3/4:ℝ)*sourceRepresentative np*
        (a+b'*Real.sqrt L+((I : ℝ)^(1/4:ℝ)*U*c*Real.sqrt L)*Real.sqrt (P/min (sourceRepresentative np) w)) :=
      Finset.sum_le_sum (fun np _=>hinner np)
    _=(I : ℝ)^(3/4:ℝ)*(∑np∈Sp,sourceRepresentative np*
        (a+b'*Real.sqrt L+((I : ℝ)^(1/4:ℝ)*U*c*Real.sqrt L)*Real.sqrt (P/min (sourceRepresentative np) w))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro np hnp
      ring
    _≤(I : ℝ)^(3/4:ℝ)*(2*(128*P)*(a+b'*Real.sqrt L)+
      4*(128*P)*Real.sqrt (P/w)*((I : ℝ)^(1/4:ℝ)*U*c*Real.sqrt L)) :=
      mul_le_mul_of_nonneg_left (momentum_affine_stability_sum_upper hP (by positivity) hw
        (by linarith : w≤128*P) (by positivity) (by positivity) Sp hp) (by positivity)
    _=128*(2*P*(I : ℝ)^(3/4:ℝ)*(a+b'*Real.sqrt L)+4*I*P*Real.sqrt (P/w)*U*c*Real.sqrt L) := by
      calc
        _=128*(2*P*(I : ℝ)^(3/4:ℝ)*(a+b'*Real.sqrt L)+
          4*((I : ℝ)^(3/4:ℝ)*(I : ℝ)^(1/4:ℝ))*P*Real.sqrt (P/w)*U*c*Real.sqrt L) := by ring
        _=_ := by rw [hquarter]
    _≤_ := by
      have hh := mul_le_mul_of_nonneg_left
        (remaining_source_uniform_numerics hI hI1 hP hw hwP hM hA hL ha hb' hc)
        (by norm_num : (0:ℝ)≤128)
      simpa only [U,a,b',c,mul_assoc] using hh

lemma receiver_scale_card_enlarged {P w : ℝ} (hP : 1≤P) (hw : 0<w) (hwP : w≤P)
    (hL : 1≤Real.log (2+P)) (S : Finset ℕ)
    (hS : ∀n∈S,1/(32*w)≤cappedRepresentative n) :
    (S.card:ℝ)≤(1+Real.log 32)*pairCountConstant*Real.log (2+P) := by
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hP' : 1≤32*P := by linarith
  have hlog : Real.log (2+P)≤Real.log (2+32*P) :=
    Real.log_le_log (by positivity) (by linarith)
  have hc := receiver_scale_card hP' (by positivity : 0<32*w)
    (mul_le_mul_of_nonneg_left hwP (by norm_num : (0:ℝ)≤32)) (hL.trans hlog) S hS
  have hl : Real.log (2+32*P)≤(1+Real.log 32)*Real.log (2+P) := by
    calc
      _≤Real.log (32*(2+P)) := Real.log_le_log (by positivity) (by linarith)
      _=Real.log 32+Real.log (2+P) := Real.log_mul (by norm_num) (by positivity)
      _≤_ := by nlinarith [Real.log_nonneg (by norm_num : (1:ℝ)≤32)]
  have hN : 0≤pairCountConstant := by unfold pairCountConstant; positivity
  exact hc.trans (by nlinarith [mul_le_mul_of_nonneg_left hl hN])

lemma Admissible.direct_source_shared_short_angles {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0≤Cg ∧ 0≤Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nφ : ℕ) (a b I w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → a≤b → 0<I → b-a≤I → 0<M → 0≤A → 0<P → 0<w →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ (Sθ : Finset ℕ) (Sσ : ℕ→Finset ℕ),
      (∀i∈Sθ,cappedRepresentative nφ≤16*cappedRepresentative i) →
      (∀i∈Sθ,∀j∈Sσ i,cappedRepresentative j≤136*cappedRepresentative i ∧
        512≤cappedRepresentative j*sourceRepresentative np ∧ 32≤cappedRepresentative j*w) →
      let p := sourceRepresentative np
      let φ := cappedRepresentative nφ
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun i j nr=>relativeRepresentativeClosedBin T w ![np,i,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Kg := relativeCauchyConstant Cg E
        (goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I nφ).toReal
      let Kb := relativeCauchyConstant Cb E
        (2*(magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I nφ).toReal)
      let D := dyadicBalanceConstant (1/2) (1/2)
      let R₁ := 2*Real.sqrt 16384*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min p w)*
        (Real.sqrt M+Real.sqrt (Real.sqrt (A*Real.log (2+P))))
      (∑i∈Sθ,∑j∈Sσ i,∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤I then
        ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B i j nr) z
          ∂physicalBinMeasure V (B i j nr) (Icc a b) else 0) ≤
      ENNReal.ofReal (D*(I : ℝ)^(3/4:ℝ)*p*
        (Kg*(2*remainingGoodConstant 136 16 0*Real.sqrt φ+R₁*remainingGoodConstant 136 16 (1/2))+
         Kb*(2*remainingMagneticConstant 136 16 0+R₁*remainingMagneticConstant 136 16 (1/2)))) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_shared_short_clipped
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S np nφ a b I w M A P hS hS0 ha hb hab hI hJI hM hA hP hw HX HZ
    Sθ Sσ hθ hσ
  dsimp only
  let p := sourceRepresentative np
  let φ := cappedRepresentative nφ
  let E := ∫x : Vec,totalEnergy s (0,x)
  let Kg := relativeCauchyConstant Cg E
    (goodFieldBudget s (fun t=>(prefixFlow F.flow T zX t).1)
      (fun t=>velocity (prefixFlow F.flow T zX t).2) 1 a b I nφ).toReal
  let Kb := relativeCauchyConstant Cb E
    (2*(magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I nφ).toReal)
  let D := dyadicBalanceConstant (1/2) (1/2)
  let R (j : ℕ) := Real.sqrt (Real.sqrt (1+I/min I (stabilityLength P 16384 M A p w (cappedRepresentative j)/2)))
  let U (i j : ℕ) := R j*relativeSourceAngle (cappedRepresentative i) φ (cappedRepresentative j)*
    (Kg*(φ/(cappedRepresentative i)^2)+Kb)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hφ : 0<φ := cappedRepresentative_pos _
  have hKg : 0≤Kg := relativeCauchyConstant_nonneg hCg
  have hKb : 0≤Kb := relativeCauchyConstant_nonneg hCb
  have hD : 0≤D := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hU (i j : ℕ) : 0≤U i j := by
    dsimp only [U]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (relativeSourceAngle_nonneg
      (cappedRepresentative_pos i).le hφ.le (cappedRepresentative_pos j))) (by positivity)
  have hn := remaining_stable_source_angular hI hP (by norm_num : (0:ℝ)<16384) hM hA hp hw hφ
    (by norm_num : (0:ℝ)<136) (by norm_num : (0:ℝ)<16) hKg hKb Sθ Sσ hθ
      (fun i hi j hj=>(hσ i hi j hj).1)
  calc
    _≤∑i∈Sθ,∑j∈Sσ i,ENNReal.ofReal ((D*(I : ℝ)^(3/4:ℝ)*p)*U i j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hh := hsource s T F hs hT h0 zX S np i nφ j a b I w M A P hS hS0 ha hb hab
        hI hJI hM hA hP hw (hσ i hi j hj).2.1 (hσ i hi j hj).2.2 HX HZ
      dsimp only at hh
      simpa only [U,R,D,Kg,Kb,p,φ,E,mul_assoc] using hh
    _=ENNReal.ofReal ((D*(I : ℝ)^(3/4:ℝ)*p)*(∑i∈Sθ,∑j∈Sσ i,U i j)) := by
      rw [Finset.mul_sum]
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg]
        exact fun j _=>mul_nonneg (by positivity) (hU i j)
      · intro i hi
        exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _=>hU i j))
    _≤_ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hn (by positivity))

lemma remainingGoodConstant_nonneg {K κ β : ℝ} (hK : 0≤K) (hκ : 0≤κ)
    (hβ : 0≤β) (hβ1 : β≤1/2) : 0≤remainingGoodConstant K κ β := by
  unfold remainingGoodConstant
  exact mul_nonneg (mul_nonneg (relativeAngularConstant_nonneg hK hκ (by linarith))
    (inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_le_one (by norm_num) (by norm_num) (by linarith)))))
    (Real.rpow_nonneg hκ _)

lemma remainingMagneticConstant_nonneg {K κ β : ℝ} (hK : 0≤K) (hκ : 0≤κ)
    (_hβ : 0≤β) (hβ1 : β≤1/2) : 0≤remainingMagneticConstant K κ β := by
  unfold remainingMagneticConstant
  exact mul_nonneg (relativeAngularConstant_nonneg hK hκ (by linarith))
    (inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_le_one (by norm_num) (by norm_num) (by linarith))))

lemma Admissible.direct_remaining_source_short_uniform {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T →
    ∀ (zX : Phase) (S : Set Phase) (a b I w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I →
      1≤M → 1≤A → 1≤P → 1≤Real.log (2+P) → 0<w → w≤P →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ (Sp Sφ : Finset ℕ) (Sθ : ℕ→ℕ→Finset ℕ) (Sσ : ℕ→ℕ→ℕ→Finset ℕ),
      (∀np∈Sp,sourceRepresentative np≤128*P) →
      (∀nf∈Sφ,1/(32*w)≤cappedRepresentative nf) →
      (∀np∈Sp,∀nf∈Sφ,∀nt∈Sθ np nf,cappedRepresentative nf≤16*cappedRepresentative nt) →
      (∀np∈Sp,∀nf∈Sφ,∀nt∈Sθ np nf,∀j∈Sσ np nf nt,
        cappedRepresentative j≤136*cappedRepresentative nt ∧
        512≤cappedRepresentative j*sourceRepresentative np ∧ 32≤cappedRepresentative j*w) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun np nt nf j nr=>relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j
      (∑np∈Sp,∑nf∈Sφ,∑nt∈Sθ np nf,∑j∈Sσ np nf nt,∑'nr : ℕ,
        if max 1 T*cappedRepresentative nr≤I then
          ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B np nt nf j nr) z
            ∂physicalBinMeasure V (B np nt nf j nr) (Icc a b) else 0)≤
      ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cg,Cb,hCg,hCb,hbin⟩ := hd.direct_source_shared_short_angles
  let E := datumEnergyNumber d
  let Eg := 20*E
  let Eb := 120*E
  let N := (1+Real.log 32)*pairCountConstant
  let g := relativeCauchyConstant Cg E 1
  let b' := relativeCauchyConstant Cb E 1
  let g₀ := 2*remainingGoodConstant 136 16 0
  let g₁ := remainingGoodConstant 136 16 (1/2)
  let b₀ := 2*remainingMagneticConstant 136 16 0
  let b₁ := remainingMagneticConstant 136 16 (1/2)
  let H := 2*Real.sqrt 16384
  let D := dyadicBalanceConstant (1/2) (1/2)
  let aa := g*g₀*Real.sqrt Eg*Real.sqrt 2
  let bb := b'*b₀*Real.sqrt Eb*Real.sqrt N
  let cc := H*(g*g₁*Real.sqrt Eg+b'*b₁*Real.sqrt Eb)*Real.sqrt N
  have hE : 0≤E := hd.datumEnergyNumber_nonneg
  have hEg : 0≤Eg := by dsimp [Eg]; positivity
  have hEb : 0≤Eb := by dsimp [Eb]; positivity
  have hN : 0≤N := by dsimp [N,pairCountConstant]; positivity
  have hg : 0≤g := relativeCauchyConstant_nonneg hCg
  have hb' : 0≤b' := relativeCauchyConstant_nonneg hCb
  have hg₀ : 0≤g₀ := mul_nonneg (by norm_num) (remainingGoodConstant_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have hg₁ : 0≤g₁ := remainingGoodConstant_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb₀ : 0≤b₀ := mul_nonneg (by norm_num) (remainingMagneticConstant_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have hb₁ : 0≤b₁ := remainingMagneticConstant_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hH : 0≤H := by dsimp [H]; positivity
  have hD : 0≤D := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have haa : 0≤aa := by dsimp [aa]; positivity
  have hbb : 0≤bb := by dsimp [bb]; positivity
  have hcc : 0≤cc := by dsimp [cc]; positivity
  refine ⟨D*(128*(2*aa+2*bb+4*cc)),by positivity,?_⟩
  intro s T F hs hT zX S a b I w M A P hS hS0 ha hb hab hI hI1 hJI hM hA hP hL hw hwP HX HZ
    Sp Sφ Sθ Sσ hp hφ hθ hσ
  dsimp only
  let G := directReceiverGoodBudget s F zX a b I
  let B := directReceiverMagneticBudget s F zX a b I
  let U := Real.sqrt M+Real.sqrt (Real.sqrt (A*Real.log (2+P)))
  let f (np nf : ℕ) := (I : ℝ)^(3/4:ℝ)*sourceRepresentative np*
    (g*Real.sqrt (G nf)*(g₀*Real.sqrt (cappedRepresentative nf)+
      H*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min (sourceRepresentative np) w)*U*g₁)+
     b'*Real.sqrt (B nf)*(b₀+
      H*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min (sourceRepresentative np) w)*U*b₁))
  have hG (nf : ℕ) : 0≤G nf := ENNReal.toReal_nonneg
  have hB (nf : ℕ) : 0≤B nf := by dsimp [B,directReceiverMagneticBudget]; positivity
  have hf (np nf : ℕ) : 0≤f np nf := by dsimp [f,U,sourceRepresentative]; positivity
  obtain ⟨hGs,hGt⟩ := hs.directReceiverGoodBudget_sum hd F zX ha hb hI hJI
  obtain ⟨hBs,hBt⟩ := hs.directReceiverMagneticBudget_sum hd F zX hI hJI
  have hGb : ∑nf∈Sφ,G nf≤Eg := (hGs.sum_le_tsum Sφ (fun n _=>hG n)).trans hGt
  have hBb : ∑nf∈Sφ,B nf≤Eb := (hBs.sum_le_tsum Sφ (fun n _=>hB n)).trans hBt
  have hi (np : ℕ) (hnp : np∈Sp) (nf : ℕ) (hnf : nf∈Sφ) :=
    hbin s T F hs.energyPrefix hT hs.initial_f zX S np nf a b I w M A P
      hS hS0 ha hb hab hI hJI (zero_lt_one.trans_le hM) (zero_le_one.trans hA)
      (zero_lt_one.trans_le hP) hw HX HZ (Sθ np nf) (Sσ np nf) (hθ np hnp nf hnf) (hσ np hnp nf hnf)
  have he (np nf : ℕ) :
      D*(I : ℝ)^(3/4:ℝ)*sourceRepresentative np*
        (relativeCauchyConstant Cg (∫x : Vec,totalEnergy s (0,x)) (G nf)*
          (2*remainingGoodConstant 136 16 0*Real.sqrt (cappedRepresentative nf)+
            H*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min (sourceRepresentative np) w)*U*remainingGoodConstant 136 16 (1/2))+
         relativeCauchyConstant Cb (∫x : Vec,totalEnergy s (0,x)) (B nf)*
          (2*remainingMagneticConstant 136 16 0+
            H*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min (sourceRepresentative np) w)*U*remainingMagneticConstant 136 16 (1/2)))=
      D*f np nf := by
    rw [hs.initial_energy_eq,relativeCauchyConstant_factor Cg,relativeCauchyConstant_factor Cb]
    dsimp [f,g,b',E,g₀,g₁,b₀,b₁]
    ring
  calc
    _≤∑np∈Sp,∑nf∈Sφ,ENNReal.ofReal (D*f np nf) := by
      apply Finset.sum_le_sum
      intro np hnp
      apply Finset.sum_le_sum
      intro nf hnf
      have hh := hi np hnp nf hnf
      dsimp only at hh
      change _≤ENNReal.ofReal _ at hh
      rw [←he np nf]
      exact hh
    _=ENNReal.ofReal (D*(∑np∈Sp,∑nf∈Sφ,f np nf)) := by
      simp_rw [←ENNReal.ofReal_sum_of_nonneg (fun n _=>mul_nonneg hD (hf _ n)),
        ←ENNReal.ofReal_sum_of_nonneg (fun n _=>Finset.sum_nonneg (fun i _=>mul_nonneg hD (hf n i))),
        ←Finset.mul_sum]
    _≤_ := by
      apply ENNReal.ofReal_le_ofReal
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hD
      exact remaining_source_budget_total Sp Sφ G B hI hI1 (zero_lt_one.trans_le hP) hw hwP hM hA hL
        (fun n _=>hG n) (fun n _=>hB n) hEg hEb hN hg hb' hg₀ hg₁ hb₀ hb₁ hH hGb hBb
        (receiver_scale_card_enlarged hP hw hwP hL Sφ hφ) hp

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.direct_remaining_source_short_uniform_expanded {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T →
    ∀ (zX : Phase) (S : Set Phase) (a b I w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I →
      1≤M → 1≤A → 1≤P → 1≤Real.log (2+P) → 0<w → w≤P →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ (Sp Sφ : Finset ℕ) (Sθ : ℕ→ℕ→Finset ℕ) (Sσ : ℕ→ℕ→ℕ→Finset ℕ),
      (∀np∈Sp,sourceRepresentative np≤128*P) →
      (∀nf∈Sφ,1/(32*w)≤cappedRepresentative nf) →
      (∀np∈Sp,∀nf∈Sφ,∀nt∈Sθ np nf,cappedRepresentative nf≤16384*cappedRepresentative nt) →
      (∀np∈Sp,∀nf∈Sφ,∀nt∈Sθ np nf,∀j∈Sσ np nf nt,
        cappedRepresentative j≤131080*cappedRepresentative nt ∧
        512≤cappedRepresentative j*sourceRepresentative np ∧ 32≤cappedRepresentative j*w) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun np nt nf j nr=>relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j
      (∑np∈Sp,∑nf∈Sφ,∑nt∈Sθ np nf,∑j∈Sσ np nf nt,∑'nr : ℕ,
        if max 1 T*cappedRepresentative nr≤I then
          ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B np nt nf j nr) z
            ∂physicalBinMeasure V (B np nt nf j nr) (Icc a b) else 0)≤
      ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cg,Cb,hCg,hCb,hbin⟩ := hd.direct_source_shared_short_angles_expanded
  let E := datumEnergyNumber d
  let Eg := 20*E
  let Eb := 120*E
  let N := (1+Real.log 32)*pairCountConstant
  let g := relativeCauchyConstant Cg E 1
  let b' := relativeCauchyConstant Cb E 1
  let g₀ := 2*remainingGoodConstant 131080 16384 0
  let g₁ := remainingGoodConstant 131080 16384 (1/2)
  let b₀ := 2*remainingMagneticConstant 131080 16384 0
  let b₁ := remainingMagneticConstant 131080 16384 (1/2)
  let H := 2*Real.sqrt 16384
  let D := dyadicBalanceConstant (1/2) (1/2)
  let aa := g*g₀*Real.sqrt Eg*Real.sqrt 2
  let bb := b'*b₀*Real.sqrt Eb*Real.sqrt N
  let cc := H*(g*g₁*Real.sqrt Eg+b'*b₁*Real.sqrt Eb)*Real.sqrt N
  have hE : 0≤E := hd.datumEnergyNumber_nonneg
  have hEg : 0≤Eg := by dsimp [Eg]; positivity
  have hEb : 0≤Eb := by dsimp [Eb]; positivity
  have hN : 0≤N := by dsimp [N,pairCountConstant]; positivity
  have hg : 0≤g := relativeCauchyConstant_nonneg hCg
  have hb' : 0≤b' := relativeCauchyConstant_nonneg hCb
  have hg₀ : 0≤g₀ := mul_nonneg (by norm_num) (remainingGoodConstant_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have hg₁ : 0≤g₁ := remainingGoodConstant_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb₀ : 0≤b₀ := mul_nonneg (by norm_num) (remainingMagneticConstant_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have hb₁ : 0≤b₁ := remainingMagneticConstant_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hH : 0≤H := by dsimp [H]; positivity
  have hD : 0≤D := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have haa : 0≤aa := by dsimp [aa]; positivity
  have hbb : 0≤bb := by dsimp [bb]; positivity
  have hcc : 0≤cc := by dsimp [cc]; positivity
  refine ⟨D*(128*(2*aa+2*bb+4*cc)),by positivity,?_⟩
  intro s T F hs hT zX S a b I w M A P hS hS0 ha hb hab hI hI1 hJI hM hA hP hL hw hwP HX HZ
    Sp Sφ Sθ Sσ hp hφ hθ hσ
  dsimp only
  let G := directReceiverGoodBudget s F zX a b I
  let B := directReceiverMagneticBudget s F zX a b I
  let U := Real.sqrt M+Real.sqrt (Real.sqrt (A*Real.log (2+P)))
  let f (np nf : ℕ) := (I : ℝ)^(3/4:ℝ)*sourceRepresentative np*
    (g*Real.sqrt (G nf)*(g₀*Real.sqrt (cappedRepresentative nf)+
      H*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min (sourceRepresentative np) w)*U*g₁)+
     b'*Real.sqrt (B nf)*(b₀+
      H*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min (sourceRepresentative np) w)*U*b₁))
  have hG (nf : ℕ) : 0≤G nf := ENNReal.toReal_nonneg
  have hB (nf : ℕ) : 0≤B nf := by dsimp [B,directReceiverMagneticBudget]; positivity
  have hf (np nf : ℕ) : 0≤f np nf := by dsimp [f,U,sourceRepresentative]; positivity
  obtain ⟨hGs,hGt⟩ := hs.directReceiverGoodBudget_sum hd F zX ha hb hI hJI
  obtain ⟨hBs,hBt⟩ := hs.directReceiverMagneticBudget_sum hd F zX hI hJI
  have hGb : ∑nf∈Sφ,G nf≤Eg := (hGs.sum_le_tsum Sφ (fun n _=>hG n)).trans hGt
  have hBb : ∑nf∈Sφ,B nf≤Eb := (hBs.sum_le_tsum Sφ (fun n _=>hB n)).trans hBt
  have hi (np : ℕ) (hnp : np∈Sp) (nf : ℕ) (hnf : nf∈Sφ) :=
    hbin s T F hs.energyPrefix hT hs.initial_f zX S np nf a b I w M A P
      hS hS0 ha hb hab hI hJI (zero_lt_one.trans_le hM) (zero_le_one.trans hA)
      (zero_lt_one.trans_le hP) hw HX HZ (Sθ np nf) (Sσ np nf) (hθ np hnp nf hnf) (hσ np hnp nf hnf)
  have he (np nf : ℕ) :
      D*(I : ℝ)^(3/4:ℝ)*sourceRepresentative np*
        (relativeCauchyConstant Cg (∫x : Vec,totalEnergy s (0,x)) (G nf)*
          (2*remainingGoodConstant 131080 16384 0*Real.sqrt (cappedRepresentative nf)+
            H*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min (sourceRepresentative np) w)*U*remainingGoodConstant 131080 16384 (1/2))+
         relativeCauchyConstant Cb (∫x : Vec,totalEnergy s (0,x)) (B nf)*
          (2*remainingMagneticConstant 131080 16384 0+
            H*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min (sourceRepresentative np) w)*U*remainingMagneticConstant 131080 16384 (1/2)))=
      D*f np nf := by
    rw [hs.initial_energy_eq,relativeCauchyConstant_factor Cg,relativeCauchyConstant_factor Cb]
    dsimp [f,g,b',E,g₀,g₁,b₀,b₁]
    ring
  calc
    _≤∑np∈Sp,∑nf∈Sφ,ENNReal.ofReal (D*f np nf) := by
      apply Finset.sum_le_sum
      intro np hnp
      apply Finset.sum_le_sum
      intro nf hnf
      have hh := hi np hnp nf hnf
      dsimp only at hh
      change _≤ENNReal.ofReal _ at hh
      rw [←he np nf]
      exact hh
    _=ENNReal.ofReal (D*(∑np∈Sp,∑nf∈Sφ,f np nf)) := by
      simp_rw [←ENNReal.ofReal_sum_of_nonneg (fun n _=>mul_nonneg hD (hf _ n)),
        ←ENNReal.ofReal_sum_of_nonneg (fun n _=>Finset.sum_nonneg (fun i _=>mul_nonneg hD (hf n i))),
        ←Finset.mul_sum]
    _≤_ := by
      apply ENNReal.ofReal_le_ofReal
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hD
      exact remaining_source_budget_total Sp Sφ G B hI hI1 (zero_lt_one.trans_le hP) hw hwP hM hA hL
        (fun n _=>hG n) (fun n _=>hB n) hEg hEb hN hg hb' hg₀ hg₁ hb₀ hb₁ hH hGb hBb
        (receiver_scale_card_enlarged hP hw hwP hL Sφ hφ) hp

end RVM

end

end OAI
