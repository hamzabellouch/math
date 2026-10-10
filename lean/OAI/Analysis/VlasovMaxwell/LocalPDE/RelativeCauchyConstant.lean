import Mathlib
import OAI.Analysis.VlasovMaxwell.Flow.ClosedEulerianTimeBudget

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.direct_source_relative_radius_budget {d : Datum} (hd₀ : Admissible d) :
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
      let O := ENNReal.ofReal (491520*E*(1+φ/σ)*(1+I/len)/(p*r*φ^2))
      let H := ENNReal.ofReal (576*I*r*φ^2)
      let Dg := ENNReal.ofReal (128*Cg*p^3*(min θ σ)^2)
      let Db := ENNReal.ofReal (128*Cb*p^3*(min θ σ)^2)
      (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z
        ∂physicalBinMeasure V B (Icc a b)) ≤
      ENNReal.ofReal (10240*φ/(p*θ^2))*
        ((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*(min (Dg^2*H) (Dg*O))^(1/2:ℝ))+
      ENNReal.ofReal (10240/p)*
        ((ENNReal.ofReal (40*(I+2*r)*E))^(1/2:ℝ)*(min (Db^2*H) (Db*O))^(1/2:ℝ)) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_relative_budget
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S k j a b I len w M A P L massScale Cs hS hS0
    ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable HX HZ
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let σ := cappedRepresentative j
  let r := max 1 T*cappedRepresentative (k 3)
  let B := relativeRepresentativeClosedBin T w k j
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let E := ∫x : Vec,totalEnergy s (0,x)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hσ : 0<σ := cappedRepresentative_pos _
  have hr : 0<r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hBmax : B.rmax=2*r := by dsimp [B,relativeRepresentativeClosedBin,representativeClosedBin,r]; ring
  have hBmin : B.rmin=r/2 := rfl
  have hBDmin : B.Dmin=φ^2/2 := rfl
  have hI : 0<I := hlen.trans_le hlenI
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hangle (D : ℝ) (hD : D∈Icc B.Dmin B.Dmax) : DyadicWindow 1 (k 2) (Real.sqrt (D/2)) :=
    dyadicWindow_one_sqrt (k 2)
      (by simpa only [B,relativeRepresentativeClosedBin,representativeClosedBin,cappedRepresentative,inv_pow] using hD.1)
      (by simpa only [B,relativeRepresentativeClosedBin,representativeClosedBin,cappedRepresentative,inv_pow] using hD.2)
  have hn := hsource s T F hs hT h0 zX B S M A P L a b massScale φ θ σ Cs p len I 1 (k 2)
    hS hS0 ha hb hab hp hlen hlenI hJI hM hA hP hL hm hφ hθ hσ
    (cappedRepresentative_le_one _) hCs hstable le_rfl le_rfl hmq hmw
    (by rw [hBmin]; positivity) (by rw [hBmax]; positivity) (by rw [hBDmin]; positivity)
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
    (by change 4≤σ*(p/128); dsimp [σ,p] at *; nlinarith only [hqσ])
    (by change 4≤σ*(w/8); dsimp [σ] at *; nlinarith only [hwσ]) hangle HX HZ
  dsimp only at hn
  have hmass : (ENNReal.ofReal (30720*B.rmax/p*(1+φ/σ)*(1+I/len))*ENNReal.ofReal E)/
      ENNReal.ofReal (B.rmin^2*B.Dmin) =
      ENNReal.ofReal (491520*E*(1+φ/σ)*(1+I/len)/(p*r*φ^2)) := by
    rw [hBmax,hBmin,hBDmin,←ENNReal.ofReal_mul (by positivity : 0≤30720*(2*r)/p*(1+φ/σ)*(1+I/len)),
      ←ENNReal.ofReal_div_of_pos (by positivity : 0<(r/2)^2*(φ^2/2))]
    congr 1
    field_simp [hp.ne',hr.ne',hφ.ne',hσ.ne',hlen.ne']
    ring
  have hvolume : volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2) ≤
      ENNReal.ofReal (576*I*r*φ^2) := by
    rw [Real.volume_Icc,hBmax,hBmin]
    calc
      _ ≤ ENNReal.ofReal I*ENNReal.ofReal (2*r-r/2)*ENNReal.ofReal (384*φ^2) := by gcongr
      _ = _ := by
        rw [←ENNReal.ofReal_mul hI.le,←ENNReal.ofReal_mul (mul_nonneg hI.le (by linarith : 0≤2*r-r/2))]
        congr 1
        ring
  have hgood : ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I (k 2) ≤
      ENNReal.ofReal (20*I*E) := by
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.goodFieldBudget_uniform X (fun t=>velocity (V t)) 1 hJ hI hJI)
    calc
      _ ≤ ENNReal.ofReal I*((4*1+1:ℕ)*ENNReal.ofReal (4*E)) := mul_le_mul' le_rfl hh
      _ = _ := by
        change ENNReal.ofReal I*(5*ENNReal.ofReal (4*E))=_
        rw [←ENNReal.ofReal_ofNat (n:=5),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤5),
          ←ENNReal.ofReal_mul hI.le]
        congr 1
        ring
  have hmag : ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T 1
      (max 0 (a-B.rmax)) (min T (b-B.rmin)) I (k 2) ≤ ENNReal.ofReal (40*(I+2*r)*E) := by
    have hsub : Icc (max 0 (a-B.rmax)) (min T (b-B.rmin))⊆Icc 0 T :=
      Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
    have hh : min T (b-B.rmin)-max 0 (a-B.rmax) ≤ (1+2*r/I)*I := by
      have hb' := min_le_right T (b-B.rmin)
      have ha' := le_max_right 0 (a-B.rmax)
      rw [hBmax] at ha'
      rw [hBmin] at hb'
      have he : (1+2*r/I)*I=I+2*r := by field_simp
      rw [hBmin,hBmax,he]
      linarith only [hJI,hb',ha',hr]
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.magneticFieldBudget_uniform F.flow zX 1 hsub hI (by positivity : 0≤1+2*r/I) hh)
    calc
      _ ≤ ENNReal.ofReal (2*I)*((2*(4*1+1):ℕ)*ENNReal.ofReal (1+2*r/I)*ENNReal.ofReal (2*E)) :=
        mul_le_mul' le_rfl hh
      _ = _ := by
        change ENNReal.ofReal (2*I)*(10*ENNReal.ofReal (1+2*r/I)*ENNReal.ofReal (2*E))=_
        rw [←ENNReal.ofReal_ofNat (n:=10),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10),
          ←ENNReal.ofReal_mul (by positivity : 0≤10*(1+2*r/I)),
          ←ENNReal.ofReal_mul (by positivity : 0≤2*I)]
        congr 1
        field_simp [hI.ne']
        ring
  have heG : 80*φ/(p/128*θ^2)=10240*φ/(p*θ^2) := by ring
  have heB : 80/(p/128)=10240/p := by ring
  rw [heG,heB,hmass] at hn
  apply hn.trans
  apply add_le_add
  · apply mul_le_mul' le_rfl
    apply mul_le_mul' (ENNReal.rpow_le_rpow hgood (by norm_num))
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    exact min_le_min (mul_le_mul' le_rfl hvolume) le_rfl
  · apply mul_le_mul' le_rfl
    apply mul_le_mul' (ENNReal.rpow_le_rpow hmag (by norm_num))
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    exact min_le_min (mul_le_mul' le_rfl hvolume) le_rfl

def relativeCauchyConstant (C E Z : ℝ) : ℝ :=
  31457280*C*Real.sqrt Z+10240*Real.sqrt Z*Real.sqrt (62914560*C*E)

lemma relativeCauchyConstant_nonneg {C E Z : ℝ} (hC : 0≤C) :
    0≤relativeCauchyConstant C E Z := by unfold relativeCauchyConstant; positivity

lemma relative_density_near_sqrt {C I p ν r φ : ℝ}
    (hC : 0≤C) (hI : 0≤I) (hp : 0≤p) (_hν : 0≤ν) (hr : 0≤r) (hφ : 0≤φ) :
    Real.sqrt ((128*C*p^3*ν^2)^2*(576*I*r*φ^2)) =
      3072*C*p^3*ν^2*Real.sqrt I*Real.sqrt r*φ := by
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity),
    show 576*I*r*φ^2=576*((I*r)*φ^2) by ring,
    Real.sqrt_mul (by norm_num : (0:ℝ)≤576),Real.sqrt_mul (mul_nonneg hI hr),
    Real.sqrt_mul hI,Real.sqrt_sq hφ]
  norm_num
  ring

lemma relative_density_far_sqrt {C E p ν R r φ κ : ℝ}
    (hC : 0≤C) (hE : 0≤E) (hp : 0<p) (hν : 0<ν) (hR : 0≤R)
    (hr : 0<r) (hφ : 0<φ) (hκ : 0≤κ) :
    Real.sqrt ((128*C*p^3*ν^2)*(491520*E*κ*R^2/(p*r*φ^2))) =
      Real.sqrt (62914560*C*E)*Real.sqrt κ*p*ν*R/(Real.sqrt r*φ) := by
  have he : (128*C*p^3*ν^2)*(491520*E*κ*R^2/(p*r*φ^2))=
      (62914560*C*E*κ)*p^2*ν^2*R^2/(r*φ^2) := by
    field_simp [hp.ne',hr.ne',hφ.ne']
    ring
  rw [he,source_far_sqrt_mass (by positivity) hp hν hR hr hφ,
    Real.sqrt_mul (by positivity : 0≤62914560*C*E)]

lemma relative_radius_cauchy_scalar {C E Z I p ν R r φ κ γ : ℝ}
    (hC : 0≤C) (hE : 0≤E) (hZ : 0≤Z) (hI : 0<I) (hp : 0<p)
    (hν : 0<ν) (hR : 0≤R) (hr : 0<r) (hφ : 0<φ) (hκ : 0≤κ) (hγ : 0≤γ) :
    let D := ENNReal.ofReal (128*C*p^3*ν^2)
    let H := ENNReal.ofReal (576*I*r*φ^2)
    let O := ENNReal.ofReal (491520*E*κ*R^2/(p*r*φ^2))
    ENNReal.ofReal (10240*γ/p)*
      ((ENNReal.ofReal (Z*I))^(1/2:ℝ)*(min (D^2*H) (D*O))^(1/2:ℝ)) ≤
    ENNReal.ofReal (relativeCauchyConstant C E Z*
      min ((I*p^2*ν^2*φ*γ)*Real.sqrt r)
        ((Real.sqrt I*R*ν*Real.sqrt κ*γ/φ)/Real.sqrt r)) := by
  dsimp only
  let K := relativeCauchyConstant C E Z
  have hK : 0≤K := relativeCauchyConstant_nonneg hC
  rw [mul_min_of_nonneg _ _ hK,ENNReal.ofReal_min]
  apply le_min
  · calc
      _ ≤ ENNReal.ofReal (10240*γ/p)*
          ((ENNReal.ofReal (Z*I))^(1/2:ℝ)*
            ((ENNReal.ofReal (128*C*p^3*ν^2))^2*ENNReal.ofReal (576*I*r*φ^2))^(1/2:ℝ)) := by
        gcongr
        exact min_le_left _ _
      _ = ENNReal.ofReal ((31457280*C*Real.sqrt Z)*
          ((I*p^2*ν^2*φ*γ)*Real.sqrt r)) := by
        rw [←ENNReal.ofReal_pow (by positivity : 0≤128*C*p^3*ν^2),
          ←ENNReal.ofReal_mul (sq_nonneg _),
          ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
          relative_density_near_sqrt hC hI.le hp.le hν.le hr.le hφ.le,
          Real.sqrt_mul hZ,
          ←ENNReal.ofReal_mul (by positivity : 0≤Real.sqrt Z*Real.sqrt I),
          ←ENNReal.ofReal_mul (by positivity : 0≤10240*γ/p)]
        congr 1
        have hIsq : Real.sqrt I*Real.sqrt I=I := Real.mul_self_sqrt hI.le
        calc
          _ = 31457280*C*Real.sqrt Z*(Real.sqrt I*Real.sqrt I)*p^2*ν^2*φ*γ*Real.sqrt r := by
            field_simp [hp.ne']
            ring
          _ = _ := by rw [hIsq]; ring
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact le_add_of_nonneg_right (by positivity)
  · calc
      _ ≤ ENNReal.ofReal (10240*γ/p)*
          ((ENNReal.ofReal (Z*I))^(1/2:ℝ)*
            ((ENNReal.ofReal (128*C*p^3*ν^2))*
              ENNReal.ofReal (491520*E*κ*R^2/(p*r*φ^2)))^(1/2:ℝ)) := by
        gcongr
        exact min_le_right _ _
      _ = ENNReal.ofReal ((10240*Real.sqrt Z*Real.sqrt (62914560*C*E))*
          ((Real.sqrt I*R*ν*Real.sqrt κ*γ/φ)/Real.sqrt r)) := by
        rw [←ENNReal.ofReal_mul (by positivity : 0≤128*C*p^3*ν^2),
          ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
          relative_density_far_sqrt hC hE hp hν hR hr hφ hκ,Real.sqrt_mul hZ,
          ←ENNReal.ofReal_mul (by positivity : 0≤Real.sqrt Z*Real.sqrt I),
          ←ENNReal.ofReal_mul (by positivity : 0≤10240*γ/p)]
        congr 1
        field_simp [hp.ne',hφ.ne',(Real.sqrt_pos.mpr hr).ne']
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact le_add_of_nonneg_left (by positivity)

lemma Admissible.direct_source_relative_short_radius {d : Datum} (hd₀ : Admissible d) :
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
      let Kg := relativeCauchyConstant Cg E (20*E)
      let Kb := relativeCauchyConstant Cb E (120*E)
      (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z
        ∂physicalBinMeasure V B (Icc a b)) ≤
      ENNReal.ofReal (Kg*min ((I*p^2*ν^2*φ^2/θ^2)*Real.sqrt r)
        ((Real.sqrt I*R*ν*Real.sqrt κ/θ^2)/Real.sqrt r)+
      Kb*min ((I*p^2*ν^2*φ)*Real.sqrt r)
        ((Real.sqrt I*R*ν*Real.sqrt κ/φ)/Real.sqrt r)) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_relative_radius_budget
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S k j a b I len w M A P L massScale Cs hS hS0
    ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable hrI HX HZ
  have hn := hsource s T F hs hT h0 zX S k j a b I len w M A P L massScale Cs
    hS hS0 ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable HX HZ
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
  have hg := relative_radius_cauchy_scalar hCg hE (show 0≤20*E by positivity) hI hp hν hR hr hφ hκ
    (show 0≤φ/θ^2 by positivity)
  dsimp only at hg
  have heγ : 10240*(φ/θ^2)/p=10240*φ/(p*θ^2) := by ring
  have hea : I*p^2*ν^2*φ*(φ/θ^2)=I*p^2*ν^2*φ^2/θ^2 := by ring
  have heb : Real.sqrt I*R*ν*Real.sqrt κ*(φ/θ^2)/φ=Real.sqrt I*R*ν*Real.sqrt κ/θ^2 := by
    field_simp [hφ.ne']
  rw [heγ,hea,heb,show (20*E)*I=20*I*E by ring,hRsq] at hg
  have hbnd := relative_radius_cauchy_scalar hCb hE (show 0≤120*E by positivity) hI hp hν hR hr hφ hκ
    (show 0≤(1:ℝ) by norm_num)
  dsimp only at hbnd
  simp only [mul_one] at hbnd
  rw [show (120*E)*I=120*I*E by ring,hRsq] at hbnd
  have hmag : ENNReal.ofReal (40*(I+2*r)*E) ≤ ENNReal.ofReal (120*I*E) := by
    apply ENNReal.ofReal_le_ofReal
    have hrI' : r≤I := hrI
    nlinarith only [mul_nonneg (sub_nonneg.mpr hrI') hE]
  apply hn.trans
  calc
    _ ≤ ENNReal.ofReal (relativeCauchyConstant Cg E (20*E)*
          min ((I*p^2*ν^2*φ^2/θ^2)*Real.sqrt r)
            ((Real.sqrt I*R*ν*Real.sqrt κ/θ^2)/Real.sqrt r))+
        ENNReal.ofReal (relativeCauchyConstant Cb E (120*E)*
          min ((I*p^2*ν^2*φ)*Real.sqrt r)
            ((Real.sqrt I*R*ν*Real.sqrt κ/φ)/Real.sqrt r)) := by
      apply add_le_add hg
      refine le_trans ?_ hbnd
      apply mul_le_mul' le_rfl
      apply mul_le_mul' (ENNReal.rpow_le_rpow hmag (by norm_num)) le_rfl
    _ = _ := by
      rw [←ENNReal.ofReal_add
        (mul_nonneg (relativeCauchyConstant_nonneg hCg) (by positivity))
        (mul_nonneg (relativeCauchyConstant_nonneg hCb) (by positivity))]

lemma capped_sqrt_radius_ennreal_sum {a b H K : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hH : 0<H) (hK : 0≤K) :
    (∑'n : ℕ, ENNReal.ofReal (K*min (a*Real.sqrt (H*cappedRepresentative n))
      (b/Real.sqrt (H*cappedRepresentative n)))) ≤
      ENNReal.ofReal (K*dyadicBalanceConstant (1/2) (1/2)*Real.sqrt (a*b)) := by
  let g : ℤ→ℝ := fun k=>min (a*Real.sqrt (H*(2:ℝ)^k)) (b/Real.sqrt (H*(2:ℝ)^k))
  have hg0 (k : ℤ) : 0≤g k := by dsimp [g]; positivity
  have hg := dyadic_sqrt_radius_balance ha hb hH
  have he (n : ℕ) : cappedRepresentative n=(2:ℝ)^(-(n:ℤ)) := by
    simp only [cappedRepresentative,zpow_neg,zpow_natCast,inv_pow]
  have hinj : Function.Injective (fun n : ℕ=>-(n:ℤ)) := by
    intro a b hab
    exact_mod_cast neg_injective hab
  calc
    _ = ∑'n : ℕ,ENNReal.ofReal (K*g (-(n:ℤ))) := by
      apply tsum_congr
      intro n
      rw [he]
    _ ≤ ∑'k : ℤ,ENNReal.ofReal (K*g k) :=
      ENNReal.tsum_comp_le_tsum_of_injective hinj (fun k=>ENNReal.ofReal (K*g k))
    _ = ENNReal.ofReal (K*∑'k : ℤ,g k) := by
      rw [←ENNReal.ofReal_tsum_of_nonneg (fun k=>mul_nonneg hK (hg0 k)) (hg.1.mul_left K),tsum_mul_left]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [g,mul_assoc] using mul_le_mul_of_nonneg_left hg.2 hK

lemma Admissible.direct_source_relative_short_radial_sum {d : Datum} (hd₀ : Admissible d) :
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
      let Kg := relativeCauchyConstant Cg E (20*E)
      let Kb := relativeCauchyConstant Cb E (120*E)
      let D := dyadicBalanceConstant (1/2) (1/2)
      (∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤I then
        ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
          ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
      ENNReal.ofReal (Kg*D*Real.sqrt
        ((I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*R*ν*Real.sqrt κ/θ^2))+
        Kb*D*Real.sqrt ((I*p^2*ν^2*φ)*(Real.sqrt I*R*ν*Real.sqrt κ/φ))) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_relative_short_radius
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
  let Kg := relativeCauchyConstant Cg E (20*E)
  let Kb := relativeCauchyConstant Cb E (120*E)
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

lemma Admissible.direct_source_remaining_short_sum {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → b-a ≤ (w/P)^2 →
      0 < M → 0 ≤ A → 0 < P → 1 ≤ Real.log (2+P) → 0 < w → w≤P →
      sourceRepresentative np≤128*P →
      cappedRepresentative nφ≤16*cappedRepresentative nθ →
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
      ENNReal.ofReal ((16*Kg+Kb)*dyadicBalanceConstant (1/2) (1/2)*
        Real.sqrt (32768*17*(1+16384*(M+Real.sqrt A))*w^2*Real.sqrt (Real.log (2+P)))) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_relative_short_radial_sum
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b w M A P hS hS0 ha hb hab hJI
    hM hA hP hL hw hwP hpP hφθ hpσ hwσ HX HZ
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
  let U := 32768*17*(1+16384*(M+Real.sqrt A))*w^2*Real.sqrt L
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
    convert hlenlam using 1; norm_num [lam]
  have hn := hsource s T F hs hT h0 zX S np nθ nφ j a b I len w M A P L m 128
    hS hS0 ha hb hab hlen hlenI hJI hM hA hP (by dsimp [L]; linarith only [hL]) hm hw
    (by norm_num) hmq hmw hpσ hwσ hstable HX HZ
  have hg := remaining_good_balance_coefficient hP hL (show (0:ℝ)<16384 by norm_num)
    hM hA hp hw hθ hφ.le hσ (cappedRepresentative_le_one _) (by norm_num : (0:ℝ)≤16) hφθ hpP hwP
  have hb' := remaining_magnetic_balance_coefficient hP hL (show (0:ℝ)<16384 by norm_num)
    hM hA hp hw hθ.le (cappedRepresentative_le_one _) hφ.le hσ
    (cappedRepresentative_le_one _) (by norm_num : (0:ℝ)≤16) hφθ hpP hwP
  have hg' : (I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*R*ν*Real.sqrt (1+φ/σ)/θ^2)≤256*U := by
    convert hg using 1 <;> dsimp [I,R,ν,len,lam,U,L] <;> ring
  have hb'' : (I*p^2*ν^2*φ)*(Real.sqrt I*R*ν*Real.sqrt (1+φ/σ)/φ)≤U := by
    convert hb' using 1
    · dsimp [I,R,ν,len,lam]
      field_simp [hφ.ne']
    · dsimp [U,L]
      ring
  have hKg : 0≤Kg := relativeCauchyConstant_nonneg hCg
  have hKb : 0≤Kb := relativeCauchyConstant_nonneg hCb
  have hD : 0≤D := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hr : Real.sqrt (256*U)=16*Real.sqrt U := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤256)]; norm_num
  apply hn.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Kg*D*Real.sqrt (256*U)+Kb*D*Real.sqrt U :=
      add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hg') (mul_nonneg hKg hD))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb'') (mul_nonneg hKb hD))
    _ = _ := by rw [hr]; dsimp [Kg,Kb,D,U,E,L]; ring

lemma Admissible.direct_source_large_radius_budget {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (k : Fin 4→ℕ) (j : ℕ) (a b I w : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ I → 0 < I →
      I ≤ max 1 T*cappedRepresentative (k 3) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let σ := cappedRepresentative j
      let r := max 1 T*cappedRepresentative (k 3)
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := relativeRepresentativeClosedBin T w k j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Og := ENNReal.ofReal (491520*E/(p*r*φ^2))
      let Ob := ENNReal.ofReal (491520*I*E/(r^2*θ^2))
      let H := ENNReal.ofReal (576*I*r*φ^2)
      let Dg := ENNReal.ofReal (128*Cg*p^3*(min θ σ)^2)
      let Db := ENNReal.ofReal (128*Cb*p^3*(min θ σ)^2)
      (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z
        ∂physicalBinMeasure V B (Icc a b)) ≤
      ENNReal.ofReal (10240*φ/(p*θ^2))*
        ((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*(min (Dg^2*H) (Dg*Og))^(1/2:ℝ))+
      ENNReal.ofReal (10240/p)*
        ((ENNReal.ofReal (120*r*E))^(1/2:ℝ)*(min (Db^2*H) (Db*Ob))^(1/2:ℝ)) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_two_budget_bound
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S k j a b I w hS hS0 ha hb hJI hI hIr
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let σ := cappedRepresentative j
  let r := max 1 T*cappedRepresentative (k 3)
  let B := relativeRepresentativeClosedBin T w k j
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let E := ∫x : Vec,totalEnergy s (0,x)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hσ : 0<σ := cappedRepresentative_pos _
  have hr : 0<r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hBmax : B.rmax=2*r := by dsimp [B,relativeRepresentativeClosedBin,representativeClosedBin,r]; ring
  have hBmin : B.rmin=r/2 := rfl
  have hBDmin : B.Dmin=φ^2/2 := rfl
  have hqlo : B.qmin=p/128 := rfl
  have hqhi : B.qmax≤p := by change p/32≤p; linarith only [hp]
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hC : Icc (max 0 (a-B.rmax)) (min T (b-B.rmin))⊆Icc 0 T :=
    Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have hR : 0<B.rmin := by rw [hBmin]; positivity
  have hD : 0<B.Dmin := by rw [hBDmin]; positivity
  have hangle (D : ℝ) (hD : D∈Icc B.Dmin B.Dmax) : DyadicWindow 1 (k 2) (Real.sqrt (D/2)) :=
    dyadicWindow_one_sqrt (k 2)
      (by simpa only [B,relativeRepresentativeClosedBin,representativeClosedBin,cappedRepresentative,inv_pow] using hD.1)
      (by simpa only [B,relativeRepresentativeClosedBin,representativeClosedBin,cappedRepresentative,inv_pow] using hD.2)
  have hn := hsource s T F hs hT h0 zX B S a b I (p/128) p θ φ σ 1 (k 2)
    hS hS0 hJ hI (by positivity) hp hθ hφ hσ.le hR hD le_rfl hqhi
    le_rfl le_rfl le_rfl le_rfl le_rfl hangle
  let O := coneOccupation F.flow zX T s.f
    (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))/
      ENNReal.ofReal (B.rmin^2*B.Dmin)
  have hgO : O≤ENNReal.ofReal (491520*E/(p*r*φ^2)) := by
    have ho := F.closedEulerian_crude_budget hs hT zX B hS hJ hJI hR.le (by rw [hqlo]; positivity)
    have hc : ENNReal.ofReal (I+B.rmax)/ENNReal.ofReal B.qmin≤ENNReal.ofReal (384*r/p) := by
      rw [hBmax,hqlo,←ENNReal.ofReal_div_of_pos (by positivity : 0<p/128)]
      apply ENNReal.ofReal_le_ofReal
      calc
        (I+2*r)/(p/128)≤(3*r)/(p/128) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          have hIr' : I≤r := hIr
          linarith only [hIr']
        _ = _ := by ring
    have ho' := ho.trans (mul_le_mul' hc le_rfl)
    calc
      O ≤ (ENNReal.ofReal (384*r/p)*ENNReal.ofReal E)/ENNReal.ofReal (B.rmin^2*B.Dmin) := by
        simpa only [O,div_eq_mul_inv] using mul_le_mul' ho' (le_refl ((ENNReal.ofReal (B.rmin^2*B.Dmin))⁻¹))
      _ = ENNReal.ofReal (3072*E/(p*r*φ^2)) := by
        rw [hBmin,hBDmin,←ENNReal.ofReal_mul (by positivity : 0≤384*r/p),
          ←ENNReal.ofReal_div_of_pos (by positivity : 0<(r/2)^2*(φ^2/2))]
        congr 1
        field_simp [hp.ne',hr.ne',hφ.ne']
        ring
      _ ≤ _ := by apply ENNReal.ofReal_le_ofReal; gcongr; norm_num
  have hbO : O≤ENNReal.ofReal (491520*I*E/(r^2*θ^2)) := by
    have ho := F.closedEulerian_angular_time_budget hs hT zX B hS hJ hC hR hθ hφ hI.le hJI
      le_rfl (by change 0<8*φ^2; positivity) le_rfl
    calc
      O ≤ (ENNReal.ofReal (16*I*φ^2/θ^2)*ENNReal.ofReal E)/ENNReal.ofReal (B.rmin^2*B.Dmin) := by
        simpa only [O,div_eq_mul_inv] using mul_le_mul' ho (le_refl ((ENNReal.ofReal (B.rmin^2*B.Dmin))⁻¹))
      _ = ENNReal.ofReal (128*I*E/(r^2*θ^2)) := by
        rw [hBmin,hBDmin,←ENNReal.ofReal_mul (by positivity : 0≤16*I*φ^2/θ^2),
          ←ENNReal.ofReal_div_of_pos (by positivity : 0<(r/2)^2*(φ^2/2))]
        congr 1
        field_simp [hr.ne',hφ.ne',hθ.ne']
        ring
      _ ≤ _ := by apply ENNReal.ofReal_le_ofReal; gcongr; norm_num
  have hvolume : volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2) ≤
      ENNReal.ofReal (576*I*r*φ^2) := by
    rw [Real.volume_Icc,hBmax,hBmin]
    calc
      _ ≤ ENNReal.ofReal I*ENNReal.ofReal (2*r-r/2)*ENNReal.ofReal (384*φ^2) := by gcongr
      _ = _ := by
        rw [←ENNReal.ofReal_mul hI.le,←ENNReal.ofReal_mul (mul_nonneg hI.le (by linarith : 0≤2*r-r/2))]
        congr 1
        ring
  have hgood : ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I (k 2) ≤
      ENNReal.ofReal (20*I*E) := by
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.goodFieldBudget_uniform X (fun t=>velocity (V t)) 1 hJ hI hJI)
    calc
      _ ≤ ENNReal.ofReal I*((4*1+1:ℕ)*ENNReal.ofReal (4*E)) := mul_le_mul' le_rfl hh
      _ = _ := by
        change ENNReal.ofReal I*(5*ENNReal.ofReal (4*E))=_
        rw [←ENNReal.ofReal_ofNat (n:=5),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤5),
          ←ENNReal.ofReal_mul hI.le]
        congr 1
        ring
  have hmag : ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T 1
      (max 0 (a-B.rmax)) (min T (b-B.rmin)) I (k 2) ≤ ENNReal.ofReal (40*(I+2*r)*E) := by
    have hsub : Icc (max 0 (a-B.rmax)) (min T (b-B.rmin))⊆Icc 0 T :=
      Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
    have hh : min T (b-B.rmin)-max 0 (a-B.rmax) ≤ (1+2*r/I)*I := by
      have hb' := min_le_right T (b-B.rmin)
      have ha' := le_max_right 0 (a-B.rmax)
      rw [hBmax] at ha'
      rw [hBmin] at hb'
      have he : (1+2*r/I)*I=I+2*r := by field_simp
      rw [hBmin,hBmax,he]
      linarith only [hJI,hb',ha',hr]
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.magneticFieldBudget_uniform F.flow zX 1 hsub hI (by positivity : 0≤1+2*r/I) hh)
    calc
      _ ≤ ENNReal.ofReal (2*I)*((2*(4*1+1):ℕ)*ENNReal.ofReal (1+2*r/I)*ENNReal.ofReal (2*E)) :=
        mul_le_mul' le_rfl hh
      _ = _ := by
        change ENNReal.ofReal (2*I)*(10*ENNReal.ofReal (1+2*r/I)*ENNReal.ofReal (2*E))=_
        rw [←ENNReal.ofReal_ofNat (n:=10),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10),
          ←ENNReal.ofReal_mul (by positivity : 0≤10*(1+2*r/I)),
          ←ENNReal.ofReal_mul (by positivity : 0≤2*I)]
        congr 1
        field_simp [hI.ne']
        ring

  have hmag' : ENNReal.ofReal (40*(I+2*r)*E)≤ENNReal.ofReal (120*r*E) := by
    apply ENNReal.ofReal_le_ofReal
    have hIr' : I≤r := hIr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hIr') hE]
  have heG : 80*φ/(p/128*θ^2)=10240*φ/(p*θ^2) := by ring
  have heB : 80/(p/128)=10240/p := by ring
  dsimp only at hn
  rw [heG,heB] at hn
  apply hn.trans
  apply add_le_add
  · apply mul_le_mul' le_rfl
    apply mul_le_mul' (ENNReal.rpow_le_rpow hgood (by norm_num))
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    exact min_le_min (mul_le_mul' le_rfl hvolume) (mul_le_mul' le_rfl hgO)
  · apply mul_le_mul' le_rfl
    apply mul_le_mul' (ENNReal.rpow_le_rpow (hmag.trans hmag') (by norm_num))
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    exact min_le_min (mul_le_mul' le_rfl hvolume) (mul_le_mul' le_rfl hbO)

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma relative_radius_cauchy_near {C E Z I p ν r φ γ : ℝ}
    (hC : 0≤C) (hZ : 0≤Z) (hI : 0<I) (hp : 0<p)
    (hν : 0≤ν) (hr : 0≤r) (hφ : 0≤φ) (hγ : 0≤γ) :
    ENNReal.ofReal (10240*γ/p)*
      ((ENNReal.ofReal (Z*I))^(1/2:ℝ)*
        ((ENNReal.ofReal (128*C*p^3*ν^2))^2*ENNReal.ofReal (576*I*r*φ^2))^(1/2:ℝ)) ≤
    ENNReal.ofReal (relativeCauchyConstant C E Z*(I*p^2*ν^2*φ*γ)*Real.sqrt r) := by
  calc
    _ = ENNReal.ofReal ((31457280*C*Real.sqrt Z)*(I*p^2*ν^2*φ*γ)*Real.sqrt r) := by
      rw [←ENNReal.ofReal_pow (by positivity : 0≤128*C*p^3*ν^2),
        ←ENNReal.ofReal_mul (sq_nonneg _),
        ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
        relative_density_near_sqrt hC hI.le hp.le hν hr hφ,
        Real.sqrt_mul hZ,
        ←ENNReal.ofReal_mul (by positivity : 0≤Real.sqrt Z*Real.sqrt I),
        ←ENNReal.ofReal_mul (by positivity : 0≤10240*γ/p)]
      congr 1
      have hIsq : Real.sqrt I*Real.sqrt I=I := Real.mul_self_sqrt hI.le
      calc
        _ = 31457280*C*Real.sqrt Z*(Real.sqrt I*Real.sqrt I)*p^2*ν^2*φ*γ*Real.sqrt r := by
          field_simp [hp.ne']
          ring
        _ = _ := by rw [hIsq]; ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact le_add_of_nonneg_right (by positivity)

lemma Admissible.direct_source_short_near {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (k : Fin 4→ℕ) (j : ℕ) (a b I w : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ I → 0 < I →
      max 1 T*cappedRepresentative (k 3)≤I →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let σ := cappedRepresentative j
      let ν := min θ σ
      let r := max 1 T*cappedRepresentative (k 3)
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := relativeRepresentativeClosedBin T w k j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Kg := relativeCauchyConstant Cg E (20*E)
      let Kb := relativeCauchyConstant Cb E (120*E)
      (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z
        ∂physicalBinMeasure V B (Icc a b)) ≤
      ENNReal.ofReal ((Kg*(I*p^2*ν^2*φ^2/θ^2)+Kb*(I*p^2*ν^2*φ))*Real.sqrt r) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_two_budget_bound
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S k j a b I w hS hS0 ha hb hJI hI hrI
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let σ := cappedRepresentative j
  let r := max 1 T*cappedRepresentative (k 3)
  let B := relativeRepresentativeClosedBin T w k j
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let E := ∫x : Vec,totalEnergy s (0,x)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hσ : 0<σ := cappedRepresentative_pos _
  have hr : 0<r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hBmax : B.rmax=2*r := by dsimp [B,relativeRepresentativeClosedBin,representativeClosedBin,r]; ring
  have hBmin : B.rmin=r/2 := rfl
  have hBDmin : B.Dmin=φ^2/2 := rfl
  have hqlo : B.qmin=p/128 := rfl
  have hqhi : B.qmax≤p := by change p/32≤p; linarith only [hp]
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hC : Icc (max 0 (a-B.rmax)) (min T (b-B.rmin))⊆Icc 0 T :=
    Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have hR : 0<B.rmin := by rw [hBmin]; positivity
  have hD : 0<B.Dmin := by rw [hBDmin]; positivity
  have hangle (D : ℝ) (hD : D∈Icc B.Dmin B.Dmax) : DyadicWindow 1 (k 2) (Real.sqrt (D/2)) :=
    dyadicWindow_one_sqrt (k 2)
      (by simpa only [B,relativeRepresentativeClosedBin,representativeClosedBin,cappedRepresentative,inv_pow] using hD.1)
      (by simpa only [B,relativeRepresentativeClosedBin,representativeClosedBin,cappedRepresentative,inv_pow] using hD.2)
  have hn := hsource s T F hs hT h0 zX B S a b I (p/128) p θ φ σ 1 (k 2)
    hS hS0 hJ hI (by positivity) hp hθ hφ hσ.le hR hD le_rfl hqhi
    le_rfl le_rfl le_rfl le_rfl le_rfl hangle
  have hvolume : volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2) ≤
      ENNReal.ofReal (576*I*r*φ^2) := by
    rw [Real.volume_Icc,hBmax,hBmin]
    calc
      _ ≤ ENNReal.ofReal I*ENNReal.ofReal (2*r-r/2)*ENNReal.ofReal (384*φ^2) := by gcongr
      _ = _ := by
        rw [←ENNReal.ofReal_mul hI.le,←ENNReal.ofReal_mul (mul_nonneg hI.le (by linarith : 0≤2*r-r/2))]
        congr 1
        ring
  have hgood : ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I (k 2) ≤
      ENNReal.ofReal (20*I*E) := by
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.goodFieldBudget_uniform X (fun t=>velocity (V t)) 1 hJ hI hJI)
    calc
      _ ≤ ENNReal.ofReal I*((4*1+1:ℕ)*ENNReal.ofReal (4*E)) := mul_le_mul' le_rfl hh
      _ = _ := by
        change ENNReal.ofReal I*(5*ENNReal.ofReal (4*E))=_
        rw [←ENNReal.ofReal_ofNat (n:=5),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤5),
          ←ENNReal.ofReal_mul hI.le]
        congr 1
        ring
  have hmag : ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T 1
      (max 0 (a-B.rmax)) (min T (b-B.rmin)) I (k 2) ≤ ENNReal.ofReal (40*(I+2*r)*E) := by
    have hsub : Icc (max 0 (a-B.rmax)) (min T (b-B.rmin))⊆Icc 0 T :=
      Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
    have hh : min T (b-B.rmin)-max 0 (a-B.rmax) ≤ (1+2*r/I)*I := by
      have hb' := min_le_right T (b-B.rmin)
      have ha' := le_max_right 0 (a-B.rmax)
      rw [hBmax] at ha'
      rw [hBmin] at hb'
      have he : (1+2*r/I)*I=I+2*r := by field_simp
      rw [hBmin,hBmax,he]
      linarith only [hJI,hb',ha',hr]
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.magneticFieldBudget_uniform F.flow zX 1 hsub hI (by positivity : 0≤1+2*r/I) hh)
    calc
      _ ≤ ENNReal.ofReal (2*I)*((2*(4*1+1):ℕ)*ENNReal.ofReal (1+2*r/I)*ENNReal.ofReal (2*E)) :=
        mul_le_mul' le_rfl hh
      _ = _ := by
        change ENNReal.ofReal (2*I)*(10*ENNReal.ofReal (1+2*r/I)*ENNReal.ofReal (2*E))=_
        rw [←ENNReal.ofReal_ofNat (n:=10),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10),
          ←ENNReal.ofReal_mul (by positivity : 0≤10*(1+2*r/I)),
          ←ENNReal.ofReal_mul (by positivity : 0≤2*I)]
        congr 1
        field_simp [hI.ne']
        ring

  have hmag' : ENNReal.ofReal (40*(I+2*r)*E)≤ENNReal.ofReal (120*I*E) := by
    apply ENNReal.ofReal_le_ofReal
    have hrI' : r≤I := hrI
    nlinarith only [mul_nonneg (sub_nonneg.mpr hrI') hE]
  have heG : 80*φ/(p/128*θ^2)=10240*φ/(p*θ^2) := by ring
  have heB : 80/(p/128)=10240/p := by ring
  dsimp only at hn
  rw [heG,heB] at hn
  have hnear := hn.trans (add_le_add
    (mul_le_mul' le_rfl (mul_le_mul' (ENNReal.rpow_le_rpow hgood (by norm_num))
      (ENNReal.rpow_le_rpow ((min_le_left _ _).trans (mul_le_mul' le_rfl hvolume)) (by norm_num))))
    (mul_le_mul' le_rfl (mul_le_mul' (ENNReal.rpow_le_rpow (hmag.trans hmag') (by norm_num))
      (ENNReal.rpow_le_rpow ((min_le_left _ _).trans (mul_le_mul' le_rfl hvolume)) (by norm_num)))))
  let ν := min θ σ
  have hν : 0≤ν := (lt_min hθ hσ).le
  have hg := relative_radius_cauchy_near (E:=E) hCg (show 0≤20*E by positivity)
    hI hp hν hr.le hφ.le (show 0≤φ/θ^2 by positivity)
  have hm := relative_radius_cauchy_near (E:=E) hCb (show 0≤120*E by positivity)
    hI hp hν hr.le hφ.le (show 0≤(1:ℝ) by norm_num)
  have heγ : 10240*(φ/θ^2)/p=10240*φ/(p*θ^2) := by ring
  have hea : I*p^2*ν^2*φ*(φ/θ^2)=I*p^2*ν^2*φ^2/θ^2 := by ring
  rw [heγ,hea,show (20*E)*I=20*I*E by ring] at hg
  simp only [mul_one] at hm
  rw [show (120*E)*I=120*I*E by ring] at hm
  have hG0 : 0≤relativeCauchyConstant Cg E (20*E)*(I*p^2*ν^2*φ^2/θ^2)*Real.sqrt r :=
    mul_nonneg (mul_nonneg (relativeCauchyConstant_nonneg hCg) (by positivity)) (Real.sqrt_nonneg _)
  have hB0 : 0≤relativeCauchyConstant Cb E (120*E)*(I*p^2*ν^2*φ)*Real.sqrt r :=
    mul_nonneg (mul_nonneg (relativeCauchyConstant_nonneg hCb) (by positivity)) (Real.sqrt_nonneg _)
  apply hnear.trans
  calc
    _ ≤ ENNReal.ofReal (relativeCauchyConstant Cg E (20*E)*(I*p^2*ν^2*φ^2/θ^2)*Real.sqrt r)+
        ENNReal.ofReal (relativeCauchyConstant Cb E (120*E)*(I*p^2*ν^2*φ)*Real.sqrt r) := add_le_add hg hm
    _ = _ := by rw [←ENNReal.ofReal_add hG0 hB0]; congr 1; ring

end RVM

end

end OAI
