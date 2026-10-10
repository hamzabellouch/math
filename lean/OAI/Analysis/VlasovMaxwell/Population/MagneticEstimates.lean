import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.SpatialEstimates

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma direct_magnetic_near_ennreal {C I E H h φ p θ : ℝ}
    (hC : 0≤C) (hI : 0≤I) (hE : 0≤E) (hH : 0≤H) (hh : 0≤h)
    (hφ : 0<φ) (hp : 0<p) (hθ : 0<θ) :
    ENNReal.ofReal (1/p)*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
      ((ENNReal.ofReal (128*C*p^3*θ^2))^2*ENNReal.ofReal (768*I*(H*h)*φ^2))^(1/2:ℝ))=
    ENNReal.ofReal ((128*C*Real.sqrt 15360*Real.sqrt E*Real.sqrt H)*(I*Real.sqrt h*p^2*θ^2*φ)) := by
  have he : (1:ℝ)/p=(θ^2/φ)*(φ/(p*θ^2)) := by field_simp
  rw [he,ENNReal.ofReal_mul (by positivity : 0≤θ^2/φ),mul_assoc,
    direct_good_near_ennreal hC hI hE hH hh hφ.le hp hθ,
    ←ENNReal.ofReal_mul (by positivity : 0≤θ^2/φ)]
  congr 1
  field_simp

lemma direct_magnetic_far_ennreal {C K E I p θ O H h φ : ℝ}
    (hC : 0≤C) (hK : 0≤K) (hE : 0≤E) (hI : 0≤I) (hp : 0<p) (hθ : 0<θ)
    (hO : 0≤O) (hH : 1≤H) (hh : 0<h) (hφ : 0<φ) :
    ENNReal.ofReal (1/p)*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
      ((ENNReal.ofReal (128*C*p^3*θ^2))*(ENNReal.ofReal (K*O)*ENNReal.ofReal E/
        ENNReal.ofReal ((H*h)^2*φ^2/8)))^(1/2:ℝ))≤
    ENNReal.ofReal ((Real.sqrt (20480*C*K)*E)*(Real.sqrt I*Real.sqrt (p*O)*θ/(h*φ))) := by
  have he : (1:ℝ)/p=(θ^2/φ)*(φ/(p*θ^2)) := by field_simp
  rw [he,ENNReal.ofReal_mul (by positivity : 0≤θ^2/φ),mul_assoc]
  apply (mul_le_mul' le_rfl (direct_good_far_ennreal hC hK hE hI hp hθ hO hH hh hφ)).trans_eq
  rw [←ENNReal.ofReal_mul (by positivity : 0≤θ^2/φ)]
  congr 1
  field_simp

lemma Admissible.representative_magnetic_short_Cauchy {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ → ∀(zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I → cappedRepresentative (k 3)≤I →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let h := cappedRepresentative (k 3)
      let H := max 1 T
      let B := representativeClosedBin T w k
      let O := coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T B (tsupport d.f₀) a b
          (max 0 (a-B.rmax)) (min T (b-B.rmin)))
      let E := (2+4*max 1 T₀)*datumEnergyNumber d
      let D := ENNReal.ofReal (128*C*p^3*θ^2)
      representativeMagneticCost s F zX w k a b ≤
        ENNReal.ofReal (1/p)*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
          (min (D^2*ENNReal.ofReal (768*I*(H*h)*φ^2))
            (D*(O/ENNReal.ofReal ((H*h)^2*φ^2/8))))^(1/2:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := hd.uniform_actual_magnetic_Cauchy
  refine ⟨C,hC,?_⟩
  intro s T F hs hT hTT zX k a b I w ha hb hI hab hhI
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let r := max 1 T*cappedRepresentative (k 3)
  let B := representativeClosedBin T w k
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hr : 0<r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hBmax : B.rmax=2*r := by dsimp [B,representativeClosedBin,r]; ring
  have hBmin : B.rmin=r/2 := rfl
  have hmeasure : volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)≤
      ENNReal.ofReal (768*I*r*φ^2) := by
    calc
      _ ≤ ENNReal.ofReal I*ENNReal.ofReal (2*r)*ENNReal.ofReal (384*φ^2) := by
        apply mul_le_mul' (mul_le_mul' _ _) le_rfl
        · rw [Real.volume_Icc]; exact ENNReal.ofReal_le_ofReal hab
        · apply ENNReal.ofReal_le_ofReal; rw [hBmax,hBmin]; linarith only [hr]
      _ = _ := by rw [←ENNReal.ofReal_mul hI.le,←ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  have hE := hd.datumEnergyNumber_nonneg
  have hmag : ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T 1
      (max 0 (a-B.rmax)) (min T (b-B.rmin)) I (k 2) ≤
      ENNReal.ofReal (20*I*((2+4*max 1 T₀)*datumEnergyNumber d)) := by
    have hsub : Icc (max 0 (a-B.rmax)) (min T (b-B.rmin))⊆Icc 0 T :=
      Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
    have hrI : r ≤ max 1 T₀*I := mul_le_mul (max_le_max le_rfl hTT) hhI
      (cappedRepresentative_pos _).le (zero_le_one.trans (le_max_left _ _))
    have hlen : min T (b-B.rmin)-max 0 (a-B.rmax)≤(1+2*max 1 T₀)*I := by
      have hb' := min_le_right T (b-B.rmin)
      have ha' := le_max_right 0 (a-B.rmax)
      rw [hBmax] at ha'
      rw [hBmin] at hb'
      rw [hBmax,hBmin]
      nlinarith only [hab,hb',ha',hrI,hr]
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.energyPrefix.magneticFieldBudget_uniform F.flow zX 1 hsub hI (by positivity : 0≤1+2*max 1 T₀) hlen)
    rw [hs.initial_energy_eq] at hh
    calc
      _ ≤ ENNReal.ofReal (2*I)*((2*(4*1+1):ℕ)*ENNReal.ofReal (1+2*max 1 T₀)*ENNReal.ofReal (2*datumEnergyNumber d)) :=
        mul_le_mul' le_rfl hh
      _ = _ := by
        norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat]
        rw [←ENNReal.ofReal_ofNat (n:=10),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10),
          ←ENNReal.ofReal_mul (by positivity : 0≤10*(1+2*max 1 T₀)),←ENNReal.ofReal_mul (by positivity : 0≤2*I)]
        congr 1
        ring
  have hangle (D : ℝ) (hD : D∈Icc B.Dmin B.Dmax) : DyadicWindow 1 (k 2) (Real.sqrt (D/2)) :=
    dyadicWindow_one_sqrt (k 2)
      (by simpa only [B,representativeClosedBin,cappedRepresentative,inv_pow] using hD.1)
      (by simpa only [B,representativeClosedBin,cappedRepresentative,inv_pow] using hD.2)
  have hS0 : tsupport (fun z=>s.f (0,z))⊆tsupport d.f₀ := by
    have he : (fun z=>s.f (0,z))=d.f₀ := funext hs.initial_f
    rw [he]
  have hbnd := hbound s T F hs.energyPrefix hT hs.initial_f zX B (tsupport d.f₀)
    a b I p θ φ 1 1 (k 2) hd.2.1 hS0 hJ hI hp hθ.le hφ.le (by norm_num)
    (by change 0<r/2; positivity) (by change 0<φ^2/2; positivity) le_rfl
    (by change p/32≤p; linarith) le_rfl le_rfl (by norm_num [B,representativeClosedBin]) hangle
  dsimp only at hbnd
  have hθ1 : θ≤1 := cappedRepresentative_le_one (k 1)
  simp only [min_eq_left hθ1] at hbnd
  have hden : B.rmin^2*B.Dmin=r^2*φ^2/8 := by change (r/2)^2*(φ^2/2)=_; ring
  rw [hden] at hbnd
  have heq : representativeMagneticCost s F zX w k a b=
      ENNReal.ofReal (1/p)*(∫⁻z : ConeCoordinate,ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal φ*
        ENNReal.ofReal (prefixConeMagnetic s T X z)*physicalBinDensity s X V B z.1 z.2.1 z.2.2
          ∂physicalBinMeasure V B (Icc a b)) := by
    unfold representativeMagneticCost
    dsimp only
    rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro z
    change ENNReal.ofReal (φ/p) * (ENNReal.ofReal (z.1-z.2.1) *
      ENNReal.ofReal (prefixConeMagnetic s T X z) * physicalBinDensity s X V B z.1 z.2.1 z.2.2) = _
    simp only [ENNReal.ofReal_div_of_pos hp,ENNReal.ofReal_one]
    simp only [div_eq_mul_inv]
    ring
  rw [heq]
  apply mul_le_mul' le_rfl
  apply hbnd.trans
  apply mul_le_mul' (ENNReal.rpow_le_rpow hmag (by norm_num))
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  exact min_le_min (mul_le_mul' le_rfl hmeasure) le_rfl

lemma Admissible.representative_magnetic_short_central {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ → ∀(zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I → cappedRepresentative (k 3)≤I →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let E := (2+4*max 1 T₀)*datumEnergyNumber d
      representativeMagneticCost s F zX w k a b ≤
        ENNReal.ofReal (1/p)*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
          (ENNReal.ofReal (128*C*p^3*θ^2)*representativeCentralCost s F zX w k a b)^(1/2:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := hd.uniform_physicalBinDensity_constant
  refine ⟨C,hC,?_⟩
  intro s T F hs hT hTT zX k a b I w ha hb hI hab hhI
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let r := max 1 T*cappedRepresentative (k 3)
  let B := representativeClosedBin T w k
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let N : ConeCoordinate→ℝ≥0∞ := fun z=>physicalBinDensity s X V B z.1 z.2.1 z.2.2
  let μ := physicalBinMeasure V B (Icc a b)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hr : 0<r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hBmax : B.rmax=2*r := by dsimp [B,representativeClosedBin,r]; ring
  have hBmin : B.rmin=r/2 := rfl
  have hE := hd.datumEnergyNumber_nonneg
  have hmag : ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T 1
      (max 0 (a-B.rmax)) (min T (b-B.rmin)) I (k 2) ≤
      ENNReal.ofReal (20*I*((2+4*max 1 T₀)*datumEnergyNumber d)) := by
    have hsub : Icc (max 0 (a-B.rmax)) (min T (b-B.rmin))⊆Icc 0 T :=
      Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
    have hrI : r ≤ max 1 T₀*I := mul_le_mul (max_le_max le_rfl hTT) hhI
      (cappedRepresentative_pos _).le (zero_le_one.trans (le_max_left _ _))
    have hlen : min T (b-B.rmin)-max 0 (a-B.rmax)≤(1+2*max 1 T₀)*I := by
      have hb' := min_le_right T (b-B.rmin)
      have ha' := le_max_right 0 (a-B.rmax)
      rw [hBmax] at ha'
      rw [hBmin] at hb'
      rw [hBmax,hBmin]
      nlinarith only [hab,hb',ha',hrI,hr]
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.energyPrefix.magneticFieldBudget_uniform F.flow zX 1 hsub hI (by positivity : 0≤1+2*max 1 T₀) hlen)
    rw [hs.initial_energy_eq] at hh
    calc
      _ ≤ ENNReal.ofReal (2*I)*((2*(4*1+1):ℕ)*ENNReal.ofReal (1+2*max 1 T₀)*ENNReal.ofReal (2*datumEnergyNumber d)) :=
        mul_le_mul' le_rfl hh
      _ = _ := by
        norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat]
        rw [←ENNReal.ofReal_ofNat (n:=10),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10),
          ←ENNReal.ofReal_mul (by positivity : 0≤10*(1+2*max 1 T₀)),←ENNReal.ofReal_mul (by positivity : 0≤2*I)]
        congr 1
        ring
  have hangle (D : ℝ) (hD : D∈Icc B.Dmin B.Dmax) : DyadicWindow 1 (k 2) (Real.sqrt (D/2)) :=
    dyadicWindow_one_sqrt (k 2)
      (by simpa only [B,representativeClosedBin,cappedRepresentative,inv_pow] using hD.1)
      (by simpa only [B,representativeClosedBin,cappedRepresentative,inv_pow] using hD.2)
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs.energyPrefix hT).comp (continuous_id.prodMk continuous_const)
  have hX : Measurable X := hα.fst.measurable
  have hV : Measurable V := hα.snd.measurable
  have hN : AEMeasurable N μ :=
    physicalBinDensity_aemeasurable hs.energyPrefix hT hX hV B measurableSet_Icc hJ
  have hG := hs.energyPrefix.measurable_prefixConeMagnetic hT hX
  let W : ConeCoordinate→ℝ≥0∞ := fun z=>ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal φ*
      ENNReal.ofReal (prefixConeMagnetic s T X z)
  have hW : AEMeasurable W μ :=
    ((measurable_fst.sub (measurable_fst.comp measurable_snd)).ennreal_ofReal.mul_const (ENNReal.ofReal φ) |>.mul hG.ennreal_ofReal).aemeasurable
  have hfield : (∫⁻z, W z^2 ∂μ)≤ENNReal.ofReal (20*I*((2+4*max 1 T₀)*datumEnergyNumber d)) := by
    apply le_trans _ ((F.physicalBin_magneticField hs.energyPrefix hT zX B 1 (k 2) hJ hI le_rfl hangle).trans hmag)
    apply le_of_eq
    apply lintegral_congr_ae
    apply ae_restrict_of_forall_mem (measurableSet_physicalBinBase hV B measurableSet_Icc)
    intro z hz
    have hr : 0≤z.1-z.2.1 := sub_nonneg.mpr hz.2.1.2
    have hg : 0≤prefixConeMagnetic s T X z := norm_nonneg _
    dsimp [W]
    rw [mul_pow,mul_pow,←ENNReal.ofReal_pow hr,←ENNReal.ofReal_pow hφ.le,
      ←ENNReal.ofReal_pow hg,←ENNReal.ofReal_mul (sq_nonneg _),
      ←ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  have hD : ∀ᵐz ∂μ,N z≤ENNReal.ofReal (128*C*p^3*θ^2) := by
    apply ae_restrict_of_forall_mem (measurableSet_physicalBinBase hV B measurableSet_Icc)
    intro z hz
    have hh := hbound s T F hs.energyPrefix hs.initial_f X V B z.1 z.2.1 z.2.2 p θ 1
      ⟨hz.2.1.1,hz.2.1.2.trans (hJ hz.1).2⟩ hp.le hθ.le (by norm_num)
      (by change p/32≤p; linarith) le_rfl (by norm_num [B,representativeClosedBin])
    have hθ1 : θ≤1 := cappedRepresentative_le_one (k 1)
    simpa only [min_eq_left hθ1] using hh
  have heq : representativeMagneticCost s F zX w k a b=
      ENNReal.ofReal (1/p)*(∫⁻z : ConeCoordinate,ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal φ*
        ENNReal.ofReal (prefixConeMagnetic s T X z)*physicalBinDensity s X V B z.1 z.2.1 z.2.2
          ∂physicalBinMeasure V B (Icc a b)) := by
    unfold representativeMagneticCost
    dsimp only
    rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro z
    change ENNReal.ofReal (φ/p) * (ENNReal.ofReal (z.1-z.2.1) *
      ENNReal.ofReal (prefixConeMagnetic s T X z) * physicalBinDensity s X V B z.1 z.2.1 z.2.2) = _
    simp only [ENNReal.ofReal_div_of_pos hp,ENNReal.ofReal_one]
    simp only [div_eq_mul_inv]
    ring
  rw [heq]
  apply mul_le_mul' le_rfl
  have hh := lintegral_product_bound_two μ hW hN hfield hD
    (le_rfl : (∫⁻z,N z ∂μ)≤∫⁻z,N z ∂μ) (le_rfl : μ univ≤μ univ)
  apply hh.trans
  apply mul_le_mul' le_rfl
  exact ENNReal.rpow_le_rpow (min_le_right _ _) (by norm_num)

lemma magnetic_central_near_scalar {C E D I h p θ φ : ℝ}
    (hC : 0≤C) (hE : 0≤E) (hD : 0≤D) (hI : 0≤I) (hh : 0≤h)
    (hp : 0<p) (hθ : 0≤θ) (hφ : 0≤φ) :
    (1/p)*(Real.sqrt (20*I*E)*Real.sqrt ((128*C*p^3*θ^2)*(D*(I*h*p^3*θ^2*φ^2))))=
    Real.sqrt (2560*C*E*D)*(I*Real.sqrt h*p^2*θ^2*φ) := by
  rw [←Real.sqrt_mul (by positivity : 0≤20*I*E)]
  have he : Real.sqrt ((20*I*E)*((128*C*p^3*θ^2)*(D*(I*h*p^3*θ^2*φ^2))))=
      Real.sqrt (2560*C*E*D)*(I*Real.sqrt h*p^3*θ^2*φ) := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity)
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hθ 2)) hφ))).mpr
    simp only [mul_pow,Real.sq_sqrt (by positivity : 0≤2560*C*E*D),Real.sq_sqrt hh]
    ring
  rw [he]
  field_simp

lemma magnetic_central_far_scalar {C E D I R h p θ φ : ℝ}
    (hC : 0≤C) (hE : 0≤E) (hD : 0≤D) (hI : 0≤I) (hR : 0≤R)
    (hh : 0<h) (hp : 0<p) (hθ : 0≤θ) (hφ : 0<φ) :
    (1/p)*(Real.sqrt (20*I*E)*Real.sqrt ((128*C*p^3*θ^2)*(D*(R^2/(p*h*φ^2)))))=
    Real.sqrt (2560*C*E*D)*(Real.sqrt I*R*θ/(Real.sqrt h*φ)) := by
  rw [←Real.sqrt_mul (by positivity : 0≤20*I*E)]
  have he : Real.sqrt ((20*I*E)*((128*C*p^3*θ^2)*(D*(R^2/(p*h*φ^2)))))=
      Real.sqrt (2560*C*E*D)*(Real.sqrt I*R*p*θ/(Real.sqrt h*φ)) := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    simp only [div_pow,mul_pow,Real.sq_sqrt (by positivity : 0≤2560*C*E*D),
      Real.sq_sqrt hh.le,Real.sq_sqrt hI]
    field_simp
    ring
  rw [he]
  field_simp

lemma magnetic_central_near_ennreal {C E D I h p θ φ : ℝ}
    (hC : 0≤C) (hE : 0≤E) (hD : 0≤D) (hI : 0≤I) (hh : 0≤h)
    (hp : 0<p) (hθ : 0≤θ) (hφ : 0≤φ) :
    ENNReal.ofReal (1/p)*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
      (ENNReal.ofReal (128*C*p^3*θ^2)*ENNReal.ofReal (D*(I*h*p^3*θ^2*φ^2)))^(1/2:ℝ))=
    ENNReal.ofReal (Real.sqrt (2560*C*E*D)*(I*Real.sqrt h*p^2*θ^2*φ)) := by
  rw [←ENNReal.ofReal_mul (by positivity : 0≤128*C*p^3*θ^2),
    ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
    ←ENNReal.ofReal_mul (Real.sqrt_nonneg _),←ENNReal.ofReal_mul (by positivity),
    magnetic_central_near_scalar hC hE hD hI hh hp hθ hφ]

lemma magnetic_central_far_ennreal {C E D I R h p θ φ : ℝ}
    (hC : 0≤C) (hE : 0≤E) (hD : 0≤D) (hI : 0≤I) (hR : 0≤R)
    (hh : 0<h) (hp : 0<p) (hθ : 0≤θ) (hφ : 0<φ) :
    ENNReal.ofReal (1/p)*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
      (ENNReal.ofReal (128*C*p^3*θ^2)*ENNReal.ofReal (D*(R^2/(p*h*φ^2))))^(1/2:ℝ))=
    ENNReal.ofReal (Real.sqrt (2560*C*E*D)*(Real.sqrt I*R*θ/(Real.sqrt h*φ))) := by
  rw [←ENNReal.ofReal_mul (by positivity : 0≤128*C*p^3*θ^2),
    ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
    ←ENNReal.ofReal_mul (Real.sqrt_nonneg _),←ENNReal.ofReal_mul (by positivity),
    magnetic_central_far_scalar hC hE hD hI hR hh hp hθ hφ]

noncomputable def representativeRegularShortMagneticCost (s : Solution) {T : ℝ} (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (P M A I w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ := by
  classical
  exact if regularCentralIndex P M A I w k ∧ cappedRepresentative (k 3)≤I then
    representativeMagneticCost s F zX w k a b else 0

lemma Admissible.representative_regular_short_magnetic {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let h := cappedRepresentative (k 3)
      let R := representativeSharedRadius s F zX P M A w a b I (k 0,k 2)
      representativeRegularShortMagneticCost s F zX P M A I w k a b≤
        ENNReal.ofReal (C*min (I*Real.sqrt h*p^2*θ^2*φ) (Real.sqrt I*R*θ/(Real.sqrt h*φ))) := by
  classical
  obtain ⟨Cd,hCd,hmag⟩ := hd.representative_magnetic_short_central T₀
  obtain ⟨Cc,hCc,hcentral⟩ := hd.representative_regular_central_shared T₀
  let E := (2+4*max 1 T₀)*datumEnergyNumber d
  have hE : 0≤E := mul_nonneg (by positivity) hd.datumEnergyNumber_nonneg
  let C := Real.sqrt (2560*Cd*E*Cc)
  refine ⟨C,Real.sqrt_nonneg _,?_⟩
  intro M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha hb hI hab hw hsmall HZ
  dsimp only
  unfold representativeRegularShortMagneticCost
  split_ifs with hk
  · have hcen := hcentral M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha hb hI hab hw hsmall HZ
    unfold representativeRegularCentralCost at hcen
    rw [ite_eq_left hk.1] at hcen
    let p := sourceRepresentative (k 0)
    let θ := cappedRepresentative (k 1)
    let φ := cappedRepresentative (k 2)
    let h := cappedRepresentative (k 3)
    let R := representativeSharedRadius s F zX P M A w a b I (k 0,k 2)
    have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
    have hθ : 0<θ := cappedRepresentative_pos _
    have hφ : 0<φ := cappedRepresentative_pos _
    have hh : 0<h := cappedRepresentative_pos _
    have hR : 0≤R := zero_le_one.trans (representativeSharedRadius_one_le ..)
    have hmb := hmag s T F hs hT hTT zX k a b I w ha hb hI hab hk.2
    dsimp only at hcen hmb
    have hnear : representativeMagneticCost s F zX w k a b≤
        ENNReal.ofReal (C*(I*Real.sqrt h*p^2*θ^2*φ)) := by
      apply hmb.trans
      apply le_trans _ (le_of_eq (magnetic_central_near_ennreal hCd hE hCc hI.le hh.le hp hθ.le hφ.le))
      apply mul_le_mul' le_rfl
      apply mul_le_mul' le_rfl
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      apply mul_le_mul' le_rfl
      apply hcen.trans
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (min_le_left _ _) hCc)
    have hfar : representativeMagneticCost s F zX w k a b≤
        ENNReal.ofReal (C*(Real.sqrt I*R*θ/(Real.sqrt h*φ))) := by
      apply hmb.trans
      apply le_trans _ (le_of_eq (magnetic_central_far_ennreal hCd hE hCc hI.le hR hh hp hθ.le hφ))
      apply mul_le_mul' le_rfl
      apply mul_le_mul' le_rfl
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      apply mul_le_mul' le_rfl
      apply hcen.trans
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (min_le_right _ _) hCc)
    rw [mul_min_of_nonneg _ _ (Real.sqrt_nonneg _),ENNReal.ofReal_min]
    exact le_min hnear hfar
  · exact bot_le

lemma Admissible.representative_regular_short_magnetic_double_sum {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (np nf : ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → I≤1 → b-a≤I → 0<w →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let p := sourceRepresentative np
      let φ := cappedRepresentative nf
      let R := representativeSharedRadius s F zX P M A w a b I (np,nf)
      (∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative nt≤φ/16 then
        representativeRegularShortMagneticCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤
        ENNReal.ofReal (C*Real.sqrt I*R*p*φ) := by
  classical
  obtain ⟨C,hC,hbound⟩ := hd.representative_regular_short_magnetic T₀
  let K := dyadicBalanceConstant (1/2) (1/2)
  have hK : 0<K := dyadicBalanceConstant_pos (by norm_num) (by norm_num)
  refine ⟨2*K*C,by positivity,?_⟩
  intro M A P hM hA hP s T F hs hT hTT zX np nf a b I w hzX ha hb hI hI1 hJI hw HZ
  dsimp only
  let p := sourceRepresentative np
  let φ := cappedRepresentative nf
  let R := representativeSharedRadius s F zX P M A w a b I (np,nf)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hφ : 0<φ := cappedRepresentative_pos _
  have hR : 0<R := zero_lt_one.trans_le (representativeSharedRadius_one_le _ _ _ _ _ _ _ _ _ _ _)
  have hr (nt : ℕ) (hnt : cappedRepresentative nt≤φ/16) :
      (∑'nr : ℕ,representativeRegularShortMagneticCost s F zX P M A I w ![np,nt,nf,nr] a b)≤
      ENNReal.ofReal (C*(K*Real.sqrt I*R*p*cappedRepresentative nt)) := by
    calc
      _≤∑'nr : ℕ,ENNReal.ofReal (C*min
          (I*Real.sqrt (cappedRepresentative nr)*p^2*(cappedRepresentative nt)^2*φ)
          (Real.sqrt I*R*cappedRepresentative nt/(Real.sqrt (cappedRepresentative nr)*φ))) := by
        apply ENNReal.tsum_le_tsum
        intro nr
        exact hbound M A P hM hA hP s T F hs hT hTT zX ![np,nt,nf,nr] a b I w
          hzX ha hb hI hJI hw hnt HZ
      _=ENNReal.ofReal C*(∑'nr : ℕ,ENNReal.ofReal (min
          (I*Real.sqrt (cappedRepresentative nr)*p^2*(cappedRepresentative nt)^2*φ)
          (Real.sqrt I*R*cappedRepresentative nt/(Real.sqrt (cappedRepresentative nr)*φ)))) := by
        simp_rw [ENNReal.ofReal_mul hC,ENNReal.tsum_mul_left]
      _≤ENNReal.ofReal C*ENNReal.ofReal (K*Real.sqrt I*R*p*cappedRepresentative nt) :=
        mul_le_mul' le_rfl (magnetic_shared_radial_sum hI hI1 (representativeSharedRadius_one_le ..) hp (cappedRepresentative_pos _) (cappedRepresentative_le_one _) hφ)
      _=_ := (ENNReal.ofReal_mul hC).symm
  have hsum : (∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative nt≤φ/16 then
      representativeRegularShortMagneticCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤
      ENNReal.ofReal (K*C*Real.sqrt I*R*p)*
        (∑'nt : ℕ,ENNReal.ofReal (if cappedRepresentative nt≤φ then cappedRepresentative nt else 0)) := by
    rw [←ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro nt
    by_cases ht : cappedRepresentative nt≤φ/16
    · have ht' : cappedRepresentative nt≤φ := ht.trans (by linarith)
      simp only [ite_eq_left ht,ite_eq_left ht']
      apply (hr nt ht).trans_eq
      rw [←ENNReal.ofReal_mul (by positivity : 0≤K*C*Real.sqrt I*R*p)]
      congr 1
      ring
    · simp only [ite_eq_right ht,tsum_zero]
      exact bot_le
  apply hsum.trans
  calc
    _≤ENNReal.ofReal (K*C*Real.sqrt I*R*p)*ENNReal.ofReal (2*φ) :=
      mul_le_mul' le_rfl (capped_linear_tail_sum hφ)
    _=_ := by rw [←ENNReal.ofReal_mul (by positivity : 0≤K*C*Real.sqrt I*R*p)]; congr 1; ring

lemma Admissible.magnetic_regular_short_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → I≤1 → b-a≤I → 0<w → w≤P →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative nt≤cappedRepresentative n.2/16 then
          representativeRegularShortMagneticCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  classical
  obtain ⟨Cc,hCc,hcentral⟩ := hd.representative_regular_short_magnetic_double_sum T₀
  let E := 3468*datumEnergyNumber d
  let D := pairCountConstant+4*Real.sqrt pairCountConstant+2
  let K := 4+16384*Real.sqrt E*D
  have hE : 0≤E := mul_nonneg (by norm_num) hd.datumEnergyNumber_nonneg
  have hD : 0≤D := by dsimp [D]; exact add_nonneg (add_nonneg pairCountConstant_pos.le (by positivity)) (by norm_num)
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨Cc*K,mul_nonneg hCc hK,?_⟩
  intro M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hI1 hJI hw hwP HZ
  dsimp only
  let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
    1/sourceRepresentative n.1≤cappedRepresentative n.2}
  let J := representativeJointEnergy s F zX a b I
  let R := representativeSharedRadius s F zX P M A w a b I
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hR (n : ℕ×ℕ) : 0<R n := zero_lt_one.trans_le (representativeSharedRadius_one_le ..)
  have hp (n : ℕ) : 0<sourceRepresentative n := by dsimp [sourceRepresentative]; positivity
  have hpair (n : ℕ×ℕ) (hn : n∈Q) : sourceRepresentative n.1≤P ∧
      1/sourceRepresentative n.1≤cappedRepresentative n.2 := hn
  obtain ⟨hJs,hJsum,hJeq⟩ := hs.representativeJointEnergy_sum hd F zX hI hJI
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun n=>n∈Q)
  have hU (n) (hn : n∈U) : n∈Q := (Finset.mem_filter.mp hn).2
  have he : (∑n∈S,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
      if cappedRepresentative nt≤cappedRepresentative n.2/16 then
        representativeRegularShortMagneticCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)=
      ∑n∈U,(∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative nt≤cappedRepresentative n.2/16 then
        representativeRegularShortMagneticCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) := by
    simp [U,Finset.sum_filter,indicator_apply]
  rw [he]
  have hJn (n : ℕ×ℕ) : 0≤J n := representativeJointEnergy_nonneg ..
  have hbudget : ∑n∈U,J n≤E := (hJs.sum_le_tsum U (fun n _=>hJn n)).trans hJsum
  have hn := shared_radius_pair_sum hP hL hM.le hA hI.le hw hwP hE U J
    (fun n _=>hJn n) hbudget (fun n hn=>hpair n (hU n hn))
  change (∑n∈U,Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2)≤
    K*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w) at hn
  calc
    _≤∑n∈U,ENNReal.ofReal (Cc*Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hcentral M A P hM hA hP0 s T F hs hT hTT zX n.1 n.2 a b I w
        hzX ha hb hI hI1 hJI hw HZ
    _=ENNReal.ofReal (Cc*(∑n∈U,Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2)) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun n _=>by
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCc (Real.sqrt_nonneg I)) (hR n).le) (hp _).le) (cappedRepresentative_pos _).le)]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _≤_ := ENNReal.ofReal_le_ofReal (by
      have hh := mul_le_mul_of_nonneg_left hn hCc
      simpa only [mul_assoc] using hh)

lemma Admissible.representative_magnetic_short_near {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ → ∀(zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I → cappedRepresentative (k 3)≤I →
      representativeMagneticCost s F zX w k a b ≤
        ENNReal.ofReal (C*(I*Real.sqrt (cappedRepresentative (k 3))*(sourceRepresentative (k 0))^2*
          (cappedRepresentative (k 1))^2*cappedRepresentative (k 2))) := by
  obtain ⟨Cd,hCd,hmag⟩ := hd.representative_magnetic_short_Cauchy T₀
  let E := (2+4*max 1 T₀)*datumEnergyNumber d
  have hE : 0≤E := mul_nonneg (by positivity) hd.datumEnergyNumber_nonneg
  refine ⟨128*Cd*Real.sqrt 15360*Real.sqrt E*Real.sqrt (max 1 T₀),by positivity,?_⟩
  intro s T F hs hT hTT zX k a b I w ha hb hI hab hhI
  have hm := hmag s T F hs hT hTT zX k a b I w ha hb hI hab hhI
  dsimp only at hm
  have hp : 0<sourceRepresentative (k 0) := by dsimp [sourceRepresentative]; positivity
  have hθ := cappedRepresentative_pos (k 1)
  have hφ := cappedRepresentative_pos (k 2)
  have hh := cappedRepresentative_pos (k 3)
  have hH : 0 ≤ max 1 T := zero_le_one.trans (le_max_left _ _)
  apply hm.trans
  apply le_trans _ (le_of_eq (direct_magnetic_near_ennreal hCd hI.le hE hH hh.le hφ hp hθ)) |>.trans
  · apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (max_le_max le_rfl hTT)) (by positivity)
  · apply mul_le_mul' le_rfl
    apply mul_le_mul' le_rfl
    exact ENNReal.rpow_le_rpow (min_le_left _ _) (by norm_num)

noncomputable def representativeLowShortMagneticCost (s : Solution) {T : ℝ} (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (I w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ := by
  classical
  exact if cappedRepresentative (k 2)≤512/min (sourceRepresentative (k 0)) w ∧
    cappedRepresentative (k 3)≤I then representativeMagneticCost s F zX w k a b else 0

lemma Admissible.representative_low_magnetic_triple_sum {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (np : ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I → 0<w →
      (∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative nt≤cappedRepresentative nf/16 then
          representativeLowShortMagneticCost s F zX I w ![np,nt,nf,nr] a b else 0)≤
        ENNReal.ofReal (C*I*Real.sqrt I*(sourceRepresentative np)^2*(512/min (sourceRepresentative np) w)^3) := by
  classical
  obtain ⟨Cn,hCn,hnear⟩ := hd.representative_magnetic_short_near T₀
  let K := (1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹
  have hK : 0<K := majorant_shortSqrtConstant_pos
  refine ⟨4*K*Cn,by positivity,?_⟩
  intro s T F hs hT hTT zX np a b I w ha hb hI hJI hw
  let p := sourceRepresentative np
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hpoint (nf nt nr : ℕ) :
      (if cappedRepresentative nt≤cappedRepresentative nf/16 then
        representativeLowShortMagneticCost s F zX I w ![np,nt,nf,nr] a b else 0)≤
      ENNReal.ofReal Cn*(if cappedRepresentative nf≤512/min p w then
        if cappedRepresentative nt≤cappedRepresentative nf then
          if cappedRepresentative nr≤I then
            ENNReal.ofReal (I*Real.sqrt (cappedRepresentative nr)*p^2*(cappedRepresentative nt)^2*cappedRepresentative nf)
          else 0 else 0 else 0) := by
    by_cases ht : cappedRepresentative nt≤cappedRepresentative nf/16
    · rw [ite_eq_left ht]
      by_cases hr : cappedRepresentative nf≤512/min p w ∧ cappedRepresentative nr≤I
      · have hnt : cappedRepresentative nt≤cappedRepresentative nf := by
          have hf0 := (cappedRepresentative_pos nf).le
          linarith
        change (if cappedRepresentative nf≤512/min p w ∧ cappedRepresentative nr≤I then
          representativeMagneticCost s F zX w ![np,nt,nf,nr] a b else 0)≤_
        rw [ite_eq_left hr,ite_eq_left hr.1,ite_eq_left hnt,ite_eq_left hr.2,←ENNReal.ofReal_mul hCn]
        simpa [p] using hnear s T F hs hT hTT zX ![np,nt,nf,nr] a b I w ha hb hI hJI hr.2
      · have hz : representativeLowShortMagneticCost s F zX I w ![np,nt,nf,nr] a b=0 := by
          change (if cappedRepresentative nf≤512/min p w ∧ cappedRepresentative nr≤I then _ else 0)=0
          exact ite_eq_right hr
        rw [hz]
        exact bot_le
    · rw [ite_eq_right ht]
      exact bot_le
  calc
    _≤∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
        ENNReal.ofReal Cn*(if cappedRepresentative nf≤512/min p w then
          if cappedRepresentative nt≤cappedRepresentative nf then
            if cappedRepresentative nr≤I then
              ENNReal.ofReal (I*Real.sqrt (cappedRepresentative nr)*p^2*(cappedRepresentative nt)^2*cappedRepresentative nf)
            else 0 else 0 else 0) :=
      ENNReal.tsum_le_tsum (fun nf=>ENNReal.tsum_le_tsum (fun nt=>ENNReal.tsum_le_tsum (hpoint nf nt)))
    _=ENNReal.ofReal Cn*(∑'nf : ℕ,if cappedRepresentative nf≤512/min p w then
        ∑'nt : ℕ,if cappedRepresentative nt≤cappedRepresentative nf then
          ∑'nr : ℕ,if cappedRepresentative nr≤I then
            ENNReal.ofReal (I*Real.sqrt (cappedRepresentative nr)*p^2*(cappedRepresentative nt)^2*cappedRepresentative nf)
          else 0 else 0 else 0) := by
      simp only [ENNReal.tsum_mul_left]
      congr 1
      apply tsum_congr
      intro nf
      split_ifs with hf
      · apply tsum_congr
        intro nt
        split_ifs with ht <;> simp only [tsum_zero]
      · simp only [tsum_zero]
    _≤ENNReal.ofReal Cn*ENNReal.ofReal (4*K*I*Real.sqrt I*p^2*(512/min p w)^3) :=
      mul_le_mul' le_rfl (magnetic_low_triple_sum hI hp hw)
    _=_ := by rw [←ENNReal.ofReal_mul hCn]; congr 1; dsimp only [p]; ring

lemma Admissible.magnetic_low_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ P : ℝ,1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      0≤a → b≤T → 0<I → I≤1 → b-a≤I → 1≤w → w≤P →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative nt≤cappedRepresentative n.2/16 then
          representativeLowShortMagneticCost s F zX I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*(I*P^2*Real.log (2+P)/w)) := by
  classical
  obtain ⟨Cn,hCn,hnear⟩ := hd.representative_low_magnetic_triple_sum T₀
  have hpc := pairCountConstant_pos
  refine ⟨512^3*Cn*pairCountConstant,by positivity,?_⟩
  intro P hP hL s T F hs hT hTT zX a b I w ha hb hI hI1 hJI hw hwP
  dsimp only
  let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
    1/sourceRepresentative n.1≤cappedRepresentative n.2}
  let g := fun np=>∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
    if cappedRepresentative nt≤cappedRepresentative nf/16 then
      representativeLowShortMagneticCost s F zX I w ![np,nt,nf,nr] a b else 0
  let D := 512^3*Cn*I*P^2/w
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hw0 : 0<w := zero_lt_one.trans_le hw
  have hD : 0≤D := by dsimp [D]; positivity
  have hgb (np : ℕ) (hn : sourceRepresentative np≤P) : g np≤ENNReal.ofReal D := by
    apply (hnear s T F hs hT hTT zX np a b I w ha hb hI hJI hw0).trans
    apply ENNReal.ofReal_le_ofReal
    have hh := mul_le_mul_of_nonneg_left
      (magnetic_low_coefficient hP (sourceRepresentative_one_le _) hn hw hwP)
      (by positivity : 0≤Cn*I*Real.sqrt I)
    have hsqrt : Real.sqrt I≤1 := (Real.sqrt_le_one).mpr hI1
    calc
      _=(Cn*I*Real.sqrt I)*((sourceRepresentative np)^2*(512/min (sourceRepresentative np) w)^3) := by ring
      _≤(Cn*I*Real.sqrt I)*(512^3*P^2/w) := hh
      _≤(Cn*I*1)*(512^3*P^2/w) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsqrt (by positivity)) (by positivity)
      _=D := by dsimp [D]; ring
  have hdom : (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
      if cappedRepresentative nt≤cappedRepresentative n.2/16 then
        representativeLowShortMagneticCost s F zX I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ∑'np : ℕ,if sourceRepresentative np≤P then g np else 0 := by
    rw [ENNReal.tsum_prod']
    apply ENNReal.tsum_le_tsum
    intro np
    split_ifs with hn
    · apply ENNReal.tsum_le_tsum
      intro nf
      exact (indicator_le_self _ _) (np,nf)
    · have hz (nf : ℕ) : (np,nf)∉Q := fun hh=>hn hh.1
      simp only [indicator_of_notMem (hz _),tsum_zero,le_refl]
  apply hdom.trans
  obtain ⟨N,hN,hidx⟩ := exists_small_pair_count hP hL
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun np=>sourceRepresentative np≤P)
  have hU (np) (hn : np∈U) : sourceRepresentative np≤P := (Finset.mem_filter.mp hn).2
  have hsub : U⊆Finset.range N := by
    intro np hn
    have hpn : 1/sourceRepresentative np≤cappedRepresentative 0 := by
      rw [show cappedRepresentative 0=1 by rfl]
      exact (div_le_one (zero_lt_one.trans_le (sourceRepresentative_one_le _))).mpr (sourceRepresentative_one_le _)
    exact Finset.mem_range.mpr (hidx np 0 (hU np hn) hpn).1
  have hcard : (U.card:ℝ)≤pairCountConstant*Real.log (2+P) := by
    have hh : (U.card:ℝ)≤N := by exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range N)
    exact hh.trans hN
  have he : (∑np∈S,if sourceRepresentative np≤P then g np else 0)=∑np∈U,g np := by
    simp [U,Finset.sum_filter]
  rw [he]
  calc
    _≤∑np∈U,ENNReal.ofReal D := Finset.sum_le_sum (fun np hn=>hgb np (hU np hn))
    _=ENNReal.ofReal ((U.card:ℝ)*D) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _=>hD)]
      simp
    _≤ENNReal.ofReal ((pairCountConstant*Real.log (2+P))*D) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hD)
    _=_ := by congr 1; dsimp [D]; ring

lemma Admissible.magnetic_small_short_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,1≤M → 0≤A → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → I≤1 → b-a≤I → 1≤w → w≤P →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative nt≤cappedRepresentative n.2/16 then
          (if cappedRepresentative nr≤I then representativeMagneticCost s F zX w ![n.1,nt,n.2,nr] a b else 0) else 0) n)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  classical
  obtain ⟨Cr,hCr,hregular⟩ := hd.magnetic_regular_short_uniform T₀
  obtain ⟨Ce,hCe,hexception⟩ := hd.magnetic_low_uniform T₀
  refine ⟨Cr+Ce,add_nonneg hCr hCe,?_⟩
  intro M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hI1 hJI hw hwP HZ
  dsimp only
  let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
    1/sourceRepresentative n.1≤cappedRepresentative n.2}
  let Gr := fun n : ℕ×ℕ=>∑'nt : ℕ,∑'nr : ℕ,
    if cappedRepresentative nt≤cappedRepresentative n.2/16 then
      representativeRegularShortMagneticCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0
  let Ge := fun n : ℕ×ℕ=>∑'nt : ℕ,∑'nr : ℕ,
    if cappedRepresentative nt≤cappedRepresentative n.2/16 then
      representativeLowShortMagneticCost s F zX I w ![n.1,nt,n.2,nr] a b else 0
  have he (n : ℕ×ℕ) : Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
      if cappedRepresentative nt≤cappedRepresentative n.2/16 then
        (if cappedRepresentative nr≤I then representativeMagneticCost s F zX w ![n.1,nt,n.2,nr] a b else 0) else 0) n≤
      Q.indicator Gr n+Q.indicator Ge n := by
    by_cases hn : n∈Q
    · simp only [indicator_of_mem hn,Gr,Ge]
      rw [←ENNReal.tsum_add]
      apply ENNReal.tsum_le_tsum
      intro nt
      rw [←ENNReal.tsum_add]
      apply ENNReal.tsum_le_tsum
      intro nr
      by_cases ht : cappedRepresentative nt≤cappedRepresentative n.2/16
      · simp only [ite_eq_left ht]
        by_cases hr : cappedRepresentative nr≤I
        · rw [ite_eq_left hr]
          by_cases hreg : regularCentralIndex P M A I w ![n.1,nt,n.2,nr]
          · have he : representativeRegularShortMagneticCost s F zX P M A I w ![n.1,nt,n.2,nr] a b=
                representativeMagneticCost s F zX w ![n.1,nt,n.2,nr] a b := by
              exact ite_eq_left ⟨hreg,hr⟩
            rw [he]
            exact le_add_right le_rfl
          · have hlow : cappedRepresentative n.2≤512/min (sourceRepresentative n.1) w := by
              have hh : ¬(512/min (sourceRepresentative n.1) w<cappedRepresentative n.2 ∨
                min I (stabilityLength P 16384 M A (sourceRepresentative n.1) w (cappedRepresentative n.2))<cappedRepresentative nr) := hreg
              exact le_of_not_gt (not_or.mp hh).1
            have he : representativeLowShortMagneticCost s F zX I w ![n.1,nt,n.2,nr] a b=
                representativeMagneticCost s F zX w ![n.1,nt,n.2,nr] a b := by
              exact ite_eq_left ⟨hlow,hr⟩
            rw [he]
            exact le_add_left le_rfl
        · rw [ite_eq_right hr]
          exact bot_le
      · simp only [ite_eq_right ht,zero_add,le_refl]
    · simp only [indicator_of_notMem hn,zero_add,le_refl]
  change (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
    if cappedRepresentative nt≤cappedRepresentative n.2/16 then
      (if cappedRepresentative nr≤I then representativeMagneticCost s F zX w ![n.1,nt,n.2,nr] a b else 0) else 0) n)≤_
  apply (ENNReal.tsum_le_tsum he).trans
  rw [ENNReal.tsum_add]
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  let V := I*P^2*Real.log (2+P)/w
  have hV : 0≤V := by dsimp [V]; positivity
  have hB : 0≤B := by dsimp [B]; positivity
  have hVB : V≤B := by
    have hroot := Real.sqrt_nonneg A
    have hfirst : 0≤P*Real.sqrt I := by positivity
    have ht : V≤(M+Real.sqrt A)*V := le_mul_of_one_le_left hV (by linarith)
    calc
      V≤(M+Real.sqrt A)*V := ht
      _≤P*Real.sqrt I+(M+Real.sqrt A)*V := le_add_of_nonneg_left hfirst
      _=B := by dsimp [B,V]; ring
  have hr := hregular M A P (zero_lt_one.trans_le hM) hA hP hL s T F hs hT hTT
    zX a b I w hzX ha hb hI hI1 hJI (zero_lt_one.trans_le hw) hwP HZ
  have he' := hexception P hP hL s T F hs hT hTT zX a b I w ha hb hI hI1 hJI hw hwP
  calc
    _≤ENNReal.ofReal (Cr*B)+ENNReal.ofReal (Ce*V) := add_le_add hr he'
    _≤ENNReal.ofReal (Cr*B)+ENNReal.ofReal (Ce*B) :=
      add_le_add le_rfl (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hVB hCe))
    _=ENNReal.ofReal ((Cr+Ce)*B) := by rw [←ENNReal.ofReal_add (mul_nonneg hCr hB) (mul_nonneg hCe hB)]; congr 1; ring

lemma Admissible.representative_magnetic_large_Cauchy {d : Datum} (hd : Admissible d) :
    ∃ C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → ∀(zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I → I ≤ max 1 T*cappedRepresentative (k 3) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let h := cappedRepresentative (k 3)
      let H := max 1 T
      let E := datumEnergyNumber d
      let D := ENNReal.ofReal (128*C*p^3*θ^2)
      representativeMagneticCost s F zX w k a b ≤
        ENNReal.ofReal (10240/p)*((ENNReal.ofReal (120*(H*h)*E))^(1/2:ℝ)*
          (min (D^2*ENNReal.ofReal (576*I*(H*h)*φ^2))
            (D*ENNReal.ofReal (491520*I*E/((H*h)^2*θ^2))))^(1/2:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := hd.uniform_actual_magnetic_Cauchy
  refine ⟨C,hC,?_⟩
  intro s T F hs hT zX k a b I w ha hb hI hab hIr
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let r := max 1 T*cappedRepresentative (k 3)
  let B := representativeClosedBin T w k
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hr : 0<r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hBmax : B.rmax=2*r := by dsimp [B,representativeClosedBin,r]; ring
  have hBmin : B.rmin=r/2 := rfl
  let E := datumEnergyNumber d
  have hE : 0≤E := hd.datumEnergyNumber_nonneg
  have hBDmin : B.Dmin=φ^2/2 := rfl
  have hC : Icc (max 0 (a-B.rmax)) (min T (b-B.rmin))⊆Icc 0 T :=
    Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have hR : 0<B.rmin := by rw [hBmin]; positivity
  let O := coneOccupation F.flow zX T s.f
    (closedBinEulerian F.flow zX T B (tsupport d.f₀) a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))/
      ENNReal.ofReal (B.rmin^2*B.Dmin)
  have hbO : O≤ENNReal.ofReal (491520*I*E/(r^2*θ^2)) := by
    have ho := F.closedEulerian_angular_time_budget hs.energyPrefix hT zX B hd.2.1 hJ hC hR hθ hφ hI.le hab
      le_rfl (by change 0<8*φ^2; positivity) le_rfl
    rw [hs.initial_energy_eq] at ho
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
      linarith only [hab,hb',ha',hr]
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.energyPrefix.magneticFieldBudget_uniform F.flow zX 1 hsub hI (by positivity : 0≤1+2*r/I) hh)
    rw [hs.initial_energy_eq] at hh
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
  have hangle (D : ℝ) (hD : D∈Icc B.Dmin B.Dmax) : DyadicWindow 1 (k 2) (Real.sqrt (D/2)) :=
    dyadicWindow_one_sqrt (k 2)
      (by simpa only [B,representativeClosedBin,cappedRepresentative,inv_pow] using hD.1)
      (by simpa only [B,representativeClosedBin,cappedRepresentative,inv_pow] using hD.2)
  have hS0 : tsupport (fun z=>s.f (0,z))⊆tsupport d.f₀ := by
    have he : (fun z=>s.f (0,z))=d.f₀ := funext hs.initial_f
    rw [he]
  have hbnd := hbound s T F hs.energyPrefix hT hs.initial_f zX B (tsupport d.f₀)
    a b I p θ φ 1 1 (k 2) hd.2.1 hS0 hJ hI hp hθ.le hφ.le (by norm_num)
    (by change 0<r/2; positivity) (by change 0<φ^2/2; positivity) le_rfl
    (by change p/32≤p; linarith) le_rfl le_rfl (by norm_num [B,representativeClosedBin]) hangle
  dsimp only at hbnd
  have hθ1 : θ≤1 := cappedRepresentative_le_one (k 1)
  simp only [min_eq_left hθ1] at hbnd
  have hden : B.rmin^2*B.Dmin=r^2*φ^2/8 := by change (r/2)^2*(φ^2/2)=_; ring
  rw [hden] at hbnd
  have heq : representativeMagneticCost s F zX w k a b=
      ENNReal.ofReal (1/p)*(∫⁻z : ConeCoordinate,ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal φ*
        ENNReal.ofReal (prefixConeMagnetic s T X z)*physicalBinDensity s X V B z.1 z.2.1 z.2.2
          ∂physicalBinMeasure V B (Icc a b)) := by
    unfold representativeMagneticCost
    dsimp only
    rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro z
    change ENNReal.ofReal (φ/p) * (ENNReal.ofReal (z.1-z.2.1) *
      ENNReal.ofReal (prefixConeMagnetic s T X z) * physicalBinDensity s X V B z.1 z.2.1 z.2.2) = _
    simp only [ENNReal.ofReal_div_of_pos hp,ENNReal.ofReal_one]
    simp only [div_eq_mul_inv]
    ring
  rw [heq]
  apply mul_le_mul'
  · apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_right (by norm_num) hp.le
  · apply hbnd.trans
    apply mul_le_mul' (ENNReal.rpow_le_rpow (hmag.trans hmag') (by norm_num))
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    apply min_le_min (mul_le_mul' le_rfl hvolume)
    apply mul_le_mul' le_rfl
    simpa only [O,hden] using hbO

lemma Admissible.representative_magnetic_large {d : Datum} (hd : Admissible d) :
    ∃ C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → ∀(zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I → I ≤ max 1 T*cappedRepresentative (k 3) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let r := max 1 T*cappedRepresentative (k 3)
      representativeMagneticCost s F zX w k a b ≤
        ENNReal.ofReal (C*Real.sqrt I*min (r*p^2*θ^2*φ) (Real.sqrt p/Real.sqrt r)) := by
  obtain ⟨Cb,hCb,hmag⟩ := hd.representative_magnetic_large_Cauchy
  let E := datumEnergyNumber d
  have hE : 0≤E := hd.datumEnergyNumber_nonneg
  refine ⟨majorant_relativeCauchyConstant Cb E (120*E),majorant_relativeCauchyConstant_nonneg hCb,?_⟩
  intro s T F hs hT zX k a b I w ha hb hI hab hIr
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let r := max 1 T*cappedRepresentative (k 3)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hr : 0<r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hh := majorant_relative_large_magnetic_cauchy_scalar hCb hE (show 0≤120*E by positivity)
    hI hp hθ.le hr hφ.le hθ
  dsimp only at hh
  have he : Real.sqrt p*θ/(θ*Real.sqrt r)=Real.sqrt p/Real.sqrt r := by field_simp [hθ.ne']
  rw [he,show (120*E)*r=120*r*E by ring] at hh
  exact (hmag s T F hs hT zX k a b I w ha hb hI hab hIr).trans hh

noncomputable def representativeLargeMagneticCost (s : Solution) {T : ℝ} (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (I w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ := by
  classical
  exact if I < cappedRepresentative (k 3) then representativeMagneticCost s F zX w k a b else 0

lemma capped_large_magnetic_weighted_sum {H p θ φ K : ℝ}
    (hH : 0<H) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ) (hK : 0≤K) :
    (∑'n : ℕ, ENNReal.ofReal (K*min
      (H*cappedRepresentative n*p^2*θ^2*φ)
      (Real.sqrt p/Real.sqrt (H*cappedRepresentative n)))) ≤
      ENNReal.ofReal (K*dyadicBalanceConstant 1 (1/2)*p*θ^(2/3:ℝ)*φ^(1/3:ℝ)) := by
  let g : ℤ→ℝ := fun k=>min (H*(2:ℝ)^k*p^2*θ^2*φ) (Real.sqrt p/Real.sqrt (H*(2:ℝ)^k))
  have hg0 (k : ℤ) : 0≤g k := by dsimp [g]; positivity
  have hg := large_radius_magnetic_balance hH hp hθ hφ hθ
  simp only [min_self] at hg
  have heq (k : ℤ) : Real.sqrt p*θ/(θ*Real.sqrt (H*(2:ℝ)^k))=Real.sqrt p/Real.sqrt (H*(2:ℝ)^k) := by
    field_simp [hθ.ne']
  simp_rw [heq] at hg
  have he (n : ℕ) : cappedRepresentative n=(2:ℝ)^(-(n:ℤ)) := by
    simp only [cappedRepresentative,zpow_neg,zpow_natCast,inv_pow]
  have hinj : Function.Injective (fun n : ℕ=>-(n:ℤ)) := by
    intro a b hab
    exact_mod_cast neg_injective hab
  have hθeq : θ^(4/3:ℝ)*θ^(-(2/3:ℝ))=θ^(2/3:ℝ) := by
    rw [←Real.rpow_add hθ]
    congr 1
    norm_num
  calc
    _ = ∑'n : ℕ,ENNReal.ofReal (K*g (-(n:ℤ))) := by simp only [g,he]
    _ ≤ ∑'k : ℤ,ENNReal.ofReal (K*g k) :=
      ENNReal.tsum_comp_le_tsum_of_injective hinj (fun k=>ENNReal.ofReal (K*g k))
    _ = ENNReal.ofReal (K*∑'k : ℤ,g k) := by
      rw [←ENNReal.ofReal_tsum_of_nonneg (fun k=>mul_nonneg hK (hg0 k)) (hg.1.mul_left K),tsum_mul_left]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_left hg.2 hK
      calc
        _ ≤ K*(dyadicBalanceConstant 1 (1/2)*(p*θ^(4/3:ℝ)*θ^(-(2/3:ℝ))*φ^(1/3:ℝ))) := hh
        _ = (K*dyadicBalanceConstant 1 (1/2)*p)*(θ^(4/3:ℝ)*θ^(-(2/3:ℝ)))*φ^(1/3:ℝ) := by ring
        _ = _ := by rw [hθeq]

lemma capped_rpow_ennreal_sum {α : ℝ} (hα : 0<α) :
    (∑'n : ℕ, ENNReal.ofReal ((cappedRepresentative n)^α))≤
      ENNReal.ofReal ((1-((2:ℝ)⁻¹)^α)⁻¹) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  rw [←ENNReal.ofReal_sum_of_nonneg (fun n _=>Real.rpow_nonneg (cappedRepresentative_pos n).le _)]
  apply ENNReal.ofReal_le_ofReal
  simpa using capped_positive_power_sum_unscaled (by norm_num : (0:ℝ)<1) hα S
    (fun n _=>cappedRepresentative_le_one n)

lemma capped_rpow_sum_constant_pos {α : ℝ} (hα : 0<α) : 0<(1-((2:ℝ)⁻¹)^α)⁻¹ := by
  apply inv_pos.mpr
  exact sub_pos.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) hα)

lemma large_magnetic_triple_sum {H p K : ℝ} (hH : 0<H) (hp : 0<p) (hK : 0≤K) :
    (∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,ENNReal.ofReal (K*min
      (H*cappedRepresentative nr*p^2*(cappedRepresentative nt)^2*cappedRepresentative nf)
      (Real.sqrt p/Real.sqrt (H*cappedRepresentative nr))))≤
      ENNReal.ofReal (K*dyadicBalanceConstant 1 (1/2)*p*
        (1-((2:ℝ)⁻¹)^(2/3:ℝ))⁻¹*(1-((2:ℝ)⁻¹)^(1/3:ℝ))⁻¹) := by
  let D := dyadicBalanceConstant 1 (1/2)
  have hD : 0≤D := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  let A := (1-((2:ℝ)⁻¹)^(2/3:ℝ))⁻¹
  let B := (1-((2:ℝ)⁻¹)^(1/3:ℝ))⁻¹
  have hA : 0<A := capped_rpow_sum_constant_pos (by norm_num)
  have hB : 0<B := capped_rpow_sum_constant_pos (by norm_num)
  calc
    _≤∑'nf : ℕ,∑'nt : ℕ,ENNReal.ofReal (K*D*p*(cappedRepresentative nt)^(2/3:ℝ)*(cappedRepresentative nf)^(1/3:ℝ)) :=
      ENNReal.tsum_le_tsum (fun nf=>ENNReal.tsum_le_tsum (fun nt=>
        capped_large_magnetic_weighted_sum hH hp (cappedRepresentative_pos _) (cappedRepresentative_pos _) hK))
    _=ENNReal.ofReal (K*D*p)*(∑'nt : ℕ,ENNReal.ofReal ((cappedRepresentative nt)^(2/3:ℝ)))*
        (∑'nf : ℕ,ENNReal.ofReal ((cappedRepresentative nf)^(1/3:ℝ))) := by
      have he (nf nt : ℕ) : ENNReal.ofReal (K*D*p*(cappedRepresentative nt)^(2/3:ℝ)*(cappedRepresentative nf)^(1/3:ℝ))=
          ENNReal.ofReal (K*D*p)*ENNReal.ofReal ((cappedRepresentative nt)^(2/3:ℝ))*ENNReal.ofReal ((cappedRepresentative nf)^(1/3:ℝ)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (by positivity : 0≤K*D*p)
          (Real.rpow_nonneg (cappedRepresentative_pos nt).le _)),ENNReal.ofReal_mul (by positivity : 0≤K*D*p)]
      simp only [he,ENNReal.tsum_mul_right,ENNReal.tsum_mul_left]
    _≤ENNReal.ofReal (K*D*p)*ENNReal.ofReal A*ENNReal.ofReal B := mul_le_mul'
      (mul_le_mul' le_rfl (capped_rpow_ennreal_sum (by norm_num)))
      (capped_rpow_ennreal_sum (by norm_num))
    _=_ := by rw [←ENNReal.ofReal_mul (by positivity : 0≤K*D*p),
        ←ENNReal.ofReal_mul (by positivity : 0≤K*D*p*A)]

lemma Admissible.representative_large_magnetic_triple_sum {d : Datum} (hd : Admissible d) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T →
    ∀ (zX : Phase) (np : ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I →
      (∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
          representativeLargeMagneticCost s F zX I w ![np,nt,nf,nr] a b)≤
        ENNReal.ofReal (C*Real.sqrt I*sourceRepresentative np) := by
  classical
  obtain ⟨Cb,hCb,hlarge⟩ := hd.representative_magnetic_large
  let D := dyadicBalanceConstant 1 (1/2)
  let A := (1-((2:ℝ)⁻¹)^(2/3:ℝ))⁻¹
  let B := (1-((2:ℝ)⁻¹)^(1/3:ℝ))⁻¹
  have hD : 0≤D := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hA : 0<A := capped_rpow_sum_constant_pos (by norm_num)
  have hB : 0<B := capped_rpow_sum_constant_pos (by norm_num)
  refine ⟨Cb*D*A*B,by positivity,?_⟩
  intro s T F hs hT zX np a b I w ha hb hI hJI
  let p := sourceRepresentative np
  let H := max 1 T
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hH : 0<H := zero_lt_one.trans_le (le_max_left _ _)
  have hpoint (nf nt nr : ℕ) :
      representativeLargeMagneticCost s F zX I w ![np,nt,nf,nr] a b≤
      ENNReal.ofReal ((Cb*Real.sqrt I)*min
        (H*cappedRepresentative nr*p^2*(cappedRepresentative nt)^2*cappedRepresentative nf)
        (Real.sqrt p/Real.sqrt (H*cappedRepresentative nr))) := by
    by_cases hr : I<cappedRepresentative nr
    · have hIr : I ≤ max 1 T*cappedRepresentative nr := hr.le.trans
        (le_mul_of_one_le_left (cappedRepresentative_pos nr).le (le_max_left _ _))
      change (if I<cappedRepresentative nr then _ else 0)≤_
      rw [ite_eq_left hr]
      exact hlarge s T F hs hT zX ![np,nt,nf,nr] a b I w ha hb hI hJI hIr
    · change (if I<cappedRepresentative nr then _ else 0)≤_
      rw [ite_eq_right hr]
      exact bot_le
  apply (ENNReal.tsum_le_tsum (fun nf=>ENNReal.tsum_le_tsum (fun nt=>ENNReal.tsum_le_tsum (hpoint nf nt)))).trans
  apply (large_magnetic_triple_sum hH hp (mul_nonneg hCb (Real.sqrt_nonneg I))).trans
  apply le_of_eq
  congr 1
  dsimp only [p,D,A,B]
  ring

lemma Admissible.magnetic_large_uniform {d : Datum} (hd : Admissible d) :
    ∃ C : ℝ,0≤C ∧ ∀ P : ℝ,0≤P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T →
    ∀ (zX : Phase) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative nt≤cappedRepresentative n.2/16 then
          representativeLargeMagneticCost s F zX I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*(P*Real.sqrt I)) := by
  classical
  obtain ⟨Cn,hCn,hlarge⟩ := hd.representative_large_magnetic_triple_sum
  refine ⟨2*Cn,by positivity,?_⟩
  intro P hP s T F hs hT zX a b I w ha hb hI hJI
  dsimp only
  let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
    1/sourceRepresentative n.1≤cappedRepresentative n.2}
  let g := fun np=>∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
    representativeLargeMagneticCost s F zX I w ![np,nt,nf,nr] a b
  have hdom : (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
      if cappedRepresentative nt≤cappedRepresentative n.2/16 then
        representativeLargeMagneticCost s F zX I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ∑'np : ℕ,if sourceRepresentative np≤P then g np else 0 := by
    rw [ENNReal.tsum_prod']
    apply ENNReal.tsum_le_tsum
    intro np
    split_ifs with hn
    · apply ENNReal.tsum_le_tsum
      intro nf
      apply (indicator_le_self _ _ (np,nf)).trans
      apply ENNReal.tsum_le_tsum
      intro nt
      apply ENNReal.tsum_le_tsum
      intro nr
      split_ifs
      · rfl
      · exact bot_le
    · have hz (nf : ℕ) : (np,nf)∉Q := fun hh=>hn hh.1
      simp only [indicator_of_notMem (hz _),tsum_zero,le_refl]
  apply hdom.trans
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun np=>sourceRepresentative np≤P)
  have hU (np) (hn : np∈U) : sourceRepresentative np≤P := (Finset.mem_filter.mp hn).2
  have he : (∑np∈S,if sourceRepresentative np≤P then g np else 0)=∑np∈U,g np := by
    simp [U,Finset.sum_filter]
  rw [he]
  calc
    _≤∑np∈U,ENNReal.ofReal (Cn*Real.sqrt I*sourceRepresentative np) := Finset.sum_le_sum
      (fun np _=>hlarge s T F hs hT zX np a b I w ha hb hI hJI)
    _=ENNReal.ofReal (Cn*Real.sqrt I*(∑np∈U,sourceRepresentative np)) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun np _=>by
        exact mul_nonneg (mul_nonneg hCn (Real.sqrt_nonneg I)) (by dsimp [sourceRepresentative]; positivity))]
      congr 1
      rw [Finset.mul_sum]
    _≤ENNReal.ofReal (Cn*Real.sqrt I*(2*P)) := ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (sourceRepresentative_sum_bound hP U hU) (by positivity))
    _=_ := by congr 1; ring

lemma Admissible.magnetic_small_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,1≤M → 0≤A → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → I≤1 → b-a≤I → 1≤w → w≤P →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative nt≤cappedRepresentative n.2/16 then
          representativeMagneticCost s F zX w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  classical
  obtain ⟨Cr,hCr,hregular⟩ := hd.magnetic_small_short_uniform T₀
  obtain ⟨Ce,hCe,hexception⟩ := hd.magnetic_large_uniform
  refine ⟨Cr+Ce,add_nonneg hCr hCe,?_⟩
  intro M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hI1 hJI hw hwP HZ
  dsimp only
  let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
    1/sourceRepresentative n.1≤cappedRepresentative n.2}
  let Gr := fun n : ℕ×ℕ=>∑'nt : ℕ,∑'nr : ℕ,
    if cappedRepresentative nt≤cappedRepresentative n.2/16 then
      (if cappedRepresentative nr≤I then representativeMagneticCost s F zX w ![n.1,nt,n.2,nr] a b else 0) else 0
  let Ge := fun n : ℕ×ℕ=>∑'nt : ℕ,∑'nr : ℕ,
    if cappedRepresentative nt≤cappedRepresentative n.2/16 then
      representativeLargeMagneticCost s F zX I w ![n.1,nt,n.2,nr] a b else 0
  have he (n : ℕ×ℕ) : Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
      if cappedRepresentative nt≤cappedRepresentative n.2/16 then
        representativeMagneticCost s F zX w ![n.1,nt,n.2,nr] a b else 0) n=
      Q.indicator Gr n+Q.indicator Ge n := by
    by_cases hn : n∈Q
    · simp only [indicator_of_mem hn,Gr,Ge]
      rw [←ENNReal.tsum_add]
      apply tsum_congr
      intro nt
      rw [←ENNReal.tsum_add]
      apply tsum_congr
      intro nr
      by_cases ht : cappedRepresentative nt≤cappedRepresentative n.2/16
      · simp only [ite_eq_left ht]
        change representativeMagneticCost _ _ _ _ _ _ _=
          (if cappedRepresentative nr≤I then _ else 0)+
          (if I<cappedRepresentative nr then _ else 0)
        by_cases hr : cappedRepresentative nr≤I
        · rw [ite_eq_left hr,ite_eq_right (not_lt.mpr hr),add_zero]
        · rw [ite_eq_right hr,ite_eq_left (lt_of_not_ge hr),zero_add]
      · simp only [ite_eq_right ht,zero_add]
    · simp only [indicator_of_notMem hn,zero_add]
  change (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
    if cappedRepresentative nt≤cappedRepresentative n.2/16 then
      representativeMagneticCost s F zX w ![n.1,nt,n.2,nr] a b else 0) n)≤_
  simp_rw [he]
  rw [ENNReal.tsum_add]
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  let V := P*Real.sqrt I
  have hV : 0≤V := by dsimp [V]; positivity
  have hB : 0≤B := by dsimp [B]; positivity
  have hVB : V≤B := le_add_of_nonneg_right (by positivity)
  have hr := hregular M A P hM hA hP hL s T F hs hT hTT
    zX a b I w hzX ha hb hI hI1 hJI hw hwP HZ
  have he' := hexception P (zero_le_one.trans hP) s T F hs hT zX a b I w ha hb hI hJI
  calc
    _≤ENNReal.ofReal (Cr*B)+ENNReal.ofReal (Ce*V) := add_le_add hr he'
    _≤ENNReal.ofReal (Cr*B)+ENNReal.ofReal (Ce*B) :=
      add_le_add le_rfl (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hVB hCe))
    _=ENNReal.ofReal ((Cr+Ce)*B) := by rw [←ENNReal.ofReal_add (mul_nonneg hCr hB) (mul_nonneg hCe hB)]; congr 1; ring

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.bulkSource_cost_sum {s : Solution} {T P M A w I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    {a b : ℝ} (ha : 0≤a) (hb : b≤T)
    (hband : ∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P)
    {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) (hW1 : ∀t∈Icc a b,‖W t‖≤1)
    {C : ℝ} (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C) :
    (∫⁻p,ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T (bulkSelection P M A w I)
      (coneSourceCutoffTangent s F.flow zX) W (Icc a b) p‖ ∂trianglePhaseMeasure)≤
      ENNReal.ofReal (99840000*C)*(∑'k : Fin 4→ℕ,(bulkSourceBoundary P M A w I).indicator
        (fun k=>representativeGoodCost s F zX w k a b+representativeMagneticCost s F zX w k a b) k) := by
  let Q := bulkSelection P M A w I
  let R := bulkSourceBoundary P M A w I
  let g := fun p=>ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q
    (coneSourceCutoffTangent s F.flow zX) W (Icc a b) p‖
  have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
  have hg : Measurable g :=
    (F.partialCutoffTriangle_measurable hs zX Q (F.coneSourceCutoffTangent_continuousOn hs zX) hW measurableSet_Icc).norm.ennreal_ofReal
  have hc : ∀p,g p≠0→∃k∈R,p∈physicalBinPhaseSet
      (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) (Icc a b) := by
    intro p hp
    have hpn : partialCutoffTriangle s F.flow zX T Q (coneSourceCutoffTangent s F.flow zX) W (Icc a b) p≠0 := by
      intro h; apply hp; simp only [g,h,norm_zero,ENNReal.ofReal_zero]
    obtain ⟨k,hk,hr,hpk⟩ := F.bulkCutoffTriangle_small_support zX _ W (Icc_subset_Icc ha hb) hband hP hpn
    exact ⟨k,⟨hk,hr⟩,hpk⟩
  apply (physicalBinPhase_cover_lintegral hV measurableSet_Icc T w R hg hc).trans
  rw [←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : k∈R
  · rw [indicator_of_mem hk,indicator_of_mem hk]
    exact F.bulkSource_bin_integral hs hT zX Q ha hb W hW1 hC0 hC k hk.1.2.2
  · rw [indicator_of_notMem hk,indicator_of_notMem hk,mul_zero]

lemma Admissible.bulk_source_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,1≤M → 0<A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I → 1≤w → w≤P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ W : ℝ→Vec→L[ℝ]Vec,Measurable W → (∀t∈Icc a b,‖W t‖≤1) →
      (∫⁻p,ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T (bulkSelection P M A w I)
        (coneSourceCutoffTangent s F.flow zX) W (Icc a b) p‖ ∂trianglePhaseMeasure)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cs,hCs,hgood⟩ := hd.bulk_source_good_uniform T₀
  obtain ⟨Cm,hCm,hmag⟩ := hd.magnetic_small_uniform T₀
  obtain ⟨Cd,hCd,hder⟩ := dyadicFactor_log_derivative_bound
  refine ⟨99840000*Cd*(Cs+Cm),by positivity,?_⟩
  intro M A hM hA
  filter_upwards [hgood M A hM hA] with P hg
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hsource hphysical hband HZ W hW hW1
  let R := bulkSourceBoundary P M A w I
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  have hB : 0≤B := by dsimp [B]; positivity
  have hmg : (∑'k : Fin 4→ℕ,R.indicator (fun k=>representativeMagneticCost s F zX w k a b) k)≤
      ENNReal.ofReal (Cm*B) := by
    calc
      _≤∑'k : Fin 4→ℕ,(centralIndexSector P).indicator (fun k=>representativeMagneticCost s F zX w k a b) k := by
        apply ENNReal.tsum_le_tsum
        intro k
        by_cases hk : k∈R
        · rw [indicator_of_mem hk,indicator_of_mem (representativeSmallSector_subset_centralIndexSector P hk.1)]
        · rw [indicator_of_notMem hk]; exact bot_le
      _≤_ := by
        rw [tsum_centralIndexSector]
        exact hmag M A P hM hA.le hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hI1 hJI hw hwP HZ
  have hgd := hg hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hsource HZ
  have hsum : (∑'k : Fin 4→ℕ,R.indicator
      (fun k=>representativeGoodCost s F zX w k a b+representativeMagneticCost s F zX w k a b) k)≤
      ENNReal.ofReal ((Cs+Cm)*B) := by
    rw [show R.indicator (fun k=>representativeGoodCost s F zX w k a b+representativeMagneticCost s F zX w k a b)=
      (fun k=>R.indicator (fun k=>representativeGoodCost s F zX w k a b) k+
        R.indicator (fun k=>representativeMagneticCost s F zX w k a b) k) by
          funext k; simp only [indicator_add],ENNReal.tsum_add]
    apply (add_le_add hgd hmg).trans_eq
    rw [←ENNReal.ofReal_add (mul_nonneg hCs hB) (mul_nonneg hCm hB)]
    congr 1; ring
  apply (F.bulkSource_cost_sum hs.energyPrefix hT zX ha hb hband hphysical hW hW1 hCd hder).trans
  apply (mul_le_mul' le_rfl hsum).trans_eq
  rw [←ENNReal.ofReal_mul (by positivity : 0≤99840000*Cd)]
  congr 1; ring

end RVM

end

end OAI
