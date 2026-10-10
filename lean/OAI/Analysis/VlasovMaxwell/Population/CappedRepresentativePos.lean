import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.PhysicalDirectTransportDensity

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma cappedRepresentative_pos (n : ℕ) : 0 < cappedRepresentative n := by
  dsimp [cappedRepresentative]
  positivity

lemma cappedRepresentative_le_one (n : ℕ) : cappedRepresentative n ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

lemma Admissible.geometry_cutoff_baseline_bin {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (k : Fin 4→ℕ)
        (a b I len w M A P L massScale Cs : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → 0 < len → len ≤ I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
      massScale ≤ sourceRepresentative (k 0)/128 → massScale ≤ w/8 →
      cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 →
      32 ≤ cappedRepresentative (k 2)*w →
      2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative (k 2)+
        Real.sqrt (A*L/cappedRepresentative (k 2))))⁻¹^2 →
      (∀t∈Icc a b,w/16 ≤ ‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let r := max 1 T*cappedRepresentative (k 3)
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := representativeClosedBin T w k
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∫⁻z : ConeCoordinate,physicalGeometryCutoffDensity s X V B T w Q z ∂physicalBinMeasure V B (Icc a b)) ≤
        ENNReal.ofReal (C*(1+E))*
          min (ENNReal.ofReal (I*p^3*θ*φ^4*r))
              (ENNReal.ofReal ((1+I/len)/(p*θ*r))) := by
  obtain ⟨Cρ,hCρ,hdensity⟩ := hd₀.uniform_physicalBinDensity_constant
  obtain ⟨c,hc,hcut⟩ := dyadicFactor_log_derivative_bound
  let C : ℝ := 10^18*c*(1+Cρ)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro s T F hs hT h0 zX S Q k a b I len w M A P L massScale Cs hS hS0 ha hb hlen hlenI hab
    hM hA hP hL hm hw hCs hmq hmw hsmall hwφ hstable hband HX HZ
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let r := max 1 T*cappedRepresentative (k 3)
  let B := representativeClosedBin T w k
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let E := ∫x : Vec,totalEnergy s (0,x)
  have hp : 0 < p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0 < θ := cappedRepresentative_pos _
  have hφ : 0 < φ := cappedRepresentative_pos _
  have hr : 0 < r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hBmax : B.rmax=2*r := by dsimp [B,representativeClosedBin,r]; ring
  have hBmin : B.rmin=r/2 := rfl
  have hBDmin : B.Dmin=φ^2/2 := rfl
  have hI : 0 < I := hlen.trans_le hlenI
  have hE : 0 ≤ E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hdsmall : B.dmax ≤ φ^2/32 := by
    change 8*θ^2 ≤ φ^2/32
    have hh : θ ≤ φ/16 := hsmall
    have hh2 := sq_le_sq₀ hθ.le (by positivity : 0 ≤ φ/16) |>.mpr hh
    nlinarith
  have hBD : B.dmax ≤ B.Dmin := by change 8*θ^2 ≤ φ^2/2; have hdc : 8*θ^2 ≤ φ^2/32 := hdsmall; nlinarith only [hdc,sq_nonneg φ]
  have hden : ∀z∈physicalBinBase V B (Icc a b),
      physicalBinDensity s X V B z.1 z.2.1 z.2.2 ≤ ENNReal.ofReal (128*Cρ*p^3*θ^2) := by
    intro z hz
    have hzT : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans (hJ hz.1).2⟩
    have hn := hdensity s T F hs h0 X V B z.1 z.2.1 z.2.2 p θ 1 hzT hp.le hθ.le (by norm_num)
      (by change p/32 ≤ p; linarith only [hp]) le_rfl (by norm_num [B,representativeClosedBin])
    simpa only [min_eq_left (show θ ≤ 1 from cappedRepresentative_le_one (k 1))] using hn
  have hnearfar := F.geometry_cutoff_near_far hs hT zX B hS hS0 hJ hc hcut hw hθ hφ.le hBD
    (by change 0 < r/2; positivity) (by change 0 < φ^2/2; positivity) le_rfl le_rfl hband Q hden
  have hbudget := F.closedEulerian_baseline_budget hs hT zX B hS (k 0) (k 2)
    (by rfl : p=64*(2:ℝ)^(k 0)) (by rfl : φ=(2:ℝ)⁻¹^(k 2)) ha hb hlen hlenI hab
    hM hA hP hL hm hφ (cappedRepresentative_le_one _) hCs hstable le_rfl le_rfl hmq hmw
    (by change 0 < r/2; positivity) (by rw [hBmax]; positivity) hdsmall le_rfl le_rfl
    (by change 4 ≤ φ*(w/8); have hh : 32 ≤ φ*w := hwφ; nlinarith only [hh]) HX HZ
  have hvol : volume (Icc a b) ≤ ENNReal.ofReal I := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal hab
  let near := I*p^3*θ*φ^4*r
  let far := (1+I/len)/(p*θ*r)
  have hn0 : 0 ≤ near := by dsimp only [near]; positivity
  have hf0 : 0 ≤ far := by dsimp only [far]; positivity
  have hn : ENNReal.ofReal (78400000*c*φ^2/θ)*ENNReal.ofReal (128*Cρ*p^3*θ^2)*
      (volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)) ≤
      ENNReal.ofReal (C*(1+E))*ENNReal.ofReal near := by
    calc
      _  ≤  ENNReal.ofReal (78400000*c*φ^2/θ)*ENNReal.ofReal (128*Cρ*p^3*θ^2)*
          (ENNReal.ofReal I*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)) := by gcongr
      _ = ENNReal.ofReal (5780275200000*c*Cρ*near) := by
        rw [hBmax,hBmin]
        rw [←ENNReal.ofReal_mul (by positivity : 0 ≤ I),
          ←ENNReal.ofReal_mul (mul_nonneg hI.le (by linarith : 0 ≤ 2*r-r/2)),
          ←ENNReal.ofReal_mul (by positivity : 0 ≤ 78400000*c*φ^2/θ),
          ←ENNReal.ofReal_mul (by positivity : 0 ≤ (78400000*c*φ^2/θ)*(128*Cρ*p^3*θ^2))]
        congr 1
        change (78400000*c*φ^2/θ)*(128*Cρ*p^3*θ^2)*(I*(2*r-r/2)*(384*φ^2))=_
        dsimp only [near]
        field_simp [hθ.ne',hp.ne',hr.ne',hφ.ne',hlen.ne']
        ring
      _  ≤  ENNReal.ofReal (C*(1+E)*near) := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ hn0
        dsimp [C]
        have ha : 5780275200000*c*Cρ ≤ 10^18*c*(1+Cρ) := by
          nlinarith only [hc,mul_nonneg hc hCρ]
        exact ha.trans (le_mul_of_one_le_right (by positivity) (by linarith only [hE]))
      _ = _ := ENNReal.ofReal_mul (by dsimp [C]; positivity)
  have hf : ENNReal.ofReal (78400000*c*φ^2/θ)*
      (coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) /
        ENNReal.ofReal (B.rmin^2*B.Dmin)) ≤
      ENNReal.ofReal (C*(1+E))*ENNReal.ofReal far := by
    calc
      _  ≤  ENNReal.ofReal (78400000*c*φ^2/θ)*
          ((ENNReal.ofReal (35512320*B.rmax/p*(1+I/len))*ENNReal.ofReal E)/
          ENNReal.ofReal (B.rmin^2*B.Dmin)) := by gcongr
      _ = ENNReal.ofReal (44546654208000000*c*E*far) := by
        rw [hBmax,hBmin,hBDmin]
        rw [←ENNReal.ofReal_mul (by positivity : 0 ≤ 35512320*(2*r)/p*(1+I/len)),
          ←ENNReal.ofReal_div_of_pos (by positivity : 0 < (r/2)^2*(φ^2/2)),
          ←ENNReal.ofReal_mul (by positivity : 0 ≤ 78400000*c*φ^2/θ)]
        congr 1
        dsimp only [far]
        field_simp [hθ.ne',hp.ne',hr.ne',hφ.ne',hlen.ne']
        ring
      _  ≤  ENNReal.ofReal (C*(1+E)*far) := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ hf0
        have hcC : 44546654208000000*c ≤ C := by
          dsimp [C]
          nlinarith only [hc,mul_nonneg hc hCρ]
        calc
          _  ≤  C*E := mul_le_mul_of_nonneg_right hcC hE
          _  ≤  C*(1+E) := by
            have hC : 0 ≤ C := by dsimp [C]; positivity
            exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)) hC
      _ = _ := ENNReal.ofReal_mul (by dsimp [C]; positivity)
  apply hnearfar.trans
  rw [mul_min]
  exact min_le_min hn hf

lemma geometry_radial_ennreal_sum {I len p θ φ H : ℝ}
    (hI : 0<I) (hlen : 0<len) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ) (hH : 0<H) :
    (∑'n : ℕ,min (ENNReal.ofReal (I*p^3*θ*φ^4*(H*cappedRepresentative n)))
      (ENNReal.ofReal ((1+I/len)/(p*θ*(H*cappedRepresentative n)))))≤
      ENNReal.ofReal (6*Real.sqrt I*Real.sqrt (1+I/len)*p*φ^2) := by
  let R := Real.sqrt (1+I/len)
  have hR : 0<R := Real.sqrt_pos.mpr (by positivity)
  have hRsq : R^2=1+I/len := Real.sq_sqrt (by positivity)
  let g : ℤ→ℝ := fun k=>min (I*p^3*θ*φ^4*(H*(2:ℝ)^k)) (R^2/(p*θ*(H*(2:ℝ)^k)))
  have hg0 (k : ℤ) : 0≤g k := by dsimp [g]; positivity
  have hg := geometry_radial_balance hI hR hp hθ hφ hH
  have he (n : ℕ) : cappedRepresentative n=(2:ℝ)^(-(n:ℤ)) := by
    simp only [cappedRepresentative,zpow_neg,zpow_natCast,inv_pow]
  have hinj : Function.Injective (fun n : ℕ=>-(n:ℤ)) := by
    intro a b hab
    exact_mod_cast neg_injective hab
  calc
    _ = ∑'n : ℕ,ENNReal.ofReal (g (-(n:ℤ))) := by
      apply tsum_congr
      intro n
      rw [he]
      simp only [g,hRsq,ENNReal.ofReal_min]
    _ ≤ ∑'k : ℤ,ENNReal.ofReal (g k) :=
      ENNReal.tsum_comp_le_tsum_of_injective hinj (fun k=>ENNReal.ofReal (g k))
    _ = ENNReal.ofReal (∑'k : ℤ,g k) := (ENNReal.ofReal_tsum_of_nonneg hg0 hg.1).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hg.2

lemma Admissible.geometry_cutoff_baseline_radial_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (np nθ nφ : ℕ)
        (a b I len w M A P L massScale Cs : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → 0 < len → len ≤ I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
      massScale ≤ sourceRepresentative np/128 → massScale ≤ w/8 →
      cappedRepresentative nθ ≤ cappedRepresentative nφ/16 →
      32 ≤ cappedRepresentative nφ*w →
      2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative nφ+
        Real.sqrt (A*L/cappedRepresentative nφ)))⁻¹^2 →
      (∀t∈Icc a b,w/16 ≤ ‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
      let p := sourceRepresentative np
      let φ := cappedRepresentative nφ
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>representativeClosedBin T w ![np,nθ,nφ,nr]
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalGeometryCutoffDensity s X V (B nr) T w Q z
        ∂physicalBinMeasure V (B nr) (Icc a b)) ≤
      ENNReal.ofReal (C*(1+E)*(6*Real.sqrt I*Real.sqrt (1+I/len)*p*φ^2)) := by
  obtain ⟨C,hC,hbound⟩ := hd₀.geometry_cutoff_baseline_bin
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX S Q np nθ nφ a b I len w M A P L massScale Cs hS hS0 ha hb hlen hlenI hab
    hM hA hP hL hm hw hCs hmq hmw hsmall hwφ hstable hband HX HZ
  dsimp only
  have hI : 0<I := hlen.trans_le hlenI
  have hE : 0≤ ∫x : Vec,totalEnergy s (0,x) := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hbnd (nr : ℕ) := hbound s T F hs hT h0 zX S Q ![np,nθ,nφ,nr]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three] at hbnd
  have hbnd' (nr : ℕ) := hbnd nr a b I len w M A P L massScale Cs hS hS0 ha hb hlen hlenI hab
    hM hA hP hL hm hw hCs hmq hmw hsmall hwφ hstable hband HX HZ
  have hs1 := ENNReal.tsum_le_tsum hbnd'
  rw [ENNReal.tsum_mul_left] at hs1
  apply hs1.trans
  rw [ENNReal.ofReal_mul (by positivity : 0≤C*(1+∫x : Vec,totalEnergy s (0,x)))]
  exact mul_le_mul' le_rfl (geometry_radial_ennreal_sum (I:=I) (len:=len)
    (p:=sourceRepresentative np) (θ:=cappedRepresentative nθ) (φ:=cappedRepresentative nφ)
    (H:=max 1 T) hI hlen
    (by dsimp [sourceRepresentative]; positivity) (cappedRepresentative_pos _)
    (cappedRepresentative_pos _) (zero_lt_one.trans_le (le_max_left _ _)))

lemma source_far_sqrt_mass {b p θ R r φ : ℝ}
    (hb : 0≤b) (hp : 0<p) (hθ : 0<θ) (hR : 0≤R) (hr : 0<r) (hφ : 0<φ) :
    Real.sqrt (b*p^2*θ^2*R^2/(r*φ^2)) =
      Real.sqrt b*p*θ*R/(Real.sqrt r*φ) := by
  rw [Real.sqrt_div (by positivity),Real.sqrt_mul (by positivity : 0≤b*p^2*θ^2),
    Real.sqrt_mul (by positivity : 0≤b*p^2),Real.sqrt_mul hb,
    Real.sqrt_mul hr.le,Real.sqrt_sq hp.le,Real.sqrt_sq hθ.le,
    Real.sqrt_sq hR,Real.sqrt_sq hφ.le]

lemma source_far_good_scalar {a b I p θ R r φ : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hp : 0<p) (hθ : 0<θ)
    (hR : 0≤R) (hr : 0<r) (hφ : 0<φ) :
    φ^2/(p*θ^2)*Real.sqrt (a*I)*Real.sqrt (b*p^2*θ^2*R^2/(r*φ^2)) =
      Real.sqrt (a*b)*Real.sqrt I*R*φ/(θ*Real.sqrt r) := by
  rw [source_far_sqrt_mass hb hp hθ hR hr hφ,Real.sqrt_mul ha,Real.sqrt_mul ha]
  field_simp [hp.ne',hθ.ne',hφ.ne',(Real.sqrt_pos.mpr hr).ne']

lemma source_far_magnetic_scalar {a b I p θ R r φ : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hI : 0≤I) (hp : 0<p) (hθ : 0<θ)
    (hR : 0≤R) (hr : 0<r) (hφ : 0<φ) :
    φ/p*Real.sqrt (a*(I+2*r))*Real.sqrt (b*p^2*θ^2*R^2/(r*φ^2)) =
      Real.sqrt (a*b)*R*θ*Real.sqrt (I/r+2) := by
  have hs : Real.sqrt (I/r+2)=Real.sqrt (I+2*r)/Real.sqrt r := by
    rw [show I/r+2=(I+2*r)/r by field_simp,Real.sqrt_div (by positivity)]
  rw [hs,source_far_sqrt_mass hb hp hθ hR hr hφ,Real.sqrt_mul ha,Real.sqrt_mul ha]
  field_simp [hp.ne',hφ.ne',(Real.sqrt_pos.mpr hr).ne']

lemma source_far_magnetic_le {I θ R r φ : ℝ}
    (hI : 0≤I) (hθ : 0<θ) (hR : 0≤R) (hr : 0<r) (hθφ : θ^2≤φ) :
    R*θ*Real.sqrt (I/r+2) ≤ Real.sqrt I*R*φ/(θ*Real.sqrt r)+2*R*θ := by
  have hs : Real.sqrt (I/r+2) ≤ Real.sqrt I/Real.sqrt r+2 := by
    calc
      _ ≤ Real.sqrt (I/r)+Real.sqrt 2 := by
        apply (Real.sqrt_le_left (by positivity)).mpr
        nlinarith only [Real.sq_sqrt (show 0≤I/r by positivity),
          Real.sq_sqrt (show (0:ℝ)≤2 by norm_num),
          mul_nonneg (Real.sqrt_nonneg (I/r)) (Real.sqrt_nonneg 2)]
      _ ≤ _ := by rw [Real.sqrt_div hI]; gcongr; norm_num
  have hθ' : θ≤φ/θ := (le_div_iff₀ hθ).mpr (by simpa only [sq] using hθφ)
  calc
    _ ≤ R*θ*(Real.sqrt I/Real.sqrt r+2) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = Real.sqrt I*R*θ/Real.sqrt r+2*R*θ := by ring
    _ ≤ Real.sqrt I*R*(φ/θ)/Real.sqrt r+2*R*θ := by gcongr
    _ = _ := by ring

lemma ennreal_half_ofReal {x : ℝ} (hx : 0≤x) :
    (ENNReal.ofReal x)^(1/2:ℝ)=ENNReal.ofReal (Real.sqrt x) := by
  rw [Real.sqrt_eq_rpow,ENNReal.ofReal_rpow_of_nonneg hx (by norm_num)]

lemma sqrt_energy_pair {a b E : ℝ} (ha : 0≤a) (hb : 0≤b) (hE : 0≤E) :
    Real.sqrt ((a*E)*(b*E))=Real.sqrt (a*b)*E := by
  rw [show (a*E)*(b*E)=(a*b)*E^2 by ring,Real.sqrt_mul (mul_nonneg ha hb),Real.sqrt_sq hE]

lemma source_far_energy_scalar {K b g E I p θ R r φ : ℝ}
    (hK : 0≤K) (hb : 0≤b) (hg : 0≤g) (hE : 0≤E) (hI : 0≤I)
    (hp : 0<p) (hθ : 0<θ) (hR : 0≤R) (hr : 0<r) (hφ : 0<φ) (hθφ : θ^2≤φ) :
    K*(φ^2/(p*θ^2)*Real.sqrt ((20*E)*I)*Real.sqrt ((b*E)*p^2*θ^2*R^2/(r*φ^2)))+
    K*(φ/p*Real.sqrt ((40*E)*(I+2*r))*Real.sqrt ((g*E)*p^2*θ^2*R^2/(r*φ^2))) ≤
    K*(Real.sqrt (20*b)+Real.sqrt (40*g))*E*(Real.sqrt I*R*φ/(θ*Real.sqrt r)+2*R*θ) := by
  rw [source_far_good_scalar (by positivity) (mul_nonneg hb hE) hp hθ hR hr hφ,
    source_far_magnetic_scalar (by positivity) (mul_nonneg hg hE) hI hp hθ hR hr hφ,
    sqrt_energy_pair (by norm_num) hb hE,sqrt_energy_pair (by norm_num) hg hE]
  have hm := source_far_magnetic_le hI hθ hR hr hθφ
  calc
    _ = K*(Real.sqrt (20*b)*E*(Real.sqrt I*R*φ/(θ*Real.sqrt r)))+
        K*(Real.sqrt (40*g)*E*(R*θ*Real.sqrt (I/r+2))) := by ring
    _ ≤ K*(Real.sqrt (20*b)*E*(Real.sqrt I*R*φ/(θ*Real.sqrt r)+2*R*θ))+
        K*(Real.sqrt (40*g)*E*(Real.sqrt I*R*φ/(θ*Real.sqrt r)+2*R*θ)) := by
      gcongr
      exact le_add_of_nonneg_right (by positivity)
    _ = _ := by ring

lemma source_far_ennreal_scalar {K Cg Cb E I p θ r φ len : ℝ}
    (hK : 0≤K) (hCg : 0≤Cg) (hCb : 0≤Cb) (hE : 0≤E) (hI : 0<I)
    (hp : 0<p) (hθ : 0<θ) (hr : 0<r) (hφ : 0<φ) (hlen : 0<len) (hθφ : θ^2≤φ) :
    let R := Real.sqrt (1+I/len)
    let mass := ENNReal.ofReal (568197120*E*(1+I/len)/(p*r*φ^2))
    ENNReal.ofReal (K*φ^2/(p*θ^2))*
      ((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
        (ENNReal.ofReal (128*Cg*p^3*θ^2)*mass)^(1/2:ℝ))+
    ENNReal.ofReal (K*φ/p)*
      ((ENNReal.ofReal (40*(I+2*r)*E))^(1/2:ℝ)*
        (ENNReal.ofReal (128*Cb*p^3*θ^2)*mass)^(1/2:ℝ)) ≤
    ENNReal.ofReal (K*(Real.sqrt (20*(128*568197120*Cg))+Real.sqrt (40*(128*568197120*Cb)))*E*
      (Real.sqrt I*R*φ/(θ*Real.sqrt r)+2*R*θ)) := by
  dsimp only
  let R := Real.sqrt (1+I/len)
  have hR : 0≤R := Real.sqrt_nonneg _
  have hRsq : R^2=1+I/len := Real.sq_sqrt (by positivity)
  have he (C : ℝ) : (128*C*p^3*θ^2)*(568197120*E*(1+I/len)/(p*r*φ^2))=
      ((128*568197120*C)*E)*p^2*θ^2*R^2/(r*φ^2) := by
    rw [hRsq]
    field_simp [hp.ne',hr.ne',hφ.ne']
  rw [←ENNReal.ofReal_mul (by positivity : 0≤128*Cg*p^3*θ^2),
    ←ENNReal.ofReal_mul (by positivity : 0≤128*Cb*p^3*θ^2),he Cg,he Cb]
  rw [ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
    ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity)]
  rw [←ENNReal.ofReal_mul (Real.sqrt_nonneg _),←ENNReal.ofReal_mul (by positivity : 0≤K*φ^2/(p*θ^2)),
    ←ENNReal.ofReal_mul (Real.sqrt_nonneg _),←ENNReal.ofReal_mul (by positivity : 0≤K*φ/p),
    ←ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h := source_far_energy_scalar hK (show 0≤128*568197120*Cg by positivity)
    (show 0≤128*568197120*Cb by positivity) hE hI.le hp hθ hR hr hφ hθφ
  convert h using 1; congr 1 <;> ring_nf

lemma Admissible.projected_source_baseline_far {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb c : ℝ,0 ≤ Cg ∧ 0 ≤ Cb ∧ 0 ≤ c ∧
    ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (k : Fin 4→ℕ)
        (a b I len w M A P L massScale Cs : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → 0 < len → len ≤ I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
      massScale ≤ sourceRepresentative (k 0)/128 → massScale ≤ w/8 →
      cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 →
      32 ≤ cappedRepresentative (k 2)*w →
      2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative (k 2)+
        Real.sqrt (A*L/cappedRepresentative (k 2))))⁻¹^2 →
      (∀t∈Icc a b,w/16 ≤ ‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let r := max 1 T*cappedRepresentative (k 3)
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := representativeClosedBin T w k
      let E := ∫x : Vec,totalEnergy s (0,x)
      let mass := ENNReal.ofReal (568197120*E*(1+I/len)/(p*r*φ^2))
      (∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s X V B T w Q z
        ∂physicalBinMeasure V B (Icc a b))  ≤
      ENNReal.ofReal (128*(3840+94080000*c)*φ^2/(p*θ^2))*
        ((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
          (ENNReal.ofReal (128*Cg*p^3*θ^2)*mass)^(1/2:ℝ))+
      ENNReal.ofReal (128*(3840+94080000*c)*φ/p)*
        ((ENNReal.ofReal (40*(I+2*r)*E))^(1/2:ℝ)*
          (ENNReal.ofReal (128*Cb*p^3*θ^2)*mass)^(1/2:ℝ)) := by
  obtain ⟨Cg,Cb,c,hCg,hCb,hc,hsource⟩ := hd₀.projected_source_two_budget_bound
  refine ⟨Cg,Cb,c,hCg,hCb,hc,?_⟩
  intro s T F hs hT h0 zX S Q k a b I len w M A P L massScale Cs hS hS0 ha hb hlen hlenI hab
    hM hA hP hL hm hw hCs hmq hmw hsmall hwφ hstable hband HX HZ
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let r := max 1 T*cappedRepresentative (k 3)
  let B := representativeClosedBin T w k
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let E := ∫x : Vec,totalEnergy s (0,x)
  have hp : 0 < p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0 < θ := cappedRepresentative_pos _
  have hφ : 0 < φ := cappedRepresentative_pos _
  have hr : 0 < r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hBmax : B.rmax=2*r := by dsimp [B,representativeClosedBin,r]; ring
  have hBmin : B.rmin=r/2 := rfl
  have hBDmin : B.Dmin=φ^2/2 := rfl
  have hI : 0 < I := hlen.trans_le hlenI
  have hE : 0 ≤ E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hdsmall : B.dmax ≤ φ^2/32 := by
    change 8*θ^2 ≤ φ^2/32
    have ht : θ ≤ φ/16 := hsmall
    nlinarith only [sq_le_sq₀ hθ.le (by positivity : 0 ≤ φ/16) |>.mpr ht]
  have hbudget := F.closedEulerian_baseline_budget hs hT zX B hS (k 0) (k 2)
    (by rfl : p=64*(2:ℝ)^(k 0)) (by rfl : φ=(2:ℝ)⁻¹^(k 2)) ha hb hlen hlenI hab
    hM hA hP hL hm hφ (cappedRepresentative_le_one _) hCs hstable le_rfl le_rfl hmq hmw
    (by change 0 < r/2; positivity) (by rw [hBmax]; positivity) hdsmall le_rfl le_rfl
    (by change 4 ≤ φ*(w/8); dsimp [φ] at *; nlinarith only [hwφ]) HX HZ
  have hmass : coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) /
      ENNReal.ofReal (B.rmin^2*B.Dmin)  ≤
      ENNReal.ofReal (568197120*E*(1+I/len)/(p*r*φ^2)) := by
    calc
      _  ≤  (ENNReal.ofReal (35512320*B.rmax/p*(1+I/len))*ENNReal.ofReal E)/
          ENNReal.ofReal (B.rmin^2*B.Dmin) := by gcongr
      _ = _ := by
        rw [hBmax,hBmin,hBDmin,←ENNReal.ofReal_mul (by positivity : 0 ≤ 35512320*(2*r)/p*(1+I/len)),
          ←ENNReal.ofReal_div_of_pos (by positivity : 0 < (r/2)^2*(φ^2/2))]
        congr 1
        field_simp [hp.ne',hr.ne',hφ.ne',hlen.ne']
        ring
  have hgood : ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I (k 2)  ≤
      ENNReal.ofReal (20*I*E) := by
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.goodFieldBudget_uniform X (fun t=>velocity (V t)) 1 hJ hI hab)
    calc
      _  ≤  ENNReal.ofReal I*((4*1+1:ℕ)*ENNReal.ofReal (4*E)) := mul_le_mul' le_rfl hh
      _ = _ := by
        change ENNReal.ofReal I*(5*ENNReal.ofReal (4*E))=_
        rw [←ENNReal.ofReal_ofNat (n:=5),←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 5),
          ←ENNReal.ofReal_mul hI.le]
        congr 1
        ring
  have hmag : ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T 1
      (max 0 (a-B.rmax)) (min T (b-B.rmin)) I (k 2)  ≤
      ENNReal.ofReal (40*(I+2*r)*E) := by
    have hsub : Icc (max 0 (a-B.rmax)) (min T (b-B.rmin))⊆Icc 0 T :=
      Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
    have hh : min T (b-B.rmin)-max 0 (a-B.rmax)  ≤  (1+2*r/I)*I := by
      have hb' := min_le_right T (b-B.rmin)
      have ha' := le_max_right 0 (a-B.rmax)
      rw [hBmax] at ha'
      rw [hBmin] at hb'
      have he : (1+2*r/I)*I=I+2*r := by field_simp
      rw [hBmin,hBmax,he]
      linarith only [hab,hb',ha',hr]
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.magneticFieldBudget_uniform F.flow zX 1 hsub hI (by positivity : 0 ≤ 1+2*r/I) hh)
    calc
      _  ≤  ENNReal.ofReal (2*I)*((2*(4*1+1):ℕ)*ENNReal.ofReal (1+2*r/I)*ENNReal.ofReal (2*E)) :=
        mul_le_mul' le_rfl hh
      _ = _ := by
        change ENNReal.ofReal (2*I)*(10*ENNReal.ofReal (1+2*r/I)*ENNReal.ofReal (2*E))=_
        rw [←ENNReal.ofReal_ofNat (n:=10),←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 10),
          ←ENNReal.ofReal_mul (by positivity : 0 ≤ 10*(1+2*r/I)),
          ←ENNReal.ofReal_mul (by positivity : 0 ≤ 2*I)]
        congr 1
        field_simp [hI.ne']
        ring
  have hband' (t : ℝ) (ht : t∈Icc a b) : w/16 ≤ ‖V t‖ := by
    simpa only [V,prefixFlow,prefixClamp_eq (hJ ht)] using hband t ht
  have hangle (D : ℝ) (hD : D∈Icc B.Dmin B.Dmax) : DyadicWindow 1 (k 2) (Real.sqrt (D/2)) :=
    dyadicWindow_one_sqrt (k 2)
      (by simpa only [B,representativeClosedBin,cappedRepresentative,inv_pow] using hD.1)
      (by simpa only [B,representativeClosedBin,cappedRepresentative,inv_pow] using hD.2)
  have hn := hsource s T F hs hT h0 zX B S Q a b I w (p/128) p θ φ 1 1 (k 2)
    hS hS0 hJ hI hw (by positivity) hp hθ hφ (by norm_num)
    (by change 0 < r/2; positivity) (by change 0 < φ^2/2; positivity)
    le_rfl (by change p/32 ≤ p; linarith only [hp]) le_rfl le_rfl le_rfl le_rfl
    (by norm_num [B,representativeClosedBin]) (hdsmall.trans (by change φ^2/32 ≤ φ^2/2; nlinarith only [sq_nonneg φ]))
    hangle hband'
  dsimp only at hn
  have hθ1 : θ ≤ 1 := cappedRepresentative_le_one _
  simp only [min_eq_left hθ1] at hn
  have heqG : (3840+94080000*c)*φ^2/(p/128*θ^2)=128*(3840+94080000*c)*φ^2/(p*θ^2) := by ring
  have heqB : (3840+94080000*c)*φ/(p/128)=128*(3840+94080000*c)*φ/p := by ring
  rw [heqG,heqB] at hn
  apply hn.trans
  apply add_le_add
  · apply mul_le_mul' le_rfl
    apply mul_le_mul' (ENNReal.rpow_le_rpow hgood (by norm_num))
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    exact (min_le_right _ _).trans (mul_le_mul' le_rfl hmass)
  · apply mul_le_mul' le_rfl
    apply mul_le_mul' (ENNReal.rpow_le_rpow hmag (by norm_num))
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    exact (min_le_right _ _).trans (mul_le_mul' le_rfl hmass)

lemma Admissible.projected_source_baseline_radius_bound {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ, 0≤C ∧
    ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (k : Fin 4→ℕ)
        (a b I len w M A P L massScale Cs : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → 0 < len → len ≤ I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
      massScale ≤ sourceRepresentative (k 0)/128 → massScale ≤ w/8 →
      cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 →
      32 ≤ cappedRepresentative (k 2)*w →
      2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative (k 2)+
        Real.sqrt (A*L/cappedRepresentative (k 2))))⁻¹^2 →
      (∀t∈Icc a b,w/16 ≤ ‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let r := max 1 T*cappedRepresentative (k 3)
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := representativeClosedBin T w k
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s X V B T w Q z
        ∂physicalBinMeasure V B (Icc a b)) ≤
      ENNReal.ofReal (C*E*(Real.sqrt I*Real.sqrt (1+I/len)*φ/(θ*Real.sqrt r)+
        2*Real.sqrt (1+I/len)*θ)) := by
  obtain ⟨Cg,Cb,c,hCg,hCb,hc,hsource⟩ := hd₀.projected_source_baseline_far
  let K := 128*(3840+94080000*c)
  let C := K*(Real.sqrt (20*(128*568197120*Cg))+Real.sqrt (40*(128*568197120*Cb)))
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro s T F hs hT h0 zX S Q k a b I len w M A P L massScale Cs hS hS0 ha hb hlen hlenI hab
    hM hA hP hL hm hw hCs hmq hmw hsmall hwφ hstable hband HX HZ
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let r := max 1 T*cappedRepresentative (k 3)
  let E := ∫x : Vec,totalEnergy s (0,x)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hr : 0<r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hI : 0<I := hlen.trans_le hlenI
  have hθφ : θ^2≤φ := by
    have hh : θ≤φ := by have h := hsmall; change θ≤φ/16 at h; linarith only [h,hφ]
    have h1 : θ≤1 := cappedRepresentative_le_one _
    simpa only [sq,mul_one] using mul_le_mul hh h1 hθ.le hφ.le
  have hbound := hsource s T F hs hT h0 zX S Q k a b I len w M A P L massScale Cs
    hS hS0 ha hb hlen hlenI hab hM hA hP hL hm hw hCs hmq hmw hsmall hwφ hstable hband HX HZ
  exact hbound.trans (source_far_ennreal_scalar hK hCg hCb hE hI hp hθ hr hφ hlen hθφ)

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.direct_source_shared_radius_budget {d : Datum} (hd₀ : Admissible d) :
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
      max 1 T*cappedRepresentative (k 3)≤I →
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
      let G := goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I (k 2)
      let Hf := magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I (k 2)
      let O := ENNReal.ofReal (491520*E*(1+φ/σ)*(1+I/len)/(p*r*φ^2))
      let H := ENNReal.ofReal (576*I*r*φ^2)
      let Dg := ENNReal.ofReal (128*Cg*p^3*(min θ σ)^2)
      let Db := ENNReal.ofReal (128*Cb*p^3*(min θ σ)^2)
      (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z
        ∂physicalBinMeasure V B (Icc a b)) ≤
      ENNReal.ofReal (10240*φ/(p*θ^2))*
        ((ENNReal.ofReal I*G)^(1/2:ℝ)*(min (Dg^2*H) (Dg*O))^(1/2:ℝ))+
      ENNReal.ofReal (10240/p)*
        ((ENNReal.ofReal (2*I)*Hf)^(1/2:ℝ)*(min (Db^2*H) (Db*O))^(1/2:ℝ)) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_relative_budget
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S k j a b I len w M A P L massScale Cs hS hS0
    ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable hrI HX HZ
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
  have hmag : magneticFieldBudget s F.flow zX T 1
      (max 0 (a-B.rmax)) (min T (b-B.rmin)) I (k 2) ≤
      magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I (k 2) := by
    apply magneticFieldBudget_mono
    apply radial_source_interval_common
    · rw [hBmin]; positivity
    · rw [hBmax]
      exact mul_le_mul_of_nonneg_left hrI (by norm_num)
  have heG : 80*φ/(p/128*θ^2)=10240*φ/(p*θ^2) := by ring
  have heB : 80/(p/128)=10240/p := by ring
  rw [heG,heB,hmass] at hn
  apply hn.trans
  apply add_le_add
  · apply mul_le_mul' le_rfl
    apply mul_le_mul' le_rfl
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    exact min_le_min (mul_le_mul' le_rfl hvolume) le_rfl
  · apply mul_le_mul' le_rfl
    apply mul_le_mul' (ENNReal.rpow_le_rpow (mul_le_mul' le_rfl hmag) (by norm_num))
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    exact min_le_min (mul_le_mul' le_rfl hvolume) le_rfl

end RVM

end

end OAI
