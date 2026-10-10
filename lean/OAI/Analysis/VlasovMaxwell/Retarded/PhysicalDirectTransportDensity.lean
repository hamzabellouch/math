import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.PhysicalProjectedRemainderDensity
import OAI.Analysis.VlasovMaxwell.Population.SqrtBaselineClippedLength
import OAI.Analysis.VlasovMaxwell.Population.RelativeClosedBinHitGeometry
import OAI.Analysis.VlasovMaxwell.Geometry.RelativeAngleCoordinate

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
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma dyadic_sqrt_radius_balance {a b H : ℝ} (ha : 0≤a) (hb : 0≤b) (hH : 0<H) :
    Summable (fun k : ℤ=>min (a*Real.sqrt (H*(2:ℝ)^k))
      (b/Real.sqrt (H*(2:ℝ)^k))) ∧
    (∑'k : ℤ,min (a*Real.sqrt (H*(2:ℝ)^k))
      (b/Real.sqrt (H*(2:ℝ)^k)))≤dyadicBalanceConstant (1/2) (1/2)*Real.sqrt (a*b) := by
  let a' := a*Real.sqrt H
  let b' := b/Real.sqrt H
  have hHroot : 0<Real.sqrt H := Real.sqrt_pos.mpr hH
  have he (k : ℤ) : min (a'*((2:ℝ)^k)^(1/2:ℝ)) (b'*((2:ℝ)^k)^(-(1/2:ℝ)))=
      min (a*Real.sqrt (H*(2:ℝ)^k)) (b/Real.sqrt (H*(2:ℝ)^k)) := by
    rw [Real.rpow_neg (zpow_pos (by norm_num : (0:ℝ)<2) k).le]
    rw [←Real.sqrt_eq_rpow,Real.sqrt_mul hH.le]
    dsimp [a',b']
    congr 1 <;> ring
  have hs := dyadic_power_min_summable (mul_nonneg ha hHroot.le)
    (div_nonneg hb hHroot.le) (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1/2)
  change Summable (fun k : ℤ=>min (a'*((2:ℝ)^k)^(1/2:ℝ)) (b'*((2:ℝ)^k)^(-(1/2:ℝ)))) at hs
  simp_rw [he] at hs
  refine ⟨hs,?_⟩
  rcases eq_or_lt_of_le ha with rfl|ha'
  · have he0 (k : ℤ) : min (0*Real.sqrt (H*(2:ℝ)^k)) (b/Real.sqrt (H*(2:ℝ)^k))=0 := by
      rw [zero_mul,min_eq_left (by positivity)]
    rw [tsum_congr he0]
    simp
  rcases eq_or_lt_of_le hb with rfl|hb'
  · have he0 (k : ℤ) : min (a*Real.sqrt (H*(2:ℝ)^k)) (0/Real.sqrt (H*(2:ℝ)^k))=0 := by
      rw [zero_div,min_eq_right (by positivity)]
    rw [tsum_congr he0]
    simp
  have ht := dyadic_balance (mul_pos ha' hHroot) (div_pos hb' hHroot)
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1/2)
  change (∑'k : ℤ,min (a'*((2:ℝ)^k)^(1/2:ℝ)) (b'*((2:ℝ)^k)^(-(1/2:ℝ))))≤_ at ht
  simp_rw [he] at ht
  norm_num only [show (1/2:ℝ)+(1/2)=1 by norm_num,div_one] at ht
  change (∑'k : ℤ,min (a*Real.sqrt (H*(2:ℝ)^k)) (b/Real.sqrt (H*(2:ℝ)^k)))≤
    dyadicBalanceConstant (1/2) (1/2)*(a'^(1/2:ℝ)*b'^(1/2:ℝ)) at ht
  rw [←Real.sqrt_eq_rpow a',←Real.sqrt_eq_rpow b',←Real.sqrt_mul (by positivity : 0≤a')] at ht
  have hab : a'*b'=a*b := by dsimp [a',b']; field_simp
  rw [hab] at ht
  exact ht

lemma remaining_good_radial_sum {P C M A p w θ φ σ κ H : ℝ}
    (hP : 0<P) (hL : 1≤Real.log (2+P)) (hC : 0<C) (hM : 0<M) (hA : 0≤A)
    (hp : 0<p) (hw : 0<w) (hθ : 0<θ) (hφ : 0<φ) (hσ : 0<σ) (hσ1 : σ≤1)
    (hκ : 0≤κ) (hφθ : φ≤κ*θ) (hpP : p≤128*P) (hwP : w≤P) (hH : 0<H) :
    let I := (w/P)^2
    let R := Real.sqrt (1+I/min I (stabilityLength P C M A p w σ/2))
    let ν := min θ σ
    let a := I*p^2*ν^2*φ^2/θ^2
    let b := Real.sqrt I*R*ν*Real.sqrt (1+φ/σ)/θ^2
    Summable (fun k : ℤ=>min (a*Real.sqrt (H*(2:ℝ)^k)) (b/Real.sqrt (H*(2:ℝ)^k))) ∧
    (∑'k : ℤ,min (a*Real.sqrt (H*(2:ℝ)^k)) (b/Real.sqrt (H*(2:ℝ)^k)))≤
      dyadicBalanceConstant (1/2) (1/2)*Real.sqrt
        (32768*κ^2*(1+κ)*(1+C*(M+Real.sqrt A))*w^2*Real.sqrt (Real.log (2+P))) := by
  dsimp only
  have hν : 0 ≤ min θ σ := le_min hθ.le hσ.le
  have ht := dyadic_sqrt_radius_balance (a:=((w/P)^2*p^2*(min θ σ)^2*φ^2/θ^2))
    (b:=Real.sqrt ((w/P)^2)*Real.sqrt (1+(w/P)^2/min ((w/P)^2)
      (stabilityLength P C M A p w σ/2))*(min θ σ)*Real.sqrt (1+φ/σ)/θ^2)
    (by positivity) (by positivity) hH
  refine ⟨ht.1,ht.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  apply Real.sqrt_le_sqrt
  convert remaining_good_balance_coefficient hP hL hC hM hA hp hw hθ hφ.le hσ hσ1 hκ hφθ hpP hwP using 1
  ring

lemma remaining_magnetic_radial_sum {P C M A p w θ φ σ κ H : ℝ}
    (hP : 0<P) (hL : 1≤Real.log (2+P)) (hC : 0<C) (hM : 0<M) (hA : 0≤A)
    (hp : 0<p) (hw : 0<w) (hθ : 0≤θ) (hθ1 : θ≤1) (hφ : 0<φ) (hσ : 0<σ) (hσ1 : σ≤1)
    (hκ : 0≤κ) (hφθ : φ≤κ*θ) (hpP : p≤128*P) (hwP : w≤P) (hH : 0<H) :
    let I := (w/P)^2
    let R := Real.sqrt (1+I/min I (stabilityLength P C M A p w σ/2))
    let ν := min θ σ
    let a := I*p^2*ν^2*φ
    let b := Real.sqrt I*R*ν*Real.sqrt (1+φ/σ)/φ
    Summable (fun k : ℤ=>min (a*Real.sqrt (H*(2:ℝ)^k)) (b/Real.sqrt (H*(2:ℝ)^k))) ∧
    (∑'k : ℤ,min (a*Real.sqrt (H*(2:ℝ)^k)) (b/Real.sqrt (H*(2:ℝ)^k)))≤
      dyadicBalanceConstant (1/2) (1/2)*Real.sqrt
        (32768*(1+κ)*(1+C*(M+Real.sqrt A))*w^2*Real.sqrt (Real.log (2+P))) := by
  dsimp only
  have hν : 0 ≤ min θ σ := le_min hθ hσ.le
  have ht := dyadic_sqrt_radius_balance (a:=((w/P)^2*p^2*(min θ σ)^2*φ))
    (b:=Real.sqrt ((w/P)^2)*Real.sqrt (1+(w/P)^2/min ((w/P)^2)
      (stabilityLength P C M A p w σ/2))*(min θ σ)*Real.sqrt (1+φ/σ)/φ)
    (by positivity) (by positivity) hH
  refine ⟨ht.1,ht.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  apply Real.sqrt_le_sqrt
  convert remaining_magnetic_balance_coefficient hP hL hC hM hA hp hw hθ hθ1 hφ.le hσ hσ1 hκ hφθ hpP hwP using 1
  field_simp [hφ.ne']

lemma direct_transport_bin_bound {r p θ φ : ℝ} (n W v : Vec)
    (hr : 0<r) (hp : 0<p) (hθ : 0<θ) (hφ : 0≤φ) (hn : ‖n‖=1)
    (hq : p≤q v) (hdlo : θ^2/2≤1-dot n (velocity v))
    (hdhi : 1-dot n (velocity v)≤8*θ^2)
    (hDhi : 1-dot n (velocity W)≤8*φ^2) :
    ‖forceTransportKernel r n (velocity W) v‖≤128*(θ+φ)/(r^2*p^2*θ^3) := by
  let d := 1-dot n (velocity v)
  let D := 1-dot n (velocity W)
  have hd : 0<d := cone_denom_pos v n hn
  have hD : 0<D := cone_denom_pos W n hn
  have hsθ : Real.sqrt (2*d)≤4*θ := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith⟩
  have hsφ : Real.sqrt (2*D)≤4*φ := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith⟩
  have hnum : d+2*Real.sqrt (2*D)*Real.sqrt (2*d)≤8*θ^2+32*φ*θ := by
    have hh := mul_le_mul hsφ hsθ (Real.sqrt_nonneg _) (by positivity : 0≤4*φ)
    dsimp only [d] at *
    nlinarith
  have hb := forceTransportKernel_bound r n W v hn
  change _ ≤ (r^2*(q v)^2*d^2)⁻¹*(d+2*Real.sqrt (2*D)*Real.sqrt (2*d)) at hb
  calc
    _ ≤ (r^2*(q v)^2*d^2)⁻¹*(d+2*Real.sqrt (2*D)*Real.sqrt (2*d)) := hb
    _ ≤ (r^2*p^2*(θ^2/2)^2)⁻¹*(8*θ^2+32*φ*θ) := by
      apply mul_le_mul _ hnum (by positivity) (by positivity)
      apply inv_anti₀ (by positivity)
      gcongr
    _ = (32*θ+128*φ)/(r^2*p^2*θ^3) := by field_simp; ring
    _ ≤ 128*(θ+φ)/(r^2*p^2*θ^3) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith

lemma direct_source_bin_bound {r p θ φ : ℝ} (n W v E B : Vec)
    (hr : 0<r) (hp : 0<p) (hθ : 0<θ) (hφ : 0≤φ) (hn : ‖n‖=1)
    (hq : p≤q v) (hdlo : θ^2/2≤1-dot n (velocity v))
    (hDhi : 1-dot n (velocity W)≤8*φ^2) :
    ‖forceSourceKernel r n (velocity W) v
      (fderiv ℝ velocity v (E+cross (velocity v) B))‖≤
      (80*φ/(r*p))*(goodField E B n/θ^2+‖B‖) := by
  let d := 1-dot n (velocity v)
  let D := 1-dot n (velocity W)
  have hd : 0<d := cone_denom_pos v n hn
  have hD : 0<D := cone_denom_pos W n hn
  have hG : 0≤goodField E B n := add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hsφ : Real.sqrt (2*D)≤4*φ := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith⟩
  have hc : 10*Real.sqrt (2*D)/(r*q v)≤40*φ/(r*p) := by
    calc
      _ ≤ 10*(4*φ)/(r*p) := by gcongr
      _ = _ := by ring
  have hg : goodField E B n/d≤2*(goodField E B n/θ^2) := by
    calc
      goodField E B n/d≤goodField E B n/(θ^2/2) := by gcongr
      _ = _ := by ring
  have hb := forceSourceKernel_bound r n W v E B hr hn
  change _ ≤ (10*Real.sqrt (2*D))/(r*q v*d)*(goodField E B n+d*‖B‖) at hb
  calc
    _ ≤ (10*Real.sqrt (2*D))/(r*q v*d)*(goodField E B n+d*‖B‖) := hb
    _ = (10*Real.sqrt (2*D)/(r*q v))*(goodField E B n/d+‖B‖) := by field_simp
    _ ≤ (40*φ/(r*p))*(2*(goodField E B n/θ^2+‖B‖)) := by
      apply mul_le_mul hc _ (by positivity) (by positivity)
      linarith [norm_nonneg B]
    _ = _ := by ring

def physicalDirectTransportDensity (s : Solution) (X V : ℝ→Vec)
    (B : ClosedConeBin) (z : ConeCoordinate) : ℝ≥0∞ :=
  let r := z.1-z.2.1
  let y := X z.1-r • z.2.2.1
  ENNReal.ofReal (r^2)*∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
    ENNReal.ofReal ‖s.f (z.2.1,(y,v)) • forceTransportKernel r z.2.2.1 (velocity (V z.1)) v‖

lemma physicalDirectTransportDensity_bound {s : Solution} {X V : ℝ→Vec}
    {B : ClosedConeBin} {p θ φ : ℝ} {z : ConeCoordinate}
    (hr : 0<z.1-z.2.1) (hp : 0<p) (hθ : 0<θ) (hφ : 0≤φ)
    (hq : p≤B.qmin) (hdlo : θ^2/2≤B.dmin) (hdhi : B.dmax≤8*θ^2)
    (hDhi : 1-dot z.2.2.1 (velocity (V z.1))≤8*φ^2)
    (hf : ∀v,0 ≤ s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) :
    physicalDirectTransportDensity s X V B z≤
      ENNReal.ofReal (128*(θ+φ)/(p^2*θ^3))*physicalBinDensity s X V B z.1 z.2.1 z.2.2 := by
  unfold physicalDirectTransportDensity
  calc
    _ ≤ ENNReal.ofReal ((z.1-z.2.1)^2)*
        ∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
          ENNReal.ofReal (128*(θ+φ)/((z.1-z.2.1)^2*p^2*θ^3))*
            ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) := by
      apply mul_le_mul' le_rfl
      apply setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _)
      intro v hv
      rw [←ENNReal.ofReal_mul (by positivity : 0≤128*(θ+φ)/((z.1-z.2.1)^2*p^2*θ^3))]
      apply ENNReal.ofReal_le_ofReal
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hf v)]
      calc
        _ ≤ s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))*
            (128*(θ+φ)/((z.1-z.2.1)^2*p^2*θ^3)) :=
          mul_le_mul_of_nonneg_left
            (direct_transport_bin_bound _ _ _ hr hp hθ hφ (sphere_norm _)
              (hq.trans hv.1.1) (hdlo.trans hv.2.1.1) (hv.2.1.2.trans hdhi) hDhi) (hf v)
        _ = _ := mul_comm _ _
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←mul_assoc,
        ←ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      congr 1
      field_simp

lemma PhaseFlowOn.direct_transport_near_far {s : Solution} {T a b C p qUpper θ φ σ : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase}
    (hS : IsCompact S) (hS0 : tsupport (fun z=>s.f (0,z))⊆S)
    (hJ : Icc a b⊆Icc 0 T) (hp : 0<p) (hθ : 0<θ) (hφ : 0≤φ)
    (hq : p≤B.qmin) (hdlo : θ^2/2≤B.dmin) (hdhi : B.dmax≤8*θ^2)
    (hDhi : B.Dmax≤8*φ^2) (hr : 0<B.rmin) (hD : 0<B.Dmin)
    (hdensity : ∀z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2) B (Icc a b),
      physicalBinDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) B z.1 z.2.1 z.2.2≤ENNReal.ofReal (C*qUpper^3*(min θ σ)^2)) :
    (∫⁻z : ConeCoordinate,physicalDirectTransportDensity s
      (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>(prefixFlow F.flow T zX t).2) B z
      ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) B (Icc a b))≤
      ENNReal.ofReal (128*(θ+φ)/(p^2*θ^3))*min
        (ENNReal.ofReal (C*qUpper^3*(min θ σ)^2)*(volume (Icc a b)*
          ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)))
        (coneOccupation F.flow zX T s.f
          (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))/
            ENNReal.ofReal (B.rmin^2*B.Dmin)) := by
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have he : (∫⁻z : ConeCoordinate,physicalDirectTransportDensity s
      (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>(prefixFlow F.flow T zX t).2) B z
      ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) B (Icc a b))≤
      ENNReal.ofReal (128*(θ+φ)/(p^2*θ^3))*
        (∫⁻z : ConeCoordinate,physicalBinDensity s
          (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>(prefixFlow F.flow T zX t).2) B z.1 z.2.1 z.2.2
          ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) B (Icc a b)) := by
    rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hα.snd.measurable B measurableSet_Icc)] with z hz
    exact physicalDirectTransportDensity_bound (hr.trans_le hz.2.2.1.1) hp hθ hφ hq hdlo hdhi
      (hz.2.2.2.2.2.trans hDhi) (fun v=>hs.nonnegative _ ⟨hz.2.1.1,hz.2.1.2.trans (hJ hz.1).2⟩ _)
  have hscale : 128*(C/128)=C := by ring
  have hnear := physicalBin_density_near (C:=C/128) (p:=qUpper) (θ:=min θ σ)
    hα.snd.measurable B measurableSet_Icc hφ hDhi (by simpa only [hscale] using hdensity)
  simp only [hscale] at hnear
  have hfar := F.physicalBin_density_far hs hT zX B hS hS0 hJ hr hD
  exact he.trans (mul_le_mul' le_rfl (le_min hnear hfar))

lemma Admissible.direct_transport_relative_budget {d : Datum} (hd₀ : Admissible d) :
    ∃Cρ : ℝ,0 ≤ Cρ ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (B : ClosedConeBin) (S : Set Phase)
        (M A P L a b massScale φ θ σ Cs p len I : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → 0 < p → 0 < len → len ≤ I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale →
      0 < φ → 0 < θ → 0 < σ → σ ≤ 1 → 128 ≤ Cs →
      2*len ≤ (Cs*(P/massScale)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2 →
      p/128 ≤ B.qmin → B.qmax ≤ p/32 → massScale ≤ B.qmin → massScale ≤ B.wmin →
      0 < B.rmin → 0 ≤ B.rmax → 0 < B.Dmin →
      θ^2/2 ≤ B.dmin → B.dmax ≤ 8*θ^2 → B.Dmax ≤ 8*φ^2 →
      σ^2/2 ≤ B.emin → B.emax ≤ 8*σ^2 → 4 ≤ σ*B.qmin → 4 ≤ σ*B.wmin →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V B z ∂physicalBinMeasure V B (Icc a b))≤
        ENNReal.ofReal (128*(θ+φ)/((p/128)^2*θ^3))*min
          (ENNReal.ofReal (Cρ*p^3*(min θ σ)^2)*(volume (Icc a b)*
            ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)))
          ((ENNReal.ofReal (30720*B.rmax/p*(1+φ/σ)*(1+I/len))*ENNReal.ofReal E)/
            ENNReal.ofReal (B.rmin^2*B.Dmin)) := by
  obtain ⟨Cρ,hCρ,hρ⟩ := hd₀.uniform_physicalBinDensity_constant
  refine ⟨128*Cρ,by positivity,?_⟩
  intro s T F hs hT h0 zX B S M A P L a b massScale φ θ σ Cs p len I
    hS hS0 ha hb hab hp hlen hlenI hJI hM hA hP hL hm hφ hθ hσ hσ1 hCs hstable
    hqmin hqmax hmq hmw hr hrmax hD hdlo hdhi hDhi helo hehi hq hw HX HZ
  dsimp only
  have hpq : B.qmax ≤ p := hqmax.trans (by linarith)
  have hdensity (z : ConeCoordinate)
      (hz : z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2) B (Icc a b)) :
      physicalBinDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) B z.1 z.2.1 z.2.2≤
          ENNReal.ofReal ((128*Cρ)*p^3*(min θ σ)^2) := by
    exact hρ s T F hs h0 _ _ B _ _ _ p θ σ ⟨hz.2.1.1,hz.2.1.2.trans (hz.1.2.trans hb)⟩
      hp.le hθ.le hσ.le hpq hdhi hehi
  have hn := F.direct_transport_near_far hs hT zX B hS hS0 (Icc_subset_Icc ha hb)
    (by positivity : 0<p/128) hθ hφ.le hqmin hdlo hdhi hDhi hr hD hdensity
  have ho := F.relative_closedEulerian_baseline hs hT zX B hS ha hb hab hp hlen hlenI hJI
    hM hA hP hL hm hφ hσ hσ1 hCs hstable hqmin hqmax hmq hmw hr hrmax
    hDhi helo hehi hq hw HX HZ
  apply hn.trans
  apply mul_le_mul' le_rfl
  apply min_le_min_left
  simpa only [div_eq_mul_inv] using mul_le_mul' ho (le_refl ((ENNReal.ofReal (B.rmin^2*B.Dmin))⁻¹))

def physicalDirectSourceDensity (s : Solution) (X V : ℝ→Vec)
    (C : ClosedConeBin) (z : ConeCoordinate) : ℝ≥0∞ :=
  ENNReal.ofReal ((z.1-z.2.1)^2) *
    ∫⁻v in coneBinMomentumSet C z.2.2.1 (velocity (V z.1)),
      let r := z.1-z.2.1
      let n := z.2.2.1
      let W := V z.1
      let y := X z.1-r • n
      let f := s.f (z.2.1,(y,v))
      let K := s.E (z.2.1,y)+cross (velocity v) (s.B (z.2.1,y))
      ENNReal.ofReal ‖f • forceSourceKernel r n (velocity W) v (fderiv ℝ velocity v K)‖

lemma physicalDirectSourceDensity_bound {s : Solution} {X V : ℝ→Vec}
    {C : ClosedConeBin} {p θ φ : ℝ} {z : ConeCoordinate}
    (hr : 0<z.1-z.2.1) (hp : 0<p) (hθ : 0<θ) (hφ : 0≤φ)
    (hq : p≤C.qmin) (hd : θ^2/2≤C.dmin)
    (hD : 1-dot z.2.2.1 (velocity (V z.1))≤8*φ^2)
    (hf : ∀v,0 ≤ s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) :
    physicalDirectSourceDensity s X V C z ≤
      ENNReal.ofReal ((80*φ/p)*(z.1-z.2.1)*
        (goodField (s.E (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1))
          (s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)) z.2.2.1/θ^2+
          ‖s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)‖))*
        physicalBinDensity s X V C z.1 z.2.1 z.2.2 := by
  let G := goodField (s.E (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1))
    (s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)) z.2.2.1
  let b := ‖s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)‖
  have hG : 0≤G := add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hb : 0≤b := norm_nonneg _
  unfold physicalDirectSourceDensity
  calc
    _ ≤ ENNReal.ofReal ((z.1-z.2.1)^2) *
        ∫⁻v in coneBinMomentumSet C z.2.2.1 (velocity (V z.1)),
          ENNReal.ofReal ((80*φ/((z.1-z.2.1)*p))*(G/θ^2+b))*
            ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) := by
      apply mul_le_mul' le_rfl
      apply setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _)
      intro v hv
      rw [←ENNReal.ofReal_mul (by positivity : 0≤(80*φ/((z.1-z.2.1)*p))*(G/θ^2+b))]
      apply ENNReal.ofReal_le_ofReal
      rw [norm_smul,Real.norm_of_nonneg (hf v)]
      calc
        _ ≤ s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))*
            ((80*φ/((z.1-z.2.1)*p))*(G/θ^2+b)) :=
          mul_le_mul_of_nonneg_left
            (direct_source_bin_bound _ _ _ _ _ hr hp hθ hφ (sphere_norm _)
              (hq.trans hv.1.1) (hd.trans hv.2.1.1) hD) (hf v)
        _ = _ := mul_comm _ _
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←mul_assoc,
        ←ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      congr 1
      field_simp [hr.ne']
      rfl

lemma physicalDirectSource_integral_bound {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) {X V : ℝ→Vec}
    (hX : Measurable X) (hV : Measurable V) (B : ClosedConeBin)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) {p θ φ : ℝ} (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ)
    (hr : 0<B.rmin) (hq : p≤B.qmin) (hdlo : θ^2/2≤B.dmin)
    (hDhi : B.Dmax≤8*φ^2)
    :
    (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z ∂physicalBinMeasure V B J)≤
      ENNReal.ofReal (80*φ/(p*θ^2))*(∫⁻z : ConeCoordinate,
        ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal (prefixConeGood s T X z)*
          physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J)+
      ENNReal.ofReal (80/p)*(∫⁻z : ConeCoordinate,
        ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal φ*ENNReal.ofReal (prefixConeMagnetic s T X z)*
          physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J) := by
  have hN := physicalBinDensity_aemeasurable hs hT hX hV B hJ hJT
  have hG := hs.measurable_prefixConeGood hT hX
  have hR : Measurable (fun z : ConeCoordinate=>ENNReal.ofReal (z.1-z.2.1)) :=
    (measurable_fst.sub (measurable_fst.comp measurable_snd)).ennreal_ofReal
  have hb : (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z ∂physicalBinMeasure V B J)≤
      ∫⁻z : ConeCoordinate,
        ENNReal.ofReal (80*φ/(p*θ^2))*(ENNReal.ofReal (z.1-z.2.1)*
          ENNReal.ofReal (prefixConeGood s T X z)*physicalBinDensity s X V B z.1 z.2.1 z.2.2)+
        ENNReal.ofReal (80/p)*(ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal φ*
          ENNReal.ofReal (prefixConeMagnetic s T X z)*physicalBinDensity s X V B z.1 z.2.1 z.2.2)
          ∂physicalBinMeasure V B J := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV B hJ)] with z hz
    have hzT : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩
    have hrz : 0<z.1-z.2.1 := hr.trans_le hz.2.2.1.1
    have hb := physicalDirectSourceDensity_bound (X:=X)
      hrz hp hθ hφ.le hq hdlo (hz.2.2.2.2.2.trans hDhi)
      (fun v=>hs.nonnegative _ hzT _)
    apply hb.trans_eq
    let G := prefixConeGood s T X z
    let b := prefixConeMagnetic s T X z
    have hG0 : 0≤G := add_nonneg (norm_nonneg _) (abs_nonneg _)
    have hb0 : 0≤b := norm_nonneg _
    have heG : goodField (s.E (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1))
        (s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)) z.2.2.1=G := by
      simp [G,prefixConeGood,prefixField,prefixClamp_eq hzT]
    have heb : ‖s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)‖=b := by
      simp [b,prefixConeMagnetic,coneFoot,prefixField,prefixClamp_eq hzT]
    rw [heG,heb]
    have he : (80*φ/p)*(z.1-z.2.1)*(G/θ^2+b)=
        (80*φ/(p*θ^2))*((z.1-z.2.1)*G)+
          (80/p)*((z.1-z.2.1)*φ*b) := by ring
    rw [he,ENNReal.ofReal_add (by positivity) (by positivity),add_mul]
    simp only [ENNReal.ofReal_mul (by positivity : 0≤80*φ/(p*θ^2)),
      ENNReal.ofReal_mul (by positivity : 0≤80/p),
      ENNReal.ofReal_mul (mul_nonneg hrz.le hφ.le),ENNReal.ofReal_mul hrz.le]
    dsimp only [G,b]
    ac_rfl
  refine hb.trans_eq ?_
  have hMG : AEMeasurable (fun z : ConeCoordinate=>
      ENNReal.ofReal (80*φ/(p*θ^2))*(ENNReal.ofReal (z.1-z.2.1)*
          ENNReal.ofReal (prefixConeGood s T X z)*physicalBinDensity s X V B z.1 z.2.1 z.2.2))
      (physicalBinMeasure V B J) := by
    simpa only [Pi.mul_apply] using (((hR.mul hG.ennreal_ofReal).aemeasurable.mul hN).const_mul
      (ENNReal.ofReal (80*φ/(p*θ^2))))
  rw [lintegral_add_left' hMG,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

lemma Admissible.direct_source_two_budget_bound {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0≤Cg ∧ 0≤Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (B : ClosedConeBin) (S : Set Phase)
      (a b I p P θ φ σ : ℝ) (k j : ℕ), IsCompact S →
      tsupport (fun z=>s.f (0,z))⊆S → Icc a b⊆Icc 0 T →
      0<I → 0<p → 0<P → 0<θ → 0<φ → 0≤σ → 0<B.rmin → 0<B.Dmin →
      p≤B.qmin → B.qmax≤P → θ^2/2≤B.dmin → B.dmax≤8*θ^2 →
      φ^2/2≤B.Dmin → B.Dmax≤8*φ^2 → B.emax≤8*σ^2 →
      (∀D∈Icc B.Dmin B.Dmax,DyadicWindow k j (Real.sqrt (D/2))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let M := coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) /
          ENNReal.ofReal (B.rmin^2*B.Dmin)
      let H := volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)
      let Dg := ENNReal.ofReal (128*Cg*P^3*(min θ σ)^2)
      let Db := ENNReal.ofReal (128*Cb*P^3*(min θ σ)^2)
      (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z ∂physicalBinMeasure V B (Icc a b))≤
        ENNReal.ofReal (80*φ/(p*θ^2))*
          ((ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) k a b I j)^(1/2:ℝ)*
            (min (Dg^2*H) (Dg*M))^(1/2:ℝ))+
        ENNReal.ofReal (80/p)*
          ((ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T k
            (max 0 (a-B.rmax)) (min T (b-B.rmin)) I j)^(1/2:ℝ)*
            (min (Db^2*H) (Db*M))^(1/2:ℝ)) := by
  obtain ⟨Cg,hCg,hgood⟩ := hd₀.uniform_actual_bin_Cauchy
  obtain ⟨Cb,hCb,hmag⟩ := hd₀.uniform_actual_magnetic_Cauchy
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX B S a b I p P θ φ σ k j hS hS0 hJ hI hp hP hθ hφ hσ
    hR hD hqlo hqhi hdlo hdhi hDlo hDhi he hangle
  dsimp only
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hb := physicalDirectSource_integral_bound hs hT hα.fst.measurable hα.snd.measurable B
    measurableSet_Icc hJ hp hθ hφ hR hqlo hdlo hDhi
  exact hb.trans (add_le_add
    (mul_le_mul' le_rfl (hgood s T F hs hT h0 zX B S a b I P θ φ σ k j hS hS0 hJ
      hI hP hθ.le hφ.le hσ hR hD hqhi hdhi hDhi he hangle))
    (mul_le_mul' le_rfl (hmag s T F hs hT h0 zX B S a b I P θ φ σ k j hS hS0 hJ
      hI hP hθ.le hφ.le hσ hR hD hDlo hqhi hdhi hDhi he hangle)))

lemma Admissible.direct_source_relative_budget {d : Datum} (hd₀ : Admissible d) :
    ∃Cg Cb : ℝ,0 ≤ Cg ∧ 0 ≤ Cb ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (B : ClosedConeBin) (S : Set Phase)
        (M A P L a b massScale φ θ σ Cs p len I : ℝ) (k j : ℕ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → 0 < p → 0 < len → len ≤ I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale →
      0 < φ → 0 < θ → 0 < σ → σ ≤ 1 → 128 ≤ Cs →
      2*len ≤ (Cs*(P/massScale)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2 →
      p/128 ≤ B.qmin → B.qmax ≤ p/32 → massScale ≤ B.qmin → massScale ≤ B.wmin →
      0 < B.rmin → 0 ≤ B.rmax → 0 < B.Dmin →
      θ^2/2 ≤ B.dmin → B.dmax ≤ 8*θ^2 → φ^2/2 ≤ B.Dmin → B.Dmax ≤ 8*φ^2 →
      σ^2/2 ≤ B.emin → B.emax ≤ 8*σ^2 → 4 ≤ σ*B.qmin → 4 ≤ σ*B.wmin →
      (∀D∈Icc B.Dmin B.Dmax,DyadicWindow k j (Real.sqrt (D/2))) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let E := ∫x : Vec,totalEnergy s (0,x)
      let O := (ENNReal.ofReal (30720*B.rmax/p*(1+φ/σ)*(1+I/len))*ENNReal.ofReal E)/
        ENNReal.ofReal (B.rmin^2*B.Dmin)
      let H := volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)
      let Dg := ENNReal.ofReal (128*Cg*p^3*(min θ σ)^2)
      let Db := ENNReal.ofReal (128*Cb*p^3*(min θ σ)^2)
      (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z ∂physicalBinMeasure V B (Icc a b))≤
        ENNReal.ofReal (80*φ/((p/128)*θ^2))*
          ((ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) k a b I j)^(1/2:ℝ)*
            (min (Dg^2*H) (Dg*O))^(1/2:ℝ))+
        ENNReal.ofReal (80/(p/128))*
          ((ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T k
            (max 0 (a-B.rmax)) (min T (b-B.rmin)) I j)^(1/2:ℝ)*
            (min (Db^2*H) (Db*O))^(1/2:ℝ)) := by
  obtain ⟨Cg,Cb,hCg,hCb,hforce⟩ := hd₀.direct_source_two_budget_bound
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX B S M A P L a b massScale φ θ σ Cs p len I k j
    hS hS0 ha hb hab hp hlen hlenI hJI hM hA hP hL hm hφ hθ hσ hσ1 hCs hstable
    hqmin hqmax hmq hmw hr hrmax hD hdlo hdhi hDlo hDhi helo hehi hq hw hangle HX HZ
  dsimp only
  have hI : 0<I := hlen.trans_le hlenI
  have hpq : B.qmax≤p := hqmax.trans (by linarith)
  have hforceBound := hforce s T F hs hT h0 zX B S a b I (p/128) p θ φ σ k j
    hS hS0 (Icc_subset_Icc ha hb) hI (by positivity) hp hθ hφ hσ.le hr hD
    hqmin hpq hdlo hdhi hDlo hDhi hehi hangle
  have ho := F.relative_closedEulerian_baseline hs hT zX B hS ha hb hab hp hlen hlenI hJI
    hM hA hP hL hm hφ hσ hσ1 hCs hstable hqmin hqmax hmq hmw hr hrmax
    hDhi helo hehi hq hw HX HZ
  have hod : coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))/
        ENNReal.ofReal (B.rmin^2*B.Dmin) ≤
      (ENNReal.ofReal (30720*B.rmax/p*(1+φ/σ)*(1+I/len))*ENNReal.ofReal (∫x : Vec,totalEnergy s (0,x)))/
        ENNReal.ofReal (B.rmin^2*B.Dmin) := by
    simpa only [div_eq_mul_inv] using mul_le_mul' ho (le_refl ((ENNReal.ofReal (B.rmin^2*B.Dmin))⁻¹))
  apply hforceBound.trans
  gcongr

lemma PhaseFlowOn.direct_transport_split_near_far {s : Solution} {T a b C p qUpper θ φ σ : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase}
    (hS : IsCompact S) (hS0 : tsupport (fun z=>s.f (0,z))⊆S)
    (hJ : Icc a b⊆Icc 0 T) (hp : 0<p) (hθ : 0<θ) (hφ : 0≤φ)
    (hq : p≤B.qmin) (hdlo : θ^2/2≤B.dmin) (hdhi : B.dmax≤8*θ^2)
    (hDhi : B.Dmax≤8*φ^2) (hr : 0<B.rmin) (hD : 0<B.Dmin)
    (hdensity : ∀z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2) B (Icc a b),
      physicalBinDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) B z.1 z.2.1 z.2.2≤ENNReal.ofReal (C*qUpper^3*(min θ σ)^2)) :
    (∫⁻z : ConeCoordinate,physicalDirectTransportDensity s
      (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>(prefixFlow F.flow T zX t).2) B z
      ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) B (Icc a b))≤
      ENNReal.ofReal (128/(p^2*θ^2))*
        (ENNReal.ofReal (C*qUpper^3*(min θ σ)^2)*(volume (Icc a b)*
          ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)))+
      ENNReal.ofReal (128*φ/(p^2*θ^3))*min
        (ENNReal.ofReal (C*qUpper^3*(min θ σ)^2)*(volume (Icc a b)*
          ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)))
        (coneOccupation F.flow zX T s.f
          (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))/
            ENNReal.ofReal (B.rmin^2*B.Dmin)) := by
  have hb := F.direct_transport_near_far hs hT zX B hS hS0 hJ hp hθ hφ hq hdlo hdhi hDhi hr hD hdensity
  have he : 128*(θ+φ)/(p^2*θ^3)=128/(p^2*θ^2)+128*φ/(p^2*θ^3) := by field_simp
  rw [he,ENNReal.ofReal_add (by positivity) (by positivity),add_mul] at hb
  exact hb.trans (add_le_add (mul_le_mul' le_rfl (min_le_left _ _)) le_rfl)

lemma Admissible.direct_transport_split_relative_budget {d : Datum} (hd₀ : Admissible d) :
    ∃Cρ : ℝ,0 ≤ Cρ ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (B : ClosedConeBin) (S : Set Phase)
        (M A P L a b massScale φ θ σ Cs p len I : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → 0 < p → 0 < len → len ≤ I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale →
      0 < φ → 0 < θ → 0 < σ → σ ≤ 1 → 128 ≤ Cs →
      2*len ≤ (Cs*(P/massScale)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2 →
      p/128 ≤ B.qmin → B.qmax ≤ p/32 → massScale ≤ B.qmin → massScale ≤ B.wmin →
      0 < B.rmin → 0 ≤ B.rmax → 0 < B.Dmin →
      θ^2/2 ≤ B.dmin → B.dmax ≤ 8*θ^2 → B.Dmax ≤ 8*φ^2 →
      σ^2/2 ≤ B.emin → B.emax ≤ 8*σ^2 → 4 ≤ σ*B.qmin → 4 ≤ σ*B.wmin →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let E := ∫x : Vec,totalEnergy s (0,x)
      let H := ENNReal.ofReal (Cρ*p^3*(min θ σ)^2)*(volume (Icc a b)*
        ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2))
      let O := (ENNReal.ofReal (30720*B.rmax/p*(1+φ/σ)*(1+I/len))*ENNReal.ofReal E)/
        ENNReal.ofReal (B.rmin^2*B.Dmin)
      (∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V B z ∂physicalBinMeasure V B (Icc a b))≤
        ENNReal.ofReal (128/((p/128)^2*θ^2))*H+
          ENNReal.ofReal (128*φ/((p/128)^2*θ^3))*min H O := by
  obtain ⟨Cρ,hCρ,hforce⟩ := hd₀.direct_transport_relative_budget
  refine ⟨Cρ,hCρ,?_⟩
  intro s T F hs hT h0 zX B S M A P L a b massScale φ θ σ Cs p len I
    hS hS0 ha hb hab hp hlen hlenI hJI hM hA hP hL hm hφ hθ hσ hσ1 hCs hstable
    hqmin hqmax hmq hmw hr hrmax hD hdlo hdhi hDhi helo hehi hq hw HX HZ
  have hh := hforce s T F hs hT h0 zX B S M A P L a b massScale φ θ σ Cs p len I
    hS hS0 ha hb hab hp hlen hlenI hJI hM hA hP hL hm hφ hθ hσ hσ1 hCs hstable
    hqmin hqmax hmq hmw hr hrmax hD hdlo hdhi hDhi helo hehi hq hw HX HZ
  dsimp only at hh ⊢
  have he : 128*(θ+φ)/((p/128)^2*θ^3)=128/((p/128)^2*θ^2)+128*φ/((p/128)^2*θ^3) := by
    field_simp
  rw [he,ENNReal.ofReal_add (by positivity) (by positivity),add_mul] at hh
  exact hh.trans (add_le_add (mul_le_mul' le_rfl (min_le_left _ _)) le_rfl)

end RVM

end

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
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma measurable_forceTransportKernel (r : ℝ) (n a : Vec) :
    Measurable (fun v : Vec=>forceTransportKernel r n a v) := by
  have hu : Measurable velocity := (contDiff_velocity (k:=0)).continuous.measurable
  have hq : Measurable q := (contDiff_q (k:=0)).continuous.measurable
  have hd : Measurable (fun v : Vec=>1-dot n (velocity v)) :=
    measurable_const.sub (continuous_dot.measurable.comp (measurable_const.prodMk hu))
  have hQ : Measurable (fun v : Vec=>receiverQCLM a n (n-velocity v)) :=
    (receiverQCLM a n).continuous.measurable.comp (measurable_const.sub hu)
  have hm := (((measurable_const (a:=r^2)).mul (hq.pow_const 2)).mul (hd.pow_const 2)).inv.smul hQ
  convert hm using 1
  funext v
  simp only [forceTransportKernel,Pi.smul_apply',Pi.inv_apply,Pi.mul_apply,receiverQCLM_apply]

lemma measurable_forceSourceKernel_lorentz (r : ℝ) (n a E B : Vec) :
    Measurable (fun v : Vec=>forceSourceKernel r n a v
      (fderiv ℝ velocity v (E+cross (velocity v) B))) := by
  have hu : Measurable velocity := (contDiff_velocity (k:=0)).continuous.measurable
  have hq : Measurable q := (contDiff_q (k:=0)).continuous.measurable
  have hK : Measurable (fun v : Vec=>E+cross (velocity v) B) :=
    measurable_const.add ((contDiff_cross (k:=0)).continuous.measurable.comp (hu.prodMk measurable_const))
  have hb := hq.inv.smul (hK.sub ((continuous_dot.measurable.comp (hu.prodMk hK)).smul hu))
  have hd : Measurable (fun v : Vec=>1-dot n (velocity v)) :=
    measurable_const.sub (continuous_dot.measurable.comp (measurable_const.prodMk hu))
  have hNum : Measurable (fun v : Vec=>
      dot n ((q v)⁻¹ • ((E+cross (velocity v) B)-dot (velocity v) (E+cross (velocity v) B) • velocity v)) •
        (n-velocity v)-(1-dot n (velocity v)) •
          ((q v)⁻¹ • ((E+cross (velocity v) B)-dot (velocity v) (E+cross (velocity v) B) • velocity v))) :=
    ((continuous_dot.measurable.comp (measurable_const.prodMk hb)).smul
      (measurable_const.sub hu)).sub (hd.smul hb)
  have hQ := (receiverQCLM a n).continuous.measurable.comp hNum
  have hm := ((measurable_const (a:=r)).mul (hd.pow_const 2)).inv.smul hQ
  convert hm using 1
  funext v
  simp only [forceSourceKernel,sourceNumerator,fderiv_velocity_apply,
    Pi.smul_apply',Pi.inv_apply,Pi.mul_apply,Function.comp_apply,receiverQCLM_apply]

lemma physicalDirectTransportDensity_relative_cover {s : Solution} {X V : ℝ→Vec}
    (B : ClosedConeBin) (z : ConeCoordinate) {N : ℕ} (hN : 1024*B.qmax≤(2:ℝ)^N)
    (hf : Measurable (fun v : Vec=>s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v)))) :
    physicalDirectTransportDensity s X V B z≤
      ∑j∈Finset.range N,physicalDirectTransportDensity s X V (relativeBinRefinement B j) z := by
  let g := fun v : Vec=>ENNReal.ofReal ‖s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v)) •
    forceTransportKernel (z.1-z.2.1) z.2.2.1 (velocity (V z.1)) v‖
  have hg : Measurable g := (hf.smul (measurable_forceTransportKernel _ _ _)).norm.ennreal_ofReal
  have hc := lintegral_coneBin_relative_cover B z.2.2.1 (V z.1) hN hg
  unfold physicalDirectTransportDensity
  dsimp only
  change ENNReal.ofReal ((z.1-z.2.1)^2)*(∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),g v)≤_
  apply (mul_le_mul' le_rfl hc).trans_eq
  exact Finset.mul_sum _ _ _

lemma physicalDirectSourceDensity_relative_cover {s : Solution} {X V : ℝ→Vec}
    (B : ClosedConeBin) (z : ConeCoordinate) {N : ℕ} (hN : 1024*B.qmax≤(2:ℝ)^N)
    (hf : Measurable (fun v : Vec=>s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v)))) :
    physicalDirectSourceDensity s X V B z≤
      ∑j∈Finset.range N,physicalDirectSourceDensity s X V (relativeBinRefinement B j) z := by
  let y := X z.1-(z.1-z.2.1) • z.2.2.1
  let g := fun v : Vec=>ENNReal.ofReal ‖s.f (z.2.1,(y,v)) •
    forceSourceKernel (z.1-z.2.1) z.2.2.1 (velocity (V z.1)) v
      (fderiv ℝ velocity v (s.E (z.2.1,y)+cross (velocity v) (s.B (z.2.1,y))))‖
  have hg : Measurable g := (hf.smul (measurable_forceSourceKernel_lorentz _ _ _ _ _)).norm.ennreal_ofReal
  have hc := lintegral_coneBin_relative_cover B z.2.2.1 (V z.1) hN hg
  unfold physicalDirectSourceDensity
  dsimp only
  change ENNReal.ofReal ((z.1-z.2.1)^2)*(∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),g v)≤_
  apply (mul_le_mul' le_rfl hc).trans_eq
  exact Finset.mul_sum _ _ _

lemma measurable_forceTransportFamily {α : Type*} [MeasurableSpace α]
    {r : α→ℝ} {n a v : α→Vec} (hr : Measurable r) (hn : Measurable n)
    (ha : Measurable a) (hv : Measurable v) :
    Measurable (fun x=>forceTransportKernel (r x) (n x) (a x) (v x)) := by
  have hu := (contDiff_velocity (k:=0)).continuous.measurable.comp hv
  have hq := (contDiff_q (k:=0)).continuous.measurable.comp hv
  have hd : Measurable (fun x=>1-dot (n x) (velocity (v x))) :=
    measurable_const.sub (continuous_dot.measurable.comp (hn.prodMk hu))
  have hD : Measurable (fun x=>1-dot (n x) (a x)) :=
    measurable_const.sub (continuous_dot.measurable.comp (hn.prodMk ha))
  unfold forceTransportKernel receiverQ
  exact (((hr.pow_const 2).mul (hq.pow_const 2)).mul (hd.pow_const 2)).inv.smul
    ((hD.smul (hn.sub hu)).add ((continuous_dot.measurable.comp (ha.prodMk (hn.sub hu))).smul hn))

lemma measurable_forceSourceFamily {α : Type*} [MeasurableSpace α]
    {r : α→ℝ} {n a v b : α→Vec} (hr : Measurable r) (hn : Measurable n)
    (ha : Measurable a) (hv : Measurable v) (hb : Measurable b) :
    Measurable (fun x=>forceSourceKernel (r x) (n x) (a x) (v x) (b x)) := by
  have hu := (contDiff_velocity (k:=0)).continuous.measurable.comp hv
  have hd : Measurable (fun x=>1-dot (n x) (velocity (v x))) :=
    measurable_const.sub (continuous_dot.measurable.comp (hn.prodMk hu))
  have hD : Measurable (fun x=>1-dot (n x) (a x)) :=
    measurable_const.sub (continuous_dot.measurable.comp (hn.prodMk ha))
  have hN : Measurable (fun x=>sourceNumerator (n x) (velocity (v x)) (b x)) :=
    ((continuous_dot.measurable.comp (hn.prodMk hb)).smul (hn.sub hu)).sub (hd.smul hb)
  unfold forceSourceKernel receiverQ
  exact ((hr.mul (hd.pow_const 2)).inv.smul
    ((hD.smul hN).add ((continuous_dot.measurable.comp (ha.prodMk hN)).smul hn)))

lemma measurable_lorentz_acceleration {α : Type*} [MeasurableSpace α]
    {v E B : α→Vec} (hv : Measurable v) (hE : Measurable E) (hB : Measurable B) :
    Measurable (fun x=>fderiv ℝ velocity (v x) (E x+cross (velocity (v x)) (B x))) := by
  have hu := (contDiff_velocity (k:=0)).continuous.measurable.comp hv
  have hq := (contDiff_q (k:=0)).continuous.measurable.comp hv
  have hK := hE.add ((contDiff_cross (k:=0)).continuous.measurable.comp (hu.prodMk hB))
  simp_rw [fderiv_velocity_apply]
  exact hq.inv.smul (hK.sub ((continuous_dot.measurable.comp (hu.prodMk hK)).smul hu))

lemma measurable_coneBin_kernelDensity {g : Particle} (hg : Measurable g)
    {X V : ℝ→Vec} (hX : Measurable X) (hV : Measurable V) (B : ClosedConeBin)
    {K : ConeCoordinate×Vec→Vec} (hK : Measurable K) :
    Measurable (fun z : ConeCoordinate=>∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal ‖g (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v)) • K (z,v)‖) := by
  let H : Set (ConeCoordinate×Vec) :=
    {p | p.2∈coneBinMomentumSet B p.1.2.2.1 (velocity (V p.1.1))}
  have hn : Measurable (fun p : ConeCoordinate×Vec=>p.1.2.2.1) :=
    measurable_subtype_coe.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hv : Measurable (fun p : ConeCoordinate×Vec=>velocity p.2) :=
    (contDiff_velocity (k:=0)).continuous.measurable.comp measurable_snd
  have ha : Measurable (fun p : ConeCoordinate×Vec=>velocity (V p.1.1)) :=
    (contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp (measurable_fst.comp measurable_fst))
  have hH : MeasurableSet H := by
    exact (measurableSet_Icc.preimage ((contDiff_q (k:=0)).continuous.measurable.comp measurable_snd)).inter
      ((measurableSet_Icc.preimage (measurable_const.sub (continuous_dot.measurable.comp (hn.prodMk hv)))).inter
        (measurableSet_Icc.preimage (measurable_const.sub (continuous_dot.measurable.comp (ha.prodMk hv)))))
  have hf : Measurable (fun p : ConeCoordinate×Vec=>
      g (p.1.2.1,(X p.1.1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2))) := by
    exact hg.comp ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
      (((hX.comp (measurable_fst.comp measurable_fst)).sub
        (((measurable_fst.comp measurable_fst).sub (measurable_fst.comp (measurable_snd.comp measurable_fst))).smul hn)).prodMk measurable_snd))
  have hm : Measurable (fun z : ConeCoordinate=>∫⁻v : Vec,H.indicator
      (fun p=>ENNReal.ofReal ‖g (p.1.2.1,(X p.1.1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2)) • K p‖) (z,v)) :=
    (((hf.smul hK).norm.ennreal_ofReal).indicator hH).lintegral_prod_right'
  convert hm using 1
  ext z
  rw [←lintegral_indicator (measurableSet_coneBinMomentumSet B _ _)]
  apply lintegral_congr
  intro v
  rfl

lemma physicalDirectTransportDensity_aemeasurable {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) {X V : ℝ→Vec} (hX : Measurable X) (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) :
    AEMeasurable (physicalDirectTransportDensity s X V B) (physicalBinMeasure V B J) := by
  have ht : Measurable (fun p : ConeCoordinate×Vec=>p.1.1) := measurable_fst.comp measurable_fst
  have hσ : Measurable (fun p : ConeCoordinate×Vec=>p.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hn : Measurable (fun p : ConeCoordinate×Vec=>p.1.2.2.1) :=
    measurable_subtype_coe.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hK := measurable_forceTransportFamily (ht.sub hσ) hn
    ((contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp ht)) measurable_snd
  have hm := measurable_coneBin_kernelDensity (hs.continuous_prefixParticle hT).measurable hX hV B hK
  have hR : Measurable (fun z : ConeCoordinate=>ENNReal.ofReal ((z.1-z.2.1)^2)) :=
    ((measurable_fst.sub (measurable_fst.comp measurable_snd)).pow_const 2).ennreal_ofReal
  apply (hR.mul hm).aemeasurable.congr
  apply ae_restrict_of_forall_mem (measurableSet_physicalBinBase hV B hJ)
  intro z hz
  unfold physicalDirectTransportDensity
  dsimp only [Pi.mul_apply]
  congr 1
  apply lintegral_congr
  intro v
  rw [prefixParticle,prefixClamp_eq (show z.2.1∈Icc 0 T from ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩)]
  rfl

lemma physicalDirectSourceDensity_aemeasurable {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) {X V : ℝ→Vec} (hX : Measurable X) (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) :
    AEMeasurable (physicalDirectSourceDensity s X V B) (physicalBinMeasure V B J) := by
  have ht : Measurable (fun p : ConeCoordinate×Vec=>p.1.1) := measurable_fst.comp measurable_fst
  have hσ : Measurable (fun p : ConeCoordinate×Vec=>p.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hn : Measurable (fun p : ConeCoordinate×Vec=>p.1.2.2.1) :=
    measurable_subtype_coe.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hy := hσ.prodMk ((hX.comp ht).sub ((ht.sub hσ).smul hn))
  have hb := measurable_lorentz_acceleration measurable_snd
    ((continuous_prefixField hs.E_smooth.continuousOn hT).measurable.comp hy)
    ((continuous_prefixField hs.B_smooth.continuousOn hT).measurable.comp hy)
  have hK := measurable_forceSourceFamily (ht.sub hσ) hn
    ((contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp ht)) measurable_snd hb
  have hm := measurable_coneBin_kernelDensity (hs.continuous_prefixParticle hT).measurable hX hV B hK
  have hR : Measurable (fun z : ConeCoordinate=>ENNReal.ofReal ((z.1-z.2.1)^2)) :=
    ((measurable_fst.sub (measurable_fst.comp measurable_snd)).pow_const 2).ennreal_ofReal
  apply (hR.mul hm).aemeasurable.congr
  apply ae_restrict_of_forall_mem (measurableSet_physicalBinBase hV B hJ)
  intro z hz
  unfold physicalDirectSourceDensity
  dsimp only [Pi.mul_apply]
  congr 1
  apply lintegral_congr
  intro v
  dsimp only [Pi.sub_apply,Pi.smul_apply',Function.comp_apply]
  simp only [prefixParticle,prefixField,prefixClamp_eq
    (show z.2.1∈Icc 0 T from ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩)]

lemma EnergyPrefix.measurable_velocity_slice {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) {σ : ℝ} (hσ : σ∈Icc 0 T) (y : Vec) :
    Measurable (fun v : Vec=>s.f (σ,(y,v))) := by
  exact (hs.f_smooth.continuousOn.comp_continuous
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    (fun _=>⟨hσ,mem_univ _⟩)).measurable

lemma physicalDirectTransport_integral_relative_cover {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) {X V : ℝ→Vec} (hX : Measurable X) (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    {N : ℕ} (hN : 1024*B.qmax≤(2:ℝ)^N) :
    (∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V B z ∂physicalBinMeasure V B J)≤
      ∑j∈Finset.range N,∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V (relativeBinRefinement B j) z
        ∂physicalBinMeasure V (relativeBinRefinement B j) J := by
  have hp : (∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V B z ∂physicalBinMeasure V B J)≤
      ∫⁻z : ConeCoordinate,∑j∈Finset.range N,physicalDirectTransportDensity s X V (relativeBinRefinement B j) z
        ∂physicalBinMeasure V B J := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV B hJ)] with z hz
    exact physicalDirectTransportDensity_relative_cover B z hN
      (hs.measurable_velocity_slice ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩ _)
  apply hp.trans_eq
  exact lintegral_finsetSum' _ (fun j _=>
    physicalDirectTransportDensity_aemeasurable hs hT hX hV (relativeBinRefinement B j) hJ hJT)

lemma physicalDirectSource_integral_relative_cover {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) {X V : ℝ→Vec} (hX : Measurable X) (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    {N : ℕ} (hN : 1024*B.qmax≤(2:ℝ)^N) :
    (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z ∂physicalBinMeasure V B J)≤
      ∑j∈Finset.range N,∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (relativeBinRefinement B j) z
        ∂physicalBinMeasure V (relativeBinRefinement B j) J := by
  have hp : (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z ∂physicalBinMeasure V B J)≤
      ∫⁻z : ConeCoordinate,∑j∈Finset.range N,physicalDirectSourceDensity s X V (relativeBinRefinement B j) z
        ∂physicalBinMeasure V B J := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV B hJ)] with z hz
    exact physicalDirectSourceDensity_relative_cover B z hN
      (hs.measurable_velocity_slice ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩ _)
  apply hp.trans_eq
  exact lintegral_finsetSum' _ (fun j _=>
    physicalDirectSourceDensity_aemeasurable hs hT hX hV (relativeBinRefinement B j) hJ hJT)

end RVM

end

end OAI
