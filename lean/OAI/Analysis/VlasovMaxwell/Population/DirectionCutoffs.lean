import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.PhysicalProjectedRemainderSourceTruncate
import OAI.Analysis.VlasovMaxwell.Retarded.DirectForce
import OAI.Analysis.VlasovMaxwell.Retarded.SourceMajorantFamily

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

lemma Admissible.central_density_low_receiver_log_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (a b w P : ℝ),
      0 ≤ a → b ≤ T → b-a ≤ (w/P)^2 → 0<w → P ≤ w^2 → 0<P →
      1 ≤ Real.log (2+P) →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2 ≤ P) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let sector : Set (Fin 4→ℕ) := {k | cappedRepresentative (k 2)*w ≤ 32}
      (∑'k : Fin 4→ℕ,sector.indicator (fun k=>
        ENNReal.ofReal (78400000*(cappedRepresentative (k 2))^2/cappedRepresentative (k 1))*
        (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k)
          z.1 z.2.1 z.2.2 ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b))) k) ≤
      ENNReal.ofReal (C*max 1 T*w*(Real.log (2+P))^2) := by
  classical
  obtain ⟨Cρ,hCρ,hnear⟩ := hd₀.central_density_near_bin
  obtain ⟨Cn,hCn,hcount⟩ := exists_source_dyadic_count
  refine ⟨12*128^3*32^3*Cρ*Cn^2,by positivity,?_⟩
  intro s T F hs hT h0 zX a b w P ha hb hab hw hPw hP hL hsource
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let I := (w/P)^2
  let sector : Set (Fin 4→ℕ) := {k | cappedRepresentative (k 2)*w ≤ 32}
  let cfun := fun k : Fin 4→ℕ=>
    ENNReal.ofReal (78400000*(cappedRepresentative (k 2))^2/cappedRepresentative (k 1))*
    (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k)
      z.1 z.2.1 z.2.2 ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b))
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  let source : Set (Fin 4→ℕ) := {k | k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0) ≤ 128*P}
  let f := (source∩sector).indicator cfun
  let c := 6*128^3*32^3*Cρ*max 1 T*w
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have heq : sector.indicator cfun=f := by
    funext k
    by_cases hk : k∈sector
    · by_cases hsrc : k∈source
      · rw [indicator_of_mem hk,show f k=cfun k from indicator_of_mem (show k∈source∩sector from ⟨hsrc,hk⟩) cfun]
      · rw [indicator_of_mem hk,show f k=0 from indicator_of_notMem (fun h=>hsrc h.1) cfun]
        dsimp [cfun]
        rw [F.physicalBinDensity_integral_source_truncate hs hsource N hN X V
          hα.snd.measurable measurableSet_Icc hJ w k hsrc,mul_zero]
    · rw [indicator_of_notMem hk,show f k=0 from indicator_of_notMem (fun h=>hk h.2) cfun]
  have hvol : volume (Icc a b) ≤ ENNReal.ofReal I := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal hab
  have hrad (np nt nf : ℕ) : (∑'nr,f ![np,nt,nf,nr]) ≤
      (if np<N ∧ nt<N then ENNReal.ofReal c*ENNReal.ofReal ((2:ℝ)⁻¹^nf) else 0) := by
    by_cases hidx : np<N ∧ nt<N
    · rw [ite_eq_left hidx]
      let φ := cappedRepresentative nf
      have hφ : 0<φ := cappedRepresentative_pos _
      let coeff := Cρ*I*(128*P)^3*(32/w)^3*φ
      have hcoeff : 0 ≤ coeff := by dsimp [coeff,I]; positivity
      have hpoint (nr : ℕ) : f ![np,nt,nf,nr] ≤
          ENNReal.ofReal coeff*ENNReal.ofReal (max 1 T*cappedRepresentative nr) := by
        let k : Fin 4→ℕ := ![np,nt,nf,nr]
        by_cases hk : k∈source∩sector
        · have hlowφ : φ ≤ 32/w := (le_div_iff₀ hw).mpr hk.2
          change (source∩sector).indicator cfun k ≤ _
          rw [indicator_of_mem hk]
          have hh := hnear s T F hs hT h0 zX k (Icc a b) I w measurableSet_Icc hJ
            (by dsimp [I]; positivity) hvol
          apply hh.trans
          rw [←ENNReal.ofReal_mul hcoeff]
          apply ENNReal.ofReal_le_ofReal
          have hp : 0  ≤  sourceRepresentative np := by dsimp [sourceRepresentative]; positivity
          have hpbound : sourceRepresentative np ≤ 128*P := hk.1.2.2
          have hθ : 0 ≤ cappedRepresentative nt := (cappedRepresentative_pos _).le
          have hθ1 : cappedRepresentative nt ≤ 1 := cappedRepresentative_le_one _
          have hr : 0 ≤ max 1 T*cappedRepresentative nr :=
            mul_nonneg (zero_le_one.trans (le_max_left _ _)) (cappedRepresentative_pos _).le
          have hφ4 : φ^4 ≤ (32/w)^3*φ := by
            calc
              φ^4=φ^3*φ := by ring
              _ ≤ (32/w)^3*φ := mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ hφ.le hlowφ 3) hφ.le
          change Cρ*I*(sourceRepresentative np)^3*cappedRepresentative nt*φ^4*
            (max 1 T*cappedRepresentative nr) ≤ coeff*(max 1 T*cappedRepresentative nr)
          dsimp [coeff]
          calc
            _  ≤  Cρ*I*(128*P)^3*1*((32/w)^3*φ)*(max 1 T*cappedRepresentative nr) := by gcongr
            _ = _ := by ring
        · change (source∩sector).indicator cfun k ≤ _
          rw [indicator_of_notMem hk]
          exact bot_le
      have hsum := ENNReal.tsum_le_tsum hpoint
      rw [ENNReal.tsum_mul_left] at hsum
      have ht := capped_radius_tail (H:=max 1 T) (zero_lt_one.trans_le (le_max_left _ _))
        (show 0 ≤ max 1 T from zero_le_one.trans (le_max_left _ _))
      have hall (n : ℕ) : max 1 T*cappedRepresentative n ≤ max 1 T :=
        mul_le_of_le_one_right (zero_le_one.trans (le_max_left _ _)) (cappedRepresentative_le_one n)
      simp_rw [ite_eq_left (hall _)] at ht
      apply (hsum.trans (mul_le_mul' le_rfl ht)).trans
      rw [←ENNReal.ofReal_mul hcoeff,←ENNReal.ofReal_mul hc]
      apply ENNReal.ofReal_le_ofReal
      have hratio : P/w ≤ w := (div_le_iff₀ hw).mpr (by nlinarith only [hPw])
      calc
        _ = (6*128^3*32^3*Cρ*max 1 T*φ)*(P/w) := by
          dsimp [coeff,I]
          field_simp
        _ ≤ (6*128^3*32^3*Cρ*max 1 T*φ)*w := mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = _ := by dsimp [c,φ,cappedRepresentative]; ring
    · have hz (nr : ℕ) : f ![np,nt,nf,nr]=0 := by
        apply indicator_of_notMem
        intro hk
        exact hidx ⟨hk.1.1,hk.1.2.1⟩
      simp only [hz,tsum_zero,ite_eq_right hidx,le_refl]
  change (∑'k : Fin 4→ℕ,sector.indicator cfun k) ≤ _
  rw [heq]
  apply (tsum_quad_of_radial_bound f N (ENNReal.ofReal c) hrad).trans
  have heN : (2:ℝ≥0∞)*(N:ℝ≥0∞)^2=ENNReal.ofReal (2*(N:ℝ)^2) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      ENNReal.ofReal_pow (Nat.cast_nonneg N),ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat]
  rw [heN,←ENNReal.ofReal_mul hc]
  apply ENNReal.ofReal_le_ofReal
  calc
    _  ≤  c*(2*(Cn*Real.log (2+P))^2) := by gcongr
    _ = _ := by dsimp [c]; ring

lemma Admissible.central_density_small_sector_log_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → b-a≤(w/P)^2 →
      0<M → 0≤A → 0<P → 1≤Real.log (2+P) → 0<w → w≤P → P≤w^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let sector : Set (Fin 4→ℕ) := {k |
        cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16}
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'k : Fin 4→ℕ,sector.indicator (fun k=>
        ENNReal.ofReal (78400000*(cappedRepresentative (k 2))^2/cappedRepresentative (k 1))*
        (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k)
          z.1 z.2.1 z.2.2 ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b))) k)≤
      ENNReal.ofReal (C*max 1 T*(1+E)*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^3) := by
  classical
  obtain ⟨Cs,hCs,hstable⟩ := hd₀.central_density_stable_log_sum
  obtain ⟨Cl,hCl,hlow⟩ := hd₀.central_density_low_receiver_log_sum
  refine ⟨Cs+Cl,add_nonneg hCs hCl,?_⟩
  intro s T F hs hT h0 zX S a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP hPw hsource HX HZ
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let E := ∫x : Vec,totalEnergy s (0,x)
  let L := Real.log (2+P)
  let B := 1+16384*(M+Real.sqrt A)
  let H := max 1 T
  let sector : Set (Fin 4→ℕ) := {k | cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16}
  let high : Set (Fin 4→ℕ) := {k | k∈sector ∧ 32≤cappedRepresentative (k 2)*w}
  let low : Set (Fin 4→ℕ) := {k | cappedRepresentative (k 2)*w≤32}
  let f := fun k : Fin 4→ℕ=>
    ENNReal.ofReal (78400000*(cappedRepresentative (k 2))^2/cappedRepresentative (k 1))*
    (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k)
      z.1 z.2.1 z.2.2 ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b))
  have hsumb : (∑'k : Fin 4→ℕ,sector.indicator f k)≤
      (∑'k : Fin 4→ℕ,high.indicator f k)+(∑'k : Fin 4→ℕ,low.indicator f k) := by
    rw [←ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro k
    by_cases hk : k∈sector
    · rw [indicator_of_mem hk]
      by_cases hh : 32≤cappedRepresentative (k 2)*w
      · rw [indicator_of_mem (show k∈high from ⟨hk,hh⟩)]
        exact le_self_add
      · rw [indicator_of_mem (show k∈low from (lt_of_not_ge hh).le)]
        exact le_add_self
    · rw [indicator_of_notMem hk]
      exact bot_le
  have hh : (∑'k : Fin 4→ℕ,high.indicator f k)≤
      ENNReal.ofReal (Cs*(1+E)*B*w*L^3) :=
    hstable s T F hs hT h0 zX S a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP hsource HX HZ
  have hl : (∑'k : Fin 4→ℕ,low.indicator f k)≤ENNReal.ofReal (Cl*H*w*L^2) :=
    hlow s T F hs hT h0 zX a b w P ha hb hab hw hPw hP hL hsource
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hE1 : 1≤1+E := by linarith only [hE]
  have hB1 : 1≤B := by dsimp [B]; linarith only [hM,Real.sqrt_nonneg A]
  have hH1 : 1≤H := le_max_left _ _
  have hH0 : 0≤H := zero_le_one.trans hH1
  have hB0 : 0≤B := zero_le_one.trans hB1
  have hL0 : 0≤L := zero_le_one.trans hL
  have hL23 : L^2≤L^3 := by nlinarith only [mul_le_mul_of_nonneg_left hL (sq_nonneg L)]
  change (∑'k : Fin 4→ℕ,sector.indicator f k)≤_
  apply (hsumb.trans (add_le_add hh hl)).trans
  rw [←ENNReal.ofReal_add (by positivity : 0≤Cs*(1+E)*B*w*L^3) (by positivity : 0≤Cl*H*w*L^2)]
  apply ENNReal.ofReal_le_ofReal
  have hh' : Cs*(1+E)*B*w*L^3≤Cs*H*(1+E)*B*w*L^3 := by
    calc
      _ = Cs*1*(1+E)*B*w*L^3 := by ring
      _ ≤ _ := by gcongr
  have hl' : Cl*H*w*L^2≤Cl*H*(1+E)*B*w*L^3 := by
    calc
      _ = Cl*H*1*1*w*L^2 := by ring
      _ ≤ _ := by gcongr
  calc
    _ ≤ Cs*H*(1+E)*B*w*L^3+Cl*H*(1+E)*B*w*L^3 := add_le_add hh' hl'
    _ = _ := by dsimp [H,E,B,L]; ring

lemma Admissible.geometry_cutoff_small_sector_log_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → b-a≤(w/P)^2 →
      0<M → 0≤A → 0<P → 1≤Real.log (2+P) → 0<w → w≤P → P≤w^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let sector : Set (Fin 4→ℕ) := {k |
        cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16}
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'k : Fin 4→ℕ,sector.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalGeometryCutoffDensity s X V (representativeClosedBin T w k) T w Q z
          ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k)≤
      ENNReal.ofReal (C*max 1 T*(1+E)*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^3) := by
  classical
  obtain ⟨C,hC,hsum⟩ := hd₀.central_density_small_sector_log_sum
  obtain ⟨c,hc,hcut⟩ := dyadicFactor_log_derivative_bound
  refine ⟨c*C,by positivity,?_⟩
  intro s T F hs hT h0 zX S Q a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP hPw hsource hband HX HZ
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let sector : Set (Fin 4→ℕ) := {k |
    cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16}
  let f := fun k : Fin 4→ℕ=>
    ENNReal.ofReal (78400000*(cappedRepresentative (k 2))^2/cappedRepresentative (k 1))*
    (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k)
      z.1 z.2.1 z.2.2 ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b))
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hband' : ∀t∈Icc a b,w/16≤‖V t‖ := by
    intro t ht
    simpa only [V,prefixFlow,prefixClamp_eq (hJ ht)] using hband t ht
  have hbnd (k : Fin 4→ℕ) (hk : k∈sector) :
      (∫⁻z : ConeCoordinate,physicalGeometryCutoffDensity s X V (representativeClosedBin T w k) T w Q z
        ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b))≤ENNReal.ofReal c*f k := by
    let θ := cappedRepresentative (k 1)
    let φ := cappedRepresentative (k 2)
    have hθ : 0<θ := cappedRepresentative_pos _
    have hφ : 0<φ := cappedRepresentative_pos _
    have hsmall : (representativeClosedBin T w k).dmax≤(representativeClosedBin T w k).Dmin := by
      change 8*θ^2≤φ^2/2
      have hh : θ≤φ/16 := hk
      have hh2 := (sq_le_sq₀ hθ.le (by positivity : 0≤φ/16)).mpr hh
      nlinarith only [hh2]
    have hh := physicalGeometryCutoff_integral_bound (X:=X) hs hα.snd.measurable
      (representativeClosedBin T w k) measurableSet_Icc hJ hc hcut hw hθ hφ.le hsmall
      (representativeClosedBin_radius_pos T w k) le_rfl le_rfl hband' Q
    have he : 78400000*c*φ^2/θ=c*(78400000*φ^2/θ) := by ring
    rw [he,ENNReal.ofReal_mul hc,mul_assoc] at hh
    exact hh
  have hs1 : (∑'k : Fin 4→ℕ,sector.indicator (fun k=>∫⁻z : ConeCoordinate,
      physicalGeometryCutoffDensity s X V (representativeClosedBin T w k) T w Q z
        ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k)≤
      ∑'k : Fin 4→ℕ,ENNReal.ofReal c*sector.indicator f k := by
    apply ENNReal.tsum_le_tsum
    intro k
    by_cases hk : k∈sector
    · simpa only [indicator_of_mem hk] using hbnd k hk
    · simp only [indicator_of_notMem hk,mul_zero,le_refl]
  rw [ENNReal.tsum_mul_left] at hs1
  have hs2 := hsum s T F hs hT h0 zX S a b w M A P hS hS0 ha hb hab
    hM hA hP hL hw hwP hPw hsource HX HZ
  apply hs1.trans ((mul_le_mul' le_rfl hs2).trans_eq _)
  rw [←ENNReal.ofReal_mul hc]
  congr 1
  ring

lemma Admissible.projected_remainder_small_sector_log_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → b-a≤(w/P)^2 →
      0<M → 0≤A → 0<P → 1≤Real.log (2+P) → 0<w → w≤P → P≤w^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let K := prefixMomentumForce s F.flow T zX
      let sector : Set (Fin 4→ℕ) := {k |
        cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 ∧
        sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1}
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'k : Fin 4→ℕ,sector.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalProjectedRemainderDensity s X V (representativeClosedBin T w k) w K z
          ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k)≤
      ENNReal.ofReal (C*max 1 T*(1+E)*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^3)+
      (∫⁻t in Icc a b,ENNReal.ofReal ‖K t‖)*
        ENNReal.ofReal (C*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w) := by
  classical
  obtain ⟨Cs,hCs,hcentral⟩ := hd₀.central_density_small_sector_log_sum
  obtain ⟨Cr,hCr,hremainder⟩ := hd₀.projected_remainder_selected_sum
  obtain ⟨Cn,hCn,hcount⟩ := exists_source_dyadic_count
  let C := Cs+Cr*Cn^2
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX S a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP hPw hsource hband HX HZ
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let K := prefixMomentumForce s F.flow T zX
  let W := ∫⁻t in Icc a b,ENNReal.ofReal ‖K t‖
  let E := ∫x : Vec,totalEnergy s (0,x)
  let sector : Set (Fin 4→ℕ) := {k |
    cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 ∧
    sourceRepresentative (k 0)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1}
  let stable : Set (Fin 4→ℕ) := {k |
    cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16}
  let rfun := fun k : Fin 4→ℕ=>∫⁻z : ConeCoordinate,
    physicalProjectedRemainderDensity s X V (representativeClosedBin T w k) w K z
      ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)
  let cfun := fun k : Fin 4→ℕ=>
    ENNReal.ofReal (78400000*(cappedRepresentative (k 2))^2/cappedRepresentative (k 1))*
    (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k)
      z.1 z.2.1 z.2.2 ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b))
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  let source : Set (Fin 4→ℕ) := {k | k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0)≤128*P}
  let Q := source∩sector
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have heq : sector.indicator rfun=Q.indicator rfun := by
    funext k
    by_cases hk : k∈sector
    · by_cases hsrc : k∈source
      · rw [indicator_of_mem hk,indicator_of_mem (show k∈Q from ⟨hsrc,hk⟩)]
      · rw [indicator_of_mem hk,indicator_of_notMem (show k∉Q from fun h=>hsrc h.1)]
        exact F.physicalProjectedRemainder_integral_source_truncate hs hsource N hN X V K
          hα.snd.measurable measurableSet_Icc hJ w k hsrc
    · rw [indicator_of_notMem hk,indicator_of_notMem (show k∉Q from fun h=>hk h.2)]
  have hQ : ∀k∈Q,k 0<N ∧ k 1<N ∧ cappedRepresentative (k 1)≤cappedRepresentative (k 2) ∧
      sourceRepresentative (k 0)*cappedRepresentative (k 1)*
        Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1 := by
    intro k hk
    refine ⟨hk.1.1,hk.1.2.1,?_,hk.2.2⟩
    have hh := hk.2.1
    have hφ := cappedRepresentative_pos (k 2)
    linarith only [hh,hφ]
  have hcsub : (∑'k : Fin 4→ℕ,Q.indicator cfun k)≤∑'k : Fin 4→ℕ,stable.indicator cfun k := by
    apply ENNReal.tsum_le_tsum
    intro k
    by_cases hk : k∈Q
    · rw [indicator_of_mem hk,indicator_of_mem (show k∈stable from hk.2.1)]
    · rw [indicator_of_notMem hk]
      exact bot_le
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hL0 : 0≤Real.log (2+P) := zero_le_one.trans hL
  have hc : (∑'k : Fin 4→ℕ,Q.indicator cfun k)≤
      ENNReal.ofReal (C*max 1 T*(1+E)*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^3) := by
    apply (hcsub.trans (hcentral s T F hs hT h0 zX S a b w M A P hS hS0 ha hb hab
      hM hA hP hL hw hwP hPw hsource HX HZ)).trans
    apply ENNReal.ofReal_le_ofReal
    have hCsC : Cs≤C := by dsimp [C]; linarith only [mul_nonneg hCr (sq_nonneg Cn)]
    gcongr
  have hN2 : Cr*Real.sqrt (max 1 T)*(N:ℝ)^2/w≤C*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w := by
    apply div_le_div_of_nonneg_right _ hw.le
    calc
      _ ≤ Cr*Real.sqrt (max 1 T)*(Cn*Real.log (2+P))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg N) hNc _) (by positivity)
      _ = (Cr*Cn^2)*Real.sqrt (max 1 T)*(Real.log (2+P))^2 := by ring
      _ ≤ _ := by
        have hh : Cr*Cn^2≤C := by dsimp [C]; linarith only [hCs]
        gcongr
  change (∑'k : Fin 4→ℕ,sector.indicator rfun k)≤_
  rw [heq]
  exact (hremainder s T F hs hT h0 zX (Icc a b) w N Q hQ measurableSet_Icc hJ hw hband).trans
    (add_le_add hc (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hN2)))

lemma Admissible.projected_source_near_bin {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb c : ℝ,0≤Cg ∧ 0≤Cb ∧ 0≤c ∧
    ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (k : Fin 4→ℕ)
        (a b I w : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → 0<I → b-a≤I → 0<w →
      cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let r := max 1 T*cappedRepresentative (k 3)
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := representativeClosedBin T w k
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s X V B T w Q z
        ∂physicalBinMeasure V B (Icc a b))≤
      ENNReal.ofReal (128*(3840+94080000*c)*φ^2/(p*θ^2))*
        ((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
          ((ENNReal.ofReal (128*Cg*p^3*θ^2))^2*ENNReal.ofReal (768*I*r*φ^2))^(1/2:ℝ))+
      ENNReal.ofReal (128*(3840+94080000*c)*φ/p)*
        ((ENNReal.ofReal (40*(I+2*r)*E))^(1/2:ℝ)*
          ((ENNReal.ofReal (128*Cb*p^3*θ^2))^2*ENNReal.ofReal (768*I*r*φ^2))^(1/2:ℝ)) := by
  obtain ⟨Cg,Cb,c,hCg,hCb,hc,hsource⟩ := hd₀.projected_source_two_budget_bound
  refine ⟨Cg,Cb,c,hCg,hCb,hc,?_⟩
  intro s T F hs hT h0 zX S Q k a b I w hS hS0 ha hb hI hab hw hsmall hband
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
  have hE : 0 ≤ E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hdsmall : B.dmax ≤ φ^2/32 := by
    change 8*θ^2 ≤ φ^2/32
    have ht : θ ≤ φ/16 := hsmall
    nlinarith only [sq_le_sq₀ hθ.le (by positivity : 0 ≤ φ/16) |>.mpr ht]
  have hvol : volume (Icc a b)≤ENNReal.ofReal I := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal hab
  have hmeasure : volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)≤
      ENNReal.ofReal (768*I*r*φ^2) := by
    calc
      _ ≤ ENNReal.ofReal I*ENNReal.ofReal (2*r)*ENNReal.ofReal (384*φ^2) := by
        apply mul_le_mul' (mul_le_mul' hvol _) le_rfl
        apply ENNReal.ofReal_le_ofReal
        rw [hBmax,hBmin]
        linarith only [hr]
      _ = _ := by
        rw [←ENNReal.ofReal_mul hI.le,←ENNReal.ofReal_mul (by positivity : 0≤I*(2*r))]
        congr 1
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
    exact (min_le_left _ _).trans (mul_le_mul' le_rfl hmeasure)
  · apply mul_le_mul' le_rfl
    apply mul_le_mul' (ENNReal.rpow_le_rpow hmag (by norm_num))
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    exact (min_le_left _ _).trans (mul_le_mul' le_rfl hmeasure)

lemma sqrt_near_product {a b I E r φ D : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hI : 0≤I) (hE : 0≤E) (hr : 0≤r) (hφ : 0≤φ) (hD : 0≤D) :
    Real.sqrt (a*E)*Real.sqrt (D^2*(b*I*r*φ^2))=
      D*φ*Real.sqrt (a*I)*Real.sqrt (b*E)*Real.sqrt r := by
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hD]
  calc
    _ = D*Real.sqrt ((a*E)*(b*I*r*φ^2)) := by
      rw [Real.sqrt_mul (mul_nonneg ha hE)]
      ring
    _ = D*Real.sqrt ((a*I)*(b*E)*r*φ^2) := by congr 2; ring
    _ = _ := by
      rw [Real.sqrt_mul (by positivity : 0≤(a*I)*(b*E)*r),
        Real.sqrt_sq hφ,Real.sqrt_mul (by positivity : 0≤(a*I)*(b*E)),
        Real.sqrt_mul (mul_nonneg ha hI)]
      ring

lemma source_near_good_scalar {K C I E r φ p θ : ℝ}
    (hC : 0≤C) (hI : 0≤I) (hE : 0≤E) (hr : 0≤r) (hφ : 0≤φ)
    (hp : 0<p) (hθ : 0<θ) :
    (K*φ^2/(p*θ^2))*(Real.sqrt (20*I*E)*
      Real.sqrt ((128*C*p^3*θ^2)^2*(768*I*r*φ^2)))=
    (128*K*C*Real.sqrt 15360)*Real.sqrt E*I*p^2*φ^3*Real.sqrt r := by
  rw [sqrt_near_product (by positivity : 0≤20*I) (by norm_num : (0:ℝ)≤768)
    hI hE hr hφ (by positivity)]
  rw [show (20:ℝ)*I*I=20*(I:ℝ)^2 from by ring,Real.sqrt_mul (by norm_num : (0:ℝ)≤20),Real.sqrt_sq hI,
    Real.sqrt_mul (by norm_num : (0:ℝ)≤768)]
  have he : Real.sqrt (20:ℝ)*Real.sqrt 768=Real.sqrt 15360 := by
    rw [←Real.sqrt_mul (by norm_num : (0:ℝ)≤20)]
    norm_num
  calc
    _ = (128*K*C*(Real.sqrt 20*Real.sqrt 768))*Real.sqrt E*I*p^2*φ^3*Real.sqrt r := by
      field_simp
    _ = _ := by rw [he]

lemma source_near_magnetic_scalar {K C I E r φ p θ : ℝ}
    (hC : 0≤C) (hI : 0≤I) (hE : 0≤E) (hr : 0≤r) (hφ : 0≤φ)
    (hp : 0<p) :
    (K*φ/p)*(Real.sqrt (40*(I+2*r)*E)*
      Real.sqrt ((128*C*p^3*θ^2)^2*(768*I*r*φ^2)))=
    (128*K*C*Real.sqrt 30720)*Real.sqrt E*Real.sqrt I*Real.sqrt (I+2*r)*
      p^2*θ^2*φ^2*Real.sqrt r := by
  rw [sqrt_near_product (by positivity : 0≤40*(I+2*r)) (by norm_num : (0:ℝ)≤768)
    hI hE hr hφ (by positivity)]
  rw [Real.sqrt_mul (by positivity : 0≤40*(I+2*r)),
    Real.sqrt_mul (by norm_num : (0:ℝ)≤40),Real.sqrt_mul (by norm_num : (0:ℝ)≤768)]
  have he : Real.sqrt (40:ℝ)*Real.sqrt 768=Real.sqrt 30720 := by
    rw [←Real.sqrt_mul (by norm_num : (0:ℝ)≤40)]
    norm_num
  calc
    _ = (128*K*C*(Real.sqrt 40*Real.sqrt 768))*Real.sqrt E*Real.sqrt I*Real.sqrt (I+2*r)*
        p^2*θ^2*φ^2*Real.sqrt r := by
      field_simp
    _ = _ := by rw [he]

lemma source_near_ennreal_scalar {K Cg Cb I E r φ p θ : ℝ}
    (hK : 0≤K) (hCg : 0≤Cg) (hCb : 0≤Cb) (hI : 0≤I) (hE : 0≤E)
    (hr : 0≤r) (hφ : 0≤φ) (hp : 0<p) (hθ : 0<θ) :
    ENNReal.ofReal (K*φ^2/(p*θ^2))*
        ((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
          ((ENNReal.ofReal (128*Cg*p^3*θ^2))^2*ENNReal.ofReal (768*I*r*φ^2))^(1/2:ℝ))+
      ENNReal.ofReal (K*φ/p)*
        ((ENNReal.ofReal (40*(I+2*r)*E))^(1/2:ℝ)*
          ((ENNReal.ofReal (128*Cb*p^3*θ^2))^2*ENNReal.ofReal (768*I*r*φ^2))^(1/2:ℝ)) =
    ENNReal.ofReal ((128*K*Cg*Real.sqrt 15360)*Real.sqrt E*I*p^2*φ^3*Real.sqrt r+
      (128*K*Cb*Real.sqrt 30720)*Real.sqrt E*Real.sqrt I*Real.sqrt (I+2*r)*
        p^2*θ^2*φ^2*Real.sqrt r) := by
  rw [←ENNReal.ofReal_pow (by positivity : 0≤128*Cg*p^3*θ^2),
    ←ENNReal.ofReal_pow (by positivity : 0≤128*Cb*p^3*θ^2),
    ←ENNReal.ofReal_mul (sq_nonneg _),←ENNReal.ofReal_mul (sq_nonneg _)]
  rw [ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
    ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity)]
  rw [←ENNReal.ofReal_mul (Real.sqrt_nonneg _),←ENNReal.ofReal_mul (by positivity : 0≤K*φ^2/(p*θ^2)),
    ←ENNReal.ofReal_mul (Real.sqrt_nonneg _),←ENNReal.ofReal_mul (by positivity : 0≤K*φ/p),
    source_near_good_scalar hCg hI hE hr hφ hp hθ,
    source_near_magnetic_scalar hCb hI hE hr hφ hp,
    ←ENNReal.ofReal_add (by positivity) (by positivity)]

lemma Admissible.projected_source_near_real_bin {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ,0≤Cg ∧ 0≤Cb ∧
    ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (k : Fin 4→ℕ)
        (a b I w : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → 0<I → b-a≤I → 0<w →
      cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let r := max 1 T*cappedRepresentative (k 3)
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := representativeClosedBin T w k
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s X V B T w Q z
        ∂physicalBinMeasure V B (Icc a b))≤
      ENNReal.ofReal (Cg*Real.sqrt E*I*p^2*φ^3*Real.sqrt r+
        Cb*Real.sqrt E*Real.sqrt I*Real.sqrt (I+2*r)*p^2*θ^2*φ^2*Real.sqrt r) := by
  obtain ⟨Cg,Cb,c,hCg,hCb,hc,hnear⟩ := hd₀.projected_source_near_bin
  let K := 128*(3840+94080000*c)
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨128*K*Cg*Real.sqrt 15360,128*K*Cb*Real.sqrt 30720,by positivity,by positivity,?_⟩
  intro s T F hs hT h0 zX S Q k a b I w hS hS0 ha hb hI hab hw hsmall hband
  have hh := hnear s T F hs hT h0 zX S Q k a b I w hS hS0 ha hb hI hab hw hsmall hband
  apply hh.trans_eq
  apply source_near_ennreal_scalar hK hCg hCb hI.le
    (integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩))
    (mul_nonneg (zero_le_one.trans (le_max_left _ _)) (cappedRepresentative_pos _).le)
    (cappedRepresentative_pos _).le
    (by dsimp [sourceRepresentative]; positivity) (cappedRepresentative_pos _)

lemma capped_radius_sqrt_sum {H : ℝ} (hH : 1≤H) :
    (∑'n : ℕ,ENNReal.ofReal (Real.sqrt (H*cappedRepresentative n)))≤ENNReal.ofReal (4*H) := by
  have hH0 : 0≤H := zero_le_one.trans hH
  have hs : Real.sqrt H≤H := (Real.sqrt_le_iff.mpr ⟨hH0,by nlinarith only [hH]⟩)
  have hhalf : Real.sqrt ((2:ℝ)⁻¹)≤3/4 := (Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
  have hpow (n : ℕ) : Real.sqrt (cappedRepresentative n)≤(3/4:ℝ)^n := by
    induction n with
    | zero => norm_num [cappedRepresentative]
    | succ n ih =>
      rw [cappedRepresentative,pow_succ,Real.sqrt_mul (by positivity)]
      rw [pow_succ]
      exact mul_le_mul ih hhalf (Real.sqrt_nonneg _) (by positivity)
  have hpoint (n : ℕ) : ENNReal.ofReal (Real.sqrt (H*cappedRepresentative n))≤
      ENNReal.ofReal H*ENNReal.ofReal ((3/4:ℝ)^n) := by
    rw [←ENNReal.ofReal_mul hH0,Real.sqrt_mul hH0]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul hs (hpow n) (Real.sqrt_nonneg _) hH0)
  have hge : (∑'n : ℕ,ENNReal.ofReal ((3/4:ℝ)^n))=4 := by
    have hsum : Summable (fun n : ℕ=>(3/4:ℝ)^n) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    rw [←ENNReal.ofReal_tsum_of_nonneg (fun n=>by positivity) hsum,
      tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤3/4) (by norm_num : (3/4:ℝ)<1)]
    norm_num
  calc
    _ ≤ ∑'n : ℕ,ENNReal.ofReal H*ENNReal.ofReal ((3/4:ℝ)^n) := ENNReal.tsum_le_tsum hpoint
    _ = _ := by
      rw [ENNReal.tsum_mul_left,hge,←ENNReal.ofReal_ofNat (n:=4),←ENNReal.ofReal_mul hH0]
      congr 1
      ring

lemma source_low_receiver_scalar {Cg Cb E H p θ φ r w P : ℝ}
    (hCg : 0≤Cg) (hCb : 0≤Cb) (hE : 0≤E) (hH : 1≤H) (hp : 0≤p)
    (hθ : 0≤θ) (hφ : 0<φ) (hr : 0≤r) (hw : 0<w) (hP : 0<P)
    (hple : p≤128*P) (hθφ : θ≤φ) (hφw : φ*w≤32) (hrH : r≤H)
    (hwP : w≤P) (hPw : P≤w^2) :
    Cg*Real.sqrt E*(w/P)^2*p^2*φ^3*Real.sqrt r+
      Cb*Real.sqrt E*Real.sqrt ((w/P)^2)*Real.sqrt ((w/P)^2+2*r)*p^2*θ^2*φ^2*Real.sqrt r≤
    (128^2*32^2*Cg+2*128^2*32^3*Cb)*(1+E)*H*φ*Real.sqrt r := by
  have hH0 : 0≤H := zero_le_one.trans hH
  have hwp : 0≤w/P := div_nonneg hw.le hP.le
  have hI : (w/P)^2≤1 := by
    have hh : w/P≤1 := (div_le_one hP).mpr hwP
    nlinarith only [hh,hwp]
  have hsE : Real.sqrt E≤1+E := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith only [hE]⟩
  have hsH : Real.sqrt ((w/P)^2+2*r)≤2*H :=
    Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith only [hI,hrH,hH]⟩
  have hφle : φ≤32/w := (le_div_iff₀ hw).mpr hφw
  have hφ3 : φ^3≤(32/w)^2*φ := by
    calc
      _ = φ^2*φ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hφ.le hφle _) hφ.le
  have htφ4 : θ^2*φ^2≤(32/w)^3*φ := by
    calc
      _ ≤ φ^2*φ^2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hθ hθφ _) (sq_nonneg φ)
      _ = φ^3*φ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hφ.le hφle _) hφ.le
  have hrat : P/w^2≤1 := (div_le_one (sq_pos_of_pos hw)).mpr hPw
  have hg : Cg*Real.sqrt E*(w/P)^2*p^2*φ^3*Real.sqrt r≤
      (128^2*32^2*Cg)*(1+E)*H*φ*Real.sqrt r := by
    calc
      _ ≤ Cg*(1+E)*(w/P)^2*(128*P)^2*((32/w)^2*φ)*Real.sqrt r := by gcongr
      _ = (128^2*32^2*Cg)*(1+E)*1*φ*Real.sqrt r := by field_simp
      _ ≤ _ := by gcongr
  have hb : Cb*Real.sqrt E*Real.sqrt ((w/P)^2)*Real.sqrt ((w/P)^2+2*r)*p^2*θ^2*φ^2*Real.sqrt r≤
      (2*128^2*32^3*Cb)*(1+E)*H*φ*Real.sqrt r := by
    rw [Real.sqrt_sq hwp]
    calc
      _ = Cb*Real.sqrt E*(w/P)*Real.sqrt ((w/P)^2+2*r)*p^2*(θ^2*φ^2)*Real.sqrt r := by ring
      _ ≤ Cb*(1+E)*(w/P)*(2*H)*(128*P)^2*((32/w)^3*φ)*Real.sqrt r := by gcongr
      _ = ((2*128^2*32^3*Cb)*(1+E)*H*φ*Real.sqrt r)*(P/w^2) := by field_simp
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hrat
  calc
    _ ≤ (128^2*32^2*Cg)*(1+E)*H*φ*Real.sqrt r+
        (2*128^2*32^3*Cb)*(1+E)*H*φ*Real.sqrt r := add_le_add hg hb
    _ = _ := by ring

lemma PhaseFlowOn.physicalProjectedSource_source_truncate {s : Solution} {T P : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (hP : ∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P)
    (N : ℕ) (hN : 1024*P≤(2:ℝ)^N) (X V : ℝ→Vec) (Q : Set (Fin 4→ℕ))
    {z : ConeCoordinate} {w : ℝ} (hr : z.2.1∈Icc 0 T) (k : Fin 4→ℕ)
    (hk : ¬(k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0)≤128*P)) :
    physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z=0 := by
  unfold physicalProjectedSourceDensity
  apply mul_eq_zero_of_right
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (measurableSet_coneBinMomentumSet _ _ _)] with v hv
  have hf : s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))=0 := by
    by_contra hc
    have hq := F.eulerian_supported_momentum hs hP hr _ v hc
    have hidx := representativeClosedBin_source_indices (sphere_norm z.2.2) hv
      ((mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ)≤1024)).trans hN)
    have hp : sourceRepresentative (k 0)≤128*P := by
      have hh : sourceRepresentative (k 0)/128≤q v := hv.1.1
      linarith only [hh,hq]
    exact hk ⟨hidx.1,hidx.2,hp⟩
  simp only [hf,zero_mul,zero_div,zero_smul,norm_zero,add_zero,ENNReal.ofReal_zero,Pi.zero_apply]

lemma PhaseFlowOn.physicalProjectedSource_integral_source_truncate {s : Solution} {T P : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (hP : ∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P)
    (N : ℕ) (hN : 1024*P≤(2:ℝ)^N) (X V : ℝ→Vec) (Q : Set (Fin 4→ℕ)) (hV : Measurable V)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) (w : ℝ) (k : Fin 4→ℕ)
    (hk : ¬(k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0)≤128*P)) :
    (∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
      ∂physicalBinMeasure V (representativeClosedBin T w k) J)=0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV _ hJ)] with z hz
  exact F.physicalProjectedSource_source_truncate hs hP N hN X V Q
    ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩ k hk

lemma Admissible.projected_source_low_receiver_log_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (a b w P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → b-a≤(w/P)^2 → 0<w → w≤P → P≤w^2 → 0<P →
      1≤Real.log (2+P) →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let E := ∫x : Vec,totalEnergy s (0,x)
      let sector : Set (Fin 4→ℕ) := {k |
        cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 ∧
        cappedRepresentative (k 2)*w≤32}
      (∑'k : Fin 4→ℕ,sector.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
          ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k)≤
      ENNReal.ofReal (C*(1+E)*(max 1 T)^2*(Real.log (2+P))^2) := by
  classical
  obtain ⟨Cg,Cb,hCg,hCb,hnear⟩ := hd₀.projected_source_near_real_bin
  obtain ⟨Cn,hCn,hcount⟩ := exists_source_dyadic_count
  let B := 128^2*32^2*Cg+2*128^2*32^3*Cb
  have hB : 0≤B := by dsimp [B]; positivity
  refine ⟨8*B*Cn^2,by positivity,?_⟩
  intro s T F hs hT h0 zX S Q a b w P hS hS0 ha hb hab hw hwP hPw hP hL hsource hband
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let E := ∫x : Vec,totalEnergy s (0,x)
  let I := (w/P)^2
  let H := max 1 T
  let sector : Set (Fin 4→ℕ) := {k |
    cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 ∧
    cappedRepresentative (k 2)*w≤32}
  let rfun := fun k : Fin 4→ℕ=>∫⁻z : ConeCoordinate,
    physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
      ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hH : 1≤H := le_max_left _ _
  have hH0 : 0≤H := zero_le_one.trans hH
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  let source : Set (Fin 4→ℕ) := {k | k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0)≤128*P}
  let f := (source∩sector).indicator rfun
  let c := 4*B*(1+E)*H^2
  have hc : 0≤c := by dsimp [c]; positivity
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have heq : sector.indicator rfun=f := by
    funext k
    by_cases hk : k∈sector
    · by_cases hsrc : k∈source
      · rw [indicator_of_mem hk,show f k=rfun k from indicator_of_mem (show k∈source∩sector from ⟨hsrc,hk⟩) rfun]
      · rw [indicator_of_mem hk,show f k=0 from indicator_of_notMem (fun h=>hsrc h.1) rfun]
        exact F.physicalProjectedSource_integral_source_truncate hs hsource N hN X V Q
          hα.snd.measurable measurableSet_Icc hJ w k hsrc
    · rw [indicator_of_notMem hk,show f k=0 from indicator_of_notMem (fun h=>hk h.2) rfun]
  have hrad (np nt nf : ℕ) : (∑'nr,f ![np,nt,nf,nr])≤
      (if np<N ∧ nt<N then ENNReal.ofReal c*ENNReal.ofReal ((2:ℝ)⁻¹^nf) else 0) := by
    by_cases hidx : np<N ∧ nt<N
    · rw [ite_eq_left hidx]
      let φ := cappedRepresentative nf
      have hφ : 0<φ := cappedRepresentative_pos _
      let coeff := B*(1+E)*H*φ
      have hcoeff : 0≤coeff := by dsimp [coeff]; positivity
      have hpoint (nr : ℕ) : f ![np,nt,nf,nr]≤
          ENNReal.ofReal coeff*ENNReal.ofReal (Real.sqrt (H*cappedRepresentative nr)) := by
        let k : Fin 4→ℕ := ![np,nt,nf,nr]
        by_cases hk : k∈source∩sector
        · change (source∩sector).indicator rfun k≤_
          rw [indicator_of_mem hk]
          have hh := hnear s T F hs hT h0 zX S Q k a b I w hS hS0 ha hb
            (by dsimp [I]; positivity) hab hw hk.2.1 hband
          apply hh.trans
          rw [←ENNReal.ofReal_mul hcoeff]
          apply ENNReal.ofReal_le_ofReal
          have hp : 0 ≤ sourceRepresentative np := by dsimp [sourceRepresentative]; positivity
          have hθ : 0≤cappedRepresentative nt := (cappedRepresentative_pos _).le
          have hθφ : cappedRepresentative nt≤φ := by
            have ht : cappedRepresentative nt≤φ/16 := hk.2.1
            linarith only [ht,hφ]
          have hrH : H*cappedRepresentative nr≤H := mul_le_of_le_one_right hH0 (cappedRepresentative_le_one nr)
          exact source_low_receiver_scalar hCg hCb hE hH hp hθ hφ
            (mul_nonneg hH0 (cappedRepresentative_pos _).le) hw hP hk.1.2.2 hθφ hk.2.2 hrH hwP hPw
        · change (source∩sector).indicator rfun k≤_
          rw [indicator_of_notMem hk]
          exact bot_le
      have hh := ENNReal.tsum_le_tsum hpoint
      rw [ENNReal.tsum_mul_left] at hh
      apply (hh.trans (mul_le_mul' le_rfl (capped_radius_sqrt_sum hH))).trans_eq
      rw [←ENNReal.ofReal_mul hcoeff,←ENNReal.ofReal_mul hc]
      congr 1
      dsimp [coeff,c,φ,cappedRepresentative]
      ring
    · have hz (nr : ℕ) : f ![np,nt,nf,nr]=0 := by
        apply indicator_of_notMem
        intro hk
        exact hidx ⟨hk.1.1,hk.1.2.1⟩
      simp only [hz,tsum_zero,ite_eq_right hidx,le_refl]
  change (∑'k : Fin 4→ℕ,sector.indicator rfun k)≤_
  rw [heq]
  apply (tsum_quad_of_radial_bound f N (ENNReal.ofReal c) hrad).trans
  have heN : (2:ℝ≥0∞)*(N:ℝ≥0∞)^2=ENNReal.ofReal (2*(N:ℝ)^2) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),
      ENNReal.ofReal_pow (Nat.cast_nonneg N),ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat]
  rw [heN,←ENNReal.ofReal_mul hc]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ c*(2*(Cn*Real.log (2+P))^2) := by gcongr
    _ = _ := by dsimp [c,H,E]; ring

end RVM

end

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.source_majorant_remaining_log_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤C ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → a≤b → b-a≤(w/P)^2 →
      0<M → 0≤A → 1≤P → 1≤Real.log (2+P) → 0<w → w≤P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let E := ∫x : Vec,totalEnergy s (0,x)
      let sector : Set (Fin 4→ℕ) := {k | cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1)}
      (∑'k : Fin 4→ℕ,sector.indicator (fun k=>∫⁻z : ConeCoordinate,
          physicalSourceMajorantDensity s X V (representativeClosedBin T w k) z
            ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k)≤
      ENNReal.ofReal (C*(1+E)*(1+M+Real.sqrt A)*w*(Real.log (2+P))^5) := by
  classical
  obtain ⟨C,hC,hbound⟩ := hd₀.source_majorant_remaining_radial_cover
  obtain ⟨Cn,hCn,hcount⟩ := exists_direct_dyadic_count
  refine ⟨C*Cn^4,by positivity,?_⟩
  intro s T F hs hT h0 zX S a b w M A P hS hS0 ha hb hab hJI hM hA hP hL hw hwP hsource HX HZ
  dsimp only
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let U := C*(1+∫x : Vec,totalEnergy s (0,x))*(1+M+Real.sqrt A)*w*Real.log (2+P)
  let sector : Set (Fin 4→ℕ) := {k | cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1)}
  let f := sector.indicator (fun k=>∫⁻z : ConeCoordinate,
    physicalSourceMajorantDensity s X V (representativeClosedBin T w k) z
      ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b))
  have hj : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hα := (F.continuous_prefixFlow hs hT).comp
    (continuous_id.prodMk continuous_const : Continuous (fun t : ℝ=>(t,zX)))
  have hzero (k : Fin 4→ℕ)
      (hk : ¬(k 0<N ∧ k 1<N ∧ k 2<N ∧ sourceRepresentative (k 0)≤128*P)) : f k=0 := by
    dsimp only [f]
    by_cases hsec : k∈sector
    · rw [Set.indicator_of_mem hsec]
      exact F.physicalSourceMajorant_integral_truncate hs (zero_le_one.trans hP) hwP hsource N hN
        X V hα.snd.measurable measurableSet_Icc hj k hk
    · exact Set.indicator_of_notMem hsec _
  have hbnd : ∀np nt nf, (∑'nr,f ![np,nt,nf,nr]) ≤
      (if np<N ∧ nt<N ∧ nf<N then (N:ℝ≥0∞)*ENNReal.ofReal U else 0) := by
    intro np nt nf
    by_cases hi : np<N ∧ nt<N ∧ nf<N
    · rw [ite_eq_left hi]
      by_cases hp : sourceRepresentative np≤128*P
      · by_cases hsec : cappedRepresentative nf≤16384*cappedRepresentative nt
        · have hh := hbound s T F hs hT h0 zX S np nt nf a b w M A P N hS hS0 ha hb hab hJI
            hM hA hP hL hw hwP hp hN hsec HX HZ
          simpa [f,sector,Set.indicator_apply,hsec] using hh
        · have hfz : ∀nr,f ![np,nt,nf,nr]=0 := by
            intro nr
            exact Set.indicator_of_notMem (by simpa [sector] using hsec) _
          simp only [hfz,tsum_zero,zero_le]
      · have hfz : ∀nr,f ![np,nt,nf,nr]=0 := by
          intro nr
          apply hzero
          simpa using
            (show ¬(np<N ∧ nt<N ∧ nf<N ∧ sourceRepresentative np≤128*P) by tauto)
        simp only [hfz,tsum_zero,zero_le]
    · rw [ite_eq_right hi]
      have hfz : ∀nr,f ![np,nt,nf,nr]=0 := by
        intro nr
        apply hzero
        simpa using
          (show ¬(np<N ∧ nt<N ∧ nf<N ∧ sourceRepresentative np≤128*P) by tauto)
      simp only [hfz,tsum_zero,le_refl]
  apply (tsum_quad_of_finite_radial_bound f N ((N:ℝ≥0∞)*ENNReal.ofReal U) hbnd).trans
  calc
    _ = (N:ℝ≥0∞)^4*ENNReal.ofReal U := by ring
    _ ≤ ENNReal.ofReal (Cn^4*(Real.log (2+P))^4*U) :=
      ennreal_count_four_bound hCn (zero_le_one.trans hL) hNc U
    _ = _ := by congr 1; dsimp only [U]; ring

def directionSelection (T : ℝ) : Set (Fin 4→ℕ) :=
  {k | cappedRepresentative (k 1)≤(1/1024)*cappedRepresentative (k 2) ∧
    sourceRepresentative (k 0)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1}

lemma dyadic_neighbor_product_le {T : ℝ} {j k : Fin 4→ℕ}
    (h : ∀i,j i≤ k i+2 ∧ k i≤ j i+2) :
    sourceRepresentative (j 0)*cappedRepresentative (j 1)*
      Real.sqrt (max 1 T*cappedRepresentative (j 3)) ≤
    32*(sourceRepresentative (k 0)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3))) := by
  have hH : 0≤ max (1:ℝ) T := le_trans (by norm_num) (le_max_left _ _)
  have hp := sourceRepresentative_le_four (h 0).1
  have hθ := cappedRepresentative_le_four (h 1).2
  have hr := cappedRepresentative_le_four (h 3).2
  have hsqrt : Real.sqrt (max 1 T*cappedRepresentative (j 3)) ≤
      2*Real.sqrt (max 1 T*cappedRepresentative (k 3)) := by
    calc
      _ ≤ Real.sqrt (max 1 T*(4*cappedRepresentative (k 3))) := by gcongr
      _ = _ := by
        rw [show max 1 T*(4*cappedRepresentative (k 3))=4*(max 1 T*cappedRepresentative (k 3)) by ring,
          Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
        norm_num
  calc
    _ ≤ (4*sourceRepresentative (k 0))*(4*cappedRepresentative (k 1))*
        (2*Real.sqrt (max 1 T*cappedRepresentative (k 3))) := by
      have hpk : 0 < sourceRepresentative (k 0) := by dsimp [sourceRepresentative]; positivity
      have hθk := cappedRepresentative_pos (k 1)
      exact mul_le_mul (mul_le_mul hp hθ (cappedRepresentative_pos _).le (by positivity))
        hsqrt (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring

lemma directionSelection_boundary_split {T : ℝ} {k : Fin 4→ℕ}
    (hk : k∈dyadicSelectionBoundary (directionSelection T)) :
    cappedRepresentative (k 1)≤ cappedRepresentative (k 2)/64 ∧
    (cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1) ∨
      1/32≤ sourceRepresentative (k 0)*cappedRepresentative (k 1)*
        Real.sqrt (max 1 T*cappedRepresentative (k 3))) := by
  have hu := dyadicSelectionBoundary_direction (T:=T) (κ:=1/1024) (by norm_num)
    (Q:=directionSelection T) (fun j hj=>hj) hk
  refine ⟨by linarith only [hu.1],?_⟩
  by_cases hs : cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1)
  · exact Or.inl hs
  · right
    obtain ⟨j,hjn,hnear⟩ := hk.2
    have hjθ := cappedRepresentative_le_four (hnear 1).2
    have hkφ := cappedRepresentative_le_four (hnear 2).1
    have hjselect : cappedRepresentative (j 1)≤(1/1024)*cappedRepresentative (j 2) := by
      linarith only [hjθ,hkφ,lt_of_not_ge hs]
    have hjprod : 1< sourceRepresentative (j 0)*cappedRepresentative (j 1)*
        Real.sqrt (max 1 T*cappedRepresentative (j 3)) := by
      by_contra hh
      exact hjn ⟨hjselect,le_of_not_gt hh⟩
    have hp := dyadic_neighbor_product_le (T:=T) hnear
    linarith only [hjprod,hp]

lemma Admissible.projected_source_structural_edge_log_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤ C ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤ T → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤ a → b≤ T → a≤ b → b-a≤(w/P)^2 →
      0< M → 0≤ A → 1≤ P → 1≤ Real.log (2+P) → 0< w → w≤ P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤ P) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let E := ∫x : Vec,totalEnergy s (0,x)
      let edge : Set (Fin 4→ℕ) := {k | cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1) ∧
        cappedRepresentative (k 1)≤ cappedRepresentative (k 2)/16}
      (∑'k : Fin 4→ℕ,edge.indicator (fun k=>∫⁻z : ConeCoordinate,
          physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
            ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k)≤
      ENNReal.ofReal (C*(1+E)*(1+M+Real.sqrt A)*w*(Real.log (2+P))^5) := by
  classical
  obtain ⟨C,hC,hbound⟩ := hd₀.source_majorant_remaining_log_sum
  obtain ⟨c,hc,hcut⟩ := dyadicFactor_log_derivative_bound
  let D := 64+5880000*c
  have hD : 0≤ D := by dsimp [D]; positivity
  refine ⟨D*C,by positivity,?_⟩
  intro s T F hs hT h0 zX S Q a b w M A P hS hS0 ha hb hab hJI hM hA hP hL hw hwP hsource hW HX HZ
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := fun k=>representativeClosedBin T w k
  let edge : Set (Fin 4→ℕ) := {k | cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1) ∧
    cappedRepresentative (k 1)≤ cappedRepresentative (k 2)/16}
  let sector : Set (Fin 4→ℕ) := {k | cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1)}
  have hj : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hα := (F.continuous_prefixFlow hs hT).comp
    (continuous_id.prodMk continuous_const : Continuous (fun t : ℝ=>(t,zX)))
  have hpoint (k : Fin 4→ℕ) : edge.indicator (fun k=>∫⁻z : ConeCoordinate,
      physicalProjectedSourceDensity s X V (B k) T w Q z ∂physicalBinMeasure V (B k) (Icc a b)) k ≤
    ENNReal.ofReal D*sector.indicator (fun k=>∫⁻z : ConeCoordinate,
      physicalSourceMajorantDensity s X V (B k) z ∂physicalBinMeasure V (B k) (Icc a b)) k := by
    by_cases hk : k∈edge
    · rw [Set.indicator_of_mem hk,Set.indicator_of_mem (show k∈sector from hk.1)]
      apply physicalProjectedSourceIntegral_le_majorant (X:=X) (V:=V) hs hα.snd.measurable (B k) Q measurableSet_Icc hj hc hcut hw
      · intro t ht
        simp only [V,prefixFlow,prefixClamp_eq (hj ht)]
        exact hW t ht
      · change 0< max 1 T*cappedRepresentative (k 3)/2
        exact div_pos (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
          (cappedRepresentative_pos _)) (by norm_num)
      · apply representativeClosedBin_small_of_angle
        have hφ := cappedRepresentative_pos (k 2)
        linarith only [hk.2,hφ]
    · rw [Set.indicator_of_notMem hk]
      exact bot_le
  apply (ENNReal.tsum_le_tsum hpoint).trans
  rw [ENNReal.tsum_mul_left]
  apply (mul_le_mul' le_rfl (hbound s T F hs hT h0 zX S a b w M A P hS hS0 ha hb hab hJI
    hM hA hP hL hw hwP hsource HX HZ)).trans_eq
  rw [←ENNReal.ofReal_mul hD]
  congr 1
  ring

def directionSourceEdge : Set (Fin 4→ℕ) :=
  {k | cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1) ∧
    cappedRepresentative (k 1)≤ cappedRepresentative (k 2)/16}

def directionSourceLow (w : ℝ) : Set (Fin 4→ℕ) :=
  {k | cappedRepresentative (k 1)≤ cappedRepresentative (k 2)/16 ∧
    cappedRepresentative (k 2)*w≤32}

def directionSourceFar (T w P : ℝ) : Set (Fin 4→ℕ) :=
  {k | sourceRepresentative (k 0)≤128*P ∧
    cappedRepresentative (k 1)≤ cappedRepresentative (k 2)/16 ∧
    32≤ cappedRepresentative (k 2)*w ∧
    1/32≤ sourceRepresentative (k 0)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3))}

lemma direction_source_cover_sum {T w P : ℝ} (f : (Fin 4→ℕ)→ℝ≥0∞)
    (S : Set (Fin 4→ℕ))
    (hS : ∀k∈S,cappedRepresentative (k 1)≤ cappedRepresentative (k 2)/16 ∧
      (cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1) ∨
        1/32≤ sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))))
    (hf : ∀k,¬sourceRepresentative (k 0)≤128*P→f k=0) :
    (∑'k,S.indicator f k)≤
      (∑'k,directionSourceEdge.indicator f k)+
      (∑'k,(directionSourceFar T w P).indicator f k)+
      (∑'k,(directionSourceLow w).indicator f k) := by
  classical
  rw [←ENNReal.tsum_add,←ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : k∈S
  · rw [Set.indicator_of_mem hk]
    by_cases hp : sourceRepresentative (k 0)≤128*P
    · obtain ⟨hθ,hcase⟩ := hS k hk
      by_cases he : cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1)
      · have hm : k∈directionSourceEdge := ⟨he,hθ⟩
        rw [Set.indicator_of_mem hm]
        exact (le_add_of_nonneg_right (bot_le)).trans (le_add_of_nonneg_right (bot_le))
      · by_cases hl : cappedRepresentative (k 2)*w≤32
        · have hm : k∈directionSourceLow w := ⟨hθ,hl⟩
          rw [Set.indicator_of_mem hm]
          exact le_add_of_nonneg_left (bot_le)
        · have hm : k∈directionSourceFar T w P := ⟨hp,hθ,(lt_of_not_ge hl).le,hcase.resolve_left he⟩
          rw [Set.indicator_of_mem hm]
          exact (le_add_of_nonneg_left (bot_le)).trans (le_add_of_nonneg_right (bot_le))
    · rw [hf k hp]
      exact bot_le
  · rw [Set.indicator_of_notMem hk]
    exact bot_le

lemma Admissible.direction_boundary_source_log_sum {d : Datum} (hd₀ : Admissible d)
    (T₀ : ℝ) :
    ∃Ce Cf Cl : ℝ,0≤ Ce ∧ 0≤ Cf ∧ 0≤ Cl ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤ T → T≤ T₀ → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤ a → b≤ T → a≤ b → b-a≤(w/P)^2 →
      0< M → 0≤ A → 1≤ P → 1≤ Real.log (2+P) → 1≤ w → w≤ P → P≤ w^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤ P) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Q := directionSelection T
      (∑'k : Fin 4→ℕ,(dyadicSelectionBoundary Q).indicator (fun k=>∫⁻z : ConeCoordinate,
          physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
            ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k)≤
      ENNReal.ofReal (Ce*(1+E)*(1+M+Real.sqrt A)*w*(Real.log (2+P))^5)+
      ENNReal.ofReal (Cf*E*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^5)+
      ENNReal.ofReal (Cl*(1+E)*(max 1 T)^2*(Real.log (2+P))^2) := by
  classical
  obtain ⟨Ce,hCe,hedge⟩ := hd₀.projected_source_structural_edge_log_sum
  obtain ⟨Cf,hCf,hfar⟩ := hd₀.projected_source_stable_far_log_sum T₀
  obtain ⟨Cl,hCl,hlow⟩ := hd₀.projected_source_low_receiver_log_sum
  refine ⟨Ce,Cf,Cl,hCe,hCf,hCl,?_⟩
  intro s T F hs hT hTT h0 zX S a b w M A P hS hS0 ha hb hab hJI hM hA hP hL hw hwP hPw hsource hW HX HZ
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let Q := directionSelection T
  let f := fun k=>∫⁻z : ConeCoordinate,
    physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
      ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)
  have hj : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hα := (F.continuous_prefixFlow hs hT).comp
    (continuous_id.prodMk continuous_const : Continuous (fun t : ℝ=>(t,zX)))
  obtain ⟨Cn,hCn,hcount⟩ := exists_direct_dyadic_count
  obtain ⟨N,hN,_⟩ := hcount P hP hL
  have h1024 : 1024*P≤(2:ℝ)^N := by linarith only [hN,hP]
  have hzero (k : Fin 4→ℕ) (hk : ¬sourceRepresentative (k 0)≤128*P) : f k=0 := by
    apply F.physicalProjectedSource_integral_source_truncate hs hsource N h1024 X V Q
      hα.snd.measurable measurableSet_Icc hj w k
    intro hc
    exact hk hc.2.2
  have hroute (k : Fin 4→ℕ) (hk : k∈dyadicSelectionBoundary Q) :=
    directionSelection_boundary_split hk
  have hh := direction_source_cover_sum (T:=T) (w:=w) (P:=P) f (dyadicSelectionBoundary Q)
    (fun k hk=>⟨by have hφ := cappedRepresentative_pos (k 2); linarith only [(hroute k hk).1,hφ],
      (hroute k hk).2⟩) hzero
  apply hh.trans
  exact add_le_add (add_le_add
    (hedge s T F hs hT h0 zX S Q a b w M A P hS hS0 ha hb hab hJI hM hA hP hL
      (zero_lt_one.trans_le hw) hwP hsource hW HX HZ)
    (hfar s T F hs hT hTT h0 zX S Q a b w M A P hS hS0 ha hb hJI hM hA
      (zero_lt_one.trans_le hP) hL hw hwP hW HX HZ))
    (hlow s T F hs hT h0 zX S Q a b w P hS hS0 ha hb hJI
      (zero_lt_one.trans_le hw) hwP hPw (zero_lt_one.trans_le hP) hL hsource hW)

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma tsum_set_indicator_mono {ι : Type*} {A B : Set ι} (hAB : A⊆B)
    (f : ι→ℝ≥0∞) : (∑'i,A.indicator f i)≤∑'i,B.indicator f i := by
  classical
  apply ENNReal.tsum_le_tsum
  intro i
  by_cases hi : i∈A
  · rw [Set.indicator_of_mem hi,Set.indicator_of_mem (hAB hi)]
  · rw [Set.indicator_of_notMem hi]
    exact bot_le

lemma Admissible.direction_sourceCutoff_label_log_bound {d : Datum} (hd₀ : Admissible d)
    (T₀ : ℝ) :
    ∃Ce Cf Cl : ℝ,0≤ Ce ∧ 0≤ Cf ∧ 0≤ Cl ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤ T → T≤ T₀ → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (a b w M A P : ℝ) (hw : 0<w),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤ a → b≤ T → a≤ b → b-a≤(w/P)^2 →
      0< M → 0≤ A → 1≤ P → 1≤ Real.log (2+P) → 1≤ w → w≤ P → P≤ w^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤ P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖(Icc a b).indicator (prefixAngularMultiplier s F.flow T w hw zX)
        (labelReceiverTime F.flow zX T p)
        (partialCutoffLabelCost s F.flow zX T (directionSelection T)
          (fun p=>cutoffSourceTangent (lorentzField s.E s.B (p.1,F.flow p.2 p.1)).2) p)‖)≤
      ENNReal.ofReal (Ce*(1+E)*(1+M+Real.sqrt A)*w*(Real.log (2+P))^5)+
      ENNReal.ofReal (Cf*E*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^5)+
      ENNReal.ofReal (Cl*(1+E)*(max 1 T)^2*(Real.log (2+P))^2) := by
  classical
  obtain ⟨Ce,Cf,Cl,hCe,hCf,hCl,hbound⟩ := hd₀.direction_boundary_source_log_sum T₀
  refine ⟨Ce,Cf,Cl,hCe,hCf,hCl,?_⟩
  intro s T F hs hT hTT h0 zX S a b w M A P hw hS hS0 ha hb hab hJI hM hA hP hL hw1 hwP hPw hsource hq hW HX HZ
  dsimp only
  obtain ⟨Cn,hCn,hcount⟩ := exists_source_dyadic_count
  obtain ⟨N,hN,_⟩ := hcount P (zero_lt_one.trans_le hP) hL
  have hEuler (σ : ℝ) (hσ : σ∈Icc 0 T) (z : Phase) (hf : s.f (σ,z)≠0) :
      1024*q z.2≤(2:ℝ)^N :=
    (mul_le_mul_of_nonneg_left (F.eulerian_supported_momentum hs hsource hσ z.1 z.2 hf)
      (by norm_num : (0:ℝ)≤1024)).trans hN
  apply (F.actual_sourceCutoff_label_boundary_sum hs hT zX (directionSelection T) hw
    measurableSet_Icc (Icc_subset_Icc ha hb) hq hW N hEuler).trans
  apply (tsum_set_indicator_mono inter_subset_left _).trans
  exact hbound s T F hs hT hTT h0 zX S a b w M A P hS hS0 ha hb hab hJI hM hA hP hL hw1 hwP hPw hsource hW HX HZ

lemma Admissible.direction_geometryCutoff_label_log_bound {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤ C ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤ T → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (a b w M A P : ℝ) (hw : 0<w),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤ a → b≤ T → b-a≤(w/P)^2 →
      0< M → 0≤ A → 0< P → 1≤ Real.log (2+P) → w≤ P → P≤ w^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤ P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖(Icc a b).indicator (prefixAngularMultiplier s F.flow T w hw zX)
        (labelReceiverTime F.flow zX T p)
        (partialCutoffLabelCost s F.flow zX T (directionSelection T)
          (fun p=>cutoffGeometryTangent (branchTime F.flow zX p.2 T p.1-p.1) (branchRate F.flow zX p.2 T p.1)
            (velocity (F.flow zX (branchTime F.flow zX p.2 T p.1)).2) (velocity (F.flow p.2 p.1).2)
            (branchDirection F.flow zX p.2 T p.1)) p)‖)≤
      ENNReal.ofReal (C*max 1 T*(1+E)*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^3) := by
  classical
  obtain ⟨C,hC,hbound⟩ := hd₀.geometry_cutoff_small_sector_log_sum
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX S a b w M A P hw hS hS0 ha hb hJI hM hA hP hL hwP hPw hsource hq hW HX HZ
  dsimp only
  obtain ⟨Cn,hCn,hcount⟩ := exists_source_dyadic_count
  obtain ⟨N,hN,_⟩ := hcount P hP hL
  have hEuler (σ : ℝ) (hσ : σ∈Icc 0 T) (z : Phase) (hf : s.f (σ,z)≠0) :
      1024*q z.2≤(2:ℝ)^N :=
    (mul_le_mul_of_nonneg_left (F.eulerian_supported_momentum hs hsource hσ z.1 z.2 hf)
      (by norm_num : (0:ℝ)≤1024)).trans hN
  apply (F.actual_geometryCutoff_label_boundary_sum hs hT zX (directionSelection T) hw
    measurableSet_Icc (Icc_subset_Icc ha hb) hq hW N hEuler).trans
  apply (tsum_set_indicator_mono (B:={k : Fin 4→ℕ | cappedRepresentative (k 1)≤ cappedRepresentative (k 2)/16})
    (fun k hk=>by
      change cappedRepresentative (k 1)≤ cappedRepresentative (k 2)/16
      have hh := (directionSelection_boundary_split hk.1).1
      have hφ := cappedRepresentative_pos (k 2)
      linarith only [hh,hφ]) _).trans
  exact hbound s T F hs hT h0 zX S (directionSelection T) a b w M A P hS hS0 ha hb hJI hM hA hP hL hw hwP hPw hsource hW HX HZ

end RVM

end

end OAI
