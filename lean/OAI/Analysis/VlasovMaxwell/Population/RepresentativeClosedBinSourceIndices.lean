import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.ProjectedSourceStableFarBound

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

lemma representativeClosedBin_source_indices {T w : ℝ} {k : Fin 4→ℕ} {N : ℕ}
    {v n a : Vec} (hn : ‖n‖=1)
    (hv : v∈coneBinMomentumSet (representativeClosedBin T w k) n a)
    (hP : 1024*q v≤(2:ℝ)^N) : k 0<N ∧ k 1<N := by
  have hq := q_pos v
  have hθ := cappedRepresentative_pos (k 1)
  have heq := cappedRepresentative_mul_pow (k 1)
  have he := source_angle_coordinate_lower v n hn
  have hlo : sourceRepresentative (k 0)/128≤q v := hv.1.1
  have hhi : 1-dot n (velocity v)≤8*(cappedRepresentative (k 1))^2 := hv.2.1.2
  have hroot : Real.sqrt ((1-dot n (velocity v))/2)≤2*cappedRepresentative (k 1) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith only [hhi]
  have hqθ : 1/2≤2*q v*cappedRepresentative (k 1) :=
    he.trans (by nlinarith only [mul_le_mul_of_nonneg_left hroot hq.le])
  constructor
  · by_contra hc
    have hp : (2:ℝ)^N≤(2:ℝ)^(k 0) := pow_le_pow_right₀ (by norm_num) (Nat.le_of_not_gt hc)
    dsimp [sourceRepresentative] at hlo
    nlinarith only [hP,hp,hlo,hq]
  · by_contra hc
    have hp : (2:ℝ)^N≤(2:ℝ)^(k 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_of_not_gt hc)
    have hh := mul_le_mul_of_nonneg_right (hP.trans hp) hθ.le
    nlinarith only [hh,heq,hqθ]

lemma PhaseFlowOn.eulerian_supported_momentum {s : Solution} {T P : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (hP : ∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P)
    {r : ℝ} (hr : r∈Icc 0 T) (x v : Vec) (hf : s.f (r,(x,v))≠0) : q v≤P := by
  have hf0 : s.f (0,inversePhase F.flow (r,(x,v)))≠0 := by
    rwa [←F.transport_inverse hs.f_smooth hs.vlasov hr]
  have hh := hP (inversePhase F.flow (r,(x,v))) hf0 r hr
  simpa only [F.flow_inversePhase hr] using hh

lemma PhaseFlowOn.physicalBinDensity_source_truncate {s : Solution} {T P : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (hP : ∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P)
    (N : ℕ) (hN : 1024*P≤(2:ℝ)^N) (X V : ℝ→Vec)
    {r t w : ℝ} (hr : r∈Icc 0 T) (n : Sphere) (k : Fin 4→ℕ)
    (hk : ¬(k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0)≤128*P)) :
    physicalBinDensity s X V (representativeClosedBin T w k) t r n=0 := by
  unfold physicalBinDensity
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (measurableSet_coneBinMomentumSet _ _ _)] with v hv
  have hf : s.f (r,(X t-(t-r) • n.1,v))=0 := by
    by_contra hc
    have hq := F.eulerian_supported_momentum hs hP hr _ v hc
    have hidx := representativeClosedBin_source_indices (sphere_norm n) hv
      ((mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ)≤1024)).trans hN)
    have hp : sourceRepresentative (k 0)≤128*P := by
      have hh : sourceRepresentative (k 0)/128≤q v := hv.1.1
      linarith only [hh,hq]
    exact hk ⟨hidx.1,hidx.2,hp⟩
  simp only [hf,ENNReal.ofReal_zero,Pi.zero_apply]

lemma PhaseFlowOn.physicalBinDensity_integral_source_truncate {s : Solution} {T P : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (hP : ∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P)
    (N : ℕ) (hN : 1024*P≤(2:ℝ)^N) (X V : ℝ→Vec) (hV : Measurable V)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) (w : ℝ) (k : Fin 4→ℕ)
    (hk : ¬(k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0)≤128*P)) :
    (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k)
      z.1 z.2.1 z.2.2 ∂physicalBinMeasure V (representativeClosedBin T w k) J)=0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV _ hJ)] with z hz
  exact F.physicalBinDensity_source_truncate hs hP N hN X V
    ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩ z.2.2 k hk

lemma exists_source_dyadic_count : ∃C : ℝ,0≤C ∧ ∀P : ℝ,
    0<P → 1≤Real.log (2+P) → ∃N : ℕ,1024*P≤(2:ℝ)^N ∧ (N:ℝ)≤C*Real.log (2+P) := by
  obtain ⟨C,hC,hcount⟩ := exists_far_dyadic_count 0
  refine ⟨C,hC,?_⟩
  intro P hP hL
  obtain ⟨N,_hN0,hN1,_hN3,hNc⟩ := hcount P hP hL
  refine ⟨N,?_,hNc⟩
  norm_num at hN1
  linarith only [hN1,hP]

lemma Admissible.central_density_stable_log_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → b-a≤(w/P)^2 →
      0<M → 0≤A → 0<P → 1≤Real.log (2+P) → 0<w → w≤P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let sector : Set (Fin 4→ℕ) := {k |
        cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 ∧
        32≤cappedRepresentative (k 2)*w}
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'k : Fin 4→ℕ,sector.indicator (fun k=>
        ENNReal.ofReal (78400000*(cappedRepresentative (k 2))^2/cappedRepresentative (k 1))*
        (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k)
          z.1 z.2.1 z.2.2 ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b))) k)≤
      ENNReal.ofReal (C*(1+E)*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^3) := by
  classical
  obtain ⟨Cs,hCs,hsum⟩ := hd₀.central_density_stable_sum
  obtain ⟨Cn,hCn,hcount⟩ := exists_source_dyadic_count
  refine ⟨Cs*Cn^2,by positivity,?_⟩
  intro s T F hs hT h0 zX S a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP hsource HX HZ
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let E := ∫x : Vec,totalEnergy s (0,x)
  let sector : Set (Fin 4→ℕ) := {k |
    cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 ∧
    32≤cappedRepresentative (k 2)*w}
  let f := fun k : Fin 4→ℕ=>
    ENNReal.ofReal (78400000*(cappedRepresentative (k 2))^2/cappedRepresentative (k 1))*
    (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k)
      z.1 z.2.1 z.2.2 ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b))
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  let source : Set (Fin 4→ℕ) := {k | k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0)≤128*P}
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have heq : sector.indicator f=(source∩sector).indicator f := by
    funext k
    by_cases hk : k∈sector
    · by_cases hsrc : k∈source
      · rw [indicator_of_mem hk,indicator_of_mem (show k∈source∩sector from ⟨hsrc,hk⟩)]
      · rw [indicator_of_mem hk,indicator_of_notMem (show k∉source∩sector from fun h=>hsrc h.1)]
        dsimp [f]
        rw [F.physicalBinDensity_integral_source_truncate hs hsource N hN X V hα.snd.measurable
          measurableSet_Icc (Icc_subset_Icc ha hb) w k hsrc,mul_zero]
    · rw [indicator_of_notMem hk,indicator_of_notMem (show k∉source∩sector from fun h=>hk h.2)]
  have hset : source∩sector={k : Fin 4→ℕ | k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0)≤128*P ∧
      cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 ∧
      32≤cappedRepresentative (k 2)*w} := by
    ext k
    exact ⟨fun h=>⟨h.1.1,h.1.2.1,h.1.2.2,h.2⟩,fun h=>⟨⟨h.1,h.2.1,h.2.2.1⟩,h.2.2.2⟩⟩
  change (∑'k,sector.indicator f k)≤_
  rw [heq,hset]
  have hbnd := hsum s T F hs hT h0 zX S N a b w M A P hS hS0 ha hb hab
    hM hA hP hL hw hwP HX HZ
  apply hbnd.trans
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hL0 : 0≤Real.log (2+P) := zero_le_one.trans hL
  have hscalar : Real.sqrt (Real.log (2+P))*(N:ℝ)^2≤Cn^2*(Real.log (2+P))^3 := by
    calc
      _ ≤ Real.log (2+P)*(Cn*Real.log (2+P))^2 :=
        mul_le_mul (Real.sqrt_le_self_iff.mpr (Or.inr hL))
          (pow_le_pow_left₀ (Nat.cast_nonneg N) hNc _) (by positivity) hL0
      _ = _ := by ring
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = (Cs*(1+E)*(1+16384*(M+Real.sqrt A))*w)*
        (Real.sqrt (Real.log (2+P))*(N:ℝ)^2) := by ring
    _ ≤ (Cs*(1+E)*(1+16384*(M+Real.sqrt A))*w)*(Cn^2*(Real.log (2+P))^3) :=
      mul_le_mul_of_nonneg_left hscalar (by positivity)
    _ = _ := by dsimp [E]; ring

lemma capped_radius_tail {H R : ℝ} (hH : 0<H) (hR : 0 ≤ R) :
    (∑'n : ℕ,if H*cappedRepresentative n ≤ R then ENNReal.ofReal (H*cappedRepresentative n) else 0) ≤
      ENNReal.ofReal (6*R) := by
  classical
  rcases hR.eq_or_lt with hr0|hR
  · have hfalse (n : ℕ) : ¬H*cappedRepresentative n ≤ R := by
      rw [←hr0]
      exact not_le.mpr (mul_pos hH (cappedRepresentative_pos n))
    simp only [ite_eq_right (hfalse _),tsum_zero]
    rw [←hr0,mul_zero,ENNReal.ofReal_zero]
  · let g : ℤ→ℝ := fun k=>min (H*(2:ℝ)^k) (R^2/(H*(2:ℝ)^k))
    have hg0 (k : ℤ) : 0 ≤ g k := by dsimp [g]; positivity
    have hg : Summable g ∧ (∑'k : ℤ,g k) ≤ 6*R := by
      simpa only [one_pow,one_mul,mul_one,Real.sqrt_one] using
        (geometry_radial_balance (I:=1) (p:=1) (θ:=1) (φ:=1) (by norm_num) hR
          (by norm_num) (by norm_num) (by norm_num) hH)
    have he (n : ℕ) : cappedRepresentative n=(2:ℝ)^(-(n:ℤ)) := by
      simp only [cappedRepresentative,zpow_neg,zpow_natCast,inv_pow]
    have hinj : Function.Injective (fun n : ℕ=>-(n:ℤ)) := by
      intro a b hab
      exact_mod_cast neg_injective hab
    calc
      _  ≤  ∑'n : ℕ,ENNReal.ofReal (g (-(n:ℤ))) := by
        apply ENNReal.tsum_le_tsum
        intro n
        by_cases hn : H*cappedRepresentative n ≤ R
        · rw [ite_eq_left hn]
          apply ENNReal.ofReal_le_ofReal
          dsimp [g]
          rw [←he]
          apply le_min le_rfl
          apply (le_div_iff₀ (mul_pos hH (cappedRepresentative_pos n))).mpr
          nlinarith [sq_le_sq₀ (mul_pos hH (cappedRepresentative_pos n)).le hR.le |>.mpr hn]
        · rw [ite_eq_right hn]
          exact bot_le
      _  ≤  ∑'k : ℤ,ENNReal.ofReal (g k) :=
        ENNReal.tsum_comp_le_tsum_of_injective hinj (fun index => ENNReal.ofReal (g index))
      _ = ENNReal.ofReal (∑'k : ℤ,g k) := (ENNReal.ofReal_tsum_of_nonneg hg0 hg.1).symm
      _  ≤  _ := ENNReal.ofReal_le_ofReal hg.2

lemma Admissible.central_density_near_bin {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (k : Fin 4→ℕ) (J : Set ℝ) (I w : ℝ),
      MeasurableSet J → J⊆Icc 0 T → 0 ≤ I → volume J ≤ ENNReal.ofReal I →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let r := max 1 T*cappedRepresentative (k 3)
      ENNReal.ofReal (78400000*φ^2/θ)*
        (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k)
          z.1 z.2.1 z.2.2 ∂physicalBinMeasure V (representativeClosedBin T w k) J) ≤
      ENNReal.ofReal (C*I*p^3*θ*φ^4*r) := by
  obtain ⟨Cρ,hCρ,hdensity⟩ := hd₀.uniform_physicalBinDensity_constant
  refine ⟨5780275200000*Cρ,by positivity,?_⟩
  intro s T F hs hT h0 zX k J I w hJ hJT hI hvol
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := representativeClosedBin T w k
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let r := max 1 T*cappedRepresentative (k 3)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hr : 0<r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hBmax : B.rmax=2*r := by dsimp [B,representativeClosedBin,r]; ring
  have hBmin : B.rmin=r/2 := rfl
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hden : ∀z∈physicalBinBase V B J,
      physicalBinDensity s X V B z.1 z.2.1 z.2.2 ≤ ENNReal.ofReal (128*Cρ*p^3*θ^2) := by
    intro z hz
    have hzT : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩
    have hn := hdensity s T F hs h0 X V B z.1 z.2.1 z.2.2 p θ 1 hzT hp.le hθ.le (by norm_num)
      (by change p/32 ≤ p; linarith) le_rfl (by norm_num [B,representativeClosedBin])
    simpa only [min_eq_left (show θ ≤ 1 from cappedRepresentative_le_one _)] using hn
  have hnear := physicalBin_density_near hα.snd.measurable B hJ hφ.le le_rfl hden
  calc
    _  ≤  ENNReal.ofReal (78400000*φ^2/θ)*ENNReal.ofReal (128*Cρ*p^3*θ^2)*
        (volume J*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)) := by
      simpa only [mul_assoc] using mul_le_mul' le_rfl hnear
    _  ≤  ENNReal.ofReal (78400000*φ^2/θ)*ENNReal.ofReal (128*Cρ*p^3*θ^2)*
        (ENNReal.ofReal I*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)) := by gcongr
    _ = _ := by
      rw [hBmax,hBmin]
      rw [←ENNReal.ofReal_mul hI,
        ←ENNReal.ofReal_mul (mul_nonneg hI (by linarith : 0 ≤ 2*r-r/2)),
        ←ENNReal.ofReal_mul (by positivity : 0 ≤ 78400000*φ^2/θ),
        ←ENNReal.ofReal_mul (by positivity : 0 ≤ (78400000*φ^2/θ)*(128*Cρ*p^3*θ^2))]
      congr 1
      change (78400000*φ^2/θ)*(128*Cρ*p^3*θ^2)*(I*(2*r-r/2)*(384*φ^2))=
        5780275200000*Cρ*I*p^3*θ*φ^4*r
      field_simp [hθ.ne']
      ring

lemma Admissible.central_density_deficit_log_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (a b w P D : ℝ),
      0 ≤ a → b ≤ T → b-a ≤ (w/P)^2 → 0<w → w ≤ P → 0<P →
      1 ≤ Real.log (2+P) → 0 ≤ D →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2 ≤ P) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let sector : Set (Fin 4→ℕ) := {k | max 1 T*cappedRepresentative (k 3) ≤ D/P^2}
      (∑'k : Fin 4→ℕ,sector.indicator (fun k=>
        ENNReal.ofReal (78400000*(cappedRepresentative (k 2))^2/cappedRepresentative (k 1))*
        (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k)
          z.1 z.2.1 z.2.2 ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b))) k) ≤
      ENNReal.ofReal (C*D*w*(Real.log (2+P))^2) := by
  classical
  obtain ⟨Cρ,hCρ,hnear⟩ := hd₀.central_density_near_bin
  obtain ⟨Cn,hCn,hcount⟩ := exists_source_dyadic_count
  refine ⟨12*128^3*Cρ*Cn^2,by positivity,?_⟩
  intro s T F hs hT h0 zX a b w P D ha hb hab hw hwP hP hL hD hsource
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let I := (w/P)^2
  let sector : Set (Fin 4→ℕ) := {k | max 1 T*cappedRepresentative (k 3) ≤ D/P^2}
  let cfun := fun k : Fin 4→ℕ=>
    ENNReal.ofReal (78400000*(cappedRepresentative (k 2))^2/cappedRepresentative (k 1))*
    (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k)
      z.1 z.2.1 z.2.2 ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b))
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  let source : Set (Fin 4→ℕ) := {k | k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0) ≤ 128*P}
  let f := (source∩sector).indicator cfun
  let c := 6*128^3*Cρ*D*w
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
      have hφ1 : φ ≤ 1 := cappedRepresentative_le_one _
      let coeff := Cρ*I*(128*P)^3*φ
      have hcoeff : 0 ≤ coeff := by dsimp [coeff,I]; positivity
      have hpoint (nr : ℕ) : f ![np,nt,nf,nr] ≤
          ENNReal.ofReal coeff*(if max 1 T*cappedRepresentative nr ≤ D/P^2 then
            ENNReal.ofReal (max 1 T*cappedRepresentative nr) else 0) := by
        let k : Fin 4→ℕ := ![np,nt,nf,nr]
        by_cases hk : k∈source∩sector
        · have hkr : max 1 T*cappedRepresentative nr ≤ D/P^2 := hk.2
          rw [ite_eq_left hkr]
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
          have hφ4 : φ^4 ≤ φ := by
            calc
              φ^4 ≤ φ^1 := pow_le_pow_of_le_one hφ.le hφ1 (by norm_num)
              _ = φ := pow_one _
          change Cρ*I*(sourceRepresentative np)^3*cappedRepresentative nt*φ^4*
            (max 1 T*cappedRepresentative nr) ≤ coeff*(max 1 T*cappedRepresentative nr)
          dsimp [coeff]
          calc
            _  ≤  Cρ*I*(128*P)^3*1*φ*(max 1 T*cappedRepresentative nr) := by gcongr
            _ = _ := by ring
        · change (source∩sector).indicator cfun k ≤ _
          rw [indicator_of_notMem hk]
          exact bot_le
      have hsum := ENNReal.tsum_le_tsum hpoint
      rw [ENNReal.tsum_mul_left] at hsum
      have ht := capped_radius_tail (H:=max 1 T) (zero_lt_one.trans_le (le_max_left _ _))
        (show 0 ≤ D/P^2 by positivity)
      apply (hsum.trans (mul_le_mul' le_rfl ht)).trans
      rw [←ENNReal.ofReal_mul hcoeff,←ENNReal.ofReal_mul hc]
      apply ENNReal.ofReal_le_ofReal
      have hratio : w^2/P ≤ w := (div_le_iff₀ hP).mpr (by nlinarith only [mul_le_mul_of_nonneg_left hwP hw.le])
      calc
        _ = (6*128^3*Cρ*D*φ)*(w^2/P) := by dsimp [coeff,I]; field_simp
        _  ≤  (6*128^3*Cρ*D*φ)*w := mul_le_mul_of_nonneg_left hratio (by positivity)
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

lemma Admissible.direction_family_moving_log_bound {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (J : Set ℝ) (w P : ℝ) (Q : Set (Fin 4→ℕ)),
      0<P → 1≤Real.log (2+P) →
      (∀z,s.f (0,z)≠0→∀σ∈Icc 0 T,q (F.flow z σ).2≤P) →
      (∀k∈Q,cappedRepresentative (k 1)≤cappedRepresentative (k 2) ∧
        sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1) →
      MeasurableSet J → J⊆Icc 0 T → 0<w →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      ∀(ι : Type) (S : Finset ι) (a b ℓ : ι→ℝ),
      (∀i∈S,0<ℓ i) → (∀i∈S,2*ℓ i≤b i-a i) → (∀i∈S,Icc (a i) (b i)⊆J) →
      (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) →
      (∑i∈S,selectedAngularMovingCost s F.flow zX T w Q (directionWeight (a i) (b i) (ℓ i)))≤
      (∫⁻t in J,ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖)*
        ENNReal.ofReal (C*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w) := by
  obtain ⟨Cb,hCb,hb⟩ := hd.direction_family_moving_bound
  obtain ⟨Cn,hCn,hcount⟩ := exists_source_dyadic_count
  refine ⟨Cb*Cn^2,by positivity,?_⟩
  intro s T F hs hT h0 zX J w P Q hP hL hsource hQ hJ hJT hw hband hv ι S a b ℓ hℓ hlen hcell hdis
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  have hsourceN : ∀z,s.f (0,z)≠0→∀σ∈Icc 0 T,1024*q (F.flow z σ).2≤(2:ℝ)^N := by
    intro z hz σ hσ
    exact (mul_le_mul_of_nonneg_left (hsource z hz σ hσ) (by norm_num)).trans hN
  have hh := hb s T F hs hT h0 zX J w N Q hsourceN hQ hJ hJT hw hband hv ι S a b ℓ hℓ hlen hcell hdis
  apply hh.trans
  apply mul_le_mul' le_rfl
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Cb*Real.sqrt (max 1 T)*(Cn*Real.log (2+P))^2/w := by gcongr
    _ = _ := by ring

lemma Admissible.direction_family_weight_log_bound {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (J : Set ℝ) (w P : ℝ) (Q : Set (Fin 4→ℕ)),
      0<P → 1≤Real.log (2+P) →
      (∀z,s.f (0,z)≠0→∀σ∈Icc 0 T,q (F.flow z σ).2≤P) →
      (∀k∈Q,cappedRepresentative (k 1)≤cappedRepresentative (k 2) ∧
        sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1) →
      MeasurableSet J → J⊆Icc 0 T → 0<w →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      ∀(ι : Type) (S : Finset ι) (a b ℓ : ι→ℝ),
      (∀i∈S,0<ℓ i) → (∀i∈S,2*ℓ i≤b i-a i) → (∀i∈S,Icc (a i) (b i)⊆J) →
      (∑i∈S,selectedAngularWeightCost s F.flow zX T w Q (directionWeight (a i) (b i) (ℓ i)))≤
        (S.card:ℝ≥0∞)*ENNReal.ofReal (2*C*Real.sqrt (max 1 T)*(Real.log (2+P))^2) := by
  obtain ⟨Cb,hCb,hb⟩ := hd.direction_family_weight_bound
  obtain ⟨Cn,hCn,hcount⟩ := exists_source_dyadic_count
  refine ⟨Cb*Cn^2,by positivity,?_⟩
  intro s T F hs hT h0 zX J w P Q hP hL hsource hQ hJ hJT hw hband hv ι S a b ℓ hℓ hlen hcell
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  have hsourceN : ∀z,s.f (0,z)≠0→∀σ∈Icc 0 T,1024*q (F.flow z σ).2≤(2:ℝ)^N := by
    intro z hz σ hσ
    exact (mul_le_mul_of_nonneg_left (hsource z hz σ hσ) (by norm_num)).trans hN
  have hh := hb s T F hs hT h0 zX J w N Q hsourceN hQ hJ hJT hw hband hv ι S a b ℓ hℓ hlen hcell
  apply hh.trans
  apply mul_le_mul' le_rfl
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ 2*Cb*Real.sqrt (max 1 T)*(Cn*Real.log (2+P))^2 := by gcongr
    _ = _ := by ring

lemma unselected_multiplier_support_congr (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ)
    {G H : ℝ→Vec→L[ℝ]Vec} (hG : EqOn G H (tsupport ψ)) :
    (fun p=>G (labelReceiverTime α zX T p) (unselectedLabelSignedForce s α zX T Q ψ p))=
      fun p=>H (labelReceiverTime α zX T p) (unselectedLabelSignedForce s α zX T Q ψ p) := by
  funext p
  by_cases ht : labelReceiverTime α zX T p∈tsupport ψ
  · rw [hG ht]
  · have hz := image_eq_zero_of_notMem_tsupport ht
    simp only [unselectedLabelSignedForce,hz,zero_smul,smul_zero,map_zero]

lemma SmoothClassicalPrefix.actual_angular_decomposition {d : Datum} {s : Solution} {T w : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hT : 0 ≤ T) (hw : 0<w)
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {ψ : ℝ→ℝ} {L : NNReal} (hψ : LipschitzWith L ψ)
    (hψb : ∀t∈Icc 0 T,|ψ t| ≤ 1) (hψT : ψ T=0)
    (hS : tsupport ψ⊆Icc 0 T) (hband : ∀t∈tsupport ψ,w/16 ≤ ‖(F.flow zX t).2‖) :
    let G := fun t=>angularMultiplierCLM w (F.flow zX t).2
    let G' := fun t=>angularDerivativeCLM w (F.flow zX t).2
      (lorentzField s.E s.B (t,F.flow zX t)).2
    (∫t in Ioo (0:ℝ) T,ψ t • G t
      (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
        boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2)))=
      (4*Real.pi)⁻¹ • ((∫p,G (labelReceiverTime F.flow zX T p)
        (unselectedLabelSignedForce s F.flow zX T Q ψ p))+
        (∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q ψ G z)+
        ∫p,selectedMultiplierCosts s F.flow zX T Q ψ G G' p) := by
  dsimp only
  have henergy : EnergyPrefix s T := by
    refine ⟨(hs.f_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
      (hs.E_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
      (hs.B_smooth.of_le (by decide)).mono (fun _ hp => hp.1),hs.nonnegative,
      hs.E_L2,hs.B_L2,hs.compact,?_,?_⟩
    · intro time ht position momentum
      have hh := (hs.equations time ht.1.le ht.2).1 position momentum
      rwa [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at hh
    · intro time ht position
      have he := (hs.equations time ht.1.le ht.2).2.1 position
      have hb := (hs.equations time ht.1.le ht.2).2.2.1 position
      rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at he hb
      exact ⟨he,hb⟩
  obtain ⟨hW,hW',hd⟩ := F.prefixAngular_regular henergy hT hw zX
  have he := hs.selected_multiplier_decomposition hT F zX Q hψ hψb hψT hW hW' hd
  have hG : EqOn (prefixAngularMultiplier s F.flow T w hw zX)
      (fun t=>angularMultiplierCLM w (F.flow zX t).2) (tsupport ψ) :=
    fun t ht=>(prefixAngular_highband hw zX (hS ht) (hband t ht)).1
  have hG' : EqOn (prefixAngularRate s F.flow T w hw zX)
      (fun t=>angularDerivativeCLM w (F.flow zX t).2
        (lorentzField s.E s.B (t,F.flow zX t)).2) (tsupport ψ) :=
    fun t ht=>(prefixAngular_highband hw zX (hS ht) (hband t ht)).2
  obtain ⟨_eF,eC⟩ := selected_multiplier_support_congr s F.flow zX T Q ψ hG hG'
  rw [eC,selected_initial_support_congr F.flow zX T (fun z=>s.f (0,z)) Q ψ hG,
    unselected_multiplier_support_congr s F.flow zX T Q ψ hG] at he
  rw [←he]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t _ht
  dsimp only
  by_cases ht : t∈tsupport ψ
  · rw [hG ht]
  · rw [image_eq_zero_of_notMem_tsupport ht,zero_smul,zero_smul]

lemma angularMultiplierCLM_norm_le {w : ℝ} (hw : 0<w) {v : Vec}
    (hv : w/64 ≤ ‖v‖) : ‖angularMultiplierCLM w v‖ ≤ 64 := by
  have hρ : 0<‖v‖ := (div_pos hw (by norm_num)).trans_le hv
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro h
  rw [angularMultiplierCLM_apply,angularMultiplier,norm_smul,Real.norm_eq_abs,
    abs_of_pos (div_pos hw hρ)]
  apply mul_le_mul _ (transverseProjection_norm v h) (norm_nonneg _) (by norm_num)
  apply (div_le_iff₀ hρ).mpr
  linarith only [hv]

lemma extendedAngularCLM_norm_le (w : ℝ) (hw : 0<w) (v : Vec) :
    ‖extendedAngularCLM w hw v‖ ≤ 64 := by
  have hb : 0 ≤ angularZeroBump w hw v := (angularZeroBump w hw).nonneg
  have hb1 : angularZeroBump w hw v ≤ 1 := (angularZeroBump w hw).le_one
  by_cases hv : ‖v‖<w/64
  · have hvb : v∈closedBall (0:Vec) (angularZeroBump w hw).rIn := by
      simpa only [mem_closedBall,dist_zero_right,angularZeroBump] using hv.le
    rw [extendedAngularCLM,(angularZeroBump w hw).one_of_mem_closedBall hvb,sub_self,
      zero_smul ℝ (angularMultiplierCLM w v),norm_zero]
    norm_num
  · rw [extendedAngularCLM,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hb1)]
    calc
      _ ≤ ‖angularMultiplierCLM w v‖ := by
        nlinarith only [hb,hb1,norm_nonneg (angularMultiplierCLM w v)]
      _ ≤ 64 := angularMultiplierCLM_norm_le hw (le_of_not_gt hv)

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

lemma directionWeight_integrable {a b ℓ : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ ≤ b-a) :
    Integrable (directionWeight a b ℓ) := by
  have hc : HasCompactSupport (directionWeight a b ℓ) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (directionWeight_tsupport hℓ hab)
  exact (directionWeight_lipschitz a b ℓ).continuous.integrable_of_hasCompactSupport hc

lemma directionWeight_family_mass {ι : Type*} (S : Finset ι) (a b ℓ : ι→ℝ)
    (hℓ : ∀i∈S,0<ℓ i) (hlen : ∀i∈S,2*ℓ i ≤ b i-a i)
    (hdis : (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    {c d T : ℝ} (hcd : c ≤ d) (hcell : ∀i∈S,Icc (a i) (b i)⊆Icc c d) :
    (∑i∈S,∫t in Ioo (0:ℝ) T,|directionWeight (a i) (b i) (ℓ i) t|) ≤ d-c := by
  have hi (i : ι) (hi : i∈S) : Integrable (directionWeight (a i) (b i) (ℓ i)) :=
    directionWeight_integrable (hℓ i hi) (hlen i hi)
  have hn (i : ι) (hi : i∈S) (t : ℝ) : 0 ≤ directionWeight (a i) (b i) (ℓ i) t :=
    (directionWeight_bounds (hℓ i hi) (hlen i hi)).1
  have hsumint : Integrable (fun t=>∑i∈S,directionWeight (a i) (b i) (ℓ i) t) :=
    integrable_finsetSum S hi
  calc
    _ = ∫t in Ioo (0:ℝ) T,∑i∈S,directionWeight (a i) (b i) (ℓ i) t := by
      rw [integral_finsetSum S (fun i hiS=>(hi i hiS).integrableOn)]
      apply Finset.sum_congr rfl
      intro i hiS
      simp_rw [abs_of_nonneg (hn i hiS _)]
    _ ≤ ∫t,∑i∈S,directionWeight (a i) (b i) (ℓ i) t :=
      integral_mono_measure Measure.restrict_le_self
        (ae_of_all _ (fun t=>Finset.sum_nonneg (fun i hiS=>hn i hiS t))) hsumint
    _ = ∫t in Icc c d,∑i∈S,directionWeight (a i) (b i) (ℓ i) t := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      apply Finset.sum_eq_zero
      intro i hiS
      exact image_eq_zero_of_notMem_tsupport
        (fun hit=>ht (hcell i hiS (directionWeight_tsupport (hℓ i hiS) (hlen i hiS) hit)))
    _ ≤ ∫_t in Icc c d,(1:ℝ) := by
      apply integral_mono_ae hsumint.integrableOn (integrableOn_const measure_Icc_lt_top.ne)
      exact ae_of_all _ (fun t=>directionWeight_sum_le_one S a b ℓ hℓ hlen hdis t)
    _ = d-c := by
      simp only [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,ENNReal.toReal_ofReal (sub_nonneg.mpr hcd),smul_eq_mul,mul_one]

lemma Admissible.direction_family_initial_bound {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (w c e : ℝ),0<w → c ≤ e →
      ∀(ι : Type) (S : Finset ι) (a b ℓ : ι→ℝ) (Q : ι→Set (Fin 4→ℕ)),
      (∀i∈S,0<ℓ i) → (∀i∈S,2*ℓ i ≤ b i-a i) →
      (∀i∈S,Icc (a i) (b i)⊆Icc c e) →
      (∀i∈S,Icc (a i) (b i)⊆Icc 0 T) →
      (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) →
      (∀i∈S,∀t∈Icc (a i) (b i),w/16 ≤ ‖(F.flow zX t).2‖) →
      (∑i∈S,‖∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) (Q i)
        (directionWeight (a i) (b i) (ℓ i)) (fun t=>angularMultiplierCLM w (F.flow zX t).2) z‖) ≤
      C*T*(e-c) := by
  obtain ⟨C,hC,hbound⟩ := selectedInitialKernel_integrable_bound hd.1.continuous hd.2.1 hd.2.2.1
  refine ⟨64*C,by positivity,?_⟩
  intro s T F hs hT h0 zX w c e hw hce ι S a b ℓ Q hℓ hlen hcell hcellT hdis hband
  let W := prefixAngularMultiplier s F.flow T w hw zX
  have hW : Continuous W := (F.prefixAngular_regular hs hT hw zX).1
  have hWM (t : ℝ) : ‖W t‖ ≤ 64 := extendedAngularCLM_norm_le w hw _
  have hdata : (fun z=>s.f (0,z))=d.f₀ := funext h0
  have hbnd (i : ι) (hi : i∈S) :
      ‖∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) (Q i)
        (directionWeight (a i) (b i) (ℓ i)) (fun t=>angularMultiplierCLM w (F.flow zX t).2) z‖ ≤
      64*C*T*(∫t in Ioo (0:ℝ) T,|directionWeight (a i) (b i) (ℓ i) t|) := by
    have hG : EqOn W (fun t=>angularMultiplierCLM w (F.flow zX t).2)
        (tsupport (directionWeight (a i) (b i) (ℓ i))) := by
      intro t ht
      have htc := directionWeight_tsupport (hℓ i hi) (hlen i hi) ht
      exact (prefixAngular_highband hw zX (hcellT i hi htc) (hband i hi t htc)).1
    rw [←selected_initial_support_congr F.flow zX T (fun z=>s.f (0,z)) (Q i)
      (directionWeight (a i) (b i) (ℓ i)) hG,hdata]
    have hh := (hbound s.E s.B T F zX (Q i) (directionWeight (a i) (b i) (ℓ i)) W 64 hT
      (by norm_num) (directionWeight_lipschitz _ _ _).continuous.continuousOn hW.continuousOn
      (fun t _=>hWM t)).2
    convert hh using 1
    ring
  calc
    _ ≤ ∑i∈S,64*C*T*(∫t in Ioo (0:ℝ) T,|directionWeight (a i) (b i) (ℓ i) t|) := Finset.sum_le_sum hbnd
    _ = 64*C*T*(∑i∈S,∫t in Ioo (0:ℝ) T,|directionWeight (a i) (b i) (ℓ i) t|) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (directionWeight_family_mass S a b ℓ hℓ hlen hdis hce hcell) (by positivity)

lemma Admissible.supported_boundary_force_bound {d : Datum} (hd : Admissible d)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (E B : Field) (F : PhaseFlowOn E B T) (zX : Phase),
      zX∈tsupport d.f₀ → ∀t∈Ioc (0:ℝ) T,
      ‖boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1
        (velocity (F.flow zX t).2)‖ ≤ C := by
  obtain ⟨R,hR⟩ := hd.2.1.bddAbove_image
    (show ContinuousOn (fun z : Phase=>‖z.1‖) (tsupport d.f₀) from continuous_fst.norm.continuousOn)
  obtain ⟨C,hC,hb⟩ := boundaryLorentzForce_datum_bound hd T (R+T)
  refine ⟨C,hC,?_⟩
  intro E B F zX hz t ht
  have hx0 : ‖zX.1‖ ≤ R := hR ⟨zX,hz,rfl⟩
  have hh := (F.position_lipschitz zX).dist_le_mul t ⟨ht.1.le,ht.2⟩ 0 ⟨le_rfl,hT⟩
  simp only [F.initial,NNReal.coe_one,one_mul,Real.dist_eq,sub_zero,abs_of_nonneg ht.1.le] at hh
  apply hb t ht (F.flow zX t).1 _ _ (norm_velocity_lt_one _).le
  rw [mem_closedBall,dist_zero_right]
  calc
    ‖(F.flow zX t).1‖=‖((F.flow zX t).1-zX.1)+zX.1‖ := by rw [sub_add_cancel]
    _ ≤ ‖(F.flow zX t).1-zX.1‖+‖zX.1‖ := norm_add_le _ _
    _ ≤ t+R := add_le_add (by simpa only [dist_eq_norm] using hh) hx0
    _ ≤ R+T := by linarith only [ht.2]

lemma Admissible.direction_family_datum_bound {d : Datum} (hd : Admissible d)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (E B : Field) (F : PhaseFlowOn E B T) (zX : Phase),
      zX∈tsupport d.f₀ → ∀(w c e : ℝ),0<w → c ≤ e →
      ∀(ι : Type) (S : Finset ι) (a b ℓ : ι→ℝ),
      (∀i∈S,0<ℓ i) → (∀i∈S,2*ℓ i ≤ b i-a i) →
      (∀i∈S,Icc (a i) (b i)⊆Icc c e) →
      (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) →
      (∀i∈S,∀t∈Icc (a i) (b i),w/16 ≤ ‖(F.flow zX t).2‖) →
      (∑i∈S,‖∫t in Ioo (0:ℝ) T,directionWeight (a i) (b i) (ℓ i) t •
        angularMultiplierCLM w (F.flow zX t).2
          (boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1
            (velocity (F.flow zX t).2))‖) ≤ C*(e-c) := by
  obtain ⟨C,hC,hbound⟩ := hd.supported_boundary_force_bound T hT
  refine ⟨64*C,by positivity,?_⟩
  intro E B F zX hz w c e hw hce ι S a b ℓ hℓ hlen hcell hdis hband
  have hbnd (i : ι) (hi : i∈S) :
      ‖∫t in Ioo (0:ℝ) T,directionWeight (a i) (b i) (ℓ i) t •
        angularMultiplierCLM w (F.flow zX t).2
          (boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1
            (velocity (F.flow zX t).2))‖ ≤
      64*C*(∫t in Ioo (0:ℝ) T,|directionWeight (a i) (b i) (ℓ i) t|) := by
    rw [←integral_const_mul]
    apply norm_integral_le_of_norm_le ((directionWeight_integrable (hℓ i hi) (hlen i hi)).norm.const_mul _).integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    by_cases hψ : directionWeight (a i) (b i) (ℓ i) t=0
    · simp only [hψ,zero_smul,norm_zero,mul_zero,le_refl]
    · have htc := (directionWeight_ne_zero_interior (hℓ i hi) (hlen i hi) hψ)
      have hG := angularMultiplierCLM_norm_le hw
        (show w/64 ≤ ‖(F.flow zX t).2‖ by linarith only [hw,hband i hi t (Ioo_subset_Icc_self htc)])
      have hB := hbound E B F zX hz t ⟨ht.1,ht.2.le⟩
      rw [norm_smul,Real.norm_eq_abs]
      calc
        _ ≤ |directionWeight (a i) (b i) (ℓ i) t| * (64*C) :=
          mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul hG hB (norm_nonneg _) (by norm_num))) (abs_nonneg _)
        _ = _ := by ring
  calc
    _ ≤ ∑i∈S,64*C*(∫t in Ioo (0:ℝ) T,|directionWeight (a i) (b i) (ℓ i) t|) := Finset.sum_le_sum hbnd
    _ = 64*C*(∑i∈S,∫t in Ioo (0:ℝ) T,|directionWeight (a i) (b i) (ℓ i) t|) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (directionWeight_family_mass S a b ℓ hℓ hlen hdis hce hcell) (by positivity)

end RVM

end

end OAI
