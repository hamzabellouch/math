import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.PhysicalBinPhaseSet
import OAI.Analysis.VlasovMaxwell.Population.RepresentativeClosedBinSourceIndices
import OAI.Analysis.VlasovMaxwell.Retarded.GeneralDirectRadial

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.direct_transport_radius_near {d : Datum} (hd₀ : Admissible d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (k : Fin 4→ℕ) (j : ℕ) (a b I w : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ I → 0 < I →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let σ := cappedRepresentative j
      let r := max 1 T*cappedRepresentative (k 3)
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := relativeRepresentativeClosedBin T w k j
      (∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V B z
        ∂physicalBinMeasure V B (Icc a b)) ≤
      ENNReal.ofReal (C*I*r*p*(min θ σ)^2*φ^2*(θ+φ)/θ^3) := by
  obtain ⟨Cρ,hCρ,hρ⟩ := hd₀.uniform_physicalBinDensity_constant
  refine ⟨154618822656*Cρ,by positivity,?_⟩
  intro s T F hs hT h0 zX S k j a b I w hS hS0 ha hb hJI hI
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let σ := cappedRepresentative j
  let r := max 1 T*cappedRepresentative (k 3)
  let B := relativeRepresentativeClosedBin T w k j
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hσ : 0<σ := cappedRepresentative_pos _
  have hr : 0<r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hBmax : B.rmax=2*r := by dsimp [B,relativeRepresentativeClosedBin,representativeClosedBin,r]; ring
  have hBmin : B.rmin=r/2 := rfl
  have hBDmin : B.Dmin=φ^2/2 := rfl
  have hα := F.continuous_prefixFlow hs hT
  have hdensity (z : ConeCoordinate) (hz : z∈physicalBinBase V B (Icc a b)) :
      physicalBinDensity s X V B z.1 z.2.1 z.2.2 ≤
        ENNReal.ofReal ((128*Cρ)*p^3*(min θ σ)^2) := by
    exact hρ s T F hs h0 _ _ B _ _ _ p θ σ
      ⟨hz.2.1.1,hz.2.1.2.trans (hz.1.2.trans hb)⟩ hp.le hθ.le hσ.le
      (by change p/32≤p; linarith only [hp]) le_rfl le_rfl
  have hn := F.direct_transport_near_far hs hT zX B hS hS0 (Icc_subset_Icc ha hb)
    (by positivity : 0<p/128) hθ hφ.le (show p/128≤B.qmin from le_rfl)
    le_rfl le_rfl le_rfl (by rw [hBmin]; positivity) (by rw [hBDmin]; positivity) hdensity
  have hvolume : volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2) ≤
      ENNReal.ofReal (576*I*r*φ^2) := by
    rw [Real.volume_Icc,hBmax,hBmin]
    calc
      _ ≤ ENNReal.ofReal I*ENNReal.ofReal (2*r-r/2)*ENNReal.ofReal (384*φ^2) := by gcongr
      _ = _ := by
        rw [←ENNReal.ofReal_mul hI.le,←ENNReal.ofReal_mul (mul_nonneg hI.le (by linarith : 0≤2*r-r/2))]
        congr 1
        ring
  apply hn.trans
  calc
    _ ≤ ENNReal.ofReal (128*(θ+φ)/((p/128)^2*θ^3))*
        (ENNReal.ofReal ((128*Cρ)*p^3*(min θ σ)^2)*ENNReal.ofReal (576*I*r*φ^2)) :=
      mul_le_mul' le_rfl ((min_le_left _ _).trans (mul_le_mul' le_rfl hvolume))
    _ = _ := by
      rw [←ENNReal.ofReal_mul (by positivity : 0≤(128*Cρ)*p^3*(min θ σ)^2),
        ←ENNReal.ofReal_mul (by positivity : 0≤128*(θ+φ)/((p/128)^2*θ^3))]
      congr 1
      dsimp only [p,θ,φ,σ,r] at *
      field_simp
      ring

lemma capped_linear_radius_sum {C H : ℝ} (hC : 0≤C) (hH : 0≤H) :
    (∑'n : ℕ,ENNReal.ofReal (C*(H*cappedRepresentative n)))=ENNReal.ofReal (2*C*H) := by
  dsimp only [cappedRepresentative]
  simp_rw [←mul_assoc,ENNReal.ofReal_mul (mul_nonneg hC hH)]
  rw [ENNReal.tsum_mul_left,ennreal_capped_half_sum]
  rw [←ENNReal.ofReal_ofNat (n:=2),←ENNReal.ofReal_mul (mul_nonneg hC hH)]
  congr 1
  ring

lemma Admissible.direct_transport_remaining_all_radii {d : Datum} (hd₀ : Admissible d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b I w P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ I → 0 < I → 0<w → 0<P → w≤P →
      I≤(w/P)^2 → sourceRepresentative np≤128*P →
      cappedRepresentative nφ≤16*cappedRepresentative nθ →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      (∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V (B nr) z
        ∂physicalBinMeasure V (B nr) (Icc a b)) ≤
      ENNReal.ofReal (C*max 1 T*w) := by
  obtain ⟨C,hC,hnear⟩ := hd₀.direct_transport_radius_near
  refine ⟨4352*C,by positivity,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b I w P hS hS0 ha hb hJI hI hw hP hwP hIw hpP hφθ
  dsimp only
  let p := sourceRepresentative np
  let θ := cappedRepresentative nθ
  let φ := cappedRepresentative nφ
  let σ := cappedRepresentative j
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hσ : 0<σ := cappedRepresentative_pos _
  have hν : 0≤ min θ σ := le_min hθ.le hσ.le
  have hφ1 : φ≤1 := cappedRepresentative_le_one _
  have hIp : I*p≤128*w := (mul_le_mul_of_nonneg_right hIw hp.le).trans
    (direction_interval_momentum_factor hP hp.le hw.le hpP hwP)
  have hcoef : I*p*(min θ σ)^2*φ^2*(θ+φ)/θ^3 ≤ 2176*w := by
    have hsq : (min θ σ)^2≤θ^2 := pow_le_pow_left₀ hν (min_le_left _ _) 2
    have hφsq : φ^2≤1 := pow_le_one₀ hφ.le hφ1
    calc
      _ ≤ I*p*θ^2*1*(17*θ)/θ^3 := by gcongr; linarith only [hφθ]
      _ = 17*(I*p) := by field_simp
      _ ≤ 17*(128*w) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ∑'nr : ℕ,ENNReal.ofReal ((2176*C*w)*(max 1 T*cappedRepresentative nr)) := by
      apply ENNReal.tsum_le_tsum
      intro nr
      have hn := hnear s T F hs hT h0 zX S ![np,nθ,nφ,nr] j a b I w hS hS0 ha hb hJI hI
      apply hn.trans
      apply ENNReal.ofReal_le_ofReal
      dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Matrix.cons_val,Fin.reduceFinMk]
      calc
        _ = (C*(max 1 T*cappedRepresentative nr))*(I*p*(min θ σ)^2*φ^2*(θ+φ)/θ^3) := by ring
        _ ≤ (C*(max 1 T*cappedRepresentative nr))*(2176*w) :=
          mul_le_mul_of_nonneg_left hcoef (mul_nonneg hC (mul_nonneg (zero_le_one.trans (le_max_left _ _)) (cappedRepresentative_pos nr).le))
        _ = _ := by ring
    _ = _ := by
      rw [capped_linear_radius_sum (by positivity) (by positivity)]
      congr 1
      ring

lemma transport_absolute_coefficient {I p θ φ σ w P : ℝ}
    (hI : 0≤I) (hp : 0≤p) (hθ : 0<θ) (hφ : 0≤φ) (hσ : 0≤σ)
    (hφ1 : φ≤1) (hpθ : 1≤p*θ) (hw : 1≤w) (hP : 0<P)
    (hwP : w≤P) (hIp : I≤(w/P)^2) (hpP : p≤128*P) :
    I*p*(min θ σ)^2*φ^2*(θ+φ)/θ^3≤16512*w^2 := by
  have hν : 0≤ min θ σ := le_min hθ.le hσ
  have hsq : (min θ σ)^2≤θ^2 := pow_le_pow_left₀ hν (min_le_left _ _) 2
  have hφsq : φ^2≤1 := pow_le_one₀ hφ hφ1
  have hinv : 1/θ≤p := (div_le_iff₀ hθ).mpr hpθ
  have hIp1 : I*p≤128*w := (mul_le_mul_of_nonneg_right hIp hp).trans
    (direction_interval_momentum_factor hP hp (zero_le_one.trans hw) hpP hwP)
  have hIp2 : I*p^2≤16384*w^2 := by
    calc
      _ ≤ (w/P)^2*(128*P)^2 := by gcongr
      _ = _ := by field_simp; ring
  calc
    _ ≤ I*p*θ^2*1*(θ+1)/θ^3 := by gcongr
    _ = I*p*(1+1/θ) := by field_simp
    _ ≤ I*p*(1+p) := by gcongr
    _ = I*p+I*p^2 := by ring
    _ ≤ 128*w+16384*w^2 := add_le_add hIp1 hIp2
    _ ≤ 16512*w^2 := by nlinarith [sq_nonneg (w-1)]

lemma Admissible.direct_transport_all_radii_consistent {d : Datum} (hd₀ : Admissible d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b I w P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ I → 0 < I → 1≤w → 0<P → w≤P →
      I≤(w/P)^2 → sourceRepresentative np≤128*P →
      1≤ sourceRepresentative np*cappedRepresentative nθ →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      (∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V (B nr) z
        ∂physicalBinMeasure V (B nr) (Icc a b)) ≤
      ENNReal.ofReal (C*max 1 T*w^2) := by
  obtain ⟨C,hC,hnear⟩ := hd₀.direct_transport_radius_near
  refine ⟨33024*C,by positivity,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b I w P hS hS0 ha hb hJI hI hw hP hwP hIw hpP hpθ
  dsimp only
  have hp : 0<sourceRepresentative np := by dsimp [sourceRepresentative]; positivity
  have hcoef := transport_absolute_coefficient hI.le hp.le (cappedRepresentative_pos nθ)
    (cappedRepresentative_pos nφ).le (cappedRepresentative_pos j).le
    (cappedRepresentative_le_one nφ) hpθ hw hP hwP hIw hpP
  calc
    _ ≤ ∑'nr : ℕ,ENNReal.ofReal ((16512*C*w^2)*(max 1 T*cappedRepresentative nr)) := by
      apply ENNReal.tsum_le_tsum
      intro nr
      have hn := hnear s T F hs hT h0 zX S ![np,nθ,nφ,nr] j a b I w hS hS0 ha hb hJI hI
      apply hn.trans
      apply ENNReal.ofReal_le_ofReal
      dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Matrix.cons_val,Fin.reduceFinMk]
      calc
        _ = (C*(max 1 T*cappedRepresentative nr))*(I*sourceRepresentative np*
              (min (cappedRepresentative nθ) (cappedRepresentative j))^2*
              (cappedRepresentative nφ)^2*(cappedRepresentative nθ+cappedRepresentative nφ)/
              (cappedRepresentative nθ)^3) := by ring
        _ ≤ (C*(max 1 T*cappedRepresentative nr))*(16512*w^2) :=
          mul_le_mul_of_nonneg_left hcoef (mul_nonneg hC (mul_nonneg
            (zero_le_one.trans (le_max_left _ _)) (cappedRepresentative_pos nr).le))
        _ = _ := by ring
    _ = _ := by
      rw [capped_linear_radius_sum (by positivity) (by positivity)]
      congr 1
      ring

lemma physicalDirectTransport_integral_geometry_zero (s : Solution) {T w : ℝ}
    {X V : ℝ→Vec} (hV : Measurable V) {J : Set ℝ} (hJ : MeasurableSet J)
    {k : Fin 4→ℕ} {j : ℕ}
    (hbad : ¬1≤ sourceRepresentative (k 0)*cappedRepresentative (k 1)) :
    (∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V (relativeRepresentativeClosedBin T w k j) z
      ∂physicalBinMeasure V (relativeRepresentativeClosedBin T w k j) J)=0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV _ hJ)] with z hz
  have hempty : coneBinMomentumSet (relativeRepresentativeClosedBin T w k j) z.2.2.1 (velocity (V z.1))=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    exact hbad (relativeRepresentative_nonempty_geometry hz hv).1
  simp only [physicalDirectTransportDensity,hempty,Measure.restrict_empty,lintegral_zero_measure,mul_zero,Pi.zero_apply]

lemma Admissible.direct_transport_all_radii {d : Datum} (hd₀ : Admissible d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b I w P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ I → 0 < I → 1≤w → 0<P → w≤P →
      I≤(w/P)^2 → sourceRepresentative np≤128*P →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      (∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V (B nr) z
        ∂physicalBinMeasure V (B nr) (Icc a b)) ≤
      ENNReal.ofReal (C*max 1 T*w^2) := by
  obtain ⟨C,hC,hbound⟩ := hd₀.direct_transport_all_radii_consistent
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b I w P hS hS0 ha hb hJI hI hw hP hwP hIw hpP
  dsimp only
  by_cases hgeometry : 1≤ sourceRepresentative np*cappedRepresentative nθ
  · exact hbound s T F hs hT h0 zX S np nθ nφ j a b I w P hS hS0 ha hb hJI hI hw hP hwP hIw hpP hgeometry
  · have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
      ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
    have hz (nr : ℕ) : (∫⁻z : ConeCoordinate,physicalDirectTransportDensity s
        (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>(prefixFlow F.flow T zX t).2)
        (relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j) z
        ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2)
          (relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j) (Icc a b))=0 := by
      exact physicalDirectTransport_integral_geometry_zero s hV measurableSet_Icc hgeometry
    simp_rw [hz,tsum_zero]
    exact bot_le

lemma exists_dyadicFactor_positive {x : ℝ} (hx : 0<x) (hx1 : x≤1) :
    ∃n : ℕ,0<dyadicFactor n x := by
  by_contra hn
  push Not at hn
  have hz (n : ℕ) : dyadicFactor n x=0 := le_antisymm (hn n) (dyadicFactor_nonneg _ _)
  have hh := tsum_dyadicFactor hx hx1
  simp_rw [hz] at hh
  simp at hh

lemma exists_dyadicMultiFactor_positive {ι : Type*} [Fintype ι] {x : ι→ℝ}
    (hx : ∀i,0<x i) (hx1 : ∀i,x i≤1) : ∃k : ι→ℕ,0<dyadicMultiFactor k x := by
  choose k hk using fun i=>exists_dyadicFactor_positive (hx i) (hx1 i)
  exact ⟨k,Finset.prod_pos (fun i _=>hk i)⟩

abbrev DirectOuterIndex (N : ℕ) := Fin 4→Fin N

def directOuterBin {N : ℕ} (T w : ℝ) (i : DirectOuterIndex N) (nr : ℕ) : ClosedConeBin :=
  relativeRepresentativeClosedBin T w ![(i 0).val,(i 1).val,(i 2).val,nr] (i 3).val

lemma physical_direct_finite_cover {T w P t σ : ℝ} {V : ℝ→Vec} {J : Set ℝ}
    {N : ℕ} (hP : 0≤P) (hwP : w≤P) (hN : 8192*P≤(2:ℝ)^N)
    (ht : t∈J) (htT : t≤T) (hσ : σ∈Ico 0 t)
    (hband : q (V t)∈Icc (w/8) (8*w)) (n : Sphere) (v : Vec) (hq : q v≤P) :
    ∃i : DirectOuterIndex N, ∃nr : ℕ,
      sourceRepresentative (i 0).val≤128*P ∧
      (t,σ,n)∈physicalBinBase V (directOuterBin T w i nr) J ∧
      v∈coneBinMomentumSet (directOuterBin T w i nr) n.1 (velocity (V t)) := by
  have hr : 0<t-σ := sub_pos.mpr hσ.2
  have hrT : t-σ≤ max 1 T := by linarith [le_max_right (1:ℝ) T,hσ.1]
  obtain ⟨k,hk⟩ := exists_dyadicMultiFactor_positive
    (physicalCutoffCoordinates_pos (v:=v) (w:=V t) (sphere_norm n) hr)
    (physicalCutoffCoordinates_le_one (v:=v) (w:=V t) (sphere_norm n) hrT)
  obtain ⟨j,hj⟩ := exists_relative_dyadic_positive v (V t)
  have hrel : 0<relativePhysicalFactor T (t-σ) n.1 v (V t) k j := mul_pos hk hj
  have hvN : 1024*q v≤(2:ℝ)^N := by linarith only [hq,hP,hN]
  have hidx := relativePhysicalFactor_positive_indices (sphere_norm n) hvN hrel
  have hW : 1024*q (V t)≤(2:ℝ)^N := by linarith only [hband.2,hwP,hN]
  have hnf : k 2<N := source_angle_index_lt (sphere_norm n)
    (show DyadicBand (k 2) (Real.sqrt ((1-dot n.1 (velocity (V t)))/2)) from
      dyadicMultiFactor_positive_bands hk 2) hW
  let i : DirectOuterIndex N := ![⟨k 0,hidx.1⟩,⟨k 1,hidx.2.1⟩,⟨k 2,hnf⟩,⟨j,hidx.2.2⟩]
  have he : ![(i 0).val,(i 1).val,(i 2).val,k 3]=k := by
    funext l
    fin_cases l <;> rfl
  have hmem := relativePhysicalFactor_positive_closedBin ht ⟨hσ.1,hσ.2.le⟩ hband hrel
  refine ⟨i,k 3,?_,?_,?_⟩
  · have hlo : sourceRepresentative (k 0)/128≤q v := hmem.2.1.1
    change sourceRepresentative (k 0)≤128*P
    linarith only [hlo,hq]
  · simpa only [directOuterBin,he,show (i 3).val=j from rfl] using hmem.1
  · simpa only [directOuterBin,he,show (i 3).val=j from rfl] using hmem.2

lemma physicalBinFamily_cover_lintegral {ι : Type*} [Countable ι]
    {V : ℝ→Vec} (hV : Measurable V) {J : Set ℝ} (hJ : MeasurableSet J)
    (B : ι→ClosedConeBin) (R : Set ι) {g : TrianglePhase→ℝ≥0∞} (hg : Measurable g)
    (hcover : ∀p,g p≠0→∃i∈R,p∈physicalBinPhaseSet V (B i) J) :
    (∫⁻p,g p ∂trianglePhaseMeasure)≤
      ∑'i : ι,R.indicator (fun i=>
        ∫⁻z : ConeCoordinate,∫⁻v in coneBinMomentumSet (B i) z.2.2.1 (velocity (V z.1)),
          g (z,v) ∂volume ∂physicalBinMeasure V (B i) J) i := by
  classical
  let f : ι→TrianglePhase→ℝ≥0∞ := fun i=>
    if i∈R then (physicalBinPhaseSet V (B i) J).indicator g else 0
  have hm (i : ι) : Measurable (f i) := by
    dsimp only [f]
    split_ifs
    · exact hg.indicator (measurableSet_physicalBinPhaseSet hV _ hJ)
    · exact measurable_const
  calc
    _ ≤ ∫⁻p,∑'i : ι,f i p ∂trianglePhaseMeasure := by
      apply lintegral_mono
      intro p
      by_cases hp : g p=0
      · rw [hp]; exact bot_le
      · obtain ⟨i,hi,hpi⟩ := hcover p hp
        calc
          _ = f i p := by simp only [f,ite_eq_left hi,indicator_of_mem hpi]
          _ ≤ _ := ENNReal.le_tsum (f := fun index => f index p) i
    _ = ∑'i : ι,∫⁻p,f i p ∂trianglePhaseMeasure := lintegral_tsum (fun i=>(hm i).aemeasurable)
    _ = _ := by
      apply tsum_congr
      intro i
      by_cases hi : i∈R
      · simp only [f,ite_eq_left hi,indicator_of_mem hi]
        rw [lintegral_indicator (measurableSet_physicalBinPhaseSet hV _ hJ),physicalBinPhase_integral hV _ hJ hg]
      · simp only [f,ite_eq_right hi,Pi.zero_apply,lintegral_zero,indicator_of_notMem hi]

lemma directOuter_card (N : ℕ) : Fintype.card (DirectOuterIndex N)=N^4 := by
  simp [DirectOuterIndex, Fintype.card_pi]

lemma directOuter_family_sum_bound {N : ℕ} {P : ℝ}
    (f : DirectOuterIndex N→ℕ→ℝ≥0∞) (C : ℝ≥0∞)
    (hf : ∀i,sourceRepresentative (i 0).val≤128*P→(∑'nr,f i nr)≤C) :
    (∑'i : DirectOuterIndex N×ℕ,
      {i : DirectOuterIndex N×ℕ | sourceRepresentative (i.1 0).val≤128*P}.indicator
        (fun i=>f i.1 i.2) i) ≤ (N:ℝ≥0∞)^4*C := by
  classical
  rw [ENNReal.tsum_prod']
  calc
    _ ≤ ∑'i : DirectOuterIndex N,C := by
      apply ENNReal.tsum_le_tsum
      intro i
      change (∑'nr,if sourceRepresentative (i 0).val≤128*P then f i nr else 0)≤C
      by_cases hi : sourceRepresentative (i 0).val≤128*P
      · simpa only [ite_eq_left hi] using hf i hi
      · simp only [ite_eq_right hi,tsum_zero]
        exact bot_le
    _ = _ := by simp [tsum_fintype,nsmul_eq_mul]

def directTriangleDomain (T : ℝ) (J : Set ℝ) : Set TrianglePhase :=
  trianglePhaseDomain T ∩ {p | p.1.1∈J}

lemma measurableSet_directTriangleDomain (T : ℝ) {J : Set ℝ} (hJ : MeasurableSet J) :
    MeasurableSet (directTriangleDomain T J) :=
  (measurableSet_trianglePhaseDomain T).inter (hJ.preimage measurable_fst.fst)

def directTriangleDensity (s : Solution) (X : ℝ→Vec) (T : ℝ) (J : Set ℝ)
    (K : TrianglePhase→Vec) (p : TrianglePhase) : ℝ≥0∞ :=
  (directTriangleDomain T J).indicator (fun p=>
    ENNReal.ofReal ((p.1.1-p.1.2.1)^2)*
    ENNReal.ofReal ‖prefixParticle s T
      (p.1.2.1,(X p.1.1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2)) • K p‖) p

def directTransportTriangleKernel (V : ℝ→Vec) (p : TrianglePhase) : Vec :=
  forceTransportKernel (p.1.1-p.1.2.1) p.1.2.2.1 (velocity (V p.1.1)) p.2

def directSourceTriangleKernel (s : Solution) (X V : ℝ→Vec) (T : ℝ) (p : TrianglePhase) : Vec :=
  let y := X p.1.1-(p.1.1-p.1.2.1) • p.1.2.2.1
  forceSourceKernel (p.1.1-p.1.2.1) p.1.2.2.1 (velocity (V p.1.1)) p.2
    (fderiv ℝ velocity p.2 (prefixField s.E T (p.1.2.1,y)+
      cross (velocity p.2) (prefixField s.B T (p.1.2.1,y))))

lemma measurable_directTriangleDensity {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) {X : ℝ→Vec} (hX : Measurable X)
    {J : Set ℝ} (hJ : MeasurableSet J) {K : TrianglePhase→Vec} (hK : Measurable K) :
    Measurable (directTriangleDensity s X T J K) := by
  have ht : Measurable (fun p : TrianglePhase=>p.1.1) := measurable_fst.fst
  have hσ : Measurable (fun p : TrianglePhase=>p.1.2.1) := measurable_fst.snd.fst
  have hn : Measurable (fun p : TrianglePhase=>p.1.2.2.1) :=
    measurable_subtype_coe.comp measurable_fst.snd.snd
  have hy := hσ.prodMk (((hX.comp ht).sub ((ht.sub hσ).smul hn)).prodMk measurable_snd)
  have hf := (hs.continuous_prefixParticle hT).measurable.comp hy
  exact (((ht.sub hσ).pow_const 2).ennreal_ofReal.mul
    (hf.smul hK).norm.ennreal_ofReal).indicator (measurableSet_directTriangleDomain T hJ)

lemma measurable_directTransportTriangleKernel {V : ℝ→Vec} (hV : Measurable V) :
    Measurable (directTransportTriangleKernel V) := by
  exact measurable_forceTransportFamily (measurable_fst.fst.sub measurable_fst.snd.fst)
    (measurable_subtype_coe.comp measurable_fst.snd.snd)
    ((contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp measurable_fst.fst)) measurable_snd

lemma measurable_directSourceTriangleKernel {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) {X V : ℝ→Vec} (hX : Measurable X) (hV : Measurable V) :
    Measurable (directSourceTriangleKernel s X V T) := by
  have ht : Measurable (fun p : TrianglePhase=>p.1.1) := measurable_fst.fst
  have hσ : Measurable (fun p : TrianglePhase=>p.1.2.1) := measurable_fst.snd.fst
  have hn : Measurable (fun p : TrianglePhase=>p.1.2.2.1) :=
    measurable_subtype_coe.comp measurable_fst.snd.snd
  have hy := hσ.prodMk ((hX.comp ht).sub ((ht.sub hσ).smul hn))
  exact measurable_forceSourceFamily (ht.sub hσ) hn
    ((contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp ht)) measurable_snd
    (measurable_lorentz_acceleration measurable_snd
      ((continuous_prefixField hs.E_smooth.continuousOn hT).measurable.comp hy)
      ((continuous_prefixField hs.B_smooth.continuousOn hT).measurable.comp hy))

lemma directTriangleDensity_nonzero {s : Solution} {X : ℝ→Vec} {T : ℝ} {J : Set ℝ}
    {K : TrianglePhase→Vec} {p : TrianglePhase} (hp : directTriangleDensity s X T J K p≠0) :
    p∈directTriangleDomain T J ∧
      s.f (p.1.2.1,(X p.1.1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2))≠0 := by
  have hmem : p∈directTriangleDomain T J := by
    by_contra hc
    exact hp (indicator_of_notMem hc _)
  refine ⟨hmem,?_⟩
  intro hz
  apply hp
  have hσ : p.1.2.1∈Icc 0 T := ⟨hmem.1.2.1.le,hmem.1.2.2.le.trans hmem.1.1.2.le⟩
  simp only [directTriangleDensity,indicator_of_mem hmem,prefixParticle,prefixClamp_eq hσ,
    hz,zero_smul,norm_zero,ENNReal.ofReal_zero,mul_zero]

lemma directTransportTriangle_bin_bound {s : Solution} {X V : ℝ→Vec} {T : ℝ}
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (B : ClosedConeBin) {z : ConeCoordinate}
    (hz : z∈physicalBinBase V B J) :
    (∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      directTriangleDensity s X T J (directTransportTriangleKernel V) (z,v))≤
      physicalDirectTransportDensity s X V B z := by
  unfold physicalDirectTransportDensity
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro v
  by_cases hp : (z,v)∈directTriangleDomain T J
  · have hσ : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩
    simp only [directTriangleDensity,indicator_of_mem hp,directTransportTriangleKernel,
      prefixParticle,prefixClamp_eq hσ]
    exact le_rfl
  · simp only [directTriangleDensity,indicator_of_notMem hp]
    exact bot_le

lemma directSourceTriangle_bin_bound {s : Solution} {X V : ℝ→Vec} {T : ℝ}
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (B : ClosedConeBin) {z : ConeCoordinate}
    (hz : z∈physicalBinBase V B J) :
    (∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      directTriangleDensity s X T J (directSourceTriangleKernel s X V T) (z,v))≤
      physicalDirectSourceDensity s X V B z := by
  unfold physicalDirectSourceDensity
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro v
  by_cases hp : (z,v)∈directTriangleDomain T J
  · have hσ : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩
    simp only [directTriangleDensity,indicator_of_mem hp,directSourceTriangleKernel,
      prefixParticle,prefixField,prefixClamp_eq hσ]
    exact le_rfl
  · simp only [directTriangleDensity,indicator_of_notMem hp]
    exact bot_le

lemma PhaseFlowOn.directTriangleDensity_finite_cover {s : Solution} {T P w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (hP : 0≤P) (hwP : w≤P) (N : ℕ) (hN : 8192*P≤(2:ℝ)^N)
    (hbound : ∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P)
    (X V : ℝ→Vec) {J : Set ℝ} (hband : ∀t∈J,q (V t)∈Icc (w/8) (8*w))
    (K : TrianglePhase→Vec) (p : TrianglePhase)
    (hp : directTriangleDensity s X T J K p≠0) :
    ∃i : DirectOuterIndex N×ℕ,
      i∈{i : DirectOuterIndex N×ℕ | sourceRepresentative (i.1 0).val≤128*P} ∧
      p∈physicalBinPhaseSet V (directOuterBin T w i.1 i.2) J := by
  have hh := directTriangleDensity_nonzero hp
  have hσ : p.1.2.1∈Icc 0 T := ⟨hh.1.1.2.1.le,hh.1.1.2.2.le.trans hh.1.1.1.2.le⟩
  have hq := F.eulerian_supported_momentum hs hbound hσ _ p.2 hh.2
  obtain ⟨i,nr,hcap,hbase,hv⟩ := physical_direct_finite_cover hP hwP hN hh.1.2
    hh.1.1.1.2.le ⟨hh.1.1.2.1.le,hh.1.1.2.2⟩ (hband _ hh.1.2) p.1.2.2 p.2 hq
  exact ⟨(i,nr),hcap,hbase,hv⟩

lemma PhaseFlowOn.directTriangle_family_estimate {s : Solution} {T P w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (hP : 0≤P) (hwP : w≤P) (N : ℕ) (hN : 8192*P≤(2:ℝ)^N)
    (hbound : ∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P)
    (X V : ℝ→Vec) (hX : Measurable X) (hV : Measurable V)
    (J : Set ℝ) (hJ : MeasurableSet J) (hband : ∀t∈J,q (V t)∈Icc (w/8) (8*w))
    (K : TrianglePhase→Vec) (hK : Measurable K) (f : ClosedConeBin → ConeCoordinate → ℝ≥0∞)
    (C : ℝ≥0∞)
    (hbin : ∀B z,z∈physicalBinBase V B J→
      (∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
        directTriangleDensity s X T J K (z,v))≤f B z)
    (hfamily : ∀i : DirectOuterIndex N,sourceRepresentative (i 0).val≤128*P→
      (∑'nr,∫⁻z,f (directOuterBin T w i nr) z ∂physicalBinMeasure V (directOuterBin T w i nr) J)≤C) :
    (∫⁻p,directTriangleDensity s X T J K p ∂trianglePhaseMeasure)≤(N:ℝ≥0∞)^4*C := by
  let R := {i : DirectOuterIndex N×ℕ | sourceRepresentative (i.1 0).val≤128*P}
  have hc := physicalBinFamily_cover_lintegral hV hJ
    (fun i : DirectOuterIndex N×ℕ=>directOuterBin T w i.1 i.2) R
    (measurable_directTriangleDensity hs hT hX hJ hK)
    (F.directTriangleDensity_finite_cover hs hP hwP N hN hbound X V hband K)
  apply hc.trans
  apply (ENNReal.tsum_le_tsum (fun i=>?_)).trans
  · exact directOuter_family_sum_bound
      (fun i nr=>∫⁻z,f (directOuterBin T w i nr) z ∂physicalBinMeasure V (directOuterBin T w i nr) J) C hfamily
  · apply indicator_le_indicator
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV _ hJ)] with z hz
    exact hbin _ z hz

lemma Admissible.direct_transport_physical_bound {d : Datum} (hd₀ : Admissible d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (a b w P : ℝ) (N : ℕ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ (w/P)^2 → 1≤w → 0<P → w≤P →
      8192*P≤(2:ℝ)^N →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      (∫⁻p,directTriangleDensity s X T (Icc a b) (directTransportTriangleKernel V) p
        ∂trianglePhaseMeasure) ≤ (N:ℝ≥0∞)^4*ENNReal.ofReal (C*max 1 T*w^2) := by
  obtain ⟨C,hC,hbound⟩ := hd₀.direct_transport_all_radii
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX S a b w P N hS hS0 ha hb hJI hw hP hwP hN hPbound hW
  dsimp only
  have hα : Continuous (fun t : ℝ => prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hJT : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hband : ∀t∈Icc a b,q (prefixFlow F.flow T zX t).2∈Icc (w/8) (8*w) := by
    intro t ht
    simpa only [prefixFlow,prefixClamp_eq (hJT ht)] using hW t ht
  apply F.directTriangle_family_estimate hs hT hP.le hwP N hN hPbound
    (fun t => (prefixFlow F.flow T zX t).1) (fun t => (prefixFlow F.flow T zX t).2)
    hα.fst.measurable hα.snd.measurable (Icc a b) measurableSet_Icc hband
    (directTransportTriangleKernel (fun t => (prefixFlow F.flow T zX t).2))
    (measurable_directTransportTriangleKernel hα.snd.measurable)
    (physicalDirectTransportDensity s (fun t => (prefixFlow F.flow T zX t).1)
      (fun t => (prefixFlow F.flow T zX t).2)) (ENNReal.ofReal (C*max 1 T*w^2))
    (fun B z hz=>directTransportTriangle_bin_bound (s:=s)
      (X:=fun t=>(prefixFlow F.flow T zX t).1) (V:=fun t=>(prefixFlow F.flow T zX t).2)
      (T:=T) hJT B hz)
  intro i hi
  exact hbound s T F hs hT h0 zX S (i 0).val (i 1).val (i 2).val (i 3).val a b ((w/P)^2) w P
    hS hS0 ha hb hJI (sq_pos_of_pos (div_pos (zero_lt_one.trans_le hw) hP)) hw hP hwP le_rfl hi

lemma Admissible.direct_source_physical_bound {d : Datum} (hd₀ : Admissible d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (a b w M A P : ℝ) (N : ℕ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a≤b → b-a ≤ (w/P)^2 →
      0<M → 0≤A → 1≤P → 1≤Real.log (2+P) → 1≤w → w≤P →
      8192*P≤(2:ℝ)^N →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∫⁻p,directTriangleDensity s X T (Icc a b) (directSourceTriangleKernel s X V T) p
        ∂trianglePhaseMeasure) ≤
      (N:ℝ≥0∞)^4*ENNReal.ofReal (C*(1+E)*(1+M+Real.sqrt A)*w*Real.sqrt w*Real.log (2+P)) := by
  obtain ⟨C,hC,hbound⟩ := hd₀.direct_source_all_radii
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX S a b w M A P N hS hS0 ha hb hab hJI hM hA hP hL hw hwP hN hPbound hW HX HZ
  dsimp only
  have hα : Continuous (fun t : ℝ => prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hJT : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hband : ∀t∈Icc a b,q (prefixFlow F.flow T zX t).2∈Icc (w/8) (8*w) := by
    intro t ht
    simpa only [prefixFlow,prefixClamp_eq (hJT ht)] using hW t ht
  apply F.directTriangle_family_estimate hs hT (zero_le_one.trans hP) hwP N hN hPbound
    (fun t => (prefixFlow F.flow T zX t).1) (fun t => (prefixFlow F.flow T zX t).2)
    hα.fst.measurable hα.snd.measurable (Icc a b) measurableSet_Icc hband
    (directSourceTriangleKernel s (fun t => (prefixFlow F.flow T zX t).1)
      (fun t => (prefixFlow F.flow T zX t).2) T)
    (measurable_directSourceTriangleKernel hs hT hα.fst.measurable hα.snd.measurable)
    (physicalDirectSourceDensity s (fun t => (prefixFlow F.flow T zX t).1)
      (fun t => (prefixFlow F.flow T zX t).2))
    (ENNReal.ofReal (C*(1+∫x : Vec,totalEnergy s (0,x))*(1+M+Real.sqrt A)*w*Real.sqrt w*Real.log (2+P)))
    (fun B z hz=>directSourceTriangle_bin_bound (s:=s)
      (X:=fun t=>(prefixFlow F.flow T zX t).1) (V:=fun t=>(prefixFlow F.flow T zX t).2)
      (T:=T) hJT B hz)
  intro i hi
  exact hbound s T F hs hT h0 zX S (i 0).val (i 1).val (i 2).val (i 3).val a b w M A P
    hS hS0 ha hb hab hJI hM hA hP hL hw hwP hi HX HZ

lemma exists_direct_dyadic_count : ∃C : ℝ,0≤C ∧ ∀P : ℝ,
    1≤P → 1≤Real.log (2+P) → ∃N : ℕ,8192*P≤(2:ℝ)^N ∧ (N:ℝ)≤C*Real.log (2+P) := by
  obtain ⟨C,hC,hcount⟩ := exists_far_dyadic_count 0
  refine ⟨C,hC,?_⟩
  intro P hP hL
  obtain ⟨N,_,_,hN,hNc⟩ := hcount P (zero_lt_one.trans_le hP) hL
  refine ⟨N,?_,hNc⟩
  norm_num at hN
  have hh : P≤P^2 := by nlinarith only [hP,sq_nonneg (P-1)]
  nlinarith only [hN,hP,hh]

lemma ennreal_count_four_bound {N : ℕ} {C L : ℝ} (hC : 0≤C) (hL : 0≤L)
    (hN : (N:ℝ)≤C*L) (B : ℝ) :
    (N:ℝ≥0∞)^4*ENNReal.ofReal B ≤ ENNReal.ofReal (C^4*L^4*B) := by
  have hNc : (N:ℝ≥0∞)≤ENNReal.ofReal (C*L) := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hN
  calc
    _ ≤ (ENNReal.ofReal (C*L))^4*ENNReal.ofReal B := mul_le_mul' (pow_le_pow_left' hNc 4) le_rfl
    _ = _ := by
      rw [←ENNReal.ofReal_pow (mul_nonneg hC hL),←ENNReal.ofReal_mul (pow_nonneg (mul_nonneg hC hL) 4)]
      congr 1
      ring

lemma Admissible.direct_transport_physical_log_bound {d : Datum} (hd₀ : Admissible d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (a b w P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ (w/P)^2 → 1≤w → 1≤P → w≤P → 1≤Real.log (2+P) →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      (∫⁻p,directTriangleDensity s X T (Icc a b) (directTransportTriangleKernel V) p
        ∂trianglePhaseMeasure) ≤ ENNReal.ofReal (C*max 1 T*w^2*(Real.log (2+P))^4) := by
  obtain ⟨C,hC,hbound⟩ := hd₀.direct_transport_physical_bound
  obtain ⟨Cn,hCn,hcount⟩ := exists_direct_dyadic_count
  refine ⟨C*Cn^4,by positivity,?_⟩
  intro s T F hs hT h0 zX S a b w P hS hS0 ha hb hJI hw hP hwP hL hPbound hW
  dsimp only
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  apply (hbound s T F hs hT h0 zX S a b w P N hS hS0 ha hb hJI hw
    (zero_lt_one.trans_le hP) hwP hN hPbound hW).trans
  convert ennreal_count_four_bound hCn (zero_le_one.trans hL) hNc (C*max 1 T*w^2) using 1
  congr 1
  ring

lemma Admissible.direct_source_physical_log_bound {d : Datum} (hd₀ : Admissible d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a≤b → b-a ≤ (w/P)^2 →
      0<M → 0≤A → 1≤P → 1≤Real.log (2+P) → 1≤w → w≤P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∫⁻p,directTriangleDensity s X T (Icc a b) (directSourceTriangleKernel s X V T) p
        ∂trianglePhaseMeasure) ≤
      ENNReal.ofReal (C*(1+E)*(1+M+Real.sqrt A)*w*Real.sqrt w*(Real.log (2+P))^5) := by
  obtain ⟨C,hC,hbound⟩ := hd₀.direct_source_physical_bound
  obtain ⟨Cn,hCn,hcount⟩ := exists_direct_dyadic_count
  refine ⟨C*Cn^4,by positivity,?_⟩
  intro s T F hs hT h0 zX S a b w M A P hS hS0 ha hb hab hJI hM hA hP hL hw hwP hPbound hW HX HZ
  dsimp only
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  apply (hbound s T F hs hT h0 zX S a b w M A P N hS hS0 ha hb hab hJI hM hA hP hL hw hwP
    hN hPbound hW HX HZ).trans
  convert ennreal_count_four_bound hCn (zero_le_one.trans hL) hNc
    (C*(1+∫x : Vec,totalEnergy s (0,x))*(1+M+Real.sqrt A)*w*Real.sqrt w*Real.log (2+P)) using 1
  congr 1
  ring

lemma directTriangle_lintegral_polar {T : ℝ} {J : Set ℝ}
    (hJ : MeasurableSet J) {g : TrianglePhase → ℝ≥0∞} (hg : Measurable g)
    (hsupp : ∀p,p∉directTriangleDomain T J → g p=0) :
    (∫⁻p,g p ∂trianglePhaseMeasure)=
      ∫⁻t in Ioo (0:ℝ) T∩J,∫⁻n : Sphere,∫⁻σ in Ioo (0:ℝ) t,∫⁻v : Vec,
        g ((t,σ,n),v) ∂volume ∂volume ∂sphereMeasure := by
  have hm : Measurable (fun z : ConeCoordinate=>∫⁻v : Vec,g (z,v)) := hg.lintegral_prod_right'
  have he : (∫⁻p,g p ∂trianglePhaseMeasure)=
      ∫⁻t : ℝ,∫⁻σ : ℝ,∫⁻n : Sphere,∫⁻v : Vec,g ((t,σ,n),v) ∂volume ∂sphereMeasure := by
    rw [trianglePhaseMeasure,lintegral_prod _ hg.aemeasurable,lintegral_prod _ hm.aemeasurable]
    apply lintegral_congr
    intro t
    exact lintegral_prod _ (hm.comp (measurable_const.prodMk measurable_id)).aemeasurable
  rw [he,←lintegral_indicator (measurableSet_Ioo.inter hJ)]
  apply lintegral_congr
  intro t
  by_cases ht : t∈Ioo 0 T∩J
  · rw [indicator_of_mem ht]
    have hh : (∫⁻σ : ℝ,∫⁻n : Sphere,∫⁻v : Vec,g ((t,σ,n),v) ∂volume ∂sphereMeasure)=
        ∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,∫⁻v : Vec,g ((t,σ,n),v) ∂volume ∂sphereMeasure := by
      rw [←lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro σ
      by_cases hσ : σ∈Ioo 0 t
      · rw [indicator_of_mem hσ]
      · rw [indicator_of_notMem hσ]
        have hz (n : Sphere) (v : Vec) : g ((t,σ,n),v)=0 :=
          hsupp _ (fun hp=>hσ hp.1.2)
        simp only [hz,lintegral_zero]
    rw [hh]
    exact lintegral_lintegral_swap
      ((hm.comp (measurable_const.prodMk measurable_id)).aemeasurable)
  · rw [indicator_of_notMem ht]
    have hz (σ : ℝ) (n : Sphere) (v : Vec) : g ((t,σ,n),v)=0 :=
      hsupp _ (fun hp=>ht ⟨hp.1.1,hp.2⟩)
    simp only [hz,lintegral_zero]

lemma directTriangleDensity_outside (s : Solution) (X : ℝ→Vec) (T : ℝ)
    (J : Set ℝ) (K : TrianglePhase→Vec) (p : TrianglePhase)
    (hp : p∉directTriangleDomain T J) : directTriangleDensity s X T J K p=0 :=
  indicator_of_notMem hp _

lemma normalised_direct_kernel_identity (s : Solution) (X V : ℝ→Vec) {T t σ : ℝ}
    (ht : t≤T) (hσ : σ∈Ioo 0 t) (n : Sphere) (v : Vec) :
    (1-dot n.1 (velocity (V t))) •
      (s.f (σ,(X t-(t-σ) • n.1,v)) •
        normalisedSignedForce (t-σ) (velocity (V t)) (velocity v) n.1
          (sourceAcceleration s (σ,(X t-(t-σ) • n.1,v))))=
      (t-σ)^2 • (prefixParticle s T (σ,(X t-(t-σ) • n.1,v)) •
        (directTransportTriangleKernel V ((t,σ,n),v)+
          directSourceTriangleKernel s X V T ((t,σ,n),v))) := by
  have hσT : σ∈Icc 0 T := ⟨hσ.1.le,hσ.2.le.trans ht⟩
  rw [smul_comm,normalisedSignedForce_flux n.1 (velocity (V t)) v _
    (sub_pos.mpr hσ.2).ne' (sphere_norm n) (cone_denom_pos (V t) n.1 (sphere_norm n)).ne',smul_comm]
  simp only [directTransportTriangleKernel,directSourceTriangleKernel,prefixParticle,prefixField,
    prefixClamp_eq hσT,sourceAcceleration]

lemma normalised_direct_density_bound (s : Solution) (X V : ℝ→Vec) {T t σ : ℝ}
    {J : Set ℝ} (ht : t∈Ioo 0 T∩J) (hσ : σ∈Ioo 0 t) (n : Sphere) (v : Vec) :
    ENNReal.ofReal ‖(1-dot n.1 (velocity (V t))) •
      (s.f (σ,(X t-(t-σ) • n.1,v)) •
        normalisedSignedForce (t-σ) (velocity (V t)) (velocity v) n.1
          (sourceAcceleration s (σ,(X t-(t-σ) • n.1,v))))‖≤
      directTriangleDensity s X T J (directTransportTriangleKernel V) ((t,σ,n),v)+
      directTriangleDensity s X T J (directSourceTriangleKernel s X V T) ((t,σ,n),v) := by
  rw [normalised_direct_kernel_identity s X V ht.1.2.le hσ n v]
  have hp : ((t,σ,n),v)∈directTriangleDomain T J := ⟨⟨ht.1,hσ⟩,ht.2⟩
  simp only [directTriangleDensity,indicator_of_mem hp]
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (t-σ)),
    ENNReal.ofReal_mul (sq_nonneg _),smul_add,←mul_add,
    ←ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (norm_add_le _ _))

lemma norm_integral_ENN_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (g : Ω → Vec) :
    ENNReal.ofReal ‖∫p,g p ∂μ‖ ≤ ∫⁻p,ENNReal.ofReal ‖g p‖ ∂μ := by
  simpa only [ofReal_norm] using enorm_integral_le_lintegral_enorm g

lemma SmoothClassicalPrefix.direct_force_fiber_bound {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) (X V : ℝ→Vec) {J : Set ℝ} {t : ℝ}
    (ht : t∈Ioo 0 T∩J) :
    ENNReal.ofReal ‖s.E (t,X t)+cross (velocity (V t)) (s.B (t,X t))-
      boundaryLorentzForce (datumBoundarySolution d) t (X t) (velocity (V t))‖≤
      ENNReal.ofReal (4*Real.pi)⁻¹ *
        (∫⁻n : Sphere,∫⁻σ in Ioo (0:ℝ) t,∫⁻v : Vec,
          (directTriangleDensity s X T J (directTransportTriangleKernel V) ((t,σ,n),v)+
           directTriangleDensity s X T J (directSourceTriangleKernel s X V T) ((t,σ,n),v))
          ∂volume ∂volume ∂sphereMeasure) := by
  rw [hs.retarded_force_source_polar ht.1.1 ht.1.2 (X t) (velocity (V t))
    (norm_velocity_lt_one _),add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
    abs_of_pos (by positivity : 0<(4*Real.pi)⁻¹),ENNReal.ofReal_mul (by positivity : 0≤(4*Real.pi)⁻¹)]
  apply mul_le_mul' le_rfl
  apply (norm_integral_ENN_bound _).trans
  apply lintegral_mono
  intro n
  apply (norm_integral_ENN_bound _).trans
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with σ hσ
  rw [←integral_smul]
  apply (norm_integral_ENN_bound _).trans
  exact lintegral_mono (normalised_direct_density_bound s X V ht hσ n)

lemma restrict_inside_finite_prefix {T : ℝ} {J : Set ℝ} (hJT : J⊆Icc 0 T) :
    (volume : Measure ℝ).restrict J=volume.restrict (Ioo 0 T∩J) := by
  apply Measure.restrict_congr_set
  filter_upwards [Ioo_ae_eq_Icc (μ:=(volume : Measure ℝ)) (a:=0) (b:=T)] with t ht
  apply propext
  constructor
  · intro hj
    exact ⟨ht.mpr (hJT hj),hj⟩
  · exact fun h=>h.2

private lemma SmoothClassicalPrefix.directForceEnergyPrefix
    {datum : Datum} {solution : Solution} {horizon : ℝ}
    (hs : SmoothClassicalPrefix datum solution horizon) : EnergyPrefix solution horizon := by
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

lemma SmoothClassicalPrefix.direct_force_triangle_bound {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hT : 0≤T) (X V : ℝ→Vec)
    (hX : Measurable X) (hV : Measurable V) {J : Set ℝ} (hJ : MeasurableSet J)
    (hJT : J⊆Icc 0 T) :
    (∫⁻t in J,ENNReal.ofReal ‖s.E (t,X t)+cross (velocity (V t)) (s.B (t,X t))-
      boundaryLorentzForce (datumBoundarySolution d) t (X t) (velocity (V t))‖)≤
      ENNReal.ofReal (4*Real.pi)⁻¹ *
        ((∫⁻p,directTriangleDensity s X T J (directTransportTriangleKernel V) p ∂trianglePhaseMeasure)+
         (∫⁻p,directTriangleDensity s X T J (directSourceTriangleKernel s X V T) p ∂trianglePhaseMeasure)) := by
  let g₁ := directTriangleDensity s X T J (directTransportTriangleKernel V)
  let g₂ := directTriangleDensity s X T J (directSourceTriangleKernel s X V T)
  have hm₁ : Measurable g₁ := measurable_directTriangleDensity hs.directForceEnergyPrefix hT hX hJ
    (measurable_directTransportTriangleKernel hV)
  have hm₂ : Measurable g₂ := measurable_directTriangleDensity hs.directForceEnergyPrefix hT hX hJ
    (measurable_directSourceTriangleKernel hs.directForceEnergyPrefix hT hX hV)
  have hsum : (∫⁻p,g₁ p+g₂ p ∂trianglePhaseMeasure)=
      (∫⁻p,g₁ p ∂trianglePhaseMeasure)+(∫⁻p,g₂ p ∂trianglePhaseMeasure) :=
    lintegral_add_left hm₁ _
  change _≤ENNReal.ofReal (4*Real.pi)⁻¹ *
    ((∫⁻p,g₁ p ∂trianglePhaseMeasure)+(∫⁻p,g₂ p ∂trianglePhaseMeasure))
  rw [←hsum,directTriangle_lintegral_polar (g:=fun p=>g₁ p+g₂ p) hJ (hm₁.add hm₂)
    (fun p hp=>by dsimp only [g₁,g₂]; rw [directTriangleDensity_outside s X T J _ p hp,
      directTriangleDensity_outside s X T J _ p hp]; exact add_zero 0)]
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,restrict_inside_finite_prefix hJT]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.inter hJ)] with t ht
  exact hs.direct_force_fiber_bound X V ht

lemma SmoothClassicalPrefix.direct_lorentz_triangle_bound {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hT : 0≤T) (X V : ℝ→Vec)
    (hX : Measurable X) (hV : Measurable V) {J : Set ℝ} (hJ : MeasurableSet J)
    (hJT : J⊆Icc 0 T) (C : ℝ) (hC : 0≤C)
    (hdatum : ∀t∈Ioo 0 T∩J,‖boundaryLorentzForce (datumBoundarySolution d) t (X t) (velocity (V t))‖≤C) :
    (∫⁻t in J,ENNReal.ofReal ‖s.E (t,X t)+cross (velocity (V t)) (s.B (t,X t))‖)≤
      ENNReal.ofReal C*volume J + ENNReal.ofReal (4*Real.pi)⁻¹ *
        ((∫⁻p,directTriangleDensity s X T J (directTransportTriangleKernel V) p ∂trianglePhaseMeasure)+
         (∫⁻p,directTriangleDensity s X T J (directSourceTriangleKernel s X V T) p ∂trianglePhaseMeasure)) := by
  have hpt : ∀ᵐt∂volume.restrict J,
      ENNReal.ofReal ‖s.E (t,X t)+cross (velocity (V t)) (s.B (t,X t))‖≤
        ENNReal.ofReal C+ENNReal.ofReal ‖s.E (t,X t)+cross (velocity (V t)) (s.B (t,X t))-
          boundaryLorentzForce (datumBoundarySolution d) t (X t) (velocity (V t))‖ := by
    rw [restrict_inside_finite_prefix hJT]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.inter hJ)] with t ht
    rw [←ENNReal.ofReal_add hC (norm_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _=‖boundaryLorentzForce (datumBoundarySolution d) t (X t) (velocity (V t))+
        (s.E (t,X t)+cross (velocity (V t)) (s.B (t,X t))-
          boundaryLorentzForce (datumBoundarySolution d) t (X t) (velocity (V t)))‖ := by
          congr 1; abel
      _≤_ := (norm_add_le _ _).trans (add_le_add (hdatum t ht) le_rfl)
  apply (lintegral_mono_ae hpt).trans
  rw [lintegral_add_left measurable_const,lintegral_const,Measure.restrict_apply_univ]
  exact add_le_add le_rfl (hs.direct_force_triangle_bound hT X V hX hV hJ hJT)

lemma Admissible.direct_lorentz_log_bound {d : Datum} (hd₀ : Admissible d)
    (T : ℝ) (hT : 0≤T) :
    ∃ Cb Ct Cs : ℝ,0≤Cb ∧ 0≤Ct ∧ 0≤Cs ∧
    ∀ (s : Solution) (F : PhaseFlowOn s.E s.B T), SmoothClassicalPrefix d s T →
    ∀ (zX : Phase) (S : Set Phase) (a b w M A P : ℝ),
      zX∈tsupport d.f₀ → IsCompact S → tsupport d.f₀⊆S →
      0≤a → b≤T → a≤b → b-a≤(w/P)^2 →
      0<M → 0≤A → 1≤P → 1≤Real.log (2+P) → 1≤w → w≤P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∫⁻t in Icc a b,ENNReal.ofReal ‖s.E (t,(F.flow zX t).1)+
          cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))‖) ≤
      ENNReal.ofReal (Cb*(b-a)) + ENNReal.ofReal (4*Real.pi)⁻¹ *
       (ENNReal.ofReal (Ct*max 1 T*w^2*(Real.log (2+P))^4) +
        ENNReal.ofReal (Cs*(1+E)*(1+M+Real.sqrt A)*w*Real.sqrt w*(Real.log (2+P))^5)) := by
  obtain ⟨Cb,hCb,hdatum⟩ := hd₀.supported_boundary_force_bound T hT
  obtain ⟨Ct,hCt,htrans⟩ := hd₀.direct_transport_physical_log_bound
  obtain ⟨Cs,hCs,hsource⟩ := hd₀.direct_source_physical_log_bound
  refine ⟨Cb,Ct,Cs,hCb,hCt,hCs,?_⟩
  intro s F hs zX S a b w M A P hzX hS hS0 ha hb hab hJI hM hA hP hL hw hwP hPbound hW HX HZ
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  have hcon := (F.continuous_prefixFlow hs.directForceEnergyPrefix hT).comp
    (continuous_id.prodMk continuous_const : Continuous (fun t : ℝ=>(t,zX)))
  have hX : Measurable X := hcon.fst.measurable
  have hV : Measurable V := hcon.snd.measurable
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hdata : (fun z=>s.f (0,z))=d.f₀ := funext hs.initial_f
  have hS0' : tsupport (fun z=>s.f (0,z))⊆S := by rw [hdata]; exact hS0
  have hDb : ∀t∈Ioo 0 T∩Icc a b,
      ‖boundaryLorentzForce (datumBoundarySolution d) t (X t) (velocity (V t))‖≤Cb := by
    intro t ht
    dsimp only [X,V,prefixFlow]
    rw [prefixClamp_eq (hJ ht.2)]
    exact hdatum s.E s.B F zX hzX t ⟨ht.1.1,ht.1.2.le⟩
  have hraw : (∫⁻t in Icc a b,ENNReal.ofReal ‖s.E (t,(F.flow zX t).1)+
      cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))‖)=
      ∫⁻t in Icc a b,ENNReal.ofReal ‖s.E (t,X t)+cross (velocity (V t)) (s.B (t,X t))‖ := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp only [X,V,prefixFlow,prefixClamp_eq (hJ ht)]
  rw [hraw]
  apply (hs.direct_lorentz_triangle_bound hT X V hX hV measurableSet_Icc hJ Cb hCb hDb).trans
  have hD : ENNReal.ofReal Cb*volume (Icc a b)=ENNReal.ofReal (Cb*(b-a)) := by
    rw [Real.volume_Icc,ENNReal.ofReal_mul hCb]
  rw [hD]
  apply add_le_add le_rfl
  apply mul_le_mul' le_rfl
  exact add_le_add
    (htrans s T F hs.directForceEnergyPrefix hT hs.initial_f zX S a b w P hS hS0' ha hb hJI hw hP hwP hL hPbound hW)
    (hsource s T F hs.directForceEnergyPrefix hT hs.initial_f zX S a b w M A P hS hS0' ha hb hab hJI hM hA hP hL hw hwP
      hPbound hW HX HZ)

end RVM

end

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

def directOuterIndexEquiv (N : ℕ) : DirectOuterIndex N ≃ Fin N×Fin N×Fin N×Fin N where
  toFun k := (k 0,k 2,k 1,k 3)
  invFun k := ![k.1,k.2.2.1,k.2.1,k.2.2.2]
  left_inv k := by funext i; fin_cases i <;> rfl
  right_inv k := by rcases k with ⟨a,b,c,d⟩; rfl

lemma directOuter_remaining_sum {N : ℕ} (P : ℝ) (f : ℕ→ℕ→ℕ→ℕ→ℕ→ℝ≥0∞) :
    (∑'i : DirectOuterIndex N×ℕ,
      ({i : DirectOuterIndex N×ℕ | sourceRepresentative (i.1 0).val≤128*P ∧
        cappedRepresentative (i.1 2).val≤16384*cappedRepresentative (i.1 1).val}).indicator
        (fun i=>f (i.1 0).val (i.1 2).val (i.1 1).val (i.1 3).val i.2) i)=
      ∑np∈(Finset.range N).filter (fun np=>sourceRepresentative np≤128*P),
        ∑nf∈Finset.range N,∑nt∈(Finset.range N).filter
          (fun nt=>cappedRepresentative nf≤16384*cappedRepresentative nt),
          ∑j∈Finset.range N,∑'nr : ℕ,f np nf nt j nr := by
  rw [ENNReal.tsum_prod',←(directOuterIndexEquiv N).symm.tsum_eq]
  simp only [ENNReal.tsum_prod',directOuterIndexEquiv,Equiv.coe_fn_symm_mk]
  simp only [Set.indicator_apply,mem_ofPred_eq]
  change (∑'np : Fin N,∑'nf : Fin N,∑'nt : Fin N,∑'j : Fin N,∑'nr : ℕ,
    if sourceRepresentative np.val≤128*P ∧ cappedRepresentative nf.val≤16384*cappedRepresentative nt.val
      then f np.val nf.val nt.val j.val nr else 0)=_
  simp only [tsum_fintype,Finset.sum_filter]
  simp_rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro np hnp
  by_cases hp : sourceRepresentative np.val≤128*P
  · simp only [hp,true_and,ite_true]
    apply Finset.sum_congr rfl
    intro nf hnf
    apply Finset.sum_congr rfl
    intro nt hnt
    by_cases ht : cappedRepresentative nf.val≤16384*cappedRepresentative nt.val
    · simp only [ht,ite_true]
    · simp only [ht,ite_false,tsum_zero,Finset.sum_const_zero]
  · simp only [hp,false_and,ite_false,tsum_zero,Finset.sum_const_zero]

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma ennreal_filter_sum_le_tsum (S : Finset ℕ) (p : ℕ→Prop) (f : ℕ→ℝ≥0∞) :
    (∑n∈S.filter p,f n)≤∑'n : ℕ,if p n then f n else 0 := by
  rw [Finset.sum_filter]
  exact ENNReal.sum_le_tsum _

lemma directOuter_remaining_le_tsum {N : ℕ} (P : ℝ) (f : ℕ→ℕ→ℕ→ℕ→ℕ→ℝ≥0∞) :
    (∑'i : DirectOuterIndex N×ℕ,
      ({i : DirectOuterIndex N×ℕ | sourceRepresentative (i.1 0).val≤128*P ∧
        cappedRepresentative (i.1 2).val≤16384*cappedRepresentative (i.1 1).val}).indicator
        (fun i=>f (i.1 0).val (i.1 2).val (i.1 1).val (i.1 3).val i.2) i)≤
      ∑'np : ℕ,if sourceRepresentative np≤128*P then
        ∑'nt : ℕ,∑'nf : ℕ,if cappedRepresentative nf≤16384*cappedRepresentative nt then
          ∑'j : ℕ,∑'nr : ℕ,f np nf nt j nr else 0 else 0 := by
  rw [directOuter_remaining_sum]
  apply le_trans (ennreal_filter_sum_le_tsum (Finset.range N) (fun np=>sourceRepresentative np≤128*P) _)
  apply ENNReal.tsum_le_tsum
  intro np
  split_ifs with hp
  · rw [ENNReal.tsum_comm]
    apply le_trans (ENNReal.sum_le_tsum _)
    apply ENNReal.tsum_le_tsum
    intro nf
    apply le_trans (ennreal_filter_sum_le_tsum (Finset.range N) (fun nt=>cappedRepresentative nf≤16384*cappedRepresentative nt) _)
    apply ENNReal.tsum_le_tsum
    intro nt
    split_ifs with ht
    · exact ENNReal.sum_le_tsum _
    · rfl
  · rfl

end RVM

end

end OAI
