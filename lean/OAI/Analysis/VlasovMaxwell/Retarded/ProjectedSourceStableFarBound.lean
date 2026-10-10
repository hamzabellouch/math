import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.QuadIndexEquiv
import OAI.Analysis.VlasovMaxwell.Geometry.IndexTwoPow

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

lemma Admissible.projected_source_stable_far_bound {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ, 0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (k : Fin 4→ℕ)
        (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ (w/P)^2 →
      0 < M → 0 ≤ A → 0 < P → 1 ≤ Real.log (2+P) → 1 ≤ w → w ≤ P →
      sourceRepresentative (k 0) ≤ 128*P →
      cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 →
      32 ≤ cappedRepresentative (k 2)*w →
      1/32 ≤ sourceRepresentative (k 0)*cappedRepresentative (k 1)*
        Real.sqrt (max 1 T*cappedRepresentative (k 3)) →
      (∀t∈Icc a b,w/16 ≤ ‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := representativeClosedBin T w k
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s X V B T w Q z
        ∂physicalBinMeasure V B (Icc a b)) ≤
      ENNReal.ofReal (C*E*(1+16384*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P))) := by
  obtain ⟨C,hC,hbound⟩ := hd₀.projected_source_baseline_radius_bound
  refine ⟨8196*C,by positivity,?_⟩
  intro s T F hs hT h0 zX S Q k a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP
    hpP hsmall hwφ hfar hband HX HZ
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let r := max 1 T*cappedRepresentative (k 3)
  let L := Real.log (2+P)
  let I := (w/P)^2
  let lam := stabilityLength P 16384 M A p w φ
  let len := min I (lam/2)
  let m := min p w/128
  let E := ∫x : Vec,totalEnergy s (0,x)
  have hp1 : 1 ≤ p := by
    have hh : (1:ℝ) ≤ 2^(k 0) := one_le_pow₀ (by norm_num)
    dsimp [p,sourceRepresentative]
    linarith only [hh]
  have hp : 0 < p := zero_lt_one.trans_le hp1
  have hw0 : 0 < w := zero_lt_one.trans_le hw
  have hθ : 0 < θ := cappedRepresentative_pos _
  have hφ : 0 < φ := cappedRepresentative_pos _
  have hr : 0 < r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hθφ : θ ≤ φ := by change θ≤φ/16 at hsmall; linarith only [hsmall,hφ]
  have hI : 0 < I := sq_pos_of_pos (div_pos hw0 hP)
  have hlam : 0 < lam := stabilityLength_pos hP (by norm_num) hM hp hw0 hφ
  have hlen : 0 < len := lt_min hI (by positivity)
  have hlenI : len ≤ I := min_le_left _ _
  have hlenlam : 2*len ≤ lam := by
    have hh : len ≤ lam/2 := min_le_right _ _
    linarith only [hh]
  have hm : 0 < m := div_pos (lt_min hp hw0) (by norm_num)
  have hmq : m ≤ p/128 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hmw : m ≤ w/8 := by
    have hh : min p w ≤ w := min_le_right _ _
    dsimp [m]
    linarith only [hh,hw0]
  have hstable : 2*len ≤ (128*(P/m)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2 := by
    dsimp only [m,L]
    rw [stability_massScale_identity]
    convert hlenlam using 1; norm_num [lam]
  have hbnd := hbound s T F hs hT h0 zX S Q k a b I len w M A P L m 128
    hS hS0 ha hb hlen hlenI hab hM hA hP (by dsimp [L]; linarith only [hL]) hm hw0 (by norm_num)
    hmq hmw hsmall hwφ hstable hband HX HZ
  have hscale := direction_source_far_scale hP hL (show (0:ℝ) < 16384 by norm_num)
    hM hA hp1 hw hθ hr hφ (cappedRepresentative_le_one _) hθφ hpP hwP hfar
  have hE : 0 ≤ E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  apply hbnd.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ C*E*(8196*(1+16384*(M+Real.sqrt A))*w*Real.sqrt L) :=
      mul_le_mul_of_nonneg_left hscale (mul_nonneg hC hE)
    _ = _ := by dsimp [E,L]; ring

lemma tsum_quad_cutoff_bound (f : (Fin 4→ℕ)→ℝ≥0∞) (N : ℕ) (c : ℝ≥0∞)
    (h : ∀k,f k ≤ if ∀i,k i<N then c else 0) :
    (∑'k,f k) ≤ c*(N:ℝ≥0∞)^4 := by
  classical
  have he (np nt nf nr : ℕ) : (∀i : Fin 4,(![np,nt,nf,nr] : Fin 4→ℕ) i<N) ↔
      np<N ∧ nt<N ∧ nf<N ∧ nr<N := by simp [Fin.forall_fin_succ]
  calc
    _ ≤ ∑'k,if ∀i,k i<N then c else 0 := ENNReal.tsum_le_tsum h
    _ = ∑'np,∑'nt,∑'nf,∑'nr,if np<N ∧ nt<N ∧ nf<N ∧ nr<N then c else 0 := by
      rw [tsum_quad_index]
      simp_rw [he]
    _ = ∑'np,if np<N then ∑'nt,if nt<N then ∑'nf,if nf<N then ∑'nr,if nr<N then c else 0 else 0 else 0 else 0 := by
      apply tsum_congr
      intro np
      by_cases hp : np<N
      · simp only [hp,true_and,ite_true]
        apply tsum_congr
        intro nt
        by_cases ht : nt<N
        · simp only [ht,true_and,ite_true]
          apply tsum_congr
          intro nf
          by_cases hf : nf<N <;> simp [hf]
        · simp [ht]
      · simp [hp]
    _ = c*(N:ℝ≥0∞)^4 := by simp only [ennreal_tsum_indicator_lt]; ring

lemma Admissible.projected_source_stable_far_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ, 0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (N : ℕ)
        (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ (w/P)^2 →
      0 < M → 0 ≤ A → 0 < P → 1 ≤ Real.log (2+P) → 1 ≤ w → w ≤ P →
      (∀t∈Icc a b,w/16 ≤ ‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let sector : Set (Fin 4→ℕ) := {k | (∀i,k i<N) ∧ sourceRepresentative (k 0) ≤ 128*P ∧
        cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 ∧
        32 ≤ cappedRepresentative (k 2)*w ∧
        1/32 ≤ sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))}
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'k : Fin 4→ℕ,sector.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
          ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k) ≤
      ENNReal.ofReal (C*E*(1+16384*(M+Real.sqrt A))*w*
        Real.sqrt (Real.log (2+P))*(N:ℝ)^4) := by
  classical
  obtain ⟨C,hC,hbound⟩ := hd₀.projected_source_stable_far_bound
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX S Q N a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP hband HX HZ
  dsimp only
  let E := ∫x : Vec,totalEnergy s (0,x)
  let c := C*E*(1+16384*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P))
  let sector : Set (Fin 4→ℕ) := {k | (∀i,k i<N) ∧ sourceRepresentative (k 0) ≤ 128*P ∧
    cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 ∧
    32 ≤ cappedRepresentative (k 2)*w ∧
    1/32 ≤ sourceRepresentative (k 0)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3))}
  let f := sector.indicator (fun k=>∫⁻z : ConeCoordinate,
    physicalProjectedSourceDensity s (fun t=>(prefixFlow F.flow T zX t).1)
      (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) T w Q z
        ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2)
          (representativeClosedBin T w k) (Icc a b))
  have hE : 0 ≤ E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hbin (k : Fin 4→ℕ) : f k ≤ if ∀i,k i<N then ENNReal.ofReal c else 0 := by
    by_cases hk : k∈sector
    · have he : f k = ∫⁻z : ConeCoordinate,
          physicalProjectedSourceDensity s (fun t=>(prefixFlow F.flow T zX t).1)
            (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) T w Q z
            ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2)
              (representativeClosedBin T w k) (Icc a b) := indicator_of_mem hk _
      rw [he,ite_eq_left hk.1]
      exact hbound s T F hs hT h0 zX S Q k a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP
        hk.2.1 hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2 hband HX HZ
    · have he : f k=0 := indicator_of_notMem hk _
      rw [he]
      exact bot_le
  have hsum := tsum_quad_cutoff_bound f N (ENNReal.ofReal c) hbin
  apply hsum.trans_eq
  rw [show (N:ℝ≥0∞)^4=ENNReal.ofReal ((N:ℝ)^4) by
    rw [ENNReal.ofReal_pow (Nat.cast_nonneg N),ENNReal.ofReal_natCast],←ENNReal.ofReal_mul hc]

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

lemma Admissible.projected_source_stable_far_log_sum {d : Datum} (hd₀ : Admissible d)
    (T₀ : ℝ) :
    ∃C : ℝ, 0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → T ≤ T₀ → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ))
        (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ (w/P)^2 →
      0 < M → 0 ≤ A → 0 < P → 1 ≤ Real.log (2+P) → 1 ≤ w → w ≤ P →
      (∀t∈Icc a b,w/16 ≤ ‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let sector : Set (Fin 4→ℕ) := {k | sourceRepresentative (k 0) ≤ 128*P ∧
        cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 ∧
        32 ≤ cappedRepresentative (k 2)*w ∧
        1/32 ≤ sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))}
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'k : Fin 4→ℕ,sector.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
          ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k) ≤
      ENNReal.ofReal (C*E*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^5) := by
  classical
  obtain ⟨Cs,hCs,hsum⟩ := hd₀.projected_source_stable_far_sum
  obtain ⟨Cn,hCn,hcount⟩ := exists_far_dyadic_count T₀
  refine ⟨Cs*Cn^4,by positivity,?_⟩
  intro s T F hs hT hTT h0 zX S Q a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP
    hband HX HZ
  dsimp only
  let E := ∫x : Vec,totalEnergy s (0,x)
  let sector : Set (Fin 4→ℕ) := {k | sourceRepresentative (k 0) ≤ 128*P ∧
    cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 ∧
    32 ≤ cappedRepresentative (k 2)*w ∧
    1/32 ≤ sourceRepresentative (k 0)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3))}
  obtain ⟨N,hN0,hN1,hN3,hNc⟩ := hcount P hP hL
  have hH : max (1:ℝ) T ≤ max 1 T₀ := max_le_max_left 1 hTT
  have hN1' : 4096*P*Real.sqrt (max 1 T) < (2:ℝ)^N :=
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hH) (by positivity)).trans_lt hN1
  have hN3' : (4096*P)^2*max 1 T < (2:ℝ)^N :=
    (mul_le_mul_of_nonneg_left hH (sq_nonneg _)).trans_lt hN3
  have hidx (k : Fin 4→ℕ) (hk : k∈sector) : ∀i,k i<N := by
    have hφ : 0 < cappedRepresentative (k 2) := cappedRepresentative_pos _
    have hθφ : cappedRepresentative (k 1) ≤ cappedRepresentative (k 2) := by
      have hh := hk.2.1
      linarith only [hh,hφ]
    exact direction_far_indices hP hk.1 hθφ hk.2.2.2 hN0 hN1' hN3'
  have heq : {k : Fin 4→ℕ | (∀i,k i<N) ∧ sourceRepresentative (k 0) ≤ 128*P ∧
      cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 ∧
      32 ≤ cappedRepresentative (k 2)*w ∧
      1/32 ≤ sourceRepresentative (k 0)*cappedRepresentative (k 1)*
        Real.sqrt (max 1 T*cappedRepresentative (k 3))} = sector := by
    ext k
    exact ⟨fun hk=>hk.2,fun hk=>⟨hidx k hk,hk⟩⟩
  have hbnd := hsum s T F hs hT h0 zX S Q N a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP
    hband HX HZ
  dsimp only at hbnd
  rw [heq] at hbnd
  have hE : 0 ≤ E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hL0 : 0 ≤ Real.log (2+P) := zero_le_one.trans hL
  have hroot : Real.sqrt (Real.log (2+P)) ≤ Real.log (2+P) := Real.sqrt_le_self_iff.mpr (Or.inr hL)
  have hpower : (N:ℝ)^4 ≤ (Cn*Real.log (2+P))^4 := pow_le_pow_left₀ (Nat.cast_nonneg N) hNc _
  have hscalar : Real.sqrt (Real.log (2+P))*(N:ℝ)^4 ≤ Cn^4*(Real.log (2+P))^5 := by
    calc
      _ ≤ Real.log (2+P)*(Cn*Real.log (2+P))^4 := mul_le_mul hroot hpower (by positivity) hL0
      _ = _ := by ring
  apply hbnd.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = (Cs*E*(1+16384*(M+Real.sqrt A))*w)*(Real.sqrt (Real.log (2+P))*(N:ℝ)^4) := by ring
    _ ≤ (Cs*E*(1+16384*(M+Real.sqrt A))*w)*(Cn^4*(Real.log (2+P))^5) :=
      mul_le_mul_of_nonneg_left hscalar (by positivity)
    _ = _ := by dsimp [E]; ring

lemma Admissible.central_density_baseline_bin {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (k : Fin 4→ℕ)
        (a b I len w M A P L massScale Cs : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → 0 < len → len ≤ I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
      massScale ≤ sourceRepresentative (k 0)/128 → massScale ≤ w/8 →
      cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 →
      32 ≤ cappedRepresentative (k 2)*w →
      2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative (k 2)+
        Real.sqrt (A*L/cappedRepresentative (k 2))))⁻¹^2 →
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
      ENNReal.ofReal (78400000*φ^2/θ)*(∫⁻z : ConeCoordinate,physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B (Icc a b)) ≤
        ENNReal.ofReal (C*(1+E))*
          min (ENNReal.ofReal (I*p^3*θ*φ^4*r))
              (ENNReal.ofReal ((1+I/len)/(p*θ*r))) := by
  obtain ⟨Cρ,hCρ,hdensity⟩ := hd₀.uniform_physicalBinDensity_constant
  let c : ℝ := 1
  have hc : 0 ≤ c := by norm_num [c]
  let C : ℝ := 10^18*c*(1+Cρ)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro s T F hs hT h0 zX S k a b I len w M A P L massScale Cs hS hS0 ha hb hlen hlenI hab
    hM hA hP hL hm hw hCs hmq hmw hsmall hwφ hstable HX HZ
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
  have hden : ∀z∈physicalBinBase V B (Icc a b),
      physicalBinDensity s X V B z.1 z.2.1 z.2.2 ≤ ENNReal.ofReal (128*Cρ*p^3*θ^2) := by
    intro z hz
    have hzT : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans (hJ hz.1).2⟩
    have hn := hdensity s T F hs h0 X V B z.1 z.2.1 z.2.2 p θ 1 hzT hp.le hθ.le (by norm_num)
      (by change p/32 ≤ p; linarith) le_rfl (by norm_num [B,representativeClosedBin])
    simpa only [min_eq_left (show θ ≤ 1 from cappedRepresentative_le_one (k 1))] using hn
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hnear := physicalBin_density_near hα.snd.measurable B measurableSet_Icc hφ.le le_rfl hden
  have hfar := F.physicalBin_density_far hs hT zX B hS hS0 hJ
    (by change 0 < r/2; positivity) (by change 0 < φ^2/2; positivity)
  have hnearfar := mul_le_mul' (le_refl (ENNReal.ofReal (78400000*c*φ^2/θ))) (le_min hnear hfar)
  have hbudget := F.closedEulerian_baseline_budget hs hT zX B hS (k 0) (k 2)
    (by rfl : p=64*(2:ℝ)^(k 0)) (by rfl : φ=(2:ℝ)⁻¹^(k 2)) ha hb hlen hlenI hab
    hM hA hP hL hm hφ (cappedRepresentative_le_one _) hCs hstable le_rfl le_rfl hmq hmw
    (by change 0 < r/2; positivity) (by rw [hBmax]; positivity) hdsmall le_rfl le_rfl
    (by change 4 ≤ φ*(w/8); dsimp [φ] at *; nlinarith) HX HZ
  have hvol : volume (Icc a b) ≤ ENNReal.ofReal I := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal hab
  let near := I*p^3*θ*φ^4*r
  let far := (1+I/len)/(p*θ*r)
  have hn0 : 0 ≤ near := by dsimp [near]; positivity
  have hf0 : 0 ≤ far := by dsimp [far]; positivity
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
        dsimp [near]
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
        dsimp [far]
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
            nlinarith
      _ = _ := ENNReal.ofReal_mul (by dsimp [C]; positivity)
  have he : (78400000:ℝ)*c*φ^2/θ=78400000*φ^2/θ := by dsimp [c]; ring
  rw [he] at hnearfar hn hf
  apply hnearfar.trans
  simpa only [near,far,E,p,θ,φ,r,mul_min,mul_assoc] using min_le_min hn hf

lemma Admissible.central_density_baseline_radial_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (np nθ nφ : ℕ)
        (a b I len w M A P L massScale Cs : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → 0 < len → len ≤ I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
      massScale ≤ sourceRepresentative np/128 → massScale ≤ w/8 →
      cappedRepresentative nθ ≤ cappedRepresentative nφ/16 →
      32 ≤ cappedRepresentative nφ*w →
      2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative nφ+
        Real.sqrt (A*L/cappedRepresentative nφ)))⁻¹^2 →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
      let p := sourceRepresentative np
      let φ := cappedRepresentative nφ
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>representativeClosedBin T w ![np,nθ,nφ,nr]
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'nr : ℕ,ENNReal.ofReal (78400000*(cappedRepresentative nφ)^2/cappedRepresentative nθ)*
        (∫⁻z : ConeCoordinate,physicalBinDensity s X V (B nr) z.1 z.2.1 z.2.2
          ∂physicalBinMeasure V (B nr) (Icc a b))) ≤
      ENNReal.ofReal (C*(1+E)*(6*Real.sqrt I*Real.sqrt (1+I/len)*p*φ^2)) := by
  obtain ⟨C,hC,hbound⟩ := hd₀.central_density_baseline_bin
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ a b I len w M A P L massScale Cs hS hS0 ha hb hlen hlenI hab
    hM hA hP hL hm hw hCs hmq hmw hsmall hwφ hstable HX HZ
  dsimp only
  have hI : 0<I := hlen.trans_le hlenI
  have hE : 0≤ ∫x : Vec,totalEnergy s (0,x) := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hbnd (nr : ℕ) := hbound s T F hs hT h0 zX S ![np,nθ,nφ,nr]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three] at hbnd
  have hbnd' (nr : ℕ) := hbnd nr a b I len w M A P L massScale Cs hS hS0 ha hb hlen hlenI hab
    hM hA hP hL hm hw hCs hmq hmw hsmall hwφ hstable HX HZ
  have hs1 := ENNReal.tsum_le_tsum hbnd'
  rw [ENNReal.tsum_mul_left] at hs1
  apply hs1.trans
  rw [ENNReal.ofReal_mul (by positivity : 0≤C*(1+∫x : Vec,totalEnergy s (0,x)))]
  exact mul_le_mul' le_rfl (geometry_radial_ennreal_sum (I:=I) (len:=len)
    (p:=sourceRepresentative np) (θ:=cappedRepresentative nθ) (φ:=cappedRepresentative nφ)
    (H:=max 1 T) hI hlen
    (by dsimp [sourceRepresentative]; positivity) (cappedRepresentative_pos _)
    (cappedRepresentative_pos _) (zero_lt_one.trans_le (le_max_left _ _)))

lemma Admissible.central_density_stable_radial_bound {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ, 0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (np nθ nφ : ℕ)
        (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ (w/P)^2 →
      0 < M → 0 ≤ A → 0 < P → 1 ≤ Real.log (2+P) → 0 < w → w ≤ P →
      sourceRepresentative np ≤ 128*P →
      cappedRepresentative nθ ≤ cappedRepresentative nφ/16 →
      32 ≤ cappedRepresentative nφ*w →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>representativeClosedBin T w ![np,nθ,nφ,nr]
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'nr : ℕ,ENNReal.ofReal (78400000*(cappedRepresentative nφ)^2/cappedRepresentative nθ)*
        (∫⁻z : ConeCoordinate,physicalBinDensity s X V (B nr) z.1 z.2.1 z.2.2
          ∂physicalBinMeasure V (B nr) (Icc a b))) ≤
      ENNReal.ofReal (C*(1+E)*(1+16384*(M+Real.sqrt A))*w*
        Real.sqrt (Real.log (2+P))*cappedRepresentative nφ) := by
  obtain ⟨C,hC,hbound⟩ := hd₀.central_density_baseline_radial_sum
  refine ⟨1536*C,by positivity,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP
    hpP hsmall hwφ HX HZ
  dsimp only
  let p := sourceRepresentative np
  let φ := cappedRepresentative nφ
  let L := Real.log (2+P)
  let I := (w/P)^2
  let lam := stabilityLength P 16384 M A p w φ
  let len := min I (lam/2)
  let m := min p w/128
  let E := ∫x : Vec,totalEnergy s (0,x)
  have hp : 0 < p := by dsimp [p,sourceRepresentative]; positivity
  have hφ : 0 < φ := cappedRepresentative_pos _
  have hI : 0 < I := sq_pos_of_pos (div_pos hw hP)
  have hlam : 0 < lam := stabilityLength_pos hP (by norm_num) hM hp hw hφ
  have hlen : 0 < len := lt_min hI (by positivity)
  have hlenI : len ≤ I := min_le_left _ _
  have hlenlam : 2*len ≤ lam := by
    have hh : len ≤ lam/2 := min_le_right _ _
    linarith
  have hm : 0 < m := div_pos (lt_min hp hw) (by norm_num)
  have hmq : m ≤ p/128 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hmw : m ≤ w/8 := by
    have hh : min p w ≤ w := min_le_right _ _
    dsimp [m]
    linarith
  have hstable : 2*len ≤ (128*(P/m)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2 := by
    dsimp only [m,L]
    rw [stability_massScale_identity]
    convert hlenlam using 1; norm_num [lam]
  have hbnd := hbound s T F hs hT h0 zX S np nθ nφ a b I len w M A P L m 128
    hS hS0 ha hb hlen hlenI hab hM hA hP (by dsimp [L]; linarith) hm hw (by norm_num)
    hmq hmw hsmall hwφ hstable HX HZ
  have hR := direction_clipped_baseline_R_log_bound128 hP hL (show (0:ℝ) < 16384 by norm_num)
    hM hA hp hw hφ (cappedRepresentative_le_one _) hpP hwP
  have hR' : Real.sqrt I*Real.sqrt (1+I/len)*p*φ ≤
      256*(1+16384*(M+Real.sqrt A))*w*Real.sqrt L := hR
  have hE : 0 ≤ E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hgeom : 6*Real.sqrt I*Real.sqrt (1+I/len)*p*φ^2 ≤
      1536*(1+16384*(M+Real.sqrt A))*w*Real.sqrt L*φ := by
    calc
      _ = 6*(Real.sqrt I*Real.sqrt (1+I/len)*p*φ)*φ := by ring
      _ ≤ 6*(256*(1+16384*(M+Real.sqrt A))*w*Real.sqrt L)*φ := by gcongr
      _ = _ := by ring
  apply hbnd.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ C*(1+E)*(1536*(1+16384*(M+Real.sqrt A))*w*Real.sqrt L*φ) :=
      mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = _ := by dsimp [E,L,φ]; ring

lemma Admissible.central_density_stable_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ, 0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (N : ℕ)
        (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ (w/P)^2 →
      0 < M → 0 ≤ A → 0 < P → 1 ≤ Real.log (2+P) → 0 < w → w ≤ P →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let sector : Set (Fin 4→ℕ) := {k | k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0) ≤ 128*P ∧
        cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 ∧
        32 ≤ cappedRepresentative (k 2)*w}
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'k : Fin 4→ℕ,sector.indicator (fun k=>ENNReal.ofReal (78400000*(cappedRepresentative (k 2))^2/cappedRepresentative (k 1))*
        (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k) z.1 z.2.1 z.2.2
          ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b))) k) ≤
      ENNReal.ofReal (C*(1+E)*(1+16384*(M+Real.sqrt A))*w*
        Real.sqrt (Real.log (2+P))*(N:ℝ)^2) := by
  classical
  obtain ⟨C,hC,hbound⟩ := hd₀.central_density_stable_radial_bound
  refine ⟨2*C,by positivity,?_⟩
  intro s T F hs hT h0 zX S N a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP HX HZ
  dsimp only
  let E := ∫x : Vec,totalEnergy s (0,x)
  let c := C*(1+E)*(1+16384*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P))
  let sector : Set (Fin 4→ℕ) := {k | k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0) ≤ 128*P ∧
    cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 ∧
    32 ≤ cappedRepresentative (k 2)*w}
  let f := sector.indicator (fun k=>ENNReal.ofReal (78400000*(cappedRepresentative (k 2))^2/cappedRepresentative (k 1))*
    (∫⁻z : ConeCoordinate,physicalBinDensity s (fun t=>(prefixFlow F.flow T zX t).1)
      (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) z.1 z.2.1 z.2.2
        ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2)
          (representativeClosedBin T w k) (Icc a b)))
  have hE : 0 ≤ E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have he (np nt nf nr : ℕ) : ![np,nt,nf,nr]∈sector ↔
      np<N ∧ nt<N ∧ sourceRepresentative np ≤ 128*P ∧
        cappedRepresentative nt ≤ cappedRepresentative nf/16 ∧ 32 ≤ cappedRepresentative nf*w := by
    rfl
  have hrad (np nt nf : ℕ) : (∑'nr,f ![np,nt,nf,nr]) ≤
      (if np<N ∧ nt<N then ENNReal.ofReal c*ENNReal.ofReal ((2:ℝ)⁻¹^nf) else 0) := by
    by_cases hbin : np<N ∧ nt<N ∧ sourceRepresentative np ≤ 128*P ∧
        cappedRepresentative nt ≤ cappedRepresentative nf/16 ∧ 32 ≤ cappedRepresentative nf*w
    · have hf (nr : ℕ) : f ![np,nt,nf,nr] = ENNReal.ofReal (78400000*(cappedRepresentative nf)^2/cappedRepresentative nt)*
          (∫⁻z : ConeCoordinate,physicalBinDensity s (fun t=>(prefixFlow F.flow T zX t).1)
            (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w ![np,nt,nf,nr]) z.1 z.2.1 z.2.2
            ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2)
              (representativeClosedBin T w ![np,nt,nf,nr]) (Icc a b)) :=
        indicator_of_mem ((he np nt nf nr).mpr hbin) _
      simp_rw [hf]
      rw [ite_eq_left ⟨hbin.1,hbin.2.1⟩,←ENNReal.ofReal_mul hc]
      exact hbound s T F hs hT h0 zX S np nt nf a b w M A P hS hS0 ha hb hab
        hM hA hP hL hw hwP hbin.2.2.1 hbin.2.2.2.1 hbin.2.2.2.2 HX HZ
    · have hf (nr : ℕ) : f ![np,nt,nf,nr]=0 := indicator_of_notMem (fun hk=>hbin ((he np nt nf nr).mp hk)) _
      simp only [hf,tsum_zero]
      exact bot_le
  have hsum := tsum_quad_of_radial_bound f N (ENNReal.ofReal c) hrad
  apply hsum.trans_eq
  have heq : (2:ℝ≥0∞)*(N:ℝ≥0∞)^2=ENNReal.ofReal (2*(N:ℝ)^2) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),
      ENNReal.ofReal_pow (Nat.cast_nonneg N),ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat]
  rw [heq,←ENNReal.ofReal_mul hc]
  congr 1
  dsimp [c,E]
  ring

end RVM

end

end OAI
