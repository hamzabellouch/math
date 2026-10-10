import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.CappedRepresentativePos

namespace OAI

noncomputable section
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

def quadIndexEquiv : (Fin 4→ℕ) ≃ ℕ×ℕ×ℕ×ℕ where
  toFun k := (k 0,k 1,k 2,k 3)
  invFun k := ![k.1,k.2.1,k.2.2.1,k.2.2.2]
  left_inv k := by funext i; fin_cases i <;> rfl
  right_inv k := by rcases k with ⟨a,b,c,d⟩; rfl

lemma tsum_quad_index (f : (Fin 4→ℕ)→ℝ≥0∞) :
    (∑'k,f k)=∑'np,∑'nt,∑'nf,∑'nr,f ![np,nt,nf,nr] := by
  have h := quadIndexEquiv.symm.tsum_eq f
  rw [←h]
  simp only [ENNReal.tsum_prod']
  rfl

lemma ennreal_capped_half_sum :
    (∑'n : ℕ,ENNReal.ofReal ((2:ℝ)⁻¹^n)) = 2 := by
  have hsum : Summable (fun n : ℕ=>(2:ℝ)⁻¹^n) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun n=>by positivity) hsum]
  rw [tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤2⁻¹) (by norm_num : (2:ℝ)⁻¹<1)]
  norm_num

lemma ennreal_tsum_indicator_lt (N : ℕ) (c : ℝ≥0∞) :
    (∑'n : ℕ,if n<N then c else 0)=(N:ℝ≥0∞)*c := by
  classical
  calc
    _ = ∑n∈Finset.range N,if n<N then c else 0 := by
      apply tsum_eq_sum
      intro n hn
      exact ite_eq_right (fun h=>hn (Finset.mem_range.mpr h))
    _ = _ := by
      rw [Finset.sum_ite_of_true (fun n hn=>Finset.mem_range.mp hn)]
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]

lemma tsum_quad_of_radial_bound (f : (Fin 4→ℕ)→ℝ≥0∞) (N : ℕ) (c : ℝ≥0∞)
    (h : ∀np nt nf, (∑'nr,f ![np,nt,nf,nr]) ≤
      (if np<N ∧ nt<N then c*ENNReal.ofReal ((2:ℝ)⁻¹^nf) else 0)) :
    (∑'k,f k) ≤ c*(2*(N:ℝ≥0∞)^2) := by
  classical
  rw [tsum_quad_index]
  calc
    _ ≤ ∑'np,∑'nt,∑'nf,if np<N ∧ nt<N then c*ENNReal.ofReal ((2:ℝ)⁻¹^nf) else 0 := by
      apply ENNReal.tsum_le_tsum
      intro np
      apply ENNReal.tsum_le_tsum
      intro nt
      exact ENNReal.tsum_le_tsum (h np nt)
    _ = ∑'np,∑'nt,if np<N ∧ nt<N then c*2 else 0 := by
      apply tsum_congr
      intro np
      apply tsum_congr
      intro nt
      by_cases hb : np<N ∧ nt<N
      · simp only [ite_eq_left hb,ENNReal.tsum_mul_left,ennreal_capped_half_sum]
      · simp only [ite_eq_right hb,tsum_zero]
    _ = ∑'np,if np<N then ∑'nt,if nt<N then c*2 else 0 else 0 := by
      apply tsum_congr
      intro np
      by_cases hp : np<N <;> simp [hp]
    _ = c*(2*(N:ℝ≥0∞)^2) := by
      rw [ennreal_tsum_indicator_lt]
      simp only [ennreal_tsum_indicator_lt]
      ring

lemma Admissible.geometry_cutoff_stable_radial_bound {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ, 0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (np nθ nφ : ℕ)
        (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ (w/P)^2 →
      0 < M → 0 ≤ A → 0 < P → 1 ≤ Real.log (2+P) → 0 < w → w ≤ P →
      sourceRepresentative np ≤ 128*P →
      cappedRepresentative nθ ≤ cappedRepresentative nφ/16 →
      32 ≤ cappedRepresentative nφ*w →
      (∀t∈Icc a b,w/16 ≤ ‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>representativeClosedBin T w ![np,nθ,nφ,nr]
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalGeometryCutoffDensity s X V (B nr) T w Q z
        ∂physicalBinMeasure V (B nr) (Icc a b)) ≤
      ENNReal.ofReal (C*(1+E)*(1+16384*(M+Real.sqrt A))*w*
        Real.sqrt (Real.log (2+P))*cappedRepresentative nφ) := by
  obtain ⟨C,hC,hbound⟩ := hd₀.geometry_cutoff_baseline_radial_sum
  refine ⟨1536*C,by positivity,?_⟩
  intro s T F hs hT h0 zX S Q np nθ nφ a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP
    hpP hsmall hwφ hband HX HZ
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
  have hbnd := hbound s T F hs hT h0 zX S Q np nθ nφ a b I len w M A P L m 128
    hS hS0 ha hb hlen hlenI hab hM hA hP (by dsimp [L]; linarith) hm hw (by norm_num)
    hmq hmw hsmall hwφ hstable hband HX HZ
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

lemma Admissible.geometry_cutoff_stable_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ, 0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (N : ℕ)
        (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ (w/P)^2 →
      0 < M → 0 ≤ A → 0 < P → 1 ≤ Real.log (2+P) → 0 < w → w ≤ P →
      (∀t∈Icc a b,w/16 ≤ ‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let sector : Set (Fin 4→ℕ) := {k | k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0) ≤ 128*P ∧
        cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 ∧
        32 ≤ cappedRepresentative (k 2)*w}
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'k : Fin 4→ℕ,sector.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalGeometryCutoffDensity s X V (representativeClosedBin T w k) T w Q z
          ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k) ≤
      ENNReal.ofReal (C*(1+E)*(1+16384*(M+Real.sqrt A))*w*
        Real.sqrt (Real.log (2+P))*(N:ℝ)^2) := by
  classical
  obtain ⟨C,hC,hbound⟩ := hd₀.geometry_cutoff_stable_radial_bound
  refine ⟨2*C,by positivity,?_⟩
  intro s T F hs hT h0 zX S Q N a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP hband HX HZ
  dsimp only
  let E := ∫x : Vec,totalEnergy s (0,x)
  let c := C*(1+E)*(1+16384*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P))
  let sector : Set (Fin 4→ℕ) := {k | k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0) ≤ 128*P ∧
    cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 ∧
    32 ≤ cappedRepresentative (k 2)*w}
  let f := sector.indicator (fun k=>∫⁻z : ConeCoordinate,
    physicalGeometryCutoffDensity s (fun t=>(prefixFlow F.flow T zX t).1)
      (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) T w Q z
        ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2)
          (representativeClosedBin T w k) (Icc a b))
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
    · have hf (nr : ℕ) : f ![np,nt,nf,nr] = ∫⁻z : ConeCoordinate,
          physicalGeometryCutoffDensity s (fun t=>(prefixFlow F.flow T zX t).1)
            (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w ![np,nt,nf,nr]) T w Q z
            ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2)
              (representativeClosedBin T w ![np,nt,nf,nr]) (Icc a b) :=
        indicator_of_mem ((he np nt nf nr).mpr hbin) _
      simp_rw [hf]
      rw [ite_eq_left ⟨hbin.1,hbin.2.1⟩,←ENNReal.ofReal_mul hc]
      exact hbound s T F hs hT h0 zX S Q np nt nf a b w M A P hS hS0 ha hb hab
        hM hA hP hL hw hwP hbin.2.2.1 hbin.2.2.2.1 hbin.2.2.2.2 hband HX HZ
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
