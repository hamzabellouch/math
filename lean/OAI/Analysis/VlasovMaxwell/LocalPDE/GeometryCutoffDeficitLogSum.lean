import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.PhysicalProjectedRemainderSourceTruncate

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

lemma Admissible.geometry_cutoff_deficit_log_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (Q : Set (Fin 4→ℕ)) (a b w P D : ℝ),
      0 ≤ a → b ≤ T → b-a ≤ (w/P)^2 →
      0 ≤ D → 0<P → 1 ≤ Real.log (2+P) → 0<w → w ≤ P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2 ≤ P) →
      (∀t∈Icc a b,w/16 ≤ ‖(F.flow zX t).2‖) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let sector : Set (Fin 4→ℕ) := {k |
        cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 ∧
        max 1 T*cappedRepresentative (k 3) ≤ D/P^2}
      (∑'k : Fin 4→ℕ,sector.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalGeometryCutoffDensity s X V (representativeClosedBin T w k) T w Q z
          ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k) ≤
      ENNReal.ofReal (C*D*w*(Real.log (2+P))^2) := by
  classical
  obtain ⟨C,hC,hsum⟩ := hd₀.central_density_deficit_log_sum
  obtain ⟨c,hc,hcut⟩ := dyadicFactor_log_derivative_bound
  refine ⟨c*C,by positivity,?_⟩
  intro s T F hs hT h0 zX Q a b w P D ha hb hab hD hP hL hw hwP hsource hband
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let sector : Set (Fin 4→ℕ) := {k |
    cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 ∧
    max 1 T*cappedRepresentative (k 3) ≤ D/P^2}
  let f := fun k : Fin 4→ℕ=>
    ENNReal.ofReal (78400000*(cappedRepresentative (k 2))^2/cappedRepresentative (k 1))*
    (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k)
      z.1 z.2.1 z.2.2 ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b))
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hband' : ∀t∈Icc a b,w/16 ≤ ‖V t‖ := by
    intro t ht
    simpa only [V,prefixFlow,prefixClamp_eq (hJ ht)] using hband t ht
  have hbnd (k : Fin 4→ℕ) (hk : k∈sector) :
      (∫⁻z : ConeCoordinate,physicalGeometryCutoffDensity s X V (representativeClosedBin T w k) T w Q z
        ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) ≤ ENNReal.ofReal c*f k := by
    let θ := cappedRepresentative (k 1)
    let φ := cappedRepresentative (k 2)
    have hθ : 0<θ := cappedRepresentative_pos _
    have hφ : 0<φ := cappedRepresentative_pos _
    have hsmall : (representativeClosedBin T w k).dmax ≤ (representativeClosedBin T w k).Dmin := by
      change 8*θ^2 ≤ φ^2/2
      have hh : θ ≤ φ/16 := hk.1
      have hh2 := (sq_le_sq₀ hθ.le (by positivity : 0 ≤ φ/16)).mpr hh
      nlinarith only [hh2]
    have hh := physicalGeometryCutoff_integral_bound (X:=X) hs hα.snd.measurable
      (representativeClosedBin T w k) measurableSet_Icc hJ hc hcut hw hθ hφ.le hsmall
      (representativeClosedBin_radius_pos T w k) le_rfl le_rfl hband' Q
    have he : 78400000*c*φ^2/θ=c*(78400000*φ^2/θ) := by ring
    rw [he,ENNReal.ofReal_mul hc,mul_assoc] at hh
    exact hh
  have hs1 : (∑'k : Fin 4→ℕ,sector.indicator (fun k=>∫⁻z : ConeCoordinate,
      physicalGeometryCutoffDensity s X V (representativeClosedBin T w k) T w Q z
        ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k) ≤
      ∑'k : Fin 4→ℕ,ENNReal.ofReal c*sector.indicator f k := by
    apply ENNReal.tsum_le_tsum
    intro k
    by_cases hk : k∈sector
    · simpa only [indicator_of_mem hk] using hbnd k hk
    · simp only [indicator_of_notMem hk,mul_zero,le_refl]
  rw [ENNReal.tsum_mul_left] at hs1
  have hsub : (∑'k : Fin 4→ℕ,sector.indicator f k) ≤
      ∑'k : Fin 4→ℕ,({k | max 1 T*cappedRepresentative (k 3) ≤ D/P^2}:Set (Fin 4→ℕ)).indicator f k := by
    apply ENNReal.tsum_le_tsum
    intro k
    by_cases hk : k∈sector
    · rw [indicator_of_mem hk,indicator_of_mem (show k∈({k | max 1 T*cappedRepresentative (k 3) ≤ D/P^2}:Set (Fin 4→ℕ)) from hk.2)]
    · rw [indicator_of_notMem hk]
      exact bot_le
  have hs2 := hsub.trans (hsum s T F hs hT h0 zX a b w P D ha hb hab hw hwP hP hL hD hsource)
  apply hs1.trans ((mul_le_mul' le_rfl hs2).trans_eq _)
  rw [←ENNReal.ofReal_mul hc]
  congr 1
  ring

lemma Admissible.projected_remainder_deficit_log_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (a b w P D : ℝ),
      0 ≤ a → b ≤ T → b-a ≤ (w/P)^2 →
      0 ≤ D → 0<P → 1 ≤ Real.log (2+P) → 0<w → w ≤ P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2 ≤ P) →
      (∀t∈Icc a b,w/16 ≤ ‖(F.flow zX t).2‖) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let K := prefixMomentumForce s F.flow T zX
      let sector : Set (Fin 4→ℕ) := {k |
        cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 ∧
        max 1 T*cappedRepresentative (k 3) ≤ D/P^2 ∧
        sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3)) ≤ 1}
      (∑'k : Fin 4→ℕ,sector.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalProjectedRemainderDensity s X V (representativeClosedBin T w k) w K z
          ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k) ≤
      ENNReal.ofReal (C*D*w*(Real.log (2+P))^2)+
      (∫⁻t in Icc a b,ENNReal.ofReal ‖K t‖)*
        ENNReal.ofReal (C*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w) := by
  classical
  obtain ⟨Cs,hCs,hcentral⟩ := hd₀.central_density_deficit_log_sum
  obtain ⟨Cr,hCr,hremainder⟩ := hd₀.projected_remainder_selected_sum
  obtain ⟨Cn,hCn,hcount⟩ := exists_source_dyadic_count
  let C := Cs+Cr*Cn^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX a b w P D ha hb hab hD hP hL hw hwP hsource hband
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let K := prefixMomentumForce s F.flow T zX
  let W := ∫⁻t in Icc a b,ENNReal.ofReal ‖K t‖
  let sector : Set (Fin 4→ℕ) := {k |
    cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 ∧
    max 1 T*cappedRepresentative (k 3) ≤ D/P^2 ∧
    sourceRepresentative (k 0)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3)) ≤ 1}
  let stable : Set (Fin 4→ℕ) := {k | max 1 T*cappedRepresentative (k 3) ≤ D/P^2}
  let rfun := fun k : Fin 4→ℕ=>∫⁻z : ConeCoordinate,
    physicalProjectedRemainderDensity s X V (representativeClosedBin T w k) w K z
      ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)
  let cfun := fun k : Fin 4→ℕ=>
    ENNReal.ofReal (78400000*(cappedRepresentative (k 2))^2/cappedRepresentative (k 1))*
    (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k)
      z.1 z.2.1 z.2.2 ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b))
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  let source : Set (Fin 4→ℕ) := {k | k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0) ≤ 128*P}
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
  have hQ : ∀k∈Q,k 0<N ∧ k 1<N ∧ cappedRepresentative (k 1) ≤ cappedRepresentative (k 2) ∧
      sourceRepresentative (k 0)*cappedRepresentative (k 1)*
        Real.sqrt (max 1 T*cappedRepresentative (k 3)) ≤ 1 := by
    intro k hk
    refine ⟨hk.1.1,hk.1.2.1,?_,hk.2.2.2⟩
    have hh := hk.2.1
    have hφ := cappedRepresentative_pos (k 2)
    linarith only [hh,hφ]
  have hcsub : (∑'k : Fin 4→ℕ,Q.indicator cfun k) ≤ ∑'k : Fin 4→ℕ,stable.indicator cfun k := by
    apply ENNReal.tsum_le_tsum
    intro k
    by_cases hk : k∈Q
    · rw [indicator_of_mem hk,indicator_of_mem (show k∈stable from hk.2.2.1)]
    · rw [indicator_of_notMem hk]
      exact bot_le
  have hL0 : 0 ≤ Real.log (2+P) := zero_le_one.trans hL
  have hc : (∑'k : Fin 4→ℕ,Q.indicator cfun k) ≤
      ENNReal.ofReal (C*D*w*(Real.log (2+P))^2) := by
    apply (hcsub.trans (hcentral s T F hs hT h0 zX a b w P D ha hb hab hw hwP hP hL hD hsource)).trans
    apply ENNReal.ofReal_le_ofReal
    have hCsC : Cs ≤ C := by dsimp [C]; linarith only [mul_nonneg hCr (sq_nonneg Cn)]
    gcongr
  have hN2 : Cr*Real.sqrt (max 1 T)*(N:ℝ)^2/w ≤ C*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w := by
    apply div_le_div_of_nonneg_right _ hw.le
    calc
      _  ≤  Cr*Real.sqrt (max 1 T)*(Cn*Real.log (2+P))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg N) hNc _) (by positivity)
      _ = (Cr*Cn^2)*Real.sqrt (max 1 T)*(Real.log (2+P))^2 := by ring
      _  ≤  _ := by
        have hh : Cr*Cn^2 ≤ C := by dsimp [C]; linarith only [hCs]
        gcongr
  change (∑'k : Fin 4→ℕ,sector.indicator rfun k) ≤ _
  rw [heq]
  exact (hremainder s T F hs hT h0 zX (Icc a b) w N Q hQ measurableSet_Icc hJ hw hband).trans
    (add_le_add hc (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hN2)))

end RVM

end

end OAI
