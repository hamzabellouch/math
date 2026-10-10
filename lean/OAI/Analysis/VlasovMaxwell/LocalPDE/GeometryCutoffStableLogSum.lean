import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.RepresentativeClosedBinSourceIndices

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

lemma Admissible.geometry_cutoff_stable_log_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → b-a≤(w/P)^2 →
      0<M → 0≤A → 0<P → 1≤Real.log (2+P) → 0<w → w≤P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let sector : Set (Fin 4→ℕ) := {k |
        cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 ∧
        32≤cappedRepresentative (k 2)*w}
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'k : Fin 4→ℕ,sector.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalGeometryCutoffDensity s X V (representativeClosedBin T w k) T w Q z
          ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k)≤
      ENNReal.ofReal (C*(1+E)*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^3) := by
  classical
  obtain ⟨C,hC,hsum⟩ := hd₀.central_density_stable_log_sum
  obtain ⟨c,hc,hcut⟩ := dyadicFactor_log_derivative_bound
  refine ⟨c*C,by positivity,?_⟩
  intro s T F hs hT h0 zX S Q a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP hsource hband HX HZ
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let sector : Set (Fin 4→ℕ) := {k |
    cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 ∧
    32≤cappedRepresentative (k 2)*w}
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
      have hh : θ≤φ/16 := hk.1
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
    hM hA hP hL hw hwP hsource HX HZ
  apply hs1.trans ((mul_le_mul' le_rfl hs2).trans_eq _)
  rw [←ENNReal.ofReal_mul hc]
  congr 1
  ring

lemma Admissible.projected_remainder_selected_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (J : Set ℝ) (w : ℝ) (N : ℕ) (Q : Set (Fin 4→ℕ)),
      (∀k∈Q,k 0<N ∧ k 1<N ∧ cappedRepresentative (k 1)≤cappedRepresentative (k 2) ∧
        sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1) →
      MeasurableSet J → J⊆Icc 0 T → 0<w →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let W := ∫⁻t in J,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖
      (∑'k : Fin 4→ℕ,Q.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalProjectedRemainderDensity s X V (representativeClosedBin T w k) w
          (prefixMomentumForce s F.flow T zX) z
          ∂physicalBinMeasure V (representativeClosedBin T w k) J) k)≤
      (∑'k : Fin 4→ℕ,Q.indicator (fun k=>
        ENNReal.ofReal (78400000*(cappedRepresentative (k 2))^2/cappedRepresentative (k 1))*
        (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k)
          z.1 z.2.1 z.2.2 ∂physicalBinMeasure V (representativeClosedBin T w k) J)) k)+
      W*ENNReal.ofReal (C*Real.sqrt (max 1 T)*(N:ℝ)^2/w) := by
  classical
  obtain ⟨Cρ,hCρ,hdensity⟩ := hd₀.uniform_physicalBinDensity_constant
  let C := 1974272*49152*Cρ
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨32*C,by positivity,?_⟩
  intro s T F hs hT h0 zX J w N Q hQ hJ hJT hw hband
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let K := prefixMomentumForce s F.flow T zX
  let W := ∫⁻t in J,ENNReal.ofReal ‖K t‖
  let cfun := fun k : Fin 4→ℕ=>
    ENNReal.ofReal (78400000*(cappedRepresentative (k 2))^2/cappedRepresentative (k 1))*
    (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k)
      z.1 z.2.1 z.2.2 ∂physicalBinMeasure V (representativeClosedBin T w k) J)
  let rfun := fun k : Fin 4→ℕ=>∫⁻z : ConeCoordinate,
    physicalProjectedRemainderDensity s X V (representativeClosedBin T w k) w K z
      ∂physicalBinMeasure V (representativeClosedBin T w k) J
  let coeff := ENNReal.ofReal (4*C*Real.sqrt (max 1 T)/w)
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hK : Measurable (fun t=>ENNReal.ofReal ‖K t‖) :=
    (F.continuous_prefixMomentumForce hs hT zX).norm.measurable.ennreal_ofReal
  have hband' : ∀t∈J,w/16≤‖V t‖ := by
    intro t ht
    simpa only [V,prefixFlow,prefixClamp_eq (hJT ht)] using hband t ht
  have hbnd (k : Fin 4→ℕ) (hk : k∈Q) :
      rfun k≤cfun k+W*(coeff*ENNReal.ofReal (directionWeightMajorant N k)) := by
    let p := sourceRepresentative (k 0)
    let θ := cappedRepresentative (k 1)
    let φ := cappedRepresentative (k 2)
    let B := representativeClosedBin T w k
    have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
    have hθ : 0<θ := cappedRepresentative_pos _
    have hφ : 0<φ := cappedRepresentative_pos _
    have hsmall : θ≤φ := (hQ k hk).2.2.1
    have hr : 0<B.rmin := representativeClosedBin_radius_pos T w k
    have hR : 0≤B.rmax := by dsimp [B,representativeClosedBin,cappedRepresentative]; positivity
    have hden : ∀z∈physicalBinBase V B J,
        physicalBinDensity s X V B z.1 z.2.1 z.2.2≤ENNReal.ofReal (128*Cρ*p^3*θ^2) := by
      intro z hz
      have hzT : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩
      have hh := hdensity s T F hs h0 X V B z.1 z.2.1 z.2.2 p θ 1 hzT hp.le hθ.le (by norm_num)
        (by change p/32≤p; linarith only [hp]) le_rfl (by norm_num [B,representativeClosedBin])
      simpa only [min_eq_left (show θ≤1 from cappedRepresentative_le_one _)] using hh
    have hb := physicalProjectedRemainder_integral_bound hs hT hα.fst.measurable hα.snd.measurable B
      hJ hJT hw hθ.le hφ hsmall hr le_rfl le_rfl le_rfl hband' (K:=K)
    have hac := physicalBin_radial_density_near hα.snd.measurable B hJ
      hCρ hp.le hθ.le hφ.le hR le_rfl hden hK
    have hc : 6272*φ≤78400000*φ^2/θ := by
      apply (le_div_iff₀ hθ).mpr
      have hh := mul_le_mul_of_nonneg_left hsmall hφ.le
      nlinarith only [hh,sq_nonneg φ]
    have hacc : ENNReal.ofReal (1974272*θ/(w*φ))*
        ((∫⁻z : ConeCoordinate,ENNReal.ofReal ‖K z.1‖*ENNReal.ofReal (z.1-z.2.1)*
          physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J))≤
        W*(coeff*ENNReal.ofReal (directionWeightMajorant N k)) := by
      calc
        _ ≤ ENNReal.ofReal (1974272*θ/(w*φ))*
            (W*ENNReal.ofReal (49152*Cρ*p^3*θ^2*φ^2*B.rmax*(B.rmax-B.rmin))) :=
          mul_le_mul' le_rfl hac
        _ = W*ENNReal.ofReal (C*(p*θ)^3*φ/w*B.rmax*(B.rmax-B.rmin)) := by
          rw [mul_left_comm,←ENNReal.ofReal_mul (by positivity : 0≤1974272*θ/(w*φ))]
          congr 2
          dsimp [C]
          field_simp [hφ.ne',hw.ne']
        _ ≤ W*(coeff*ENNReal.ofReal (directionWeightMajorant N k)) := by
          apply mul_le_mul' le_rfl
          dsimp [coeff]
          rw [←ENNReal.ofReal_mul (by positivity : 0≤4*C*Real.sqrt (max 1 T)/w)]
          exact ENNReal.ofReal_le_ofReal (selected_representative_moving_bound hC hw.le
            (hQ k hk).1 (hQ k hk).2.1 (hQ k hk).2.2.2)
    exact hb.trans (add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal hc) le_rfl) hacc)
  change (∑'k,Q.indicator rfun k)≤(∑'k,Q.indicator cfun k)+_
  calc
    _ ≤ ∑'k : Fin 4→ℕ,(Q.indicator cfun k+W*(coeff*ENNReal.ofReal (directionWeightMajorant N k))) := by
      apply ENNReal.tsum_le_tsum
      intro k
      by_cases hk : k∈Q
      · simpa only [indicator_of_mem hk] using hbnd k hk
      · simp only [indicator_of_notMem hk,zero_add]
        exact bot_le
    _ = (∑'k,Q.indicator cfun k)+W*(coeff*(∑'k : Fin 4→ℕ,ENNReal.ofReal (directionWeightMajorant N k))) := by
      rw [ENNReal.tsum_add,ENNReal.tsum_mul_left,ENNReal.tsum_mul_left]
    _ ≤ (∑'k,Q.indicator cfun k)+W*(coeff*ENNReal.ofReal (8*(N:ℝ)^2)) :=
      add_le_add le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl (tsum_directionWeightMajorant N)))
    _ = _ := by
      dsimp [coeff]
      rw [←ENNReal.ofReal_mul (by positivity : 0≤4*C*Real.sqrt (max 1 T)/w)]
      congr 3
      ring

end RVM

end

end OAI
