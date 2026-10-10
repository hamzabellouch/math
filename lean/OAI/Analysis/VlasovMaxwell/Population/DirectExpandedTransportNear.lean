import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.CentralOccupation

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma remaining_transport_near_point_expanded {θ φ σ : ℝ} (hθ : 0<θ) (hφ : 0≤φ) (hσ : 0≤σ)
    (hφθ : φ≤16384*θ) :
    (min θ σ)^2*φ^2*(θ+φ)/θ^3≤16385*σ*φ^2/θ := by
  have hν : 0 ≤ min θ σ := le_min hθ.le hσ
  have hs : (min θ σ)^2≤θ*σ := by
    calc
      _=(min θ σ)*(min θ σ) := pow_two _
      _≤θ*σ := mul_le_mul (min_le_left _ _) (min_le_right _ _) hν hθ.le
  calc
    _≤(θ*σ)*φ^2*(16385*θ)/θ^3 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul (mul_le_mul_of_nonneg_right hs (sq_nonneg φ)) (by linarith : θ+φ≤16385*θ)
        (by positivity) (by positivity)
    _=_ := by field_simp

lemma remaining_transport_near_angular_expanded :
    (∑'nt : ℕ,∑'nf : ℕ,if cappedRepresentative nf≤16384*cappedRepresentative nt then
      ∑'j : ℕ,ENNReal.ofReal ((min (cappedRepresentative nt) (cappedRepresentative j))^2*
        (cappedRepresentative nf)^2*(cappedRepresentative nt+cappedRepresentative nf)/(cappedRepresentative nt)^3)
      else 0)≤ENNReal.ofReal 35186519572480 := by
  have hrelative (nt nf : ℕ) (hφθ : cappedRepresentative nf≤16384*cappedRepresentative nt) :
      (∑'j : ℕ,ENNReal.ofReal ((min (cappedRepresentative nt) (cappedRepresentative j))^2*
        (cappedRepresentative nf)^2*(cappedRepresentative nt+cappedRepresentative nf)/(cappedRepresentative nt)^3))≤
      ENNReal.ofReal (32770*(cappedRepresentative nf)^2/cappedRepresentative nt) := by
    calc
      _≤∑'j : ℕ,ENNReal.ofReal ((16385*(cappedRepresentative nf)^2/cappedRepresentative nt)*cappedRepresentative j) := by
        apply ENNReal.tsum_le_tsum
        intro j
        apply ENNReal.ofReal_le_ofReal
        calc
          _≤16385*cappedRepresentative j*(cappedRepresentative nf)^2/cappedRepresentative nt :=
            remaining_transport_near_point_expanded (cappedRepresentative_pos _) (cappedRepresentative_pos _).le
              (cappedRepresentative_pos _).le hφθ
          _=_ := by ring
      _=_ := by
        rw [show (∑'j : ℕ,ENNReal.ofReal ((16385*(cappedRepresentative nf)^2/cappedRepresentative nt)*cappedRepresentative j))=
          ∑'j : ℕ,ENNReal.ofReal ((16385*(cappedRepresentative nf)^2/cappedRepresentative nt)*(1*cappedRepresentative j)) by simp]
        rw [capped_linear_radius_sum (div_nonneg (by positivity) (cappedRepresentative_pos _).le) (by norm_num)]
        congr 1
        ring
  have hreceiver (nt : ℕ) :
      (∑'nf : ℕ,if cappedRepresentative nf≤16384*cappedRepresentative nt then
        ENNReal.ofReal (32770*(cappedRepresentative nf)^2/cappedRepresentative nt) else 0)≤
      ENNReal.ofReal (17593259786240*cappedRepresentative nt) := by
    let θ := cappedRepresentative nt
    have hθ : 0<θ := cappedRepresentative_pos _
    have he (nf : ℕ) : (if cappedRepresentative nf≤16384*θ then
        ENNReal.ofReal (32770*(cappedRepresentative nf)^2/θ) else 0)=
        ENNReal.ofReal (32770/θ)*ENNReal.ofReal (if cappedRepresentative nf≤16384*θ then (cappedRepresentative nf)^2 else 0) := by
      split_ifs
      · rw [←ENNReal.ofReal_mul (by positivity : 0≤32770/θ)]
        congr 1
        ring
      · simp
    change (∑'nf : ℕ,if cappedRepresentative nf≤16384*θ then ENNReal.ofReal (32770*(cappedRepresentative nf)^2/θ) else 0)≤_
    simp_rw [he]
    rw [ENNReal.tsum_mul_left]
    calc
      _≤ENNReal.ofReal (32770/θ)*ENNReal.ofReal (2*(16384*θ)^2) :=
        mul_le_mul' le_rfl (capped_square_tail_sum (by positivity))
      _=_ := by
        rw [←ENNReal.ofReal_mul (by positivity : 0≤32770/θ)]
        congr 1
        dsimp [θ]
        field_simp
        ring
  calc
    _≤∑'nt : ℕ,∑'nf : ℕ,if cappedRepresentative nf≤16384*cappedRepresentative nt then
        ENNReal.ofReal (32770*(cappedRepresentative nf)^2/cappedRepresentative nt) else 0 := by
      apply ENNReal.tsum_le_tsum
      intro nt
      apply ENNReal.tsum_le_tsum
      intro nf
      split_ifs with h
      · exact hrelative nt nf h
      · rfl
    _≤∑'nt : ℕ,ENNReal.ofReal (17593259786240*cappedRepresentative nt) := ENNReal.tsum_le_tsum hreceiver
    _=ENNReal.ofReal 35186519572480 := by
      convert capped_linear_radius_sum (by norm_num : (0:ℝ)≤17593259786240) (by norm_num : (0:ℝ)≤1) using 1 <;> norm_num

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.direct_remaining_transport_angular_expanded {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np : ℕ) (a b I w : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → b-a≤I → 0<I →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nt nf j nr=>relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j
      (∑'nt : ℕ,∑'nf : ℕ,if cappedRepresentative nf≤16384*cappedRepresentative nt then
        ∑'j : ℕ,∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V (B nt nf j nr) z
          ∂physicalBinMeasure V (B nt nf j nr) (Icc a b) else 0)≤
      ENNReal.ofReal (C*I*max 1 T*sourceRepresentative np) := by
  obtain ⟨Cn,hCn,hnear⟩ := hd.direct_transport_radius_near
  refine ⟨70373039144960*Cn,by positivity,?_⟩
  intro s T F hs hT h0 zX S np a b I w hS hS0 ha hb hJI hI
  dsimp only
  let p := sourceRepresentative np
  let H := max 1 T
  let k := 2*Cn*I*H*p
  let ang (nt nf j : ℕ) := (min (cappedRepresentative nt) (cappedRepresentative j))^2*
    (cappedRepresentative nf)^2*(cappedRepresentative nt+cappedRepresentative nf)/(cappedRepresentative nt)^3
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hH : 0<H := zero_lt_one.trans_le (le_max_left _ _)
  have hk : 0≤k := by dsimp [k]; positivity
  have hanga (nt nf j : ℕ) : 0≤ang nt nf j := by
    have ht := (cappedRepresentative_pos nt).le
    have hf := (cappedRepresentative_pos nf).le
    dsimp [ang]
    positivity
  have hradius (nt nf j : ℕ) :
      (∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalDirectTransportDensity s
        (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>(prefixFlow F.flow T zX t).2)
        (relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j) z
        ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2)
          (relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j) (Icc a b))≤
      ENNReal.ofReal k*ENNReal.ofReal (ang nt nf j) := by
    calc
      _≤∑'nr : ℕ,ENNReal.ofReal ((Cn*I*p*ang nt nf j)*(H*cappedRepresentative nr)) := by
        apply ENNReal.tsum_le_tsum
        intro nr
        have hh := hnear s T F hs hT h0 zX S ![np,nt,nf,nr] j a b I w hS hS0 ha hb hJI hI
        dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
          Matrix.cons_val,Fin.reduceFinMk] at hh
        apply hh.trans_eq
        congr 1
        dsimp [ang,H,p]
        ring
      _=ENNReal.ofReal (2*(Cn*I*p*ang nt nf j)*H) := capped_linear_radius_sum (mul_nonneg (by positivity) (hanga nt nf j)) hH.le
      _=_ := by
        rw [←ENNReal.ofReal_mul hk]
        congr 1
        dsimp [k]
        ring
  calc
    _≤∑'nt : ℕ,∑'nf : ℕ,if cappedRepresentative nf≤16384*cappedRepresentative nt then
        ∑'j : ℕ,ENNReal.ofReal k*ENNReal.ofReal (ang nt nf j) else 0 := by
      apply ENNReal.tsum_le_tsum
      intro nt
      apply ENNReal.tsum_le_tsum
      intro nf
      split_ifs
      · exact ENNReal.tsum_le_tsum (hradius nt nf)
      · rfl
    _=ENNReal.ofReal k*(∑'nt : ℕ,∑'nf : ℕ,if cappedRepresentative nf≤16384*cappedRepresentative nt then
        ∑'j : ℕ,ENNReal.ofReal (ang nt nf j) else 0) := by
      simp_rw [ENNReal.tsum_mul_left]
      have he (nt nf : ℕ) : (if cappedRepresentative nf≤16384*cappedRepresentative nt then
          ENNReal.ofReal k*(∑'j : ℕ,ENNReal.ofReal (ang nt nf j)) else 0)=
          ENNReal.ofReal k*(if cappedRepresentative nf≤16384*cappedRepresentative nt then
          ∑'j : ℕ,ENNReal.ofReal (ang nt nf j) else 0) := by split_ifs <;> simp
      simp_rw [he,ENNReal.tsum_mul_left]
    _≤ENNReal.ofReal k*ENNReal.ofReal 35186519572480 :=
      mul_le_mul' le_rfl remaining_transport_near_angular_expanded
    _=_ := by
      rw [←ENNReal.ofReal_mul hk]
      congr 1
      dsimp [k,p,H]
      ring

lemma Admissible.direct_remaining_transport_uniform_expanded {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀P : ℝ,0≤P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (a b I w : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → b-a≤I → 0<I → I≤1 →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun np nt nf j nr=>relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j
      (∑'np : ℕ,if sourceRepresentative np≤128*P then
        ∑'nt : ℕ,∑'nf : ℕ,if cappedRepresentative nf≤16384*cappedRepresentative nt then
          ∑'j : ℕ,∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V (B np nt nf j nr) z
            ∂physicalBinMeasure V (B np nt nf j nr) (Icc a b) else 0 else 0)≤
      ENNReal.ofReal (C*max 1 T*(P*Real.sqrt I)) := by
  obtain ⟨Cn,hCn,hangular⟩ := hd.direct_remaining_transport_angular_expanded
  refine ⟨256*Cn,by positivity,?_⟩
  intro P hP s T F hs hT h0 zX S a b I w hS hS0 ha hb hJI hI hI1
  dsimp only
  apply le_trans (b:=∑'np : ℕ,if sourceRepresentative np≤128*P then ENNReal.ofReal (Cn*I*max 1 T*sourceRepresentative np) else 0)
  · apply ENNReal.tsum_le_tsum
    intro np
    split_ifs
    · exact hangular s T F hs hT h0 zX S np a b I w hS hS0 ha hb hJI hI
    · rfl
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro U
  let V := U.filter (fun np=>sourceRepresentative np≤128*P)
  have he : (∑np∈U,if sourceRepresentative np≤128*P then ENNReal.ofReal (Cn*I*max 1 T*sourceRepresentative np) else 0)=
      ∑np∈V,ENNReal.ofReal (Cn*I*max 1 T*sourceRepresentative np) := by simp [V,Finset.sum_filter]
  rw [he,←ENNReal.ofReal_sum_of_nonneg (fun np _=>by dsimp [sourceRepresentative]; positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [←Finset.mul_sum]
  have hsum := sourceRepresentative_sum_bound (by positivity : 0≤128*P) V
    (fun np hnp=>(Finset.mem_filter.mp hnp).2)
  have hIsqrt : I≤Real.sqrt I := by
    nlinarith [Real.sq_sqrt hI.le,Real.sqrt_nonneg I,sq_nonneg (Real.sqrt I)]
  calc
    _≤(Cn*I*max 1 T)*(2*(128*P)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _≤(Cn*Real.sqrt I*max 1 T)*(2*(128*P)) := by gcongr
    _=_ := by ring

end RVM

end

end OAI
