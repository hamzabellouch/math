import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.DirectLargeAngularSharp

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma remaining_large_good_receiver_expanded {φ : ℝ} (hφ : 0<φ)
    (Sθ : Finset ℕ) (Sσ : ℕ→Finset ℕ)
    (hθ : ∀i∈Sθ,φ≤16384*cappedRepresentative i)
    (hσ : ∀i∈Sθ,∀j∈Sσ i,cappedRepresentative j≤131080*cappedRepresentative i) :
    (∑i∈Sθ,∑j∈Sσ i,(min (cappedRepresentative i) (cappedRepresentative j))^(3/2:ℝ)*
      (φ/(cappedRepresentative i)^2))≤remainingGoodConstant 131080 16384 0*Real.sqrt φ := by
  have hh := remaining_good_fixed_receiver_sum hφ (by norm_num : (0:ℝ)<131080)
    (by norm_num : (0:ℝ)<16384) (by norm_num : (0:ℝ)≤0) (by norm_num) Sθ Sσ hθ hσ
  simp only [Real.rpow_zero,div_one,add_zero,sub_zero,←Real.sqrt_eq_rpow] at hh
  simp only [remainingGoodConstant, sub_zero, add_zero, ←Real.sqrt_eq_rpow]
  apply le_trans _ hh
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  have hi0 := (cappedRepresentative_pos i).le
  have hj0 := (cappedRepresentative_pos j).le
  have hκ : 1≤(1+φ/cappedRepresentative j)^(1/4:ℝ) :=
    Real.one_le_rpow (by linarith [div_nonneg hφ.le hj0]) (by norm_num)
  rw [mul_comm _ (φ/(cappedRepresentative i)^2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact le_mul_of_one_le_right (by positivity) hκ

lemma remaining_large_good_angles_expanded (Sφ : Finset ℕ) (Sθ : ℕ→Finset ℕ) (Sσ : ℕ→ℕ→Finset ℕ)
    (hθ : ∀nf∈Sφ,∀i∈Sθ nf,cappedRepresentative nf≤16384*cappedRepresentative i)
    (hσ : ∀nf∈Sφ,∀i∈Sθ nf,∀j∈Sσ nf i,cappedRepresentative j≤131080*cappedRepresentative i) :
    (∑nf∈Sφ,∑i∈Sθ nf,∑j∈Sσ nf i,(min (cappedRepresentative i) (cappedRepresentative j))^(3/2:ℝ)*
      (cappedRepresentative nf/(cappedRepresentative i)^2))≤
      remainingGoodConstant 131080 16384 0*directDyadicPowerConstant (1/2) := by
  calc
    _≤∑nf∈Sφ,remainingGoodConstant 131080 16384 0*Real.sqrt (cappedRepresentative nf) :=
      Finset.sum_le_sum (fun nf hnf=>remaining_large_good_receiver_expanded (cappedRepresentative_pos nf)
        (Sθ nf) (Sσ nf) (hθ nf hnf) (hσ nf hnf))
    _≤_ := by
      rw [←Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (remainingGoodConstant_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      have hh := capped_positive_power_sum_unscaled (by norm_num : (0:ℝ)<1)
        (by norm_num : (0:ℝ)<1/2) Sφ (fun n _=>cappedRepresentative_le_one n)
      simpa only [directDyadicPowerConstant,Real.one_rpow,mul_one,←Real.sqrt_eq_rpow,Real.sqrt_one] using hh

lemma remaining_large_magnetic_receiver_expanded {φ : ℝ} (hφ : 0≤φ)
    (Sθ : Finset ℕ) (Sσ : ℕ→Finset ℕ)
    (hσ : ∀i∈Sθ,∀j∈Sσ i,cappedRepresentative j≤131080*cappedRepresentative i) :
    (∑i∈Sθ,∑j∈Sσ i,(min (cappedRepresentative i) (cappedRepresentative j))^(4/3:ℝ)*
      (cappedRepresentative i)^(-(2/3:ℝ))*φ^(1/3:ℝ))≤
      directDyadicPowerConstant (4/3)*(131080:ℝ)^(4/3:ℝ)*directDyadicPowerConstant (2/3)*φ^(1/3:ℝ) := by
  have hh := capped_positive_power_sum_unscaled (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)<2/3) Sθ (fun n _=>cappedRepresentative_le_one n)
  rw [Real.one_rpow,mul_one] at hh
  have hC : 0≤directDyadicPowerConstant (4/3)*(131080:ℝ)^(4/3:ℝ) :=
    mul_nonneg (directDyadicPowerConstant_nonneg (by norm_num)) (by positivity)
  calc
    _≤∑i∈Sθ,directDyadicPowerConstant (4/3)*(131080:ℝ)^(4/3:ℝ)*(cappedRepresentative i)^(2/3:ℝ)*φ^(1/3:ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [one_mul,mul_one,directDyadicPowerConstant] using large_radius_magnetic_relative_sum
        (by norm_num : (0:ℝ)≤1) (cappedRepresentative_pos i) hφ (by norm_num : (0:ℝ)<131080) (Sσ i) (hσ i hi)
    _=(directDyadicPowerConstant (4/3)*(131080:ℝ)^(4/3:ℝ))*(∑i∈Sθ,(cappedRepresentative i)^(2/3:ℝ))*φ^(1/3:ℝ) := by
      simp only [Finset.sum_mul,Finset.mul_sum]
    _≤_ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hC) (Real.rpow_nonneg hφ _)

lemma remaining_large_magnetic_angles_expanded (Sφ : Finset ℕ) (Sθ : ℕ→Finset ℕ) (Sσ : ℕ→ℕ→Finset ℕ)
    (hσ : ∀nf∈Sφ,∀i∈Sθ nf,∀j∈Sσ nf i,cappedRepresentative j≤131080*cappedRepresentative i) :
    (∑nf∈Sφ,∑i∈Sθ nf,∑j∈Sσ nf i,(min (cappedRepresentative i) (cappedRepresentative j))^(4/3:ℝ)*
      (cappedRepresentative i)^(-(2/3:ℝ))*(cappedRepresentative nf)^(1/3:ℝ))≤
      directDyadicPowerConstant (4/3)*(131080:ℝ)^(4/3:ℝ)*directDyadicPowerConstant (2/3)*directDyadicPowerConstant (1/3) := by
  calc
    _≤∑nf∈Sφ,directDyadicPowerConstant (4/3)*(131080:ℝ)^(4/3:ℝ)*directDyadicPowerConstant (2/3)*
        (cappedRepresentative nf)^(1/3:ℝ) :=
      Finset.sum_le_sum (fun nf hnf=>remaining_large_magnetic_receiver_expanded (cappedRepresentative_pos nf).le
        (Sθ nf) (Sσ nf) (hσ nf hnf))
    _≤_ := by
      rw [←Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by
        exact mul_nonneg (mul_nonneg (directDyadicPowerConstant_nonneg (by norm_num)) (by positivity)) (directDyadicPowerConstant_nonneg (by norm_num)))
      have hh := capped_positive_power_sum_unscaled (by norm_num : (0:ℝ)<1)
        (by norm_num : (0:ℝ)<1/3) Sφ (fun n _=>cappedRepresentative_le_one n)
      simpa only [directDyadicPowerConstant,Real.one_rpow,mul_one] using hh

lemma remaining_large_combined_angles_expanded {g b : ℝ} (hg : 0≤g) (hb : 0≤b)
    (Sφ : Finset ℕ) (Sθ : ℕ→Finset ℕ) (Sσ : ℕ→ℕ→Finset ℕ)
    (hθ : ∀nf∈Sφ,∀i∈Sθ nf,cappedRepresentative nf≤16384*cappedRepresentative i)
    (hσ : ∀nf∈Sφ,∀i∈Sθ nf,∀j∈Sσ nf i,cappedRepresentative j≤131080*cappedRepresentative i) :
    (∑nf∈Sφ,∑i∈Sθ nf,∑j∈Sσ nf i,
      (g*(min (cappedRepresentative i) (cappedRepresentative j))^(3/2:ℝ)*
        (cappedRepresentative nf/(cappedRepresentative i)^2)+
       b*(min (cappedRepresentative i) (cappedRepresentative j))^(4/3:ℝ)*
        (cappedRepresentative i)^(-(2/3:ℝ))*(cappedRepresentative nf)^(1/3:ℝ)))≤
      g*(remainingGoodConstant 131080 16384 0*directDyadicPowerConstant (1/2))+
      b*(directDyadicPowerConstant (4/3)*(131080:ℝ)^(4/3:ℝ)*directDyadicPowerConstant (2/3)*directDyadicPowerConstant (1/3)) := by
  have hg' := remaining_large_good_angles_expanded Sφ Sθ Sσ hθ hσ
  have hb' := remaining_large_magnetic_angles_expanded Sφ Sθ Sσ hσ
  simp_rw [mul_assoc, Finset.sum_add_distrib, ←Finset.mul_sum]
  simpa only [mul_assoc] using add_le_add (mul_le_mul_of_nonneg_left hg' hg) (mul_le_mul_of_nonneg_left hb' hb)

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.direct_remaining_source_large_uniform_expanded {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T →
    ∀ (zX : Phase) (S : Set Phase) (a b I w P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → b-a≤I → 0<I → I≤1 → 0≤P →
    ∀ (Sp Sφ : Finset ℕ) (Sθ : ℕ→ℕ→Finset ℕ) (Sσ : ℕ→ℕ→ℕ→Finset ℕ),
      (∀np∈Sp,sourceRepresentative np≤128*P) →
      (∀np∈Sp,∀nf∈Sφ,∀nt∈Sθ np nf,cappedRepresentative nf≤16384*cappedRepresentative nt) →
      (∀np∈Sp,∀nf∈Sφ,∀nt∈Sθ np nf,∀j∈Sσ np nf nt,cappedRepresentative j≤131080*cappedRepresentative nt) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun np nt nf j nr=>relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j
      (∑np∈Sp,∑nf∈Sφ,∑nt∈Sθ np nf,∑j∈Sσ np nf nt,∑'nr : ℕ,
        if I ≤ max 1 T*cappedRepresentative nr then
          ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B np nt nf j nr) z
            ∂physicalBinMeasure V (B np nt nf j nr) (Icc a b) else 0)≤
      ENNReal.ofReal (C*(P*Real.sqrt I)) := by
  obtain ⟨Cg,Cb,hCg,hCb,hbin⟩ := hd.direct_source_large_sharp_sum
  let E := datumEnergyNumber d
  let Kg := relativeCauchyConstant Cg E (20*E)
  let Kb := relativeCauchyConstant Cb E (120*E)
  let Dg := dyadicBalanceConstant (1/2) (1/2)
  let Db := dyadicBalanceConstant 1 (1/2)
  let Ag := remainingGoodConstant 131080 16384 0*directDyadicPowerConstant (1/2)
  let Ab := directDyadicPowerConstant (4/3)*(131080:ℝ)^(4/3:ℝ)*directDyadicPowerConstant (2/3)*directDyadicPowerConstant (1/3)
  have hKg : 0≤Kg := relativeCauchyConstant_nonneg hCg
  have hKb : 0≤Kb := relativeCauchyConstant_nonneg hCb
  have hDg : 0≤Dg := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hDb : 0≤Db := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hAg : 0≤Ag := mul_nonneg
    (remainingGoodConstant_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (directDyadicPowerConstant_nonneg (by norm_num))
  have hAb : 0≤Ab := by
    dsimp [Ab]
    exact mul_nonneg (mul_nonneg (mul_nonneg (directDyadicPowerConstant_nonneg (by norm_num))
      (by positivity)) (directDyadicPowerConstant_nonneg (by norm_num))) (directDyadicPowerConstant_nonneg (by norm_num))
  refine ⟨256*(Kg*Dg*Ag+Kb*Db*Ab),by positivity,?_⟩
  intro s T F hs hT zX S a b I w P hS hS0 ha hb hJI hI hI1 hP Sp Sφ Sθ Sσ hp hθ hσ
  dsimp only
  let g (np : ℕ) := Kg*Dg*(I : ℝ)^(3/4:ℝ)*sourceRepresentative np
  let b' (np : ℕ) := Kb*Real.sqrt I*Db*sourceRepresentative np
  let f (np nf nt j : ℕ) :=
    g np*(min (cappedRepresentative nt) (cappedRepresentative j))^(3/2:ℝ)*
      (cappedRepresentative nf/(cappedRepresentative nt)^2)+
    b' np*(min (cappedRepresentative nt) (cappedRepresentative j))^(4/3:ℝ)*
      (cappedRepresentative nt)^(-(2/3:ℝ))*(cappedRepresentative nf)^(1/3:ℝ)
  have hgn (np : ℕ) : 0≤g np := by dsimp [g,sourceRepresentative]; positivity
  have hbn (np : ℕ) : 0≤b' np := by dsimp [b',sourceRepresentative]; positivity
  have hfn (np nf nt j : ℕ) : 0≤f np nf nt j := by
    have hnt := (cappedRepresentative_pos nt).le
    have hnf := (cappedRepresentative_pos nf).le
    have hj := (cappedRepresentative_pos j).le
    have hg0 := hgn np
    have hb0 := hbn np
    dsimp [f]
    positivity
  calc
    _≤∑np∈Sp,∑nf∈Sφ,∑nt∈Sθ np nf,∑j∈Sσ np nf nt,ENNReal.ofReal (f np nf nt j) := by
      apply Finset.sum_le_sum
      intro np hnp
      apply Finset.sum_le_sum
      intro nf hnf
      apply Finset.sum_le_sum
      intro nt hnt
      apply Finset.sum_le_sum
      intro j hj
      have hh := hbin s T F hs.energyPrefix hT hs.initial_f zX S np nt nf j a b I w hS hS0 ha hb hJI hI
      dsimp only at hh
      rw [hs.initial_energy_eq] at hh
      apply hh.trans_eq
      congr 1
      dsimp [f,g,b',Kg,Kb,Dg,Db,E]
      ring
    _=ENNReal.ofReal (∑np∈Sp,∑nf∈Sφ,∑nt∈Sθ np nf,∑j∈Sσ np nf nt,f np nf nt j) := by
      simp_rw [←ENNReal.ofReal_sum_of_nonneg (fun j _=>hfn _ _ _ j),
        ←ENNReal.ofReal_sum_of_nonneg (fun n _=>Finset.sum_nonneg (fun j _=>hfn _ _ n j)),
        ←ENNReal.ofReal_sum_of_nonneg (fun n _=>Finset.sum_nonneg (fun j _=>Finset.sum_nonneg (fun k _=>hfn _ n j k))),
        ←ENNReal.ofReal_sum_of_nonneg (fun n _=>Finset.sum_nonneg (fun j _=>Finset.sum_nonneg (fun k _=>Finset.sum_nonneg (fun l _=>hfn n j k l))))]
    _≤ENNReal.ofReal (∑np∈Sp,(g np*Ag+b' np*Ab)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Finset.sum_le_sum
      intro np hnp
      exact remaining_large_combined_angles_expanded (hgn np) (hbn np) Sφ (Sθ np) (Sσ np) (hθ np hnp) (hσ np hnp)
    _≤_ := by
      apply ENNReal.ofReal_le_ofReal
      have hsump := sourceRepresentative_sum_bound (by positivity : 0≤128*P) Sp hp
      have hIpow := rpow_three_quarters_le_sqrt hI hI1
      have hs' : ∑np∈Sp,(g np*Ag+b' np*Ab)≤
          (Kg*Dg*Ag+Kb*Db*Ab)*Real.sqrt I*(∑np∈Sp,sourceRepresentative np) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro np hnp
        have hpp : 0 ≤ sourceRepresentative np := by dsimp [sourceRepresentative]; positivity
        dsimp [g,b']
        nlinarith [mul_le_mul_of_nonneg_left hIpow (mul_nonneg (mul_nonneg (mul_nonneg hKg hDg) hAg) hpp)]
      apply hs'.trans
      calc
        _≤(Kg*Dg*Ag+Kb*Db*Ab)*Real.sqrt I*(2*(128*P)) := mul_le_mul_of_nonneg_left hsump (by positivity)
        _=_ := by ring

end RVM

end

end OAI
