import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.SharedBudget

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

def directDyadicPowerConstant (α : ℝ) : ℝ := (1-((2:ℝ)⁻¹)^α)⁻¹

lemma directDyadicPowerConstant_nonneg {α : ℝ} (hα : 0≤α) : 0≤directDyadicPowerConstant α := by
  exact inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_le_one (by norm_num) (by norm_num) hα))

lemma remaining_large_good_receiver {φ : ℝ} (hφ : 0<φ)
    (Sθ : Finset ℕ) (Sσ : ℕ→Finset ℕ)
    (hθ : ∀i∈Sθ,φ≤16*cappedRepresentative i)
    (hσ : ∀i∈Sθ,∀j∈Sσ i,cappedRepresentative j≤136*cappedRepresentative i) :
    (∑i∈Sθ,∑j∈Sσ i,(min (cappedRepresentative i) (cappedRepresentative j))^(3/2:ℝ)*
      (φ/(cappedRepresentative i)^2))≤remainingGoodConstant 136 16 0*Real.sqrt φ := by
  have hh := remaining_good_fixed_receiver_sum hφ (by norm_num : (0:ℝ)<136)
    (by norm_num : (0:ℝ)<16) (by norm_num : (0:ℝ)≤0) (by norm_num) Sθ Sσ hθ hσ
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

lemma remaining_large_good_angles (Sφ : Finset ℕ) (Sθ : ℕ→Finset ℕ) (Sσ : ℕ→ℕ→Finset ℕ)
    (hθ : ∀nf∈Sφ,∀i∈Sθ nf,cappedRepresentative nf≤16*cappedRepresentative i)
    (hσ : ∀nf∈Sφ,∀i∈Sθ nf,∀j∈Sσ nf i,cappedRepresentative j≤136*cappedRepresentative i) :
    (∑nf∈Sφ,∑i∈Sθ nf,∑j∈Sσ nf i,(min (cappedRepresentative i) (cappedRepresentative j))^(3/2:ℝ)*
      (cappedRepresentative nf/(cappedRepresentative i)^2))≤
      remainingGoodConstant 136 16 0*directDyadicPowerConstant (1/2) := by
  calc
    _≤∑nf∈Sφ,remainingGoodConstant 136 16 0*Real.sqrt (cappedRepresentative nf) :=
      Finset.sum_le_sum (fun nf hnf=>remaining_large_good_receiver (cappedRepresentative_pos nf)
        (Sθ nf) (Sσ nf) (hθ nf hnf) (hσ nf hnf))
    _≤_ := by
      rw [←Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (remainingGoodConstant_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      have hh := capped_positive_power_sum_unscaled (by norm_num : (0:ℝ)<1)
        (by norm_num : (0:ℝ)<1/2) Sφ (fun n _=>cappedRepresentative_le_one n)
      simpa only [directDyadicPowerConstant,Real.one_rpow,mul_one,←Real.sqrt_eq_rpow,Real.sqrt_one] using hh

lemma remaining_large_magnetic_receiver {φ : ℝ} (hφ : 0≤φ)
    (Sθ : Finset ℕ) (Sσ : ℕ→Finset ℕ)
    (hσ : ∀i∈Sθ,∀j∈Sσ i,cappedRepresentative j≤136*cappedRepresentative i) :
    (∑i∈Sθ,∑j∈Sσ i,(min (cappedRepresentative i) (cappedRepresentative j))^(4/3:ℝ)*
      (cappedRepresentative i)^(-(2/3:ℝ))*φ^(1/3:ℝ))≤
      directDyadicPowerConstant (4/3)*(136:ℝ)^(4/3:ℝ)*directDyadicPowerConstant (2/3)*φ^(1/3:ℝ) := by
  have hh := capped_positive_power_sum_unscaled (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)<2/3) Sθ (fun n _=>cappedRepresentative_le_one n)
  rw [Real.one_rpow,mul_one] at hh
  have hC : 0≤directDyadicPowerConstant (4/3)*(136:ℝ)^(4/3:ℝ) :=
    mul_nonneg (directDyadicPowerConstant_nonneg (by norm_num)) (by positivity)
  calc
    _≤∑i∈Sθ,directDyadicPowerConstant (4/3)*(136:ℝ)^(4/3:ℝ)*(cappedRepresentative i)^(2/3:ℝ)*φ^(1/3:ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [one_mul,mul_one,directDyadicPowerConstant] using large_radius_magnetic_relative_sum
        (by norm_num : (0:ℝ)≤1) (cappedRepresentative_pos i) hφ (by norm_num : (0:ℝ)<136) (Sσ i) (hσ i hi)
    _=(directDyadicPowerConstant (4/3)*(136:ℝ)^(4/3:ℝ))*(∑i∈Sθ,(cappedRepresentative i)^(2/3:ℝ))*φ^(1/3:ℝ) := by
      simp only [Finset.sum_mul,Finset.mul_sum]
    _≤_ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hC) (Real.rpow_nonneg hφ _)

lemma remaining_large_magnetic_angles (Sφ : Finset ℕ) (Sθ : ℕ→Finset ℕ) (Sσ : ℕ→ℕ→Finset ℕ)
    (hσ : ∀nf∈Sφ,∀i∈Sθ nf,∀j∈Sσ nf i,cappedRepresentative j≤136*cappedRepresentative i) :
    (∑nf∈Sφ,∑i∈Sθ nf,∑j∈Sσ nf i,(min (cappedRepresentative i) (cappedRepresentative j))^(4/3:ℝ)*
      (cappedRepresentative i)^(-(2/3:ℝ))*(cappedRepresentative nf)^(1/3:ℝ))≤
      directDyadicPowerConstant (4/3)*(136:ℝ)^(4/3:ℝ)*directDyadicPowerConstant (2/3)*directDyadicPowerConstant (1/3) := by
  calc
    _≤∑nf∈Sφ,directDyadicPowerConstant (4/3)*(136:ℝ)^(4/3:ℝ)*directDyadicPowerConstant (2/3)*
        (cappedRepresentative nf)^(1/3:ℝ) :=
      Finset.sum_le_sum (fun nf hnf=>remaining_large_magnetic_receiver (cappedRepresentative_pos nf).le
        (Sθ nf) (Sσ nf) (hσ nf hnf))
    _≤_ := by
      rw [←Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by
        exact mul_nonneg (mul_nonneg (directDyadicPowerConstant_nonneg (by norm_num)) (by positivity)) (directDyadicPowerConstant_nonneg (by norm_num)))
      have hh := capped_positive_power_sum_unscaled (by norm_num : (0:ℝ)<1)
        (by norm_num : (0:ℝ)<1/3) Sφ (fun n _=>cappedRepresentative_le_one n)
      simpa only [directDyadicPowerConstant,Real.one_rpow,mul_one] using hh

lemma remaining_large_combined_angles {g b : ℝ} (hg : 0≤g) (hb : 0≤b)
    (Sφ : Finset ℕ) (Sθ : ℕ→Finset ℕ) (Sσ : ℕ→ℕ→Finset ℕ)
    (hθ : ∀nf∈Sφ,∀i∈Sθ nf,cappedRepresentative nf≤16*cappedRepresentative i)
    (hσ : ∀nf∈Sφ,∀i∈Sθ nf,∀j∈Sσ nf i,cappedRepresentative j≤136*cappedRepresentative i) :
    (∑nf∈Sφ,∑i∈Sθ nf,∑j∈Sσ nf i,
      (g*(min (cappedRepresentative i) (cappedRepresentative j))^(3/2:ℝ)*
        (cappedRepresentative nf/(cappedRepresentative i)^2)+
       b*(min (cappedRepresentative i) (cappedRepresentative j))^(4/3:ℝ)*
        (cappedRepresentative i)^(-(2/3:ℝ))*(cappedRepresentative nf)^(1/3:ℝ)))≤
      g*(remainingGoodConstant 136 16 0*directDyadicPowerConstant (1/2))+
      b*(directDyadicPowerConstant (4/3)*(136:ℝ)^(4/3:ℝ)*directDyadicPowerConstant (2/3)*directDyadicPowerConstant (1/3)) := by
  have hg' := remaining_large_good_angles Sφ Sθ Sσ hθ hσ
  have hb' := remaining_large_magnetic_angles Sφ Sθ Sσ hσ
  simp_rw [mul_assoc, Finset.sum_add_distrib, ←Finset.mul_sum]
  simpa only [mul_assoc] using add_le_add (mul_le_mul_of_nonneg_left hg' hg) (mul_le_mul_of_nonneg_left hb' hb)

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma capped_large_magnetic_sharp_ennreal_sum {H p θ φ σ K : ℝ}
    (hH : 0<H) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ) (hσ : 0<σ) (hK : 0≤K) :
    (∑'n : ℕ,ENNReal.ofReal (K*min
      (H*cappedRepresentative n*p^2*(min θ σ)^2*φ)
      (Real.sqrt p*(min θ σ)/(θ*Real.sqrt (H*cappedRepresentative n)))))≤
      ENNReal.ofReal (K*dyadicBalanceConstant 1 (1/2)*
        (p*(min θ σ)^(4/3:ℝ)*θ^(-(2/3:ℝ))*φ^(1/3:ℝ))) := by
  let g : ℤ→ℝ := fun k=>min (H*(2:ℝ)^k*p^2*(min θ σ)^2*φ)
    (Real.sqrt p*(min θ σ)/(θ*Real.sqrt (H*(2:ℝ)^k)))
  have hν : 0 < min θ σ := lt_min hθ hσ
  have hg0 (k : ℤ) : 0≤g k := by dsimp [g]; positivity
  have hg := large_radius_magnetic_balance hH hp hθ hφ hσ
  have he (n : ℕ) : cappedRepresentative n=(2:ℝ)^(-(n:ℤ)) := by
    simp only [cappedRepresentative,zpow_neg,zpow_natCast,inv_pow]
  have hinj : Function.Injective (fun n : ℕ=>-(n:ℤ)) := by
    intro a b hab
    exact_mod_cast neg_injective hab
  calc
    _=∑'n : ℕ,ENNReal.ofReal (K*g (-(n:ℤ))) := by simp_rw [he]; rfl
    _≤∑'k : ℤ,ENNReal.ofReal (K*g k) :=
      ENNReal.tsum_comp_le_tsum_of_injective hinj (fun k=>ENNReal.ofReal (K*g k))
    _=ENNReal.ofReal (K*∑'k : ℤ,g k) := by
      rw [←ENNReal.ofReal_tsum_of_nonneg (fun k=>mul_nonneg hK (hg0 k)) (hg.1.mul_left K),tsum_mul_left]
    _≤_ := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [g,mul_assoc] using mul_le_mul_of_nonneg_left hg.2 hK

lemma direct_large_good_balance {I p θ φ σ : ℝ}
    (hI : 0<I) (hp : 0≤p) (hθ : 0<θ) (hφ : 0<φ) (hσ : 0≤σ) :
    Real.sqrt ((I*p^2*(min θ σ)^2*φ^2/θ^2)*(Real.sqrt I*(min θ σ)/θ^2))=
      (I : ℝ)^(3/4:ℝ)*p*(min θ σ)^(3/2:ℝ)*(φ/θ^2) := by
  simpa only [Real.sqrt_one,Real.one_rpow,mul_one] using
    relative_source_good_balance_factor hI hp (le_min hθ.le hσ)
      (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)≤1) hφ hθ

lemma Admissible.direct_source_large_sharp_sum {d : Datum} (hd : Admissible d) :
    ∃Cg Cb : ℝ,0≤Cg ∧ 0≤Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nt nf j : ℕ) (a b I w : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → b-a≤I → 0<I →
      let p := sourceRepresentative np
      let θ := cappedRepresentative nt
      let φ := cappedRepresentative nf
      let σ := cappedRepresentative j
      let ν := min θ σ
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Kg := relativeCauchyConstant Cg E (20*E)
      let Kb := relativeCauchyConstant Cb E (120*E)
      (∑'nr : ℕ,if I ≤ max 1 T*cappedRepresentative nr then
        ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
          ∂physicalBinMeasure V (B nr) (Icc a b) else 0)≤
      ENNReal.ofReal (Kg*dyadicBalanceConstant (1/2) (1/2)*
        ((I : ℝ)^(3/4:ℝ)*p*ν^(3/2:ℝ)*(φ/θ^2))+
        Kb*Real.sqrt I*dyadicBalanceConstant 1 (1/2)*
          (p*ν^(4/3:ℝ)*θ^(-(2/3:ℝ))*φ^(1/3:ℝ))) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd.direct_source_large_radius
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S np nt nf j a b I w hS hS0 ha hb hJI hI
  dsimp only
  let p := sourceRepresentative np
  let θ := cappedRepresentative nt
  let φ := cappedRepresentative nf
  let σ := cappedRepresentative j
  let ν := min θ σ
  let E := ∫x : Vec,totalEnergy s (0,x)
  let Kg := relativeCauchyConstant Cg E (20*E)
  let Kb := relativeCauchyConstant Cb E (120*E)
  let ag := I*p^2*ν^2*φ^2/θ^2
  let bg := Real.sqrt I*ν/θ^2
  let G := fun n=>ENNReal.ofReal (Kg*min (ag*Real.sqrt (max 1 T*cappedRepresentative n))
    (bg/Real.sqrt (max 1 T*cappedRepresentative n)))
  let Bm := fun n=>ENNReal.ofReal (Kb*Real.sqrt I*min
    (max 1 T*cappedRepresentative n*p^2*ν^2*φ)
    (Real.sqrt p*ν/(θ*Real.sqrt (max 1 T*cappedRepresentative n))))
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hσ : 0<σ := cappedRepresentative_pos _
  have hν : 0<ν := lt_min hθ hσ
  have hKg : 0≤Kg := relativeCauchyConstant_nonneg hCg
  have hKb : 0≤Kb := relativeCauchyConstant_nonneg hCb
  have hH : 0 < max 1 T := zero_lt_one.trans_le (le_max_left _ _)
  have hg := capped_sqrt_radius_ennreal_sum (show 0≤ag by dsimp [ag]; positivity)
    (show 0≤bg by dsimp [bg]; positivity) hH hKg
  have hm := capped_large_magnetic_sharp_ennreal_sum hH hp hθ hφ hσ
    (mul_nonneg hKb (Real.sqrt_nonneg I))
  have he : Real.sqrt (ag*bg)=(I : ℝ)^(3/4:ℝ)*p*ν^(3/2:ℝ)*(φ/θ^2) :=
    direct_large_good_balance hI hp.le hθ hφ hσ.le
  rw [he] at hg
  have hDs : 0≤dyadicBalanceConstant (1/2) (1/2) :=
    (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hDm : 0≤dyadicBalanceConstant 1 (1/2) :=
    (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  calc
    _≤∑'n : ℕ,(G n+Bm n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      split_ifs with hIr
      · have h := hsource s T F hs hT h0 zX S ![np,nt,nf,n] j a b I w hS hS0 ha hb hJI hI hIr
        dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Matrix.cons_val,Fin.reduceFinMk] at h
        have hrad : 0 < max 1 T*cappedRepresentative n := mul_pos hH (cappedRepresentative_pos _)
        refine h.trans_eq ?_
        exact ENNReal.ofReal_add
          (mul_nonneg hKg (by positivity))
          (mul_nonneg (mul_nonneg hKb (Real.sqrt_nonneg I)) (le_min (by positivity) (by positivity)))
      · exact bot_le
    _=(∑'n : ℕ,G n)+(∑'n : ℕ,Bm n) := ENNReal.tsum_add
    _≤_ := by
      have hh := add_le_add hg hm
      rw [←ENNReal.ofReal_add (by positivity) (by positivity)] at hh
      exact hh

end RVM

end

end OAI
