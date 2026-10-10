import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.ExpectedRadialCapBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SharpErrorLimit_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis CoulombNeumann

lemma patch_power_ratio {a : ℝ} (ha : 0 < a) (p w : ℝ) :
    (a^p/(a^(1/5:ℝ))^2)/a^w = a^(p-2/5-w) := by
  rw [←Real.rpow_mul_natCast ha.le,←Real.rpow_sub ha,←Real.rpow_sub ha]
  norm_num

lemma patch_sqrt_ratio {a : ℝ} (ha : 0 < a) (w : ℝ) :
    Real.sqrt (8*a^(1/5:ℝ))/a^w = Real.sqrt 8*a^(1/10-w) := by
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 8),Real.sqrt_eq_rpow (a^(1/5:ℝ)),
    ←Real.rpow_mul ha.le]
  norm_num
  rw [mul_div_assoc,←Real.rpow_sub ha]

 def weightedDimensionlessPatch (a M w : ℝ) : ℝ :=
    a^(8/5-w)*localizationIMSConstant*(Real.sqrt (8*a^(1/5:ℝ))*actualCellMomentConstant*M)+
    a^(3/5-w)*neumannRemainderConstant*actualCellMomentConstant^(2/3:ℝ)*M^(4/3:ℝ)+
    a^(8/5-w)*neumannRemainderConstant*actualCellMomentConstant*M+
    a^(14/5-w)*((2*Real.pi+1)/2)*actualCellMomentConstant*M+
    sharpFreshFieldConstant*(Real.sqrt 8*a^(1/10-w))*actualCellMomentConstant*M^2+
    a^(8/5-w)*(packetDirichlet canonicalRealPacket/2)*768*sharpFreshFieldConstant*M

lemma dimensionlessPatchRemainder_weight {a : ℝ} (ha : 0 < a) (M w : ℝ) :
    dimensionlessPatchRemainder a (a^(1/5:ℝ)) M/a^w = weightedDimensionlessPatch a M w := by
  have h2 : (a^2/(a^(1/5:ℝ))^2)/a^w = a^(8/5-w) := by
    convert patch_power_ratio ha 2 w using 1 <;> norm_num
  have h1 : (a/(a^(1/5:ℝ))^2)/a^w = a^(3/5-w) := by
    convert patch_power_ratio ha 1 w using 1 <;> norm_num
  have h3 : (a^3/a^(1/5:ℝ))/a^w = a^(14/5-w) := by
    rw [←Real.rpow_natCast,←Real.rpow_sub ha,←Real.rpow_sub ha]
    norm_num
  have hr := patch_sqrt_ratio ha w
  unfold dimensionlessPatchRemainder weightedDimensionlessPatch
  rw [←h2,←h1,←h3,←hr]
  ring

theorem dimensionlessPatchRemainder_div_tendsto {ι : Type*} {l : Filter ι}
    {a M : ι → ℝ} {M₀ w : ℝ} (ha : ∀ᶠ i in l, 0 < a i)
    (ha0 : Tendsto a l (𝓝 0)) (hM : Tendsto M l (𝓝 M₀)) (hw : w < 1/10) :
    Tendsto (fun i => dimensionlessPatchRemainder (a i) ((a i)^(1/5:ℝ)) (M i)/(a i)^w)
      l (𝓝 0) := by
  have hpow (p : ℝ) (hp : 0 < p) := ha0.rpow_const_nhds_zero hp
  have hs : Tendsto (fun i => Real.sqrt (8*(a i)^(1/5:ℝ))) l (𝓝 0) := by
    simpa using ((hpow (1/5) (by norm_num)).const_mul 8).sqrt
  have h1 := ((hpow (8/5-w) (by linarith)).mul_const localizationIMSConstant).mul
    ((hs.mul_const actualCellMomentConstant).mul hM)
  have h2 := (((hpow (3/5-w) (by linarith)).mul_const neumannRemainderConstant).mul_const
    ((actualCellMomentConstant)^(2/3:ℝ))).mul (hM.rpow_const (Or.inr (by norm_num : (0:ℝ) ≤ 4/3)))
  have h3 := (((hpow (8/5-w) (by linarith)).mul_const neumannRemainderConstant).mul_const
    actualCellMomentConstant).mul hM
  have h4 := (((hpow (14/5-w) (by linarith)).mul_const ((2*Real.pi+1)/2)).mul_const
    actualCellMomentConstant).mul hM
  have h5 := ((((hpow (1/10-w) (by linarith)).const_mul (Real.sqrt 8)).const_mul
    sharpFreshFieldConstant).mul_const actualCellMomentConstant).mul (hM.pow 2)
  have h6 := ((((hpow (8/5-w) (by linarith)).mul_const (packetDirichlet canonicalRealPacket/2)).mul_const
    768).mul_const sharpFreshFieldConstant).mul hM
  have hh : Tendsto (fun i => weightedDimensionlessPatch (a i) (M i) w) l (𝓝 0) := by
    simpa only [weightedDimensionlessPatch,zero_mul,mul_zero,add_zero] using
      ((((h1.add h2).add h3).add h4).add h5).add h6
  apply hh.congr'
  filter_upwards [ha] with i hi
  exact (dimensionlessPatchRemainder_weight hi (M i) w).symm

lemma dimensionlessLocalPotential_tendsto {ι : Type*} {l : Filter ι}
    {M u : ι → ℝ} {M₀ : ℝ} (hM : Tendsto M l (𝓝 M₀)) (hu : Tendsto u l (𝓝 0)) :
    Tendsto (fun i => dimensionlessLocalPotential (M i) (u i)) l (𝓝 0) := by
  have h1 := ((hM.pow 2).const_mul sharpOrdinaryDensityConstant).rpow_const
    (Or.inr (by norm_num : (0:ℝ) ≤ 3/5))
  have h2 := hu.rpow_const_nhds_zero (by norm_num : (0:ℝ) < 1/5)
  simpa only [dimensionlessLocalPotential,mul_zero] using
    (h1.mul_const ((8*Real.pi)^(2/5:ℝ))).mul h2

theorem dimensionlessPotentialRemainder_tendsto {ι : Type*} {l : Filter ι}
    {a M E : ι → ℝ} {M₀ w : ℝ} (ha : ∀ᶠ i in l, 0 < a i)
    (ha0 : Tendsto a l (𝓝 0)) (hM : Tendsto M l (𝓝 M₀)) (hw : 0 < w) (hw' : w < 1/10)
    (hE : Tendsto (fun i => E i/(a i)^w) l (𝓝 0)) :
    Tendsto (fun i => dimensionlessPotentialRemainder (a i) ((a i)^(1/5:ℝ)) (M i) (E i) ((a i)^w))
      l (𝓝 0) := by
  have hR := dimensionlessPatchRemainder_div_tendsto ha ha0 hM hw'
  have hτ := ha0.rpow_const_nhds_zero hw
  have hβ := ha0.rpow_const_nhds_zero (by norm_num : (0:ℝ) < 1/5)
  have hroot : Tendsto (fun i => Real.sqrt ((2/(a i)^w)*
      (E i+dimensionlessPatchRemainder (a i) ((a i)^(1/5:ℝ)) (M i)))) l (𝓝 0) := by
    have ht := ((hE.add hR).const_mul 2).sqrt
    convert ht using 1
    · funext i
      congr 1
      ring
    · simp
  have hu1 : Tendsto (fun i => (a i)^w+Real.sqrt 3*(a i)^(1/5:ℝ)) l (𝓝 0) := by
    simpa using hτ.add (hβ.const_mul (Real.sqrt 3))
  have hu2 : Tendsto (fun i => Real.sqrt 3*(a i)^(1/5:ℝ)) l (𝓝 0) := by
    simpa using hβ.const_mul (Real.sqrt 3)
  have hcap := (hτ.pow 2).const_mul (2*Real.pi*tfPatchDensityCapConstant)
  have hdel := (((hβ.const_mul 8).sqrt).mul_const actualCellMomentConstant).mul hM
  simpa only [dimensionlessPotentialRemainder,zero_mul,mul_zero,zero_pow (by decide : 2 ≠ 0),
    Real.sqrt_zero,add_zero] using
    (((hroot.add (dimensionlessLocalPotential_tendsto hM hu1)).add hcap).add
      (dimensionlessLocalPotential_tendsto hM hu2)).add hdel

end Work_SharpErrorLimit_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis

lemma microscopicWidth_eq {a : ℝ} (ha : 0 < a) :
    a*a^(1/5:ℝ) = a^(6/5:ℝ) := by
  calc _ = a^(1:ℝ)*a^(1/5:ℝ) := by rw [Real.rpow_one]
       _ = _ := by rw [←Real.rpow_add ha]; norm_num

lemma microscopic_collar {a m : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hm : 1/a^3 ≤ m) : a ≤ (a*a^(1/5:ℝ))^2*m := by
  have hβ : a ≤ a^(1/5:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ha ha1 (by norm_num : (1/5:ℝ) ≤ 1)
  have hb : a^2 ≤ a*a^(1/5:ℝ) := by nlinarith
  have hm0 : 0 ≤ m := le_trans (by positivity) hm
  have hsq : a^4 ≤ (a*a^(1/5:ℝ))^2 := by nlinarith [sq_nonneg (a*a^(1/5:ℝ)-a^2)]
  calc a = a^4*(1/a^3) := by field_simp
       _ ≤ a^4*m := mul_le_mul_of_nonneg_left hm (by positivity)
       _ ≤ (a*a^(1/5:ℝ))^2*m := mul_le_mul_of_nonneg_right hsq hm0

lemma normalized_excess_ratio {a D w : ℝ} (ha : 0 < a) :
    (D*a^7)/a^w = D*a^(7-w) := by
  rw [mul_div_assoc,←Real.rpow_natCast,←Real.rpow_sub ha]
  norm_num

theorem physical_local_mass_tendsto {ι : Type*} {l : Filter ι}
    {y : ι → Space} {D : ι → ℝ} {w : ℝ}
    (hy : ∀ᶠ i in l, y i ≠ 0) (hy0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hw : 0 < w)
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-w)) l (𝓝 0)) :
    Tendsto (fun i => (localCellRadius (y i))^3*localOffsetMass (D i) (y i)) l (𝓝 1) := by
  let a := fun i => localCellRadius (y i)
  have hp : Tendsto (fun i => (a i)^w) l (𝓝 0) := hy0.rpow_const_nhds_zero hw
  have hE : Tendsto (fun i => D i*(a i)^7) l (𝓝 0) := by
    have ht := hD.mul hp
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [hy] with i hi
    have ha := localCellRadius_pos hi
    change D i*(a i)^(7-w)*(a i)^w = D i*(a i)^7
    rw [mul_assoc,←Real.rpow_add ha]
    norm_num [a]
  have ht : Tendsto (fun i => 1+Real.sqrt (D i*(a i)^7)) l (𝓝 1) := by
    simpa using hE.sqrt.const_add 1
  apply ht.congr'
  filter_upwards [hy,hy0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hi ha1
  exact (localOffsetMass_rescale hi ha1.le).symm

theorem physical_potential_error_tendsto {ι : Type*} {l : Filter ι}
    {y : ι → Space} {D : ι → ℝ} {w : ℝ}
    (hy : ∀ᶠ i in l, y i ≠ 0) (hy0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hw : 0 < w) (hw' : w < 1/10)
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-w)) l (𝓝 0)) :
    Tendsto (fun i => (localCellRadius (y i))^4*
      sharpPotentialRemainder (localCellRadius (y i))
        ((localCellRadius (y i))^(6/5:ℝ)) (localOffsetMass (D i) (y i)) (D i)
        ((localCellRadius (y i))*(localCellRadius (y i))^w)) l (𝓝 0) := by
  let a := fun i => localCellRadius (y i)
  let M := fun i => (a i)^3*localOffsetMass (D i) (y i)
  let E := fun i => D i*(a i)^7
  have ha : ∀ᶠ i in l, 0 < a i := hy.mono (fun i hi => localCellRadius_pos hi)
  have hM : Tendsto M l (𝓝 1) := physical_local_mass_tendsto hy hy0 hw hD
  have hE : Tendsto (fun i => E i/(a i)^w) l (𝓝 0) := by
    apply hD.congr'
    filter_upwards [ha] with i hi
    exact (normalized_excess_ratio hi).symm
  have ht := dimensionlessPotentialRemainder_tendsto ha hy0 hM hw hw' hE
  apply ht.congr'
  filter_upwards [ha] with i hi
  have hMi : 0 ≤ M i := mul_nonneg (pow_nonneg hi.le _) (le_trans zero_le_one (localOffsetMass_one_le _ _))
  have he := sharpPotentialRemainder_rescale (E := E i) hi (Real.rpow_pos_of_pos hi (1/5:ℝ)) hMi (Real.rpow_pos_of_pos hi w)
  have hmass : M i/(a i)^3 = localOffsetMass (D i) (y i) := by dsimp [M]; field_simp
  have henergy : E i/(a i)^7 = D i := by dsimp [E]; field_simp
  rw [hmass,henergy,microscopicWidth_eq hi] at he
  exact he.symm

theorem physical_patch_error_tendsto {ι : Type*} {l : Filter ι}
    {y : ι → Space} {D : ι → ℝ} {w : ℝ}
    (hy : ∀ᶠ i in l, y i ≠ 0) (hy0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hw : 0 < w) (hw' : w < 1/10)
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-w)) l (𝓝 0)) :
    Tendsto (fun i => (D i+sharpPatchRemainder (localCellRadius (y i))
      ((localCellRadius (y i))^(6/5:ℝ)) (localOffsetMass (D i) (y i)))*
        (localCellRadius (y i))^(7-w)) l (𝓝 0) := by
  let a := fun i => localCellRadius (y i)
  let M := fun i => (a i)^3*localOffsetMass (D i) (y i)
  have ha : ∀ᶠ i in l, 0 < a i := hy.mono (fun i hi => localCellRadius_pos hi)
  have hM : Tendsto M l (𝓝 1) := physical_local_mass_tendsto hy hy0 hw hD
  have ht := hD.add (dimensionlessPatchRemainder_div_tendsto ha hy0 hM hw')
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [ha] with i hi
  have hMi : 0 ≤ M i := mul_nonneg (pow_nonneg hi.le _) (le_trans zero_le_one (localOffsetMass_one_le _ _))
  have he := sharpPatchRemainder_rescale hi (Real.rpow_pos_of_pos hi (1/5:ℝ)) hMi
  have hmass : M i/(a i)^3 = localOffsetMass (D i) (y i) := by dsimp [M]; field_simp
  rw [hmass,microscopicWidth_eq hi] at he
  rw [←he,add_mul]
  congr 1
  rw [mul_comm ((a i)^7),normalized_excess_ratio hi]

theorem physical_master_error_tendsto {ι : Type*} {l : Filter ι}
    {y : ι → Space} {D u : ι → ℝ} {w : ℝ}
    (hy : ∀ᶠ i in l, y i ≠ 0) (hy0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hw : 0 < w)
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-w)) l (𝓝 0))
    (hu : ∀ᶠ i in l, 0 ≤ u i) (hu0 : Tendsto u l (𝓝 0)) :
    Tendsto (fun i => (localCellRadius (y i))^4*sharpLocalPotentialBudget
      (localCellRadius (y i)) (localOffsetMass (D i) (y i))
      ((localCellRadius (y i))*u i)) l (𝓝 0) := by
  let M := fun i => (localCellRadius (y i))^3*localOffsetMass (D i) (y i)
  have hM : Tendsto M l (𝓝 1) := physical_local_mass_tendsto hy hy0 hw hD
  have ht := dimensionlessLocalPotential_tendsto hM hu0
  apply ht.congr'
  filter_upwards [hy,hu] with i hi hui
  have ha := localCellRadius_pos hi
  have he := sharpLocalPotentialBudget_rescale (M := M i) ha hui
  have hm : M i/(localCellRadius (y i))^3 = localOffsetMass (D i) (y i) := by dsimp [M]; field_simp
  rw [hm] at he
  exact he.symm

end CoulombAtom

end

end OAI
