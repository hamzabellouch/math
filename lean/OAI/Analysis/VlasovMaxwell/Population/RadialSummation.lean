import Mathlib
import OAI.Analysis.VlasovMaxwell.LocalPDE.RelativeCauchyConstant

namespace OAI

noncomputable section

namespace RVM

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


lemma capped_positive_power_sum_unscaled {x α : ℝ} (hx : 0<x) (hα : 0<α)
    (S : Finset ℕ) (hS : ∀j∈S,cappedRepresentative j≤x) :
    ∑j∈S,(cappedRepresentative j)^α≤(1-((2:ℝ)⁻¹)^α)⁻¹*x^α := by
  have hh := capped_positive_power_sum hx hα S hS
  have he (j : ℕ) : (cappedRepresentative j/x)^α=(cappedRepresentative j)^α/x^α :=
    Real.div_rpow (cappedRepresentative_pos j).le hx.le α
  simp_rw [he] at hh
  rw [←Finset.sum_div] at hh
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hx α)).mp hh

lemma large_radius_magnetic_relative_sum {p θ φ K : ℝ}
    (hp : 0≤p) (hθ : 0<θ) (hφ : 0≤φ) (hK : 0<K)
    (S : Finset ℕ) (hS : ∀j∈S,cappedRepresentative j≤K*θ) :
    ∑j∈S,p*(min θ (cappedRepresentative j))^(4/3:ℝ)*θ^(-(2/3:ℝ))*φ^(1/3:ℝ)≤
      (1-((2:ℝ)⁻¹)^(4/3:ℝ))⁻¹*K^(4/3:ℝ)*p*θ^(2/3:ℝ)*φ^(1/3:ℝ) := by
  have hsum := capped_positive_power_sum_unscaled (mul_pos hK hθ) (by norm_num : (0:ℝ)<4/3) S hS
  have he : (K*θ)^(4/3:ℝ)*θ^(-(2/3:ℝ))=K^(4/3:ℝ)*θ^(2/3:ℝ) := by
    rw [Real.mul_rpow hK.le hθ.le,mul_assoc,←Real.rpow_add hθ]
    congr 2
    norm_num
  calc
    _ ≤ ∑j∈S,p*(cappedRepresentative j)^(4/3:ℝ)*θ^(-(2/3:ℝ))*φ^(1/3:ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hm := Real.rpow_le_rpow (le_min hθ.le (cappedRepresentative_pos j).le)
        (min_le_right θ (cappedRepresentative j)) (by norm_num : (0:ℝ)≤4/3)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hp)
          (Real.rpow_nonneg hθ.le _)) (Real.rpow_nonneg hφ _)
    _ = p*(∑j∈S,(cappedRepresentative j)^(4/3:ℝ))*θ^(-(2/3:ℝ))*φ^(1/3:ℝ) := by
      simp only [Finset.sum_mul,Finset.mul_sum]
    _ ≤ p*((1-((2:ℝ)⁻¹)^(4/3:ℝ))⁻¹*(K*θ)^(4/3:ℝ))*θ^(-(2/3:ℝ))*φ^(1/3:ℝ) := by
      gcongr
    _ = _ := by
      calc
        _ = (1-((2:ℝ)⁻¹)^(4/3:ℝ))⁻¹*p*((K*θ)^(4/3:ℝ)*θ^(-(2/3:ℝ)))*φ^(1/3:ℝ) := by ring
        _ = _ := by rw [he]; ring

lemma large_radius_magnetic_angular_sum {p K : ℝ} (hp : 0≤p) (hK : 0<K)
    (Sθ Sφ : Finset ℕ) (Sσ : ℕ→ℕ→Finset ℕ)
    (hS : ∀i∈Sθ,∀k∈Sφ,∀j∈Sσ i k,cappedRepresentative j≤K*cappedRepresentative i) :
    ∑i∈Sθ,∑k∈Sφ,∑j∈Sσ i k,
      p*(min (cappedRepresentative i) (cappedRepresentative j))^(4/3:ℝ)*
        (cappedRepresentative i)^(-(2/3:ℝ))*(cappedRepresentative k)^(1/3:ℝ)≤
    ((1-((2:ℝ)⁻¹)^(4/3:ℝ))⁻¹*K^(4/3:ℝ)*
      (1-((2:ℝ)⁻¹)^(2/3:ℝ))⁻¹*(1-((2:ℝ)⁻¹)^(1/3:ℝ))⁻¹)*p := by
  let C := (1-((2:ℝ)⁻¹)^(4/3:ℝ))⁻¹*K^(4/3:ℝ)
  have hC : 0≤C := by
    dsimp only [C]
    apply mul_nonneg
    · apply inv_nonneg.mpr
      exact sub_nonneg.mpr (Real.rpow_le_one (by norm_num) (by norm_num) (by norm_num))
    · positivity
  have hθsum := capped_positive_power_sum_unscaled (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)<2/3) Sθ (fun _ _=>cappedRepresentative_le_one _)
  have hφsum := capped_positive_power_sum_unscaled (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)<1/3) Sφ (fun _ _=>cappedRepresentative_le_one _)
  rw [Real.one_rpow,mul_one] at hθsum hφsum
  have hφ0 : 0≤∑k∈Sφ,(cappedRepresentative k)^(1/3:ℝ) :=
    Finset.sum_nonneg (fun _ _=>Real.rpow_nonneg (cappedRepresentative_pos _).le _)
  have hden : 0≤(1-((2:ℝ)⁻¹)^(2/3:ℝ))⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_le_one (by norm_num) (by norm_num) (by norm_num)))
  calc
    _ ≤ ∑i∈Sθ,∑k∈Sφ,C*p*(cappedRepresentative i)^(2/3:ℝ)*(cappedRepresentative k)^(1/3:ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro k hk
      exact large_radius_magnetic_relative_sum hp (cappedRepresentative_pos i)
        (cappedRepresentative_pos k).le hK (Sσ i k) (hS i hi k hk)
    _ = C*p*(∑i∈Sθ,(cappedRepresentative i)^(2/3:ℝ))*(∑k∈Sφ,(cappedRepresentative k)^(1/3:ℝ)) := by
      simp_rw [←Finset.mul_sum]
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ C*p*((1-((2:ℝ)⁻¹)^(2/3:ℝ))⁻¹)*((1-((2:ℝ)⁻¹)^(1/3:ℝ))⁻¹) := by
      gcongr
    _ = _ := by dsimp only [C]; ring

lemma physical_relative_remaining_upper {T w t r κ : ℝ} {V : ℝ→Vec} {J : Set ℝ}
    {k : Fin 4→ℕ} {j : ℕ} {n : Sphere} {v : Vec}
    (hκ : 0≤κ) (hsector : cappedRepresentative (k 2)≤κ*cappedRepresentative (k 1))
    (hb : (t,r,n)∈physicalBinBase V (relativeRepresentativeClosedBin T w k j) J)
    (hv : v∈coneBinMomentumSet (relativeRepresentativeClosedBin T w k j) n.1 (velocity (V t))) :
    cappedRepresentative j≤8*(1+κ)*cappedRepresentative (k 1) := by
  exact cone_relative_bin_upper (v:=v) (w:=V t) (n:=n.1) (sphere_norm n)
    (cappedRepresentative_pos (k 1)).le (cappedRepresentative_pos (k 2)).le
    (cappedRepresentative_pos j).le hκ hsector hv.2.1.1 hv.2.1.2
    hb.2.2.2.2.1 hb.2.2.2.2.2 hv.2.2.1 hv.2.2.2

lemma large_radius_magnetic_full_sum {p K H : ℝ} (hp : 0<p) (hK : 0<K) (hH : 0<H)
    (Sθ Sφ : Finset ℕ) (Sσ : ℕ→ℕ→Finset ℕ) (Sr : ℕ→ℕ→ℕ→Finset ℤ)
    (hS : ∀i∈Sθ,∀k∈Sφ,∀j∈Sσ i k,cappedRepresentative j≤K*cappedRepresentative i) :
    (∑i∈Sθ,∑k∈Sφ,∑j∈Sσ i k,∑r∈Sr i k j,
      min (H*(2:ℝ)^r*p^2*(min (cappedRepresentative i) (cappedRepresentative j))^2*cappedRepresentative k)
        (Real.sqrt p*(min (cappedRepresentative i) (cappedRepresentative j))/
          (cappedRepresentative i*Real.sqrt (H*(2:ℝ)^r))))≤
    dyadicBalanceConstant 1 (1/2)*
      (((1-((2:ℝ)⁻¹)^(4/3:ℝ))⁻¹*K^(4/3:ℝ)*
        (1-((2:ℝ)⁻¹)^(2/3:ℝ))⁻¹*(1-((2:ℝ)⁻¹)^(1/3:ℝ))⁻¹)*p) := by
  have hpoint (i k j : ℕ) : (∑r∈Sr i k j,
      min (H*(2:ℝ)^r*p^2*(min (cappedRepresentative i) (cappedRepresentative j))^2*cappedRepresentative k)
        (Real.sqrt p*(min (cappedRepresentative i) (cappedRepresentative j))/
          (cappedRepresentative i*Real.sqrt (H*(2:ℝ)^r))))≤
      dyadicBalanceConstant 1 (1/2)*(p*(min (cappedRepresentative i) (cappedRepresentative j))^(4/3:ℝ)*
        (cappedRepresentative i)^(-(2/3:ℝ))*(cappedRepresentative k)^(1/3:ℝ)) := by
    obtain ⟨hs,hb⟩ := large_radius_magnetic_balance hH hp (cappedRepresentative_pos i)
      (cappedRepresentative_pos k) (cappedRepresentative_pos j)
    apply le_trans (hs.sum_le_tsum (Sr i k j) (fun r _=>?_)) hb
    have hk0 := (cappedRepresentative_pos k).le
    exact le_min (by positivity)
      (div_nonneg (mul_nonneg (Real.sqrt_nonneg _)
        (le_min (cappedRepresentative_pos i).le (cappedRepresentative_pos j).le))
        (mul_nonneg (cappedRepresentative_pos i).le (Real.sqrt_nonneg _)))
  have hsum := large_radius_magnetic_angular_sum hp.le hK Sθ Sφ Sσ hS
  calc
    _ ≤ ∑i∈Sθ,∑k∈Sφ,∑j∈Sσ i k,dyadicBalanceConstant 1 (1/2)*
      (p*(min (cappedRepresentative i) (cappedRepresentative j))^(4/3:ℝ)*
        (cappedRepresentative i)^(-(2/3:ℝ))*(cappedRepresentative k)^(1/3:ℝ)) :=
      Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun k _=>Finset.sum_le_sum (fun j _=>hpoint i k j)))
    _ = dyadicBalanceConstant 1 (1/2)*(∑i∈Sθ,∑k∈Sφ,∑j∈Sσ i k,
      p*(min (cappedRepresentative i) (cappedRepresentative j))^(4/3:ℝ)*
        (cappedRepresentative i)^(-(2/3:ℝ))*(cappedRepresentative k)^(1/3:ℝ)) := by
      simp_rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum
      (dyadicBalanceConstant_pos (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1/2)).le


end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma relative_density_time_far_sqrt {C E I p ν r θ : ℝ}
    (hC : 0≤C) (hE : 0≤E) (hI : 0≤I) (hp : 0<p) (hν : 0≤ν)
    (hr : 0<r) (hθ : 0<θ) :
    Real.sqrt ((128*C*p^3*ν^2)*(491520*I*E/(r^2*θ^2))) =
      Real.sqrt (62914560*C*E)*p*Real.sqrt p*ν*Real.sqrt I/(r*θ) := by
  have he : (128*C*p^3*ν^2)*(491520*I*E/(r^2*θ^2))=
      (62914560*C*E)*p^2*p*ν^2*I/(r*θ)^2 := by ring
  rw [he,Real.sqrt_div (by positivity),Real.sqrt_sq (mul_nonneg hr.le hθ.le),
    Real.sqrt_mul (by positivity : 0≤62914560*C*E*p^2*p*ν^2),
    Real.sqrt_mul (by positivity : 0≤62914560*C*E*p^2*p),Real.sqrt_sq hν,
    Real.sqrt_mul (by positivity : 0≤62914560*C*E*p^2),
    Real.sqrt_mul (by positivity : 0≤62914560*C*E),Real.sqrt_sq hp.le]

lemma relative_large_magnetic_cauchy_scalar {C E Z I p ν r φ θ : ℝ}
    (hC : 0≤C) (hE : 0≤E) (hZ : 0≤Z) (hI : 0<I) (hp : 0<p)
    (hν : 0≤ν) (hr : 0<r) (hφ : 0≤φ) (hθ : 0<θ) :
    let D := ENNReal.ofReal (128*C*p^3*ν^2)
    let H := ENNReal.ofReal (576*I*r*φ^2)
    let O := ENNReal.ofReal (491520*I*E/(r^2*θ^2))
    ENNReal.ofReal (10240/p)*
      ((ENNReal.ofReal (Z*r))^(1/2:ℝ)*(min (D^2*H) (D*O))^(1/2:ℝ)) ≤
    ENNReal.ofReal (relativeCauchyConstant C E Z*Real.sqrt I*
      min (r*p^2*ν^2*φ) (Real.sqrt p*ν/(θ*Real.sqrt r))) := by
  dsimp only
  let K := relativeCauchyConstant C E Z
  have hK : 0≤K := relativeCauchyConstant_nonneg hC
  rw [mul_min_of_nonneg _ _ (mul_nonneg hK (Real.sqrt_nonneg _)),ENNReal.ofReal_min]
  apply le_min
  · calc
      _ ≤ ENNReal.ofReal (10240/p)*
          ((ENNReal.ofReal (Z*r))^(1/2:ℝ)*
            ((ENNReal.ofReal (128*C*p^3*ν^2))^2*ENNReal.ofReal (576*I*r*φ^2))^(1/2:ℝ)) := by
        gcongr
        exact min_le_left _ _
      _ = ENNReal.ofReal ((31457280*C*Real.sqrt Z)*Real.sqrt I*(r*p^2*ν^2*φ)) := by
        rw [←ENNReal.ofReal_pow (by positivity : 0≤128*C*p^3*ν^2),
          ←ENNReal.ofReal_mul (sq_nonneg _),
          ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
          relative_density_near_sqrt hC hI.le hp.le hν hr.le hφ,
          Real.sqrt_mul hZ,
          ←ENNReal.ofReal_mul (by positivity : 0≤Real.sqrt Z*Real.sqrt r),
          ←ENNReal.ofReal_mul (by positivity : 0≤10240/p)]
        congr 1
        have hrsq : Real.sqrt r*Real.sqrt r=r := Real.mul_self_sqrt hr.le
        calc
          _ = 31457280*C*Real.sqrt Z*Real.sqrt I*(Real.sqrt r*Real.sqrt r)*p^2*ν^2*φ := by
            field_simp [hp.ne']
            ring
          _ = _ := by rw [hrsq]; ring
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        exact le_add_of_nonneg_right (by positivity)
  · calc
      _ ≤ ENNReal.ofReal (10240/p)*
          ((ENNReal.ofReal (Z*r))^(1/2:ℝ)*
            ((ENNReal.ofReal (128*C*p^3*ν^2))*
              ENNReal.ofReal (491520*I*E/(r^2*θ^2)))^(1/2:ℝ)) := by
        gcongr
        exact min_le_right _ _
      _ = ENNReal.ofReal ((10240*Real.sqrt Z*Real.sqrt (62914560*C*E))*Real.sqrt I*
          (Real.sqrt p*ν/(θ*Real.sqrt r))) := by
        rw [←ENNReal.ofReal_mul (by positivity : 0≤128*C*p^3*ν^2),
          ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
          relative_density_time_far_sqrt hC hE hI.le hp hν hr hθ,Real.sqrt_mul hZ,
          ←ENNReal.ofReal_mul (by positivity : 0≤Real.sqrt Z*Real.sqrt r),
          ←ENNReal.ofReal_mul (by positivity : 0≤10240/p)]
        congr 1
        have hrsq : Real.sqrt r*Real.sqrt r=r := Real.mul_self_sqrt hr.le
        field_simp [hp.ne',hr.ne',hθ.ne',(Real.sqrt_pos.mpr hr).ne']
        rw [Real.sq_sqrt hr.le]
        ring
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        exact le_add_of_nonneg_left (by positivity)

lemma Admissible.direct_source_large_radius {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (k : Fin 4→ℕ) (j : ℕ)
      (a b I w : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ I → 0 < I →
      I ≤ max 1 T*cappedRepresentative (k 3) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let σ := cappedRepresentative j
      let r := max 1 T*cappedRepresentative (k 3)
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := relativeRepresentativeClosedBin T w k j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let ν := min θ σ
      let Kg := relativeCauchyConstant Cg E (20*E)
      let Kb := relativeCauchyConstant Cb E (120*E)
      (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z
        ∂physicalBinMeasure V B (Icc a b)) ≤
      ENNReal.ofReal (Kg*min ((I*p^2*ν^2*φ^2/θ^2)*Real.sqrt r)
        ((Real.sqrt I*ν/θ^2)/Real.sqrt r)+
      Kb*Real.sqrt I*min (r*p^2*ν^2*φ) (Real.sqrt p*ν/(θ*Real.sqrt r))) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_large_radius_budget
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S k j a b I w hS hS0 ha hb hJI hI hIr
  have hn := hsource s T F hs hT h0 zX S k j a b I w hS hS0 ha hb hJI hI hIr
  dsimp only at hn ⊢
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let σ := cappedRepresentative j
  let r := max 1 T*cappedRepresentative (k 3)
  let ν := min θ σ
  let E := ∫x : Vec,totalEnergy s (0,x)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hσ : 0<σ := cappedRepresentative_pos _
  have hν : 0<ν := lt_min hθ hσ
  have hr : 0<r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hg := relative_radius_cauchy_scalar hCg hE (show 0≤20*E by positivity) hI hp hν
    (show 0≤(1:ℝ) by norm_num) hr hφ (show 0≤(1:ℝ) by norm_num)
    (show 0≤φ/θ^2 by positivity)
  dsimp only at hg
  simp only [one_pow,mul_one,Real.sqrt_one] at hg
  have heγ : 10240*(φ/θ^2)/p=10240*φ/(p*θ^2) := by ring
  have hea : I*p^2*ν^2*φ*(φ/θ^2)=I*p^2*ν^2*φ^2/θ^2 := by ring
  have heb : Real.sqrt I*ν*(φ/θ^2)/φ=Real.sqrt I*ν/θ^2 := by field_simp [hφ.ne']
  rw [heγ,hea,heb,show (20*E)*I=20*I*E by ring] at hg
  have hm := relative_large_magnetic_cauchy_scalar hCb hE (show 0≤120*E by positivity)
    hI hp hν.le hr hφ.le hθ
  dsimp only at hm
  rw [show (120*E)*r=120*r*E by ring] at hm
  have hG0 : 0≤relativeCauchyConstant Cg E (20*E)*
      min ((I*p^2*ν^2*φ^2/θ^2)*Real.sqrt r) ((Real.sqrt I*ν/θ^2)/Real.sqrt r) :=
    mul_nonneg (relativeCauchyConstant_nonneg hCg) (le_min (by positivity) (by positivity))
  have hB0 : 0≤relativeCauchyConstant Cb E (120*E)*Real.sqrt I*
      min (r*p^2*ν^2*φ) (Real.sqrt p*ν/(θ*Real.sqrt r)) :=
    mul_nonneg (mul_nonneg (relativeCauchyConstant_nonneg hCb) (Real.sqrt_nonneg _))
      (le_min (by positivity) (by positivity))
  exact hn.trans ((add_le_add hg hm).trans_eq (ENNReal.ofReal_add hG0 hB0).symm)

lemma capped_large_magnetic_ennreal_sum {H p ν θ φ K : ℝ}
    (hH : 0<H) (hp : 0<p) (hν : 0≤ν) (hθ : 0<θ)
    (hνθ : ν≤θ) (hν1 : ν≤1) (hφ : 0≤φ) (hφ1 : φ≤1) (hK : 0≤K) :
    (∑'n : ℕ, ENNReal.ofReal (K*min
      (H*cappedRepresentative n*p^2*ν^2*φ)
      (Real.sqrt p*ν/(θ*Real.sqrt (H*cappedRepresentative n))))) ≤
      ENNReal.ofReal (K*dyadicBalanceConstant 1 (1/2)*p) := by
  let g : ℤ→ℝ := fun k=>min (H*(2:ℝ)^k*p^2) (Real.sqrt p/Real.sqrt (H*(2:ℝ)^k))
  have hg0 (k : ℤ) : 0≤g k := by dsimp [g]; positivity
  have hg := large_radius_magnetic_balance hH hp (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1)
  simp only [min_self,one_pow,mul_one,one_mul,Real.one_rpow] at hg
  have he (n : ℕ) : cappedRepresentative n=(2:ℝ)^(-(n:ℤ)) := by
    simp only [cappedRepresentative,zpow_neg,zpow_natCast,inv_pow]
  have hinj : Function.Injective (fun n : ℕ=>-(n:ℤ)) := by
    intro a b hab
    exact_mod_cast neg_injective hab
  calc
    _ ≤ ∑'n : ℕ,ENNReal.ofReal (K*g (-(n:ℤ))) := by
      apply ENNReal.tsum_le_tsum
      intro n
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ hK
      dsimp only [g]
      rw [←he]
      have hcn := (cappedRepresentative_pos n).le
      apply min_le_min
      · have hνsq : ν^2≤1 := by nlinarith only [hν,hν1]
        have hprod : ν^2*φ≤1 :=
          (mul_le_mul_of_nonneg_right hνsq hφ).trans (by simpa using hφ1)
        calc
          _ = (H*cappedRepresentative n*p^2)*(ν^2*φ) := by ring
          _ ≤ (H*cappedRepresentative n*p^2)*1 :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
          _ = _ := mul_one _
      · have hr : 0<Real.sqrt (H*cappedRepresentative n) := Real.sqrt_pos.mpr (mul_pos hH (cappedRepresentative_pos _))
        apply (div_le_iff₀ (mul_pos hθ hr)).mpr
        calc
          Real.sqrt p*ν≤Real.sqrt p*θ := mul_le_mul_of_nonneg_left hνθ (Real.sqrt_nonneg _)
          _ = _ := by field_simp
    _ ≤ ∑'k : ℤ,ENNReal.ofReal (K*g k) :=
      ENNReal.tsum_comp_le_tsum_of_injective hinj (fun k=>ENNReal.ofReal (K*g k))
    _ = ENNReal.ofReal (K*∑'k : ℤ,g k) := by
      rw [←ENNReal.ofReal_tsum_of_nonneg (fun k=>mul_nonneg hK (hg0 k)) (hg.1.mul_left K),tsum_mul_left]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [g,mul_assoc] using mul_le_mul_of_nonneg_left hg.2 hK

lemma remaining_good_coarse_balance {I p ν θ φ : ℝ}
    (hI : 0<I) (hI1 : I≤1) (hp : 0≤p) (hν : 0≤ν) (hθ : 0<θ)
    (hνθ : ν≤θ) (hθ1 : θ≤1) (hφ : 0≤φ) (hsector : φ≤16*θ) :
    Real.sqrt ((I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*ν/θ^2)) ≤16*Real.sqrt I*p := by
  have hsqrt : Real.sqrt I≤1 := (Real.sqrt_le_one).mpr hI1
  have hν3 : ν^3≤θ^3 := pow_le_pow_left₀ hν hνθ 3
  have hφ2 : φ^2≤256*θ^2 := by nlinarith only [sq_nonneg (16*θ-φ),hsector,hφ,hθ]
  have hnum : ν^3*φ^2≤256*θ^4 := by
    calc
      _ ≤ θ^3*(256*θ^2) := mul_le_mul hν3 hφ2 (sq_nonneg _) (by positivity)
      _ = 256*θ^4*θ := by ring
      _ ≤ 256*θ^4*1 := mul_le_mul_of_nonneg_left hθ1 (by positivity)
      _ = _ := mul_one _
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  have hfactor : Real.sqrt I*(ν^3*φ^2)≤256*θ^4 := by
    calc
      _ ≤ 1*(256*θ^4) := mul_le_mul hsqrt hnum (by positivity) (by norm_num)
      _ = _ := one_mul _
  have he : (I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*ν/θ^2)=
      (I*p^2)*(Real.sqrt I*(ν^3*φ^2))/θ^4 := by ring
  rw [he,show (16*Real.sqrt I*p)^2=256*I*p^2 by rw [mul_pow,mul_pow,Real.sq_sqrt hI.le]; ring]
  apply (div_le_iff₀ (pow_pos hθ 4)).mpr
  calc
    _ ≤ (I*p^2)*(256*θ^4) := mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = _ := by ring

lemma Admissible.direct_source_remaining_large_sum {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b I w : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ I → 0 < I → I≤1 →
      cappedRepresentative nφ≤16*cappedRepresentative nθ →
      let p := sourceRepresentative np
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Kg := relativeCauchyConstant Cg E (20*E)
      let Kb := relativeCauchyConstant Cb E (120*E)
      (∑'nr : ℕ,if I ≤ max 1 T*cappedRepresentative nr then
        ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
          ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
      ENNReal.ofReal ((16*Kg*dyadicBalanceConstant (1/2) (1/2)+
        Kb*dyadicBalanceConstant 1 (1/2))*Real.sqrt I*p) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_large_radius
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b I w hS hS0 ha hb hJI hI hI1 hsector
  dsimp only
  let p := sourceRepresentative np
  let θ := cappedRepresentative nθ
  let φ := cappedRepresentative nφ
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
  have hν : 0<ν := lt_min hθ (cappedRepresentative_pos _)
  have hKg : 0≤Kg := relativeCauchyConstant_nonneg hCg
  have hKb : 0≤Kb := relativeCauchyConstant_nonneg hCb
  have hH : 0 < max 1 T := zero_lt_one.trans_le (le_max_left _ _)
  have hg := capped_sqrt_radius_ennreal_sum (show 0≤ag by dsimp [ag]; positivity)
    (show 0≤bg by dsimp [bg]; positivity) hH hKg
  have hm := capped_large_magnetic_ennreal_sum hH hp hν.le hθ (min_le_left _ _)
    ((min_le_left _ _).trans (cappedRepresentative_le_one _)) hφ.le
    (cappedRepresentative_le_one _) (mul_nonneg hKb (Real.sqrt_nonneg I))
  have hc := remaining_good_coarse_balance hI hI1 hp.le hν.le hθ (min_le_left _ _)
    (cappedRepresentative_le_one _) hφ.le hsector
  have hDs : 0≤dyadicBalanceConstant (1/2) (1/2) :=
    (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hDm : 0≤dyadicBalanceConstant 1 (1/2) :=
    (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  calc
    _ ≤ ∑'n : ℕ,(G n+Bm n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      split_ifs with hIr
      · have h := hsource s T F hs hT h0 zX S ![np,nθ,nφ,n] j a b I w hS hS0 ha hb hJI hI hIr
        dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Matrix.cons_val,Fin.reduceFinMk] at h
        have hrad : 0 < max 1 T*cappedRepresentative n := mul_pos hH (cappedRepresentative_pos _)
        refine h.trans_eq ?_
        exact ENNReal.ofReal_add
          (mul_nonneg hKg (by positivity))
          (mul_nonneg (mul_nonneg hKb (Real.sqrt_nonneg I)) (le_min (by positivity) (by positivity)))
      · exact bot_le
    _ = (∑'n : ℕ,G n)+(∑'n : ℕ,Bm n) := ENNReal.tsum_add
    _ ≤ ENNReal.ofReal (Kg*dyadicBalanceConstant (1/2) (1/2)*Real.sqrt (ag*bg))+
        ENNReal.ofReal (Kb*Real.sqrt I*dyadicBalanceConstant 1 (1/2)*p) := add_le_add hg hm
    _ = ENNReal.ofReal (Kg*dyadicBalanceConstant (1/2) (1/2)*Real.sqrt (ag*bg)+
        Kb*Real.sqrt I*dyadicBalanceConstant 1 (1/2)*p) :=
      (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ Kg*dyadicBalanceConstant (1/2) (1/2)*(16*Real.sqrt I*p)+
            Kb*Real.sqrt I*dyadicBalanceConstant 1 (1/2)*p :=
          add_le_add (mul_le_mul_of_nonneg_left hc (mul_nonneg hKg hDs)) le_rfl
        _ = _ := by dsimp only [Kg,Kb,p,E]; ring

lemma capped_short_sqrt_radius_sum {H R K : ℝ} (hH : 0<H) (hR : 0<R) (hK : 0≤K) :
    (∑'n : ℕ,if H*cappedRepresentative n≤R then
      ENNReal.ofReal (K*Real.sqrt (H*cappedRepresentative n)) else 0) ≤
    ENNReal.ofReal (K*(1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹*Real.sqrt R) := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro N
  let S := (Finset.range N).filter (fun n=>H*cappedRepresentative n≤R)
  have hS : ∀n∈S,cappedRepresentative n≤R/H := by
    intro n hn
    exact (le_div_iff₀ hH).mpr (by simpa only [mul_comm] using (Finset.mem_filter.mp hn).2)
  have hh := capped_positive_power_sum_unscaled (div_pos hR hH) (by norm_num : (0:ℝ)<1/2) S hS
  have he (n : ℕ) : Real.sqrt (H*cappedRepresentative n)=
      Real.sqrt H*(cappedRepresentative n)^(1/2:ℝ) := by
    rw [Real.sqrt_mul hH.le,Real.sqrt_eq_rpow (cappedRepresentative n)]
  calc
    _ = ∑n∈S,ENNReal.ofReal (K*Real.sqrt (H*cappedRepresentative n)) := by
      simp only [S,Finset.sum_filter]
    _ = ENNReal.ofReal (K*Real.sqrt H*(∑n∈S,(cappedRepresentative n)^(1/2:ℝ))) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun n hn=>mul_nonneg hK (Real.sqrt_nonneg _))]
      simp only [he,←mul_assoc,Finset.mul_sum]
    _ ≤ ENNReal.ofReal (K*Real.sqrt H*((1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹*(R/H)^(1/2:ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left hh (mul_nonneg hK (Real.sqrt_nonneg _))
    _ = _ := by
      rw [←Real.sqrt_eq_rpow (R/H),Real.sqrt_div hR.le]
      congr 1
      field_simp [(Real.sqrt_pos.mpr hH).ne']

lemma Admissible.direct_source_short_near_sum {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b I w : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ I → 0 < I →
      let p := sourceRepresentative np
      let θ := cappedRepresentative nθ
      let φ := cappedRepresentative nφ
      let σ := cappedRepresentative j
      let ν := min θ σ
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Kg := relativeCauchyConstant Cg E (20*E)
      let Kb := relativeCauchyConstant Cb E (120*E)
      (∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤I then
        ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
          ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
      ENNReal.ofReal ((Kg*(I*p^2*ν^2*φ^2/θ^2)+Kb*(I*p^2*ν^2*φ))*
        (1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹*Real.sqrt I) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_short_near
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b I w hS hS0 ha hb hJI hI
  dsimp only
  have hKg := relativeCauchyConstant_nonneg (E:=∫x : Vec,totalEnergy s (0,x)) (Z:=20*(∫x : Vec,totalEnergy s (0,x))) hCg
  have hKb := relativeCauchyConstant_nonneg (E:=∫x : Vec,totalEnergy s (0,x)) (Z:=120*(∫x : Vec,totalEnergy s (0,x))) hCb
  have hφ := (cappedRepresentative_pos nφ).le
  have hK0 : 0≤relativeCauchyConstant Cg (∫x : Vec,totalEnergy s (0,x)) (20*(∫x : Vec,totalEnergy s (0,x)))*
      (I*(sourceRepresentative np)^2*(min (cappedRepresentative nθ) (cappedRepresentative j))^2*(cappedRepresentative nφ)^2/(cappedRepresentative nθ)^2)+
      relativeCauchyConstant Cb (∫x : Vec,totalEnergy s (0,x)) (120*(∫x : Vec,totalEnergy s (0,x)))*
      (I*(sourceRepresentative np)^2*(min (cappedRepresentative nθ) (cappedRepresentative j))^2*cappedRepresentative nφ) := by positivity
  apply le_trans (ENNReal.tsum_le_tsum (fun n=>?_)) (capped_short_sqrt_radius_sum
    (show 0 < max 1 T from zero_lt_one.trans_le (le_max_left _ _)) hI hK0)
  split_ifs with hrI
  · have hh := hsource s T F hs hT h0 zX S ![np,nθ,nφ,n] j a b I w hS hS0 ha hb hJI hI hrI
    dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Matrix.cons_val,Fin.reduceFinMk] at hh
    exact hh
  · exact le_rfl

lemma deficit_short_source_coefficient {I P p w θ φ σ Kg Kb : ℝ}
    (hI : 0<I) (hI1 : I≤1) (hP : 0<P) (hp : 0<p) (hw : 0<w)
    (hθ : 0<θ) (hφ : 0≤φ) (hφ1 : φ≤1) (hσ : 0≤σ)
    (hsector : φ≤16*θ) (hpP : p≤128*P) (hIP : I≤(w/P)^2)
    (hdeficit : σ*p≤512 ∨ σ*w≤32) (hKg : 0≤Kg) (hKb : 0≤Kb) :
    Kg*(I*p^2*(min θ σ)^2*φ^2/θ^2)+Kb*(I*p^2*(min θ σ)^2*φ) ≤
      (256*Kg+Kb)*16777216 := by
  have hν : 0 ≤ min θ σ := le_min hθ.le hσ
  have hσsq : (min θ σ)^2≤σ^2 := pow_le_pow_left₀ hν (min_le_right _ _) 2
  have hIpp : I*p^2≤16384*w^2 := by
    have hp2 : p^2≤16384*P^2 := by nlinarith only [sq_nonneg (128*P-p),hpP,hp,hP]
    have h := mul_le_mul hIP hp2 (sq_nonneg _) (by positivity : 0≤(w/P)^2)
    have he : (w/P)^2*(16384*P^2)=16384*w^2 := by field_simp
    exact h.trans_eq he
  have hbase : I*p^2*(min θ σ)^2≤16777216 := by
    calc
      _ ≤ I*p^2*σ^2 := mul_le_mul_of_nonneg_left hσsq (by positivity)
      _ ≤ 16777216 := by
        rcases hdeficit with hd | hd
        · have hsq : (σ*p)^2≤512^2 := pow_le_pow_left₀ (mul_nonneg hσ hp.le) hd 2
          have he : I*p^2*σ^2=I*(σ*p)^2 := by ring
          rw [he]
          calc
            _ ≤ 1*(512:ℝ)^2 := mul_le_mul hI1 hsq (sq_nonneg _) (by norm_num)
            _ ≤ _ := by norm_num
        · have hsq : (σ*w)^2≤32^2 := pow_le_pow_left₀ (mul_nonneg hσ hw.le) hd 2
          calc
            _ ≤ (16384*w^2)*σ^2 := mul_le_mul_of_nonneg_right hIpp (sq_nonneg _)
            _ = 16384*(σ*w)^2 := by ring
            _ ≤ 16384*(32:ℝ)^2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
            _ = _ := by norm_num
  have hφ2 : φ^2/θ^2≤256 := by
    apply (div_le_iff₀ (pow_pos hθ 2)).mpr
    nlinarith only [sq_nonneg (16*θ-φ),hsector,hφ,hθ]
  have hgood : I*p^2*(min θ σ)^2*φ^2/θ^2≤16777216*256 := by
    rw [mul_div_assoc]
    exact mul_le_mul hbase hφ2 (by positivity) (by norm_num)
  have hmag : I*p^2*(min θ σ)^2*φ≤16777216 := by
    have h := mul_le_mul hbase hφ1 hφ (by norm_num : (0:ℝ)≤16777216)
    simpa only [mul_one] using h
  calc
    _ ≤ Kg*(16777216*256)+Kb*16777216 := add_le_add
      (mul_le_mul_of_nonneg_left hgood hKg) (mul_le_mul_of_nonneg_left hmag hKb)
    _ = _ := by ring

lemma shortSqrtConstant_pos : 0<(1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹ := by
  apply inv_pos.mpr
  apply sub_pos.mpr
  exact Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)

lemma Admissible.direct_source_deficit_short_sum {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b I w P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ I → 0 < I → I≤1 → 0<w → 0<P →
      sourceRepresentative np≤128*P → I≤(w/P)^2 →
      cappedRepresentative nφ≤16*cappedRepresentative nθ →
      (cappedRepresentative j*sourceRepresentative np≤512 ∨ cappedRepresentative j*w≤32) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Kg := relativeCauchyConstant Cg E (20*E)
      let Kb := relativeCauchyConstant Cb E (120*E)
      (∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤I then
        ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
          ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
      ENNReal.ofReal ((256*Kg+Kb)*16777216*(1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹*Real.sqrt I) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_short_near_sum
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b I w P hS hS0 ha hb hJI hI hI1 hw hP hpP hIP hsector hdeficit
  dsimp only
  have hn := hsource s T F hs hT h0 zX S np nθ nφ j a b I w hS hS0 ha hb hJI hI
  have hp : 0<sourceRepresentative np := by dsimp [sourceRepresentative]; positivity
  have hθ := cappedRepresentative_pos nθ
  have hφ := cappedRepresentative_pos nφ
  have hKg := relativeCauchyConstant_nonneg (E:=∫x : Vec,totalEnergy s (0,x)) (Z:=20*(∫x : Vec,totalEnergy s (0,x))) hCg
  have hKb := relativeCauchyConstant_nonneg (E:=∫x : Vec,totalEnergy s (0,x)) (Z:=120*(∫x : Vec,totalEnergy s (0,x))) hCb
  have hc := deficit_short_source_coefficient hI hI1 hP hp hw hθ hφ.le (cappedRepresentative_le_one _)
    (cappedRepresentative_pos j).le hsector hpP hIP hdeficit hKg hKb
  exact hn.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc shortSqrtConstant_pos.le) (Real.sqrt_nonneg I)))

lemma relativeCauchyConstant_energy_le {C E Z : ℝ} (hC : 0≤C) (hE : 0≤E) (hZ : 0≤Z) :
    relativeCauchyConstant C E (Z*E) ≤ relativeCauchyConstant C 1 Z*(1+E) := by
  have hroot : Real.sqrt E≤1+E := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    nlinarith only [sq_nonneg E,hE]
  have he : relativeCauchyConstant C E (Z*E)=
      (31457280*C*Real.sqrt Z)*Real.sqrt E+
      (10240*Real.sqrt Z*Real.sqrt (62914560*C))*E := by
    unfold relativeCauchyConstant
    rw [Real.sqrt_mul hZ,Real.sqrt_mul (by positivity : 0≤62914560*C)]
    rw [show 10240*(Real.sqrt Z*Real.sqrt E)*(Real.sqrt (62914560*C)*Real.sqrt E)=
      (10240*Real.sqrt Z*Real.sqrt (62914560*C))*(Real.sqrt E)^2 by ring,Real.sq_sqrt hE]
    ring
  rw [he]
  have hE1 : E≤1+E := by linarith
  calc
    _ ≤ (31457280*C*Real.sqrt Z)*(1+E)+
        (10240*Real.sqrt Z*Real.sqrt (62914560*C))*(1+E) := add_le_add
      (mul_le_mul_of_nonneg_left hroot (by positivity))
      (mul_le_mul_of_nonneg_left hE1 (by positivity))
    _ = _ := by simp only [relativeCauchyConstant,mul_one]; ring

lemma remaining_stability_sqrt_coarse {M A w L : ℝ} (hM : 0<M) (hA : 0≤A)
    (hw : 0≤w) (hL : 1≤L) :
    Real.sqrt (32768*17*(1+16384*(M+Real.sqrt A))*w^2*Real.sqrt L) ≤
      (32768*17*16384)*(1+M+Real.sqrt A)*w*L := by
  let Z := (32768*17*16384)*(1+M+Real.sqrt A)
  have hsqrt : 0≤Real.sqrt A := by simpa only [Real.sqrt_zero] using Real.sqrt_le_sqrt hA
  have hZ : 1≤Z := by dsimp [Z]; nlinarith only [hM,hsqrt]
  have hcoeff : 32768*17*(1+16384*(M+Real.sqrt A))≤Z^2 := by
    have hb : 32768*17*(1+16384*(M+Real.sqrt A))≤Z := by dsimp [Z]; nlinarith
    exact hb.trans (by nlinarith only [hZ])
  have hroot : Real.sqrt L≤L^2 := by
    have h := (Real.sqrt_le_iff).mpr (And.intro (by linarith : 0≤L) (by nlinarith only [hL] : L≤L^2))
    exact h.trans (by nlinarith only [hL])
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  change _≤(Z*w*L)^2
  calc
    _ ≤ Z^2*w^2*L^2 := mul_le_mul
      (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg w)) hroot (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring

lemma Admissible.direct_source_remaining_all_radii {d : Datum} (hd₀ : Admissible d) :
    ∃ C : ℝ, 0≤C ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → b-a ≤ (w/P)^2 →
      0 < M → 0 ≤ A → 1 ≤ P → 1 ≤ Real.log (2+P) → 0 < w → w≤P →
      sourceRepresentative np≤128*P →
      cappedRepresentative nφ≤16*cappedRepresentative nθ →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
        ∂physicalBinMeasure V (B nr) (Icc a b)) ≤
      ENNReal.ofReal (C*(1+E)*(1+M+Real.sqrt A)*w*Real.log (2+P)) := by
  obtain ⟨Cgs,Cbs,hCgs,hCbs,hshort⟩ := hd₀.direct_source_remaining_short_sum
  obtain ⟨Cgd,Cbd,hCgd,hCbd,hdef⟩ := hd₀.direct_source_deficit_short_sum
  obtain ⟨Cgl,Cbl,hCgl,hCbl,hlong⟩ := hd₀.direct_source_remaining_large_sum
  let Ds := dyadicBalanceConstant (1/2) (1/2)
  let Dm := dyadicBalanceConstant 1 (1/2)
  let Dn := (1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹
  let gs := relativeCauchyConstant Cgs 1 20
  let bs := relativeCauchyConstant Cbs 1 120
  let gd := relativeCauchyConstant Cgd 1 20
  let bd := relativeCauchyConstant Cbd 1 120
  let gl := relativeCauchyConstant Cgl 1 20
  let bl := relativeCauchyConstant Cbl 1 120
  let Cs := (16*gs+bs)*Ds*(32768*17*16384)
  let Cd := (256*gd+bd)*16777216*Dn
  let Cl := (16*gl*Ds+bl*Dm)*128
  have hDs : 0≤Ds := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hDm : 0≤Dm := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hDn : 0≤Dn := shortSqrtConstant_pos.le
  have hgs : 0≤gs := relativeCauchyConstant_nonneg hCgs
  have hbs : 0≤bs := relativeCauchyConstant_nonneg hCbs
  have hgd : 0≤gd := relativeCauchyConstant_nonneg hCgd
  have hbd : 0≤bd := relativeCauchyConstant_nonneg hCbd
  have hgl : 0≤gl := relativeCauchyConstant_nonneg hCgl
  have hbl : 0≤bl := relativeCauchyConstant_nonneg hCbl
  have hCs : 0≤Cs := by dsimp only [Cs]; positivity
  have hCd : 0≤Cd := by dsimp only [Cd]; positivity
  have hCl : 0≤Cl := by dsimp only [Cl]; positivity
  refine ⟨Cs+Cd+Cl,by positivity,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b w M A P hS hS0 ha hb hab hJI
    hM hA hP1 hL hw hwP hpP hsector HX HZ
  dsimp only
  let I := (w/P)^2
  let L := Real.log (2+P)
  let E := ∫x : Vec,totalEnergy s (0,x)
  let p := sourceRepresentative np
  let θ := cappedRepresentative nθ
  let φ := cappedRepresentative nφ
  let σ := cappedRepresentative j
  let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
  let J : ℕ→ℝ≥0∞ := fun nr=>∫⁻z : ConeCoordinate,
    physicalDirectSourceDensity s (fun t=>(prefixFlow F.flow T zX t).1)
      (fun t=>(prefixFlow F.flow T zX t).2) (B nr) z
      ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (B nr) (Icc a b)
  let Jshort : ℕ→ℝ≥0∞ := fun nr=>if max 1 T*cappedRepresentative nr≤I then J nr else 0
  let Jlong : ℕ→ℝ≥0∞ := fun nr=>if I ≤ max 1 T*cappedRepresentative nr then J nr else 0
  let U := (1+E)*(1+M+Real.sqrt A)*w*L
  have hP : 0<P := zero_lt_one.trans_le hP1
  have hI : 0<I := sq_pos_of_pos (div_pos hw hP)
  have hI1 : I≤1 := by dsimp only [I]; exact pow_le_one₀ (div_pos hw hP).le ((div_le_one hP).mpr hwP)
  have hp : 0<p := by dsimp only [p,sourceRepresentative]; positivity
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hL0 : 0≤L := zero_le_one.trans hL
  have hU : 0≤U := by dsimp only [U]; positivity
  have hMA : 1≤1+M+Real.sqrt A := by linarith [Real.sqrt_nonneg A]
  have hbaseU : (1+E)*w≤U := by
    calc
      _ = (1+E)*1*w*1 := by ring
      _ ≤ (1+E)*(1+M+Real.sqrt A)*w*L := by gcongr
  have hIsqrt : Real.sqrt I=w/P := Real.sqrt_sq (div_pos hw hP).le
  have hIw : Real.sqrt I≤w := by rw [hIsqrt]; exact (div_le_self hw.le hP1)
  have hgse := relativeCauchyConstant_energy_le hCgs hE (by norm_num : (0:ℝ)≤20)
  have hbse := relativeCauchyConstant_energy_le hCbs hE (by norm_num : (0:ℝ)≤120)
  have hgde := relativeCauchyConstant_energy_le hCgd hE (by norm_num : (0:ℝ)≤20)
  have hbde := relativeCauchyConstant_energy_le hCbd hE (by norm_num : (0:ℝ)≤120)
  have hgle := relativeCauchyConstant_energy_le hCgl hE (by norm_num : (0:ℝ)≤20)
  have hble := relativeCauchyConstant_energy_le hCbl hE (by norm_num : (0:ℝ)≤120)
  have hshortBound : (∑'n,Jshort n)≤ENNReal.ofReal ((Cs+Cd)*U) := by
    by_cases hdeficit : σ*p≤512 ∨ σ*w≤32
    · have hn := hdef s T F hs hT h0 zX S np nθ nφ j a b I w P hS hS0 ha hb hJI
        hI hI1 hw hP hpP le_rfl hsector hdeficit
      apply hn.trans
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ ((256*(gd*(1+E))+bd*(1+E))*16777216*Dn)*w := by
          dsimp only [Dn,gd,bd]
          gcongr
        _ = Cd*((1+E)*w) := by dsimp only [Cd]; ring
        _ ≤ Cd*U := mul_le_mul_of_nonneg_left hbaseU hCd
        _ ≤ (Cs+Cd)*U := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCs) hU
    · have hh := not_or.mp hdeficit
      have hn := hshort s T F hs hT h0 zX S np nθ nφ j a b w M A P hS hS0 ha hb hab hJI
        hM hA hP hL hw hwP hpP hsector (le_of_lt (lt_of_not_ge hh.1)) (le_of_lt (lt_of_not_ge hh.2)) HX HZ
      have hc := remaining_stability_sqrt_coarse hM hA hw.le hL
      apply hn.trans
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (16*(gs*(1+E))+bs*(1+E))*Ds*
            ((32768*17*16384)*(1+M+Real.sqrt A)*w*L) := by
          dsimp only [gs,bs,Ds,L]
          gcongr
        _ = Cs*U := by dsimp only [Cs,U]; ring
        _ ≤ (Cs+Cd)*U := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCd) hU
  have hlongBound : (∑'n,Jlong n)≤ENNReal.ofReal (Cl*U) := by
    have hn := hlong s T F hs hT h0 zX S np nθ nφ j a b I w hS hS0 ha hb hJI hI hI1 hsector
    apply hn.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (16*(gl*(1+E))*Ds+(bl*(1+E))*Dm)*Real.sqrt I*(128*P) := by
        dsimp only [gl,bl,Ds,Dm]
        gcongr
      _ = Cl*((1+E)*w) := by rw [hIsqrt]; dsimp only [Cl]; field_simp
      _ ≤ Cl*U := mul_le_mul_of_nonneg_left hbaseU hCl
  calc
    _ = ∑'n,J n := rfl
    _ ≤ ∑'n,(Jshort n+Jlong n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      dsimp only [Jshort,Jlong]
      by_cases hrI : max 1 T*cappedRepresentative n≤I
      · rw [ite_eq_left hrI]
        exact le_add_of_nonneg_right (bot_le : (0 : ℝ≥0∞) ≤ _)
      · rw [ite_eq_right hrI,ite_eq_left (le_of_lt (lt_of_not_ge hrI)),zero_add]
    _ = (∑'n,Jshort n)+(∑'n,Jlong n) := ENNReal.tsum_add
    _ ≤ ENNReal.ofReal ((Cs+Cd)*U)+ENNReal.ofReal (Cl*U) := add_le_add hshortBound hlongBound
    _ = _ := by
      rw [←ENNReal.ofReal_add (mul_nonneg (add_nonneg hCs hCd) hU) (mul_nonneg hCl hU)]
      congr 1
      dsimp only [U,E,L]
      ring



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


lemma deficit_short_source_coefficient_expanded {I P p w θ φ σ Kg Kb : ℝ}
    (hI : 0<I) (hI1 : I≤1) (hP : 0<P) (hp : 0<p) (hw : 0<w)
    (hθ : 0<θ) (hφ : 0≤φ) (hφ1 : φ≤1) (hσ : 0≤σ)
    (hsector : φ≤16384*θ) (hpP : p≤128*P) (hIP : I≤(w/P)^2)
    (hdeficit : σ*p≤512 ∨ σ*w≤32) (hKg : 0≤Kg) (hKb : 0≤Kb) :
    Kg*(I*p^2*(min θ σ)^2*φ^2/θ^2)+Kb*(I*p^2*(min θ σ)^2*φ) ≤
      (268435456*Kg+Kb)*16777216 := by
  have hν : 0 ≤ min θ σ := le_min hθ.le hσ
  have hσsq : (min θ σ)^2≤σ^2 := pow_le_pow_left₀ hν (min_le_right _ _) 2
  have hIpp : I*p^2≤16384*w^2 := by
    have hp2 : p^2≤16384*P^2 := by nlinarith only [sq_nonneg (128*P-p),hpP,hp,hP]
    have h := mul_le_mul hIP hp2 (sq_nonneg _) (by positivity : 0≤(w/P)^2)
    have he : (w/P)^2*(16384*P^2)=16384*w^2 := by field_simp
    exact h.trans_eq he
  have hbase : I*p^2*(min θ σ)^2≤16777216 := by
    calc
      _ ≤ I*p^2*σ^2 := mul_le_mul_of_nonneg_left hσsq (by positivity)
      _ ≤ 16777216 := by
        rcases hdeficit with hd | hd
        · have hsq : (σ*p)^2≤512^2 := pow_le_pow_left₀ (mul_nonneg hσ hp.le) hd 2
          have he : I*p^2*σ^2=I*(σ*p)^2 := by ring
          rw [he]
          calc
            _ ≤ 1*(512:ℝ)^2 := mul_le_mul hI1 hsq (sq_nonneg _) (by norm_num)
            _ ≤ _ := by norm_num
        · have hsq : (σ*w)^2≤32^2 := pow_le_pow_left₀ (mul_nonneg hσ hw.le) hd 2
          calc
            _ ≤ (16384*w^2)*σ^2 := mul_le_mul_of_nonneg_right hIpp (sq_nonneg _)
            _ = 16384*(σ*w)^2 := by ring
            _ ≤ 16384*(32:ℝ)^2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
            _ = _ := by norm_num
  have hφ2 : φ^2/θ^2≤268435456 := by
    apply (div_le_iff₀ (pow_pos hθ 2)).mpr
    nlinarith only [sq_nonneg (16384*θ-φ),hsector,hφ,hθ]
  have hgood : I*p^2*(min θ σ)^2*φ^2/θ^2≤16777216*268435456 := by
    rw [mul_div_assoc]
    exact mul_le_mul hbase hφ2 (by positivity) (by norm_num)
  have hmag : I*p^2*(min θ σ)^2*φ≤16777216 := by
    have h := mul_le_mul hbase hφ1 hφ (by norm_num : (0:ℝ)≤16777216)
    simpa only [mul_one] using h
  calc
    _ ≤ Kg*(16777216*268435456)+Kb*16777216 := add_le_add
      (mul_le_mul_of_nonneg_left hgood hKg) (mul_le_mul_of_nonneg_left hmag hKb)
    _ = _ := by ring

lemma Admissible.direct_source_deficit_short_sum_expanded {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b I w P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ I → 0 < I → I≤1 → 0<w → 0<P →
      sourceRepresentative np≤128*P → I≤(w/P)^2 →
      cappedRepresentative nφ≤16384*cappedRepresentative nθ →
      (cappedRepresentative j*sourceRepresentative np≤512 ∨ cappedRepresentative j*w≤32) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Kg := relativeCauchyConstant Cg E (20*E)
      let Kb := relativeCauchyConstant Cb E (120*E)
      (∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤I then
        ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
          ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
      ENNReal.ofReal ((268435456*Kg+Kb)*16777216*(1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹*Real.sqrt I) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_short_near_sum
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b I w P hS hS0 ha hb hJI hI hI1 hw hP hpP hIP hsector hdeficit
  dsimp only
  have hn := hsource s T F hs hT h0 zX S np nθ nφ j a b I w hS hS0 ha hb hJI hI
  have hp : 0<sourceRepresentative np := by dsimp [sourceRepresentative]; positivity
  have hθ := cappedRepresentative_pos nθ
  have hφ := cappedRepresentative_pos nφ
  have hKg := relativeCauchyConstant_nonneg (E:=∫x : Vec,totalEnergy s (0,x)) (Z:=20*(∫x : Vec,totalEnergy s (0,x))) hCg
  have hKb := relativeCauchyConstant_nonneg (E:=∫x : Vec,totalEnergy s (0,x)) (Z:=120*(∫x : Vec,totalEnergy s (0,x))) hCb
  have hc := deficit_short_source_coefficient_expanded hI hI1 hP hp hw hθ hφ.le (cappedRepresentative_le_one _)
    (cappedRepresentative_pos j).le hsector hpP hIP hdeficit hKg hKb
  exact hn.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc shortSqrtConstant_pos.le) (Real.sqrt_nonneg I)))



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


lemma relativePhysicalBase_receiver_floor {T w : ℝ} {V : ℝ→Vec}
    {J : Set ℝ} {k : Fin 4→ℕ} {j : ℕ} {z : ConeCoordinate}
    (hw : 0<w) (hz : z∈physicalBinBase V (relativeRepresentativeClosedBin T w k j) J) :
    1/(32*w)≤cappedRepresentative (k 2) := by
  have hq : q (V z.1)≤8*w := hz.2.2.2.1.2
  have hD : 1-dot z.2.2.1 (velocity (V z.1))≤8*(cappedRepresentative (k 2))^2 := hz.2.2.2.2.2
  have hf := cappedRepresentative_pos (k 2)
  have hlo := source_angle_coordinate_lower (V z.1) z.2.2.1 (sphere_norm z.2.2)
  have hroot : Real.sqrt ((1-dot z.2.2.1 (velocity (V z.1)))/2)≤2*cappedRepresentative (k 2) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith
  have hm := mul_le_mul hq hroot (Real.sqrt_nonneg _) (by positivity : (0:ℝ)≤8*w)
  apply (div_le_iff₀ (by positivity : (0:ℝ)<32*w)).mpr
  nlinarith

lemma physicalDirectSource_integral_expanded_bad_zero (s : Solution) {T w : ℝ}
    {X V : ℝ→Vec} (hV : Measurable V) {J : Set ℝ} (hJ : MeasurableSet J)
    (hw : 0<w) {k : Fin 4→ℕ} {j : ℕ}
    (hsector : cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1))
    (hbad : ¬(1/(32*w)≤cappedRepresentative (k 2) ∧
      cappedRepresentative j≤131080*cappedRepresentative (k 1))) :
    (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (relativeRepresentativeClosedBin T w k j) z
      ∂physicalBinMeasure V (relativeRepresentativeClosedBin T w k j) J)=0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV _ hJ)] with z hz
  have hempty : coneBinMomentumSet (relativeRepresentativeClosedBin T w k j) z.2.2.1 (velocity (V z.1))=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    apply hbad
    refine ⟨relativePhysicalBase_receiver_floor hw hz,?_⟩
    simpa only [show (8:ℝ)*(1+16384)=131080 by norm_num] using
      physical_relative_remaining_upper (by norm_num : (0:ℝ)≤16384) hsector hz hv
  simp only [physicalDirectSourceDensity,hempty,Measure.restrict_empty,lintegral_zero_measure,mul_zero,Pi.zero_apply]

lemma physicalDirectTransport_integral_expanded_bad_zero (s : Solution) {T w : ℝ}
    {X V : ℝ→Vec} (hV : Measurable V) {J : Set ℝ} (hJ : MeasurableSet J)
    (hw : 0<w) {k : Fin 4→ℕ} {j : ℕ}
    (hsector : cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1))
    (hbad : ¬(1/(32*w)≤cappedRepresentative (k 2) ∧
      cappedRepresentative j≤131080*cappedRepresentative (k 1))) :
    (∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V (relativeRepresentativeClosedBin T w k j) z
      ∂physicalBinMeasure V (relativeRepresentativeClosedBin T w k j) J)=0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV _ hJ)] with z hz
  have hempty : coneBinMomentumSet (relativeRepresentativeClosedBin T w k j) z.2.2.1 (velocity (V z.1))=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    apply hbad
    refine ⟨relativePhysicalBase_receiver_floor hw hz,?_⟩
    simpa only [show (8:ℝ)*(1+16384)=131080 by norm_num] using
      physical_relative_remaining_upper (by norm_num : (0:ℝ)≤16384) hsector hz hv
  simp only [physicalDirectTransportDensity,hempty,Measure.restrict_empty,lintegral_zero_measure,mul_zero,Pi.zero_apply]

end RVM

end

end OAI
