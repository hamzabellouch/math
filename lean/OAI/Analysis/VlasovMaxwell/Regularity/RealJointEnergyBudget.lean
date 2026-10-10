import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.PhysicalElectricKernel
import OAI.Analysis.VlasovMaxwell.Population.LabelOccupationDurationMass
import OAI.Analysis.VlasovMaxwell.Flow.PhaseAcceleration

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
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

def realJointEnergyBudget (s : Solution) (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ)
    (k : ℕ) (a b I : ℝ) (n : ℕ × ℕ) : ℝ :=
  (jointEnergyBudget s α zX T k a b I n).toReal

lemma PhaseFlowOn.realJointEnergyBudget_summable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (k : ℕ) {a b I : ℝ} (hJ : Icc a b⊆Icc (0:ℝ) T) (hI : 0<I) :
    Summable (realJointEnergyBudget s F.flow zX T k a b I) :=
  ENNReal.summable_toReal (F.jointEnergyBudget_finite hs zX k hJ hI)

lemma PhaseFlowOn.realJointEnergyBudget_uniform {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (k : ℕ) {a b I C : ℝ} (hJ : Icc a b⊆Icc (0:ℝ) T)
    (hI : 0<I) (hC : 0≤C) (hlen : b-a≤C*I) :
    ∑' n : ℕ × ℕ, realJointEnergyBudget s F.flow zX T k a b I n ≤
      (3*(4*k+1)^2:ℕ) * C * (∫ x : Vec, totalEnergy s (0,x)) := by
  have hfin := F.jointEnergyBudget_finite hs zX k hJ hI
  have hh := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top) (F.jointEnergyBudget_uniform hs zX k hJ hI hC hlen)
  rw [ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hfin)] at hh
  have hE : 0≤∫ x : Vec, totalEnergy s (0,x) :=
    integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  simpa only [realJointEnergyBudget,ENNReal.toReal_mul,ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hC,ENNReal.toReal_ofReal hE] using hh

lemma sum_cell_lintegral_le {ι : Type*} (S : Finset ι) (a b : ι → ℝ)
    (g : ℝ → ℝ≥0∞) {J : Set ℝ}
    (hdisj : Set.PairwiseDisjoint (↑S) (fun i => Ioc (a i) (b i)))
    (hsub : ∀ i∈S, Ioc (a i) (b i)⊆J) :
    (∑ i∈S, ∫⁻ t in Icc (a i) (b i), g t)≤∫⁻ t in J, g t := by
  have he (i : ι) : (∫⁻ t in Icc (a i) (b i), g t)=(∫⁻ t in Ioc (a i) (b i), g t) := by
    rw [Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ:=volume) (a:=a i) (b:=b i))]
  simp_rw [he]
  rw [← lintegral_biUnion_finset hdisj (fun _ _ => measurableSet_Ioc)]
  exact lintegral_mono_set (iUnion₂_subset fun i hi => hsub i hi)

lemma PhaseFlowOn.averaged_cells_occupation {s : Solution} {T len p D : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    {ι : Type*} (S : Finset ι) (a b : ι → ℝ)
    {H : ι → Phase → Set ℝ} {Z : ι → Set Phase} {G : Set (ℝ × Phase)} {J : Set ℝ}
    (hCT : ∀ i∈S, Icc (a i) (b i)⊆Icc (0:ℝ) T)
    (hlen : ∀ i∈S, b i-a i=len)
    (hdisj : Set.PairwiseDisjoint (↑S) (fun i => Ioc (a i) (b i)))
    (hsub : ∀ i∈S, Ioc (a i) (b i)⊆J)
    (hZ : ∀ i∈S, MeasurableSet (Z i))
    (hD : ∀ i∈S, ∀ z, volume (H i z)≤ENNReal.ofReal D)
    (hz : ∀ i∈S, ∀ z, (H i z).Nonempty → z∈Z i)
    (hmom : ∀ i∈S, ∀ t∈Icc (a i) (b i), ∀ z∈Z i, p≤q (F.flow z t).2)
    (hG : ∀ i∈S, ∀ t∈Icc (a i) (b i), ∀ z∈Z i, (t,F.flow z t)∈G) :
    ENNReal.ofReal len * ENNReal.ofReal p *
        (∑ i∈S, labelOccupation (fun z => s.f (0,z)) (H i)) ≤
      ENNReal.ofReal D * ∫⁻ t in J, ∫⁻ z : Phase,
        G.indicator (fun q => ENNReal.ofReal (RVM.q q.2.2*s.f q)) (t,z) := by
  calc
    _ = ∑ i∈S, ENNReal.ofReal len * ENNReal.ofReal p *
        labelOccupation (fun z => s.f (0,z)) (H i) := Finset.mul_sum _ _ _
    _ ≤ ∑ i∈S, ENNReal.ofReal D * ∫⁻ t in Icc (a i) (b i), ∫⁻ z : Phase,
        G.indicator (fun q => ENNReal.ofReal (RVM.q q.2.2*s.f q)) (t,z) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [hlen i hi] using F.averaged_cell_occupation hs (hCT i hi)
        (hZ i hi) (hD i hi) (hz i hi) (hmom i hi) (hG i hi)
    _ = ENNReal.ofReal D * (∑ i∈S, ∫⁻ t in Icc (a i) (b i), ∫⁻ z : Phase,
        G.indicator (fun q => ENNReal.ofReal (RVM.q q.2.2*s.f q)) (t,z)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul' le_rfl (sum_cell_lintegral_le S a b _ hdisj hsub)

end RVM

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma relative_angle_identity (v w : Vec) :
    2*(1-dot (velocity w) (velocity v)) =
      ‖velocity v-velocity w‖^2+(q v)⁻¹^2+(q w)⁻¹^2 :=  by
  rw [norm_sub_sq_real,← dot_eq_inner,← dot_self (velocity v),
    ← dot_self (velocity w),velocity_self,velocity_self,dot_comm (velocity v)]
  ring

lemma actual_relative_separation {v w : Vec} {ang : ℝ}
    (_hom : 0  ≤  ang) (hv : (q v)⁻¹ ≤ ang/4) (hw : (q w)⁻¹ ≤ ang/4)
    (he : ang^2/2 ≤ 1-dot (velocity w) (velocity v)) :
    ang/2 ≤ ‖velocity v-velocity w‖ :=  by
  have hid :=  relative_angle_identity v w
  have hv0 : 0  ≤  (q v)⁻¹ :=  inv_nonneg.mpr (q_pos v).le
  have hw0 : 0  ≤  (q w)⁻¹ :=  inv_nonneg.mpr (q_pos w).le
  have hv2 :=  mul_self_le_mul_self hv0 hv
  have hw2 :=  mul_self_le_mul_self hw0 hw
  nlinarith [norm_nonneg (velocity v-velocity w)]

lemma actual_small_sector_velocity {v w n : Vec} {φ : ℝ}
    (hn : ‖n‖ = 1) (hφ : 0  ≤  φ) (hw : (q w)⁻¹ ≤ φ/4)
    (hsource : ‖n-velocity v‖ ≤ φ/4)
    (hlo : φ^2/2 ≤ 1-dot n (velocity w))
    (hhi : 1-dot n (velocity w) ≤ 8*φ^2) :
    φ/2 ≤ ‖velocity v-velocity w‖ ∧ ‖velocity v-velocity w‖ ≤ 5*φ :=  by
  have hid :=  cone_angle_identity w n hn
  have hi0 : 0  ≤  (q w)⁻¹ :=  inv_nonneg.mpr (q_pos w).le
  have hi2 :=  mul_self_le_mul_self hi0 hw
  have hna0 :=  norm_nonneg (n-velocity w)
  have hnalow : 3*φ/4 ≤ ‖n-velocity w‖ :=  by nlinarith
  have hnahi : ‖n-velocity w‖ ≤ 4*φ :=  by nlinarith [sq_nonneg ((q w)⁻¹)]
  have hlo' : ‖n-velocity w‖ ≤ ‖n-velocity v‖+‖velocity v-velocity w‖ :=  by
    calc
      _  =  ‖(n-velocity v)+(velocity v-velocity w)‖ :=  by congr 1; abel
      _  ≤  _ :=  norm_add_le _ _
  have hhi' : ‖velocity v-velocity w‖ ≤ ‖n-velocity v‖+‖n-velocity w‖ :=  by
    calc
      _  =  ‖(velocity v-n)+(n-velocity w)‖ :=  by congr 1; abel
      _  ≤  ‖velocity v-n‖+‖n-velocity w‖ :=  norm_add_le _ _
      _  =  _ :=  by rw [norm_sub_rev (velocity v) n]
  exact ⟨by linarith,by linarith⟩

lemma stopping_modulus_on_stability_scale {M A P L massScale ang C ℓ Q : ℝ}
    (hM : 0  <  M) (hA : 0  ≤  A) (hP : 0  <  P) (hL : 0  ≤  L)
    (hm : 0  <  massScale) (hom : 0  <  ang) (hC : 0  <  C) (hℓ : 0  ≤  ℓ) (hQ : 0  <  Q)
    (hlen : ℓ  ≤  (C*(P/massScale)*(M/ang+Real.sqrt (A*L/ang)))⁻¹^2) :
    M*P*Real.sqrt ℓ+2*A*ℓ*P^2*L/Q  ≤
      massScale*ang/C+2*massScale^2*ang/(C^2*Q) :=  by
  let R :=  C*(P/massScale)*(M/ang+Real.sqrt (A*L/ang))
  have hR : 0  <  R :=  mul_pos (mul_pos hC (div_pos hP hm))
    (add_pos_of_pos_of_nonneg (div_pos hM hom) (Real.sqrt_nonneg _))
  have hsqrt : Real.sqrt ℓ ≤ R⁻¹ :=  by
    calc
      _  ≤  Real.sqrt (R⁻¹^2) :=  Real.sqrt_le_sqrt hlen
      _  =  _ :=  Real.sqrt_sq (inv_nonneg.mpr hR.le)
  have hfirst : M*P*R⁻¹ ≤ massScale*ang/C :=  by
    rw [← div_eq_mul_inv,div_le_div_iff₀ hR hC]
    have he : massScale*ang*R = M*P*C+massScale*ang*(C*(P/massScale))*Real.sqrt (A*L/ang) :=  by
      dsimp [R]
      field_simp
    rw [he]
    exact le_add_of_nonneg_right (by positivity)
  have hs0 : 0  ≤  A*L/ang :=  by positivity
  have hs : C*(P/massScale)*Real.sqrt (A*L/ang) ≤ R :=  by
    dsimp [R]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (div_nonneg hM.le hom.le)) (by positivity)
  have hs2 := (sq_le_sq₀ (by positivity : 0 ≤ C*(P/massScale)*Real.sqrt (A*L/ang)) hR.le).mpr hs
  rw [mul_pow,Real.sq_sqrt hs0] at hs2
  have hlen' : ℓ*R^2 ≤ 1 :=  by
    change ℓ ≤ R⁻¹^2 at hlen
    have hh :=  mul_le_mul_of_nonneg_right hlen (sq_nonneg R)
    simpa only [← mul_pow,inv_mul_cancel₀ hR.ne',one_pow] using hh
  have hproduct : ℓ*(C*(P/massScale))^2*(A*L/ang) ≤ 1 :=  by
    calc
      _  =  ℓ*((C*(P/massScale))^2*(A*L/ang)) :=  by ring
      _  ≤  ℓ*R^2 :=  mul_le_mul_of_nonneg_left hs2 hℓ
      _  ≤  1 :=  hlen'
  have hbase : A*ℓ*P^2*L ≤ massScale^2*ang/C^2 :=  by
    rw [le_div_iff₀ (sq_pos_of_pos hC)]
    have hh :=  mul_le_mul_of_nonneg_right hproduct (by positivity : 0  ≤  massScale^2*ang)
    have he : (ℓ*(C*(P/massScale))^2*(A*L/ang))*(massScale^2*ang) = (A*ℓ*P^2*L)*C^2 :=  by
      field_simp
    simpa only [he,one_mul] using hh
  apply add_le_add ((mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hM.le hP.le)).trans hfirst)
  have hh :=  mul_le_mul_of_nonneg_left hbase (show 0  ≤  2/Q by positivity)
  convert hh using 1  <;>  ring

lemma IncrementBootstrap.velocity_stability_scale {V : ℝ → Vec}
    {T M A P L a b r massScale ang C : ℝ}
    (H : IncrementBootstrap V T M A P L) (ha : 0  ≤  a) (hb : b ≤ T)
    (hr : r∈Icc a b) (hV : ContinuousOn V (Icc a b))
    (hM : 0  <  M) (hA : 0  ≤  A) (hP : 0  <  P) (hL : 0  ≤  L)
    (hm : 0  <  massScale) (hom : 0  <  ang) (hom1 : ang ≤ 1) (hC : 128 ≤ C)
    (hmq : massScale ≤ q (V r))
    (hlen : b-a ≤ (C*(P/massScale)*(M/ang+Real.sqrt (A*L/ang)))⁻¹^2) :
    ∀ t∈Icc a b, ‖V t-V r‖ ≤ massScale*ang/64 ∧
      ‖velocity (V t)-velocity (V r)‖ ≤ ang/32 ∧
      q (V r)/2 ≤ q (V t) ∧ q (V t) ≤ 2*q (V r) :=  by
  have hC0 : 0  <  C :=  by linarith
  have hε : massScale*ang/64 < q (V r)/2 :=  by
    have hh :=  mul_le_mul_of_nonneg_left hom1 hm.le
    nlinarith [q_pos (V r)]
  have hst :=  stopping_modulus_on_stability_scale hM hA hP hL hm hom hC0
    (sub_nonneg.mpr (hr.1.trans hr.2)) (q_pos (V r)) hlen
  have he₁ : massScale*ang/C ≤ massScale*ang/128 :=  div_le_div_of_nonneg_left (by positivity) (by norm_num) hC
  have he₂ : 2*massScale^2*ang/(C^2*q (V r)) ≤ massScale*ang/128 :=  by
    rw [div_le_div_iff₀ (mul_pos (sq_pos_of_pos hC0) (q_pos _)) (by norm_num : (0:ℝ) < 128)]
    have hC2 : (256:ℝ) ≤ C^2 :=  by nlinarith
    have hh :=  mul_le_mul_of_nonneg_left hmq (sq_nonneg C)
    have hh' : 256*massScale ≤ C^2*q (V r) :=
      (mul_le_mul_of_nonneg_right hC2 hm.le).trans hh
    have hfinal :=  mul_le_mul_of_nonneg_left hh' (by positivity : 0  ≤  massScale*ang)
    nlinarith
  have hstep : M*P*Real.sqrt (b-a)+2*A*(b-a)*P^2*L/q (V r) ≤ massScale*ang/64 :=  by
    linarith
  intro t ht
  obtain ⟨hg,hu,hq⟩ :=  H.velocity_stopped_about ha hb hr hV hM.le hA hP.le hL hε hstep t ht
  refine ⟨hg,hu.trans ?_,hq⟩
  rw [div_le_iff₀ (q_pos _)]
  have hh :=  mul_le_mul_of_nonneg_right hmq (show 0  ≤  ang/32 by positivity)
  nlinarith

end RVM

end

end OAI
