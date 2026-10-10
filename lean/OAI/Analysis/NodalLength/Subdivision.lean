import OAI.Analysis.NodalLength.GridImprovement

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace

namespace SharpNodal.Profiles
open Carleman

structure NormalizedPDEData (Cp : ℝ) where
  p : Plane → ℝ
  U : Plane → ℝ
  B : Plane
  S : ℝ
  K : ℝ
  d : ℝ
  smooth_p : ContDiffOn ℝ ∞ p (Metric.ball 0 1000)
  smooth_U : ContDiffOn ℝ ∞ U (Metric.ball 0 1000)
  S_pos : 0<S
  d_pos : 0<d
  coefficient_bound : ∀x∈Metric.ball (0:Plane) 1000,|p x|≤Cp
  equation : ∀x∈Metric.ball (0:Plane) 1000,euclideanLaplacian U x+K^2*p x*U x=0
  normalized : tiltedMass S B U d 0 (Metric.ball 0 1000)≤1
  parent_growth : (-1:EReal)≤logRate S (tiltedMass S B U d 0 (Metric.ball 0 1))

def NormalizedPDEData.Small {Cp : ℝ} (D : NormalizedPDEData Cp) (T : ℝ) : Prop :=
  T≤D.S ∧ |D.K/(D.S+‖D.B‖)|≤T⁻¹ ∧
  ∀i x,x∈Metric.ball (0:Plane) 1000 →
    |D.K^2*coordPartial D.p i x/(D.S*(D.S+‖D.B‖))|≤Cp*T⁻¹

def NormalizedPDEData.HasGridCorrection {Cp : ℝ} (D : NormalizedPDEData Cp)
    (A : ℕ) (Cs : ℝ) : Prop :=
  ∃c : Plane → Plane,((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,‖c y‖)≤Cs ∧
    gridMassesFinite A D.S D.B D.U D.d c ∧
    ((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,gridExcess A D.S D.B D.U D.d c y/D.S)<(A:ℝ)⁻¹/2

theorem uniform_normalized_subdivision : ∃A : ℕ,10000<A ∧ ∃Cs : ℝ,0≤Cs ∧
    ∀Cp : ℝ,∃C₀ : ℝ,0<C₀ ∧ ∀D : NormalizedPDEData Cp,
      D.Small C₀ → D.HasGridCorrection A Cs := by
  obtain ⟨A,hA,Cs,hCs,hseq⟩ := sequence_affine_improvement
  refine ⟨A,hA,Cs,hCs,?_⟩
  intro Cp
  by_contra hn
  push Not at hn
  have hf (j : ℕ) := hn ((j:ℝ)+1) (by positivity)
  choose D hs hbad using hf
  have hT : Tendsto (fun j : ℕ =>(j:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun _ =>le_add_of_nonneg_right (by norm_num)) tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun j : ℕ =>((j:ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hT
  have hS : Tendsto (fun j =>(D j).S) atTop atTop :=
    tendsto_atTop_mono (fun j =>(hs j).1) hT
  have hK : Tendsto (fun j =>(D j).K/((D j).S+‖(D j).B‖)) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ hinv
    intro j
    simpa only [Real.norm_eq_abs] using (hs j).2.1
  have he : Tendsto (fun j : ℕ =>Cp*((j:ℝ)+1)⁻¹) atTop (𝓝 0) := by
    simpa using hinv.const_mul Cp
  obtain ⟨φ,c,_hφ,hc,havg⟩ := hseq (fun j =>(D j).p) (fun j =>(D j).U)
    (fun j =>(D j).B) (fun j =>(D j).S) (fun j =>(D j).K)
    (fun j : ℕ =>Cp*((j:ℝ)+1)⁻¹) (fun j =>(D j).d) Cp
    (fun j =>(D j).smooth_p) (fun j =>(D j).smooth_U) (fun j =>(D j).S_pos)
    hS (fun j =>(D j).d_pos) hK (fun j =>(D j).coefficient_bound) he
    (fun j =>(hs j).2.2) (fun j =>(D j).equation)
    (fun j =>(D j).normalized) (fun j =>(D j).parent_growth)
  obtain ⟨j,hj⟩ := havg.exists
  exact hbad (φ j) ⟨c,hc,hj⟩

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

def centeredMass (T : Plane) (U : Plane → ℝ) (y : Plane) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻x in Metric.ball y r,ENNReal.ofReal ((Real.exp (-inner ℝ T (x-y))*U x)^2)

lemma centeredMass_mono (T : Plane) (U : Plane → ℝ) (y : Plane) {r R : ℝ}
    (hrR : r≤R) : centeredMass T U y r≤centeredMass T U y R :=
  lintegral_mono_set (Metric.ball_subset_ball hrR)

lemma tiltedMass_centered (S : ℝ) (B c : Plane) (U : Plane → ℝ) (d : ℝ)
    (hd : 0≤d) (y : Plane) (r : ℝ) :
    tiltedMass S B U d (fun x =>-inner ℝ c (x-y)) (Metric.ball y r)=
      ENNReal.ofReal (d*Real.exp (-2*inner ℝ B y))*centeredMass (B+S • c) U y r := by
  unfold tiltedMass centeredMass
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_mul (mul_nonneg hd (Real.exp_pos _).le)]
  congr 1
  have hw : tiltedWeight B S (fun x =>-(-inner ℝ c (x-y))) x=
      -inner ℝ B y-inner ℝ (B+S • c) (x-y) := by
    simp only [tiltedWeight,neg_neg,inner_add_left,real_inner_smul_left,inner_sub_right]
    ring
  rw [hw,sub_eq_add_neg,Real.exp_add]
  simp only [mul_pow]
  rw [← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show 2*(-inner ℝ B y)= -2*inner ℝ B y by ring]
  ring

lemma tilted_excess_centered (S : ℝ) (B c : Plane) (U : Plane → ℝ) (d : ℝ)
    (hd : 0<d) (y : Plane) (R r : ℝ) :
    massExcess (tiltedMass S B U d (fun x =>-inner ℝ c (x-y)) (Metric.ball y R))
      (tiltedMass S B U d (fun x =>-inner ℝ c (x-y)) (Metric.ball y r))=
    massExcess (centeredMass (B+S • c) U y R) (centeredMass (B+S • c) U y r) := by
  rw [tiltedMass_centered _ _ _ _ _ hd.le,tiltedMass_centered _ _ _ _ _ hd.le]
  apply massExcess_mul_left
  · exact ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hd (Real.exp_pos _))
  · exact ENNReal.ofReal_ne_top

lemma tilted_finite_centered {S : ℝ} {B c : Plane} {U : Plane → ℝ} {d : ℝ}
    (hd : 0<d) {y : Plane} {R r : ℝ}
    (hinner : tiltedMass S B U d (fun x =>-inner ℝ c (x-y)) (Metric.ball y r)≠0)
    (houter : tiltedMass S B U d (fun x =>-inner ℝ c (x-y)) (Metric.ball y R)≠⊤) :
    centeredMass (B+S • c) U y r≠0 ∧ centeredMass (B+S • c) U y R≠⊤ := by
  rw [tiltedMass_centered _ _ _ _ _ hd.le] at hinner houter
  refine ⟨fun h =>hinner (by simp [h]),?_⟩
  intro h
  apply houter
  rw [h,ENNReal.mul_top]
  exact ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hd (Real.exp_pos _))

lemma centeredMass_weight_bound (T T' : Plane) (U : Plane → ℝ) (y : Plane) {r : ℝ}
    : centeredMass T U y r≤
      ENNReal.ofReal (Real.exp (2*‖T-T'‖*r))*centeredMass T' U y r := by
  unfold centeredMass
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_pow,mul_pow,← Real.exp_nat_mul,← Real.exp_nat_mul]
  simp only [Nat.cast_ofNat]
  rw [← mul_assoc,← Real.exp_add]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Real.exp_le_exp.mpr
  have hnorm : ‖x-y‖≤r := by simpa [dist_eq_norm] using (Metric.mem_ball.mp hx).le
  have hi : -inner ℝ (T-T') (x-y)≤‖T-T'‖*r :=
    (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)))
  rw [inner_sub_left] at hi
  linarith

lemma massExcess_log_sub {a b : ℝ≥0∞} (ha0 : a≠0) (hat : a≠⊤) (hb0 : b≠0) (hbt : b≠⊤) :
    massExcess a b=(Real.log a.toReal-Real.log b.toReal)/2 := by
  unfold massExcess
  rw [Real.log_div (ENNReal.toReal_ne_zero.mpr ⟨ha0,hat⟩) (ENNReal.toReal_ne_zero.mpr ⟨hb0,hbt⟩)]

lemma massExcess_weight_bound {a b c d : ℝ≥0∞} {α β : ℝ}
    (ha0 : a≠0) (hat : a≠⊤) (hb0 : b≠0) (hbt : b≠⊤)
    (hc0 : c≠0) (hct : c≠⊤) (hd0 : d≠0) (hdt : d≠⊤)
    (hac : a≤ENNReal.ofReal (Real.exp (2*α))*c)
    (hdb : d≤ENNReal.ofReal (Real.exp (2*β))*b) :
    massExcess a b≤ massExcess c d+α+β := by
  have haa := (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hct) hac)
  have hdd := (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbt) hdb)
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos _).le] at haa hdd
  have hal := Real.log_le_log (ENNReal.toReal_pos ha0 hat) haa
  have hdl := Real.log_le_log (ENNReal.toReal_pos hd0 hdt) hdd
  rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ENNReal.toReal_ne_zero.mpr ⟨hc0,hct⟩),Real.log_exp] at hal
  rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ENNReal.toReal_ne_zero.mpr ⟨hb0,hbt⟩),Real.log_exp] at hdl
  rw [massExcess_log_sub ha0 hat hb0 hbt,massExcess_log_sub hc0 hct hd0 hdt]
  linarith

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma profile_zero_on_ball {Ω : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuous V) (hneg : ∀x∈Ω,V x≤0)
    (htest : FullTestProperty Ω V) {a : Plane} {r : ℝ} (hr : 0<r)
    (hball : Metric.ball a r⊆Ω) (ha : V a=0) :
    ∀x∈Metric.ball a r,V x=0 := by
  have hint := disk_submean (hV.upperSemicontinuousOn _) hneg htest hr hball
  rw [ha,neg_zero,EReal.toENNReal_zero,mul_zero] at hint
  have hz := (lintegral_eq_zero_iff'
    (usc_neg_toENNReal_aemeasurable measurableSet_ball (hV.upperSemicontinuousOn _))).mp
      (le_antisymm hint (bot_le))
  have hle : ∀ᵐx ∂(volume.restrict (Metric.ball a r)),0≤V x := by
    filter_upwards [hz] with x hx
    have := EReal.toENNReal_eq_zero_iff.mp hx
    simpa only [EReal.neg_le_zero] using this
  have ht0 : volume (Metric.ball a r ∩ V ⁻¹' Iio 0)=0 := by
    have hh := ae_imp_of_ae_restrict hle
    simpa only [ae_iff,Classical.not_imp,not_le,Set.inter_def,Set.preimage,Set.mem_Iio,Set.mem_ofPred_eq] using hh
  have ht := (Metric.isOpen_ball.inter (hV.isOpen_preimage 0)).eq_empty_of_measure_zero ht0
  intro x hx
  refine le_antisymm (hneg x (hball hx)) ?_
  by_contra hn
  have hx' : x∈Metric.ball a r ∩ V ⁻¹' Iio 0 := ⟨hx,lt_of_not_ge hn⟩
  rw [ht] at hx'
  exact hx'

theorem profile_strong_maximum {Ω : Set Plane} {V : Plane → EReal}
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hV : UpperSemicontinuous V)
    (hneg : ∀x∈Ω,V x≤0) (htest : FullTestProperty Ω V)
    {a : Plane} (haΩ : a∈Ω) (ha : V a=0) : ∀x∈Ω,V x=0 := by
  let Z : Set Plane := Ω ∩ {x | V x=0}
  have hZ : IsOpen Z := by
    apply Metric.isOpen_iff.mpr
    intro x hx
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hΩ x hx.1
    refine ⟨r,hr,fun y hy =>⟨hball hy,?_⟩⟩
    exact profile_zero_on_ball hV hneg htest hr hball hx.2 y hy
  have hd : Disjoint Z (V ⁻¹' Iio 0) := by
    apply Set.disjoint_left.mpr
    intro x hx hx'
    exact (not_lt_of_ge (ge_of_eq hx.2)) hx'
  have hcover : Ω⊆Z ∪ V ⁻¹' Iio 0 := by
    intro x hx
    rcases (hneg x hx).eq_or_lt with hz | hn
    · exact Or.inl ⟨hx,hz⟩
    · exact Or.inr hn
  have hs := hconn.subset_left_of_subset_union hZ (hV.isOpen_preimage 0) hd
    hcover ⟨a,haΩ,haΩ,ha⟩
  exact fun _ hx =>(hs hx).2

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma centeredMass_ne_zero_of {T T' : Plane} {U : Plane → ℝ} {y : Plane} {r : ℝ}
    (h : centeredMass T U y r≠0) : centeredMass T' U y r≠0 := by
  intro hz
  have hh := centeredMass_weight_bound T T' U y (r:=r)
  rw [hz,mul_zero] at hh
  exact h (le_antisymm hh bot_le)

lemma centeredMass_ne_top_of {T T' : Plane} {U : Plane → ℝ} {y : Plane} {r : ℝ}
    (h : centeredMass T U y r≠⊤) : centeredMass T' U y r≠⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h)
    (centeredMass_weight_bound T' T U y)

lemma centered_excess_nonneg {T : Plane} {U : Plane → ℝ} {y : Plane} {r R : ℝ}
    (hrR : r ≤ R) (hm0 : centeredMass T U y r≠0) (hmt : centeredMass T U y R≠⊤) :
    0 ≤ massExcess (centeredMass T U y R) (centeredMass T U y r) := by
  have hmono := centeredMass_mono T U y hrR
  have hrt := ne_top_of_le_ne_top hmt hmono
  have hrpos := ENNReal.toReal_pos hm0 hrt
  have hm := ENNReal.toReal_mono hmt hmono
  unfold massExcess
  apply div_nonneg _ (by norm_num)
  apply Real.log_nonneg
  exact (le_div_iff₀ hrpos).mpr (by simpa using hm)

lemma centered_excess_weight_bound {T T' : Plane} {U : Plane → ℝ} {y : Plane} {r R : ℝ}
    (hrR : r ≤ R) (hm0 : centeredMass T U y r≠0) (hmt : centeredMass T U y R≠⊤) :
    massExcess (centeredMass T U y R) (centeredMass T U y r) ≤
      massExcess (centeredMass T' U y R) (centeredMass T' U y r)+(R+r)*‖T-T'‖ := by
  have hmono := centeredMass_mono T U y hrR
  have hmono' := centeredMass_mono T' U y hrR
  have hm0' : centeredMass T' U y r≠0 := centeredMass_ne_zero_of hm0
  have hmt' : centeredMass T' U y R≠⊤ := centeredMass_ne_top_of hmt
  have hR0 := ne_of_gt ((pos_iff_ne_zero.mpr hm0).trans_le hmono)
  have hR0' := ne_of_gt ((pos_iff_ne_zero.mpr hm0').trans_le hmono')
  have hrt := ne_top_of_le_ne_top hmt hmono
  have hrt' := ne_top_of_le_ne_top hmt' hmono'
  have hh := massExcess_weight_bound (α:=‖T-T'‖*R) (β:=‖T-T'‖*r)
    hR0 hmt hm0 hrt hR0' hmt' hm0' hrt'
    (by simpa only [mul_assoc] using centeredMass_weight_bound T T' U y (r:=R))
    (by simpa only [norm_sub_rev,mul_assoc] using centeredMass_weight_bound T' T U y (r:=r))
  nlinarith only [hh]

lemma normalized_inner_rate_eq {S : ℝ} {B : Plane} {U : Plane → ℝ} {Ω G : Set Plane}
    (hGΩ : G⊆Ω) (hm0 : tiltedMass S B U 1 0 G≠0) (hmt : tiltedMass S B U 1 0 Ω≠⊤) :
    logRate S (tiltedMass S B U (tiltedMass S B U 1 0 Ω).toReal⁻¹ 0 G)=
      ((-massExcess (tiltedMass S B U 1 0 Ω) (tiltedMass S B U 1 0 G)/S:ℝ):EReal) := by
  let a := tiltedMass S B U 1 0 Ω
  let b := tiltedMass S B U 1 0 G
  have hba : b ≤ a := tiltedMass_mono_set _ _ _ _ _ hGΩ
  have ha0 : a≠0 := ne_of_gt ((pos_iff_ne_zero.mpr hm0).trans_le hba)
  have hbt : b≠⊤ := ne_top_of_le_ne_top hmt hba
  have ha : 0<a.toReal := ENNReal.toReal_pos ha0 hmt
  have hb : 0<b.toReal := ENNReal.toReal_pos hm0 hbt
  have heq : tiltedMass S B U a.toReal⁻¹ 0 G=ENNReal.ofReal a.toReal⁻¹*b := by
    simpa using tiltedMass_const_mul S B U a.toReal⁻¹ 1 (inv_pos.mpr ha).le 0 G
  rw [heq,logRate_real (mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr ha)) hm0)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbt),ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_pos.mpr ha).le]
  congr 1
  change Real.log (a.toReal⁻¹*b.toReal)/(2*S)= -massExcess a b/S
  rw [massExcess_log_sub ha0 hmt hm0 hbt,Real.log_mul (inv_ne_zero (ne_of_gt ha)) (ne_of_gt hb),Real.log_inv]
  ring

lemma tiltedMass_weight_mono {S : ℝ} (hS : 0 ≤ S) (B : Plane) (U : Plane → ℝ)
    {d : ℝ} (hd : 0 ≤ d) {f g : Plane → ℝ} {E : Set Plane} (hE : MeasurableSet E)
    (hfg : ∀x∈E,f x ≤ g x) : tiltedMass S B U d f E ≤ tiltedMass S B U d g E := by
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hE] with x hx
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ hd
  simp only [mul_pow,← Real.exp_nat_mul,Nat.cast_ofNat]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Real.exp_le_exp.mpr
  simp only [tiltedWeight]
  nlinarith [mul_le_mul_of_nonneg_left (hfg x hx) hS]

lemma tiltedMass_weight_add_const (S : ℝ) (B : Plane) (U : Plane → ℝ) {d : ℝ}
    (_hd : 0 ≤ d) (f : Plane → ℝ) (a : ℝ) (E : Set Plane) :
    tiltedMass S B U d (fun x =>f x+a) E=ENNReal.ofReal (Real.exp (2*S*a))*tiltedMass S B U d f E := by
  unfold tiltedMass
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  have hw : tiltedWeight B S (fun y =>-(f y+a)) x=tiltedWeight B S (fun y =>-f y) x+S*a := by
    simp only [tiltedWeight]
    ring
  rw [hw,Real.exp_add,mul_pow,mul_pow,mul_pow]
  simp only [← Real.exp_nat_mul,Nat.cast_ofNat]
  rw [show 2*(S*a)=2*S*a by ring]
  ring

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma tiltedMass_zero_center (S : ℝ) (B : Plane) (U : Plane → ℝ) (d r : ℝ)
    (hd : 0≤d) :
    tiltedMass S B U d 0 (Metric.ball 0 r)=ENNReal.ofReal d*centeredMass B U 0 r := by
  change tiltedMass S B U d (fun _ => 0) (Metric.ball 0 r)=_
  simpa using tiltedMass_centered S B 0 U d hd 0 r

theorem one_subdivision : ∃A : ℕ,10000<A ∧ ∃C₁ : ℝ,0<C₁ ∧
    ∀Cp : ℝ,0≤Cp → ∃C₀ : ℝ,0<C₀ ∧
    ∀(p U : Plane → ℝ) (b : Plane) (K S s : ℝ),
    ContDiffOn ℝ ∞ p (Metric.ball 0 1000) →
    ContDiffOn ℝ ∞ U (Metric.ball 0 1000) →
    0 < K → 0 ≤ s → C₀ ≤ S →
    (∀x∈Metric.ball (0:Plane) 1000,|p x|≤Cp) →
    (∀i x,x∈Metric.ball (0:Plane) 1000 → |coordPartial p i x|≤Cp*s) →
    (∀x∈Metric.ball (0:Plane) 1000,euclideanLaplacian U x+K^2*p x*U x=0) →
    centeredMass (K • b) U 0 1≠0 → centeredMass (K • b) U 0 1000≠⊤ →
    massExcess (centeredMass (K • b) U 0 1000) (centeredMass (K • b) U 0 1)≤S →
    K/(S+‖K • b‖)≤C₀⁻¹ → K^2*s/(S*(S+‖K • b‖))≤C₀⁻¹ →
    ∃b' : Plane → Plane,
      ((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,‖b' y-b‖)≤C₁*S/K ∧
      (∀y∈gridCenters A,centeredMass (K • b' y) U y ((A:ℝ)⁻¹)≠0 ∧
        centeredMass (K • b' y) U y (1000*(A:ℝ)⁻¹)≠⊤) ∧
      ((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,
        massExcess (centeredMass (K • b' y) U y (1000*(A:ℝ)⁻¹))
          (centeredMass (K • b' y) U y ((A:ℝ)⁻¹))/(K*(A:ℝ)⁻¹))≤S/(2*K) := by
  obtain ⟨A,hA,Cs,hCs,hu⟩ := uniform_normalized_subdivision
  refine ⟨A,hA,Cs+1,by linarith,?_⟩
  intro Cp hCp
  obtain ⟨C₀,hC₀,hcorr⟩ := hu Cp
  refine ⟨C₀,hC₀,?_⟩
  intro p U b K S s hp hU hK _hs hSmin hpb hpd hPDE hm0 hmt hE hsmall hsmall'
  have hS : 0<S := hC₀.trans_le hSmin
  let B : Plane := K • b
  have hmass (r : ℝ) : tiltedMass S B U 1 0 (Metric.ball 0 r)=centeredMass B U 0 r := by
    simpa using tiltedMass_zero_center S B U 1 r (by norm_num)
  have hmono := centeredMass_mono B U 0 (show (1:ℝ)≤1000 by norm_num)
  have hmouter : centeredMass B U 0 1000≠0 := ne_of_gt ((pos_iff_ne_zero.mpr hm0).trans_le hmono)
  obtain ⟨hd,hnorm⟩ := tiltedMass_normalized (S:=S) (B:=B) (U:=U) (Ω:=Metric.ball 0 1000) (by simpa only [hmass] using hmouter)
    (by simpa only [hmass] using hmt)
  let D : NormalizedPDEData Cp := {
    p:=p, U:=U, B:=B, K:=K, S:=S, d:=(tiltedMass S B U 1 0 (Metric.ball 0 1000)).toReal⁻¹
    smooth_p:=hp, smooth_U:=hU, S_pos:=hS, d_pos:=hd, coefficient_bound:=hpb
    equation:=hPDE, normalized:=hnorm.le
    parent_growth:=normalized_inner_rate hS (Metric.ball_subset_ball (by norm_num))
      (by simpa only [hmass] using hm0) (by simpa only [hmass] using hmt)
      (by simpa only [hmass] using hE) }
  have hD : D.Small C₀ := by
    refine ⟨hSmin,?_,?_⟩
    · change |K/(S+‖B‖)|≤C₀⁻¹
      rw [abs_of_pos (div_pos hK (add_pos_of_pos_of_nonneg hS (norm_nonneg _)))]
      exact hsmall
    · intro i x hx
      change |K^2*coordPartial p i x/(S*(S+‖B‖))|≤Cp*C₀⁻¹
      have hden : 0<S*(S+‖B‖) := mul_pos hS (add_pos_of_pos_of_nonneg hS (norm_nonneg _))
      rw [abs_div,abs_mul,abs_of_nonneg (sq_nonneg K),abs_of_pos hden]
      calc
        _ ≤ K^2*(Cp*s)/(S*(S+‖B‖)) := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hpd i x hx) (sq_nonneg K)) hden.le
        _ = Cp*(K^2*s/(S*(S+‖B‖))) := by ring
        _ ≤ Cp*C₀⁻¹ := mul_le_mul_of_nonneg_left hsmall' hCp
  obtain ⟨c,hc,hfinite,havg⟩ := hcorr D hD
  let b' : Plane → Plane := fun y => b+(S/K) • c y
  have hb' (y : Plane) : K • b' y=B+S • c y := by
    simp only [b',smul_add,smul_smul,B]
    rw [mul_div_cancel₀ _ (ne_of_gt hK)]
  refine ⟨b',?_,?_,?_⟩
  · have hc' : ((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,‖b' y-b‖)=
        (S/K)*(((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,‖c y‖)) := by
      simp only [b',add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hS hK)]
      rw [← Finset.mul_sum]
      ring
    rw [hc']
    have hh := mul_le_mul_of_nonneg_left hc (div_pos hS hK).le
    change (S/K)*(((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,‖c y‖))≤(Cs+1)*S/K
    exact hh.trans (by
      calc
        (S/K)*Cs ≤ (S/K)*(Cs+1) := mul_le_mul_of_nonneg_left (by linarith) (div_pos hS hK).le
        _ = (Cs+1)*S/K := by ring)
  · intro y hy
    rw [hb']
    exact tilted_finite_centered hd (hfinite y hy).1 (hfinite y hy).2
  · have hAr : 0<(A:ℝ) := Nat.cast_pos.mpr (by omega)
    have hρ : 0<(A:ℝ)⁻¹ := inv_pos.mpr hAr
    have hex (y : Plane) :
        massExcess (centeredMass (K • b' y) U y (1000*(A:ℝ)⁻¹))
          (centeredMass (K • b' y) U y ((A:ℝ)⁻¹))=gridExcess A S B U D.d c y := by
      rw [hb']
      exact (tilted_excess_centered S B (c y) U D.d hd y _ _).symm
    simp_rw [hex]
    have heq : ((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,gridExcess A S B U D.d c y/(K*(A:ℝ)⁻¹))=
        (S/(K*(A:ℝ)⁻¹))*(((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,gridExcess A S B U D.d c y/S)) := by
      rw [← Finset.sum_div,← Finset.sum_div]
      field_simp
    rw [heq]
    have hh := mul_le_mul_of_nonneg_left havg.le (div_pos hS (mul_pos hK hρ)).le
    convert hh using 1; first | rfl | field_simp

end SharpNodal.Profiles

end
end
end
end
end

end OAI
