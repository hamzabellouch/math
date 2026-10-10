import Mathlib
import OAI.Probability.SKFluctuations.GaussianRootTransversality
import OAI.Probability.SKFluctuations.ScalarGapFourth
import OAI.Probability.SKFluctuations.TransformedDensityShape

namespace OAI

/-! Mass Response Jet. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

noncomputable def HeatJet.massResponseFamily (J : HeatJet 0)
    (hS : ∀ k i, BddSmooth k (J.G i)) {b : ℝ} (hb : 0 < b) (D : ℝ) : HeatJetFamily 0 :=
  (((J.scalarJetFamily hS hb 0).square).reparam (fun s => D-s)
    (continuous_const.sub continuous_id)).evolveTest (J.evolve hb D) hb id continuous_id

 theorem HeatJet.massResponseFamily_F (J : HeatJet 0)
    (hS : ∀ k i, BddSmooth k (J.G i)) {b : ℝ} (hb : 0 < b) (D s : ℝ) :
    ((J.massResponseFamily hS hb D).J s).F=(J.evolve hb D).F := rfl

 theorem HeatJet.massResponseFamily_A (J : HeatJet 0)
    (hS : ∀ k i, BddSmooth k (J.G i)) {b : ℝ} (hb : 0 < b) (D s : ℝ) :
    ((J.massResponseFamily hS hb D).J s).A=J.massEnergy b hb D s := by
  funext x
  change clockTest b (J.evolve hb (D-s)).F
    (fun y => (J.scalarClockJet b 1 (D-s) y)^2) s x = J.massEnergy b hb D s x
  have he : (fun y => (J.scalarClockJet b 1 (D-s) y)^2)=
      (J.evolve hb (D-s)).potentialEnergy := by
    funext y
    rw [J.scalarClockJet_one hb]
    change (J.evolve hb (D-s)).G 0 y ^ 2 = ∑ i : Fin 1, (J.evolve hb (D-s)).G i y ^ 2
    rw [Fin.sum_univ_one]
  rw [he]
  rfl

noncomputable def HeatJet.massResponseJet (J : HeatJet 0)
    (hS : ∀ k i, BddSmooth k (J.G i)) {b : ℝ} (hb : 0 < b) (D : ℝ) : HeatJet 0 :=
  (J.massResponseFamily hS hb D).integralTest (J.evolve hb D) (volume.restrict (Ioc 0 D))

 theorem HeatJet.massResponseJet_F (J : HeatJet 0)
    (hS : ∀ k i, BddSmooth k (J.G i)) {b : ℝ} (hb : 0 < b) (D : ℝ) :
    (J.massResponseJet hS hb D).F=(J.evolve hb D).F := rfl

 theorem HeatJet.massResponseJet_A (J : HeatJet 0)
    (hS : ∀ k i, BddSmooth k (J.G i)) {b D : ℝ} (hb : 0 < b) (hD : 0 ≤ D)
    (x : Fin 1 → ℝ) :
    (J.massResponseJet hS hb D).A x=∫ s in 0..D, J.massEnergy b hb D s x := by
  change (∫ s in Ioc 0 D, ((J.massResponseFamily hS hb D).J s).A x)=_
  simp only [J.massResponseFamily_A hS hb,intervalIntegral.integral_of_le hD]

 theorem HeatJet.massEnergy_abs_le_one (J : HeatJet 0)
    (hG : ∀ y, |J.G 0 y| ≤ 1) {b : ℝ} (hb : 0 < b) (a D s : ℝ) (x : Fin 1 → ℝ) :
    |J.massEnergy a hb D s x| ≤ 1 := by
  apply clockTest_abs_le (J.evolve hb (D-s)).lipschitz (J.evolve hb (D-s)).smoothPotentialEnergy
  intro y
  simp only [HeatJet.potentialEnergy,Nat.reduceAdd,Fin.sum_univ_one]
  have hh := clockTest_abs_le J.lipschitz (J.smoothG 0) hG b (D-s) y
  change |((J.evolve hb (D-s)).G 0 y)^2| ≤ _
  have hh' : |(J.evolve hb (D-s)).G 0 y| ≤ 1 := hh
  rw [abs_pow]
  nlinarith [abs_nonneg ((J.evolve hb (D-s)).G 0 y)]

 theorem HeatJet.massResponseJet_abs_le (J : HeatJet 0)
    (hS : ∀ k i, BddSmooth k (J.G i)) (hG : ∀ y, |J.G 0 y| ≤ 1)
    {b D : ℝ} (hb : 0 < b) (hD : 0 ≤ D) (x : Fin 1 → ℝ) :
    |(J.massResponseJet hS hb D).A x| ≤ D := by
  rw [J.massResponseJet_A hS hb hD]
  simpa only [Real.norm_eq_abs,sub_zero,abs_of_nonneg hD,one_mul] using
    intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=D) (C:=1)
      (f:=fun s => J.massEnergy b hb D s x)
      (fun s _ => by simpa only [Real.norm_eq_abs] using J.massEnergy_abs_le_one hG hb b D s x)

 theorem HeatJet.massResponseJet_profileTest (J : HeatJet 0)
    (hS : ∀ k i, BddSmooth k (J.G i)) {b : ℝ} (hb : 0 < b) (D : ℝ)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (x : Fin 1 → ℝ) :
    (J.massResponseJet hS hb D).nonnegativeProfileTest α l t x=
      ∫ s in Ioc 0 D, ((J.massResponseFamily hS hb D).J s).nonnegativeProfileTest α l t x :=
  (J.massResponseFamily hS hb D).nonnegativeProfileTest_integral (J.evolve hb D)
    (J.massResponseFamily_F hS hb D) _ α hα l t x

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem hasDerivAt_of_quadratic_remainder {f : ℝ → ℝ} {d M b : ℝ}
    (hr : ∀ᶠ a in 𝓝 b, |f a-f b-(a-b)*d| ≤ M*|a-b|^2) : HasDerivAt f d b := by
  rw [hasDerivAt_iff_tendsto]
  have hlim : Tendsto (fun a : ℝ => M*|a-b|) (𝓝 b) (𝓝 0) := by
    simpa only [id_eq,sub_self,abs_zero,mul_zero] using
      ((tendsto_id.sub_const b).abs.const_mul M :
        Tendsto (fun a : ℝ => M*|a-b|) (𝓝 b) (𝓝 (M*|b-b|)))
  apply squeeze_zero' (Eventually.of_forall fun _ => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)) _ hlim
  filter_upwards [hr] with a ha
  simp only [Real.norm_eq_abs,smul_eq_mul]
  apply (mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr (abs_nonneg (a-b)))).trans
  by_cases he : a=b
  · subst a; simp
  · have hn : |a-b| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr he)
    apply le_of_eq
    field_simp

 theorem HeatJet.massContinuation_quadratic (J : HeatJet 0)
    (hS : ∀ k i, BddSmooth k (J.G i)) (hG : ∀ y, |J.G 0 y| ≤ 1)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {a D : ℝ}, 0 < a → a ≤ 1 → 0 ≤ D → ∀ x : Fin 1 → ℝ,
      |clockContinuation a J.F D x-((J.massResponseJet hS hb D).F x+
        (a-b)/2*(J.massResponseJet hS hb D).A x)| ≤ (a-b)^2*K*D^2/2 := by
  obtain ⟨K,hK,hbK⟩ := J.massEnergy_mass_bound hS hG hb hb1
  refine ⟨K,hK,?_⟩
  intro a D ha ha1 hD x
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=0) (b:=D) (C:=|a-b| *K*D)
    (f:=fun s => J.massEnergy a hb D s x-J.massEnergy b hb D s x) (fun s hs => by
      rw [uIoc_of_le hD] at hs
      simpa only [Real.norm_eq_abs] using (hbK ha.le ha1 hs.1.le hs.2 x).trans
        (mul_le_mul_of_nonneg_left hs.2 (mul_nonneg (abs_nonneg _) hK)))
  rw [intervalIntegral.integral_sub ((J.continuous_massEnergy a hb D x).intervalIntegrable 0 D)
    ((J.continuous_massEnergy b hb D x).intervalIntegrable 0 D)] at hi
  simp only [Real.norm_eq_abs,sub_zero,abs_of_nonneg hD] at hi
  rw [J.massResponseJet_F hS hb,J.massResponseJet_A hS hb hD]
  change |clockContinuation a J.F D x-(clockContinuation b J.F D x+
    (a-b)/2*(∫ s in 0..D, J.massEnergy b hb D s x))| ≤ _
  rw [show clockContinuation a J.F D x-(clockContinuation b J.F D x+
    (a-b)/2*(∫ s in 0..D, J.massEnergy b hb D s x))=
    (clockContinuation a J.F D x-clockContinuation b J.F D x)-
      (a-b)/2*(∫ s in 0..D, J.massEnergy b hb D s x) by ring]
  rw [J.mass_difference_integral ha hb hD,← mul_sub,abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply (mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ |a-b|/2)).trans
  apply le_of_eq
  rw [← sq_abs (a-b)]
  ring

 theorem HeatJet.profile_mass_quadratic (J : HeatJet 0)
    (hS : ∀ k i, BddSmooth k (J.G i)) (hG : ∀ y, |J.G 0 y| ≤ 1)
    {b D : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hD : 0 ≤ D)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {a : ℝ} (ha : 0 < a), a ≤ 1 → ∀ x : Fin 1 → ℝ,
      |(J.evolve ha D).nonnegativeProfileValue α l t x-
        (J.evolve hb D).nonnegativeProfileValue α l t x-
        (a-b)*(1/2*(J.massResponseJet hS hb D).nonnegativeProfileTest α l t x)|
      ≤ M*|a-b|^2 := by
  obtain ⟨K,hK,hbK⟩ := J.massContinuation_quadratic hS hG hb hb1
  refine ⟨K*D^2/2+(D+1)^2,by positivity,?_⟩
  intro a ha ha1 x
  have he := (J.massResponseJet hS hb D).nonnegativeProfile_response_error (J.evolve ha D)
    (K:=D+1) (s:=(a-b)/2) (E:=(a-b)^2*K*D^2/2) (by linarith)
    (fun y => (J.massResponseJet_abs_le hS hG hb hD y).trans (by linarith))
    (fun y => hbK ha ha1 hD y) α hα l t x
  have hf := HeatJet.nonnegativeProfileValue_congr_potential
    (J.massResponseJet hS hb D) (J.evolve hb D) (J.massResponseJet_F hS hb D) α l t
  rw [hf] at he
  rw [show (a-b)*(1/2*(J.massResponseJet hS hb D).nonnegativeProfileTest α l t x)=
    (a-b)/2*(J.massResponseJet hS hb D).nonnegativeProfileTest α l t x by ring]
  exact he.trans_eq (by rw [sq_abs]; ring)

noncomputable def HeatJet.massClockProfileValue (J : HeatJet 0) (D : ℝ)
    (α : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0) (x : Fin 1 → ℝ) (a : ℝ) : ℝ :=
  if ha : 0 < a then (J.evolve ha D).nonnegativeProfileValue α l t x else 0

 theorem HeatJet.hasDerivAt_massClockProfileValue (J : HeatJet 0)
    (hS : ∀ k i, BddSmooth k (J.G i)) (hG : ∀ y, |J.G 0 y| ≤ 1)
    {b D : ℝ} (hb : 0 < b) (hb1 : b < 1) (hD : 0 ≤ D)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (x : Fin 1 → ℝ) :
    HasDerivAt (J.massClockProfileValue D α l t x)
      (1/2*(J.massResponseJet hS hb D).nonnegativeProfileTest α l t x) b := by
  obtain ⟨M,_hM,hbM⟩ := J.profile_mass_quadratic hS hG hb hb1.le hD α hα l t
  apply hasDerivAt_of_quadratic_remainder (M:=M)
  filter_upwards [Ioo_mem_nhds hb hb1] with a ha
  simpa only [HeatJet.massClockProfileValue,dite_eq_left ha.1,dite_eq_left hb] using hbM ha.1 ha.2.le x

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Scalar
open MeasureTheory Filter Set
open scoped Topology

theorem derivative_nonneg_of_left_max {B : ℝ → ℝ} {d L : ℝ}
    (hL : 0 < L) (hd : HasDerivAt B d L) (hB : ∀ p ∈ Ioo 0 L, B p ≤ B L) : 0 ≤ d := by
  apply ge_of_tendsto (hd.tendsto_slope.mono_left (nhdsLT_le_nhdsNE L))
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ p : ℝ in 𝓝[<] L, 0 < p from
      nhdsWithin_le_nhds (Ioi_mem_nhds hL))] with p hp hp0
  rw [slope_def_field]
  exact div_nonneg_of_nonpos (sub_nonpos.mpr (hB p ⟨hp0,hp⟩)) (sub_nonpos.mpr hp.le)

theorem cumulative_endpoint {Q : ℝ → ℝ} {a L : ℝ} (hL : 0 < L) (hc : Continuous Q)
    (hb : ∀ s ∈ Ioc 0 L, (∫ r in 0..s, Q r) ≤ a*s^2/2)
    (he : (∫ r in 0..L, Q r) = a*L^2/2) : a*L ≤ Q L := by
  let B := fun s => (∫ r in 0..s, Q r)-a*s^2/2
  have hd : HasDerivAt B (Q L-a*L) L := by
    have hi := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 L)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
    convert hi.sub (((hasDerivAt_id L).pow 2).const_mul a |>.div_const 2) using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  have hB : B L = 0 := by dsimp [B]; rw [he,sub_self]
  have hh := derivative_nonneg_of_left_max hL hd (by
    intro p hp
    rw [hB]
    exact sub_nonpos.mpr (hb p ⟨hp.1,hp.2.le⟩))
  linarith

theorem cumulative_initial_slope {Q E : ℝ → ℝ} {a L : ℝ} (hL : 0 < L)
    (hc : Continuous Q) (he : ContinuousAt E 0) (h0 : Q 0 = 0)
    (hd : ∀ s ∈ Ioo 0 L, HasDerivAt Q (E s) s)
    (hb : ∀ s ∈ Ioc 0 L, (∫ r in 0..s, Q r) ≤ a*s^2/2) : E 0 ≤ a := by
  by_contra! ha
  obtain ⟨δ,hδ,hnear⟩ := Metric.eventually_nhds_iff.mp (he.eventually (Ioi_mem_nhds ha))
  let r := min (δ/2) (L/2)
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hrδ : r < δ := (min_le_left _ _).trans_lt (by linarith)
  have hrL : r < L := (min_le_right _ _).trans_lt (by linarith)
  have hepos : ∀ s ∈ Icc 0 r, a < E s := by
    intro s hs
    apply hnear
    rw [Real.dist_eq,sub_zero,abs_of_nonneg hs.1]
    exact hs.2.trans_lt hrδ
  have hlin : Continuous (fun s : ℝ => a*s) := continuous_const.mul continuous_id
  have hdiff : Continuous (fun s => Q s-a*s) := hc.sub hlin
  have hmono : StrictMonoOn (fun s => Q s-a*s) (Icc 0 r) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (f':=fun s => E s-a) (convex_Icc _ _) hdiff.continuousOn
    · intro s hs
      have hs' : s ∈ Ioo 0 r := by simpa only [interior_Icc] using hs
      simpa only [mul_one,id_eq] using ((hd s ⟨hs'.1,hs'.2.trans hrL⟩).fun_sub
        ((hasDerivAt_id s).const_mul a)).hasDerivWithinAt (s:=interior (Icc 0 r))
    · intro s hs
      have hs' : s ∈ Ioo 0 r := by simpa only [interior_Icc] using hs
      exact sub_pos.mpr (hepos s ⟨hs'.1.le,hs'.2.le⟩)
  have hpos : 0 < ∫ s in 0..r, Q s-a*s := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (hdiff.intervalIntegrable _ _) _ hr
    intro s hs
    have hh := hmono ⟨le_rfl,hr.le⟩ ⟨hs.1.le,hs.2.le⟩ hs.1
    simpa only [h0,mul_zero,sub_zero] using hh
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) (hlin.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,integral_id] at hpos
  have hh := hb r ⟨hr,hrL.le⟩
  norm_num at hpos
  nlinarith

end SKFluctuations.Scalar

 

 

namespace SKFluctuations.Scalar.PhysicalSlopeSlice
open Set Filter MeasureTheory
open scoped Topology
variable {m : ℝ} (S : PhysicalSlopeSlice m)

noncomputable def generalL (D : ℝ → ℝ) (x : ℝ) : ℝ :=
  S.κ x-S.z x*(D x+S.A x+S.z x)
noncomputable def generalR₁ (D : ℝ → ℝ) (x : ℝ) : ℝ :=
  S.A x*D x+(S.A x)^2/2
noncomputable def potentialTerm (D E : ℝ → ℝ) (x : ℝ) : ℝ := ((D x)^2-E x)/2
noncomputable def generalFlux (D : ℝ → ℝ) (x : ℝ) : ℝ :=
  S.z x*(2*S.κ x+3*m*S.C x)+(D x/2-3*S.z x/2+S.A x/2)*S.Φ x
noncomputable def generalIntegrand (D E : ℝ → ℝ) (x : ℝ) : ℝ :=
  (potentialTerm D E x+S.generalR₁ D x+S.R₀ x)*S.Φ x+S.G x

section
variable {D E H : ℝ → ℝ} (hD : ∀ x, HasDerivAt D (E x) x)
  (hE : ∀ x, HasDerivAt E (H x) x) (hD0 : D 0 = 0)
  (hEp : ∀ x, 0 < E x) (hHn : ∀ x, 0 ≤ x → H x ≤ 0)
include hD hD0 hEp

omit hD0 in
theorem prefixGradient_strictMono : StrictMono D :=
  strictMono_of_deriv_pos (fun x => by rw [(hD x).deriv]; exact hEp x)

omit S in
theorem prefixGradient_pos {x : ℝ} (hx : 0 < x) : 0 < D x := by
  have hh := prefixGradient_strictMono hD hEp hx
  simpa only [hD0] using hh

omit S in
theorem prefixGradient_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ D x := by
  rcases hx.eq_or_lt with rfl|hx
  · exact hD0.ge
  · exact (prefixGradient_pos hD hD0 hEp hx).le

omit hD0 hEp in
theorem dgeneralL (x : ℝ) : HasDerivAt (S.generalL D)
    (S.lam x-5*S.z x*S.κ x-2*m*S.C x*S.z x-
      (m*S.C x+S.κ x)*(D x+S.A x)-S.z x*E x) x := by
  have hh := (S.dκ x).sub ((S.dz x).mul (((hD x).add (S.dA x)).add (S.dz x)))
  convert hh using 1 <;> first | rfl | (simp only [Pi.add_apply]; ring)

theorem generalL_strictAnti (hm : 0 < m) : StrictAntiOn (S.generalL D) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
    (continuous_iff_continuousAt.mpr fun x => (S.dgeneralL hD x).continuousAt).continuousOn
  intro x hx
  rw [interior_Ici] at hx
  change 0 < x at hx
  rw [(S.dgeneralL hD x).deriv]
  have hz := S.z_pos hm hx
  have hc := S.Cpos x
  have hk := S.κnonneg x hx.le
  have ha := S.A_nonneg hx.le
  have hv := prefixGradient_nonneg hD hD0 hEp hx.le
  have h1 : 0 ≤ S.z x*S.κ x := mul_nonneg hz.le hk
  have h2 : 0 < 2*m*S.C x*S.z x := by positivity
  have h3 : 0 ≤ (m*S.C x+S.κ x)*(D x+S.A x) := by positivity
  have h4 : 0 ≤ S.z x*E x := mul_nonneg hz.le (hEp x).le
  nlinarith [S.cone x hx.le]

omit hD0 hEp in
theorem dgeneralR₁ (x : ℝ) : HasDerivAt (S.generalR₁ D)
    (S.κ x*D x+S.A x*E x+S.A x*S.κ x) x := by
  convert ((S.dA x).mul (hD x)).add ((S.dA x).pow 2 |>.div_const 2) using 1 <;>
    first | rfl | ring

theorem generalR₁_monotone : MonotoneOn (S.generalR₁ D) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    (continuous_iff_continuousAt.mpr fun x => (S.dgeneralR₁ hD x).continuousAt).continuousOn
    (fun x _ => (S.dgeneralR₁ hD x).differentiableAt.differentiableWithinAt)
  intro x hx
  rw [interior_Ici] at hx
  change 0 < x at hx
  rw [(S.dgeneralR₁ hD x).deriv]
  positivity [S.κnonneg x hx.le,S.A_nonneg hx.le,prefixGradient_nonneg hD hD0 hEp hx.le,hEp x]

include hE in
omit S hD0 hEp in
theorem dpotentialTerm (x : ℝ) : HasDerivAt (potentialTerm D E) (D x*E x-H x/2) x := by
  convert (((hD x).pow 2).sub (hE x)).div_const 2 using 1 <;> first | rfl | ring

include hE hHn in
omit S in
theorem potentialTerm_strictMono : StrictMonoOn (potentialTerm D E) (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
    (continuous_iff_continuousAt.mpr fun x => (dpotentialTerm hD hE x).continuousAt).continuousOn
  intro x hx
  rw [interior_Ici] at hx
  change 0 < x at hx
  rw [(dpotentialTerm hD hE x).deriv]
  have hp := mul_pos (prefixGradient_pos hD hD0 hEp hx) (hEp x)
  linarith [hHn x hx.le]

omit hD0 hEp in
theorem dgeneralFlux (x : ℝ) : HasDerivAt (S.generalFlux D)
    (S.thirdTest x/2-S.generalIntegrand D E x-(-D x-S.A x-3*S.z x)*S.generalFlux D x) x := by
  have hd := ((S.dz x).mul (((S.dκ x).const_mul 2).add ((S.dC x).const_mul (3*m)))).add
    (((((hD x).div_const 2).sub ((S.dz x).const_mul 3 |>.div_const 2)).add
      ((S.dA x).div_const 2)).mul (S.dΦ x))
  apply hd.congr_deriv
  dsimp only [thirdTest,generalIntegrand,generalFlux,potentialTerm,R₀,generalR₁,G,Φ,Pi.add_apply,Pi.sub_apply]
  ring

omit hD0 hEp in
theorem dweightedGeneralFlux {w : ℝ → ℝ}
    (hdw : ∀ x, HasDerivAt w (w x*(-D x-S.A x-3*S.z x)) x) (x : ℝ) :
    HasDerivAt (fun x => w x*S.generalFlux D x)
      (w x*(S.thirdTest x/2-S.generalIntegrand D E x)) x := by
  convert (hdw x).mul (S.dgeneralFlux hD x) using 1; first | rfl | ring

omit hD hEp in
theorem generalFlux_zero : S.generalFlux D 0 = 0 := by
  simp only [generalFlux,hD0,S.zzero,A,S.Bzero,mul_zero,sub_zero,zero_div,add_zero,zero_mul]

theorem weighted_tail_bounds_general (hm : 0 < m)
    {w F : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hdw : ∀ x, HasDerivAt w (w x*(-D x-S.A x-3*S.z x)) x)
    (hF : ∀ x, HasDerivAt F (-w x*S.Φ x) x)
    (hF0 : F 0 = 0) (hFt : Tendsto F atTop (𝓝 0))
    (hwzt : Tendsto (fun x => w x*S.z x) atTop (𝓝 0))
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ F x ∧ F x ≤ w x*S.z x := by
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun x => (hF x).continuousAt
  constructor
  · exact onePeak_nonneg hFc.continuousOn (by
      intro y _
      simpa only [neg_mul,mul_neg] using hF y) (fun y _ => hw y)
      (S.Φ_strictMono hm |>.monotoneOn.mono Ioi_subset_Ici_self |>.neg) hF0 hFt hx
  · have hd : ∀ y, HasDerivAt (fun y => w y*S.z y-F y) (w y*S.generalL D y) y := by
      intro y
      convert ((hdw y).mul (S.dz y)).sub (hF y) using 1;
        first | rfl | (dsimp only [generalL,Φ]; ring)
    have hh := onePeak_nonneg
      ((continuous_iff_continuousAt.mpr fun y => (hd y).continuousAt).continuousOn)
      (fun y _ => hd y) (fun y _ => hw y)
      (S.generalL_strictAnti hD hD0 hEp hm |>.antitoneOn.mono Ioi_subset_Ici_self)
      (by simp only [S.zzero,mul_zero,hF0,sub_zero]) (by simpa only [sub_zero] using hwzt.sub hFt) hx
    exact sub_nonneg.mp hh

end
end SKFluctuations.Scalar.PhysicalSlopeSlice

 

 

namespace SKFluctuations.Scalar.PhysicalSlopeSlice
open Set Filter MeasureTheory
open scoped Topology
variable {m : ℝ} (S : PhysicalSlopeSlice m)

theorem generalRootIntegral_pos {w : ℝ → ℝ} (hm : 0 < m)
    {D E H : ℝ → ℝ} (hD : ∀ x, HasDerivAt D (E x) x)
    (hE : ∀ x, HasDerivAt E (H x) x) (hD0 : D 0 = 0)
    (hEp : ∀ x, 0 < E x) (hHn : ∀ x, 0 ≤ x → H x ≤ 0)
    (hw : Continuous w) (hwp : ∀ x, 0 < w x)
    (hdw : ∀ x, HasDerivAt w (w x*(-D x-S.A x-3*S.z x)) x)
    (hi : IntegrableOn (fun x => w x*S.Φ x) (Ioi 0))
    (hi₂ : IntegrableOn (fun x => w x*S.Φ x*potentialTerm D E x) (Ioi 0))
    (hi₁ : IntegrableOn (fun x => w x*S.Φ x*S.generalR₁ D x) (Ioi 0))
    (hi₀ : IntegrableOn (fun x => w x*S.Φ x*S.R₀ x) (Ioi 0))
    (hiG : IntegrableOn (fun x => w x*S.G x) (Ioi 0))
    (hiT : IntegrableOn (fun x => w x*S.thirdTest x) (Ioi 0))
    (hiF : IntegrableOn (fun x => S.rootPrimitive w x*(2*S.lam x-5*S.z x*S.κ x)) (Ioi 0))
    (htz : Tendsto (fun x => w x*S.z x) atTop (𝓝 0))
    (htF : Tendsto (fun x => S.rootPrimitive w x*S.R₀ x) atTop (𝓝 0))
    (htFlux : Tendsto (fun x => w x*S.generalFlux D x) atTop (𝓝 0))
    (hcenter : ∫ x in Ioi 0, w x*S.Φ x = 0) :
    0 < ∫ x in Ioi 0, w x*S.thirdTest x := by
  let F := S.rootPrimitive w
  have hdF := S.rootPrimitive_hasDerivAt hw
  have hFt := S.rootPrimitive_tendsto hi hcenter
  have hFb (x : ℝ) (hx : 0 ≤ x) : 0 ≤ F x ∧ F x ≤ w x*S.z x :=
    S.weighted_tail_bounds_general hD hD0 hEp hm (fun y => (hwp y).le) hdw hdF
      (S.rootPrimitive_zero w) hFt htz hx
  obtain ⟨a,ha,hφa⟩ := centered_weight_exists_zero hw S.continuous_Φ
    (fun x _ => hwp x) (S.Φ_zero_neg hm) hi hcenter
  have h₂ : 0 < ∫ x in Ioi 0, w x*S.Φ x*potentialTerm D E x := centered_weight_mul_pos
    hw S.continuous_Φ (continuous_iff_continuousAt.mpr fun x => (dpotentialTerm hD hE x).continuousAt)
    (fun x _ => hwp x) (S.Φ_strictMono hm) (potentialTerm_strictMono hD hE hD0 hEp hHn)
    ha.le hφa hi hi₂ hcenter
  have h₁ : 0 ≤ ∫ x in Ioi 0, w x*S.Φ x*S.generalR₁ D x := centered_weight_mul_nonneg
    (fun x _ => (hwp x).le) (S.Φ_strictMono hm).monotoneOn (S.generalR₁_monotone hD hD0 hEp)
    ha.le hφa hi hi₁ hcenter
  have hFi : IntegrableOn (fun x => -w x*S.Φ x*S.R₀ x+F x*(2*S.lam x-5*S.z x*S.κ x)) (Ioi 0) := by
    apply (hi₀.neg.add hiF).congr
    filter_upwards [] with x
    simp only [Pi.add_apply,Pi.neg_apply,neg_mul,F]
  have hIBP := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ => S.dweightedPrimitive hdF x) hFi htF
  simp only [S.rootPrimitive_zero w,zero_mul,sub_zero] at hIBP
  have hIBP' : (∫ x in Ioi 0, w x*S.Φ x*S.R₀ x) =
      ∫ x in Ioi 0, F x*(2*S.lam x-5*S.z x*S.κ x) := by
    simp_rw [neg_mul] at hIBP
    have hn : IntegrableOn (fun x => -(w x*S.Φ x*S.R₀ x)) (Ioi 0) := hi₀.neg
    rw [integral_add hn hiF,integral_neg] at hIBP
    linarith
  have hcor : 0 ≤ (∫ x in Ioi 0, w x*S.Φ x*S.R₀ x)+(∫ x in Ioi 0, w x*S.G x) := by
    rw [hIBP',← integral_add hiF hiG]
    exact setIntegral_nonneg measurableSet_Ioi (fun x hx =>
      S.correction_nonneg hm hx.le (hFb x hx.le).1 (hFb x hx.le).2)
  have he : (fun x => w x*S.generalIntegrand D E x) = fun x =>
      (w x*S.Φ x*potentialTerm D E x+w x*S.Φ x*S.generalR₁ D x+w x*S.Φ x*S.R₀ x)+w x*S.G x := by
    funext x; dsimp only [generalIntegrand]; ring
  have hi21 : IntegrableOn (fun x => w x*S.Φ x*potentialTerm D E x+w x*S.Φ x*S.generalR₁ D x) (Ioi 0) := hi₂.add hi₁
  have hi210 : IntegrableOn (fun x => w x*S.Φ x*potentialTerm D E x+w x*S.Φ x*S.generalR₁ D x+w x*S.Φ x*S.R₀ x) (Ioi 0) := hi21.add hi₀
  have hroot : IntegrableOn (fun x => w x*S.generalIntegrand D E x) (Ioi 0) := by
    rw [he]
    exact hi210.add hiG
  have heq : (∫ x in Ioi 0, w x*S.generalIntegrand D E x) =
      (∫ x in Ioi 0, w x*S.Φ x*potentialTerm D E x)+
      (∫ x in Ioi 0, w x*S.Φ x*S.generalR₁ D x)+
      (∫ x in Ioi 0, w x*S.Φ x*S.R₀ x)+(∫ x in Ioi 0, w x*S.G x) := by
    rw [he,integral_add hi210 hiG,integral_add hi21 hi₀,integral_add hi₂ hi₁]
  have hrpos : 0 < ∫ x in Ioi 0, w x*S.generalIntegrand D E x := by
    rw [heq]
    linarith
  have hfluxi : IntegrableOn (fun x => w x*(S.thirdTest x/2-S.generalIntegrand D E x)) (Ioi 0) := by
    apply ((hiT.mul_const (1/2)).sub hroot).congr
    filter_upwards [] with x
    simp only [Pi.sub_apply]; ring
  have hfint := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ => S.dweightedGeneralFlux hD hdw x) hfluxi htFlux
  simp only [S.generalFlux_zero hD0,mul_zero,sub_zero] at hfint
  have he : (fun x => w x*(S.thirdTest x/2-S.generalIntegrand D E x)) =
      fun x => (w x*S.thirdTest x)*(1/2)-w x*S.generalIntegrand D E x := by funext x; ring
  rw [he,integral_sub (hiT.mul_const _) hroot,integral_mul_const] at hfint
  linarith

end SKFluctuations.Scalar.PhysicalSlopeSlice

 

 

namespace SKFluctuations.Scalar.PhysicalSlopeSlice
open MeasureTheory Set Filter
open scoped Topology
variable {m : ℝ} (S : PhysicalSlopeSlice m)

theorem generalRootIntegral_pos_gaussian {w : ℝ → ℝ} (hm : 0 < m)
    {D E H : ℝ → ℝ} (hD : ∀ x, HasDerivAt D (E x) x)
    (hE : ∀ x, HasDerivAt E (H x) x) (hD0 : D 0 = 0)
    (hEp : ∀ x, 0 < E x) (hHn : ∀ x, 0 ≤ x → H x ≤ 0)
    (hpD : PolyBounded D) (hpE : PolyBounded E)
    (hw : Continuous w) (hwp : ∀ x, 0 < w x)
    (hdw : ∀ x, HasDerivAt w (w x*(-D x-S.A x-3*S.z x)) x)
    (hGauss : GaussianDominated w) (hB : PolyBounded S.B) (hC : PolyBounded S.C)
    (hz : PolyBounded S.z) (hκ : PolyBounded S.κ) (hlam : PolyBounded S.lam)
    (hcLam : Continuous S.lam)
    (hcenter : ∫ x in Ioi 0, w x*S.Φ x = 0) :
    0 < ∫ x in Ioi 0, w x*S.thirdTest x := by
  have hA : PolyBounded S.A := hz.sub (hB.const_mul m)
  have hΦ : PolyBounded S.Φ := ((hz.pow 2).const_mul 2).sub (hC.const_mul m)
  have hR₀ : PolyBounded S.R₀ := ((hκ.const_mul 2).sub ((hC.const_mul m).div_const 2)).sub
    ((hz.pow 2).div_const 2)
  have hR₁ : PolyBounded (S.generalR₁ D) := (hA.mul hpD).add ((hA.pow 2).div_const 2)
  have hRV : PolyBounded (potentialTerm D E) := ((hpD.pow 2).sub hpE).div_const 2
  have hG : PolyBounded S.G := (hz.const_mul 2).mul (((hz.const_mul 3).mul hκ).sub hlam)
  have hT : PolyBounded S.thirdTest :=
    (((((hz.pow 2).const_mul 4).sub (hC.const_mul (2*m))).sub (hκ.const_mul 2)).pow 2 |>.sub
      ((hC.const_mul (48*m)).mul (hz.pow 2))).add ((hC.pow 2).const_mul (6*m^2))
  have hRate : PolyBounded (fun x => 2*S.lam x-5*S.z x*S.κ x) :=
    (hlam.const_mul 2).sub ((hz.const_mul 5).mul hκ)
  have hFlux : PolyBounded (S.generalFlux D) :=
    (hz.mul ((hκ.const_mul 2).add (hC.const_mul (3*m)))).add
      ((((hpD.div_const 2).sub ((hz.const_mul 3).div_const 2)).add (hA.div_const 2)).mul hΦ)
  have hcD : Continuous D := continuous_iff_continuousAt.mpr fun x => (hD x).continuousAt
  have hcE : Continuous E := continuous_iff_continuousAt.mpr fun x => (hE x).continuousAt
  have hcRV : Continuous (potentialTerm D E) := ((hcD.pow 2).sub hcE).div_const 2
  have hcB := S.continuous_B
  have hcC := S.continuous_C
  have hcz := S.continuous_z
  have hcκ := S.continuous_κ
  have hcA := S.continuous_A
  have hcR₀ : Continuous S.R₀ := by unfold R₀; fun_prop
  have hcR₁ : Continuous (S.generalR₁ D) := by unfold generalR₁; fun_prop
  have hcG : Continuous S.G := by unfold G; fun_prop
  have hcT : Continuous S.thirdTest := by unfold thirdTest; fun_prop
  have hcRate : Continuous (fun x => 2*S.lam x-5*S.z x*S.κ x) := by fun_prop
  have hi : IntegrableOn (fun x => w x*S.Φ x) (Ioi 0) :=
    (hGauss.mul_poly_integrable hΦ (hw.mul S.continuous_Φ).aestronglyMeasurable).integrableOn
  have hi₂ : IntegrableOn (fun x => w x*S.Φ x*potentialTerm D E x) (Ioi 0) := by
    have hh := hGauss.mul_poly_integrable (hΦ.mul hRV)
      (hw.mul (S.continuous_Φ.mul hcRV)).aestronglyMeasurable
    simpa only [mul_assoc] using hh.integrableOn (s := Ioi 0)
  have hi₁ : IntegrableOn (fun x => w x*S.Φ x*S.generalR₁ D x) (Ioi 0) := by
    have hh := hGauss.mul_poly_integrable (hΦ.mul hR₁)
      (hw.mul (S.continuous_Φ.mul hcR₁)).aestronglyMeasurable
    simpa only [mul_assoc] using hh.integrableOn (s := Ioi 0)
  have hi₀ : IntegrableOn (fun x => w x*S.Φ x*S.R₀ x) (Ioi 0) := by
    have hh := hGauss.mul_poly_integrable (hΦ.mul hR₀)
      (hw.mul (S.continuous_Φ.mul hcR₀)).aestronglyMeasurable
    simpa only [mul_assoc] using hh.integrableOn (s := Ioi 0)
  have hiG := (hGauss.mul_poly_integrable hG (hw.mul hcG).aestronglyMeasurable).integrableOn (s := Ioi 0)
  have hiT := (hGauss.mul_poly_integrable hT (hw.mul hcT).aestronglyMeasurable).integrableOn (s := Ioi 0)
  have htz := hGauss.mul_poly_tendsto hz
  let F := S.rootPrimitive w
  have hdF := S.rootPrimitive_hasDerivAt hw
  have hcF : Continuous F := continuous_iff_continuousAt.mpr fun x => (hdF x).continuousAt
  have hFb (x : ℝ) (hx : 0 ≤ x) : 0 ≤ F x ∧ F x ≤ w x*S.z x :=
    S.weighted_tail_bounds_general hD hD0 hEp hm (fun y => (hwp y).le) hdw hdF
      (S.rootPrimitive_zero w) (S.rootPrimitive_tendsto hi hcenter) htz hx
  have hiF : IntegrableOn (fun x => F x*(2*S.lam x-5*S.z x*S.κ x)) (Ioi 0) := by
    have hh := (hGauss.mul_poly_integrable (hz.mul hRate)
      (hw.mul (S.continuous_z.mul hcRate)).aestronglyMeasurable).norm.integrableOn (s := Ioi 0)
    apply hh.mono' (hcF.mul hcRate).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [Pi.mul_apply,Real.norm_eq_abs,abs_mul,abs_of_pos (hwp x),abs_of_nonneg (S.z_nonneg hm hx.le),
      abs_of_nonneg (hFb x hx.le).1]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hFb x hx.le).2 (abs_nonneg (2*S.lam x-5*S.z x*S.κ x))
  have htF : Tendsto (fun x => F x*S.R₀ x) atTop (𝓝 0) := by
    have ht := (hGauss.mul_poly_tendsto (hz.mul hR₀)).norm
    rw [norm_zero] at ht
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ ht
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (hwp x),abs_of_nonneg (S.z_nonneg hm hx),
      abs_of_nonneg (hFb x hx).1]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hFb x hx).2 (abs_nonneg (S.R₀ x))
  exact S.generalRootIntegral_pos hm hD hE hD0 hEp hHn hw hwp hdw hi hi₂ hi₁ hi₀ hiG hiT hiF htz htF
    (hGauss.mul_poly_tendsto hFlux) hcenter

end SKFluctuations.Scalar.PhysicalSlopeSlice

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

namespace ResidualJet

theorem Cone.gradient_zero {J : ResidualJet} (hJ : J.Cone) : J.jet 1 0 = 0 := by
  have he : (fun x => J.jet 0 (-x)) = J.jet 0 := funext hJ.1
  have hh := (J.derivative 0 (-0)).comp 0 (hasDerivAt_neg 0)
  change HasDerivAt (fun x => J.jet 0 (-x)) _ 0 at hh
  rw [he] at hh
  have hd := hh.unique (J.derivative 0 0)
  simp only [neg_zero,mul_neg_one] at hd
  linarith

theorem Cone.zero_max {J : ResidualJet} (hJ : J.Cone) (x : ℝ) : J.jet 0 x ≤ J.jet 0 0 := by
  have hm : Antitone (J.jet 1) := antitone_of_deriv_nonpos
    (fun y => (J.derivative 1 y).differentiableAt)
    (fun y => by rw [(J.derivative 1 y).deriv]; exact hJ.2.1 y)
  have hhalf : AntitoneOn (J.jet 0) (Ici 0) := antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (J.continuous 0).continuousOn
    (fun y _ => (J.derivative 0 y).differentiableAt.differentiableWithinAt)
    (fun y hy => by
      rw [interior_Ici] at hy
      rw [(J.derivative 0 y).deriv]
      have hh := hm hy.le
      rw [hJ.gradient_zero] at hh
      exact hh)
  rcases le_total 0 x with hx|hx
  · exact hhalf (show (0:ℝ) ∈ Ici (0:ℝ) from by simp) hx hx
  · simpa only [hJ.1] using hhalf (show (0:ℝ) ∈ Ici (0:ℝ) from by simp) (neg_nonneg.mpr hx) (neg_nonneg.mpr hx)

end ResidualJet
namespace GaussianResidual

theorem potential_gradient_polyBounded (R : GaussianResidual) : PolyBounded (deriv R.potential) := by
  rw [R.potential_deriv]
  exact (PolyBounded.id.div_const _).sub (PolyBounded.of_absBounded (R.residual.bounded 0))

theorem potential_curvature_polyBounded (R : GaussianResidual) : PolyBounded (deriv (deriv R.potential)) := by
  rw [R.potential_second]
  exact (PolyBounded.const _).sub (PolyBounded.of_absBounded (R.residual.bounded 1))

noncomputable def rootWeight {m : ℝ} (R : GaussianResidual) (S : PhysicalSlopeSlice m)
    (U : ℝ → ℝ) (x : ℝ) : ℝ := Real.exp (m*U x-R.potential x)*(S.C x)^2

theorem rootWeight_eq {m : ℝ} (R : GaussianResidual) (S : PhysicalSlopeSlice m)
    (U : ℝ → ℝ) (x : ℝ) :
    R.rootWeight S U x = R.density x*Real.exp (m*U x)*(S.C x)^2 := by
  unfold rootWeight potential
  rw [sub_neg_eq_add,Real.exp_add,Real.exp_log (R.density_pos x)]
  ring

theorem rootWeight_pos {m : ℝ} (R : GaussianResidual) (S : PhysicalSlopeSlice m)
    (U : ℝ → ℝ) (x : ℝ) : 0 < R.rootWeight S U x :=
  mul_pos (Real.exp_pos _) (sq_pos_of_pos (S.Cpos x))

theorem rootWeight_deriv {m : ℝ} (R : GaussianResidual) (S : PhysicalSlopeSlice m)
    {U : ℝ → ℝ} (hU : ∀ x, HasDerivAt U (S.B x) x) (x : ℝ) :
    HasDerivAt (R.rootWeight S U)
      (R.rootWeight S U x*(-deriv R.potential x-S.A x-3*S.z x)) x := by
  have hV : HasDerivAt R.potential (deriv R.potential x) x := (R.potential_hasDerivAt x).differentiableAt.hasDerivAt
  have hh := (((hU x).const_mul m).sub hV).exp.mul ((S.dC x).pow 2)
  convert! hh using 1
  simp only [rootWeight,PhysicalSlopeSlice.A,Nat.cast_ofNat,Nat.reduceSub,pow_one,Pi.sub_apply,Pi.pow_apply]
  ring

theorem rootWeight_dominated {m : ℝ} {R : GaussianResidual} (hR : R.residual.Cone)
    (S : PhysicalSlopeSlice m) (hm : 0 ≤ m) {U : ℝ → ℝ}
    (hU : ∀ x, U x ≤ U 0+|x|) (hC : AbsBounded S.C) : GaussianDominated (R.rootWeight S U) := by
  obtain ⟨a,K,ha,hK,hb⟩ := S.gaussianWeight_dominated hm R.positive hU hC
  let L := Real.exp (R.residual.jet 0 0-Real.log (Real.sqrt (2*Real.pi*R.variance)))
  have hL : 0 < L := Real.exp_pos _
  refine ⟨a,L*K,ha,mul_nonneg hL.le hK,fun x => ?_⟩
  have hmajor : R.rootWeight S U x ≤ L*S.gaussianWeight U R.variance x := by
    change Real.exp (m*U x-R.potential x)*(S.C x)^2 ≤
      L*(Real.exp (m*U x-x^2/(2*R.variance))*(S.C x)^2)
    rw [R.potential_eq]
    have he : m*U x-(Real.log (Real.sqrt (2*Real.pi*R.variance))+
        x^2/(2*R.variance)-R.residual.jet 0 x) ≤
        (R.residual.jet 0 0-Real.log (Real.sqrt (2*Real.pi*R.variance)))+
          (m*U x-x^2/(2*R.variance)) := by linarith [hR.zero_max x]
    calc
      _ ≤ Real.exp ((R.residual.jet 0 0-Real.log (Real.sqrt (2*Real.pi*R.variance)))+
          (m*U x-x^2/(2*R.variance)))*(S.C x)^2 :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he) (sq_nonneg _)
      _ = _ := by rw [Real.exp_add]; dsimp only [L]; ring
  rw [abs_of_pos (R.rootWeight_pos S U x)]
  calc
    _ ≤ L*S.gaussianWeight U R.variance x := hmajor
    _ ≤ L*(K*Real.exp (-a*x^2)) := mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (hb x)) hL.le
    _ = _ := by ring

end GaussianResidual
end SKFluctuations.Hierarchy

end

end OAI
