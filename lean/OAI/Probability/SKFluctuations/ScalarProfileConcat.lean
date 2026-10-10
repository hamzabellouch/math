import Mathlib
import OAI.Probability.SKFluctuations.BackwardClockDerivative
import OAI.Probability.SKFluctuations.ParametricTestLimit

namespace OAI

/-! Scalar Profile Concat. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem HeatJet.nonnegativeProfile_nonexpansive {n : ℕ} (J K : HeatJet n) {C : ℝ}
    (h : ∀ x, |J.F x-K.F x| ≤ C) (α : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0)
    (x : Fin (n+1) → ℝ) :
    |J.nonnegativeProfileValue α l t x-K.nonnegativeProfileValue α l t x| ≤ C := by
  exact le_of_tendsto ((J.regularized_tendsto α l t x).sub (K.regularized_tendsto α l t x)).abs
    (Eventually.of_forall (fun k => J.profileValue_nonexpansive K h (α.positiveApprox k) l t x))

theorem HeatJet.multiple_grid_error {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (k : ℕ) (l : ℝ) (h : ℝ≥0) (N : ℕ) (x : Fin (n+1) → ℝ) :
    |(J.schedule ((α.cappedApprox k).linearGrid l (h/(2^k:ℝ≥0)) (N*2^k))).F x-
        J.nonnegativeProfileValue α l ((N:ℝ≥0)*h) x| ≤
      (∑ i,(D i)^2)/2*((h:ℝ)+(N:ℝ)*h)*(1/2:ℝ)^k := by
  have he : ((N*2^k:ℕ):ℝ≥0)*(h/(2^k:ℝ≥0)) = (N:ℝ≥0)*h := by
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    field_simp
  have hh := J.capped_linear_error D hD α hα k l (h/(2^k:ℝ≥0)) (N*2^k) x
  rw [he] at hh
  apply hh.trans_eq
  simp only [NNReal.coe_div,NNReal.coe_pow,NNReal.coe_ofNat,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,div_pow,one_pow]
  field_simp

theorem scalarProfile_multiple_concat (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (h : ℝ≥0) (N M : ℕ) (x : Fin 1 → ℝ) :
    scalarTerminal.nonnegativeProfileValue α l (((N+M:ℕ):ℝ≥0)*h) x =
      (scalarProfileHeatJet α hα (l+(N:ℝ)*h) ((M:ℝ≥0)*h)).nonnegativeProfileValue α l ((N:ℝ≥0)*h) x := by
  let R := scalarProfileHeatJet α hα (l+(N:ℝ)*h) ((M:ℝ≥0)*h)
  have hA := scalarTerminal.multiple_grid_tendsto (fun _ => 1) scalarTerminal_G_bound α hα l h (N+M) x
  have hB := R.multiple_grid_tendsto (fun _ => 1) (scalarProfileHeatJet_G_bound α hα _ _) α hα l h N x
  have hd (k : ℕ) :
      dist ((R.schedule ((α.cappedApprox k).linearGrid l (h/(2^k:ℝ≥0)) (N*2^k))).F x)
        ((scalarTerminal.schedule ((α.cappedApprox k).linearGrid l (h/(2^k:ℝ≥0)) ((N+M)*2^k))).F x) ≤
      ((h:ℝ)+(M:ℝ)*h)/2*(1/2:ℝ)^k := by
    have he : l+((N*2^k:ℕ):ℝ)*((h/(2^k:ℝ≥0):ℝ≥0):ℝ) = l+(N:ℝ)*h := by
      simp only [NNReal.coe_div,NNReal.coe_pow,NNReal.coe_ofNat,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      field_simp
    rw [add_mul,(α.cappedApprox k).linearGrid_add,he,scalarTerminal.schedule_append,
      Real.dist_eq,abs_sub_comm]
    apply HeatJet.schedule_nonexpansive _ R
    intro y
    rw [show R.F y = scalarTerminal.nonnegativeProfileValue α (l+(N:ℝ)*h) ((M:ℝ≥0)*h) y from
      scalarProfileHeatJet_F α hα _ _ y]
    have hh := scalarTerminal.multiple_grid_error (fun _ => 1) scalarTerminal_G_bound α hα k
      (l+(N:ℝ)*h) h M y
    simpa only [Fin.sum_univ_succ,Fin.sum_univ_zero,one_pow,add_zero,one_div,mul_comm (2:ℝ)⁻¹,← div_eq_mul_inv] using hh
  have hp : Tendsto (fun k : ℕ => ((h:ℝ)+(M:ℝ)*h)/2*(1/2:ℝ)^k) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).const_mul (((h:ℝ)+(M:ℝ)*h)/2)
  exact tendsto_nhds_unique hA (hB.congr_dist (squeeze_zero (fun _ => dist_nonneg) hd hp))

 

theorem HeatJet.nonnegativeProfile_zero {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (x : Fin (n+1) → ℝ) : J.nonnegativeProfileValue α l 0 x = J.F x := by
  have hh := J.multiple_grid_tendsto D hD α hα l 0 0 x
  simp only [PositiveMassProfile.linearGrid,HeatJet.schedule,Nat.cast_zero,zero_mul] at hh
  exact tendsto_nhds_unique hh tendsto_const_nhds

 
theorem scalarProfile_concat_stability (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (s t u v : ℝ≥0) (x : Fin 1 → ℝ) :
    |(scalarProfileHeatJet α hα (l+s) t).nonnegativeProfileValue α l s x-
      (scalarProfileHeatJet α hα (l+u) v).nonnegativeProfileValue α l u x| ≤
        (5/2:ℝ)*|(s:ℝ)-u|+(3/2:ℝ)*|(t:ℝ)-v| := by
  let A := scalarProfileHeatJet α hα (l+s) t
  let B := scalarProfileHeatJet α hα (l+u) v
  have hAB : ∀ y, |A.F y-B.F y| ≤ |(s:ℝ)-u|+(3/2:ℝ)*|(t:ℝ)-v| := by
    intro y
    rw [show A.F y = scalarTerminal.nonnegativeProfileValue α (l+s) t y from scalarProfileHeatJet_F α hα _ _ y,
      show B.F y = scalarTerminal.nonnegativeProfileValue α (l+u) v y from scalarProfileHeatJet_F α hα _ _ y]
    simpa only [add_sub_add_left_eq_sub] using
      HeatJet.profile_window_stability scalarTerminal_admissible α hα (l+s) (l+u) t v y
  have hh := A.nonnegativeProfile_nonexpansive B hAB α l s x
  have ht := HeatJet.profile_window_stability (show B.ScalarAdmissible from fun y => scalarProfileJet_admissible α hα (l+u) v (y 0)) α hα l l s u x
  have hc := (abs_sub_le (A.nonnegativeProfileValue α l s x) (B.nonnegativeProfileValue α l s x)
    (B.nonnegativeProfileValue α l u x)).trans (add_le_add hh ht)
  simp only [sub_self,abs_zero,zero_add] at hc
  exact hc.trans_eq (by ring)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem OrderedSteps.prefixOrdered {ι : Type*} {a : ℝ} {cs : List (GaussianStep ι)}
    (h : OrderedSteps a cs) : PrefixOrdered a 1 cs := by
  induction cs generalizing a with
  | nil => exact h
  | cons c cs ih => exact ⟨h.1,h.2.1,h.2.2.1,ih h.2.2.2⟩

 theorem HeatJet.capped_diagonal_grid_error {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (k : ℕ) (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    |(J.schedule ((α.cappedApprox k).grid l t k)).F x-J.nonnegativeProfileValue α l t x| ≤
      (∑ i,(D i)^2)*(t:ℝ)*(1/2:ℝ)^k := by
  have hh := J.multiple_grid_error D hD α hα k l t 1 x
  simp only [Nat.cast_one,one_mul] at hh
  rw [(α.cappedApprox k).grid_eq_linear]
  exact hh.trans_eq (by ring)

 theorem HeatJet.capped_grid_tendstoUniformly {n : ℕ} (J : HeatJet n)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) :
    TendstoUniformly (fun k => (J.schedule ((α.cappedApprox k).grid l t k)).F)
      (J.nonnegativeProfileValue α l t) atTop := by
  choose D _ hD using fun i => (J.smoothG i).bound
  have hp : Tendsto (fun k : ℕ => (∑ i,(D i)^2)*(t:ℝ)*(1/2:ℝ)^k) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).const_mul ((∑ i,(D i)^2)*(t:ℝ))
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hp.eventually (gt_mem_nhds hε)] with k hk x
  rw [Real.dist_eq]
  simpa only [abs_sub_comm] using (J.capped_diagonal_grid_error D hD α hα k l t x).trans_lt hk

 theorem HeatJet.capped_test_parameter_bound {n : ℕ} (J : HeatJet n)
    {K : ℝ} (hK : 0 < K) (hb : ∀ x, |J.A x| ≤ K)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (k : ℕ) (s u : ℝ) (x : Fin (n+1) → ℝ) :
    |((J.terminalPerturb s).schedule ((α.cappedApprox k).grid l t k)).A x-
      ((J.terminalPerturb u).schedule ((α.cappedApprox k).grid l t k)).A x| ≤
        (4*K^2)*|s-u| := by
  simp only [HeatJet.schedule_A_prefix,HeatJet.terminalPerturb]
  have ho := ((α.cappedApprox k).grid_ordered (ι := Fin (n+1)) l t k le_rfl
    (α.cappedApprox k |>.positive l).le (α.cappedApprox_le_one hα k _)).prefixOrdered
  simpa only [mul_one] using prefixTest_terminal_lipschitz_bound J.lipschitz
    J.test_lipschitz.choose_spec hK hb _ ho s u x

 theorem HeatJet.capped_test_parameter_cauchy {n : ℕ} (J : HeatJet n)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (s : ℝ) :
    UniformCauchySeqOn (fun k => ((J.terminalPerturb s).schedule ((α.cappedApprox k).grid l t k)).A)
      atTop univ := by
  obtain ⟨K,hK,hb⟩ := J.smoothA.bound
  exact uniformCauchySeqOn_parameter_derivative (M := 4*(K+1)^2) (by positivity)
    (fun k u x => J.schedule_terminal_deriv _ u x)
    (fun k u v x => J.capped_test_parameter_bound (by linarith : 0 < K+1)
      (fun y => (hb y).trans (by linarith)) α hα l t k u v x)
    (fun u => ((J.terminalPerturb u).capped_grid_tendstoUniformly α hα l t).tendstoUniformlyOn.uniformCauchySeqOn) s

 
noncomputable def HeatJet.nonnegativeProfileTest {n : ℕ} (J : HeatJet n)
    (α : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) : ℝ :=
  limUnder atTop (fun k => (J.schedule ((α.cappedApprox k).grid l t k)).A x)

 theorem HeatJet.schedule_perturb_zero_A {n : ℕ} (J : HeatJet n) (cs : List HeatClock) :
    ((J.terminalPerturb 0).schedule cs).A = (J.schedule cs).A := by
  simp only [HeatJet.schedule_A_prefix]
  change prefixTest (heatSteps cs) (fun x => J.F x+0*J.A x) J.A = _
  simp only [zero_mul,add_zero]

 theorem HeatJet.capped_test_cauchy {n : ℕ} (J : HeatJet n)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) :
    UniformCauchySeqOn (fun k => (J.schedule ((α.cappedApprox k).grid l t k)).A)
      atTop univ := by
  simpa only [HeatJet.schedule_perturb_zero_A] using J.capped_test_parameter_cauchy α hα l t 0

 theorem HeatJet.capped_test_tendstoUniformly {n : ℕ} (J : HeatJet n)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) :
    TendstoUniformly (fun k => (J.schedule ((α.cappedApprox k).grid l t k)).A)
      (J.nonnegativeProfileTest α l t) atTop := by
  have hc := J.capped_test_cauchy α hα l t
  rw [← tendstoUniformlyOn_univ]
  exact hc.tendstoUniformlyOn_of_tendsto (fun x _ =>
    (hc.cauchySeq (mem_univ x)).tendsto_limUnder)

 

 theorem HeatJet.nonnegativeProfile_terminal_deriv {n : ℕ} (J : HeatJet n)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (s : ℝ) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun u => (J.terminalPerturb u).nonnegativeProfileValue α l t x)
      ((J.terminalPerturb s).nonnegativeProfileTest α l t x) s := by
  obtain ⟨K,hK,hb⟩ := J.smoothA.bound
  exact hasDerivAt_limit_of_lipschitz_derivative (M := 4*(K+1)^2) (by positivity)
    (fun k u => J.schedule_terminal_deriv _ u x)
    (fun k u v => J.capped_test_parameter_bound (by linarith : 0 < K+1)
      (fun y => (hb y).trans (by linarith)) α hα l t k u v x)
    (fun u => ((J.terminalPerturb u).capped_grid_tendstoUniformly α hα l t).tendsto_at x)
    (((J.terminalPerturb s).capped_test_tendstoUniformly α hα l t).tendsto_at x)

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

noncomputable def HeatJet.withTest {n : ℕ} (J : HeatJet n)
    (A : (Fin (n+1) → ℝ) → ℝ) (hA : BddSmooth 2 A) : HeatJet n :=
  HeatJet.ofTest J.F A J.G J.H J.lipschitz hA J.smoothG J.smoothH J.derivF J.derivG

 theorem prefixTest_subtract {ι : Type*} [Fintype ι] {F A B : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) (hB : BddSmooth 0 B)
    (cs : List (GaussianStep ι)) (hm : ∀ st ∈ cs, 0 < st.1) (x : ι → ℝ) :
    prefixTest cs F (fun y => A y-B y) x = prefixTest cs F A x-prefixTest cs F B x := by
  induction cs generalizing x with
  | nil => rfl
  | cons st cs ih =>
    rcases st with ⟨m,q⟩
    have ht := fun st hs => hm st (List.mem_cons_of_mem _ hs)
    simp only [prefixTest]
    rw [funext (ih ht)]
    exact shiftedMean_sub (prefixTest_smooth0 hF hA cs ht) (prefixTest_smooth0 hF hB cs ht)
      ((exponentialIncrement_gaussian q).integrable_shift (prefixContinuation_lipschitz hF cs ht) m x)

 theorem HeatJet.nonnegativeProfileValue_congr_potential {n : ℕ} (J K : HeatJet n)
    (he : J.F=K.F) (α : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0) :
    J.nonnegativeProfileValue α l t = K.nonnegativeProfileValue α l t := by
  funext x
  have hh := J.nonnegativeProfile_nonexpansive K (C := 0) (fun y => by rw [he]; simp) α l t x
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hh)

 theorem HeatJet.nonnegativeProfileTest_congr {n : ℕ} (J K : HeatJet n)
    (hF : J.F=K.F) (hA : J.A=K.A) (α : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0) :
    J.nonnegativeProfileTest α l t = K.nonnegativeProfileTest α l t := by
  unfold HeatJet.nonnegativeProfileTest
  simp only [HeatJet.schedule_A_prefix,hF,hA]

 theorem HeatJet.nonnegativeProfileTest_nonneg {n : ℕ} (J : HeatJet n)
    (hA : ∀ x, 0 ≤ J.A x) (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) : 0 ≤ J.nonnegativeProfileTest α l t x := by
  apply ge_of_tendsto ((J.capped_test_tendstoUniformly α hα l t).tendsto_at x)
  apply Eventually.of_forall
  intro k
  rw [HeatJet.schedule_A_prefix]
  exact prefixTest_nonneg J.lipschitz hA _
    (((α.cappedApprox k).grid_ordered l t k le_rfl (α.cappedApprox k |>.positive l).le
      (α.cappedApprox_le_one hα k _)).prefixOrdered.positive) x

 theorem HeatJet.nonnegativeProfileTest_abs_le {n : ℕ} (J : HeatJet n) {K : ℝ}
    (hA : ∀ x, |J.A x| ≤ K) (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) : |J.nonnegativeProfileTest α l t x| ≤ K := by
  apply le_of_tendsto ((J.capped_test_tendstoUniformly α hα l t).tendsto_at x).abs
  apply Eventually.of_forall
  intro k
  rw [HeatJet.schedule_A_prefix]
  exact prefixTest_abs_le J.lipschitz J.smoothA hA _
    (((α.cappedApprox k).grid_ordered l t k le_rfl (α.cappedApprox k |>.positive l).le
      (α.cappedApprox_le_one hα k _)).prefixOrdered.positive) x

 theorem HeatJet.nonnegativeProfileTest_sub {n : ℕ} (J K L : HeatJet n)
    (hK : K.F=J.F) (hL : L.F=J.F) (hA : L.A=fun x => J.A x-K.A x)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    L.nonnegativeProfileTest α l t x = J.nonnegativeProfileTest α l t x-K.nonnegativeProfileTest α l t x := by
  have hh := ((J.capped_test_tendstoUniformly α hα l t).tendsto_at x).sub
    ((K.capped_test_tendstoUniformly α hα l t).tendsto_at x)
  apply tendsto_nhds_unique ((L.capped_test_tendstoUniformly α hα l t).tendsto_at x)
  apply hh.congr'
  apply Eventually.of_forall
  intro k
  simp only [HeatJet.schedule_A_prefix,hK,hL,hA]
  exact (prefixTest_subtract J.lipschitz J.smoothA K.smoothA _
    (((α.cappedApprox k).grid_ordered l t k le_rfl (α.cappedApprox k |>.positive l).le
      (α.cappedApprox_le_one hα k _)).prefixOrdered.positive) x).symm

 theorem HeatJet.nonnegativeProfileTest_affine {n : ℕ} (J K : HeatJet n) (a b : ℝ)
    (hF : K.F=J.F) (hA : K.A=fun x => a+b*J.A x)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    K.nonnegativeProfileTest α l t x = a+b*J.nonnegativeProfileTest α l t x := by
  have hh := (((J.capped_test_tendstoUniformly α hα l t).tendsto_at x).const_mul b).const_add a
  apply tendsto_nhds_unique ((K.capped_test_tendstoUniformly α hα l t).tendsto_at x)
  apply hh.congr'
  apply Eventually.of_forall
  intro k
  simp only [HeatJet.schedule_A_prefix,hF,hA]
  exact (prefixTest_affine J.lipschitz J.smoothA _
    (((α.cappedApprox k).grid_ordered l t k le_rfl (α.cappedApprox k |>.positive l).le
      (α.cappedApprox_le_one hα k _)).prefixOrdered.positive) a b x).symm

 theorem HeatJet.nonnegativeProfileTest_stability {n : ℕ} (J K : HeatJet n) {E L D : ℝ}
    (hE : 0 ≤ E) (hF : ∀ x, |K.F x-J.F x| ≤ E) (hL : 0 < L) (hA : ∀ x, |J.A x| ≤ L)
    (hD : ∀ x, |K.A x-J.A x| ≤ D)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    |K.nonnegativeProfileTest α l t x-J.nonnegativeProfileTest α l t x| ≤ D+4*E*L := by
  apply le_of_tendsto (((K.capped_test_tendstoUniformly α hα l t).tendsto_at x).sub
    ((J.capped_test_tendstoUniformly α hα l t).tendsto_at x)).abs
  apply Eventually.of_forall
  intro k
  let cs := heatSteps (ι := Fin (n+1)) ((α.cappedApprox k).grid l t k)
  have ho : PrefixOrdered 0 1 cs := ((α.cappedApprox k).grid_ordered l t k le_rfl
    (α.cappedApprox k |>.positive l).le (α.cappedApprox_le_one hα k _)).prefixOrdered
  have he := prefixTest_potential_stability J.lipschitz K.lipschitz hE hF J.smoothA.continuous hL hA cs ho x
  have hd := prefixTest_abs_le K.lipschitz (K.smoothA.sub J.smoothA) hD cs ho.positive x
  rw [prefixTest_subtract K.lipschitz K.smoothA J.smoothA cs ho.positive x] at hd
  simp only [HeatJet.schedule_A_prefix]
  exact (abs_sub_le _ (prefixTest cs K.F J.A x) _).trans (by simpa only [mul_one] using add_le_add hd he)

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem HeatJet.nonnegativeProfile_perturb_zero {n : ℕ} (J : HeatJet n)
    (α : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0) :
    (J.terminalPerturb 0).nonnegativeProfileValue α l t = J.nonnegativeProfileValue α l t := by
  apply HeatJet.nonnegativeProfileValue_congr_potential
  funext x
  change J.F x+0*J.A x=J.F x
  ring

 theorem HeatJet.nonnegativeProfileTest_perturb_zero {n : ℕ} (J : HeatJet n)
    (α : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0) :
    (J.terminalPerturb 0).nonnegativeProfileTest α l t = J.nonnegativeProfileTest α l t := by
  apply HeatJet.nonnegativeProfileTest_congr
  · funext x
    change J.F x+0*J.A x=J.F x
    ring
  · rfl

 theorem HeatJet.nonnegativeProfile_terminal_deriv_zero {n : ℕ} (J : HeatJet n)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun u => (J.terminalPerturb u).nonnegativeProfileValue α l t x)
      (J.nonnegativeProfileTest α l t x) 0 := by
  simpa only [HeatJet.nonnegativeProfileTest_perturb_zero] using
    J.nonnegativeProfile_terminal_deriv α hα l t 0 x

 theorem HeatJet.nonnegativeProfile_terminal_taylor {n : ℕ} (J : HeatJet n) {K : ℝ}
    (hK : 0 < K) (hb : ∀ x, |J.A x| ≤ K)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (s : ℝ) (x : Fin (n+1) → ℝ) :
    |(J.terminalPerturb s).nonnegativeProfileValue α l t x-J.nonnegativeProfileValue α l t x-
      s*J.nonnegativeProfileTest α l t x| ≤ 4*K^2*s^2 := by
  have hf (u : ℝ) := ((J.terminalPerturb u).capped_grid_tendstoUniformly α hα l t).tendsto_at x
  have hg := ((J.terminalPerturb 0).capped_test_tendstoUniformly α hα l t).tendsto_at x
  have hh : |(J.terminalPerturb s).nonnegativeProfileValue α l t x-
      (J.terminalPerturb 0).nonnegativeProfileValue α l t x-
      (s-0)*(J.terminalPerturb 0).nonnegativeProfileTest α l t x| ≤ 4*K^2*|s-0|^2 := by
    apply le_of_tendsto (((hf s).sub (hf 0)).sub (hg.const_mul (s-0))).abs
    exact Eventually.of_forall fun k => lipschitz_derivative_remainder (by positivity)
      (fun u => J.schedule_terminal_deriv ((α.cappedApprox k).grid l t k) u x)
      (fun u v => J.capped_test_parameter_bound hK hb α hα l t k u v x) 0 s
  simpa only [J.nonnegativeProfile_perturb_zero,J.nonnegativeProfileTest_perturb_zero,
    sub_zero,sq_abs] using hh

 

 theorem HeatJet.nonnegativeProfile_response_error {n : ℕ} (J L : HeatJet n) {K E s : ℝ}
    (hK : 0 < K) (hb : ∀ x, |J.A x| ≤ K)
    (hE : ∀ x, |L.F x-(J.F x+s*J.A x)| ≤ E)
    (α : NonnegativeMassProfile) (hα : ∀ r, α.mass r ≤ 1)
    (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    |L.nonnegativeProfileValue α l t x-J.nonnegativeProfileValue α l t x-
      s*J.nonnegativeProfileTest α l t x| ≤ E+4*K^2*s^2 := by
  have he := L.nonnegativeProfile_nonexpansive (J.terminalPerturb s) hE α l t x
  have ht := J.nonnegativeProfile_terminal_taylor hK hb α hα l t s x
  have hh := abs_add_le (L.nonnegativeProfileValue α l t x-
    (J.terminalPerturb s).nonnegativeProfileValue α l t x)
    ((J.terminalPerturb s).nonnegativeProfileValue α l t x-
      J.nonnegativeProfileValue α l t x-s*J.nonnegativeProfileTest α l t x)
  rw [show (L.nonnegativeProfileValue α l t x-(J.terminalPerturb s).nonnegativeProfileValue α l t x)+
      ((J.terminalPerturb s).nonnegativeProfileValue α l t x-J.nonnegativeProfileValue α l t x-
        s*J.nonnegativeProfileTest α l t x) =
      L.nonnegativeProfileValue α l t x-J.nonnegativeProfileValue α l t x-
        s*J.nonnegativeProfileTest α l t x by ring] at hh
  exact hh.trans (add_le_add he ht)

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 
def HeatJet.OrderedHessian (J : HeatJet 0) (a B Q : ℝ) : Prop :=
  ∀ x, -B ≤ J.H 0 x ∧ J.H 0 x+a*(J.G 0 x)^2 ≤ Q

 theorem HeatJet.OrderedHessian.evolve {J : HeatJet 0} {a m B Q : ℝ}
    (hJ : J.OrderedHessian m B Q) (hm : 0 < m) (ha : a ≤ m) (t : ℝ) :
    (J.evolve hm t).OrderedHessian a B Q := by
  intro x
  have hv := clockTest_variance_nonneg J.lipschitz (J.smoothG 0) m t x
  have hl := clockTest_mono J.lipschitz (BddSmooth.const 0 (-B)) (J.smoothH 0)
    (fun y => (hJ y).1) m t x
  rw [clockTest_const J.lipschitz] at hl
  have hs : BddSmooth 0 (fun y => (J.G 0 y)^2) := by
    simpa only [pow_two] using (J.smoothG 0).mul (J.smoothG 0)
  have hu := clockTest_mono J.lipschitz ((J.smoothH 0).add (hs.const_mul m))
    (BddSmooth.const 0 Q) (fun y => (hJ y).2) m t x
  rw [clockTest_add_test J.lipschitz (J.smoothH 0) (hs.const_mul m),
    clockTest_const_mul,clockTest_const J.lipschitz] at hu
  change -B ≤ clockGradient m J.F (J.G 0) (J.G 0) (J.H 0) t x ∧
    clockGradient m J.F (J.G 0) (J.G 0) (J.H 0) t x+a*(clockTest m J.F (J.G 0) t x)^2 ≤ Q
  simp only [clockGradient,← pow_two]
  constructor
  · nlinarith [mul_nonneg hm.le hv]
  · nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg (clockTest m J.F (J.G 0) t x))]

 theorem HeatJet.schedule_ordered_hessian (J : HeatJet 0) {D B : ℝ}
    (hD : ∀ x, |J.G 0 x| ≤ D) (hB : ∀ x, |J.H 0 x| ≤ B)
    (cs : List HeatClock) {a : ℝ} (ho : OrderedSteps a (heatSteps (ι:=Fin 1) cs)) :
    (J.schedule cs).OrderedHessian a B (B+D^2) := by
  induction cs generalizing a with
  | nil =>
    intro x
    have ha : 0 ≤ a ∧ a ≤ 1 := ho
    have hs : (J.G 0 x)^2 ≤ D^2 := by
      have hh := mul_self_le_mul_self (abs_nonneg _) (hD x)
      simpa only [← pow_two,sq_abs] using hh
    simpa only [HeatJet.schedule] using (show -B ≤ J.H 0 x ∧ J.H 0 x+a*(J.G 0 x)^2 ≤ B+D^2 from
      ⟨(abs_le.mp (hB x)).1,by nlinarith [(abs_le.mp (hB x)).2,sq_nonneg (J.G 0 x)]⟩)
  | cons c cs ih =>
    change 0 ≤ a ∧ a ≤ c.mass ∧ 0 < c.mass ∧ OrderedSteps c.mass (heatSteps cs) at ho
    exact (ih ho.2.2.2).evolve c.positive ho.2.1 c.time

 theorem HeatJet.OrderedHessian.time_stability {J : HeatJet 0} {m B Q : ℝ}
    (hJ : J.OrderedHessian m B Q) (hm : 0 < m) (_hB : 0 ≤ B) (hBQ : B ≤ Q)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : Fin 1 → ℝ) :
    |clockContinuation m J.F t x-clockContinuation m J.F s x| ≤ Q/2*|t-s| := by
  have hc : ContinuousOn (fun s => (J.evolve hm s).F x) (Ici 0) :=
    ((clockContinuation_continuous J.lipschitz m).comp
      (continuous_id.prodMk continuous_const)).continuousOn
  have hd (r : ℝ) (hr : 0 < r) := J.evolve_time_F hm hr x
  have hb (r : ℝ) (_hr : 0 < r) :
      |(1/2:ℝ)*∑ i, ((J.evolve hm r).H i x+m*((J.evolve hm r).G i x)^2)| ≤ Q/2 := by
    rw [Fin.sum_univ_one]
    have hh := (hJ.evolve hm le_rfl r) x
    have hmsq := mul_nonneg hm.le (sq_nonneg ((J.evolve hm r).G 0 x))
    exact abs_le.mpr ⟨by nlinarith [hh.1],by nlinarith [hh.2]⟩
  have hh := abs_sub_le_mul_of_deriv_interior hc hd hb ht hs
  simpa only [HeatJet.evolve,abs_sub_comm] using hh

 theorem orderedSteps_scaleTimes {a : ℝ} {cs : List HeatClock}
    (ho : OrderedSteps a (heatSteps (ι:=Fin 1) cs)) (r : ℝ≥0) :
    OrderedSteps a (heatSteps (ι:=Fin 1) (scaleTimes cs r)) := by
  induction cs generalizing a with
  | nil => exact ho
  | cons c cs ih =>
    change 0 ≤ a ∧ a ≤ c.mass ∧ 0 < c.mass ∧ OrderedSteps c.mass (heatSteps cs) at ho
    exact ⟨ho.1,ho.2.1,ho.2.2.1,ih ho.2.2.2⟩

 theorem HeatJet.schedule_ordered_time_stability (J : HeatJet 0) {D B : ℝ}
    (hD : ∀ x, |J.G 0 x| ≤ D) (hB : ∀ x, |J.H 0 x| ≤ B)
    (cs : List HeatClock) {a : ℝ} (ho : OrderedSteps a (heatSteps (ι:=Fin 1) cs))
    (r s : ℝ≥0) (x : Fin 1 → ℝ) :
    |(J.schedule (scaleTimes cs r)).F x-(J.schedule (scaleTimes cs s)).F x| ≤
      (B+D^2)/2*|(r:ℝ)-s| *(cs.map (fun c => (c.time:ℝ))).sum := by
  induction cs generalizing a x with
  | nil => simp [HeatJet.schedule]
  | cons c cs ih =>
    change 0 ≤ a ∧ a ≤ c.mass ∧ 0 < c.mass ∧ OrderedSteps c.mass (heatSteps cs) at ho
    let A := J.schedule (scaleTimes cs r)
    let L := J.schedule (scaleTimes cs s)
    have hL := J.schedule_ordered_hessian hD hB _ (orderedSteps_scaleTimes ho.2.2.2 s)
    have hh := clockContinuation_abs_sub_le A.lipschitz L.lipschitz c.positive
      (fun y => ih ho.2.2.2 y) ((r*c.time:ℝ≥0):ℝ) x
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
    have ht := hL.time_stability c.positive hB0 (by nlinarith [sq_nonneg D])
      (s*c.time).coe_nonneg (r*c.time).coe_nonneg x
    have ha := (abs_sub_le (clockContinuation c.mass A.F (r*c.time) x)
      (clockContinuation c.mass L.F (r*c.time) x)
      (clockContinuation c.mass L.F (s*c.time) x)).trans (add_le_add hh ht)
    change |(J.schedule (scaleTimes (c::cs) r)).F x-(J.schedule (scaleTimes (c::cs) s)).F x| ≤ _ at ha
    apply ha.trans_eq
    simp only [NNReal.coe_mul,List.map_cons,List.sum_cons,← sub_mul,abs_mul,
      abs_of_nonneg c.time.coe_nonneg]
    ring

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem HeatJet.capped_scaled_mass_comparison_general (J : HeatJet 0) {D : ℝ}
    (hD : ∀ x, |J.G 0 x| ≤ D)
    (α β : NonnegativeMassProfile) (l : ℝ) (t r : ℝ≥0) (k : ℕ) (x : Fin 1 → ℝ) :
    |(J.schedule (scaleTimes ((α.cappedApprox k).grid l t k) r)).F x-
      (J.schedule (scaleTimes ((β.cappedApprox k).grid l t k) r)).F x| ≤
      (r:ℝ)*D^2/2*dyadicLowerSum (fun s => |α.mass s-β.mass s|) l t k := by
  have hh := J.schedule_mass_comparison (fun _ => D) (fun i x => by fin_cases i; exact hD x)
    (((α.cappedApprox k).pairedGrid (β.cappedApprox k) l t k).map (fun c => c.scaleTime r)) x
  rw [coupled_scale_left,coupled_scale_right,PositiveMassProfile.pairedGrid_left,
    PositiveMassProfile.pairedGrid_right,coupled_scale_cost,PositiveMassProfile.pairedGrid_cost_eq_sum] at hh
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hh
  have hc := dyadicLowerSum_mono (fun s => abs_max_sub_max_le_abs (α.mass s) (β.mass s) ((1/2:ℝ)^k)) l t k
  change dyadicLowerSum (fun s => |(α.cappedApprox k).mass s-(β.cappedApprox k).mass s|) l t k ≤ _ at hc
  have hh' := mul_le_mul_of_nonneg_left hc (show 0 ≤ (r:ℝ)*D^2/2 by positivity)
  apply hh.trans
  convert hh' using 1
  ring

 theorem HeatJet.profile_affine_comparison_general (J : HeatJet 0) {D B : ℝ}
    (hD : ∀ x, |J.G 0 x| ≤ D) (hB : ∀ x, |J.H 0 x| ≤ B)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l b : ℝ) (t r : ℝ≥0) (x : Fin 1 → ℝ) :
    |J.nonnegativeProfileValue α l t x-J.nonnegativeProfileValue α b r x| ≤
      (t:ℝ)*D^2/2*(∫ s in (0:ℝ)..1, |α.mass (l+(t:ℝ)*s)-α.mass (b+(r:ℝ)*s)|)+
        (B+D^2)/2*|(t:ℝ)-r| := by
  let A := α.affine l t
  let L := α.affine b r
  have hAt (k : ℕ) : scaleTimes ((A.cappedApprox k).grid 0 1 k) t = (α.cappedApprox k).grid l t k := by
    rw [NonnegativeMassProfile.cappedApprox_affine,PositiveMassProfile.grid_affine]
    simp only [mul_zero,add_zero,mul_one]
  have hLr (k : ℕ) : scaleTimes ((L.cappedApprox k).grid 0 1 k) r = (α.cappedApprox k).grid b r k := by
    rw [NonnegativeMassProfile.cappedApprox_affine,PositiveMassProfile.grid_affine]
    simp only [mul_zero,add_zero,mul_one]
  have hf (k : ℕ) :
      |(J.schedule ((α.cappedApprox k).grid l t k)).F x-
        (J.schedule ((α.cappedApprox k).grid b r k)).F x| ≤
      (t:ℝ)*D^2/2*dyadicLowerSum (fun s => |A.mass s-L.mass s|) 0 1 k+(B+D^2)/2*|(t:ℝ)-r| := by
    have hm := J.capped_scaled_mass_comparison_general hD A L 0 1 t k x
    have hc : OrderedSteps 0 (heatSteps (ι:=Fin 1) ((L.cappedApprox k).grid 0 1 k)) :=
      (L.cappedApprox k).grid_ordered 0 1 k le_rfl (L.cappedApprox k |>.positive 0).le
        (L.cappedApprox_le_one (fun s => hα _) k _)
    have ht := J.schedule_ordered_time_stability hD hB ((L.cappedApprox k).grid 0 1 k) hc t r x
    rw [PositiveMassProfile.grid_total_time] at ht
    simp only [NNReal.coe_one,mul_one] at ht
    have h := abs_sub_le ((J.schedule (scaleTimes ((A.cappedApprox k).grid 0 1 k) t)).F x)
      ((J.schedule (scaleTimes ((L.cappedApprox k).grid 0 1 k) t)).F x)
      ((J.schedule (scaleTimes ((L.cappedApprox k).grid 0 1 k) r)).F x)
    have hh := h.trans (add_le_add hm ht)
    rw [hAt,hLr] at hh
    exact hh
  have hleft := (J.capped_grid_tendstoUniformly α hα l t).tendsto_at x
  have hright := (J.capped_grid_tendstoUniformly α hα b r).tendsto_at x
  have hI := monotone_abs_sub_sum_tendsto A.monotone L.monotone 0 1
  simp only [NNReal.coe_one,zero_add] at hI
  exact le_of_tendsto_of_tendsto (hleft.sub hright).abs
    ((hI.const_mul ((t:ℝ)*D^2/2)).add_const ((B+D^2)/2*|(t:ℝ)-r|)) (Eventually.of_forall hf)

 theorem HeatJet.profile_window_stability_general (J : HeatJet 0) {D B : ℝ}
    (hD : ∀ x, |J.G 0 x| ≤ D) (hB : ∀ x, |J.H 0 x| ≤ B)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l b : ℝ) (t r : ℝ≥0) (x : Fin 1 → ℝ) :
    |J.nonnegativeProfileValue α l t x-J.nonnegativeProfileValue α b r x| ≤
      D^2*|l-b|+((B+3*D^2)/2)*|(t:ℝ)-r| := by
  have hh := J.profile_affine_comparison_general hD hB α hα l b t r x
  have hi := monotone_affine_l1_bound α.monotone α.nonneg hα l b t r t.coe_nonneg r.coe_nonneg
  have hm := mul_le_mul_of_nonneg_left hi (show 0 ≤ D^2/2 by positivity)
  nlinarith

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open Filter Set
open scoped Topology NNReal

 theorem continuous_of_uniform_response {X : Type*} [TopologicalSpace X]
    {f : ℝ → X → ℝ} {g : X → ℝ} {M : ℝ}
    (hf : ∀ s, Continuous (f s))
    (hr : ∀ s x, |f s x-f 0 x-s*g x| ≤ M*s^2) : Continuous g := by
  let r := fun k : ℕ => (1/2:ℝ)^k
  have hpos (k : ℕ) : 0 < r k := by dsimp [r]; positivity
  have hlim : Tendsto (fun k => M*r k) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).const_mul M
  have hb (k : ℕ) (x : X) : |(f (r k) x-f 0 x)/r k-g x| ≤ M*r k := by
    rw [div_sub' (ne_of_gt (hpos k)),abs_div,abs_of_pos (hpos k)]
    apply (div_le_div_of_nonneg_right (hr (r k) x) (hpos k).le).trans_eq
    field_simp
  have ht : TendstoUniformly (fun k x => (f (r k) x-f 0 x)/r k) g atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with k hk x
    rw [Real.dist_eq,abs_sub_comm]
    exact (hb k x).trans_lt hk
  exact ht.continuous (Eventually.of_forall (fun k => ((hf (r k)).sub (hf 0)).div_const (r k))).frequently

 theorem HeatJet.nonnegativeProfileValue_window_continuous (J : HeatJet 0)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1) (x : Fin 1 → ℝ) :
    Continuous (fun p : ℝ × ℝ≥0 => J.nonnegativeProfileValue α p.1 p.2 x) := by
  obtain ⟨D,_hD0,hD⟩ := (J.smoothG 0).bound
  obtain ⟨B,hB0,hB⟩ := (J.smoothH 0).bound
  let C := D^2+(B+3*D^2)/2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  suffices hs : LipschitzWith (Real.toNNReal C) (fun p : ℝ × ℝ≥0 => J.nonnegativeProfileValue α p.1 p.2 x) from
    hs.continuous
  apply LipschitzWith.of_dist_le_mul
  intro p q
  rw [Real.dist_eq,Real.coe_toNNReal _ hC]
  have hh := J.profile_window_stability_general hD hB α hα p.1 q.1 p.2 q.2 x
  have hp : |p.1-q.1| ≤ dist p q := by
    change dist p.1 q.1 ≤ dist p q
    exact le_max_left _ _
  have hq : |(p.2:ℝ)-q.2| ≤ dist p q := by
    change dist p.2 q.2 ≤ dist p q
    exact le_max_right _ _
  apply hh.trans
  dsimp only [C]
  nlinarith [mul_le_mul_of_nonneg_left hp (sq_nonneg D),
    mul_le_mul_of_nonneg_left hq (show 0 ≤ (B+3*D^2)/2 by positivity)]

 theorem HeatJet.nonnegativeProfileTest_window_continuous (J : HeatJet 0)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1) (x : Fin 1 → ℝ) :
    Continuous (fun p : ℝ × ℝ≥0 => J.nonnegativeProfileTest α p.1 p.2 x) := by
  obtain ⟨K,hK,hb⟩ := J.smoothA.bound
  apply continuous_of_uniform_response
    (f:=fun s (p : ℝ × ℝ≥0) => (J.terminalPerturb s).nonnegativeProfileValue α p.1 p.2 x)
    (M:=4*(K+1)^2)
  · intro s
    exact (J.terminalPerturb s).nonnegativeProfileValue_window_continuous α hα x
  · intro s p
    rw [J.nonnegativeProfile_perturb_zero]
    exact J.nonnegativeProfile_terminal_taylor (by linarith) (fun y => (hb y).trans (by linarith)) α hα p.1 p.2 s x

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open Filter Set
open scoped Topology NNReal

 theorem continuous_boundedProfile_test {n : ℕ} (J : HeatJet n)
    (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    Continuous (fun α : boundedMassProfiles =>
      J.nonnegativeProfileTest (boundedNonnegativeProfile α) l t x) := by
  obtain ⟨K,hK,hb⟩ := J.smoothA.bound
  apply continuous_of_uniform_response
    (f := fun s (α : boundedMassProfiles) =>
      (J.terminalPerturb s).nonnegativeProfileValue (boundedNonnegativeProfile α) l t x)
    (M := 4*(K+1)^2)
  · intro s
    exact continuous_boundedProfile_value (J.terminalPerturb s) l t x
  · intro s α
    rw [J.nonnegativeProfile_perturb_zero]
    exact J.nonnegativeProfile_terminal_taylor (by linarith)
      (fun y => (hb y).trans (by linarith)) (boundedNonnegativeProfile α)
      (fun u => (α.property.1 u).2) l t s x

end SKFluctuations.Hierarchy

end

end OAI
