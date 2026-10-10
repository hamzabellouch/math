import Mathlib
import OAI.Probability.SKFluctuations.ScalarClockRegularity
import OAI.Probability.SKFluctuations.ScalarProfileConcat

namespace OAI

/-! Scalar Arbitrary Concat. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem floor_clock_error (s : ℝ≥0) {h : ℝ≥0} (hh : 0 < h) :
    |((⌊(s:ℝ)/(h:ℝ)⌋₊:ℝ)*(h:ℝ))-(s:ℝ)| ≤ h := by
  have hp : (0:ℝ) < h := hh
  have hl := Nat.floor_le (show 0 ≤ (s:ℝ)/(h:ℝ) from div_nonneg s.coe_nonneg hp.le)
  have hu := Nat.lt_floor_add_one ((s:ℝ)/(h:ℝ))
  have hl' := (le_div_iff₀ hp).mp hl
  have hu' := (div_lt_iff₀ hp).mp hu
  rw [abs_of_nonpos (sub_nonpos.mpr hl')]
  nlinarith

 

theorem scalarProfile_concat (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (s t : ℝ≥0) (x : Fin 1 → ℝ) :
    scalarTerminal.nonnegativeProfileValue α l (s+t) x =
      (scalarProfileHeatJet α hα (l+s) t).nonnegativeProfileValue α l s x := by
  let X := scalarTerminal.nonnegativeProfileValue α l (s+t) x
  let Y := (scalarProfileHeatJet α hα (l+s) t).nonnegativeProfileValue α l s x
  have hb (h : ℝ≥0) (hh : 0 < h) : |X-Y| ≤ 7*(h:ℝ) := by
    let N := ⌊(s:ℝ)/(h:ℝ)⌋₊
    let M := ⌊(t:ℝ)/(h:ℝ)⌋₊
    let u : ℝ≥0 := (N:ℝ≥0)*h
    let v : ℝ≥0 := (M:ℝ≥0)*h
    have hsu : |(u:ℝ)-(s:ℝ)| ≤ h := floor_clock_error s hh
    have htv : |(v:ℝ)-(t:ℝ)| ≤ h := floor_clock_error t hh
    have hsum : |((s+t:ℝ≥0):ℝ)-((u+v:ℝ≥0):ℝ)| ≤ 2*(h:ℝ) := by
      simp only [NNReal.coe_add]
      have he : (s:ℝ)+t-((u:ℝ)+v) = ((s:ℝ)-u)+((t:ℝ)-v) := by ring
      rw [he]
      exact (abs_add_le _ _).trans (by rw [abs_sub_comm (s:ℝ),abs_sub_comm (t:ℝ)]; linarith)
    have hc := scalarProfile_multiple_concat α hα l h N M x
    have he : ((N+M:ℕ):ℝ≥0)*h = u+v := by simp only [Nat.cast_add,add_mul]; rfl
    rw [he] at hc
    change scalarTerminal.nonnegativeProfileValue α l (u+v) x =
      (scalarProfileHeatJet α hα (l+u) v).nonnegativeProfileValue α l u x at hc
    have hA := HeatJet.profile_window_stability scalarTerminal_admissible α hα l l (s+t) (u+v) x
    simp only [sub_self,abs_zero,zero_add] at hA
    have hB := scalarProfile_concat_stability α hα l u v s t x
    have htri := abs_sub_le X (scalarTerminal.nonnegativeProfileValue α l (u+v) x) Y
    rw [hc] at htri
    rw [hc] at hA
    change |X-(scalarProfileHeatJet α hα (l+u) v).nonnegativeProfileValue α l u x| ≤ _ at hA
    change |(scalarProfileHeatJet α hα (l+u) v).nonnegativeProfileValue α l u x-Y| ≤ _ at hB
    linarith
  have hp : Tendsto (fun k : ℕ => (1/2:ℝ)^k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hz : |X-Y| ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds
    (by simpa only [mul_zero] using hp.const_mul 7)
    (Eventually.of_forall (fun k => by
      have hh := hb ((1/2:ℝ≥0)^k) (by positivity)
      simpa only [NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] using hh))
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem HeatJet.profile_concat_grid_comparison (J R : HeatJet 0) {D B : ℝ}
    (hD : ∀ x, |J.G 0 x| ≤ D) (hB : ∀ x, |J.H 0 x| ≤ B)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (s t h : ℝ≥0) (N M : ℕ)
    (hR : R.F=J.nonnegativeProfileValue α (l+s) t) (x : Fin 1 → ℝ) :
    |J.nonnegativeProfileValue α l (((N+M:ℕ):ℝ≥0)*h) x-
      R.nonnegativeProfileValue α l ((N:ℝ≥0)*h) x| ≤
      D^2*|(N:ℝ)*h-s|+(B+3*D^2)/2*|(M:ℝ)*h-t| := by
  obtain ⟨DR,_hDR,hDR⟩ := (R.smoothG 0).bound
  have hA := J.multiple_grid_tendsto (fun _ => D) (fun i y => by fin_cases i; exact hD y) α hα l h (N+M) x
  have hB' := R.multiple_grid_tendsto (fun _ => DR) (fun i y => by fin_cases i; exact hDR y) α hα l h N x
  let E := D^2*|(N:ℝ)*h-s|+(B+3*D^2)/2*|(M:ℝ)*h-t|
  have hd (k : ℕ) :
      |(J.schedule ((α.cappedApprox k).linearGrid l (h/(2^k:ℝ≥0)) ((N+M)*2^k))).F x-
        (R.schedule ((α.cappedApprox k).linearGrid l (h/(2^k:ℝ≥0)) (N*2^k))).F x| ≤
      D^2/2*((h:ℝ)+(M:ℝ)*h)*(1/2:ℝ)^k+E := by
    have he : l+((N*2^k:ℕ):ℝ)*((h/(2^k:ℝ≥0):ℝ≥0):ℝ) = l+(N:ℝ)*h := by
      simp only [NNReal.coe_div,NNReal.coe_pow,NNReal.coe_ofNat,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      field_simp
    rw [add_mul,(α.cappedApprox k).linearGrid_add,he,J.schedule_append]
    apply HeatJet.schedule_nonexpansive _ R
    intro y
    rw [hR]
    have hg := J.multiple_grid_error (fun _ => D) (fun i y => by fin_cases i; exact hD y)
      α hα k (l+(N:ℝ)*h) h M y
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hg
    have hw := J.profile_window_stability_general hD hB α hα
      (l+(N:ℝ)*h) (l+s) ((M:ℝ≥0)*h) t y
    simp only [add_sub_add_left_eq_sub,NNReal.coe_mul,NNReal.coe_natCast] at hw
    exact (abs_sub_le _ (J.nonnegativeProfileValue α (l+(N:ℝ)*h) ((M:ℝ≥0)*h) y) _).trans
      (add_le_add hg hw)
  have hp : Tendsto (fun k : ℕ => D^2/2*((h:ℝ)+(M:ℝ)*h)*(1/2:ℝ)^k+E) atTop (𝓝 E) := by
    simpa only [mul_zero,zero_add] using ((tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).const_mul
        (D^2/2*((h:ℝ)+(M:ℝ)*h))).add_const E
  exact le_of_tendsto_of_tendsto (hA.sub hB').abs hp (Eventually.of_forall hd)

 theorem HeatJet.nonnegativeProfile_concat (J R : HeatJet 0)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (s t : ℝ≥0) (hR : R.F=J.nonnegativeProfileValue α (l+s) t)
    (x : Fin 1 → ℝ) :
    J.nonnegativeProfileValue α l (s+t) x = R.nonnegativeProfileValue α l s x := by
  obtain ⟨D,_hD0,hD⟩ := (J.smoothG 0).bound
  obtain ⟨B,hB0,hB⟩ := (J.smoothH 0).bound
  obtain ⟨DR,_hDR0,hDR⟩ := (R.smoothG 0).bound
  obtain ⟨BR,hBR0,hBR⟩ := (R.smoothH 0).bound
  let C := D^2+3*((B+3*D^2)/2)+(BR+3*DR^2)/2
  let X := J.nonnegativeProfileValue α l (s+t) x
  let Y := R.nonnegativeProfileValue α l s x
  have hb (h : ℝ≥0) (hh : 0 < h) : |X-Y| ≤ C*(h:ℝ) := by
    let N := ⌊(s:ℝ)/(h:ℝ)⌋₊
    let M := ⌊(t:ℝ)/(h:ℝ)⌋₊
    let u : ℝ≥0 := (N:ℝ≥0)*h
    let v : ℝ≥0 := (M:ℝ≥0)*h
    have hsu : |(u:ℝ)-(s:ℝ)| ≤ h := floor_clock_error s hh
    have htv : |(v:ℝ)-(t:ℝ)| ≤ h := floor_clock_error t hh
    have hsum : |((s+t:ℝ≥0):ℝ)-((u+v:ℝ≥0):ℝ)| ≤ 2*(h:ℝ) := by
      simp only [NNReal.coe_add]
      have he : (s:ℝ)+t-((u:ℝ)+v) = ((s:ℝ)-u)+((t:ℝ)-v) := by ring
      rw [he]
      exact (abs_add_le _ _).trans (by rw [abs_sub_comm (s:ℝ),abs_sub_comm (t:ℝ)]; linarith)
    have hc := J.profile_concat_grid_comparison R hD hB α hα l s t h N M hR x
    have he : ((N+M:ℕ):ℝ≥0)*h = u+v := by simp only [Nat.cast_add,add_mul]; rfl
    rw [he] at hc
    change |J.nonnegativeProfileValue α l (u+v) x-R.nonnegativeProfileValue α l u x| ≤
      D^2*|(u:ℝ)-s|+(B+3*D^2)/2*|(v:ℝ)-t| at hc
    have hA := J.profile_window_stability_general hD hB α hα l l (s+t) (u+v) x
    have hR' := R.profile_window_stability_general hDR hBR α hα l l u s x
    simp only [sub_self,abs_zero,mul_zero,zero_add] at hA hR'
    have htri := (abs_sub_le X (J.nonnegativeProfileValue α l (u+v) x) Y).trans
      (add_le_add hA ((abs_sub_le _ (R.nonnegativeProfileValue α l u x) _).trans (add_le_add hc hR')))
    have hBc : 0 ≤ (B+3*D^2)/2 := by positivity
    have hRc : 0 ≤ (BR+3*DR^2)/2 := by positivity
    dsimp only [C]
    apply htri.trans
    have h1 := mul_le_mul_of_nonneg_left hsum hBc
    have h2 := mul_le_mul_of_nonneg_left hsu (sq_nonneg D)
    have h3 := mul_le_mul_of_nonneg_left htv hBc
    have h4 := mul_le_mul_of_nonneg_left hsu hRc
    nlinarith
  have hp : Tendsto (fun k : ℕ => (1/2:ℝ)^k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hz : |X-Y| ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds
    (by simpa only [mul_zero] using hp.const_mul C)
    (Eventually.of_forall (fun k => by
      have hh := hb ((1/2:ℝ≥0)^k) (by positivity)
      simpa only [NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] using hh))
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem HeatJet.nonnegativeProfileTest_remainder_bound {n : ℕ} (J K B : HeatJet n)
    (hK : K.F=J.F) (hB : B.F=J.F) {c E : ℝ}
    (hE : ∀ y, |K.A y-J.A y-c*B.A y| ≤ E)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    |K.nonnegativeProfileTest α l t x-J.nonnegativeProfileTest α l t x-
      c*B.nonnegativeProfileTest α l t x| ≤ E := by
  apply le_of_tendsto ((((K.capped_test_tendstoUniformly α hα l t).tendsto_at x).sub
    ((J.capped_test_tendstoUniformly α hα l t).tendsto_at x)).sub
      (((B.capped_test_tendstoUniformly α hα l t).tendsto_at x).const_mul c)).abs
  apply Eventually.of_forall
  intro k
  let cs := heatSteps (ι := Fin (n+1)) ((α.cappedApprox k).grid l t k)
  have ho : PrefixOrdered 0 1 cs := ((α.cappedApprox k).grid_ordered l t k le_rfl
    (α.cappedApprox k |>.positive l).le (α.cappedApprox_le_one hα k _)).prefixOrdered
  have hb := prefixTest_abs_le J.lipschitz ((K.smoothA.sub J.smoothA).sub
    (B.smoothA.const_mul c)) hE cs ho.positive x
  rw [prefixTest_subtract J.lipschitz (K.smoothA.sub J.smoothA) (B.smoothA.const_mul c) cs ho.positive x,
    prefixTest_subtract J.lipschitz K.smoothA J.smoothA cs ho.positive x] at hb
  have he := prefixTest_affine J.lipschitz B.smoothA cs ho.positive (0:ℝ) c x
  simp only [zero_add] at he
  rw [he] at hb
  simpa only [HeatJet.schedule_A_prefix,hK,hB,cs] using hb

 theorem hasDerivAt_of_quadratic_remainder_on {f : ℝ → ℝ} {a b s d M : ℝ}
    (hs : s ∈ Ioo a b)
    (hr : ∀ u ∈ Ioo a b, |f u-f s-(u-s)*d| ≤ M*|u-s|^2) :
    HasDerivAt f d s := by
  rw [hasDerivAt_iff_tendsto]
  have hlim : Tendsto (fun u : ℝ => M*|u-s|) (𝓝 s) (𝓝 0) := by
    simpa only [id_eq,sub_self,abs_zero,mul_zero] using
      ((tendsto_id.sub_const s).abs.const_mul M :
        Tendsto (fun u : ℝ => M*|u-s|) (𝓝 s) (𝓝 (M*|s-s|)))
  apply squeeze_zero' (Eventually.of_forall fun _ =>
    mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)) _ hlim
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with u hu
  simp only [Real.norm_eq_abs,smul_eq_mul]
  apply (mul_le_mul_of_nonneg_left (hr u hu) (inv_nonneg.mpr (abs_nonneg (u-s)))).trans
  by_cases he : u=s
  · subst u; simp
  · have hn : |u-s| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr he)
    apply le_of_eq
    field_simp

 theorem second_derivative_remainder_on {f g h : ℝ → ℝ} {a b M : ℝ}
    (hf : ∀ u ∈ Ioo a b, HasDerivAt f (g u) u)
    (hg : ∀ u ∈ Ioo a b, HasDerivAt g (h u) u)
    (hh : ∀ u ∈ Ioo a b, |h u| ≤ M) {s t : ℝ}
    (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    |f t-f s-(t-s)*g s| ≤ M*|t-s|^2 := by
  have hb {u v : ℝ} (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) :
      |g v-g u| ≤ M*|v-u| := by
    simpa only [Real.norm_eq_abs] using (convex_Ioo a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (hg y hy).hasDerivWithinAt) (fun y hy => by simpa only [Real.norm_eq_abs] using hh y hy) hu hv
  have hline (y : ℝ) (hy : y ∈ Ioo a b) :
      HasDerivAt (fun z => f z-z*g s) (g y-g s) y := by
    convert (hf y hy).sub ((hasDerivAt_id y).mul_const (g s)) using 1 <;>
      first | rfl | simp only [one_mul]
  have hsub : uIcc s t ⊆ Ioo a b := (convex_Ioo a b).ordConnected.uIcc_subset hs ht
  have hM : 0 ≤ M := (abs_nonneg (h s)).trans (hh s hs)
  have hd := (convex_uIcc s t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y hy => (hline y (hsub hy)).hasDerivWithinAt)
    (fun y hy => show ‖g y-g s‖ ≤ M*|t-s| from by
      rw [Real.norm_eq_abs]
      apply (hb hs (hsub hy)).trans
      apply mul_le_mul_of_nonneg_left _ hM
      simpa only [Real.dist_eq,abs_sub_comm] using Real.dist_left_le_of_mem_uIcc hy)
    left_mem_uIcc right_mem_uIcc
  have he : (f t-t*g s)-(f s-s*g s) = f t-f s-(t-s)*g s := by ring
  rw [Real.norm_eq_abs,he,Real.norm_eq_abs] at hd
  exact hd.trans_eq (by ring)

 theorem HeatJet.nonnegativeProfileTest_hasDerivAt {n : ℕ} (J B : ℝ → HeatJet n)
    {a b s M : ℝ} (hs : s ∈ Ioo a b)
    (hF : ∀ u, (J u).F=(J s).F) (hB : (B s).F=(J s).F)
    (R : ℝ → (Fin (n+1) → ℝ) → ℝ)
    (hd : ∀ u ∈ Ioo a b, ∀ y, HasDerivAt (fun v => (J v).A y) ((B u).A y) u)
    (hdB : ∀ u ∈ Ioo a b, ∀ y, HasDerivAt (fun v => (B v).A y) (R u y) u)
    (hb : ∀ u ∈ Ioo a b, ∀ y, |R u y| ≤ M)
    (α : NonnegativeMassProfile) (hα : ∀ u, α.mass u ≤ 1)
    (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun u => (J u).nonnegativeProfileTest α l t x)
      ((B s).nonnegativeProfileTest α l t x) s := by
  apply hasDerivAt_of_quadratic_remainder_on (M:=M) hs
  intro u hu
  apply (J s).nonnegativeProfileTest_remainder_bound (J u) (B s) (hF u) hB _ α hα
  intro y
  exact second_derivative_remainder_on (fun v hv => hd v hv y)
    (fun v hv => hdB v hv y) (fun v hv => hb v hv y) hs hu

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem HeatJet.nonnegativeProfileTest_congr_ae {n : ℕ} (J : HeatJet n)
    (α β : NonnegativeMassProfile) (hα : ∀ u, α.mass u ≤ 1) (hβ : ∀ u, β.mass u ≤ 1)
    (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ)
    (he : α.mass =ᵐ[volume.restrict (Ioc l (l+t))] β.mass) :
    J.nonnegativeProfileTest α l t x=J.nonnegativeProfileTest β l t x := by
  have hf : (fun u => (J.terminalPerturb u).nonnegativeProfileValue α l t x)=
      fun u => (J.terminalPerturb u).nonnegativeProfileValue β l t x := by
    funext u
    exact (J.terminalPerturb u).nonnegativeProfileValue_congr_ae α β l t x he
  exact (J.nonnegativeProfile_terminal_deriv_zero α hα l t x).unique
    (hf ▸ J.nonnegativeProfile_terminal_deriv_zero β hβ l t x)

 theorem HeatJet.nonnegativeProfileValue_constant_Ioo {n : ℕ} (J : HeatJet n)
    (α : NonnegativeMassProfile) {m : ℝ} (hm : 0 < m) (l : ℝ) (t : ℝ≥0)
    (ht : 0 < (t:ℝ)) (hc : ∀ u ∈ Ioo l (l+t), α.mass u=m)
    (x : Fin (n+1) → ℝ) :
    J.nonnegativeProfileValue α l t x=clockContinuation m J.F t x := by
  let β : NonnegativeMassProfile := ⟨fun _ => m,fun _ => hm.le,monotone_const⟩
  have he : α.mass =ᵐ[volume.restrict (Ioc l (l+t))] β.mass := by
    refine ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact hc u hu
  rw [J.nonnegativeProfileValue_congr_ae α β l t x he]
  exact J.nonnegativeProfileValue_constant β hm l t ht (fun _ _ => rfl) x

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem HeatJet.clock_terminal_deriv {n : ℕ} (J : HeatJet n) {m : ℝ} (hm : 0 < m)
    (t s : ℝ) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun u => clockContinuation m (J.terminalPerturb u).F t x)
      (clockTest m (J.terminalPerturb s).F J.A t x) s := by
  obtain ⟨K,hK,hb⟩ := J.smoothA.bound
  exact prefixContinuation_terminal_deriv J.lipschitz J.test_lipschitz.choose_spec hK hb
    [(m,fun _ => Real.toNNReal t)] (by intro st hs; rw [List.mem_singleton] at hs; subst st; exact hm) s x

 theorem HeatJet.clock_terminal_taylor {n : ℕ} (J : HeatJet n) {m K : ℝ}
    (hm : 0 < m) (hm1 : m ≤ 1) (hK : 0 < K) (hA : ∀ y, |J.A y| ≤ K)
    (t s : ℝ) (x : Fin (n+1) → ℝ) :
    |clockContinuation m (J.terminalPerturb s).F t x-clockContinuation m J.F t x-
      s*clockTest m J.F J.A t x| ≤ 4*K^2*s^2 := by
  let cs : List (GaussianStep (Fin (n+1))) := [(m,fun _ => Real.toNNReal t)]
  have ho : PrefixOrdered 0 1 cs := ⟨le_rfl,hm.le,hm,hm.le,hm1⟩
  have hd := lipschitz_derivative_remainder (M:=4*K^2) (by positivity)
    (fun u => J.clock_terminal_deriv hm t u x)
    (fun u v => by
      simpa only [mul_one,cs,prefixTest,prefixContinuation,clockTest,HeatJet.terminalPerturb] using prefixTest_terminal_lipschitz_bound J.lipschitz
        J.test_lipschitz.choose_spec hK hA cs ho u v x) 0 s
  have hz : (J.terminalPerturb 0).F=J.F := by
    funext y
    change J.F y+0*J.A y=J.F y
    ring
  rw [hz] at hd
  simpa only [sub_zero,sq_abs] using hd

 theorem HeatJet.nonnegativeProfile_clock_concat (J : HeatJet 0)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    {m : ℝ} (hm : 0 < m) (l : ℝ) (s t : ℝ≥0) (ht : 0 < (t:ℝ))
    (hc : ∀ u ∈ Ioo (l+s) (l+s+t), α.mass u=m) (x : Fin 1 → ℝ) :
    J.nonnegativeProfileValue α l (s+t) x =
      (J.evolve hm t).nonnegativeProfileValue α l s x := by
  apply J.nonnegativeProfile_concat (J.evolve hm t) α hα l s t _ x
  funext y
  exact (J.nonnegativeProfileValue_constant_Ioo α hm (l+s) t ht hc y).symm

 theorem HeatJet.nonnegativeProfileTest_clock_concat (J : HeatJet 0)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (l : ℝ) (s t : ℝ≥0) (ht : 0 < (t:ℝ))
    (hc : ∀ u ∈ Ioo (l+s) (l+s+t), α.mass u=m) (x : Fin 1 → ℝ) :
    J.nonnegativeProfileTest α l (s+t) x =
      (J.evolve hm t).nonnegativeProfileTest α l s x := by
  obtain ⟨K,hK,hA⟩ := J.smoothA.bound
  have hK' : 0 < K+1 := by linarith
  have hb (y) : |J.A y| ≤ K+1 := (hA y).trans (by linarith)
  have hbe (y) : |(J.evolve hm t).A y| ≤ K+1 :=
    clockTest_abs_le J.lipschitz J.smoothA hb m t y
  have hd : HasDerivAt (fun u => ((J.terminalPerturb u).evolve hm t).nonnegativeProfileValue α l s x)
      ((J.evolve hm t).nonnegativeProfileTest α l s x) 0 := by
    apply hasDerivAt_of_quadratic_remainder_on (a:= -1) (b:=1) (M:=8*(K+1)^2) (by norm_num)
    intro u _
    have he := (J.evolve hm t).nonnegativeProfile_response_error
      ((J.terminalPerturb u).evolve hm t) hK' hbe (E:=4*(K+1)^2*u^2)
      (fun y => by
        change |clockContinuation m (J.terminalPerturb u).F t y-
          (clockContinuation m J.F t y+u*clockTest m J.F J.A t y)| ≤ _
        rw [sub_add_eq_sub_sub]
        exact J.clock_terminal_taylor hm hm1 hK' hb t u y) α hα l s x
    have hzero : ((J.terminalPerturb 0).evolve hm t).nonnegativeProfileValue α l s x =
        (J.evolve hm t).nonnegativeProfileValue α l s x := by
      apply congrFun (HeatJet.nonnegativeProfileValue_congr_potential _ _ _ α l s) x
      change clockContinuation m (fun y => J.F y+0*J.A y) t=clockContinuation m J.F t
      simp only [zero_mul,add_zero]
    rw [hzero,sub_zero,sq_abs]
    exact he.trans_eq (by ring)
  have he : (fun u => (J.terminalPerturb u).nonnegativeProfileValue α l (s+t) x)=
      fun u => ((J.terminalPerturb u).evolve hm t).nonnegativeProfileValue α l s x := by
    funext u
    exact (J.terminalPerturb u).nonnegativeProfile_clock_concat α hα hm l s t ht hc x
  exact (J.nonnegativeProfile_terminal_deriv_zero α hα l (s+t) x).unique (he ▸ hd)

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem HeatJet.nonnegativeProfileTest_zero {n : ℕ} (J : HeatJet n)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1) (l : ℝ)
    (x : Fin (n+1) → ℝ) : J.nonnegativeProfileTest α l 0 x = J.A x := by
  have he : (fun u => (J.terminalPerturb u).nonnegativeProfileValue α l 0 x) =
      fun u => J.F x+u*J.A x := by
    funext u
    choose D _hD hD using fun i => ((J.terminalPerturb u).smoothG i).bound
    exact (J.terminalPerturb u).nonnegativeProfile_zero D hD α hα l x
  have hd := J.nonnegativeProfile_terminal_deriv_zero α hα l 0 x
  rw [he] at hd
  have hh := ((hasDerivAt_id (0:ℝ)).mul_const (J.A x)).const_add (J.F x)
  simpa only [one_mul] using hd.unique hh

theorem HeatJet.nonnegativeProfileTest_constant_Ioo (J : HeatJet 0)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (l : ℝ) (t : ℝ≥0)
    (ht : 0 < (t:ℝ)) (hc : ∀ u ∈ Ioo l (l+t), α.mass u=m)
    (x : Fin 1 → ℝ) : J.nonnegativeProfileTest α l t x = clockTest m J.F J.A t x := by
  have hh := J.nonnegativeProfileTest_clock_concat α hα hm hm1 l 0 t ht (by simpa using hc) x
  simp only [zero_add] at hh
  rw [hh,HeatJet.nonnegativeProfileTest_zero _ α hα]
  rfl

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Scalar
open Set Filter
open scoped Topology ContDiff

theorem spatialJet_three_timePDE {u : ℝ × ℝ → ℝ} {m : ℝ}
    (hu : ∀ k : ℕ, ContDiffOn ℝ k u {p : ℝ × ℝ | 0 < p.1})
    (hPDE : ∀ t x, 0 < t → HasDerivAt (fun s => u (s,x))
      ((1/2:ℝ)*(spatialJet u 2 (t,x)+m*(spatialJet u 1 (t,x))^2)) t)
    {t x : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => spatialJet u 3 (s,x))
      ((1/2:ℝ)*spatialJet u 5 (t,x)+m*(3*spatialJet u 2 (t,x)*spatialJet u 3 (t,x)+
        spatialJet u 1 (t,x)*spatialJet u 4 (t,x))) t := by
  have hS : IsOpen {p : ℝ × ℝ | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hd (r) := spatialJet_hasDerivAt hS hu r (x := x) ht
  have hh := ((hd 4).const_mul (1/2:ℝ)).add
    ((((hd 2).pow 2).add ((hd 1).mul (hd 3))).const_mul m)
  apply spacePartial_hasDerivAt_time_of_timePDE
    (V := fun p => (1/2:ℝ)*spatialJet u 4 p+m*((spatialJet u 2 p)^2+spatialJet u 1 p*spatialJet u 3 p))
    (spatialJet_contDiffOn hS hu 2 2)
    (fun s y hs => spatialJet_two_timePDE hu hPDE (x := y) hs) ht
  convert hh using 1
  first | rfl | ring

theorem spatialJet_four_timePDE {u : ℝ × ℝ → ℝ} {m : ℝ}
    (hu : ∀ k : ℕ, ContDiffOn ℝ k u {p : ℝ × ℝ | 0 < p.1})
    (hPDE : ∀ t x, 0 < t → HasDerivAt (fun s => u (s,x))
      ((1/2:ℝ)*(spatialJet u 2 (t,x)+m*(spatialJet u 1 (t,x))^2)) t)
    {t x : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => spatialJet u 4 (s,x))
      ((1/2:ℝ)*spatialJet u 6 (t,x)+m*(3*(spatialJet u 3 (t,x))^2+
        4*spatialJet u 2 (t,x)*spatialJet u 4 (t,x)+spatialJet u 1 (t,x)*spatialJet u 5 (t,x))) t := by
  have hS : IsOpen {p : ℝ × ℝ | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hd (r) := spatialJet_hasDerivAt hS hu r (x := x) ht
  have hh := ((hd 5).const_mul (1/2:ℝ)).add
    (((((hd 2).const_mul 3).mul (hd 3)).add ((hd 1).mul (hd 4))).const_mul m)
  apply spacePartial_hasDerivAt_time_of_timePDE
    (V := fun p => (1/2:ℝ)*spatialJet u 5 p+m*(3*spatialJet u 2 p*spatialJet u 3 p+spatialJet u 1 p*spatialJet u 4 p))
    (spatialJet_contDiffOn hS hu 3 2)
    (fun s y hs => spatialJet_three_timePDE hu hPDE (x := y) hs) ht
  convert hh using 1
  first | rfl | ring

theorem spatialJet_five_timePDE {u : ℝ × ℝ → ℝ} {m : ℝ}
    (hu : ∀ k : ℕ, ContDiffOn ℝ k u {p : ℝ × ℝ | 0 < p.1})
    (hPDE : ∀ t x, 0 < t → HasDerivAt (fun s => u (s,x))
      ((1/2:ℝ)*(spatialJet u 2 (t,x)+m*(spatialJet u 1 (t,x))^2)) t)
    {t x : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => spatialJet u 5 (s,x))
      ((1/2:ℝ)*spatialJet u 7 (t,x)+m*(10*spatialJet u 3 (t,x)*spatialJet u 4 (t,x)+
        5*spatialJet u 2 (t,x)*spatialJet u 5 (t,x)+spatialJet u 1 (t,x)*spatialJet u 6 (t,x))) t := by
  have hS : IsOpen {p : ℝ × ℝ | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hd (r) := spatialJet_hasDerivAt hS hu r (x := x) ht
  have hh := ((hd 6).const_mul (1/2:ℝ)).add
    (((((hd 3).pow 2).const_mul 3).add (((hd 2).const_mul 4).mul (hd 4)) |>.add
      ((hd 1).mul (hd 5))).const_mul m)
  apply spacePartial_hasDerivAt_time_of_timePDE
    (V := fun p => (1/2:ℝ)*spatialJet u 6 p+m*(3*(spatialJet u 3 p)^2+
      4*spatialJet u 2 p*spatialJet u 4 p+spatialJet u 1 p*spatialJet u 5 p))
    (spatialJet_contDiffOn hS hu 4 2)
    (fun s y hs => spatialJet_four_timePDE hu hPDE (x := y) hs) ht
  convert hh using 1
  first | rfl | ring

theorem realSpatialJet_time_transfer {u : ℝ × ℝ → ℝ}
    (hu : ∀ k : ℕ, ContDiffOn ℝ k u {p : ℝ × ℝ | 0 < p.1})
    {t x v : ℝ} (ht : 0 < t) (k : ℕ)
    (hd : HasDerivAt (fun s => spatialJet u k (s,x)) v t) :
    HasDerivAt (fun s => realSpatialJet u k (s,x)) v t := by
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact realSpatialJet_eq_spatialJet hu hs k x

end SKFluctuations.Scalar

 

 

namespace SKFluctuations.Scalar

noncomputable def invariantP (a h p q : ℝ) : ℝ := -a*h^3-h*q/2+p^2/2
noncomputable def invariantQ (h p q r : ℝ) : ℝ := -h^2*r/2+2*h*p*q-3*p^3/2
noncomputable def invariantR (a h p q r : ℝ) : ℝ := invariantQ h p q r+3*p*invariantP a h p q/2

noncomputable def invariantPD (a h p q dh dp dq : ℝ) : ℝ :=
  -3*a*h^2*dh-(dh*q+h*dq)/2+p*dp
noncomputable def invariantQD (h p q r dh dp dq dr : ℝ) : ℝ :=
  -h*dh*r-h^2*dr/2+2*dh*p*q+2*h*dp*q+2*h*p*dq-9*p^2*dp/2
noncomputable def invariantRD (a h p q r dh dp dq dr : ℝ) : ℝ :=
  invariantQD h p q r dh dp dq dr+3*(dp*invariantP a h p q+p*invariantPD a h p q dh dp dq)/2

noncomputable def invariantPx (a h p q r : ℝ) : ℝ := -3*a*h^2*p-h*r/2+p*q/2
noncomputable def invariantPxx (a h p q _r s : ℝ) : ℝ := -6*a*h*p^2-3*a*h^2*q-h*s/2+q^2/2
noncomputable def invariantQx (h p q r s : ℝ) : ℝ := -h^2*s/2+h*p*r+2*h*q^2-5*p^2*q/2
noncomputable def invariantQxx (h p q r _s w : ℝ) : ℝ := -h^2*w/2+5*h*q*r-3*p^2*r/2-3*p*q^2
noncomputable def invariantRx (a h p q r s : ℝ) : ℝ :=
  invariantQx h p q r s+3*(q*invariantP a h p q+p*invariantPx a h p q r)/2
noncomputable def invariantRxx (a h p q r s w : ℝ) : ℝ :=
  invariantQxx h p q r s w+3*(r*invariantP a h p q+2*q*invariantPx a h p q r+
    p*invariantPxx a h p q r s)/2

theorem hasDerivAt_invariantP {h p q : ℝ → ℝ} {dh dp dq x : ℝ}
    (a : ℝ) (hh : HasDerivAt h dh x) (hp : HasDerivAt p dp x) (hq : HasDerivAt q dq x) :
    HasDerivAt (fun y => invariantP a (h y) (p y) (q y))
      (invariantPD a (h x) (p x) (q x) dh dp dq) x := by
  have hd := ((((hh.pow 3).const_mul (-a)).sub ((hh.mul hq).div_const 2)).add ((hp.pow 2).div_const 2))
  convert hd using 1 <;> first | rfl | (dsimp only [invariantPD, Pi.pow_apply, Pi.mul_apply, Pi.neg_apply]; ring)

theorem hasDerivAt_invariantQ {h p q r : ℝ → ℝ} {dh dp dq dr x : ℝ}
    (hh : HasDerivAt h dh x) (hp : HasDerivAt p dp x) (hq : HasDerivAt q dq x)
    (hr : HasDerivAt r dr x) :
    HasDerivAt (fun y => invariantQ (h y) (p y) (q y) (r y))
      (invariantQD (h x) (p x) (q x) (r x) dh dp dq dr) x := by
  have hd := (((((hh.pow 2).neg.mul hr).div_const 2).add
    ((((hh.const_mul 2).mul hp).mul hq))).sub (((hp.pow 3).const_mul 3).div_const 2))
  convert hd using 1 <;> first | rfl | (dsimp only [invariantQD, Pi.pow_apply, Pi.mul_apply, Pi.neg_apply]; ring)

theorem hasDerivAt_invariantR {h p q r : ℝ → ℝ} {dh dp dq dr x : ℝ}
    (a : ℝ) (hh : HasDerivAt h dh x) (hp : HasDerivAt p dp x) (hq : HasDerivAt q dq x)
    (hr : HasDerivAt r dr x) :
    HasDerivAt (fun y => invariantR a (h y) (p y) (q y) (r y))
      (invariantRD a (h x) (p x) (q x) (r x) dh dp dq dr) x := by
  have hd := (hasDerivAt_invariantQ hh hp hq hr).add
    (((hp.const_mul 3).mul (hasDerivAt_invariantP a hh hp hq)).div_const 2)
  convert hd using 1 <;> first | rfl | (dsimp only [invariantRD]; ring)

theorem invariantPD_space (a h p q r : ℝ) :
    invariantPD a h p q p q r = invariantPx a h p q r := by
  dsimp only [invariantPD,invariantPx]; ring

theorem invariantQD_space (h p q r s : ℝ) :
    invariantQD h p q r p q r s = invariantQx h p q r s := by
  dsimp only [invariantQD,invariantQx]; ring

theorem invariantRD_space (a h p q r s : ℝ) :
    invariantRD a h p q r p q r s = invariantRx a h p q r s := by
  simp only [invariantRD,invariantRx,invariantPD_space,invariantQD_space]

theorem hasDerivAt_invariantPx {h p q r : ℝ → ℝ} {x s : ℝ}
    (a : ℝ) (hh : HasDerivAt h (p x) x) (hp : HasDerivAt p (q x) x)
    (hq : HasDerivAt q (r x) x) (hr : HasDerivAt r s x) :
    HasDerivAt (fun y => invariantPx a (h y) (p y) (q y) (r y))
      (invariantPxx a (h x) (p x) (q x) (r x) s) x := by
  have hd := (((((hh.pow 2).const_mul (-3*a)).mul hp).sub ((hh.mul hr).div_const 2)).add
    ((hp.mul hq).div_const 2))
  convert hd using 1 <;> first | rfl | (dsimp only [invariantPxx, Pi.pow_apply, Pi.mul_apply]; ring)

theorem hasDerivAt_invariantQx {h p q r s : ℝ → ℝ} {x w : ℝ}
    (hh : HasDerivAt h (p x) x) (hp : HasDerivAt p (q x) x)
    (hq : HasDerivAt q (r x) x) (hr : HasDerivAt r (s x) x) (hs : HasDerivAt s w x) :
    HasDerivAt (fun y => invariantQx (h y) (p y) (q y) (r y) (s y))
      (invariantQxx (h x) (p x) (q x) (r x) (s x) w) x := by
  have hd := ((((((hh.pow 2).neg.mul hs).div_const 2).add ((hh.mul hp).mul hr)).add
    ((hh.const_mul 2).mul (hq.pow 2))).sub ((((hp.pow 2).const_mul 5).mul hq).div_const 2))
  convert hd using 1 <;> first | rfl | (dsimp only [invariantQxx, Pi.pow_apply, Pi.mul_apply, Pi.neg_apply]; ring)

theorem hasDerivAt_invariantRx {h p q r s : ℝ → ℝ} {x w : ℝ}
    (a : ℝ) (hh : HasDerivAt h (p x) x) (hp : HasDerivAt p (q x) x)
    (hq : HasDerivAt q (r x) x) (hr : HasDerivAt r (s x) x) (hs : HasDerivAt s w x) :
    HasDerivAt (fun y => invariantRx a (h y) (p y) (q y) (r y) (s y))
      (invariantRxx a (h x) (p x) (q x) (r x) (s x) w) x := by
  have hd := (hasDerivAt_invariantQx hh hp hq hr hs).add
    ((((hq.mul (hasDerivAt_invariantP a hh hp hq)).add
      (hp.mul (hasDerivAt_invariantPx a hh hp hq hr))).const_mul 3).div_const 2)
  convert hd using 1 <;> first | rfl | (simp only [invariantRxx,invariantPD_space]; ring)

theorem invariantP_time_algebra (a g h p q r s : ℝ) (hh : h ≠ 0) :
    invariantPD a h p q (q/2+a*(h^2+g*p)) (r/2+a*(3*h*p+g*q))
      (s/2+a*(3*p^2+4*h*q+g*r)) =
    invariantPxx a h p q r s/2+(a*g-p/h)*invariantPx a h p q r+
      (q/h+3*a*h)*invariantP a h p q := by
  dsimp only [invariantPD,invariantPxx,invariantPx,invariantP]
  field_simp [hh]
  ring

theorem invariantQ_time_algebra (a g h p q r s w : ℝ) (hh : h ≠ 0) :
    invariantQD h p q r (q/2+a*(h^2+g*p)) (r/2+a*(3*h*p+g*q))
      (s/2+a*(3*p^2+4*h*q+g*r)) (w/2+a*(10*p*q+5*h*r+g*s)) =
    invariantQxx h p q r s w/2+(a*g-2*p/h)*invariantQx h p q r s+
      (4*q/h-(p/h)^2+7*a*h)*invariantQ h p q r-
      3*p*(p^2-h*q)*invariantP a h p q/h^2 := by
  dsimp only [invariantQD,invariantQxx,invariantQx,invariantQ,invariantP]
  field_simp [hh]
  ring

theorem invariantR_time_algebra (a g h p q r s w : ℝ) (hh : h ≠ 0) :
    invariantRD a h p q r (q/2+a*(h^2+g*p)) (r/2+a*(3*h*p+g*q))
      (s/2+a*(3*p^2+4*h*q+g*r)) (w/2+a*(10*p*q+5*h*r+g*s)) =
    invariantRxx a h p q r s w/2+(a*g-2*p/h)*invariantRx a h p q r s+
      (3*(p/h)^2/4+9*q/(4*h)+13*a*h/2)*invariantR a h p q r-
      invariantP a h p q*invariantQ h p q r/(2*h^2)+3*p*(invariantP a h p q)^2/(4*h^2) := by
  dsimp only [invariantRD,invariantRxx,invariantRx,invariantR,invariantQD,invariantPD,
    invariantQxx,invariantQx,invariantPx,invariantPxx,invariantQ,invariantP]
  field_simp [hh]
  ring

end SKFluctuations.Scalar

end

end OAI
