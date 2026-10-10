import Mathlib
import OAI.Probability.SKFluctuations.ClockFlattenSchedule

namespace OAI

/-! Scalar General Head Balance. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem scalarMinimizer_head_derivative_lower {T q r m : ℝ} (hT : 0 < T)
    (hq : 0 < q) (hqr : q ≤ r) (hr : r ≤ 1)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles) (hm : 0 < m) (hmr : m < α.val r)
    (hf : ∀ s ∈ Ico (0:ℝ) q, α.val s = m)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    -T*(r-q) ≤ (1/2:ℝ)*(∫ s in 0..T*q, (scalarTailJet hT α q).filledSquare hm (T*q) s 0)-T*q^2/4 := by
  have hm1 : m < 1 := hmr.trans_le (α.property.1 r).2
  have hmq : m ≤ α.val q := by
    rw [← hf 0 ⟨le_rfl,hq⟩]
    exact α.property.2 hq.le
  have hd := (hasDerivAt_iff_tendsto_slope_left_right.mp
    (scalarHeadValue_hasDerivAt hT hq.le α hm hm1)).2
  apply ge_of_tendsto hd
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ b : ℝ in 𝓝[>] m, b < α.val r from
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hmr))] with b hmb hbr
  have hb : 0 < b := hm.trans hmb
  have hb1 : b ≤ 1 := hbr.le.trans (α.property.1 r).2
  let β := floorMassProfile α hb.le hb1
  have hβ := floorMassProfile_mem hα hb.le hb1
  have hdiff := scalarParisiValue_head_error hT hq hqr hr α β hm hb hf
    (fun s hs => floorMassProfile_head α hb.le hb1 hmb.le hf hs)
    (fun s hs => floorMassProfile_bound α hb.le hb1 hmb.le (hq.le.trans hs.1.le)
      (hmq.trans (α.property.2 hs.1.le)))
    (fun s hs => floorMassProfile_tail α (hq.le.trans hqr) hb.le hb1 hbr.le hs.1.le)
  have hminβ := hmin β hβ
  have hlo : -T*(b-m)*(r-q) ≤ scalarHeadValue hT α q b-scalarHeadValue hT α q m := by
    have hh := (abs_le.mp hdiff).2
    linarith
  rw [slope_def_field]
  apply (le_div_iff₀ (sub_pos.mpr hmb)).mpr
  nlinarith

 

theorem scalarMinimizer_head_balance {T q m : ℝ} (hT : 0 < T)
    (hq : q ∈ Ioo (0:ℝ) 1) (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hm : 0 < m) (hm1 : m < 1)
    (hf : ∀ s ∈ Ico (0:ℝ) q, α.val s = m)
    (hrise : ∀ r ∈ Ioc q 1, m < α.val r)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    2*(∫ s in 0..T*q, (scalarTailJet hT α q).filledSquare hm (T*q) s 0) = T*q^2 := by
  let D := (1/2:ℝ)*(∫ s in 0..T*q, (scalarTailJet hT α q).filledSquare hm (T*q) s 0)-T*q^2/4
  have hD : D ≤ 0 := scalarMinimizer_head_derivative_nonpos hT ⟨hq.1,hq.2.le⟩ α hα hm hm1 hf hmin
  have hlim : Tendsto (fun r : ℝ => -T*(r-q)) (𝓝[>] q) (𝓝 0) := by
    simpa only [sub_self,mul_zero] using
      (tendsto_const_nhds.mul ((tendsto_id.mono_left nhdsWithin_le_nhds).sub_const q) :
        Tendsto (fun r : ℝ => -T*(r-q)) (𝓝[>] q) (𝓝 (-T*(q-q))))
  have hD0 : 0 ≤ D := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ r : ℝ in 𝓝[>] q, r < 1 from
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hq.2))] with r hqr hr
    exact scalarMinimizer_head_derivative_lower hT hq.1 hqr.le hr.le α hα hm
      (hrise r ⟨hqr,hr.le⟩) hf hmin
  dsimp [D] at hD hD0
  linarith

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem scalarTailJet_restart {T q r : ℝ} (hT : 0 < T) (hqr : q ≤ r) (hr : r ≤ 1)
    (α : boundedMassProfiles) :
    (scalarTailJet hT α q).F = (scalarTailJet hT α r).nonnegativeProfileValue
      (rescaledMassProfile α hT) (T*q) (Real.toNNReal (T*(r-q))) := by
  funext x
  have hs : 0 ≤ T*(r-q) := mul_nonneg hT.le (sub_nonneg.mpr hqr)
  have ht : 0 ≤ T*(1-r) := mul_nonneg hT.le (sub_nonneg.mpr hr)
  have hq : 0 ≤ T*(1-q) := mul_nonneg hT.le (sub_nonneg.mpr (hqr.trans hr))
  have he : Real.toNNReal (T*(r-q))+Real.toNNReal (T*(1-r)) = Real.toNNReal (T*(1-q)) := by
    apply NNReal.eq
    simp only [NNReal.coe_add,Real.coe_toNNReal _ hs,Real.coe_toNNReal _ ht,Real.coe_toNNReal _ hq]
    ring
  have hh := scalarProfile_concat (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2)
    (T*q) (Real.toNNReal (T*(r-q))) (Real.toNNReal (T*(1-r))) x
  rw [he] at hh
  simp only [Real.coe_toNNReal _ hs,show T*q+T*(r-q)=T*r by ring] at hh
  rw [scalarTailJet_F]
  exact hh

theorem scalarTailJet_admissible {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) (q : ℝ) :
    (scalarTailJet hT α q).ScalarAdmissible := fun x =>
  scalarProfileJet_admissible (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2) _ _ (x 0)

theorem scalarTailJet_gradientTest {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) (q : ℝ) :
    (scalarTailJet hT α q).GradientTest := ⟨rfl,fun _ => rfl⟩

theorem scalarTailJet_flatten_error {T q r m : ℝ} (hT : 0 < T) (hq : 0 ≤ q)
    (hqr : q ≤ r) (hr : r ≤ 1) (α : boundedMassProfiles) (hm : 0 < m)
    (hm1 : m ≤ 1) (hmq : m ≤ α.val q) :
    |clockContinuation m (scalarTailJet hT α q).F (T*q) 0-
      clockContinuation m (scalarTailJet hT α r).F (T*r) 0-
      (T/2*(∫ s in q..r, α.val s-m))*(scalarTailJet hT α r).observedSquare m (T*r) 0| ≤
      2*T^2*(r-q)*(∫ s in q..r, α.val s-m) := by
  have hs : 0 ≤ T*(r-q) := mul_nonneg hT.le (sub_nonneg.mpr hqr)
  have he : T*q+T*(r-q)=T*r := by ring
  have hi : (∫ s in T*q..T*r, (rescaledMassProfile α hT).mass s-m) =
      T*(∫ s in q..r, α.val s-m) := by
    change (∫ s in T*q..T*r, (fun z => α.val z-m) (s/T)) = _
    rw [intervalIntegral.integral_comp_div (fun z => α.val z-m) hT.ne']
    simp only [mul_div_cancel_left₀ _ hT.ne',smul_eq_mul]
  have hh := HeatJet.flatten_profile_error (scalarTailJet_admissible hT α r)
    (scalarTailJet_gradientTest hT α r) (rescaledMassProfile α hT)
    (fun s => (α.property.1 (s/T)).2) (A:=T*q) (l:=T*q)
    (Real.toNNReal (T*(r-q))) hm hm1 (by simpa only [rescaledMassProfile,mul_div_cancel_left₀ _ hT.ne'] using hmq)
    (mul_nonneg hT.le hq) (scalarTailJet_restart hT hqr hr α) (0:Fin 1 → ℝ)
  simp only [Real.coe_toNNReal _ hs,he,hi] at hh
  rw [show T*(∫ s in q..r, α.val s-m)/2 = T/2*(∫ s in q..r, α.val s-m) by ring] at hh
  exact hh.trans_eq (by ring)

theorem scalarPenalty_flatten_bound {q r m : ℝ} (hq : 0 ≤ q) (hqr : q ≤ r) (hr : r ≤ 1)
    (α : boundedMassProfiles) (hm : 0 ≤ m) (hm1 : m ≤ 1) (hmr : m ≤ α.val r)
    (hf : ∀ s ∈ Ico (0:ℝ) q, α.val s = m) (hmq : m ≤ α.val q) :
    scalarPenalty α-scalarPenalty (replaceHeadProfile α hm hm1 hmr) ≤
      r*(∫ s in q..r, α.val s-m) := by
  let β := replaceHeadProfile α hm hm1 hmr
  let f := fun s => weightedProfile α s-weightedProfile β s
  have hfi : ∀ a b, IntervalIntegrable f volume a b := fun _ _ =>
    (weightedProfile_monotone α).intervalIntegrable.sub (weightedProfile_monotone β).intervalIntegrable
  have hz : (∫ s in (0:ℝ)..q, f s) = 0 := by
    trans ∫ _s in (0:ℝ)..q, (0:ℝ)
    · apply intervalIntegral.integral_congr_Ioo_of_le hq
      intro s hs
      dsimp only [f,weightedProfile]
      rw [hf s ⟨hs.1.le,hs.2⟩,
        replaceHeadProfile_head α hm hm1 hmr ⟨hs.1.le,hs.2.trans_le hqr⟩,sub_self]
    · simp
  have ht : (∫ s in r..1, f s) = 0 := by
    trans ∫ _s in r..1, (0:ℝ)
    · apply intervalIntegral.integral_congr_Ioo_of_le hr
      intro s hs
      dsimp only [f,weightedProfile]
      rw [replaceHeadProfile_tail α (hq.trans hqr) hm hm1 hmr hs.1.le,sub_self]
    · simp
  have he : scalarPenalty α-scalarPenalty β = ∫ s in q..r, f s := by
    unfold scalarPenalty
    rw [← intervalIntegral.integral_sub (weightedProfile_monotone α).intervalIntegrable
      (weightedProfile_monotone β).intervalIntegrable]
    change (∫ s in (0:ℝ)..1, f s) = _
    rw [← intervalIntegral.integral_add_adjacent_intervals (hfi 0 q) (hfi q 1),hz,zero_add,
      ← intervalIntegral.integral_add_adjacent_intervals (hfi q r) (hfi r 1),ht,add_zero]
  rw [show scalarPenalty α-scalarPenalty (replaceHeadProfile α hm hm1 hmr) = ∫ s in q..r, f s from he,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on_of_le_Ioo hqr (hfi q r)
    ((α.property.2.intervalIntegrable.sub intervalIntegrable_const).const_mul r)
  intro s hs
  dsimp only [f,weightedProfile]
  rw [replaceHeadProfile_head α hm hm1 hmr ⟨hq.trans hs.1.le,hs.2⟩,max_eq_left (hq.trans hs.1.le)]
  have hn : 0 ≤ α.val s-m := sub_nonneg.mpr (hmq.trans (α.property.2 hs.1.le))
  nlinarith [mul_nonneg (sub_nonneg.mpr hs.2.le) hn]

 

theorem scalarMinimizer_flatten_endpoint_bound {T q r m : ℝ} (hT : 0 < T)
    (hq : 0 < q) (hqr : q ≤ r) (hr : r ≤ 1) (α : boundedMassProfiles)
    (hα : α ∈ scalarProfiles) (hm : 0 < m) (hm1 : m ≤ 1)
    (hf : ∀ s ∈ Ico (0:ℝ) q, α.val s = m)
    (hW : 0 < ∫ s in q..r, α.val s-m)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    (scalarTailJet hT α r).observedSquare m (T*r) 0 ≤ r+4*T*(r-q) := by
  have hmq : m ≤ α.val q := by rw [← hf 0 ⟨le_rfl,hq⟩]; exact α.property.2 hq.le
  have hmr : m ≤ α.val r := hmq.trans (α.property.2 hqr)
  let β := replaceHeadProfile α hm.le hm1 hmr
  have hb := hmin β (replaceHeadProfile_mem hα hr hm.le hm1 hmr)
  have ht : (scalarTailJet hT β r).F = (scalarTailJet hT α r).F :=
    scalarTailJet_congr hT hr (fun s hs => replaceHeadProfile_tail α (hq.le.trans hqr) hm.le hm1 hmr hs.1.le)
  rw [scalarParisiValue_constant_head hT ⟨hq,hqr.trans hr⟩ α hm hf,
    scalarParisiValue_constant_head hT ⟨hq.trans_le hqr,hr⟩ β hm
      (fun s hs => replaceHeadProfile_head α hm.le hm1 hmr hs),ht] at hb
  have hp := scalarPenalty_flatten_bound hq.le hqr hr α hm.le hm1 hmr hf hmq
  have he := abs_le.mp (scalarTailJet_flatten_error hT hq.le hqr hr α hm hm1 hmq)
  have hpos : 0 < T/2*(∫ s in q..r, α.val s-m) := mul_pos (by positivity) hW
  have hh : (T/2*(∫ s in q..r, α.val s-m))*(scalarTailJet hT α r).observedSquare m (T*r) 0 ≤
      (T/2*(∫ s in q..r, α.val s-m))*(r+4*T*(r-q)) := by
    change scalarPenalty α-scalarPenalty β ≤ _ at hp
    nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ T/2)]
  exact (mul_le_mul_iff_right₀ hpos).mp hh

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem HeatJet.G_congr_F {J K : HeatJet 0} (he : J.F = K.F) : J.G 0 = K.G 0 := by
  funext x
  have hJ := J.derivF x (fun _ => 1) 0
  have hK := K.derivF x (fun _ => 1) 0
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,one_mul,zero_smul,add_zero,Nat.reduceAdd] at hJ hK
  rw [he] at hJ
  exact hJ.unique hK

theorem HeatJet.filledSquare_congr {n : ℕ} {J K : HeatJet n}
    (hF : J.F = K.F) (hA : J.A = K.A) {m : ℝ} (hm : 0 < m) (T s : ℝ)
    (x : Fin (n+1) → ℝ) : J.filledSquare hm T s x = K.filledSquare hm T s x := by
  change clockTest m (clockContinuation m J.F (T-s))
    (fun y => (clockTest m J.F J.A (T-s) y)^2) s x = _
  rw [hF,hA]
  rfl

theorem HeatJet.filledSquare_evolve {n : ℕ} (J : HeatJet n) {m d T s : ℝ}
    (hm : 0 < m) (hd : 0 ≤ d) (hs : s ≤ T) (x : Fin (n+1) → ℝ) :
    (J.evolve hm d).filledSquare hm T s x = J.filledSquare hm (T+d) s x := by
  change clockTest m (clockContinuation m (clockContinuation m J.F d) (T-s))
    (fun y => (clockTest m (clockContinuation m J.F d) (clockTest m J.F J.A d) (T-s) y)^2) s x = _
  have hF : clockContinuation m (clockContinuation m J.F d) (T-s) = clockContinuation m J.F (T+d-s) := by
    funext y
    rw [clockContinuation_add J.lipschitz hm.ne' (sub_nonneg.mpr hs) hd]
    congr 1
    ring
  have hA : clockTest m (clockContinuation m J.F d) (clockTest m J.F J.A d) (T-s) =
      clockTest m J.F J.A (T+d-s) := by
    funext y
    rw [clockTest_add J.lipschitz J.smoothA hm.ne' (sub_nonneg.mpr hs) hd]
    congr 1
    ring
  rw [hF,hA]
  rfl

theorem scalarTailJet_constant_evolve {T p q m : ℝ} (hT : 0 < T)
    (hp : 0 ≤ p) (hpq : p < q) (hq : q ≤ 1) (α : boundedMassProfiles) (hm : 0 < m)
    (hf : ∀ s ∈ Ico (0:ℝ) q, α.val s = m) :
    (scalarTailJet hT α p).F = ((scalarTailJet hT α q).evolve hm (T*(q-p))).F := by
  rw [scalarTailJet_restart hT hpq.le hq α]
  funext x
  have hd : 0 < T*(q-p) := mul_pos hT (sub_pos.mpr hpq)
  have hh := HeatJet.nonnegativeProfileValue_constant (scalarTailJet hT α q)
    (rescaledMassProfile α hT) hm (T*p) (Real.toNNReal (T*(q-p)))
    (by rwa [Real.coe_toNNReal _ hd.le]) (by
      intro s hs
      change α.val (s/T) = m
      apply hf
      rw [Real.coe_toNNReal _ hd.le] at hs
      constructor
      · exact div_nonneg ((mul_nonneg hT.le hp).trans hs.1) hT.le
      · apply (div_lt_iff₀ hT).mpr
        nlinarith [hs.2]) x
  change _ = clockContinuation m (scalarTailJet hT α q).F (T*(q-p)) x
  simpa only [Real.coe_toNNReal _ hd.le] using hh

theorem scalarTailJet_prefix_square {T p q m s : ℝ} (hT : 0 < T)
    (hp : 0 ≤ p) (hpq : p < q) (hq : q ≤ 1) (α : boundedMassProfiles) (hm : 0 < m)
    (hf : ∀ r ∈ Ico (0:ℝ) q, α.val r = m) (hs : s ≤ T*p) :
    (scalarTailJet hT α p).filledSquare hm (T*p) s 0 =
      (scalarTailJet hT α q).filledSquare hm (T*q) s 0 := by
  have hF := scalarTailJet_constant_evolve hT hp hpq hq α hm hf
  have hG := HeatJet.G_congr_F hF
  have hA : (scalarTailJet hT α p).A = ((scalarTailJet hT α q).evolve hm (T*(q-p))).A := by
    rw [(scalarTailJet_gradientTest hT α p).1,
      ((scalarTailJet_gradientTest hT α q).evolve hm (T*(q-p))).1]
    exact hG
  rw [HeatJet.filledSquare_congr hF hA hm,
    HeatJet.filledSquare_evolve _ hm (mul_nonneg hT.le (sub_nonneg.mpr hpq.le)) hs,
    show T*p+T*(q-p)=T*q by ring]

theorem scalarMinimizer_prefix_integral {T p q m : ℝ} (hT : 0 < T)
    (hp : 0 < p) (hpq : p ≤ q) (hq : q ≤ 1) (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hm : 0 < m) (hm1 : m < 1) (hf : ∀ r ∈ Ico (0:ℝ) q, α.val r = m)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    (1/2:ℝ)*(∫ s in 0..T*p, (scalarTailJet hT α q).filledSquare hm (T*q) s 0)-T*p^2/4 ≤ 0 := by
  have hh := scalarMinimizer_head_derivative_nonpos hT ⟨hp,hpq.trans hq⟩ α hα hm hm1
    (fun r hr => hf r ⟨hr.1,hr.2.trans_le hpq⟩) hmin
  rcases hpq.eq_or_lt with rfl | hpq
  · exact hh
  have he : (∫ s in 0..T*p, (scalarTailJet hT α p).filledSquare hm (T*p) s 0) =
      ∫ s in 0..T*p, (scalarTailJet hT α q).filledSquare hm (T*q) s 0 := by
    apply intervalIntegral.integral_congr_Ioo_of_le (mul_nonneg hT.le hp.le)
    intro s hs
    exact scalarTailJet_prefix_square hT hp.le hpq hq α hm hf hs.2.le
  rwa [he] at hh

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open Filter Set
open scoped Topology NNReal

 

 theorem HeatJet.nonnegativeProfileTest_terminal_tendsto {n : ℕ}
    (J : ℕ → HeatJet n) (L : HeatJet n)
    (hF : TendstoUniformly (fun k => (J k).F) L.F atTop)
    (hA : TendstoUniformly (fun k => (J k).A) L.A atTop)
    (α : ℕ → NonnegativeMassProfile) (hα : ∀ k s, (α k).mass s ≤ 1)
    (l : ℕ → ℝ) (t : ℕ → ℝ≥0) :
    TendstoUniformly (fun k x => (J k).nonnegativeProfileTest (α k) (l k) (t k) x-
      L.nonnegativeProfileTest (α k) (l k) (t k) x) (fun _ => 0) atTop := by
  obtain ⟨K,hK,hb⟩ := L.smoothA.bound
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  let δ := ε/(2+8*(K+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [Metric.tendstoUniformly_iff.mp hF δ hδ,
    Metric.tendstoUniformly_iff.mp hA δ hδ] with k hkF hkA x
  have hh := L.nonnegativeProfileTest_stability (J k) hδ.le
    (fun y => show |(J k).F y-L.F y| ≤ δ from by simpa only [Real.dist_eq,abs_sub_comm] using (hkF y).le)
    (show 0 < K+1 by linarith) (fun y => (hb y).trans (by linarith : K ≤ K+1))
    (fun y => show |(J k).A y-L.A y| ≤ δ from by simpa only [Real.dist_eq,abs_sub_comm] using (hkA y).le)
    (α k) (hα k) (l k) (t k) x
  have he : δ+4*δ*(K+1) = ε/2 := by dsimp [δ]; field_simp; ring
  simpa only [Real.dist_eq,zero_sub,abs_neg] using hh.trans_lt (by rw [he]; linarith)

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Scalar
open Set

def UniformSpatialTail (R : ℝ) (f : ℝ × ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ L : ℝ, ∀ t ∈ Icc 0 R, ∀ x, L ≤ |x| → |f (t,x)| ≤ ε

namespace UniformSpatialTail
variable {R : ℝ} {f g : ℝ × ℝ → ℝ}

theorem zero : UniformSpatialTail R (fun _ => 0) := by
  intro ε hε
  exact ⟨0,fun _ _ _ _ => by simpa using hε.le⟩

theorem add (hf : UniformSpatialTail R f) (hg : UniformSpatialTail R g) :
    UniformSpatialTail R (fun p => f p+g p) := by
  intro ε hε
  obtain ⟨L,hL⟩ := hf (ε/2) (half_pos hε)
  obtain ⟨K,hK⟩ := hg (ε/2) (half_pos hε)
  refine ⟨max L K,fun t ht x hx => ?_⟩
  have hf := hL t ht x ((le_max_left _ _).trans hx)
  have hg := hK t ht x ((le_max_right _ _).trans hx)
  linarith [abs_add_le (f (t,x)) (g (t,x))]

theorem neg (hf : UniformSpatialTail R f) : UniformSpatialTail R (fun p => -f p) := by
  intro ε hε
  obtain ⟨L,hL⟩ := hf ε hε
  exact ⟨L,fun t ht x hx => by simpa only [abs_neg] using hL t ht x hx⟩

theorem sub (hf : UniformSpatialTail R f) (hg : UniformSpatialTail R g) :
    UniformSpatialTail R (fun p => f p-g p) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem const_mul (hf : UniformSpatialTail R f) (c : ℝ) :
    UniformSpatialTail R (fun p => c*f p) := by
  intro ε hε
  obtain ⟨L,hL⟩ := hf (ε/(|c|+1)) (div_pos hε (by positivity))
  refine ⟨L,fun t ht x hx => ?_⟩
  rw [abs_mul]
  have hh := (le_div_iff₀ (show 0 < |c|+1 by positivity)).mp (hL t ht x hx)
  nlinarith [abs_nonneg (f (t,x))]

theorem div_const (hf : UniformSpatialTail R f) (c : ℝ) :
    UniformSpatialTail R (fun p => f p/c) := by
  simpa only [div_eq_mul_inv,mul_comm] using hf.const_mul c⁻¹

theorem mul (hf : UniformSpatialTail R f) (hg : UniformSpatialTail R g) :
    UniformSpatialTail R (fun p => f p*g p) := by
  intro ε hε
  obtain ⟨L,hL⟩ := hf ε hε
  obtain ⟨K,hK⟩ := hg 1 (by norm_num)
  refine ⟨max L K,fun t ht x hx => ?_⟩
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (hK t ht x ((le_max_right _ _).trans hx))
    (abs_nonneg _)).trans (by simpa using hL t ht x ((le_max_left _ _).trans hx))

theorem pow_succ (hf : UniformSpatialTail R f) (k : ℕ) :
    UniformSpatialTail R (fun p => (f p)^(k+1)) := by
  induction k with
  | zero => simpa using hf
  | succ k ih => simpa only [_root_.pow_succ] using ih.mul hf

theorem lower (hf : UniformSpatialTail R f) :
    ∀ ε > 0, ∃ L : ℝ, ∀ t ∈ Icc 0 R, ∀ x, L ≤ |x| → -ε ≤ f (t,x) := by
  intro ε hε
  obtain ⟨L,hL⟩ := hf ε hε
  exact ⟨L,fun t ht x hx => (abs_le.mp (hL t ht x hx)).1⟩

theorem lower_half (hf : UniformSpatialTail R f) :
    ∀ ε > 0, ∃ L : ℝ, ∀ t ∈ Icc 0 R, ∀ x, L ≤ x → -ε ≤ f (t,x) := by
  intro ε hε
  obtain ⟨L,hL⟩ := hf.lower ε hε
  exact ⟨max L 0,fun t ht x hx => hL t ht x ((le_max_left _ _).trans (hx.trans (le_abs_self x)))⟩
end UniformSpatialTail
end SKFluctuations.Scalar

 

 

namespace SKFluctuations.Scalar
open Set Filter
open scoped Topology

 theorem second_deriv_nonneg_at_min {f : ℝ → ℝ} {x : ℝ}
    (hmin : IsLocalMin f x) (hc : ContinuousAt f x) : 0 ≤ deriv (deriv f) x := by
  by_contra h
  have hmax := isLocalMax_of_deriv_deriv_neg (lt_of_not_ge h) hmin.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [hmin,hmax] with y hy hz
    exact le_antisymm hz hy
  have hz := he.deriv.deriv_eq
  simp only [deriv_const',deriv_const] at hz
  exact h (by rw [hz])

 theorem hasDerivAt_nonpos_at_right_min {f : ℝ → ℝ} {d t : ℝ}
    (ht : 0 < t) (hmin : IsMinOn f (Icc 0 t) t) (hd : HasDerivAt f d t) : d ≤ 0 := by
  apply le_of_tendsto hd.tendsto_slope_zero_left
  have hen : ∀ᶠ s : ℝ in 𝓝 0, -t < s := Ioi_mem_nhds (neg_neg_of_pos ht)
  have he := hen.filter_mono (show 𝓝[<] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  filter_upwards [he,self_mem_nhdsWithin] with s hs hs0
  have hs0 : s < 0 := hs0
  change s⁻¹ * (f (t+s)-f t) ≤ 0
  exact mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr hs0.le)
    (sub_nonneg.mpr (hmin ⟨by linarith,by linarith⟩))

 

theorem parabolic_nonneg {v d b c F : ℝ → ℝ → ℝ} {R a z M : ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => v p.1 p.2) (Icc 0 R ×ˢ Icc a z))
    (hpde : ∀ t ∈ Ioc 0 R, ∀ x ∈ Ioo a z,
      HasDerivAt (fun s => v s x)
        (d t x*deriv (deriv (v t)) x+b t x*deriv (v t) x+c t x*v t x+F t x) t)
    (hd : ∀ t ∈ Ioc 0 R, ∀ x ∈ Ioo a z, 0 ≤ d t x)
    (hM : ∀ t ∈ Ioc 0 R, ∀ x ∈ Ioo a z, c t x ≤ M)
    (hF : ∀ t ∈ Ioc 0 R, ∀ x ∈ Ioo a z, 0 ≤ F t x)
    (hinit : ∀ x ∈ Icc a z, 0 ≤ v 0 x)
    (hleft : ∀ t ∈ Icc 0 R, 0 ≤ v t a)
    (hright : ∀ t ∈ Icc 0 R, 0 ≤ v t z) :
    ∀ t ∈ Icc 0 R, ∀ x ∈ Icc a z, 0 ≤ v t x := by
  intro t ht x hx
  by_contra hv
  have hvn : v t x < 0 := lt_of_not_ge hv
  let E : ℝ → ℝ := fun s => Real.exp (-(M+1)*s)
  let w : ℝ → ℝ → ℝ := fun s y => E s*v s y
  have hE : ∀ s, 0 < E s := fun s => Real.exp_pos _
  have hEc : Continuous E := Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hwc : ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2) (Icc 0 t ×ˢ Icc a z) :=
    ((hEc.comp continuous_fst).continuousOn.mul hc).mono
      (prod_mono (Icc_subset_Icc_right ht.2) Subset.rfl)
  obtain ⟨p,hp,hm⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMinOn
    (show (Icc 0 t ×ˢ Icc a z).Nonempty from ⟨(t,x),⟨⟨ht.1,le_rfl⟩,hx⟩⟩) hwc
  have hm_tx : w p.1 p.2 ≤ w t x :=
    hm (show (t,x) ∈ (Icc 0 t ×ˢ Icc a z) from ⟨⟨ht.1,le_rfl⟩,hx⟩)
  have hwn : w p.1 p.2 < 0 := hm_tx.trans_lt (mul_neg_of_pos_of_neg (hE t) hvn)
  have hpt : p.1 ∈ Icc 0 R := ⟨hp.1.1,hp.1.2.trans ht.2⟩
  have hp0 : 0 < p.1 := by
    apply lt_of_le_of_ne hp.1.1
    intro he
    have hh := hinit p.2 hp.2
    have hw0 : 0 ≤ w p.1 p.2 := by
      dsimp only [w]
      rw [← he]
      exact mul_nonneg (hE 0).le hh
    exact hwn.not_ge hw0
  have hpx : p.2 ∈ Ioo a z := by
    constructor
    · apply lt_of_le_of_ne hp.2.1
      intro he
      have hh := hleft p.1 hpt
      have hw0 : 0 ≤ w p.1 p.2 := by
        dsimp only [w]
        rw [← he]
        exact mul_nonneg (hE p.1).le hh
      exact hwn.not_ge hw0
    · apply lt_of_le_of_ne hp.2.2
      intro he
      have hh := hright p.1 hpt
      have hw0 : 0 ≤ w p.1 p.2 := by
        dsimp only [w]
        rw [he]
        exact mul_nonneg (hE p.1).le hh
      exact hwn.not_ge hw0
  have hpo : p.1 ∈ Ioc 0 R := ⟨hp0,hpt.2⟩
  have hspmin : IsLocalMin (w p.1) p.2 :=
    (show IsMinOn (w p.1) (Icc a z) p.2 from
      fun y hy => hm (show (p.1,y) ∈ (Icc 0 t ×ˢ Icc a z) from ⟨hp.1,hy⟩)).isLocalMin (Icc_mem_nhds hpx.1 hpx.2)
  have hspc : ContinuousAt (w p.1) p.2 := by
    have hh : ContinuousOn (w p.1) (Icc a z) :=
      hwc.comp (continuous_const.prodMk continuous_id).continuousOn (fun y hy => ⟨hp.1,hy⟩)
    exact hh.continuousAt (Icc_mem_nhds hpx.1 hpx.2)
  have hg0 := hspmin.deriv_eq_zero
  have hh0 := second_deriv_nonneg_at_min hspmin hspc
  have htmmin : IsMinOn (fun s => w s p.2) (Icc 0 p.1) p.1 :=
    fun s hs => hm (show (s,p.2) ∈ (Icc 0 t ×ˢ Icc a z) from
      ⟨⟨hs.1,hs.2.trans hp.1.2⟩,hp.2⟩)
  have hEd : HasDerivAt E (-(M+1)*E p.1) p.1 := by
    simpa only [E, id_eq, mul_comm, one_mul, mul_one] using
      ((hasDerivAt_id p.1).const_mul (-(M+1))).exp
  have hwd := hEd.mul (hpde p.1 hpo p.2 hpx)
  have htm := hasDerivAt_nonpos_at_right_min hp0 htmmin hwd
  have hge : deriv (w p.1) p.2 = E p.1*deriv (v p.1) p.2 := deriv_const_mul_field _
  have hhe : deriv (deriv (w p.1)) p.2 = E p.1*deriv (deriv (v p.1)) p.2 := by
    dsimp only [w]
    rw [deriv_const_mul_field',deriv_const_mul_field]
  rw [hge] at hg0
  rw [hhe] at hh0
  have hsource := mul_nonneg (hE p.1).le (hF p.1 hpo p.2 hpx)
  have hdiff := mul_nonneg (hd p.1 hpo p.2 hpx) hh0
  have hzero : 0 < (c p.1 p.2-(M+1))*w p.1 p.2 :=
    mul_pos_of_neg_of_neg (by linarith [hM p.1 hpo p.2 hpx]) hwn
  dsimp only [w] at hzero
  have hb0 : b p.1 p.2*(E p.1*deriv (v p.1) p.2)=0 := mul_eq_zero.mpr (Or.inr hg0)
  nlinarith

end SKFluctuations.Scalar

 

 

namespace SKFluctuations.Scalar
open Set Filter
open scoped Topology

theorem parabolic_lower_bound {v d b c F : ℝ → ℝ → ℝ} {R a z K ε : ℝ}
    (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hc : ContinuousOn (fun p : ℝ × ℝ => v p.1 p.2) (Icc 0 R ×ˢ Icc a z))
    (hpde : ∀ t ∈ Ioc 0 R, ∀ x ∈ Ioo a z,
      HasDerivAt (fun s => v s x)
        (d t x*deriv (deriv (v t)) x+b t x*deriv (v t) x+c t x*v t x+F t x) t)
    (hd : ∀ t ∈ Ioc 0 R, ∀ x ∈ Ioo a z, 0 ≤ d t x)
    (hM : ∀ t ∈ Ioc 0 R, ∀ x ∈ Ioo a z, c t x ≤ K)
    (hF : ∀ t ∈ Ioc 0 R, ∀ x ∈ Ioo a z, 0 ≤ F t x)
    (hinit : ∀ x ∈ Icc a z, 0 ≤ v 0 x)
    (hleft : ∀ t ∈ Icc 0 R, -ε ≤ v t a)
    (hright : ∀ t ∈ Icc 0 R, -ε ≤ v t z) :
    ∀ t ∈ Icc 0 R, ∀ x ∈ Icc a z, -ε*Real.exp (K*t) ≤ v t x := by
  let E : ℝ → ℝ := fun s => ε*Real.exp (K*s)
  have hEpos : ∀ s, 0 ≤ E s := fun _ => mul_nonneg hε (Real.exp_nonneg _)
  have hEle : ∀ s, 0 ≤ s → ε ≤ E s := by
    intro s hs
    exact le_mul_of_one_le_right hε (Real.one_le_exp_iff.mpr (mul_nonneg hK hs))
  have hEd (s : ℝ) : HasDerivAt E (K*E s) s := by
    have hh := (((hasDerivAt_id s).const_mul K).exp).const_mul ε
    convert hh using 1 <;> first | rfl | (dsimp only [E,id]; ring)
  have hwc : ContinuousOn (fun p : ℝ × ℝ => v p.1 p.2+E p.1) (Icc 0 R ×ˢ Icc a z) :=
    hc.add (((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).comp
      continuous_fst).continuousOn)
  have hh := parabolic_nonneg (v := fun s y => v s y+E s) (d := d) (b := b) (c := c)
    (F := fun s y => F s y+(K-c s y)*E s) (M := K) hwc (by
      intro s hs y hy
      have hh := (hpde s hs y hy).add (hEd s)
      simp only [deriv_add_const',deriv_add_const]
      convert hh using 1
      first | rfl | ring) hd hM (by
      intro s hs y hy
      exact add_nonneg (hF s hs y hy) (mul_nonneg (sub_nonneg.mpr (hM s hs y hy)) (hEpos s)))
    (by intro y hy; exact add_nonneg (hinit y hy) (hEpos 0))
    (by intro s hs; linarith [hleft s hs,hEle s hs.1])
    (by intro s hs; linarith [hright s hs,hEle s hs.1])
  intro t ht x hx
  have hh := hh t ht x hx
  dsimp only [E] at hh
  linarith

 

theorem parabolic_nonneg_real {v d b c F : ℝ → ℝ → ℝ} {R M : ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => v p.1 p.2) (Icc 0 R ×ˢ univ))
    (hpde : ∀ t ∈ Ioc 0 R, ∀ x,
      HasDerivAt (fun s => v s x)
        (d t x*deriv (deriv (v t)) x+b t x*deriv (v t) x+c t x*v t x+F t x) t)
    (hd : ∀ t ∈ Ioc 0 R, ∀ x, 0 ≤ d t x)
    (hM : ∀ t ∈ Ioc 0 R, ∀ x, c t x ≤ M)
    (hF : ∀ t ∈ Ioc 0 R, ∀ x, 0 ≤ F t x)
    (hinit : ∀ x, 0 ≤ v 0 x)
    (htail : ∀ ε > 0, ∃ L : ℝ, ∀ t ∈ Icc 0 R, ∀ x, L ≤ |x| → -ε ≤ v t x) :
    ∀ t ∈ Icc 0 R, ∀ x, 0 ≤ v t x := by
  intro t ht x
  by_contra hv
  have hv : v t x < 0 := lt_of_not_ge hv
  let K := max M 0
  let ε := -v t x/(2*Real.exp (K*t))
  have hε : 0 < ε := div_pos (neg_pos.mpr hv) (mul_pos (by norm_num) (Real.exp_pos _))
  obtain ⟨L,hL⟩ := htail ε hε
  let A := max (max L (|x|+1)) 1
  have hLA : L ≤ A := (le_max_left _ _).trans (le_max_left _ _)
  have hA : 0 ≤ A := (by norm_num : (0:ℝ) ≤ 1).trans (le_max_right _ _)
  have hxA : |x| ≤ A := (by linarith : |x| ≤ |x|+1).trans
    ((le_max_right _ _).trans (le_max_left _ _))
  have hh := parabolic_lower_bound (v := v) (d := d) (b := b) (c := c) (F := F)
    (R := R) (a := -A) (z := A) (K := K) (ε := ε) (le_max_right _ _) hε.le
    (hc.mono (prod_mono Subset.rfl (subset_univ _)))
    (fun s hs y _ => hpde s hs y) (fun s hs y _ => hd s hs y)
    (fun s hs y _ => (hM s hs y).trans (le_max_left _ _)) (fun s hs y _ => hF s hs y)
    (fun y _ => hinit y) (fun s hs => hL s hs (-A) (by simpa only [abs_neg,abs_of_nonneg hA] using hLA))
    (fun s hs => hL s hs A (by simpa only [abs_of_nonneg hA] using hLA)) t ht x (abs_le.mp hxA)
  have he : ε*Real.exp (K*t) = -v t x/2 := by
    dsimp only [ε]
    field_simp
  nlinarith

theorem parabolic_nonneg_halfline {v d b c F : ℝ → ℝ → ℝ} {R M : ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => v p.1 p.2) (Icc 0 R ×ˢ Ici 0))
    (hpde : ∀ t ∈ Ioc 0 R, ∀ x, 0 < x →
      HasDerivAt (fun s => v s x)
        (d t x*deriv (deriv (v t)) x+b t x*deriv (v t) x+c t x*v t x+F t x) t)
    (hd : ∀ t ∈ Ioc 0 R, ∀ x, 0 < x → 0 ≤ d t x)
    (hM : ∀ t ∈ Ioc 0 R, ∀ x, 0 < x → c t x ≤ M)
    (hF : ∀ t ∈ Ioc 0 R, ∀ x, 0 < x → 0 ≤ F t x)
    (hinit : ∀ x, 0 ≤ x → 0 ≤ v 0 x)
    (hleft : ∀ t ∈ Icc 0 R, 0 ≤ v t 0)
    (htail : ∀ ε > 0, ∃ L : ℝ, ∀ t ∈ Icc 0 R, ∀ x, L ≤ x → -ε ≤ v t x) :
    ∀ t ∈ Icc 0 R, ∀ x, 0 ≤ x → 0 ≤ v t x := by
  intro t ht x hx
  by_contra hv
  have hv : v t x < 0 := lt_of_not_ge hv
  let K := max M 0
  let ε := -v t x/(2*Real.exp (K*t))
  have hε : 0 < ε := div_pos (neg_pos.mpr hv) (mul_pos (by norm_num) (Real.exp_pos _))
  obtain ⟨L,hL⟩ := htail ε hε
  let A := max L (x+1)
  have hLA : L ≤ A := le_max_left _ _
  have hxA : x ≤ A := (by linarith : x ≤ x+1).trans (le_max_right _ _)
  have hh := parabolic_lower_bound (v := v) (d := d) (b := b) (c := c) (F := F)
    (R := R) (a := 0) (z := A) (K := K) (ε := ε) (le_max_right _ _) hε.le
    (hc.mono (prod_mono Subset.rfl Icc_subset_Ici_self))
    (fun s hs y hy => hpde s hs y hy.1) (fun s hs y hy => hd s hs y hy.1)
    (fun s hs y hy => (hM s hs y hy.1).trans (le_max_left _ _)) (fun s hs y hy => hF s hs y hy.1)
    (fun y hy => hinit y hy.1) (fun s hs => (neg_nonpos.mpr hε.le).trans (hleft s hs))
    (fun s hs => hL s hs A hLA) t ht x ⟨hx,hxA⟩
  have he : ε*Real.exp (K*t) = -v t x/2 := by
    dsimp only [ε]
    field_simp
  nlinarith

end SKFluctuations.Scalar

end

end OAI
