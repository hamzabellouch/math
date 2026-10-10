import Mathlib
import OAI.Probability.SKFluctuations.NonnegativeProfileValueStep

namespace OAI

/-! Scalar Parisi Value Dirac Dyadic. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 

 theorem scalarParisiValue_dirac_dyadic {T : ℝ} (hT : 0 < T) (j : ℕ) :
    scalarParisiValue hT (diracMassProfile ((1:ℝ)/2^j)) = Scalar.rsVariation T ((1:ℝ)/2^j) := by
  have hq : (1:ℝ)/2^j ∈ Icc (0:ℝ) 1 :=
    ⟨by positivity,div_le_self (by norm_num) (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))⟩
  have hu : 0 ≤ T/2^j := by positivity
  have hv : 0 ≤ T-T/2^j := sub_nonneg.mpr (div_le_self hT.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)))
  have hs : ∀ s ∈ Ico (0:ℝ) (0+(⟨T,hT.le⟩:ℝ≥0)),
      (rescaledMassProfile (diracMassProfile ((1:ℝ)/2^j)) hT).mass s =
        if s < 0+((⟨T,hT.le⟩:ℝ≥0):ℝ)/2^j then 0 else 1 := by
    intro s _
    change (if s/T < 1/2^j then (0:ℝ) else 1) = if s < 0+T/2^j then 0 else 1
    have he : s/T < 1/2^j ↔ s < T/2^j := by
      rw [div_lt_iff₀ hT]
      ring_nf
    simp only [he,zero_add]
  have hh := scalarTerminal.nonnegativeProfileValue_step
    (rescaledMassProfile (diracMassProfile ((1:ℝ)/2^j)) hT) (by norm_num : (0:ℝ) < 1)
      0 ⟨T,hT.le⟩ hT j hs 0
  change scalarTerminal.nonnegativeProfileValue (rescaledMassProfile (diracMassProfile ((1:ℝ)/2^j)) hT) 0 ⟨T,hT.le⟩ 0 =
    zeroContinuation (Measure.pi fun _ : Fin 1 => gaussianReal 0 (Real.toNNReal (T/2^j)))
      (clockContinuation 1 scalarTerminal.F (T-T/2^j)) 0 at hh
  have he := scalarRoot_mass_one (Real.toNNReal (T/2^j)) (Real.toNNReal (T-T/2^j))
  rw [Real.coe_toNNReal _ hu,Real.coe_toNNReal _ hv] at he
  unfold scalarParisiValue
  rw [hh,he,scalarPenalty_dirac hq]
  unfold Scalar.rsVariation
  have hmul : T*(1/2^j) = T/2^j := by ring
  rw [hmul]
  ring

 

 theorem scalarParisiMinimum_neg {T : ℝ} (hT : 1 < T) {α : boundedMassProfiles}
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (by linarith : 0 < T) α ≤
      scalarParisiValue (by linarith : 0 < T) β) :
    scalarParisiValue (by linarith : 0 < T) α < 0 := by
  obtain ⟨δ,hδ,hd⟩ := Scalar.rsVariation_strictly_negative hT
  have hp : Tendsto (fun j : ℕ => (1/2:ℝ)^j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨j,hj⟩ := (hp.eventually (gt_mem_nhds hδ)).exists
  have hq : (1:ℝ)/2^j ∈ Icc (0:ℝ) 1 :=
    ⟨by positivity,div_le_self (by norm_num) (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))⟩
  have hn := hd ((1:ℝ)/2^j) ⟨by positivity,by simpa only [div_pow,one_pow] using hj⟩
  apply (hmin (diracMassProfile ((1:ℝ)/2^j)) (diracMassProfile_mem hq)).trans_lt
  rw [scalarParisiValue_dirac_dyadic]
  exact hn

end SKFluctuations.Hierarchy

namespace SKFluctuations.Scalar
open Set

 

theorem clamped_nonpos_of_concave_second {f g h : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x)
    (hdd : ∀ x ∈ Ioo a b, HasDerivAt g (h x) x)
    (ha : f a = 0) (hb : f b = 0) (hga : g a = 0) (hgb : g b = 0)
    (hc : ConcaveOn ℝ (Icc a b) h) {c : ℝ} (hcm : c ∈ Icc a b) : f c ≤ 0 := by
  by_contra hp
  have hcp : 0 < f c := lt_of_not_ge hp
  have hac : a < c := lt_of_le_of_ne hcm.1 (by intro he; rw [← he,ha] at hcp; simp at hcp)
  have hcb : c < b := lt_of_le_of_ne hcm.2 (by intro he; rw [he,hb] at hcp; simp at hcp)
  obtain ⟨u,hu,heu⟩ := exists_hasDerivAt_eq_slope f g hac
    (hf.mono (Icc_subset_Icc le_rfl hcm.2))
    (fun x hx => hd x ⟨hx.1,hx.2.trans hcb⟩)
  obtain ⟨v,hv,hev⟩ := exists_hasDerivAt_eq_slope f g hcb
    (hf.mono (Icc_subset_Icc hcm.1 le_rfl))
    (fun x hx => hd x ⟨hac.trans hx.1,hx.2⟩)
  have hgu : 0 < g u := by rw [heu,ha,sub_zero]; exact div_pos hcp (sub_pos.mpr hac)
  have hgv : g v < 0 := by rw [hev,hb,zero_sub]; exact div_neg_of_neg_of_pos (neg_neg_iff_pos.mpr hcp) (sub_pos.mpr hcb)
  have huv : u < v := hu.2.trans hv.1
  obtain ⟨p,hp,hep⟩ := exists_hasDerivAt_eq_slope g h hu.1
    (hg.mono (Icc_subset_Icc le_rfl (hu.2.trans hcb).le))
    (fun x hx => hdd x ⟨hx.1,hx.2.trans (hu.2.trans hcb)⟩)
  obtain ⟨q,hq,heq⟩ := exists_hasDerivAt_eq_slope g h huv
    (hg.mono (Icc_subset_Icc hu.1.le hv.2.le))
    (fun x hx => hdd x ⟨hu.1.trans hx.1,hx.2.trans hv.2⟩)
  obtain ⟨r,hr,her⟩ := exists_hasDerivAt_eq_slope g h hv.2
    (hg.mono (Icc_subset_Icc (hac.trans hv.1).le le_rfl))
    (fun x hx => hdd x ⟨(hac.trans hv.1).trans hx.1,hx.2⟩)
  have hhp : 0 < h p := by rw [hep,hga,sub_zero]; exact div_pos hgu (sub_pos.mpr hu.1)
  have hhq : h q < 0 := by rw [heq]; exact div_neg_of_neg_of_pos (sub_neg.mpr (hgv.trans hgu)) (sub_pos.mpr huv)
  have hhr : 0 < h r := by rw [her,hgb,zero_sub]; exact div_pos (neg_pos.mpr hgv) (sub_pos.mpr hv.2)
  have hpr : p < r := hp.2.trans (huv.trans hr.1)
  have hqr : q ∈ segment ℝ p r := by
    rw [segment_eq_Icc hpr.le]
    exact ⟨(hp.2.trans hq.1).le,(hq.2.trans hr.1).le⟩
  have hh := hc.ge_on_segment ⟨hp.1.le,(hp.2.trans (hu.2.trans hcb)).le⟩
    ⟨((hac.trans hv.1).trans hr.1).le,hr.2.le⟩ hqr
  exact (not_lt_of_ge (lt_of_lt_of_le (lt_min hhp hhr) hh).le) hhq

end SKFluctuations.Scalar

namespace SKFluctuations.Scalar
open Set Filter
open scoped Topology

 

theorem no_clamped_nonnegative_gap {f g h : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x)
    (hdd : ∀ x ∈ Ioo a b, HasDerivAt g (h x) x)
    (ha : f a = 0) (hb : f b = 0) (hga : g a = 0) (hgb : g b = 0)
    (hc : StrictConcaveOn ℝ (Icc a b) h) (hn : ∀ x ∈ Icc a b, 0 ≤ f x) : False := by
  have hz : ∀ x ∈ Icc a b, f x = 0 := fun x hx =>
    le_antisymm (clamped_nonpos_of_concave_second hf hg hd hdd ha hb hga hgb hc.concaveOn hx) (hn x hx)
  have hgz : ∀ x ∈ Ioo a b, g x = 0 := by
    intro x hx
    apply (hd x hx).unique
    apply (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact hz y (Ioo_subset_Icc_self hy)
  have hhz : ∀ x ∈ Ioo a b, h x = 0 := by
    intro x hx
    apply (hdd x hx).unique
    apply (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact hgz y hy
  let p := (3*a+b)/4
  let q := (a+b)/2
  let r := (a+3*b)/4
  have hp : p ∈ Ioo a b := by dsimp [p]; constructor <;> linarith
  have hq : q ∈ Ioo a b := by dsimp [q]; constructor <;> linarith
  have hr : r ∈ Ioo a b := by dsimp [r]; constructor <;> linarith
  have hpr : p < r := by dsimp [p,r]; linarith
  have hqr : q ∈ openSegment ℝ p r := by
    rw [openSegment_eq_Ioo hpr]
    dsimp [p,q,r]
    constructor <;> linarith
  have hh := hc.lt_on_openSegment (Ioo_subset_Icc_self hp) (Ioo_subset_Icc_self hr) hpr.ne hqr
  rw [hhz p hp,hhz q hq,hhz r hr,min_self] at hh
  exact lt_irrefl _ hh

 

theorem no_clamped_gap_of_fourth_negative {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn (deriv f) (Icc a b))
    (hh : ContinuousOn ((deriv^[2]) f) (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (deriv f x) x)
    (hdd : ∀ x ∈ Ioo a b, HasDerivAt (deriv f) ((deriv^[2]) f x) x)
    (ha : f a = 0) (hb : f b = 0) (hga : deriv f a = 0) (hgb : deriv f b = 0)
    (h4 : ∀ x ∈ Ioo a b, (deriv^[4]) f x < 0) (hn : ∀ x ∈ Icc a b, 0 ≤ f x) : False := by
  apply no_clamped_nonnegative_gap hab hf hg hd hdd ha hb hga hgb ?_ hn
  apply strictConcaveOn_of_deriv2_neg (convex_Icc a b) hh
  intro x hx
  rw [interior_Icc] at hx
  simpa only [← Function.iterate_add_apply] using h4 x hx

end SKFluctuations.Scalar

namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 theorem expect_mono {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) {P Q : T.Assignment → ℝ}
    (hPQ : ∀ σ, P σ ≤ Q σ) (x : ι → ℝ) : T.expect w φ P x ≤ T.expect w φ Q x :=
  Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hPQ σ) (T.weight_nonneg hw φ ha σ x)

 theorem expect_nonneg {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) {P : T.Assignment → ℝ}
    (hP : ∀ σ, 0 ≤ P σ) (x : ι → ℝ) : 0 ≤ T.expect w φ P x :=
  Finset.sum_nonneg fun σ _ => mul_nonneg (T.weight_nonneg hw φ ha σ x) (hP σ)

 theorem abs_expect_le_expect_abs {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (P : T.Assignment → ℝ) (x : ι → ℝ) :
    |T.expect w φ P x| ≤ T.expect w φ (fun σ => |P σ|) x := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro σ _
  rw [abs_mul,abs_of_nonneg (T.weight_nonneg hw φ ha σ x)]

 

def Placement.Preserves (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps} (p : Placement T) : Prop :=
  ∀ (P : T.Assignment → ℝ) (x : ι → ℝ),
    p.tree.expect w φ (fun σ => P (p.restrict σ)) x = T.expect w φ P x

 theorem Placement.fresh_preserves {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (c : ℝ) : (Placement.fresh T c).Preserves w φ := by
  intro P x
  change (T.fork (single steps)).expect w φ (fun σ => P σ.1) x = _
  rw [expect_fork]
  simp_rw [(single steps).expect_const hw φ ha]

 theorem Placement.step_preserves {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps}
    (st : GaussianStep ι) (ha : OrderedSteps st.1 steps) {p : Placement T}
    (hp : p.Preserves w φ) : (p.step st).Preserves w φ := by
  intro P x
  rcases st with ⟨a,q⟩
  change (p.tree.step (a,q)).expect w φ (fun σ => P (p.restrict σ)) x = _
  rw [expect_step hw φ _ a q ha,expect_step hw φ _ a q ha]
  congr 1
  funext y
  exact hp P y

omit [Nonempty S] in
 theorem Placement.left_preserves (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps} (U : ReplicaTree ι S steps)
    {p : Placement T} (hp : p.Preserves w φ) : (p.left U).Preserves w φ := by
  intro P x
  change (p.tree.fork U).expect w φ (fun σ => P (p.restrict σ.1,σ.2)) x = _
  rw [expect_fork,expect_fork]
  exact hp (fun σ => U.expect w φ (fun τ => P (σ,τ)) x) x

omit [Nonempty S] in
 theorem Placement.right_preserves (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {U : ReplicaTree ι S steps}
    {p : Placement U} (hp : p.Preserves w φ) : (p.right T).Preserves w φ := by
  intro P x
  change (T.fork p.tree).expect w φ (fun σ => P (σ.1,p.restrict σ.2)) x = _
  rw [expect_fork,expect_fork]
  congr 1
  funext σ
  exact hp (fun τ => P (σ,τ)) x

 theorem attach_preserves {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (p : Placement T) (hp : p ∈ T.attach a) : p.Preserves w φ := by
  induction T generalizing a with
  | leaf =>
    simp only [attach,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl
    · intro P x
      rfl
    · exact Placement.fresh_preserves hw φ _ ha _
  | step st T ih =>
    simp only [attach,List.mem_cons,List.mem_map] at hp
    rcases hp with rfl|⟨p,hp,rfl⟩
    · exact Placement.fresh_preserves hw φ _ ha _
    · exact Placement.step_preserves hw φ st ha.2.2.2 (ih ha.2.2.2 p hp)
  | fork T U ihT ihU =>
    simp only [attach,List.mem_cons,List.mem_append,List.mem_map] at hp
    rcases hp with rfl|(⟨p,hp,rfl⟩|⟨p,hp,rfl⟩)
    · exact Placement.fresh_preserves hw φ _ ha _
    · exact Placement.left_preserves w φ U (ihT ha p hp)
    · exact Placement.right_preserves w φ T (ihU ha p hp)

 theorem normalizedAttach_preserves {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (p : Placement T) (hp : p ∈ T.normalizedAttach a) :
    p.Preserves w φ := by
  rcases List.mem_cons.mp hp with rfl|hp
  · exact Placement.fresh_preserves hw φ _ ha _
  · exact attach_preserves hw φ T ha p hp

end SKFluctuations.Hierarchy.ReplicaTree

namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 theorem Placement.expect_abs_mul_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps}
    {a : ℝ} (ha : OrderedSteps a steps) {p : Placement T} (hp : p.Preserves w φ)
    (P : T.Assignment → ℝ) {D : ℝ} (v : ι → ℝ) (hB : ∀ σ, |φ σ v| ≤ D) (x : ι → ℝ) :
    p.tree.expect w φ (fun σ => |P (p.restrict σ)*φ (p.spin σ) v|) x ≤
      D*T.expect w φ (fun σ => |P σ|) x := by
  calc
    _ ≤ p.tree.expect w φ (fun σ => D*|P (p.restrict σ)|) x := by
      apply p.tree.expect_mono hw φ ha
      intro σ
      rw [abs_mul,mul_comm D]
      exact mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _)
    _ = _ := by rw [expect_const_mul,hp (fun σ => |P σ|) x]

 

 theorem sourceJet_relative_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (vs : List (ι → ℝ)) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    {r : ℕ} (hT : T.leaves ≤ r) (P : T.Assignment → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hB : ∀ v ∈ vs, ∀ σ, |φ σ v| ≤ D) (x : ι → ℝ) :
    |sourceJet w φ a vs T P x| ≤
      (attachmentCount r vs.length:ℝ)*T.expect w φ (fun σ => |P σ|) x*D^vs.length := by
  induction vs generalizing T r with
  | nil => simpa only [sourceJet,List.length_nil,attachmentCount,pow_zero,Nat.cast_one,mul_one,one_mul]
      using T.abs_expect_le_expect_abs hw φ ha P x
  | cons v vs ih =>
    let E := T.expect w φ (fun σ => |P σ|) x
    let L := (attachmentCount (r+1) vs.length:ℝ)*(D*E)*D^vs.length
    have hE : 0 ≤ E := T.expect_nonneg hw φ ha (fun σ => abs_nonneg (P σ)) x
    have hL : 0 ≤ L := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hD hE)) (pow_nonneg hD _)
    have hp (p : Placement T) (hp : p ∈ T.normalizedAttach a) :
        |sourceJet w φ a vs p.tree (fun σ => P (p.restrict σ)*φ (p.spin σ) v) x| ≤ L := by
      apply (ih p.tree ((normalizedAttach_leaves T a p hp).trans (Nat.add_le_add_right hT 1))
        (fun σ => P (p.restrict σ)*φ (p.spin σ) v) (fun u hu => hB u (List.mem_cons_of_mem v hu))).trans
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hD _)
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Placement.expect_abs_mul_le hw φ ha (normalizedAttach_preserves hw φ T ha p hp)
        P v (hB v (List.mem_cons_self ..)) x
    have hs := list_weight_abs_le (T.normalizedAttach a)
      (fun p => sourceJet w φ a vs p.tree (fun σ => P (p.restrict σ)*φ (p.spin σ) v) x) hp
    rw [normalizedAttach_variation T ha] at hs
    calc
      |sourceJet w φ a (v::vs) T P x| ≤ 2*(T.leaves:ℝ)*L := hs
      _ ≤ 2*(r:ℝ)*L := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hT) (by norm_num)) hL
      _ = _ := by simp only [L,E,List.length_cons,attachmentCount,Nat.cast_mul,Nat.cast_ofNat,pow_succ]; ring

 theorem powerJet_relative_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (vs : List (ι → ℝ)) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    {r : ℕ} (hT : T.leaves ≤ r) (P : T.Assignment → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hB : ∀ v ∈ vs, ∀ σ, |φ σ v| ≤ D) (x : ι → ℝ) :
    |powerJet w φ a vs T P x| ≤
      (attachmentCount r vs.length:ℝ)*T.expect w φ (fun σ => |P σ|) x*D^vs.length := by
  induction vs generalizing T r with
  | nil => simpa only [powerJet,List.length_nil,attachmentCount,pow_zero,Nat.cast_one,mul_one,one_mul]
      using T.abs_expect_le_expect_abs hw φ ha P x
  | cons v vs ih =>
    let E := T.expect w φ (fun σ => |P σ|) x
    let L := (attachmentCount (r+1) vs.length:ℝ)*(D*E)*D^vs.length
    have hE : 0 ≤ E := T.expect_nonneg hw φ ha (fun σ => abs_nonneg (P σ)) x
    have hL : 0 ≤ L := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hD hE)) (pow_nonneg hD _)
    have hp (p : Placement T) (hp : p ∈ T.attach a) :
        |powerJet w φ a vs p.tree (fun σ => P (p.restrict σ)*φ (p.spin σ) v) x| ≤ L := by
      apply (ih p.tree ((attach_leaves T a p hp).trans (Nat.add_le_add_right hT 1))
        (fun σ => P (p.restrict σ)*φ (p.spin σ) v) (fun u hu => hB u (List.mem_cons_of_mem v hu))).trans
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hD _)
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Placement.expect_abs_mul_le hw φ ha (attach_preserves hw φ T ha p hp)
        P v (hB v (List.mem_cons_self ..)) x
    have hs := list_weight_abs_le (T.attach a)
      (fun p => powerJet w φ a vs p.tree (fun σ => P (p.restrict σ)*φ (p.spin σ) v) x) hp
    rw [attach_variation T ha] at hs
    calc
      |powerJet w φ a (v::vs) T P x| ≤ (2*(T.leaves:ℝ)-a)*L := hs
      _ ≤ 2*(r:ℝ)*L := mul_le_mul_of_nonneg_right (by
        have ht : (T.leaves:ℝ) ≤ r := Nat.cast_le.mpr hT
        have ha0 := ha.bounds.1
        linarith) hL
      _ = _ := by simp only [L,E,List.length_cons,attachmentCount,Nat.cast_mul,Nat.cast_ofNat,pow_succ]; ring

end SKFluctuations.Hierarchy.ReplicaTree

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem shiftedMean_abs_le_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [IsProbabilityMeasure ν]
    {m c : ℝ} {F A B : E → ℝ} (hA : BddSmooth 0 A) (hB : BddSmooth 0 B)
    (hb : ∀ y, |A y| ≤ c*B y) {x : E}
    (hi : Integrable (fun z => Real.exp (m*F (x+z))) ν) :
    |shiftedMean ν m F A x| ≤ c*shiftedMean ν m F B x := by
  apply abs_le.mpr
  constructor
  · have hh := shiftedMean_mono (hB.const_mul (-c)) hA
      (fun y => by have := (abs_le.mp (hb y)).1; nlinarith) hi
    rw [shiftedMean_const_mul] at hh
    nlinarith
  · have hh := shiftedMean_mono hA (hB.const_mul c)
      (fun y => (abs_le.mp (hb y)).2) hi
    rwa [shiftedMean_const_mul] at hh

 theorem relative_derivative_exp_bound_on {f g : ℝ → ℝ} {c : ℝ} {D : Set ℝ}
    (hD : Convex ℝ D) (hf : ContinuousOn f D)
    (hd : ∀ t ∈ interior D, HasDerivWithinAt f (g t) (interior D) t)
    (hb : ∀ t ∈ interior D, |g t| ≤ c*f t) {s t : ℝ} (hs : s ∈ D) (ht : t ∈ D) :
    Real.exp (-c*|t-s|)*f s ≤ f t ∧ f t ≤ Real.exp (c*|t-s|)*f s := by
  have hp : MonotoneOn (fun t => Real.exp (c*t)*f t) D := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg hD
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hf)
      (fun t ht => (((hasDerivAt_id t).const_mul c).exp.hasDerivWithinAt.mul (hd t ht)))
    intro t ht
    simp only [id_eq,mul_one]
    have h := (abs_le.mp (hb t ht)).1
    have he := Real.exp_pos (c*t)
    nlinarith [mul_le_mul_of_nonneg_left h he.le]
  have hm : AntitoneOn (fun t => Real.exp (-c*t)*f t) D := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos hD
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hf)
      (fun t ht => (((hasDerivAt_id t).const_mul (-c)).exp.hasDerivWithinAt.mul (hd t ht)))
    intro t ht
    simp only [id_eq,mul_one]
    have h := (abs_le.mp (hb t ht)).2
    have he := Real.exp_pos (-c*t)
    nlinarith [mul_le_mul_of_nonneg_left h he.le]
  have he (k u v : ℝ) : Real.exp (k*u)*(Real.exp (-k*v)*f v) = Real.exp (k*(u-v))*f v := by
    rw [← mul_assoc,← Real.exp_add]
    congr 2
    ring
  have hc (k u : ℝ) : Real.exp (k*u)*(Real.exp (-k*u)*f u) = f u := by
    rw [he]
    simp
  by_cases h : s ≤ t
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    constructor
    · have hh := mul_le_mul_of_nonneg_left (hp hs ht h) (Real.exp_pos (-c*t)).le
      have haa : (fun u => Real.exp (c*u)*f u) = (fun u => Real.exp (-(-c)*u)*f u) := by simp
      rw [haa] at hh
      simpa only [he,sub_self,mul_zero,Real.exp_zero,one_mul] using hh
    · have hh := mul_le_mul_of_nonneg_left (hm hs ht h) (Real.exp_pos (c*t)).le
      simpa only [he,sub_self,mul_zero,Real.exp_zero,one_mul] using hh
  · have h' := le_of_not_ge h
    rw [abs_of_nonpos (sub_nonpos.mpr h')]
    constructor
    · have hh := mul_le_mul_of_nonneg_left (hm ht hs h') (Real.exp_pos (c*t)).le
      rw [hc,he] at hh
      simpa only [neg_mul,mul_neg,neg_neg] using hh
    · have hh := mul_le_mul_of_nonneg_left (hp ht hs h') (Real.exp_pos (-c*t)).le
      have haa : (fun u => Real.exp (c*u)*f u) = (fun u => Real.exp (-(-c)*u)*f u) := by simp
      rw [haa] at hh
      simp only [he,sub_self,mul_zero,Real.exp_zero,one_mul] at hh
      simpa only [neg_mul,mul_neg,neg_neg] using hh

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι β : Type*} {κ : β → Type*} [Fintype ι]

 theorem prefixContinuation_abs_sub_le {F G : (ι → ℝ) → ℝ} {C₀ C₁ : ℝ≥0} {K : ℝ}
    (hF : LipschitzWith C₀ F) (hG : LipschitzWith C₁ G) (hFG : ∀ x, |F x-G x| ≤ K)
    (front : List (GaussianStep ι)) (hm : ∀ st ∈ front, 0 < st.1) (x : ι → ℝ) :
    |prefixContinuation front F x-prefixContinuation front G x| ≤ K := by
  induction front generalizing x with
  | nil => exact hFG x
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    have ht := fun c hc => hm c (List.mem_cons_of_mem _ hc)
    exact shiftedContinuation_abs_sub_le (hm (m,q) List.mem_cons_self)
      ((exponentialIncrement_gaussian q).integrable_shift (prefixContinuation_lipschitz hF tail ht) m)
      ((exponentialIncrement_gaussian q).integrable_shift (prefixContinuation_lipschitz hG tail ht) m)
      (ih ht) x

 theorem BoundaryTree.weight_smooth_static {F : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) {W : ∀ b, κ b → (ι → ℝ) → ℝ}
    (hW : ∀ b σ, BddSmooth 0 (W b σ)) {front : List (GaussianStep ι)}
    (T : BoundaryTree ι β front) (hm : ∀ st ∈ front, 0 < st.1) (σ : T.Assignment κ) :
    BddSmooth 0 (T.weight (fun _ => F) (fun b σ _ => W b σ) σ 0) := by
  induction T with
  | leaf b => exact hW b σ
  | @step st tail T ih =>
    rcases st with ⟨m,q⟩
    have ht := fun c hc => hm c (List.mem_cons_of_mem _ hc)
    have hf := prefixContinuation_lipschitz hF tail ht
    have hi := (exponentialIncrement_gaussian q).integrable_shift hf m
    obtain ⟨B,hB,hb⟩ := (ih ht σ).bound
    exact ⟨continuous_shiftedMean hf (ih ht σ).continuous hB hb hi,
      ⟨B,hB, fun x => abs_tiltedMean_le ((ih ht σ).continuous.comp (continuous_const.add continuous_id)).measurable
        (hi x) (fun z => hb (x+z))⟩⟩
  | fork T U ihT ihU => exact (ihT hm σ.1).mul (ihU hm σ.2)

 theorem BoundaryTree.weight_nonneg_static {F : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) {W : ∀ b, κ b → (ι → ℝ) → ℝ}
    (hW : ∀ b σ x, 0 ≤ W b σ x) {front : List (GaussianStep ι)}
    (T : BoundaryTree ι β front) (hm : ∀ st ∈ front, 0 < st.1) (σ : T.Assignment κ) (x : ι → ℝ) :
    0 ≤ T.weight (fun _ => F) (fun b σ _ => W b σ) σ 0 x := by
  induction T generalizing x with
  | leaf b => exact hW b σ x
  | @step st tail T ih =>
    rcases st with ⟨m,q⟩
    have ht := fun c hc => hm c (List.mem_cons_of_mem _ hc)
    exact shiftedMean_nonneg (ih ht σ)
      ((exponentialIncrement_gaussian q).integrable_shift (prefixContinuation_lipschitz hF tail ht) m x)
  | fork T U ihT ihU => exact mul_nonneg (ihT hm σ.1 x) (ihU hm σ.2 x)

noncomputable def BoundaryTree.expWeight (F : (ι → ℝ) → ℝ)
    (W : ∀ b, κ b → (ι → ℝ) → ℝ) {front : List (GaussianStep ι)}
    (T : BoundaryTree ι β front) (a : ℝ) (σ : T.Assignment κ) (x : ι → ℝ) : ℝ :=
  Real.exp (a*prefixContinuation front F x)*T.weight (fun _ => F) (fun b σ _ => W b σ) σ 0 x

 theorem BoundaryTree.expWeight_step {F : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (W : ∀ b, κ b → (ι → ℝ) → ℝ)
    {front : List (GaussianStep ι)} (T : BoundaryTree ι β front)
    (hm : ∀ st ∈ front, 0 < st.1) (a : ℝ) {b : ℝ} (hb : 0 < b)
    (q : ι → ℝ≥0) (σ : T.Assignment κ) (x : ι → ℝ) :
    (T.step (b,q)).expWeight F W a σ x =
      Real.exp ((a-b)*prefixContinuation ((b,q)::front) F x)*
        ∫ z, T.expWeight F W b σ (x+z) ∂(Measure.pi fun i => gaussianReal 0 (q i)) := by
  have hi := (exponentialIncrement_gaussian q).integrable_shift (prefixContinuation_lipschitz hF front hm) b x
  have he := exp_mul_shiftedContinuation hb.ne' x hi
  change Real.exp (a*prefixContinuation ((b,q)::front) F x)*(_ / _) = _
  simp only [expWeight]
  simp_rw [mul_comm (Real.exp (b*prefixContinuation front F (x+_)))]
  have hx : Real.exp (a*prefixContinuation ((b,q)::front) F x) =
      Real.exp ((a-b)*prefixContinuation ((b,q)::front) F x)*
        ∫ z, Real.exp (b*prefixContinuation front F (x+z)) ∂(Measure.pi fun i => gaussianReal 0 (q i)) := by
    rw [← he,← Real.exp_add]
    congr 1
    change _ = (a-b)*shiftedContinuation _ b (prefixContinuation front F) x+
      b*shiftedContinuation _ b (prefixContinuation front F) x
    simp only [prefixContinuation]
    ring
  rw [hx]
  field_simp [ne_of_gt (partition_pos b hi)]

 theorem BoundaryTree.expWeight_fork (F : (ι → ℝ) → ℝ)
    (W : ∀ b, κ b → (ι → ℝ) → ℝ) {front : List (GaussianStep ι)}
    (T U : BoundaryTree ι β front) (a : ℝ) (σ : (T.fork U).Assignment κ) (x : ι → ℝ) :
    (T.fork U).expWeight F W a σ x = Real.exp (-a*prefixContinuation front F x)*
      (T.expWeight F W a σ.1 x*U.expWeight F W a σ.2 x) := by
  simp only [expWeight,weight]
  have he : Real.exp (-a*prefixContinuation front F x)*Real.exp (a*prefixContinuation front F x) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 2; ring
  calc
    _ = (Real.exp (-a*prefixContinuation front F x)*Real.exp (a*prefixContinuation front F x))*
        (Real.exp (a*prefixContinuation front F x)*T.weight (fun _ => F) (fun b σ _ => W b σ) σ.1 0 x*
        U.weight (fun _ => F) (fun b σ _ => W b σ) σ.2 0 x) := by rw [he]; ring
    _ = _ := by ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι β : Type*} {κ : β → Type*} [Fintype ι]

 theorem exp_mul_le_exp_mul_of_abs_sub {x y K a : ℝ} (h : |x-y| ≤ K) :
    Real.exp (a*x) ≤ Real.exp (|a| *K)*Real.exp (a*y) := by
  rw [← Real.exp_add,Real.exp_le_exp]
  have hh := (le_abs_self (a*(x-y))).trans
    ((abs_mul a (x-y)).le.trans (mul_le_mul_of_nonneg_left h (abs_nonneg a)))
  linarith

 

 theorem BoundaryTree.expWeight_le {F G : (ι → ℝ) → ℝ} {C₀ C₁ : ℝ≥0} {K m a : ℝ}
    (hF : LipschitzWith C₀ F) (hG : LipschitzWith C₁ G) (hK : 0 ≤ K)
    (hFG : ∀ x, |G x-F x| ≤ K)
    {W V : ∀ b, κ b → (ι → ℝ) → ℝ} (hW : ∀ b σ, BddSmooth 0 (W b σ))
    (hV : ∀ b σ, BddSmooth 0 (V b σ))
    (hpW : ∀ b σ x, 0 ≤ W b σ x) (hpV : ∀ b σ x, 0 ≤ V b σ x)
    (E : β → ℝ) (hE : ∀ b σ x, V b σ x ≤ Real.exp (E b)*W b σ x)
    {front : List (GaussianStep ι)} (T : BoundaryTree ι β front) (hO : PrefixOrdered a m front)
    (σ : T.Assignment κ) (x : ι → ℝ) :
    T.expWeight G V a σ x ≤ Real.exp (T.budget (fun b => E b+2*m*K)-a*K)*T.expWeight F W a σ x := by
  induction T generalizing a x with
  | leaf b =>
    have he := exp_mul_le_exp_mul_of_abs_sub (a := a) (hFG x)
    rw [abs_of_nonneg hO.1] at he
    have hb : E b+a*K ≤ E b+2*m*K-a*K := by nlinarith [mul_nonneg (sub_nonneg.mpr hO.2) hK]
    change Real.exp (a*G x)*V b σ x ≤ Real.exp (E b+2*m*K-a*K)*(Real.exp (a*F x)*W b σ x)
    calc
      _ ≤ (Real.exp (a*K)*Real.exp (a*F x))*(Real.exp (E b)*W b σ x) :=
        mul_le_mul he (hE b σ x) (hpV b σ x) (by positivity)
      _ = Real.exp (E b+a*K)*(Real.exp (a*F x)*W b σ x) := by rw [Real.exp_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hb) (mul_nonneg (Real.exp_nonneg _) (hpW b σ x))
  | @step st tail T ih =>
    rcases st with ⟨b,q⟩
    have ht := hO.2.2.2
    let ν := Measure.pi fun i => gaussianReal 0 (q i)
    have hf := prefixContinuation_lipschitz hF tail ht.positive
    have hg := prefixContinuation_lipschitz hG tail ht.positive
    have hIF : Integrable (fun z => T.expWeight F W b σ (x+z)) ν := by
      have hi := (T.weight_smooth_static hF hW ht.positive σ).integrable_shifted_weighted
        ((exponentialIncrement_gaussian q).integrable_shift hf b x)
      simpa only [expWeight,mul_comm] using hi
    have hIG : Integrable (fun z => T.expWeight G V b σ (x+z)) ν := by
      have hi := (T.weight_smooth_static hG hV ht.positive σ).integrable_shifted_weighted
        ((exponentialIncrement_gaussian q).integrable_shift hg b x)
      simpa only [expWeight,mul_comm] using hi
    have hi : (∫ z, T.expWeight G V b σ (x+z) ∂ν) ≤
        Real.exp (T.budget (fun d => E d+2*m*K)-b*K)*∫ z, T.expWeight F W b σ (x+z) ∂ν := by
      rw [← integral_const_mul]
      exact integral_mono hIG (hIF.const_mul _) (fun z => ih ht σ (x+z))
    have hip : 0 ≤ ∫ z, T.expWeight G V b σ (x+z) ∂ν := integral_nonneg fun z =>
      mul_nonneg (Real.exp_nonneg _) (T.weight_nonneg_static hG hpV ht.positive σ (x+z))
    have he := exp_mul_le_exp_mul_of_abs_sub (a := a-b)
      (prefixContinuation_abs_sub_le hG hF hFG ((b,q)::tail) hO.positive x)
    rw [abs_of_nonpos (sub_nonpos.mpr hO.2.1)] at he
    rw [T.expWeight_step hG V ht.positive a hO.2.2.1 q σ x,
      T.expWeight_step hF W ht.positive a hO.2.2.1 q σ x]
    calc
      _ ≤ (Real.exp (-(a-b)*K)*Real.exp ((a-b)*prefixContinuation ((b,q)::tail) F x))*
          (Real.exp (T.budget (fun d => E d+2*m*K)-b*K)*∫ z, T.expWeight F W b σ (x+z) ∂ν) :=
        mul_le_mul he hi hip (by positivity)
      _ = _ := by
        dsimp only [budget]
        rw [show T.budget (fun d => E d+2*m*K)-a*K = -(a-b)*K+(T.budget (fun d => E d+2*m*K)-b*K) by ring,Real.exp_add]
        ring
  | @fork front T U ihT ihU =>
    have ih1 := ihT hO σ.1 x
    have ih2 := ihU hO σ.2 x
    have hpT : 0 ≤ T.expWeight G V a σ.1 x :=
      mul_nonneg (Real.exp_nonneg _) (T.weight_nonneg_static hG hpV hO.positive σ.1 x)
    have hpU : 0 ≤ U.expWeight G V a σ.2 x :=
      mul_nonneg (Real.exp_nonneg _) (U.weight_nonneg_static hG hpV hO.positive σ.2 x)
    have hpF : 0 ≤ Real.exp (T.budget (fun d => E d+2*m*K)-a*K)*T.expWeight F W a σ.1 x :=
      mul_nonneg (Real.exp_nonneg _) (mul_nonneg (Real.exp_nonneg _)
        (T.weight_nonneg_static hF hpW hO.positive σ.1 x))
    have he := exp_mul_le_exp_mul_of_abs_sub (a := -a)
      (prefixContinuation_abs_sub_le hG hF hFG front hO.positive x)
    rw [abs_neg,abs_of_nonneg hO.bounds.1] at he
    rw [expWeight_fork F W,expWeight_fork G V]
    calc
      _ ≤ (Real.exp (a*K)*Real.exp (-a*prefixContinuation front F x))*
          ((Real.exp (T.budget (fun d => E d+2*m*K)-a*K)*T.expWeight F W a σ.1 x)*
          (Real.exp (U.budget (fun d => E d+2*m*K)-a*K)*U.expWeight F W a σ.2 x)) :=
        mul_le_mul he (mul_le_mul ih1 ih2 hpU hpF) (mul_nonneg hpT hpU) (by positivity)
      _ = _ := by
        dsimp only [budget]
        rw [show T.budget (fun d => E d+2*m*K)+U.budget (fun d => E d+2*m*K)-a*K =
          a*K+(T.budget (fun d => E d+2*m*K)-a*K)+(U.budget (fun d => E d+2*m*K)-a*K) by ring,
          Real.exp_add,Real.exp_add]
        ring

 theorem BoundaryTree.finite_relative {F G : (ι → ℝ) → ℝ} {C₀ C₁ : ℝ≥0} {K m : ℝ}
    (hF : LipschitzWith C₀ F) (hG : LipschitzWith C₁ G) (hK : 0 ≤ K)
    (hFG : ∀ x, |G x-F x| ≤ K)
    {W V : ∀ b, κ b → (ι → ℝ) → ℝ} (hW : ∀ b σ, BddSmooth 0 (W b σ))
    (hV : ∀ b σ, BddSmooth 0 (V b σ))
    (hpW : ∀ b σ x, 0 ≤ W b σ x) (hpV : ∀ b σ x, 0 ≤ V b σ x)
    (E : β → ℝ) (hE : ∀ b σ x, V b σ x ≤ Real.exp (E b)*W b σ x)
    {front : List (GaussianStep ι)} (T : BoundaryTree ι β front) (hO : PrefixOrdered 0 m front)
    (σ : T.Assignment κ) (x : ι → ℝ) :
    T.weight (fun _ => G) (fun b σ _ => V b σ) σ 0 x ≤
      Real.exp (T.budget (fun b => E b+2*m*K))*T.weight (fun _ => F) (fun b σ _ => W b σ) σ 0 x := by
  simpa only [expWeight,zero_mul,Real.exp_zero,one_mul,sub_zero] using
    T.expWeight_le hF hG hK hFG hW hV hpW hpV E hE hO σ x

end SKFluctuations.Hierarchy

end

end OAI
