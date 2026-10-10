import Mathlib
import OAI.Probability.SKFluctuations.Chain
import OAI.Probability.SKFluctuations.MarkedAttachPreserves

namespace OAI

/-! Marked Pair Expectation. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S]

 

noncomputable def markedPairExpectation (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (P : T.Assignment → ℝ) (C : S → S → ℝ) (x : ι → ℝ) : ℝ :=
  ((T.markedAttach a).map fun p => p.coeff*
    ((p.tree.markedAttach a).map fun q => q.coeff*
      q.tree.expect w φ (fun σ => P (p.restrict (q.restrict σ))*
        C (p.spin (q.restrict σ)) (q.spin σ)) x).sum).sum

 theorem powerJet_cons_marked (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (P : T.Assignment → ℝ) (u : ι → ℝ) (vs : List (ι → ℝ)) (x : ι → ℝ) :
    powerJet w φ a (u::vs) T P x = ((T.markedAttach a).map fun p =>
      p.coeff*powerJet w φ a vs p.tree (fun σ => P (p.restrict σ)*φ (p.spin σ) u) x).sum := by
  rw [powerJet,← T.markedAttach_forget a,List.map_map]
  rfl

 theorem powerJet_two_marked (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (P : T.Assignment → ℝ) (u v x : ι → ℝ) :
    powerJet w φ a [u,v] T P x =
      T.markedPairExpectation w φ a P (fun σ τ => φ σ u*φ τ v) x := by
  rw [powerJet_cons_marked]
  simp_rw [powerJet_cons_marked]
  simp only [powerJet,markedPairExpectation,mul_assoc]

 theorem list_sum_finset_sum {α β : Type*} (ps : List α) (is : Finset β) (f : α → β → ℝ) :
    (ps.map fun p => ∑ i ∈ is, f p i).sum = ∑ i ∈ is, (ps.map fun p => f p i).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,ih]

 theorem markedPairExpectation_finsetSum (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (P : T.Assignment → ℝ) {κ : Type*} (is : Finset κ) (C : κ → S → S → ℝ) (x : ι → ℝ) :
    T.markedPairExpectation w φ a P (fun σ τ => ∑ i ∈ is, C i σ τ) x =
      ∑ i ∈ is, T.markedPairExpectation w φ a P (C i) x := by
  simp only [markedPairExpectation,Finset.mul_sum,expect_finsetSum]
  simp_rw [list_sum_finset_sum,Finset.mul_sum,list_sum_finset_sum]

 
noncomputable def blockKernel {n : ℕ} (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ)) (σ τ : S) : ℝ :=
  ∑ i, φ σ (L (Pi.single i 1))*φ τ (L (Pi.single i 1))

 theorem powerTrace_eq_markedPair {n : ℕ} (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ)) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) (a : ℝ) (P : T.Assignment → ℝ) (x : ι → ℝ) :
    T.powerTrace w φ L a P x = T.markedPairExpectation w φ a P (blockKernel φ L) x := by
  rw [show blockKernel φ L = (fun σ τ => ∑ i, φ σ (L (Pi.single i 1))*φ τ (L (Pi.single i 1))) from rfl,
    markedPairExpectation_finsetSum]
  simp only [powerTrace,powerJet_two_marked]

variable [Nonempty S]

 theorem powerTrace_zero_one {n : ℕ} {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (ha : OrderedSteps 0 steps)
    (x : ι → ℝ) : T.powerTrace w φ L 0 (fun _ => 1) x = 0 := by
  simp only [powerTrace,powerJet_constant_two hw φ T ha,zero_mul,zero_pow (by decide : 2 ≠ 0),add_zero,Finset.sum_const_zero]

 

 theorem hasDerivWithinAt_root_covariance {n : ℕ} {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (ha : OrderedSteps 0 steps)
    (P : T.Assignment → ℝ) (x : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt
      (fun s => linearClockTest L 0 (gaussianHierarchy w φ steps) (T.expect w φ P) s x)
      ((1/2:ℝ)*linearClockTest L 0 (gaussianHierarchy w φ steps)
        (T.markedPairExpectation w φ 0 P (blockKernel φ L)) t x) (Ici 0) t := by
  have hd := T.hasDerivWithinAt_linearClockTest hw φ L ha P x ht
  have hz : T.powerTrace w φ L 0 (fun _ => 1) = fun _ => 0 := funext (T.powerTrace_zero_one hw φ L ha)
  rw [hz] at hd
  have hz' : linearClockTest L 0 (gaussianHierarchy w φ steps) (fun _ => 0) t x = 0 := by
    simp [linearClockTest,shiftedMean,tiltedMean]
  rw [hz',mul_zero,sub_zero] at hd
  have he : T.powerTrace w φ L 0 P = T.markedPairExpectation w φ 0 P (blockKernel φ L) :=
    funext (fun y => T.powerTrace_eq_markedPair w φ L 0 P y)
  rw [he] at hd
  exact hd

end SKFluctuations.Hierarchy.ReplicaTree

namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S]

 

noncomputable def markedOffDiagonal (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (P : T.Assignment → ℝ) (C : S → S → ℝ) (x : ι → ℝ) : ℝ :=
  ((T.markedAttach a).map fun p => p.coeff*
    ((p.tree.markedAttach a).map fun q => q.coeff*(1-q.hit p.mark)*
      q.tree.expect w φ (fun σ => P (p.restrict (q.restrict σ))*
        C (p.spin (q.restrict σ)) (q.spin σ)) x).sum).sum

 theorem markedPlacement_diagonal_test (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps}
    (p : MarkedPlacement T) (q : MarkedPlacement p.tree) (P : T.Assignment → ℝ)
    {C : S → S → ℝ} {d : ℝ} (hC : ∀ σ, C σ σ = d) (x : ι → ℝ) :
    q.hit p.mark*q.tree.expect w φ (fun σ => P (p.restrict (q.restrict σ))*
      C (p.spin (q.restrict σ)) (q.spin σ)) x =
      d*q.hit p.mark*q.tree.expect w φ (fun σ => P (p.restrict (q.restrict σ))) x := by
  classical
  by_cases h : q.mark = q.embed p.mark
  · have hs (σ : q.tree.Assignment) : p.spin (q.restrict σ) = q.spin σ := by
      calc
        _ = p.tree.atSlot (q.restrict σ) p.mark := p.spin_at _
        _ = q.tree.atSlot σ (q.embed p.mark) := q.restrict_at _ _
        _ = q.tree.atSlot σ q.mark := by rw [h]
        _ = _ := (q.spin_at _).symm
    simp only [MarkedPlacement.hit,ite_eq_left h,one_mul,mul_one]
    simp_rw [hs,hC]
    rw [show (fun σ : q.tree.Assignment => P (p.restrict (q.restrict σ))*d) =
      (fun σ => d*P (p.restrict (q.restrict σ))) from funext (fun _ => mul_comm _ _),expect_const_mul]
  · simp only [MarkedPlacement.hit,ite_eq_right h,zero_mul,mul_zero]

variable [Nonempty S]

 

 theorem markedPair_eq_offDiagonal {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (P : T.Assignment → ℝ)
    {C : S → S → ℝ} {d : ℝ} (hC : ∀ σ, C σ σ = d) (x : ι → ℝ) :
    T.markedPairExpectation w φ a P C x =
      T.markedOffDiagonal w φ a P C x+d*a*T.expect w φ P x := by
  have h (p : MarkedPlacement T) (q : MarkedPlacement p.tree) :
      q.coeff*q.tree.expect w φ (fun σ => P (p.restrict (q.restrict σ))*C (p.spin (q.restrict σ)) (q.spin σ)) x =
      q.coeff*(1-q.hit p.mark)*q.tree.expect w φ (fun σ => P (p.restrict (q.restrict σ))*C (p.spin (q.restrict σ)) (q.spin σ)) x+
      d*(q.coeff*q.hit p.mark*q.tree.expect w φ (fun σ => P (p.restrict (q.restrict σ))) x) := by
    calc
      _ = q.coeff*(1-q.hit p.mark)*q.tree.expect w φ (fun σ => P (p.restrict (q.restrict σ))*C (p.spin (q.restrict σ)) (q.spin σ)) x+
        q.coeff*(q.hit p.mark*q.tree.expect w φ (fun σ => P (p.restrict (q.restrict σ))*C (p.spin (q.restrict σ)) (q.spin σ)) x) := by ring
      _ = _ := by rw [markedPlacement_diagonal_test w φ p q P hC]; ring
  unfold markedPairExpectation
  simp_rw [h,List.sum_map_add,List.sum_map_mul_left,mul_add]
  rw [List.sum_map_add]
  change T.markedOffDiagonal w φ a P C x+_ = _
  congr 1
  have he : ((T.markedAttach a).map fun p => p.coeff*(d*
      ((p.tree.markedAttach a).map fun q => q.coeff*q.hit p.mark*
        q.tree.expect w φ (fun σ => P (p.restrict (q.restrict σ))) x).sum)).sum =
      d*((T.markedAttach a).map fun p => p.coeff*
      ((p.tree.markedAttach a).map fun q => q.coeff*q.hit p.mark*
        q.tree.expect w φ (fun σ => P (p.restrict (q.restrict σ))) x).sum).sum := by
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p _
    ring
  rw [he,T.markedAttach_tested_diagonal hw φ ha]
  ring

 theorem markedPair_zero_eq_offDiagonal {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    (ha : OrderedSteps 0 steps) (P : T.Assignment → ℝ)
    {C : S → S → ℝ} {d : ℝ} (hC : ∀ σ, C σ σ = d) (x : ι → ℝ) :
    T.markedPairExpectation w φ 0 P C x = T.markedOffDiagonal w φ 0 P C x := by
  rw [T.markedPair_eq_offDiagonal hw φ ha P hC,mul_zero,zero_mul,add_zero]

end SKFluctuations.Hierarchy.ReplicaTree

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem HeatJet.nonnegativeProfileValue_constant {n : ℕ} (J : HeatJet n)
    (α : NonnegativeMassProfile) {m : ℝ} (hm : 0 < m) (l : ℝ) (t : ℝ≥0)
    (ht : 0 < (t:ℝ)) (hc : ∀ s ∈ Ico l (l+t), α.mass s = m)
    (x : Fin (n+1) → ℝ) :
    J.nonnegativeProfileValue α l t x = clockContinuation m J.F t x := by
  choose D _ hD using fun i => (J.smoothG i).bound
  have he (k : ℕ) : 0 < (1/2:ℝ)^k := by positivity
  have hh (k : ℕ) : |J.profileValue (α.positiveApprox k) l t x-clockContinuation m J.F t x| ≤
      (1/2:ℝ)^k/2*(∑ i, (D i)^2)*(t:ℝ) := by
    rw [J.profileValue_constant (α.positiveApprox k) (add_pos hm (he k)) l t ht
      (fun s hs => by change α.mass s+(1/2:ℝ)^k = _; rw [hc s hs])]
    have h := J.potential_mass_difference D hD (add_pos hm (he k)) hm t.property x
    simp only [add_sub_cancel_left,abs_of_pos (he k)] at h
    convert h using 1 <;> rfl
  have hp : Tendsto (fun k : ℕ => (1/2:ℝ)^k/2*(∑ i, (D i)^2)*(t:ℝ)) atTop (𝓝 0) := by
    simpa only [zero_div,zero_mul] using
      (((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) < 1)).div_const 2).mul_const (∑ i, (D i)^2)).mul_const (t:ℝ)
  have hz : |J.nonnegativeProfileValue α l t x-clockContinuation m J.F t x| ≤ 0 :=
    le_of_tendsto_of_tendsto ((J.regularized_tendsto α l t x).sub_const _).abs hp (Filter.Eventually.of_forall hh)
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hz)

 theorem scalarParisiValue_dirac_zero {T : ℝ} (hT : 0 < T) :
    scalarParisiValue hT (diracMassProfile 0) = 0 := by
  have hs : ∀ s ∈ Ico (0:ℝ) (0+(⟨T,hT.le⟩:ℝ≥0)),
      (rescaledMassProfile (diracMassProfile 0) hT).mass s = 1 := by
    intro s hs
    exact ite_eq_right (not_lt.mpr (div_nonneg hs.1 hT.le))
  have hh := scalarTerminal.nonnegativeProfileValue_constant
    (rescaledMassProfile (diracMassProfile 0) hT) (by norm_num : (0:ℝ) < 1)
      0 ⟨T,hT.le⟩ hT hs 0
  unfold scalarParisiValue
  rw [hh]
  change clockContinuation 1 scalarTerminal.F T 0-T/2*scalarPenalty (diracMassProfile 0)-T/4 = 0
  have hm : clockContinuation 1 scalarTerminal.F T 0 = T/2 := by
    have hh := scalarTerminal_mass_one (⟨T,hT.le⟩ : ℝ≥0) 0
    change clockContinuation 1 scalarTerminal.F T 0 = Real.log (Real.cosh ((0 : Fin 1 → ℝ) 0))+T/2 at hh
    simpa only [Pi.zero_apply,Real.cosh_zero,Real.log_one,zero_add] using hh
  rw [hm,scalarPenalty_dirac (by constructor <;> norm_num : (0:ℝ) ∈ Icc 0 1)]
  ring

 

 theorem scalarParisiMinimizer_not_dirac_zero {T : ℝ} (hT : 1 < T)
    {α : boundedMassProfiles} (hα : α ∈ scalarProfiles)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (by linarith : 0 < T) α ≤
      scalarParisiValue (by linarith : 0 < T) β) :
    (profileStieltjes α).measure ≠ Measure.dirac (0:ℝ) := by
  intro he
  have hc : ∀ s, (rightMassProfile α).val s = (diracMassProfile 0).val s := by
    intro s
    have h := congrArg (fun f : StieltjesFunction ℝ => f s) (cdf_profileStieltjes hα)
    rw [he] at h
    have hd : cdf (Measure.dirac (0:ℝ)) s = if s < 0 then 0 else 1 := by
      rw [cdf_eq_real]
      by_cases hs : s < 0
      · simp [Measure.real,hs,not_le.mpr hs]
      · simp [Measure.real,hs,not_lt.mp hs]
    rw [hd] at h
    exact h.symm
  have hae : α.val =ᵐ[volume] (diracMassProfile 0).val :=
    (rightMassProfile_ae α).symm.trans (Filter.Eventually.of_forall hc)
  have hn := scalarParisiMinimum_neg hT hmin
  rw [scalarParisiValue_congr_ae (by linarith : 0 < T) hae,scalarParisiValue_dirac_zero] at hn
  exact lt_irrefl _ hn

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 

theorem HeatJet.grid_dyadic_cut {n : ℕ} (J : HeatJet n) (α : PositiveMassProfile)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (l : ℝ) (t : ℝ≥0) (ht : 0 < (t:ℝ))
    (j k r : ℕ) (hk : k ≤ 2^j)
    (hc : ∀ s ∈ Ico l (l+t), α.mass s = if s < l+(t:ℝ)*k/2^j then a else b) :
    (J.schedule (α.grid l t (j+r))).F =
      clockContinuation a (clockContinuation b J.F ((t:ℝ)-(t:ℝ)*k/2^j)) ((t:ℝ)*k/2^j) := by
  induction j generalizing J l t k with
  | zero =>
    have hk' : k = 0 ∨ k = 1 := by simpa only [pow_zero] using (Nat.le_one_iff_eq_zero_or_eq_one.mp hk)
    rcases hk' with rfl | rfl
    · simp only [Nat.cast_zero,mul_zero,zero_div,sub_zero,Nat.zero_add]
      rw [show clockContinuation a (clockContinuation b J.F t) 0 = clockContinuation b J.F t from
        funext (clockContinuation_zero ha.ne')]
      apply J.grid_constant α hb l t ht r
      intro s hs
      rw [hc s hs,ite_eq_right]
      simpa only [Nat.cast_zero,mul_zero,zero_div,add_zero,not_lt] using hs.1
    · simp only [Nat.cast_one,mul_one,pow_zero,div_one,sub_self,Nat.zero_add]
      rw [show clockContinuation b J.F 0 = J.F from funext (clockContinuation_zero hb.ne')]
      apply J.grid_constant α ha l t ht r
      intro s hs
      rw [hc s hs,ite_eq_left]
      simpa only [Nat.cast_one,mul_one,pow_zero,div_one] using hs.2
  | succ j ih =>
    have hp : (0:ℝ) < 2^j := by positivity
    have hhalf : 0 < ((t/2:ℝ≥0):ℝ) := by simpa using half_pos ht
    have he (u : ℕ) : (((t/2:ℝ≥0):ℝ)*(u:ℝ)/2^j) = (t:ℝ)*u/2^(j+1) := by
      simp only [NNReal.coe_div,NNReal.coe_ofNat,pow_succ]
      ring
    by_cases hkl : k ≤ 2^j
    · have hq : (t:ℝ)*k/2^(j+1) ≤ (t:ℝ)/2 := by
        rw [pow_succ]
        apply (div_le_iff₀ (mul_pos hp (by norm_num))).2
        have hkR : (k:ℝ) ≤ 2^j := by exact_mod_cast hkl
        nlinarith [mul_le_mul_of_nonneg_left hkR ht.le]
      have hl : ∀ s ∈ Ico l (l+(t/2:ℝ≥0)), α.mass s =
          if s < l+((t/2:ℝ≥0):ℝ)*k/2^j then a else b := by
        intro s hs
        rw [he]
        apply hc s
        simp only [NNReal.coe_div,NNReal.coe_ofNat] at hs
        exact ⟨hs.1,by linarith [hs.2]⟩
      have hr : ∀ s ∈ Ico (l+(t:ℝ)/2) (l+(t:ℝ)/2+(t/2:ℝ≥0)), α.mass s = b := by
        intro s hs
        have hs' : s ∈ Ico l (l+t) := by
          simp only [NNReal.coe_div,NNReal.coe_ofNat] at hs
          constructor <;> linarith [hs.1,hs.2]
        rw [hc s hs',ite_eq_right]
        linarith [hs.1]
      rw [Nat.succ_add,PositiveMassProfile.grid,J.schedule_append]
      rw [ih _ l (t/2) hhalf k hkl hl,J.grid_constant α hb (l+(t:ℝ)/2) (t/2) hhalf (j+r) hr,he]
      have hm : clockContinuation b (clockContinuation b J.F ((t/2:ℝ≥0):ℝ))
          (((t/2:ℝ≥0):ℝ)-(t:ℝ)*k/2^(j+1)) =
          clockContinuation b J.F ((t:ℝ)-(t:ℝ)*k/2^(j+1)) := by
        funext y
        rw [clockContinuation_add J.lipschitz hb.ne'
          (by simpa only [NNReal.coe_div,NNReal.coe_ofNat] using sub_nonneg.mpr hq) (by positivity)]
        congr 1
        simp only [NNReal.coe_div,NNReal.coe_ofNat]
        ring
      rw [hm]
    · have hklo : 2^j ≤ k := (lt_of_not_ge hkl).le
      have hkr : k-2^j ≤ 2^j := by rw [pow_succ] at hk; omega
      have hcut : (t:ℝ)/2+((t/2:ℝ≥0):ℝ)*((k-2^j:ℕ):ℝ)/2^j = (t:ℝ)*k/2^(j+1) := by
        rw [Nat.cast_sub hklo,Nat.cast_pow,Nat.cast_ofNat]
        simp only [NNReal.coe_div,NNReal.coe_ofNat,pow_succ]
        field_simp
        ring
      have hq : (t:ℝ)/2 ≤ (t:ℝ)*k/2^(j+1) := by
        rw [← hcut]
        have : 0 ≤ ((t/2:ℝ≥0):ℝ)*((k-2^j:ℕ):ℝ)/2^j := by positivity
        linarith
      have hl : ∀ s ∈ Ico l (l+(t/2:ℝ≥0)), α.mass s = a := by
        intro s hs
        have hs' : s ∈ Ico l (l+t) := by
          simp only [NNReal.coe_div,NNReal.coe_ofNat] at hs
          exact ⟨hs.1,by linarith [hs.2]⟩
        rw [hc s hs',ite_eq_left]
        simp only [NNReal.coe_div,NNReal.coe_ofNat] at hs
        linarith [hs.2]
      have hr : ∀ s ∈ Ico (l+(t:ℝ)/2) (l+(t:ℝ)/2+(t/2:ℝ≥0)), α.mass s =
          if s < l+(t:ℝ)/2+((t/2:ℝ≥0):ℝ)*((k-2^j:ℕ):ℝ)/2^j then a else b := by
        intro s hs
        rw [add_assoc l,hcut]
        apply hc s
        simp only [NNReal.coe_div,NNReal.coe_ofNat] at hs
        constructor <;> linarith [hs.1,hs.2]
      rw [Nat.succ_add,PositiveMassProfile.grid,J.schedule_append]
      rw [(J.schedule (α.grid (l+(t:ℝ)/2) (t/2) (j+r))).grid_constant α ha l (t/2) hhalf (j+r) hl]
      rw [ih _ (l+(t:ℝ)/2) (t/2) hhalf (k-2^j) hkr hr]
      have hh : ((t/2:ℝ≥0):ℝ)-((t/2:ℝ≥0):ℝ)*((k-2^j:ℕ):ℝ)/2^j = (t:ℝ)-(t:ℝ)*k/2^(j+1) := by
        simp only [NNReal.coe_div,NNReal.coe_ofNat] at hcut ⊢
        linarith
      rw [hh]
      have hFl : LipschitzWith J.C (clockContinuation b J.F ((t:ℝ)-(t:ℝ)*k/2^(j+1))) :=
        (J.evolve hb ((t:ℝ)-(t:ℝ)*k/2^(j+1))).lipschitz
      funext y
      rw [clockContinuation_add hFl ha.ne' (by positivity) (by positivity)]
      congr 1

 theorem HeatJet.profileValue_dyadic_cut {n : ℕ} (J : HeatJet n) (α : PositiveMassProfile)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (l : ℝ) (t : ℝ≥0) (ht : 0 < (t:ℝ))
    (j k : ℕ) (hk : k ≤ 2^j)
    (hc : ∀ s ∈ Ico l (l+t), α.mass s = if s < l+(t:ℝ)*k/2^j then a else b)
    (x : Fin (n+1) → ℝ) :
    J.profileValue α l t x =
      clockContinuation a (clockContinuation b J.F ((t:ℝ)-(t:ℝ)*k/2^j)) ((t:ℝ)*k/2^j) x := by
  have hh := (J.grid_tendsto α l t x).comp (tendsto_add_atTop_nat j)
  apply tendsto_nhds_unique hh
  have he : (fun r : ℕ => (J.schedule (α.grid l t (r+j))).F x) =
      (fun _ : ℕ => clockContinuation a (clockContinuation b J.F ((t:ℝ)-(t:ℝ)*k/2^j)) ((t:ℝ)*k/2^j) x) := by
    funext r
    rw [Nat.add_comm,J.grid_dyadic_cut α ha hb l t ht j k r hk hc]
  change Tendsto (fun r : ℕ => (J.schedule (α.grid l t (r+j))).F x) _ _
  rw [he]
  exact tendsto_const_nhds

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 

 theorem HeatJet.nonnegativeProfileValue_dyadic_cut {n : ℕ} (J : HeatJet n)
    (α : NonnegativeMassProfile) {b : ℝ} (hb : 0 < b) (l : ℝ) (t : ℝ≥0)
    (ht : 0 < (t:ℝ)) (j d : ℕ) (hd : d ≤ 2^j)
    (hc : ∀ s ∈ Ico l (l+t), α.mass s = if s < l+(t:ℝ)*(d:ℝ)/2^j then 0 else b)
    (x : Fin (n+1) → ℝ) :
    J.nonnegativeProfileValue α l t x = zeroContinuation
      (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 (Real.toNNReal ((t:ℝ)*(d:ℝ)/2^j)))
      (clockContinuation b J.F ((t:ℝ)-(t:ℝ)*(d:ℝ)/2^j)) x := by
  let e : ℕ → ℝ := fun k => (1/2:ℝ)^k
  have he (k : ℕ) : 0 < e k := by dsimp [e]; positivity
  have hq : 0 ≤ (t:ℝ)-(t:ℝ)*(d:ℝ)/2^j := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^j)).2
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hd) ht.le
  have hp : Tendsto e atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hp' : Tendsto e atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hp,Filter.Eventually.of_forall he⟩
  let F := clockContinuation b J.F ((t:ℝ)-(t:ℝ)*(d:ℝ)/2^j)
  have hF : LipschitzWith J.C F := (J.evolve hb _).lipschitz
  have hl := (shiftedContinuation_tendsto_zero_mass hF
    (exponentialIncrement_gaussian (fun _ : Fin (n+1) => Real.toNNReal ((t:ℝ)*(d:ℝ)/2^j))) x).comp hp'
  change Tendsto (fun k => clockContinuation (e k) F ((t:ℝ)*(d:ℝ)/2^j) x) atTop _ at hl
  have hs (k : ℕ) : J.profileValue (α.positiveApprox k) l t x =
      clockContinuation (e k) (clockContinuation (b+e k) J.F ((t:ℝ)-(t:ℝ)*(d:ℝ)/2^j)) ((t:ℝ)*(d:ℝ)/2^j) x := by
    apply J.profileValue_dyadic_cut (α.positiveApprox k) (he k) (add_pos hb (he k)) l t ht j d hd
    intro s hs
    dsimp only [NonnegativeMassProfile.positiveApprox]
    rw [hc s hs]
    split_ifs <;> simp only [zero_add,e]
  choose D _ hD using fun i => (J.smoothG i).bound
  have hd (k : ℕ) : dist (clockContinuation (e k) F ((t:ℝ)*(d:ℝ)/2^j) x)
      (J.profileValue (α.positiveApprox k) l t x) ≤
      e k/2*(∑ i, (D i)^2)*((t:ℝ)-(t:ℝ)*(d:ℝ)/2^j) := by
    rw [hs,Real.dist_eq,abs_sub_comm]
    apply clockContinuation_abs_sub_le (J.evolve (add_pos hb (he k)) _).lipschitz
      hF (he k)
    intro y
    have h := J.potential_mass_difference D hD (add_pos hb (he k)) hb hq y
    simpa only [HeatJet.evolve,F,add_sub_cancel_left,abs_of_pos (he k)] using h
  have htend : Tendsto (fun k => dist (clockContinuation (e k) F ((t:ℝ)*(d:ℝ)/2^j) x)
      (J.profileValue (α.positiveApprox k) l t x)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) hd
    simpa only [zero_div,zero_mul] using
      ((hp.div_const 2).mul_const (∑ i, (D i)^2)).mul_const ((t:ℝ)-(t:ℝ)*(d:ℝ)/2^j)
  exact tendsto_nhds_unique (J.regularized_tendsto α l t x) (hl.congr_dist htend)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

noncomputable def scalarDyadicBelow (q : ℝ) (j : ℕ) : ℝ :=
  (⌊q*(2:ℝ)^j⌋₊:ℝ)/(2:ℝ)^j

 theorem scalarDyadicBelow_nonneg (q : ℝ) (j : ℕ) : 0 ≤ scalarDyadicBelow q j := by
  unfold scalarDyadicBelow
  positivity

 theorem scalarDyadicBelow_le {q : ℝ} (hq : 0 ≤ q) (j : ℕ) : scalarDyadicBelow q j ≤ q := by
  unfold scalarDyadicBelow
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^j)).2
  exact Nat.floor_le (mul_nonneg hq (by positivity))

 theorem scalarDyadicBelow_numerator {q : ℝ} (hq : q ≤ 1) (j : ℕ) : ⌊q*(2:ℝ)^j⌋₊ ≤ 2^j := by
  apply Nat.floor_le_of_le
  simpa only [Nat.cast_pow,Nat.cast_ofNat,one_mul] using mul_le_mul_of_nonneg_right hq (show (0:ℝ) ≤ 2^j by positivity)

 theorem scalarDyadicBelow_tendsto {q : ℝ} (hq : 0 ≤ q) :
    Tendsto (scalarDyadicBelow q) atTop (𝓝 q) :=
  (tendsto_nat_floor_mul_div_atTop hq).comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2))

 

theorem diracMassProfile_tendsto_below {γ : Type*} {l : Filter γ} {f : γ → ℝ} {q : ℝ}
    (hf : Tendsto f l (𝓝 q)) (hle : ∀ᶠ i in l, f i ≤ q) :
    Tendsto (fun i => diracMassProfile (f i)) l (𝓝 (diracMassProfile q)) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro s
  by_cases hs : s < q
  · have he := hf.eventually (lt_mem_nhds hs)
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with i hi
    change (if s < q then (0:ℝ) else 1) = if s < f i then 0 else 1
    rw [ite_eq_left hs,ite_eq_left hi]
  · apply tendsto_const_nhds.congr'
    filter_upwards [hle] with i hi
    change (if s < q then (0:ℝ) else 1) = if s < f i then 0 else 1
    rw [ite_eq_right hs,ite_eq_right (not_lt.mpr (hi.trans (le_of_not_gt hs)))]

 theorem scalarParisiValue_dirac_tendsto {T q : ℝ} (hT : 0 < T) (hq : 0 ≤ q) :
    Tendsto (fun j => scalarParisiValue hT (diracMassProfile (scalarDyadicBelow q j))) atTop
      (𝓝 (scalarParisiValue hT (diracMassProfile q))) :=
  (scalarParisiValue_continuous hT).continuousAt.tendsto.comp
    (diracMassProfile_tendsto_below (scalarDyadicBelow_tendsto hq)
      (Eventually.of_forall (scalarDyadicBelow_le hq)))

 theorem scalarRSValue_tendsto {T q : ℝ} (hT : 0 < T) (hq : 0 ≤ q) :
    Tendsto (fun j => Scalar.rsVariation T (scalarDyadicBelow q j)) atTop
      (𝓝 (Scalar.rsVariation T q)) := by
  apply (Scalar.rsVariation_derivative hT.le hq).continuousWithinAt.tendsto.comp
  exact tendsto_nhdsWithin_iff.mpr ⟨scalarDyadicBelow_tendsto hq,
    Eventually.of_forall (scalarDyadicBelow_nonneg q)⟩

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 

 theorem scalarParisiValue_dirac_dyadic_cut {T : ℝ} (hT : 0 < T) (j k : ℕ) (hk : k ≤ 2^j) :
    scalarParisiValue hT (diracMassProfile ((k:ℝ)/2^j)) = Scalar.rsVariation T ((k:ℝ)/2^j) := by
  have hq : (k:ℝ)/2^j ∈ Icc (0:ℝ) 1 :=
    ⟨by positivity,(div_le_one (by positivity : (0:ℝ) < 2^j)).2 (by exact_mod_cast hk)⟩
  have hu : 0 ≤ T*(k:ℝ)/2^j := by positivity
  have hv : 0 ≤ T-T*(k:ℝ)/2^j := sub_nonneg.mpr ((div_le_iff₀ (by positivity : (0:ℝ) < 2^j)).2
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hk) hT.le))
  have hs : ∀ s ∈ Ico (0:ℝ) (0+(⟨T,hT.le⟩:ℝ≥0)),
      (rescaledMassProfile (diracMassProfile ((k:ℝ)/2^j)) hT).mass s =
        if s < 0+((⟨T,hT.le⟩:ℝ≥0):ℝ)*k/2^j then 0 else 1 := by
    intro s _
    change (if s/T < (k:ℝ)/2^j then (0:ℝ) else 1) = if s < 0+T*(k:ℝ)/2^j then 0 else 1
    have he : s/T < (k:ℝ)/2^j ↔ s < T*(k:ℝ)/2^j := by
      rw [div_lt_iff₀ hT]
      ring_nf
    simp only [he,zero_add]
  have hh := scalarTerminal.nonnegativeProfileValue_dyadic_cut
    (rescaledMassProfile (diracMassProfile ((k:ℝ)/2^j)) hT) (by norm_num : (0:ℝ) < 1)
      0 ⟨T,hT.le⟩ hT j k hk hs 0
  change scalarTerminal.nonnegativeProfileValue (rescaledMassProfile (diracMassProfile ((k:ℝ)/2^j)) hT) 0 ⟨T,hT.le⟩ 0 =
    zeroContinuation (Measure.pi fun _ : Fin 1 => gaussianReal 0 (Real.toNNReal (T*(k:ℝ)/2^j)))
      (clockContinuation 1 scalarTerminal.F (T-T*(k:ℝ)/2^j)) 0 at hh
  have he := scalarRoot_mass_one (Real.toNNReal (T*(k:ℝ)/2^j)) (Real.toNNReal (T-T*(k:ℝ)/2^j))
  rw [Real.coe_toNNReal _ hu,Real.coe_toNNReal _ hv] at he
  unfold scalarParisiValue
  rw [hh,he,scalarPenalty_dirac hq]
  unfold Scalar.rsVariation
  have hmul : T*((k:ℝ)/2^j) = T*(k:ℝ)/2^j := by ring
  rw [hmul]
  ring

 

theorem scalarParisiValue_dirac {T q : ℝ} (hT : 0 < T) (hq : q ∈ Icc (0:ℝ) 1) :
    scalarParisiValue hT (diracMassProfile q) = Scalar.rsVariation T q := by
  apply tendsto_nhds_unique (scalarParisiValue_dirac_tendsto hT hq.1)
  have he (j : ℕ) : scalarParisiValue hT (diracMassProfile (scalarDyadicBelow q j)) =
      Scalar.rsVariation T (scalarDyadicBelow q j) :=
    scalarParisiValue_dirac_dyadic_cut hT j ⌊q*(2:ℝ)^j⌋₊ (scalarDyadicBelow_numerator hq.2 j)
  simpa only [he] using scalarRSValue_tendsto hT hq.1

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 
noncomputable def twoAtomMassProfile (q r : ℝ) {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) : boundedMassProfiles :=
  ⟨fun s => a*(diracMassProfile q).val s+(1-a)*(diracMassProfile r).val s,by
    constructor
    · intro s
      have hq := (diracMassProfile q).property.1 s
      have hr := (diracMassProfile r).property.1 s
      change 0 ≤ a*(diracMassProfile q).val s+(1-a)*(diracMassProfile r).val s ∧
        a*(diracMassProfile q).val s+(1-a)*(diracMassProfile r).val s ≤ 1
      constructor
      · exact add_nonneg (mul_nonneg ha.1 hq.1) (mul_nonneg (sub_nonneg.mpr ha.2) hr.1)
      · nlinarith [hq.2,hr.2,ha.1,ha.2]
    · exact ((diracMassProfile q).property.2.const_mul ha.1).add
        ((diracMassProfile r).property.2.const_mul (sub_nonneg.mpr ha.2))⟩

 theorem twoAtomMassProfile_mem {q r a : ℝ} (hq : q ∈ Icc (0:ℝ) 1) (hr : r ∈ Icc (0:ℝ) 1)
    (ha : a ∈ Icc (0:ℝ) 1) : twoAtomMassProfile q r ha ∈ scalarProfiles := by
  constructor
  · intro s hs
    change a*(diracMassProfile q).val s+(1-a)*(diracMassProfile r).val s = 0
    rw [(diracMassProfile_mem hq).1 s hs,(diracMassProfile_mem hr).1 s hs]
    ring
  · intro s hs
    change a*(diracMassProfile q).val s+(1-a)*(diracMassProfile r).val s = 1
    rw [(diracMassProfile_mem hq).2 s hs,(diracMassProfile_mem hr).2 s hs]
    ring

 theorem twoAtomMassProfile_apply {q r a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hqr : q ≤ r) (s : ℝ) :
    (twoAtomMassProfile q r ha).val s = if s < q then 0 else if s < r then a else 1 := by
  change a*(if s < q then 0 else 1)+(1-a)*(if s < r then 0 else 1) = _
  split_ifs <;> try ring_nf
  linarith

 theorem scalarPenalty_twoAtom {q r a : ℝ} (hq : q ∈ Icc (0:ℝ) 1) (hr : r ∈ Icc (0:ℝ) 1)
    (ha : a ∈ Icc (0:ℝ) 1) :
    scalarPenalty (twoAtomMassProfile q r ha) = (a*(1-q^2)+(1-a)*(1-r^2))/2 := by
  have he : weightedProfile (twoAtomMassProfile q r ha) =
      fun s => a*weightedProfile (diracMassProfile q) s+(1-a)*weightedProfile (diracMassProfile r) s := by
    funext s
    dsimp only [weightedProfile,twoAtomMassProfile]
    ring
  unfold scalarPenalty
  rw [he,intervalIntegral.integral_add
    ((weightedProfile_monotone (diracMassProfile q)).intervalIntegrable.const_mul a)
    ((weightedProfile_monotone (diracMassProfile r)).intervalIntegrable.const_mul (1-a)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  change a*scalarPenalty (diracMassProfile q)+(1-a)*scalarPenalty (diracMassProfile r) = _
  rw [scalarPenalty_dirac hq,scalarPenalty_dirac hr]
  ring

 theorem twoAtomMassProfile_tendsto_below {γ : Type*} {l : Filter γ} {f g : γ → ℝ}
    {q r a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hf : Tendsto f l (𝓝 q)) (hg : Tendsto g l (𝓝 r))
    (hlef : ∀ᶠ i in l, f i ≤ q) (hleg : ∀ᶠ i in l, g i ≤ r) :
    Tendsto (fun i => twoAtomMassProfile (f i) (g i) ha) l (𝓝 (twoAtomMassProfile q r ha)) := by
  have hq := tendsto_pi_nhds.mp (tendsto_subtype_rng.mp (diracMassProfile_tendsto_below hf hlef))
  have hr := tendsto_pi_nhds.mp (tendsto_subtype_rng.mp (diracMassProfile_tendsto_below hg hleg))
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro s
  exact ((hq s).const_mul a).add ((hr s).const_mul (1-a))

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 
noncomputable def HeatJet.rootBoundarySchedule {n : ℕ} (J : HeatJet n)
    (as : List PositiveMass) (l : ℝ) (q : ℕ → ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  zeroContinuation (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 (Real.toNNReal (q 0-l)))
    (J.boundarySchedule as (q 0) (fun i => q (i+1))).F x

 

 theorem HeatJet.rootCumulativeClock_uniform {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (as : List PositiveMass) {l M : ℝ} {q r : ℕ → ℝ}
    (hq : Monotone q) (hr : Monotone r) (hql : l ≤ q 0) (hrl : l ≤ r 0)
    (hend : q as.length = r as.length) (hM : 0 ≤ M)
    (ho : as.Pairwise (fun a b => a.val ≤ b.val)) (hu : ∀ b ∈ as, b.val ≤ 1)
    (hm : ∀ i ≤ as.length, |q i-r i| ≤ M) (x : Fin (n+1) → ℝ) :
    |J.rootBoundarySchedule as l q x-J.rootBoundarySchedule as l r x| ≤
      (∑ i, (D i)^2)/2*M := by
  cases as with
  | nil =>
    have he : q 0 = r 0 := hend
    simp only [HeatJet.rootBoundarySchedule,HeatJet.boundarySchedule,he,sub_self,abs_zero]
    positivity
  | cons a as =>
    let F := (J.boundarySchedule (a::as) (q 0) (fun i => q (i+1))).F
    let G := (J.boundarySchedule (a::as) (r 0) (fun i => r (i+1))).F
    have hF := (J.boundarySchedule (a::as) (q 0) (fun i => q (i+1))).lipschitz
    have hG := (J.boundarySchedule (a::as) (r 0) (fun i => r (i+1))).lipschitz
    have hqne := shiftedContinuation_tendsto_zero_mass hF
      (exponentialIncrement_gaussian (fun _ : Fin (n+1) => Real.toNNReal (q 0-l))) x
    have hrne := shiftedContinuation_tendsto_zero_mass hG
      (exponentialIncrement_gaussian (fun _ : Fin (n+1) => Real.toNNReal (r 0-l))) x
    apply le_of_tendsto (hqne.sub hrne).abs
    filter_upwards [self_mem_nhdsWithin, (Iio_mem_nhds a.property : Iio a.val ∈ 𝓝 (0:ℝ)) |> mem_nhdsWithin_of_mem_nhds] with e he hea
    have hep : 0 < e := he
    let c : PositiveMass := ⟨e,hep⟩
    have hoc : (c::a::as).Pairwise (fun a b => a.val ≤ b.val) := by
      apply List.pairwise_cons.mpr
      refine ⟨?_,ho⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hea.le
      · exact hea.le.trans ((List.pairwise_cons.mp ho).1 b hb)
    have huc : ∀ b ∈ c::a::as, b.val ≤ 1 := by
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hea.le.trans (hu a (List.mem_cons_self))
      · exact hu b hb
    have hh := J.cumulativeClock_uniform D hD (c::a::as) hq hr hql hrl
      (by simpa only [List.length_cons,Nat.add_sub_cancel] using hend) hM hoc huc
      (fun i hi => hm i (by simpa only [List.length_cons,Nat.lt_add_one_iff] using hi)) x
    exact hh

end SKFluctuations.Hierarchy

end

end OAI
