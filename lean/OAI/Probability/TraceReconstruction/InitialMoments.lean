import OAI.Probability.TraceReconstruction.Patterns

namespace OAI

/-!
# InitialMoments

Initial coefficient tails, primitive conditioning, mark-list oracle densities, pure norm estimates, and moment energies.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem signedPeriodDefects_comp {u m r : ℕ} (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (s : ℕ) (X : ℤ) (τ : ℝ) (j : IncreasingTuple u r) :
    signedPeriodDefects off hsafe s X τ ∘ j.val =
      shiftedTag (periodSlot (fun _ => off) ∘ j.val) (hsafe.comp j.val j.property)
        (fun i => motifShift (motifIndicator s ((j.val i).val-X))
          ((prouhetSeries s).coeff ((j.val i).val-X)) τ) := by
  funext i; apply Fin.ext; rfl

def signedTupleKernel {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (j : IncreasingTuple u r) (v : IncreasingTuple l r) : ℝ :=
  ∑X∈π.coeff.support, π.coeff X*
    (subsetRankKernel hl (signedPeriodDefects off hsafe s X 1 ∘ j.val) v.val -
     subsetRankKernel hl (signedPeriodDefects off hsafe s X (-1) ∘ j.val) v.val)

theorem signedRankCoefficient_tuple_sum {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off))) (π : IntSeries) (s : ℕ)
    (v : IncreasingTuple l r) :
    signedRankCoefficient hl off hsafe π s v=∑j, signedTupleKernel hl off hsafe π s j v := by
  unfold signedRankCoefficient signedTupleKernel
  simp_rw [rankDefectCoefficient_eq _ _ (signedPeriodDefects_strictMono _ _ _ _ _),
    ← Finset.sum_sub_distrib,Finset.mul_sum]
  exact Finset.sum_comm

theorem signedTupleKernel_expansion {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off))) (π : IntSeries) (s : ℕ)
    (j : IncreasingTuple u r) (v : IncreasingTuple l r) :
    signedTupleKernel hl off hsafe π s j v = ∑k : Fin r → GapDifference,
      if Odd (firstDifferenceCount k) then
        2*motifPatternMultiplier π s (fun i => (j.val i).val) k *
          positionalRankDifference hl (periodSlot (fun _ => off) ∘ j.val)
            (hsafe.comp j.val j.property) k v else 0 := by
  unfold signedTupleKernel
  simp_rw [signedPeriodDefects_comp]
  have H := mixed_signed_shift_expansion π s (fun i => (j.val i).val)
    (fun a => subsetRankKernel hl
      (shiftedTag (periodSlot (fun _ => off) ∘ j.val) (hsafe.comp j.val j.property) a) v.val)
  simpa only [ite_mul,zero_mul,positionalRankDifference] using H

def clippedSignedRankCoefficient {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (θ : ℝ) (v : IncreasingTuple l r) : ℝ :=
  ∑j, if PeriodRankRegion m θ j v then signedTupleKernel hl off hsafe π s j v else 0

def clippedPatternCoefficient {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (θ : ℝ) (k : Fin r → GapDifference) (v : IncreasingTuple l r) : ℝ :=
  ∑j, if PeriodRankRegion m θ j v then
    motifPatternMultiplier π s (fun i => (j.val i).val) k *
      positionalRankDifference hl (periodSlot (fun _ => off) ∘ j.val)
        (hsafe.comp j.val j.property) k v else 0

theorem clippedSignedRankCoefficient_expansion {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (θ : ℝ) (v : IncreasingTuple l r) :
    clippedSignedRankCoefficient hl off hsafe π s θ v =
      2*∑k : Fin r → GapDifference, if Odd (firstDifferenceCount k) then
        clippedPatternCoefficient hl off hsafe π s θ k v else 0 := by
  unfold clippedSignedRankCoefficient clippedPatternCoefficient
  have he (j : IncreasingTuple u r) :
      (if PeriodRankRegion m θ j v then signedTupleKernel hl off hsafe π s j v else 0) =
      ∑k : Fin r → GapDifference, if Odd (firstDifferenceCount k) then
        (if PeriodRankRegion m θ j v then
          2*motifPatternMultiplier π s (fun i => (j.val i).val) k *
            positionalRankDifference hl (periodSlot (fun _ => off) ∘ j.val)
              (hsafe.comp j.val j.property) k v else 0) else 0 := by
    by_cases hv : PeriodRankRegion m θ j v
    · simp only [ite_eq_left hv, signedTupleKernel_expansion]
    · simp [hv]
  simp_rw [he]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : Odd (firstDifferenceCount k)
  · simp only [ite_eq_left hk,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  · simp [hk]

/-- Removing coarse rank rectangles loses an explicitly exponentially
 small amount in the actual coefficient, before any finite differences. -/
theorem signedTupleKernel_tail {u m l r : ℕ}
    (hu : 0 < u) (hm : 128 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin m) (hoff : |(off.val:ℝ)-(m:ℝ)/2|≤3)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0≤π.coeff X) (hπsum : ∑X∈π.coeff.support, π.coeff X=1)
    (s : ℕ) (j : IncreasingTuple u r) {θ : ℝ} (hθ : θ∈Set.Ioo 0 1) :
    (∑v : IncreasingTuple l r, if PeriodRankRegion m θ j v then 0 else
      |signedTupleKernel hl off hsafe π s j v|) ≤
      2*(((r+1:ℕ):ℝ)*θ^r/binomialMass (u*m) θ l * (2*Real.exp (-(m:ℝ)/(1024*u)))) := by
  let K (X : ℤ) (τ : ℝ) (v : IncreasingTuple l r) :=
    subsetRankKernel hl (signedPeriodDefects off hsafe s X τ ∘ j.val) v.val
  let B := ((r+1:ℕ):ℝ)*θ^r/binomialMass (u*m) θ l * (2*Real.exp (-(m:ℝ)/(1024*u)))
  have hK (X : ℤ) (τ : ℝ) : (∑v : IncreasingTuple l r,
      if PeriodRankRegion m θ j v then 0 else K X τ v)≤B := by
    simp_rw [K,signedPeriodDefects_comp]
    exact period_shifted_outside_region hu hm hr hl (fun _ => off) (fun _ => hoff)
      (by intro _ _; simp) j (hsafe.comp j.val j.property) _ hθ
  have hnon (X : ℤ) (τ : ℝ) (v : IncreasingTuple l r) : 0≤K X τ v :=
    subsetRankKernel_nonneg _ _ _
  calc
    _ ≤ ∑v : IncreasingTuple l r, ∑X∈π.coeff.support, π.coeff X*
        (if PeriodRankRegion m θ j v then 0 else K X 1 v+K X (-1) v) := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : PeriodRankRegion m θ j v
      · simp [hv]
      · simp only [ite_eq_right hv]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        apply Finset.sum_le_sum
        intro X _
        rw [abs_mul,abs_of_nonneg (hπ X)]
        apply mul_le_mul_of_nonneg_left _ (hπ X)
        exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (hnon X 1 v),abs_of_nonneg (hnon X (-1) v)])
    _ = ∑X∈π.coeff.support, π.coeff X*((∑v : IncreasingTuple l r,
        if PeriodRankRegion m θ j v then 0 else K X 1 v)+
        (∑v : IncreasingTuple l r, if PeriodRankRegion m θ j v then 0 else K X (-1) v)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro X _
      rw [← Finset.mul_sum,← Finset.sum_add_distrib]
      congr 1; apply Finset.sum_congr rfl
      intro v _; split_ifs <;> ring
    _ ≤ ∑X∈π.coeff.support, π.coeff X*(B+B) := by
      apply Finset.sum_le_sum
      intro X _
      exact mul_le_mul_of_nonneg_left (add_le_add (hK X 1) (hK X (-1))) (hπ X)
    _ = _ := by rw [← Finset.sum_mul,hπsum]; dsimp [B]; ring

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem motif_pattern_common_short_gap {r : ℕ} (k : Fin r → GapDifference)
    (hk : Odd (firstDifferenceCount k)) (hnl : ¬∃a, k=linearPattern a) :
    ∃ a : Fin r, k a≠.unchanged ∧ ∃c : Fin (r+1), ∀ {u s : ℕ} (π : IntSeries)
      (j : IncreasingTuple u r),
      motifPatternMultiplier π s (fun h => (j.val h).val) k≠0 →
        coarsePeriodGap j.val c ≤ 2*(2^s) := by
  obtain ⟨a,b,hab,ha,hb⟩ := odd_pattern_pair k hk hnl
  cases r with
  | zero => exact Fin.elim0 a
  | succ r =>
    have har : a.val < r := by have := b.isLt; exact lt_of_lt_of_le hab (Nat.le_of_lt_succ b.isLt)
    let i : Fin r := ⟨a.val,har⟩
    have hi : i.castSucc=a := by ext; rfl
    refine ⟨a,ha,i.castSucc.succ,?_⟩
    intro u s π j hj
    apply motif_pattern_bounded_gap π s j k i b
    · simpa only [hi] using hab
    · simpa only [hi] using ha
    · exact hb
    · exact hj

theorem clipped_linear_pattern_norm {u m l r : ℕ}
    (hm : 32 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (hcentral : CentralMotifSupport u s π)
    {θ : ℝ} (hθ : θ∈Set.Ioo 0 1) (hhalf : 1/2 ≤ θ)
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ)) (a : Fin r) :
    (∑v, (clippedPatternCoefficient hl off hsafe π s θ (linearPattern a) v)^2)  ≤ 
      periodDifferencePrefactor u m r 1 θ * periodCentralSumConstant u r *
        seriesL2Sq (prouhetSeries s*π) := by
  have hb := period_pattern_norm hm hr hl (fun _ => off) (fun _ => hoff)
    (by intro _ _; simp) (fun j => hsafe.comp j.val j.property) (linearPattern a)
    hθ hhalf hmean hv a
    (fun j => motifPatternMultiplier π s (fun i => (j.val i).val) (linearPattern a))
    (fun h => (prouhetSeries s*π).coeff h.val)
    (by intro j; rw [motif_linear_multiplier])
    (prouhet_convolution_central π hcentral)
  rw [linearPattern_order] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left
    (seriesL2Sq_partial _ (fun h : Fin u => (h.val:ℤ)) (by intro a b h; apply Fin.ext; change (a.val:ℤ)=b.val at h; exact_mod_cast h))
  unfold periodDifferencePrefactor lengthDifferenceConstant periodCentralSumConstant
  positivity

theorem clipped_nonlinear_pattern_norm {u m l r : ℕ}
    (hm : 32 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (s : ℕ) (hcentral : CentralMotifSupport u s π)
    {θ : ℝ} (hθ : θ∈Set.Ioo 0 1) (hhalf : 1/2 ≤ θ)
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (k : Fin r → GapDifference) (hk : Odd (firstDifferenceCount k)) (hnl : ¬∃a, k=linearPattern a)
    (hM : ((2*(2^s):ℕ):ℝ) < (u:ℝ)/(3*(r+1:ℝ))) :
    (∑v, (clippedPatternCoefficient hl off hsafe π s θ k v)^2)  ≤ 
      periodDifferencePrefactor u m r (∑h, (k h).order) θ *
        periodBoundedSumConstant u r (2*(2^s)) * seriesL2Sq (geomSeries (2^s)*π) := by
  obtain ⟨a,ha,c,hc⟩ := motif_pattern_common_short_gap k hk hnl
  have hb := period_pattern_bounded_norm hm hr hl (fun _ => off) (fun _ => hoff)
    (by intro _ _; simp) (fun j => hsafe.comp j.val j.property) k
    hθ hhalf hmean hv a c
    (fun j => motifPatternMultiplier π s (fun i => (j.val i).val) k)
    (fun h => (geomSeries (2^s)*π).coeff h.val)
    (fun j => motifPatternMultiplier_sq_le π hπ s _ k a ha)
    (fun j hj => hc π j hj) (unsigned_convolution_central π hcentral) hM
  apply hb.trans
  apply mul_le_mul_of_nonneg_left
    (seriesL2Sq_partial _ (fun h : Fin u => (h.val:ℤ)) (by intro a b h; apply Fin.ext; change (a.val:ℤ)=b.val at h; exact_mod_cast h))
  unfold periodDifferencePrefactor lengthDifferenceConstant periodBoundedSumConstant
  positivity

def signedPatternBound (u m r s : ℕ) (π : IntSeries) (θ : ℝ)
    (k : Fin r → GapDifference) : ℝ :=
  if ∃a, k=linearPattern a then
    periodDifferencePrefactor u m r 1 θ * periodCentralSumConstant u r * seriesL2Sq (prouhetSeries s*π)
  else periodDifferencePrefactor u m r (∑h, (k h).order) θ *
    periodBoundedSumConstant u r (2*(2^s)) * seriesL2Sq (geomSeries (2^s)*π)

theorem sum_square_card_bound {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    (∑ b, (∑a, f a b)^2)  ≤  (Fintype.card α:ℝ)*∑a, ∑b, f a b^2 := by
  calc
    _  ≤  ∑b, (Fintype.card α:ℝ)*∑a, f a b^2 := by
      apply Finset.sum_le_sum
      intro b _
      have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
        (r := fun a => f a b) (f := fun _ => (1:ℝ)) (g := fun a => f a b^2)
        (by intro _ _; norm_num) (by intro _ _; positivity) (by intro _ _; simp)
      simpa using h
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_comm]

theorem clipped_signed_initial_norm {u m l r : ℕ}
    (hm : 32 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (s : ℕ) (hcentral : CentralMotifSupport u s π)
    {θ : ℝ} (hθ : θ∈Set.Ioo 0 1) (hhalf : 1/2 ≤ θ)
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hM : ((2*(2^s):ℕ):ℝ) < (u:ℝ)/(3*(r+1:ℝ))) :
    (∑v : IncreasingTuple l r, (clippedSignedRankCoefficient hl off hsafe π s θ v)^2)  ≤ 
      4*(Fintype.card (Fin r → GapDifference):ℝ)*
        ∑k : Fin r → GapDifference, if Odd (firstDifferenceCount k) then
          signedPatternBound u m r s π θ k else 0 := by
  simp_rw [clippedSignedRankCoefficient_expansion,mul_pow,show (2:ℝ)^2=4 by norm_num]
  rw [← Finset.mul_sum]
  calc
    _  ≤  4*((Fintype.card (Fin r → GapDifference):ℝ)*∑k : Fin r → GapDifference, ∑v : IncreasingTuple l r,
        (if Odd (firstDifferenceCount k) then clippedPatternCoefficient hl off hsafe π s θ k v else 0)^2) := by
      exact mul_le_mul_of_nonneg_left (sum_square_card_bound (fun (k : Fin r → GapDifference) (v : IncreasingTuple l r) =>
        if Odd (firstDifferenceCount k) then clippedPatternCoefficient hl off hsafe π s θ k v else 0)) (by norm_num)
    _  ≤  _ := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : Odd (firstDifferenceCount k)
      · simp only [ite_eq_left hk]
        unfold signedPatternBound
        split_ifs with hlin
        · obtain ⟨a,rfl⟩ := hlin
          exact clipped_linear_pattern_norm hm hr hl off hoff hsafe π s hcentral hθ hhalf hmean hv a
        · exact clipped_nonlinear_pattern_norm hm hr hl off hoff hsafe π hπ s hcentral
            hθ hhalf hmean hv k hk hlin hM
      · simp [hk]

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem signedRankCoefficient_tail {u m l r : ℕ}
    (hu : 0 < u) (hm : 128 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support, π.coeff X=1)
    (s : ℕ) {θ : ℝ} (hθ : θ∈Set.Ioo 0 1) :
    (∑v : IncreasingTuple l r, |signedRankCoefficient hl off hsafe π s v-
        clippedSignedRankCoefficient hl off hsafe π s θ v|) ≤
      (Fintype.card (IncreasingTuple u r):ℝ)*
      (2*(((r+1:ℕ):ℝ)*θ^r/binomialMass (u*m) θ l * (2*Real.exp (-(m:ℝ)/(1024*u))))) := by
  simp_rw [signedRankCoefficient_tuple_sum,clippedSignedRankCoefficient,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑v : IncreasingTuple l r, ∑j : IncreasingTuple u r,
        if PeriodRankRegion m θ j v then 0 else |signedTupleKernel hl off hsafe π s j v| := by
      apply Finset.sum_le_sum
      intro v _
      refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    _ = ∑j : IncreasingTuple u r, ∑v : IncreasingTuple l r,
        if PeriodRankRegion m θ j v then 0 else |signedTupleKernel hl off hsafe π s j v| := Finset.sum_comm
    _ ≤ _ := by
      calc
        _ ≤ ∑j : IncreasingTuple u r,
            2*(((r+1:ℕ):ℝ)*θ^r/binomialMass (u*m) θ l * (2*Real.exp (-(m:ℝ)/(1024*u)))) :=
          Finset.sum_le_sum (fun j _ => signedTupleKernel_tail hu hm hr hl off hoff hsafe π hπ hπsum s j hθ)
        _ = _ := by simp

/-- A globally discarded l1 tail is also negligible in coefficient energy.
 This does not assume pointwise cancellation on the discarded ranks. -/
theorem finite_sum_sq_le_abs_sum_sq {α : Type*} [Fintype α] (f : α → ℝ) :
    (∑a, f a^2) ≤ (∑a, |f a|)^2 := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun a => |f a|)
    (by intro a _; exact abs_nonneg _)
  simpa only [sq_abs] using h

theorem initial_signed_energy {u m l r : ℕ}
    (hu : 0 < u) (hm : 128 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support, π.coeff X=1)
    (s : ℕ) (hcentral : CentralMotifSupport u s π)
    {θ : ℝ} (hθ : θ∈Set.Ioo 0 1) (hhalf : 1/2 ≤ θ)
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hM : ((2*(2^s):ℕ):ℝ) < (u:ℝ)/(3*(r+1:ℝ))) :
    (∑v : IncreasingTuple l r, (signedRankCoefficient hl off hsafe π s v)^2) ≤
      8*(Fintype.card (Fin r → GapDifference):ℝ)*
        (∑k : Fin r → GapDifference, if Odd (firstDifferenceCount k) then
          signedPatternBound u m r s π θ k else 0) +
      2*((Fintype.card (IncreasingTuple u r):ℝ)*
        (2*(((r+1:ℕ):ℝ)*θ^r/binomialMass (u*m) θ l * (2*Real.exp (-(m:ℝ)/(1024*u))))))^2 := by
  let A : IncreasingTuple l r → ℝ := signedRankCoefficient hl off hsafe π s
  let C : IncreasingTuple l r → ℝ := clippedSignedRankCoefficient hl off hsafe π s θ
  have hn := clipped_signed_initial_norm (by omega) hr hl off hoff hsafe π hπ s hcentral hθ hhalf hmean hv hM
  have ht := signedRankCoefficient_tail hu hm hr hl off hoff hsafe π hπ hπsum s hθ
  have hE := (finite_sum_sq_le_abs_sum_sq (fun v : IncreasingTuple l r => A v-C v)).trans
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun v _ => abs_nonneg (A v-C v))) ht 2)
  have hsum : (∑v : IncreasingTuple l r, A v^2) ≤
      2*(∑v : IncreasingTuple l r, C v^2)+2*(∑v : IncreasingTuple l r, (A v-C v)^2) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro v _
    nlinarith [sq_nonneg (A v-2*C v)]
  calc
    _ ≤ 2*(∑v : IncreasingTuple l r, C v^2)+2*(∑v : IncreasingTuple l r, (A v-C v)^2) := hsum
    _ ≤ _ := by dsimp [C] at *; linarith

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Exact complete-trace expectation, recursively on the actual binary word. -/
def listDeletionExpectation (q : ℝ) : List Bool → (List Bool → ℝ) → ℝ
  | [], F => F []
  | b::w, F => q*listDeletionExpectation q w F +
      (1-q)*listDeletionExpectation q w (fun t => F (b::t))

theorem traceOfMask_cons {n : ℕ} (x : Word (n+1)) (b : Bool) (a : Mask n) :
    traceOfMask x (Fin.cons b a)=
      if b then x 0::traceOfMask (fun i => x i.succ) a
      else traceOfMask (fun i => x i.succ) a := by
  rw [trace_filterMap,List.ofFn_succ,trace_filterMap]
  cases b <;> simp

theorem maskWeight_cons {n : ℕ} (q : ℝ) (b : Bool) (a : Mask n) :
    maskWeight q (Fin.cons b a)=(if b then 1-q else q)*maskWeight q a := by
  simp [maskWeight,Fin.prod_univ_succ]

theorem listDeletionExpectation_ofFn {n : ℕ} (q : ℝ) (x : Word n) (F : List Bool → ℝ) :
    listDeletionExpectation q (List.ofFn x) F =
      ∑a : Mask n, maskWeight q a*F (traceOfMask x a) := by
  induction n generalizing F with
  | zero => simp [listDeletionExpectation,maskWeight,traceOfMask]
  | succ n ih =>
    rw [List.ofFn_succ,listDeletionExpectation,ih,ih]
    symm
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp,Fintype.sum_prod_type]
    change (∑b : Bool, ∑a : Mask n, maskWeight q (Fin.cons b a)*F (traceOfMask x (Fin.cons b a)))=_
    simp_rw [maskWeight_cons,traceOfMask_cons]
    simp only [Bool.false_eq_true,ite_false,ite_true,Fintype.sum_bool]
    simp only [mul_assoc,← Finset.mul_sum]
    ring

theorem listDeletionExpectation_append (q : ℝ) (x y : List Bool) (F : List Bool → ℝ) :
    listDeletionExpectation q (x++y) F =
      listDeletionExpectation q x (fun t => listDeletionExpectation q y (fun u => F (t++u))) := by
  induction x generalizing F with
  | nil => simp [listDeletionExpectation]
  | cons b x ih => simp only [List.cons_append,listDeletionExpectation,ih]

/-- The primitive alphabet consists of the literal strings 01 and 1. -/
def primitiveBlock (b : Bool) : List Bool := if b then [true] else [false,true]

theorem primitiveBlock_expectation (q : ℝ) (b : Bool) (F : List Bool → ℝ) :
    listDeletionExpectation q (primitiveBlock b) F =
      ∑z : PrimitiveMark, (if b then defectPrimitiveMass q z else ordinaryPrimitiveMass q z)*F (primitiveOutput z) := by
  cases b <;> simp [primitiveBlock,listDeletionExpectation,primitiveOutput,
    defectPrimitiveMass,ordinaryPrimitiveMass,Fin.sum_univ_succ]
  ring

theorem primitiveBlock_erasure_expectation {q : ℝ} (hq : q∈Set.Ioo 0 1)
    (b : Bool) (F : List Bool → ℝ) :
    listDeletionExpectation q (primitiveBlock b) F =
      primitiveErasure q * F []+(1-primitiveErasure q)*
        (primitiveMarkLaw q hq b).expect (fun z => F (primitiveOutput z)) := by
  rw [primitiveBlock_expectation]
  simp_rw [← primitiveMark_simulation hq]
  simp only [add_mul,Finset.sum_add_distrib]
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    primitiveOutput,Matrix.cons_val_zero]
  simp only [FiniteLaw.expect,primitiveMarkLaw,mul_assoc,← Finset.mul_sum]

/-- Independent silent block erasures and conditionally emitted primitive marks.
 An emitted empty mark is retained in the list and differs from a silent erasure. -/
def silentMarkExpectation (q : ℝ) : List Bool → (List PrimitiveMark → ℝ) → ℝ
  | [], F => F []
  | b::bs, F => primitiveErasure q*silentMarkExpectation q bs F +
      (1-primitiveErasure q)*∑z : PrimitiveMark, primitiveMarkMass q b z*
        silentMarkExpectation q bs (fun ys => F (z::ys))

def joinPrimitiveMarks (ys : List PrimitiveMark) : List Bool := (ys.map primitiveOutput).flatten

theorem silentMarkExpectation_linear (q : ℝ) (bs : List Bool)
    (F G : List PrimitiveMark → ℝ) (a b : ℝ) :
    silentMarkExpectation q bs (fun ys => a*F ys+b*G ys)=
      a*silentMarkExpectation q bs F+b*silentMarkExpectation q bs G := by
  induction bs generalizing F G with
  | nil => rfl
  | cons x xs ih =>
    simp only [silentMarkExpectation,ih,mul_add,Finset.sum_add_distrib]
    have hf : (∑ z : PrimitiveMark, primitiveMarkMass q x z *
        (a*silentMarkExpectation q xs (fun ys => F (z::ys)))) =
        a*∑ z : PrimitiveMark, primitiveMarkMass q x z * silentMarkExpectation q xs (fun ys => F (z::ys)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
    have hg : (∑ z : PrimitiveMark, primitiveMarkMass q x z *
        (b*silentMarkExpectation q xs (fun ys => G (z::ys)))) =
        b*∑ z : PrimitiveMark, primitiveMarkMass q x z * silentMarkExpectation q xs (fun ys => G (z::ys)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
    rw [hf,hg]; ring

theorem silentMarkExpectation_sum {ι : Type*} [Fintype ι] (q : ℝ) (bs : List Bool)
    (F : ι → List PrimitiveMark → ℝ) :
    silentMarkExpectation q bs (fun ys => ∑i, F i ys)=∑i, silentMarkExpectation q bs (F i) := by
  induction bs generalizing F with
  | nil => rfl
  | cons x xs ih =>
    simp only [silentMarkExpectation,ih,Finset.mul_sum,Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]

theorem silentMarkExpectation_scale (q : ℝ) (bs : List Bool)
    (F : List PrimitiveMark → ℝ) (a : ℝ) :
    silentMarkExpectation q bs (fun ys => a*F ys)=a*silentMarkExpectation q bs F := by
  have h := silentMarkExpectation_linear q bs F F a 0
  simpa using h

/-- The common deterministic mark-joining simulator is exact for arbitrary
 concatenations of primitive blocks; block boundaries are not reported. -/
theorem primitive_run_simulation {q : ℝ} (hq : q∈Set.Ioo 0 1)
    (bs : List Bool) (F : List Bool → ℝ) :
    listDeletionExpectation q ((bs.map primitiveBlock).flatten) F =
      silentMarkExpectation q bs (fun ys => F (joinPrimitiveMarks ys)) := by
  induction bs generalizing F with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons,List.flatten_cons]
    rw [listDeletionExpectation_append,primitiveBlock_erasure_expectation hq]
    simp only [List.nil_append,ih,FiniteLaw.expect,primitiveMarkLaw]
    simp only [silentMarkExpectation]
    rfl

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Every emitted mark is counted, including the empty primitive output. -/
def emittedMarkExpectation (q : ℝ) : List Bool → (List PrimitiveMark → ℝ) → ℝ
  | [], F => F []
  | b::bs, F => ∑z : PrimitiveMark, primitiveMarkMass q b z*
      emittedMarkExpectation q bs (fun ys => F (z::ys))

theorem emittedMarkExpectation_ofFn {n : ℕ} (q : ℝ) (θ : Fin n → Bool)
    (F : List PrimitiveMark → ℝ) :
    emittedMarkExpectation q (List.ofFn θ) F=
      ∑x : Fin n → PrimitiveMark, (∏i, primitiveMarkMass q (θ i) (x i))*F (List.ofFn x) := by
  induction n generalizing F with
  | zero => simp [emittedMarkExpectation]
  | succ n ih =>
    rw [List.ofFn_succ,emittedMarkExpectation]
    simp_rw [ih,Finset.mul_sum]
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => PrimitiveMark)).sum_comp,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro x _
    simp [Fin.consEquiv,Fin.prod_univ_succ,List.ofFn_succ,mul_assoc]

/-- Conditioning the independent erasures on the return count chooses
 a uniformly random subset of the original block slots. -/
theorem silentMarkExpectation_mask_mixture {n : ℕ} (q : ℝ) (θ : Fin n → Bool)
    (F : List PrimitiveMark → ℝ) :
    silentMarkExpectation q (List.ofFn θ) F=
      ∑a : Mask n, maskWeight (primitiveErasure q) a*
        emittedMarkExpectation q (traceOfMask θ a) F := by
  induction n generalizing F with
  | zero => simp [silentMarkExpectation,emittedMarkExpectation,maskWeight,traceOfMask]
  | succ n ih =>
    rw [List.ofFn_succ,silentMarkExpectation]
    simp_rw [ih]
    symm
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp,Fintype.sum_prod_type]
    change (∑b : Bool, ∑a : Mask n, maskWeight (primitiveErasure q) (Fin.cons b a)*
      emittedMarkExpectation q (traceOfMask θ (Fin.cons b a)) F)=_
    simp_rw [maskWeight_cons,traceOfMask_cons]
    simp only [Fintype.sum_bool,ite_true,Bool.false_eq_true,ite_false,emittedMarkExpectation]
    simp_rw [mul_assoc,Finset.mul_sum]
    rw [Finset.sum_comm,add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro a _
    ring

def maskSubset {n : ℕ} (a : Mask n) : Finset (Fin n) := Finset.univ.filter fun i => a i

def maskSubsetEquiv (n : ℕ) : Mask n ≃ Finset (Fin n) where
  toFun := maskSubset
  invFun S i := decide (i∈S)
  left_inv a := by funext i; simp [maskSubset]
  right_inv S := by ext i; simp [maskSubset]

theorem maskWeight_card {n : ℕ} (q : ℝ) (a : Mask n) :
    maskWeight q a = (1-q)^(maskSubset a).card*q^(n-(maskSubset a).card) := by
  unfold maskWeight maskSubset
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  congr 1
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (p := fun i => a i)
  rw [Finset.card_univ,Fintype.card_fin] at h
  rw [show (Finset.univ.filter fun i : Fin n => ¬a i=true).card=
      n-(Finset.univ.filter fun i : Fin n => a i=true).card by omega]

theorem slotAtRank_ofFn {n l : ℕ} (S : FixedSubset (Fin n) l) :
    List.ofFn (slotAtRank S)=S.val.sort := by
  apply List.ext_getElem
  · simp [S.property]
  · intro i hi hj
    simp only [List.getElem_ofFn]
    rfl

theorem filtered_finRange_eq_sort {n : ℕ} (S : Finset (Fin n)) :
    ((List.finRange n).filter fun i => decide (i∈S))=S.sort := by
  apply ((List.sortedLT_finRange n).pairwise.filter _).eq_of_mem_iff S.sortedLT_sort.pairwise
  intro a
  simp

theorem selected_types_ofFn {n l : ℕ} (θ : Fin n → Bool) (S : FixedSubset (Fin n) l) :
    traceOfMask θ (fun i => decide (i∈S.val))=List.ofFn (fun v => θ (slotAtRank S v)) := by
  rw [traceOfMask,filtered_finRange_eq_sort,← slotAtRank_ofFn S,List.map_ofFn]
  rfl

theorem silentMarkExpectation_subset_mixture {n : ℕ} (q : ℝ) (θ : Fin n → Bool)
    (F : List PrimitiveMark → ℝ) :
    silentMarkExpectation q (List.ofFn θ) F=
      ∑S : Finset (Fin n), subsetWeight (1-primitiveErasure q) S*
        emittedMarkExpectation q (traceOfMask θ (fun i => decide (i∈S))) F := by
  rw [silentMarkExpectation_mask_mixture,← (maskSubsetEquiv n).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro S _
  rw [maskWeight_card]
  change (1-primitiveErasure q)^(maskSubsetEquiv n ((maskSubsetEquiv n).symm S)).card *
      (primitiveErasure q)^(n-(maskSubsetEquiv n ((maskSubsetEquiv n).symm S)).card)*
      emittedMarkExpectation q (traceOfMask θ (fun i => decide (i∈S))) F=_
  rw [Equiv.apply_symm_apply]
  simp [subsetWeight]

def cardinalSubsetEquiv (n : ℕ) : Finset (Fin n) ≃ Σl : Fin (n+1), FixedSubset (Fin n) l.val where
  toFun S := ⟨⟨S.card, by have := Finset.card_le_univ S; simpa using Nat.lt_succ_of_le this⟩,⟨S,rfl⟩⟩
  invFun x := x.2.val
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨⟨l,hl⟩,⟨S,hS⟩⟩
    dsimp
    change S.card=l at hS
    subst l
    rfl

theorem subsetWeight_count_factor {n l : ℕ} (hl : l ≤ n) (p : ℝ) (S : FixedSubset (Fin n) l) :
    subsetWeight p S.val=binomialMass n p l*(uniformSubsetLaw l (by simpa using hl)).mass S := by
  have hc : (n.choose l:ℝ)≠0 := by exact_mod_cast (Nat.choose_pos hl).ne'
  simp only [subsetWeight,binomialMass,uniformSubsetLaw,S.property,Fintype.card_fin]
  field_simp

/-- The literal conditional-list oracle used by the rank coefficients. -/
def conditionalPrimitiveLaw {n l : ℕ} (hl : l ≤ n) (q : ℝ) (hq : q∈Set.Ioo 0 1)
    (θ : Fin n → Bool) : FiniteLaw (Fin l → PrimitiveMark) :=
  (uniformSubsetLaw l (by simpa using hl)).mixture fun S =>
    FiniteLaw.coordinateProduct (fun v => primitiveMarkLaw q hq (θ (slotAtRank S v)))

theorem silentMarkExpectation_count_mixture {n : ℕ} (q : ℝ) (hq : q∈Set.Ioo 0 1)
    (θ : Fin n → Bool) (F : List PrimitiveMark → ℝ) :
    silentMarkExpectation q (List.ofFn θ) F=
      ∑l : Fin (n+1), binomialMass n (1-primitiveErasure q) l.val*
        (conditionalPrimitiveLaw (Nat.le_of_lt_succ l.isLt) q hq θ).expect (fun x => F (List.ofFn x)) := by
  rw [silentMarkExpectation_subset_mixture,← (cardinalSubsetEquiv n).symm.sum_comp,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro l _
  change (∑S : FixedSubset (Fin n) l.val, subsetWeight (1-primitiveErasure q) S.val*
      emittedMarkExpectation q (traceOfMask θ (fun i => decide (i∈S.val))) F)=_
  calc
    _ = ∑S : FixedSubset (Fin n) l.val, binomialMass n (1-primitiveErasure q) l.val*
        (uniformSubsetLaw l.val (by simpa using Nat.le_of_lt_succ l.isLt)).mass S*
        (∑x : Fin l.val → PrimitiveMark, (∏v, primitiveMarkMass q (θ (slotAtRank S v)) (x v))*F (List.ofFn x)) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [subsetWeight_count_factor (Nat.le_of_lt_succ l.isLt),selected_types_ofFn θ S,emittedMarkExpectation_ofFn]
    _ = _ := by
      unfold conditionalPrimitiveLaw FiniteLaw.expect FiniteLaw.mixture FiniteLaw.coordinateProduct primitiveMarkLaw
      simp_rw [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro S _
      ring

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Density of the actual uniform-subset primitive oracle, over the ordinary
 mark product law. This is exactly the channel defined by silent erasures. -/
theorem conditionalPrimitiveLaw_density {n l : ℕ} (hl : l ≤ n)
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (θ : Fin n → Bool) (x : Fin l → PrimitiveMark) :
    (conditionalPrimitiveLaw hl q hq θ).mass x =
      ((primitiveMarkLaw q hq false).product l).mass x *
        averagedDensity (uniformSubsetLaw l (by simpa using hl))
          (fun S v => θ (slotAtRank S v)) (primitiveScore q) x := by
  have he : (fun S : FixedSubset (Fin n) l =>
      FiniteLaw.coordinateProduct (fun v => primitiveMarkLaw q hq (θ (slotAtRank S v)))) =
      (fun S : FixedSubset (Fin n) l =>
      FiniteLaw.coordinateProduct (fun v => if θ (slotAtRank S v) then
        primitiveMarkLaw q hq true else primitiveMarkLaw q hq false)) := by
    funext S
    congr 1
    funext v
    cases θ (slotAtRank S v) <;> rfl
  unfold conditionalPrimitiveLaw
  rw [he]
  exact leaf_oracle_density (primitiveMarkLaw q hq false) (primitiveMarkLaw q hq true)
    (primitiveScore q) (primitive_score_identity hq)
    (uniformSubsetLaw l (by simpa using hl)) (fun S v => θ (slotAtRank S v)) x

def defectTypes {n u : ℕ} (d : Fin u → Fin n) (i : Fin n) : Bool := decide (i∈Set.range d)

theorem defectTypes_atRank {n l u : ℕ} (d : Fin u → Fin n) (S : FixedSubset (Fin n) l) :
    (fun v => defectTypes d (slotAtRank S v))=defectAtRank (Finset.univ.image d) S := by
  funext v
  simp [defectTypes,defectAtRank,Set.mem_range]

theorem conditionalDefectLaw_density {n l u : ℕ} (hl : l ≤ n)
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (d : Fin u → Fin n) (x : Fin l → PrimitiveMark) :
    (conditionalPrimitiveLaw hl q hq (defectTypes d)).mass x =
      ((primitiveMarkLaw q hq false).product l).mass x *
        multilinear (averagedCoefficient (uniformSubsetLaw l (by simpa using hl))
          (defectAtRank (Finset.univ.image d))) (primitiveScore q) x := by
  rw [conditionalPrimitiveLaw_density,show (fun S v => defectTypes d (slotAtRank S v))=
      defectAtRank (Finset.univ.image d) by funext S; exact defectTypes_atRank d S,
      averagedDensity_expansion]

/-- The finite-support law of the hidden motif anchor, not an additional
 distributional assumption or a changed channel parameter. -/
def seriesProbabilityLaw (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X)
    (hπsum : ∑X∈π.coeff.support, π.coeff X=1) : FiniteLaw ↥π.coeff.support where
  mass X := π.coeff X.val
  nonneg X := hπ X.val
  total := by simpa only [Finset.univ_eq_attach,Finset.sum_attach] using hπsum

def mixedMotifCoefficient {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (τ : ℝ) (σ : Fin l → Bool) : ℝ :=
  ∑X∈π.coeff.support, π.coeff X*
    averagedCoefficient (uniformSubsetLaw l (by simpa using hl))
      (defectAtRank (Finset.univ.image (signedPeriodDefects off hsafe s X τ))) σ

def conditionalMotifLaw {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X)
    (hπsum : ∑X∈π.coeff.support, π.coeff X=1) (s : ℕ) (τ : ℝ) :
    FiniteLaw (Fin l → PrimitiveMark) :=
  (seriesProbabilityLaw π hπ hπsum).mixture fun X =>
    conditionalPrimitiveLaw hl q hq (defectTypes (signedPeriodDefects off hsafe s X.val τ))

theorem conditionalMotifLaw_density {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    {q : ℝ} (hq : q∈Set.Ioo 0 1) (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X)
    (hπsum : ∑X∈π.coeff.support, π.coeff X=1) (s : ℕ) (τ : ℝ) (x : Fin l → PrimitiveMark) :
    (conditionalMotifLaw hl off hsafe hq π hπ hπsum s τ).mass x=
      ((primitiveMarkLaw q hq false).product l).mass x *
        multilinear (mixedMotifCoefficient hl off hsafe π s τ) (primitiveScore q) x := by
  unfold conditionalMotifLaw FiniteLaw.mixture seriesProbabilityLaw
  simp_rw [conditionalDefectLaw_density]
  let F : ℤ → ℝ := fun X => π.coeff X *
    (((primitiveMarkLaw q hq false).product l).mass x *
      multilinear (averagedCoefficient (uniformSubsetLaw l (by simpa using hl))
        (defectAtRank (Finset.univ.image (signedPeriodDefects off hsafe s X τ))))
        (primitiveScore q) x)
  change (∑ X : ↥π.coeff.support, F X.val) = _
  rw [Finset.sum_coe_sort]
  dsimp only [F]
  unfold mixedMotifCoefficient multilinear
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro X _
  ring

theorem mixedMotifCoefficient_rank_difference {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (v : IncreasingTuple l r) :
    mixedMotifCoefficient hl off hsafe π s 1 (rankMask v)-
      mixedMotifCoefficient hl off hsafe π s (-1) (rankMask v)=
        signedRankCoefficient hl off hsafe π s v := by
  unfold mixedMotifCoefficient signedRankCoefficient
  simp_rw [averaged_rank_coefficient hl _ v]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro X _
  ring

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

def unchangedPattern (r : ℕ) : Fin r → GapDifference := fun _ => .unchanged

theorem unchanged_positional_value {r : ℕ} (W : (Fin r → Fin 3) → ℝ) :
    (∑ a : Fin r → Fin 3, (∏ h, positionalWeight (unchangedPattern r h) (a h))*W a)=
      W (fun _ => 1) := by
  simp only [unchangedPattern,positionalWeight]
  simp_rw [product_function_delta]
  simp

/-- Comparing a signed displaced motif with the literal centered pure run
 retains every nonconstant positional pattern, not just odd ones. -/
theorem motif_pure_shift_expansion {r : ℕ} (χ β : Fin r → ℝ)
    (hβ : ∀h, IsMotifValue (χ h) (β h)) (W : (Fin r → Fin 3) → ℝ) :
    W (fun h => motifShift (χ h) (β h) 1)-W (fun _ => 1)=
      ∑ k : Fin r → GapDifference, if k=unchangedPattern r then 0 else
        (∏h, motifDifferenceWeight (χ h) (β h) 1 (k h))*
          (∑a : Fin r → Fin 3, (∏h, positionalWeight (k h) (a h))*W a) := by
  rw [motif_shift_expansion χ β 1 hβ (Or.inl rfl) W]
  have he : W (fun _ => 1)=∑k : Fin r → GapDifference,
      if k=unchangedPattern r then
        (∑a : Fin r → Fin 3, (∏h, positionalWeight (k h) (a h))*W a) else 0 := by
    simp [unchanged_positional_value]
  rw [he,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k=unchangedPattern r
  · subst k
    simp [unchangedPattern,motifDifferenceWeight]
  · simp [hk]

theorem mixed_pure_shift_expansion {r : ℕ} (π : IntSeries) (s : ℕ)
    (j : Fin r → ℤ) (W : (Fin r → Fin 3) → ℝ) :
    (∑X∈π.coeff.support, π.coeff X *
      (W (fun h => motifShift (motifIndicator s (j h-X)) ((prouhetSeries s).coeff (j h-X)) 1)-
       W (fun _ => 1)))=
      ∑k : Fin r → GapDifference, if k=unchangedPattern r then 0 else
        motifPatternMultiplier π s j k *
          (∑a : Fin r → Fin 3, (∏h, positionalWeight (k h) (a h))*W a) := by
  simp_rw [motif_pure_shift_expansion _ _ (fun h => prouhet_motif_value s (j h-_)) W,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k=unchangedPattern r
  · simp [hk]
  · simp only [ite_eq_right hk,motifPatternMultiplier,Finset.sum_mul,mul_assoc]
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm

theorem pattern_order_zero {r : ℕ} (k : Fin r → GapDifference)
    (hk : (∑h, (k h).order)=0) : k=unchangedPattern r := by
  funext h
  have hh := Finset.single_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin r))) =>
    Nat.zero_le (k i).order) (Finset.mem_univ h)
  rw [hk] at hh
  have hz : (k h).order=0 := by omega
  cases he : k h <;> simp_all [GapDifference.order,unchangedPattern]

theorem nonconstant_pattern_linear_or_order_two {r : ℕ} (k : Fin r → GapDifference)
    (hk : k≠unchangedPattern r) : (∃h, k=linearPattern h) ∨ 2≤∑h,(k h).order := by
  by_cases hlin : ∃h, k=linearPattern h
  · exact Or.inl hlin
  right
  by_contra hsmall
  have horder : (∑h,(k h).order)=1 := by
    have hn : (∑h,(k h).order)≠0 := fun he => hk (pattern_order_zero k he)
    omega
  have hc := difference_order_eq_counts k
  have hfirst : firstDifferenceCount k=1 := by omega
  have hsecond : secondDifferenceCount k=0 := by omega
  exact hlin (first_second_counts_linear k hfirst hsecond)


/-- A nonconstant motif pattern always has an actual involved position. -/
theorem nonconstant_pattern_position {r : ℕ} (k : Fin r → GapDifference)
    (hk : k≠unchangedPattern r) : ∃a, k a≠.unchanged := by
  by_contra h
  push Not at h
  exact hk (funext h)

theorem clipped_pure_nonlinear_pattern_norm {u m l r : ℕ}
    (hm : 32 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (s : ℕ) (hcentral : CentralMotifSupport u s π)
    {θ : ℝ} (hθ : θ∈Set.Ioo 0 1) (hhalf : 1/2 ≤ θ)
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (k : Fin r → GapDifference) (hk : k≠unchangedPattern r) :
    (∑v : IncreasingTuple l r, (clippedPatternCoefficient hl off hsafe π s θ k v)^2) ≤
      periodDifferencePrefactor u m r (∑h, (k h).order) θ *
        periodCentralSumConstant u r * seriesL2Sq (geomSeries (2^s)*π) := by
  obtain ⟨a,ha⟩ := nonconstant_pattern_position k hk
  have hb := period_pattern_norm hm hr hl (fun _ => off) (fun _ => hoff)
    (by intro _ _; simp) (fun j => hsafe.comp j.val j.property) k
    hθ hhalf hmean hv a
    (fun j => motifPatternMultiplier π s (fun i => (j.val i).val) k)
    (fun h => (geomSeries (2^s)*π).coeff h.val)
    (fun j => motifPatternMultiplier_sq_le π hπ s _ k a ha)
    (unsigned_convolution_central π hcentral)
  apply hb.trans
  apply mul_le_mul_of_nonneg_left
    (seriesL2Sq_partial _ (fun h : Fin u => (h.val:ℤ)) (by intro a b h; apply Fin.ext; change (a.val:ℤ)=b.val at h; exact_mod_cast h))
  unfold periodDifferencePrefactor lengthDifferenceConstant periodCentralSumConstant
  positivity

def purePatternBound (u m r s : ℕ) (π : IntSeries) (θ : ℝ)
    (k : Fin r → GapDifference) : ℝ :=
  if ∃a, k=linearPattern a then
    periodDifferencePrefactor u m r 1 θ * periodCentralSumConstant u r * seriesL2Sq (prouhetSeries s*π)
  else periodDifferencePrefactor u m r (∑h, (k h).order) θ *
    periodCentralSumConstant u r * seriesL2Sq (geomSeries (2^s)*π)

/-- Complete clipped energy, comparing the signed motif to a pure run. -/
theorem clipped_pure_initial_norm {u m l r : ℕ}
    (hm : 32 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (s : ℕ) (hcentral : CentralMotifSupport u s π)
    {θ : ℝ} (hθ : θ∈Set.Ioo 0 1) (hhalf : 1/2 ≤ θ)
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ)) :
    (∑v : IncreasingTuple l r, (∑k : Fin r → GapDifference,
      if k=unchangedPattern r then 0 else clippedPatternCoefficient hl off hsafe π s θ k v)^2) ≤
      (Fintype.card (Fin r → GapDifference):ℝ)*
        ∑k : Fin r → GapDifference, if k=unchangedPattern r then 0 else
          purePatternBound u m r s π θ k := by
  apply (sum_square_card_bound (fun (k : Fin r → GapDifference) (v : IncreasingTuple l r) =>
    if k=unchangedPattern r then 0 else clippedPatternCoefficient hl off hsafe π s θ k v)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k=unchangedPattern r
  · simp [hk]
  · simp only [ite_eq_right hk]
    unfold purePatternBound
    split_ifs with hlin
    · obtain ⟨a,rfl⟩ := hlin
      exact clipped_linear_pattern_norm hm hr hl off hoff hsafe π s hcentral hθ hhalf hmean hv a
    · exact clipped_pure_nonlinear_pattern_norm hm hr hl off hoff hsafe π hπ s hcentral
        hθ hhalf hmean hv k hk

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem shiftedTag_center {n r : ℕ} (p : Fin r → Fin n) (hp : SafeTaggedTuple p) :
    shiftedTag p hp (fun _ => 1)=p := by
  funext i
  apply Fin.ext
  simp [shiftedTag]

def pureRankCoefficient {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (v : IncreasingTuple l r) : ℝ :=
  ∑X∈π.coeff.support, π.coeff X *
    (rankDefectCoefficient hl (signedPeriodDefects off hsafe s X 1) v -
     rankDefectCoefficient hl (periodSlot (fun _ => off)) v)

def pureTupleKernel {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (j : IncreasingTuple u r) (v : IncreasingTuple l r) : ℝ :=
  ∑X∈π.coeff.support, π.coeff X *
    (subsetRankKernel hl (signedPeriodDefects off hsafe s X 1 ∘ j.val) v.val -
     subsetRankKernel hl (periodSlot (fun _ => off) ∘ j.val) v.val)

theorem pureRankCoefficient_tuple_sum {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off))) (π : IntSeries) (s : ℕ)
    (v : IncreasingTuple l r) :
    pureRankCoefficient hl off hsafe π s v=∑j, pureTupleKernel hl off hsafe π s j v := by
  unfold pureRankCoefficient pureTupleKernel
  simp_rw [rankDefectCoefficient_eq _ _ (signedPeriodDefects_strictMono _ _ _ _ _),
    rankDefectCoefficient_eq _ _ (periodSlot_strictMono _),
    ← Finset.sum_sub_distrib,Finset.mul_sum]
  exact Finset.sum_comm

theorem pureTupleKernel_expansion {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off))) (π : IntSeries) (s : ℕ)
    (j : IncreasingTuple u r) (v : IncreasingTuple l r) :
    pureTupleKernel hl off hsafe π s j v = ∑k : Fin r → GapDifference,
      if k=unchangedPattern r then 0 else
        motifPatternMultiplier π s (fun i => (j.val i).val) k *
          positionalRankDifference hl (periodSlot (fun _ => off) ∘ j.val)
            (hsafe.comp j.val j.property) k v := by
  unfold pureTupleKernel
  simp_rw [signedPeriodDefects_comp]
  have H := mixed_pure_shift_expansion π s (fun i => (j.val i).val)
    (fun a => subsetRankKernel hl
      (shiftedTag (periodSlot (fun _ => off) ∘ j.val) (hsafe.comp j.val j.property) a) v.val)
  simpa only [shiftedTag_center,positionalRankDifference] using H

def clippedPureRankCoefficient {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (θ : ℝ) (v : IncreasingTuple l r) : ℝ :=
  ∑j, if PeriodRankRegion m θ j v then pureTupleKernel hl off hsafe π s j v else 0

theorem clippedPureRankCoefficient_expansion {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (θ : ℝ) (v : IncreasingTuple l r) :
    clippedPureRankCoefficient hl off hsafe π s θ v =
      ∑k : Fin r → GapDifference, if k=unchangedPattern r then 0 else
        clippedPatternCoefficient hl off hsafe π s θ k v := by
  unfold clippedPureRankCoefficient clippedPatternCoefficient
  simp_rw [pureTupleKernel_expansion]
  have he (j : IncreasingTuple u r) :
      (if PeriodRankRegion m θ j v then ∑k : Fin r → GapDifference,
        if k=unchangedPattern r then 0 else
          motifPatternMultiplier π s (fun i => (j.val i).val) k *
            positionalRankDifference hl (periodSlot (fun _ => off) ∘ j.val)
              (hsafe.comp j.val j.property) k v else 0)=
      ∑k : Fin r → GapDifference, if k=unchangedPattern r then 0 else
        (if PeriodRankRegion m θ j v then
          motifPatternMultiplier π s (fun i => (j.val i).val) k *
            positionalRankDifference hl (periodSlot (fun _ => off) ∘ j.val)
              (hsafe.comp j.val j.property) k v else 0) := by
    by_cases hv : PeriodRankRegion m θ j v <;> simp [hv]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k=unchangedPattern r <;> simp [hk]

theorem pureTupleKernel_tail {u m l r : ℕ}
    (hu : 0 < u) (hm : 128 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin m) (hoff : |(off.val:ℝ)-(m:ℝ)/2|≤3)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0≤π.coeff X) (hπsum : ∑X∈π.coeff.support, π.coeff X=1)
    (s : ℕ) (j : IncreasingTuple u r) {θ : ℝ} (hθ : θ∈Set.Ioo 0 1) :
    (∑v : IncreasingTuple l r, if PeriodRankRegion m θ j v then 0 else
      |pureTupleKernel hl off hsafe π s j v|) ≤
      2*(((r+1:ℕ):ℝ)*θ^r/binomialMass (u*m) θ l * (2*Real.exp (-(m:ℝ)/(1024*u)))) := by
  let K (X : ℤ) (τ : ℝ) (v : IncreasingTuple l r) :=
    subsetRankKernel hl (if τ=1 then signedPeriodDefects off hsafe s X 1 ∘ j.val
      else periodSlot (fun _ => off) ∘ j.val) v.val
  let B := ((r+1:ℕ):ℝ)*θ^r/binomialMass (u*m) θ l * (2*Real.exp (-(m:ℝ)/(1024*u)))
  have hK (X : ℤ) (τ : ℝ) : (∑v : IncreasingTuple l r,
      if PeriodRankRegion m θ j v then 0 else K X τ v)≤B := by
    dsimp [K]
    split_ifs
    · rw [signedPeriodDefects_comp]
      exact period_shifted_outside_region hu hm hr hl (fun _ => off) (fun _ => hoff)
        (by intro _ _; simp) j (hsafe.comp j.val j.property) _ hθ
    · have H := period_shifted_outside_region hu hm hr hl (fun _ => off) (fun _ => hoff)
        (by intro _ _; simp) j (hsafe.comp j.val j.property) (fun _ => 1) hθ
      simpa only [shiftedTag_center] using H
  have hnon (X : ℤ) (τ : ℝ) (v : IncreasingTuple l r) : 0≤K X τ v :=
    subsetRankKernel_nonneg _ _ _
  calc
    _ ≤ ∑v : IncreasingTuple l r, ∑X∈π.coeff.support, π.coeff X*
        (if PeriodRankRegion m θ j v then 0 else K X 1 v+K X (-1) v) := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : PeriodRankRegion m θ j v
      · simp [hv]
      · simp only [ite_eq_right hv]
        have he : pureTupleKernel hl off hsafe π s j v=
            ∑X∈π.coeff.support, π.coeff X*(K X 1 v-K X (-1) v) := by
          norm_num [pureTupleKernel,K]
        rw [he]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        apply Finset.sum_le_sum
        intro X _
        rw [abs_mul,abs_of_nonneg (hπ X)]
        apply mul_le_mul_of_nonneg_left _ (hπ X)
        exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (hnon X 1 v),abs_of_nonneg (hnon X (-1) v)])
    _ = ∑X∈π.coeff.support, π.coeff X*((∑v : IncreasingTuple l r,
        if PeriodRankRegion m θ j v then 0 else K X 1 v)+
        (∑v : IncreasingTuple l r, if PeriodRankRegion m θ j v then 0 else K X (-1) v)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro X _
      rw [← Finset.mul_sum,← Finset.sum_add_distrib]
      congr 1; apply Finset.sum_congr rfl
      intro v _; split_ifs <;> ring
    _ ≤ ∑X∈π.coeff.support, π.coeff X*(B+B) := by
      apply Finset.sum_le_sum
      intro X _
      exact mul_le_mul_of_nonneg_left (add_le_add (hK X 1) (hK X (-1))) (hπ X)
    _ = _ := by rw [← Finset.sum_mul,hπsum]; dsimp [B]; ring


theorem pureRankCoefficient_tail {u m l r : ℕ}
    (hu : 0 < u) (hm : 128 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support, π.coeff X=1)
    (s : ℕ) {θ : ℝ} (hθ : θ∈Set.Ioo 0 1) :
    (∑v : IncreasingTuple l r, |pureRankCoefficient hl off hsafe π s v-
        clippedPureRankCoefficient hl off hsafe π s θ v|) ≤
      (Fintype.card (IncreasingTuple u r):ℝ)*
      (2*(((r+1:ℕ):ℝ)*θ^r/binomialMass (u*m) θ l * (2*Real.exp (-(m:ℝ)/(1024*u))))) := by
  simp_rw [pureRankCoefficient_tuple_sum,clippedPureRankCoefficient,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑v : IncreasingTuple l r, ∑j : IncreasingTuple u r,
        if PeriodRankRegion m θ j v then 0 else |pureTupleKernel hl off hsafe π s j v| := by
      apply Finset.sum_le_sum
      intro v _
      refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    _ = ∑j : IncreasingTuple u r, ∑v : IncreasingTuple l r,
        if PeriodRankRegion m θ j v then 0 else |pureTupleKernel hl off hsafe π s j v| := Finset.sum_comm
    _ ≤ _ := by
      calc
        _ ≤ ∑j : IncreasingTuple u r,
            2*(((r+1:ℕ):ℝ)*θ^r/binomialMass (u*m) θ l * (2*Real.exp (-(m:ℝ)/(1024*u)))) :=
          Finset.sum_le_sum (fun j _ => pureTupleKernel_tail hu hm hr hl off hoff hsafe π hπ hπsum s j hθ)
        _ = _ := by simp

theorem initial_pure_energy {u m l r : ℕ}
    (hu : 0 < u) (hm : 128 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support, π.coeff X=1)
    (s : ℕ) (hcentral : CentralMotifSupport u s π)
    {θ : ℝ} (hθ : θ∈Set.Ioo 0 1) (hhalf : 1/2 ≤ θ)
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    :
    (∑v : IncreasingTuple l r, (pureRankCoefficient hl off hsafe π s v)^2) ≤
      2*(Fintype.card (Fin r → GapDifference):ℝ)*
        (∑k : Fin r → GapDifference, if k=unchangedPattern r then 0 else
          purePatternBound u m r s π θ k) +
      2*((Fintype.card (IncreasingTuple u r):ℝ)*
        (2*(((r+1:ℕ):ℝ)*θ^r/binomialMass (u*m) θ l * (2*Real.exp (-(m:ℝ)/(1024*u))))))^2 := by
  let A : IncreasingTuple l r → ℝ := pureRankCoefficient hl off hsafe π s
  let C : IncreasingTuple l r → ℝ := clippedPureRankCoefficient hl off hsafe π s θ
  have hn := clipped_pure_initial_norm (by omega) hr hl off hoff hsafe π hπ s hcentral hθ hhalf hmean hv
  simp_rw [← clippedPureRankCoefficient_expansion] at hn
  have ht := pureRankCoefficient_tail hu hm hr hl off hoff hsafe π hπ hπsum s hθ
  have hE := (finite_sum_sq_le_abs_sum_sq (fun v : IncreasingTuple l r => A v-C v)).trans
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun v _ => abs_nonneg (A v-C v))) ht 2)
  have hsum : (∑v : IncreasingTuple l r, A v^2) ≤
      2*(∑v : IncreasingTuple l r, C v^2)+2*(∑v : IncreasingTuple l r, (A v-C v)^2) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro v _
    nlinarith [sq_nonneg (A v-2*C v)]
  calc
    _ ≤ 2*(∑v : IncreasingTuple l r, C v^2)+2*(∑v : IncreasingTuple l r, (A v-C v)^2) := hsum
    _ ≤ _ := by dsimp [C] at *; linarith

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

def scaleCoefficient {n : ℕ} (A : (Fin n → Bool) → ℝ) (L : ℝ) (σ : Fin n → Bool) : ℝ :=
  A σ * ∏ i, if σ i then L else 1

theorem multilinear_scale {α : Type*} {n : ℕ} (A : (Fin n → Bool) → ℝ)
    (Z : α → ℝ) {L : ℝ} (hL : L≠0) (x : Fin n → α) :
    multilinear (scaleCoefficient A L) (fun a => Z a/L) x=multilinear A Z x := by
  unfold multilinear scaleCoefficient
  apply Finset.sum_congr rfl
  intro σ _
  rw [mul_assoc,← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases σ i <;> simp
  exact mul_div_cancel₀ _ hL

theorem multilinearEnergy_scale {n : ℕ} (A : (Fin n → Bool) → ℝ) (L R : ℝ) :
    multilinearEnergy (scaleCoefficient A L) R=multilinearEnergy A (R*L) := by
  unfold multilinearEnergy scaleCoefficient
  apply Finset.sum_congr rfl
  intro σ _
  rw [mul_pow,← Finset.prod_pow,mul_assoc,← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases σ i <;> simp
  ring

/-- The exact norm-of-input factor in the conditional leaf expansion. -/
theorem multilinear_moment_scaled {α : Type*} [Fintype α] (P : FiniteLaw α)
    (Z : α → ℝ) (k : ℕ) (hk : 1 ≤ k) (hcenter : P.expect Z=0)
    {L : ℝ} (hL : 0<L) (hMoment : P.expect (fun a => |Z a|^(2*k))≤L^(2*k))
    (n : ℕ) (A : (Fin n → Bool) → ℝ) :
    (P.product n).expect (fun x => |multilinear A Z x|^(2*k)) ≤
      (multilinearEnergy A ((6*(2*k:ℕ):ℝ)*L))^k := by
  have hcenter' : P.expect (fun a => Z a/L)=0 := by
    unfold FiniteLaw.expect
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    change P.expect Z / L = 0
    rw [hcenter,zero_div]
  have hmoment' : P.expect (fun a => |Z a/L|^(2*k))≤1 := by
    simp_rw [abs_div,abs_of_pos hL,div_pow]
    unfold FiniteLaw.expect
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    apply (div_le_one (by positivity)).mpr hMoment
  have H := multilinear_even_moment P (fun a => Z a/L) k hk hcenter' hmoment' n (scaleCoefficient A L)
  simp_rw [multilinear_scale A Z hL.ne',multilinearEnergy_scale] at H
  simpa only [pow_mul,sq_abs] using H

theorem multilinear_moment_sq_scaled {α : Type*} [Fintype α] (P : FiniteLaw α)
    (Z : α → ℝ) (k : ℕ) (hk : 1 ≤ k) (hcenter : P.expect Z=0)
    {L : ℝ} (hL : 0<L) (hMoment : P.expect (fun a => |Z a|^(2*k))≤L^(2*k))
    (n : ℕ) (A : (Fin n → Bool) → ℝ) :
    (P.product n).evenMomentSq (multilinear A Z) k ≤
      multilinearEnergy A ((6*(2*k:ℕ):ℝ)*L) := by
  have H := multilinear_moment_scaled P Z k hk hcenter hL hMoment n A
  have hn : 0≤(P.product n).expect (fun x => |multilinear A Z x|^(2*k)) := by
    exact Finset.sum_nonneg (fun x _ => mul_nonneg ((P.product n).nonneg x) (by positivity))
  unfold FiniteLaw.evenMomentSq
  calc
    _ ≤ (multilinearEnergy A ((6*(2*k:ℕ):ℝ)*L)^k)^(1/(k:ℝ)) :=
      Real.rpow_le_rpow hn H (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast,one_div,Real.rpow_rpow_inv (multilinearEnergy_nonneg _ _) (by positivity)]

theorem multilinearEnergy_mixture_le {Ω : Type*} [Fintype Ω] {n : ℕ}
    (P : FiniteLaw Ω) (A : Ω → (Fin n → Bool) → ℝ) (R : ℝ) :
    multilinearEnergy (fun σ => P.expect (fun ω => A ω σ)) R ≤
      P.expect (fun ω => multilinearEnergy (A ω) R) := by
  unfold multilinearEnergy FiniteLaw.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro σ _
  have H := weighted_sum_sq_le Finset.univ P.mass (fun ω => A ω σ) (fun ω => P.nonneg ω)
  rw [P.total,one_mul] at H
  calc
    _ ≤ (∑ω, P.mass ω*A ω σ^2)*(∏i,if σ i then R^2 else 1) :=
      mul_le_mul_of_nonneg_right H (Finset.prod_nonneg (fun i _ => by split_ifs <;> positivity))
    _ = _ := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro ω _; ring

theorem multilinearEnergy_sub_le {n : ℕ} (A B : (Fin n → Bool) → ℝ) (R : ℝ) :
    multilinearEnergy (fun σ => A σ-B σ) R ≤
      2*multilinearEnergy A R+2*multilinearEnergy B R := by
  unfold multilinearEnergy
  simp_rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro σ _
  have h := mul_le_mul_of_nonneg_right (show (A σ-B σ)^2≤2*A σ^2+2*B σ^2 by nlinarith [sq_nonneg (A σ+B σ)])
    (Finset.prod_nonneg (s := Finset.univ) (f := fun i => if σ i then R^2 else 1) (fun i _ => by split_ifs <;> positivity))
  nlinarith only [h]

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end

end OAI
