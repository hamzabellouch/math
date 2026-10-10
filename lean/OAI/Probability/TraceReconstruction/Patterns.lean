import OAI.Probability.TraceReconstruction.Differences
import OAI.Probability.TraceReconstruction.InitialDensity

namespace OAI

/-!
# Patterns

Pattern serialization, motif norms, flag posteriors, signed rank coefficients, translated binomials, and support geometry.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem seriesL2Sq_partial {α : Type*} [Fintype α] (f : IntSeries)
    (j : α → ℤ) (hj : Function.Injective j) :
    (∑ a, f.coeff (j a)^2) ≤ seriesL2Sq f := by
  classical
  let A := Finset.univ.image j
  have he : (∑ a, f.coeff (j a)^2)=∑ z∈A, f.coeff z^2 := by
    rw [Finset.sum_image]
    exact fun _ _ _ _ h => hj h
  rw [he]
  calc
    _ ≤ ∑ z∈f.coeff.support ∪ A, f.coeff z^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right (fun _ _ _ => sq_nonneg _)
    _ = _ := by
      rw [seriesL2Sq_eq_sum]
      symm
      apply Finset.sum_subset Finset.subset_union_left
      intro z _ hz
      simp [Finsupp.notMem_support_iff.mp hz]

/-- The cancellation estimate after disjoint rank clipping, retaining the
 actual fixed-period kernels and all anchor correlations. -/
theorem period_pattern_norm {u m l r : ℕ}
    (hm : 32 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2)
    (hsafe : ∀ j : IncreasingTuple u r, SafeTaggedTuple (periodSlot off ∘ j.val))
    (k : Fin r → GapDifference) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 1)
    (hhalf : 1/2 ≤ θ) (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (a : Fin r) (A : IncreasingTuple u r → ℝ) (w : Fin u → ℝ)
    (hA : ∀ j, A j^2 ≤ w (j.val a)^2)
    (hw : ∀ h, w h ≠ 0 → (u:ℝ)/3 ≤ 2*h.val+1 ∧ (u:ℝ)/3 ≤ 2*u-(2*h.val+1)) :
    (∑ v, (∑ j, if PeriodRankRegion m θ j v then
      A j*positionalRankDifference hl (periodSlot off ∘ j.val) (hsafe j) k v else 0)^2) ≤
      periodDifferencePrefactor u m r (∑ h, (k h).order) θ *
        periodCentralSumConstant u r * ∑ h, w h^2 := by
  have hC : 0 ≤ periodDifferencePrefactor u m r (∑ h, (k h).order) θ := by
    unfold periodDifferencePrefactor lengthDifferenceConstant
    positivity
  calc
    _ ≤ ∑ j, A j^2*∑ v, positionalRankDifference hl (periodSlot off ∘ j.val) (hsafe j) k v^2 :=
      period_clipped_square_sum (by omega) hhalf _ A
    _ ≤ ∑ j, A j^2*(periodDifferencePrefactor u m r (∑ h, (k h).order) θ *
        ∏ i, (Real.sqrt (coarsePeriodGap j.val i))⁻¹) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (period_positionalRankDifference_bound hm hr hl off hoff hdiff j (hsafe j) k hθ hmean hv)
        (sq_nonneg _)
    _ = periodDifferencePrefactor u m r (∑ h, (k h).order) θ *
        ∑ j, A j^2*∏ i, (Real.sqrt (coarsePeriodGap j.val i))⁻¹ := by
      rw [Finset.mul_sum]; congr 1; funext j; ring
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (weighted_period_gap_sum a A w hA hw) hC

theorem period_pattern_bounded_norm {u m l r M : ℕ}
    (hm : 32 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2)
    (hsafe : ∀ j : IncreasingTuple u r, SafeTaggedTuple (periodSlot off ∘ j.val))
    (k : Fin r → GapDifference) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 1)
    (hhalf : 1/2 ≤ θ) (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (a : Fin r) (c : Fin (r+1)) (A : IncreasingTuple u r → ℝ) (w : Fin u → ℝ)
    (hA : ∀ j, A j^2 ≤ w (j.val a)^2)
    (hsupport : ∀ j, A j ≠ 0 → coarsePeriodGap j.val c ≤ M)
    (hw : ∀ h, w h ≠ 0 → (u:ℝ)/3 ≤ 2*h.val+1 ∧ (u:ℝ)/3 ≤ 2*u-(2*h.val+1))
    (hM : (M:ℝ) < (u:ℝ)/(3*(r+1:ℝ))) :
    (∑ v, (∑ j, if PeriodRankRegion m θ j v then
      A j*positionalRankDifference hl (periodSlot off ∘ j.val) (hsafe j) k v else 0)^2) ≤
      periodDifferencePrefactor u m r (∑ h, (k h).order) θ *
        periodBoundedSumConstant u r M * ∑ h, w h^2 := by
  have hC : 0 ≤ periodDifferencePrefactor u m r (∑ h, (k h).order) θ := by
    unfold periodDifferencePrefactor lengthDifferenceConstant
    positivity
  calc
    _ ≤ ∑ j, A j^2*∑ v, positionalRankDifference hl (periodSlot off ∘ j.val) (hsafe j) k v^2 :=
      period_clipped_square_sum (by omega) hhalf _ A
    _ ≤ ∑ j, A j^2*(periodDifferencePrefactor u m r (∑ h, (k h).order) θ *
        ∏ i, (Real.sqrt (coarsePeriodGap j.val i))⁻¹) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (period_positionalRankDifference_bound hm hr hl off hoff hdiff j (hsafe j) k hθ hmean hv)
        (sq_nonneg _)
    _ = periodDifferencePrefactor u m r (∑ h, (k h).order) θ *
        ∑ j, A j^2*∏ i, (Real.sqrt (coarsePeriodGap j.val i))⁻¹ := by
      rw [Finset.mul_sum]; congr 1; funext j; ring
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (weighted_period_bounded_gap_sum a c A w hA hsupport hw hM) hC

/-- Two involved motif positions force a short *fixed* internal coarse gap.
 The chosen gap is independent of the actual labels and of the offset law. -/
theorem motif_pattern_bounded_gap {u r : ℕ} (π : IntSeries) (s : ℕ)
    (j : IncreasingTuple u (r+1)) (k : Fin (r+1) → GapDifference)
    (i : Fin r) (b : Fin (r+1)) (hib : i.castSucc < b)
    (hi : k i.castSucc ≠ .unchanged) (hb : k b ≠ .unchanged)
    (hA : motifPatternMultiplier π s (fun a => (j.val a).val) k ≠ 0) :
    coarsePeriodGap j.val i.castSucc.succ ≤ 2*(2^s) := by
  have hs := motif_multiplier_bounded_separation π s (fun a => (j.val a).val) k hA i.castSucc b hi hb
  have hj1 := j.property (show i.castSucc < i.succ by exact Fin.castSucc_lt_succ)
  have hj2 := j.property.monotone (show i.succ ≤ b by simpa only [Fin.le_iff_val_le_val,Fin.lt_def,
    Fin.val_succ,Fin.val_castSucc] using (Nat.succ_le_of_lt hib))
  have h1 : (j.val i.castSucc).val < (j.val i.succ).val := hj1
  have h2 : (j.val i.succ).val ≤ (j.val b).val := hj2
  have hh := (abs_lt.mp hs).1
  rw [coarsePeriodGap_middle]
  omega

end TraceReconstruction


namespace TraceReconstruction

theorem centered_window_floor_fit (P T L t : ℕ) (Y : ℤ)
    (hP : 2*T ≤ P) (hT : 16 ≤ T) (heven : Even T)
    (hL : 8*L ≤ T) (hY : |8*Y| ≤ (T:ℤ))
    (ht : (t:ℤ)=(((P-T)/2:ℕ):ℤ)+Y) :
    t+T ≤ P ∧ t ≤ P/2 ∧ P/2+L ≤ t+T := by
  obtain ⟨k,hk⟩ := heven
  have hy := abs_le.mp hY
  omega

theorem centered_window_floor_anchor (P T : ℕ) (hTP : T ≤ P) (heven : Even T) :
    P/2-(P-T)/2=T/2 := by
  obtain ⟨k,hk⟩ := heven
  omega

theorem atomString_append (n m : ℕ) (w : Bool → List Bool) (θ : Fin (n+m) → Bool) :
    atomString (n+m) w θ =
      atomString n w (fun i => θ (i.castLE (Nat.le_add_right n m))) ++
      atomString m w (fun i => θ (i.natAdd n)) := by
  simp only [atomString,List.ofFn_add,List.flatten_append]

theorem atomString_three (n m k : ℕ) (w : Bool → List Bool) (θ : Fin (n+m+k) → Bool) :
    atomString (n+m+k) w θ =
      atomString n w (fun i => θ ⟨i.val,by omega⟩) ++
      atomString m w (fun i => θ ⟨n+i.val,by omega⟩) ++
      atomString k w (fun i => θ ⟨n+m+i.val,by omega⟩) := by
  rw [atomString_append,atomString_append]
  rfl

/-- A full deterministic template equals a pure prefix, the actual translated
 window, and a pure suffix. This equality is in unmarked binary strings. -/
theorem template_word_window (t T z a L : ℕ) (sign : Fin L → Bool) (τ : Bool)
    (w : Bool → List Bool) (hleft : t ≤ a) (hright : a+L ≤ t+T) :
    atomString (t+T+z) w (templateType (t+T+z) a L sign τ) =
      atomString t w (fun _ => false) ++
      atomString T w (templateType T (a-t) L sign τ) ++
      atomString z w (fun _ => false) := by
  rw [atomString_three]
  congr 2
  · congr 1
    funext i
    exact templateType_outside_window sign τ hleft hright ⟨i.val,by omega⟩ (Or.inl i.isLt)
  · congr 1
    funext i
    exact templateType_inside_window sign τ (by omega) hleft i
  · funext i
    exact templateType_outside_window sign τ hleft hright ⟨t+T+i.val,by omega⟩ (Or.inr (by dsimp; omega))

def pureAtomRun (w : List Bool) (n : ℕ) : List Bool :=
  (List.replicate n w).flatten

theorem atomString_constant (n : ℕ) (w : Bool → List Bool) (b : Bool) :
    atomString n w (fun _ => b)=pureAtomRun (w b) n := by
  simp [atomString,pureAtomRun]

theorem pureAtomRun_add (w : List Bool) (n m : ℕ) :
    pureAtomRun w (n+m)=pureAtomRun w n ++ pureAtomRun w m := by
  simp only [pureAtomRun,List.replicate_add,List.flatten_append]

/-- Splitting or regrouping a pure region into reported chunks changes no
 unmarked string. In particular arbitrary fixed chunk IDs are harmless. -/
theorem pureAtomRun_partition (w : List Bool) (ns : List ℕ) :
    (ns.map (pureAtomRun w)).flatten=pureAtomRun w ns.sum := by
  induction ns with
  | nil => simp [pureAtomRun]
  | cons n ns ih => simp [ih,pureAtomRun_add]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α : Type*} [Fintype α]

/-- Exact orientation law after a report: only invisible bits remain random. -/
def flagPosterior (d : Option Bool) : FiniteLaw Bool where
  mass b := match d with
    | none => 1/2
    | some c => if b=c then 1 else 0
  nonneg := by
    intro b
    cases d with
    | none => norm_num
    | some c => dsimp; split_ifs <;> norm_num
  total := by cases d with
    | none => norm_num [Fintype.sum_bool]
    | some c => simp

def pairedReportMass (P Q H : FiniteLaw α) (ω : ℝ)
    (z : Option Bool × (α × α)) : ℝ :=
  ∑ b : Bool, (1/2 : ℝ)*pairedFlagMass P Q H ω b z

/-- Pointwise Bayes factorization, valid even at zero probability reports. -/
theorem pairedFlag_bayes (P Q H : FiniteLaw α) (ω : ℝ)
    (z : Option Bool × (α × α)) (b : Bool) :
    (1/2 : ℝ)*pairedFlagMass P Q H ω b z =
      pairedReportMass P Q H ω z * (flagPosterior z.1).mass b := by
  rcases z with ⟨d,z⟩
  cases d with
  | none => simp [pairedReportMass,pairedFlagMass,flagPosterior]; ring
  | some c => cases b <;> cases c <;>
      simp [pairedReportMass,pairedFlagMass,flagPosterior]

theorem pairedReportMass_nonneg (P Q H : FiniteLaw α) {ω : ℝ} (hω : 0 ≤ ω)
    (hP : ∀ a, ω*H.mass a ≤ P.mass a) (hQ : ∀ a, ω*H.mass a ≤ Q.mass a)
    (z : Option Bool × (α × α)) : 0 ≤ pairedReportMass P Q H ω z := by
  apply Finset.sum_nonneg
  intro b _
  exact mul_nonneg (by norm_num) (pairedFlagMass_nonneg P Q H hω hP hQ b z)

theorem pairedReportMass_total (P Q H : FiniteLaw α) (ω : ℝ) :
    (∑ z, pairedReportMass P Q H ω z)=1 := by
  unfold pairedReportMass
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,pairedFlagMass_sum]
  norm_num [Fintype.sum_bool]

def pairedReport (P Q H : FiniteLaw α) {ω : ℝ} (hω : 0 ≤ ω)
    (hP : ∀ a, ω*H.mass a ≤ P.mass a) (hQ : ∀ a, ω*H.mass a ≤ Q.mass a) :
    FiniteLaw (Option Bool × (α × α)) :=
  ⟨pairedReportMass P Q H ω, pairedReportMass_nonneg P Q H hω hP hQ,
    pairedReportMass_total P Q H ω⟩

/-- Conditioning solely on exact reports does not correlate mechanisms.
 This is the actual joint-mass factorization, not an independence hypothesis. -/
theorem pairedFlags_product_bayes {ι : Type*} [Fintype ι]
    (P Q H : ι → FiniteLaw α) (ω : ι → ℝ)
    (z : ι → Option Bool × (α × α)) (b : ι → Bool) :
    (∏ i, (1/2 : ℝ)*pairedFlagMass (P i) (Q i) (H i) (ω i) (b i) (z i)) =
      (∏ i, pairedReportMass (P i) (Q i) (H i) (ω i) (z i)) *
        ∏ i, (flagPosterior (z i).1).mass (b i) := by
  simp_rw [pairedFlag_bayes]
  exact Finset.prod_mul_distrib

theorem pairedFlags_report_marginal {ι : Type*} [Fintype ι]
    (P Q H : ι → FiniteLaw α) (ω : ι → ℝ)
    (z : ι → Option Bool × (α × α)) :
    (∑ b : ι → Bool, ∏ i, (1/2 : ℝ)*pairedFlagMass (P i) (Q i) (H i) (ω i) (b i) (z i)) =
      ∏ i, pairedReportMass (P i) (Q i) (H i) (ω i) (z i) := by
  exact (Fintype.prod_sum (fun i b => (1/2 : ℝ)*pairedFlagMass (P i) (Q i) (H i) (ω i) b (z i))).symm

end TraceReconstruction.FiniteLaw


noncomputable section
namespace TraceReconstruction
open scoped Classical

def bitIndex (b : Bool) : ℕ := if b then 1 else 0

def posteriorBitSeries (d : Option Bool) : IntSeries :=
  ∑ b : Bool, AddMonoidAlgebra.single (bitIndex b : ℤ) ((FiniteLaw.flagPosterior d).mass b)

def visibleOnes (d : Option Bool) : ℕ := if d=some true then 1 else 0

def hiddenTrial (d : Option Bool) : ℕ := if d=none then 1 else 0

theorem posteriorBitSeries_factor (d : Option Bool) :
    posteriorBitSeries d = AddMonoidAlgebra.single (visibleOnes d : ℤ) 1 * fairSeries (hiddenTrial d) := by
  cases d with
  | none => simp [posteriorBitSeries,FiniteLaw.flagPosterior,bitIndex,visibleOnes,hiddenTrial,fairSeries,
      add_comm]
  | some b => cases b <;> simp [posteriorBitSeries,FiniteLaw.flagPosterior,bitIndex,visibleOnes,hiddenTrial,
      fairSeries]

/-- The count distribution of the literal posterior orientation bits is
 a translated fair binomial, including reports of probability zero. -/
theorem posterior_count_series {ι : Type*} [Fintype ι] (d : ι → Option Bool) :
    (∑ b : ι → Bool, AddMonoidAlgebra.single (∑ i, (bitIndex (b i):ℤ))
      (∏ i, (FiniteLaw.flagPosterior (d i)).mass (b i))) =
      AddMonoidAlgebra.single (∑ i, (visibleOnes (d i):ℤ)) 1 *
        fairSeries (∑ i, hiddenTrial (d i)) := by
  have he : (∑ b : ι → Bool, AddMonoidAlgebra.single (∑ i, (bitIndex (b i):ℤ))
      (∏ i, (FiniteLaw.flagPosterior (d i)).mass (b i))) = ∏ i, posteriorBitSeries (d i) := by
    rw [show (∏ i, posteriorBitSeries (d i)) =
      ∏ i, ∑ b : Bool, AddMonoidAlgebra.single (bitIndex b : ℤ) ((FiniteLaw.flagPosterior (d i)).mass b) from rfl]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [AddMonoidAlgebra.prod_single]
  rw [he]
  simp_rw [posteriorBitSeries_factor]
  rw [Finset.prod_mul_distrib,AddMonoidAlgebra.prod_single]
  simp only [Finset.prod_const_one]
  congr 1
  unfold fairSeries
  exact Finset.prod_pow_eq_pow_sum _ _ _

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem geomSeries_coeff (k : ℕ) (z : ℤ) :
    (geomSeries k).coeff z = if 0 ≤ z ∧ z < k then 1 else 0 := by
  unfold geomSeries
  simp only [AddMonoidAlgebra.single_pow,one_pow,nsmul_eq_mul,mul_one,
    AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  by_cases hz : 0 ≤ z ∧ z < k
  · obtain ⟨a,rfl⟩ := Int.eq_ofNat_of_zero_le hz.1
    rw [ite_eq_left hz,Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      exact ite_eq_right (by exact_mod_cast hb)
    · intro ha
      have ha' : a < k := by exact_mod_cast hz.2
      exact (ha (Finset.mem_range.mpr ha')).elim
  · rw [ite_eq_right hz]
    apply Finset.sum_eq_zero
    intro a ha
    apply ite_eq_right
    intro haz
    subst z
    exact hz ⟨by positivity,by exact_mod_cast Finset.mem_range.mp ha⟩

theorem motif_unsigned_convolution (π : IntSeries) (s : ℕ) (z : ℤ) :
    (∑ X ∈ π.coeff.support, π.coeff X*motifIndicator s (z-X)) =
      (geomSeries (2^s)*π).coeff z := by
  rw [mul_comm,AddMonoidAlgebra.coeff_mul_apply_left,Finsupp.sum]
  apply Finset.sum_congr rfl
  intro X _
  rw [geomSeries_coeff]
  simp only [motifIndicator,sub_eq_neg_add]

theorem motifPatternMultiplier_sq_le {r : ℕ} (π : IntSeries)
    (hπ : ∀ X, 0 ≤ π.coeff X) (s : ℕ) (j : Fin r → ℤ)
    (k : Fin r → GapDifference) (h : Fin r) (hk : k h ≠ .unchanged) :
    (motifPatternMultiplier π s j k)^2 ≤ ((geomSeries (2^s)*π).coeff (j h))^2 := by
  have ha := motifPatternMultiplier_abs_le π hπ s j k h hk
  rw [motif_unsigned_convolution] at ha
  have hh := pow_le_pow_left₀ (abs_nonneg (motifPatternMultiplier π s j k)) ha 2
  simpa only [sq_abs] using hh

theorem unsigned_motif_energy (π : IntSeries) (s : ℕ) :
    seriesL2Sq (geomSeries (2^s)*π) ≤ ((2:ℝ)^s)^2 * seriesL2Sq π := by
  refine (seriesL2Sq_mul_le _ _).trans ?_
  apply mul_le_mul_of_nonneg_right _ (seriesL2Sq_nonneg _)
  exact pow_le_pow_left₀ (seriesL1_nonneg _) (by simpa using geomSeries_L1_le (2^s)) 2

end TraceReconstruction


noncomputable section
namespace TraceReconstruction

/-- Elementary chi-square upper bound on the Bernoulli relative entropy.
 No Stirling estimate is used in the subsequent count overlap. -/
theorem bernoulli_entropy_upper {t p : ℝ} (ht : t ∈ Set.Ioo 0 1) (hp : p ∈ Set.Ioo 0 1) :
    t*Real.log (t/p)+(1-t)*Real.log ((1-t)/(1-p)) ≤
      (t-p)^2/(p*(1-p)) := by
  have h1 := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos ht.1 hp.1)) ht.1.le
  have h2 := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos (sub_pos.mpr ht.2) (sub_pos.mpr hp.2)))
    (sub_nonneg.mpr ht.2.le)
  have hid : t*(t/p-1)+(1-t)*((1-t)/(1-p)-1)=(t-p)^2/(p*(1-p)) := by
    field_simp [hp.1.ne', (sub_pos.mpr hp.2).ne']
    ring
  linarith

/-- Exact likelihood change from the mean-matched Bernoulli law. -/
theorem binomialMass_likelihood (n l : ℕ) {t p : ℝ}
    (ht : t ∈ Set.Ioo 0 1) (hp : p ∈ Set.Ioo 0 1) :
    binomialMass n p l = binomialMass n t l *
      Real.exp (-((l:ℝ)*Real.log (t/p)+((n-l:ℕ):ℝ)*Real.log ((1-t)/(1-p)))) := by
  have h1 : Real.exp (-((l:ℝ)*Real.log (t/p)))=(p/t)^l := by
    rw [show -((l:ℝ)*Real.log (t/p))=(l:ℝ)*Real.log (p/t) by
      rw [Real.log_div ht.1.ne' hp.1.ne',Real.log_div hp.1.ne' ht.1.ne']; ring,
      Real.exp_nat_mul,Real.exp_log (div_pos hp.1 ht.1)]
  have h2 : Real.exp (-(((n-l:ℕ):ℝ)*Real.log ((1-t)/(1-p))))=((1-p)/(1-t))^(n-l) := by
    rw [show -(((n-l:ℕ):ℝ)*Real.log ((1-t)/(1-p)))=
      ((n-l:ℕ):ℝ)*Real.log ((1-p)/(1-t)) by
      rw [Real.log_div (sub_pos.mpr ht.2).ne' (sub_pos.mpr hp.2).ne',
        Real.log_div (sub_pos.mpr hp.2).ne' (sub_pos.mpr ht.2).ne']; ring,
      Real.exp_nat_mul,Real.exp_log (div_pos (sub_pos.mpr hp.2) (sub_pos.mpr ht.2))]
  rw [neg_add,Real.exp_add,h1,h2]
  unfold binomialMass
  rw [div_pow,div_pow]
  field_simp [ht.1.ne', (sub_pos.mpr ht.2).ne']

/-- Pointwise lower mass at every interior integer, with mean-matched
 variance at least one. It applies uniformly even as deletion vanishes. -/
theorem binomialMass_near_mean_lower (n l : ℕ) {t p : ℝ}
    (ht : t ∈ Set.Ioo 0 1) (hp : p ∈ Set.Ioo 0 1)
    (hl : l ≤ n) (hmean : (n:ℝ)*t=l) (hv : 1 ≤ (n:ℝ)*t*(1-t)) :
    Real.exp (-((l:ℝ)-(n:ℝ)*p)^2/((n:ℝ)*p*(1-p))) /
      (12*Real.sqrt ((n:ℝ)*t*(1-t))) ≤ binomialMass n p l := by
  have hn : (0:ℝ)<n := by nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
  have hnl : ((n-l:ℕ):ℝ)=(n:ℝ)-(l:ℝ) := by exact Nat.cast_sub hl
  have he : (l:ℝ)*Real.log (t/p)+((n-l:ℕ):ℝ)*Real.log ((1-t)/(1-p)) ≤
      ((l:ℝ)-(n:ℝ)*p)^2/((n:ℝ)*p*(1-p)) := by
    have H := mul_le_mul_of_nonneg_left (bernoulli_entropy_upper ht hp) hn.le
    calc
      _ = (n:ℝ)*(t*Real.log (t/p)+(1-t)*Real.log ((1-t)/(1-p))) := by
        rw [hnl,← hmean]; ring
      _ ≤ (n:ℝ)*((t-p)^2/(p*(1-p))) := H
      _ = _ := by
        rw [← hmean]
        field_simp [hn.ne', hp.1.ne', (sub_pos.mpr hp.2).ne']
  rw [binomialMass_likelihood n l ht hp]
  calc
    _ = (1/(12*Real.sqrt ((n:ℝ)*t*(1-t)))) *
      Real.exp (-((l:ℝ)-(n:ℝ)*p)^2/((n:ℝ)*p*(1-p))) := by ring
    _ ≤ (1/(12*Real.sqrt ((n:ℝ)*t*(1-t)))) *
      Real.exp (-((l:ℝ)*Real.log (t/p)+((n-l:ℕ):ℝ)*Real.log ((1-t)/(1-p)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      simpa only [neg_div] using neg_le_neg he
    _ ≤ _ := mul_le_mul_of_nonneg_right (binomialMass_mean_lower n l ht hl hmean hv)
      (Real.exp_nonneg _)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

def signedPeriodDefects {u m : ℕ} (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (s : ℕ) (X : ℤ) (τ : ℝ) : Fin u → Fin (u*m) :=
  shiftedTag (periodSlot (fun _ => off)) hsafe
    (fun j => motifShift (motifIndicator s ((j.val:ℤ)-X)) ((prouhetSeries s).coeff ((j.val:ℤ)-X)) τ)

theorem signedPeriodDefects_strictMono {u m : ℕ} (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (s : ℕ) (X : ℤ) (τ : ℝ) : StrictMono (signedPeriodDefects off hsafe s X τ) :=
  shiftedTag_strictMono _ _ _

theorem SafeTaggedTuple.comp {n u r : ℕ} {p : Fin u → Fin n}
    (hp : SafeTaggedTuple p) (j : Fin r → Fin u) (hj : StrictMono j) :
    SafeTaggedTuple (p ∘ j) :=
  ⟨fun i => hp.1 (j i),fun i k hik => hp.2 (j i) (j k) (hj hik)⟩

theorem shiftedTag_comp {n u r : ℕ} (p : Fin u → Fin n) (hp : SafeTaggedTuple p)
    (a : Fin u → Fin 3) (j : Fin r → Fin u) (hj : StrictMono j) :
    shiftedTag p hp a ∘ j = shiftedTag (p ∘ j) (hp.comp j hj) (a ∘ j) := by
  funext i
  apply Fin.ext
  rfl

/-- Exact degree-r coefficient difference of the actual randomized motif
 in the marked central run, prior to any rank clipping. -/
def signedRankCoefficient {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (v : IncreasingTuple l r) : ℝ :=
  ∑ X ∈ π.coeff.support, π.coeff X *
    (rankDefectCoefficient hl (signedPeriodDefects off hsafe s X 1) v -
     rankDefectCoefficient hl (signedPeriodDefects off hsafe s X (-1)) v)

theorem signedRankCoefficient_expansion {u m l r : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u := u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (v : IncreasingTuple l r) :
    signedRankCoefficient hl off hsafe π s v =
      ∑ k : Fin r → GapDifference, if Odd (firstDifferenceCount k) then
        2*∑ j : IncreasingTuple u r,
          motifPatternMultiplier π s (fun i => (j.val i).val) k *
            positionalRankDifference hl (periodSlot (fun _ => off) ∘ j.val)
              (hsafe.comp j.val j.property) k v else 0 := by
  unfold signedRankCoefficient
  simp_rw [rankDefectCoefficient_eq _ _ (signedPeriodDefects_strictMono _ _ _ _ _),
    ← Finset.sum_sub_distrib,Finset.mul_sum]
  rw [Finset.sum_comm]
  have he (j : IncreasingTuple u r) :
      (∑ X ∈ π.coeff.support, π.coeff X *
        (subsetRankKernel hl (signedPeriodDefects off hsafe s X 1 ∘ j.val) v.val -
         subsetRankKernel hl (signedPeriodDefects off hsafe s X (-1) ∘ j.val) v.val)) =
      ∑ k : Fin r → GapDifference,
        (if Odd (firstDifferenceCount k) then 2*motifPatternMultiplier π s (fun i => (j.val i).val) k else 0)*
          positionalRankDifference hl (periodSlot (fun _ => off) ∘ j.val)
            (hsafe.comp j.val j.property) k v := by
    have htag (X : ℤ) (τ : ℝ) :
        signedPeriodDefects off hsafe s X τ ∘ j.val =
        shiftedTag (periodSlot (fun _ => off) ∘ j.val) (hsafe.comp j.val j.property)
          (fun i => motifShift (motifIndicator s ((j.val i).val-X))
            ((prouhetSeries s).coeff ((j.val i).val-X)) τ) := by
      funext i; apply Fin.ext; rfl
    simp_rw [htag]
    simpa only [positionalRankDifference]
      using mixed_signed_shift_expansion π s (fun i => (j.val i).val)
        (fun a => subsetRankKernel hl
          (shiftedTag (periodSlot (fun _ => off) ∘ j.val) (hsafe.comp j.val j.property) a) v.val)
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with hk
  · apply Finset.sum_congr rfl
    intro j _; ring
  · simp only [zero_mul,Finset.sum_const_zero]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

def translateSeries (c : ℤ) (f : IntSeries) : IntSeries :=
  AddMonoidAlgebra.single c 1*f

theorem translateSeries_coeff (c : ℤ) (f : IntSeries) (z : ℤ) :
    (translateSeries c f).coeff z = f.coeff (z-c) := by
  rw [translateSeries,AddMonoidAlgebra.coeff_single_mul_apply,one_mul]
  congr 1; omega

theorem translateSeries_L2Sq (c : ℤ) (f : IntSeries) :
    seriesL2Sq (translateSeries c f)=seriesL2Sq f := by
  unfold seriesL2Sq
  simp_rw [translateSeries_coeff]
  exact (Equiv.subRight c).tsum_eq (fun z => f.coeff z^2)

theorem translateSeries_L1 (c : ℤ) (f : IntSeries) :
    seriesL1 (translateSeries c f)=seriesL1 f := by
  unfold seriesL1
  simp_rw [translateSeries_coeff]
  exact (Equiv.subRight c).tsum_eq (fun z => |f.coeff z|)

theorem mul_translateSeries (c : ℤ) (f g : IntSeries) :
    f*translateSeries c g=translateSeries c (f*g) := by
  unfold translateSeries
  ring

theorem fairSeries_support (g : ℕ) (z : ℤ) (hz : (fairSeries g).coeff z ≠ 0) :
    0≤z ∧ z≤g := by
  have h0 : 0≤z := by
    by_contra h
    exact hz (fairSeries_coeff_neg g z (by omega))
  obtain ⟨k,rfl⟩ := Int.eq_ofNat_of_zero_le h0
  refine ⟨by positivity,?_⟩
  by_contra hk
  rw [fairSeries_coeff_nat,fairBinomial,Nat.choose_eq_zero_of_lt (by omega)] at hz
  simp at hz

theorem fairSeries_reflect (g : ℕ) (z : ℤ) :
    (fairSeries g).coeff ((g:ℤ)-z)=(fairSeries g).coeff z := by
  by_cases hz : 0≤z ∧ z≤g
  · obtain ⟨k,rfl⟩ := Int.eq_ofNat_of_zero_le hz.1
    have hk : k≤g := by exact_mod_cast hz.2
    rw [← Nat.cast_sub hk,fairSeries_coeff_nat,fairSeries_coeff_nat]
    simp only [fairBinomial,Nat.choose_symm hk]
  · have h1 : (fairSeries g).coeff z=0 := by
      by_contra h; exact hz (fairSeries_support g z h)
    have h2 : (fairSeries g).coeff ((g:ℤ)-z)=0 := by
      by_contra h
      have hh := fairSeries_support g ((g:ℤ)-z) h
      exact hz ⟨by omega,by omega⟩
    rw [h1,h2]

/-- Reflection in the posterior count is exactly an ordinary translated
 fair binomial; it does not change the smoothing channel. -/
theorem affine_reflected_binomial (g : ℕ) (c z : ℤ) :
    (fairSeries g).coeff (c-z)=
      (translateSeries (c-g) (fairSeries g)).coeff z := by
  rw [translateSeries_coeff,← fairSeries_reflect g (c-z)]
  congr 1; omega

theorem translated_binomial_nonneg (g : ℕ) (c z : ℤ) :
    0≤(translateSeries c (fairSeries g)).coeff z := by
  rw [translateSeries_coeff]
  exact fairSeries_nonneg _ _

theorem translated_binomial_support (g : ℕ) (c z : ℤ)
    (hz : (translateSeries c (fairSeries g)).coeff z ≠ 0) :
    c≤z ∧ z≤c+g := by
  rw [translateSeries_coeff] at hz
  have h := fairSeries_support g (z-c) hz
  omega

theorem translated_binomial_smoothing (g s : ℕ) (c : ℤ) :
    seriesL2Sq (prouhetSeries s*translateSeries c (fairSeries g)) ≤
      ((2:ℝ)^(s*s))^2*(((2*binomialBound (g/(s+1)))^s)^2*binomialBound (g/(s+1))) := by
  rw [mul_translateSeries,translateSeries_L2Sq]
  exact (signed_binomial_smoothing g s).2

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem linearPattern_order {r : ℕ} (a : Fin r) :
    (∑ h, ((linearPattern a) h).order)=1 := by
  classical
  have he (h : Fin r) : ((linearPattern a) h).order=if h=a then 1 else 0 := by
    by_cases hh : h=a <;> simp [linearPattern,hh,GapDifference.order]
  simp_rw [he]
  simp

theorem first_second_counts_linear {r : ℕ} (k : Fin r → GapDifference)
    (h1 : firstDifferenceCount k=1) (h2 : secondDifferenceCount k=0) :
    ∃ a : Fin r, k=linearPattern a := by
  classical
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp h1
  refine ⟨a,funext fun b => ?_⟩
  have hfirst : k b = .first ↔ b=a := by
    have hh := congrArg (fun A : Finset (Fin r) => b∈A) ha
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton] using (iff_of_eq hh)
  have hsecond : k b ≠ .second := by
    have hh := Finset.card_eq_zero.mp h2
    intro hb
    have hmem : b∈(Finset.univ.filter fun b => k b=.second) := by simp [hb]
    rw [hh] at hmem
    exact Finset.notMem_empty _ hmem
  by_cases hb : b=a
  · have hf := hfirst.mpr hb
    simpa [linearPattern,hb] using hf
  · have hf := mt hfirst.mp hb
    cases hk : k b <;> simp_all [linearPattern]

theorem odd_pattern_pair {r : ℕ} (k : Fin r → GapDifference)
    (hk : Odd (firstDifferenceCount k)) (hnl : ¬∃a, k=linearPattern a) :
    ∃ a b : Fin r, a<b ∧ k a≠.unchanged ∧ k b≠.unchanged := by
  classical
  have hp : 0<firstDifferenceCount k := hk.pos
  obtain ⟨a,ha⟩ := Finset.card_pos.mp hp
  have ha' : k a=.first := (Finset.mem_filter.mp ha).2
  by_contra hh
  push Not at hh
  apply hnl
  refine ⟨a,funext fun b => ?_⟩
  by_cases hb : b=a
  · subst b; simp [linearPattern,ha']
  · have hba : k b=.unchanged := by
      rcases lt_or_gt_of_ne hb with hba|hab
      · by_contra hb'
        exact (show k a≠.unchanged by simp [ha']) (hh b a hba hb')
      · exact hh a b hab (by simp [ha'])
    simp [linearPattern,hb,hba]

theorem odd_nonlinear_order {r : ℕ} (k : Fin r → GapDifference)
    (hk : Odd (firstDifferenceCount k)) (hnl : ¬∃a, k=linearPattern a) :
    3≤∑ h, (k h).order := by
  rcases odd_pattern_linear_or_order_three k hk with h|h
  · exact (hnl (first_second_counts_linear k h.1 h.2)).elim
  · exact h

/-- An actual convolution witness, retaining the common motif offset. -/
theorem motif_convolution_support (f π : IntSeries) (L : ℕ)
    (hf : ∀z, f.coeff z≠0 → 0≤z ∧ z<L) (z : ℤ) (hz : (f*π).coeff z≠0) :
    ∃X∈π.coeff.support, X≤z ∧ z<X+L := by
  rw [mul_comm,AddMonoidAlgebra.coeff_mul_apply_left,Finsupp.sum] at hz
  obtain ⟨X,hX,hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hh := hf (-X+z) (mul_ne_zero_iff.mp hv).2
  exact ⟨X,hX,by omega,by omega⟩

/-- A support criterion obtained from the actual side-count range. -/
def CentralMotifSupport (u s : ℕ) (π : IntSeries) : Prop :=
  ∀X∈π.coeff.support,
    (u:ℝ)/3≤2*(X:ℝ)+1 ∧ (u:ℝ)/3≤2*u-(2*((X:ℝ)+(2:ℝ)^s)+1)

theorem motif_convolution_central {u s : ℕ} (π f : IntSeries)
    (hπ : CentralMotifSupport u s π)
    (hf : ∀z, f.coeff z≠0 → 0≤z ∧ z<(2^s:ℕ))
    (h : Fin u) (hh : (f*π).coeff (h.val:ℤ)≠0) :
    (u:ℝ)/3≤2*h.val+1 ∧ (u:ℝ)/3≤2*u-(2*h.val+1) := by
  obtain ⟨X,hX,hL,hR⟩ := motif_convolution_support f π (2^s) hf h.val hh
  have hL' : (X:ℝ)≤h.val := by exact_mod_cast hL
  have hR' : (h.val:ℝ)<(X:ℝ)+(2:ℝ)^s := by exact_mod_cast hR
  have hs := hπ X hX
  constructor <;> linarith

theorem prouhet_convolution_central {u s : ℕ} (π : IntSeries)
    (hπ : CentralMotifSupport u s π) (h : Fin u)
    (hh : (prouhetSeries s*π).coeff (h.val:ℤ)≠0) :
    (u:ℝ)/3≤2*h.val+1 ∧ (u:ℝ)/3≤2*u-(2*h.val+1) := by
  apply motif_convolution_central π _ hπ _ h hh
  intro z hz
  constructor
  · by_contra h; exact hz ((prouhetSeries_coeff_spec s).1 z (Or.inl (by omega)))
  · by_contra h; exact hz ((prouhetSeries_coeff_spec s).1 z (Or.inr (by omega)))

theorem unsigned_convolution_central {u s : ℕ} (π : IntSeries)
    (hπ : CentralMotifSupport u s π) (h : Fin u)
    (hh : (geomSeries (2^s)*π).coeff (h.val:ℤ)≠0) :
    (u:ℝ)/3≤2*h.val+1 ∧ (u:ℝ)/3≤2*u-(2*h.val+1) := by
  apply motif_convolution_central π _ hπ _ h hh
  intro z hz
  by_contra hs
  rw [geomSeries_coeff,ite_eq_right hs] at hz
  exact hz rfl

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

end OAI
