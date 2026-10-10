import OAI.Probability.TraceReconstruction.Simulation

namespace OAI

/-!
# SourceOracle

Actual source mechanisms and posteriors, typical metadata, sparse degrees, common-event clipping, approximate oracles, and mixed Hellinger bounds.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Ambient finite trace-space choice does not lose any of the genuine
complete-trace common mass. The embedding adds only zero-mass points. -/
theorem listTraceOverlap_le_ambient {q : ℝ} (hq : q∈Set.Icc 0 1)
    (x y : List Bool) (M : ℕ) (hx : x.length≤M) (hy : y.length≤M) :
    listTraceOverlap q hq x y≤
      (listTraceLaw q hq x M hx).overlap (listTraceLaw q hq y M hy) := by
  let M₀ := max x.length y.length
  have H := approximations_trace_tv hq
    (listTraceLaw q hq x M₀ (le_max_left _ _))
    (listTraceLaw q hq y M₀ (le_max_right _ _)) Subtype.val x y 0 0 M hx hy
    (listTraceLaw_simulates q hq x M₀ _).approximate
    (listTraceLaw_simulates q hq y M₀ _).approximate
  simp only [add_zero] at H
  unfold listTraceOverlap
  rw [FiniteLaw.overlap_eq_one_sub_tv,FiniteLaw.overlap_eq_one_sub_tv]
  linarith

theorem listTraceOverlap_ambient {q : ℝ} (hq : q∈Set.Icc 0 1)
    (x y : List Bool) (M : ℕ) (hx : x.length≤M) (hy : y.length≤M) :
    listTraceOverlap q hq x y=
      (listTraceLaw q hq x M hx).overlap (listTraceLaw q hq y M hy) := by
  apply le_antisymm (listTraceOverlap_le_ambient hq x y M hx hy)
  exact simulations_overlap_le hq _ _ Subtype.val x y
    (listTraceLaw_simulates q hq x M hx) (listTraceLaw_simulates q hq y M hy)

namespace FiniteLaw
variable {α : Type*} [Fintype α]
theorem commonPart_le_right (P Q : FiniteLaw α) (h : 0<P.overlap Q)
    {ω : ℝ} (hω : ω≤P.overlap Q) (a : α) :
    ω*(commonPart P Q h).mass a≤Q.mass a := by
  change ω*(min (P.mass a) (Q.mass a)/P.overlap Q)≤_
  calc
    _ ≤ P.overlap Q*(min (P.mass a) (Q.mass a)/P.overlap Q) :=
      mul_le_mul_of_nonneg_right hω (div_nonneg (le_min (P.nonneg a) (Q.nonneg a)) h.le)
    _ = min (P.mass a) (Q.mass a) := by field_simp
    _ ≤ _ := min_le_right _ _
end FiniteLaw

/-- The paired experiment uses the actual unseparated complete deletion
traces, and the actual normalized minimum of their mass functions. -/
def tracePairedMechanisms {m : ℕ} {q ω : ℝ} (hq : q∈Set.Icc 0 1) (hω : 0<ω)
    (U V : Fin m → List Bool) (M : ℕ) (hU : ∀j,(U j).length≤M) (hV : ∀j,(V j).length≤M)
    (hov : ∀j,ω≤listTraceOverlap q hq (U j) (V j)) : PairedMechanisms (BoundedTrace M) m where
  first j := listTraceLaw q hq (U j) M (hU j)
  second j := listTraceLaw q hq (V j) M (hV j)
  common j := FiniteLaw.commonPart _ _ (hω.trans_le ((hov j).trans (listTraceOverlap_le_ambient hq _ _ M _ _)))
  hiddenWeight _ := ω
  weight_nonneg _ := hω.le
  common_first j := FiniteLaw.commonPart_le_left _ _ _
    ((hov j).trans (listTraceOverlap_le_ambient hq _ _ M _ _))
  common_second j := FiniteLaw.commonPart_le_right _ _ _
    ((hov j).trans (listTraceOverlap_le_ambient hq _ _ M _ _))

/-- Every literal side pair draws its overlap from the correct height of the
source recursion, including reflected global pairs. -/
theorem sourceTrialWord_overlap {q ω : ℝ} (hq : q∈Set.Icc 0 1)
    (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool) (b : ℕ)
    (hov : ∀j<b,ω≤listTraceOverlap q hq
      (pureAtomRun (sourceBlockWord s P atom j false) (h j))
      (pureAtomRun (sourceBlockWord s P atom j false) (h j+1)))
    (i : WindowTrial T n (sourceScheduledTrials T n) b) :
    ω≤listTraceOverlap q hq (sourceTrialWord s P T n h atom b i false)
      (sourceTrialWord s P T n h atom b i true) := by
  induction b with
  | zero => exact PEmpty.elim i
  | succ b ih =>
    rcases i with i | i | ⟨u,i⟩
    · simpa [sourceTrialWord,bitIndex] using hov b (by omega)
    · cases b with
      | zero => exact Fin.elim0 i
      | succ b => simpa [sourceTrialWord,bitIndex] using hov b (by omega)
    · exact ih (fun j hj => hov j (by omega)) i

/-- A common finite side-trace space exists without changing any word. -/
theorem finite_word_bound {ι : Type*} [Fintype ι] (w : ι → List Bool) :
    ∃M,∀i,(w i).length≤M := by
  refine ⟨∑i,(w i).length, fun i => ?_⟩
  exact Finset.single_le_sum (f:=fun i => (w i).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The actual report flags, in the literal nested trial coordinates. -/
def sourceReportFlags {Side : Type*} (T n : ℕ → ℕ) (b : ℕ)
    (z : Reports Side (SourceTrialCount T n b)) :
    WindowAssignments T n (sourceScheduledTrials T n) (Option Bool) b :=
  (sourceAssignmentCode T n (Option Bool) b).symm (fun j => (z j).1)

/-- Exact change of coordinates for the posterior of all hidden bits, not
 just separate local marginals. -/
theorem source_posterior_code_expect {Side : Type*} (T n : ℕ → ℕ) (b : ℕ)
    (z : Reports Side (SourceTrialCount T n b))
    (F : WindowAssignments T n (sourceScheduledTrials T n) Bool b → ℝ) :
    (PairedMechanisms.orientationsGiven z).expect
      (fun bits => F ((sourceAssignmentCode T n Bool b).symm bits)) =
    (windowPosteriorLaw T n (sourceScheduledTrials T n) b (sourceReportFlags T n b z)).expect F := by
  rw [windowPosterior_expect_flat,FiniteLaw.indexedProduct_expect_equiv _ (finEnumeration _)]
  simp only [sourceReportFlags,sourceAssignmentCode_eval]
  simp only [PairedMechanisms.orientationsGiven,FiniteLaw.expect,FiniteLaw.coordinateProduct,
    FiniteLaw.indexedProduct,sourceAssignmentCode,Equiv.coe_fn_symm_mk]
  apply Finset.sum_congr (by ext; simp)
  intro bits _
  rfl

/-- A monomial is precisely its set of actual leaf addresses. -/
def sourceSubsetCode (T : ℕ → ℕ) (b : ℕ) :
    (Fin (SourceLeafCount T b) → Bool) ≃ Finset (WindowLeaf T b) :=
  (maskSubsetEquiv _).trans (Equiv.finsetCongr (finEnumeration _))

theorem sourceSubsetCode_card (T : ℕ → ℕ) (b : ℕ)
    (σ : Fin (SourceLeafCount T b) → Bool) :
    (sourceSubsetCode T b σ).card=monomialDegree σ := by
  simp only [sourceSubsetCode,Equiv.trans_apply,Equiv.finsetCongr_apply,Finset.card_map]
  rfl

theorem selectionCoefficient_sign {k : ℕ} (θ σ : Fin k → Bool) :
    selectionCoefficient θ σ=∏j∈maskSubset σ,(1-boolTypeSign (θ j))/2 := by
  unfold selectionCoefficient maskSubset
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j _
  cases σ j <;> cases θ j <;> norm_num [boolTypeSign]

theorem source_leaf_selection (T n : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (b : ℕ) (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool b)
    (incoming : ℤ) (τ : Bool) (σ : Fin (SourceLeafCount T b) → Bool) :
    selectionCoefficient
      (fun j => sourceTreeLeafBool T n s center b bits incoming τ (finEnumeration _ j)) σ =
    ∏v∈sourceSubsetCode T b σ,
      (1-sourceTreeLeafSign T n (sourceScheduledTrials T n) s center
        (sourceScheduledShift T n) b bits incoming (boolTypeSign τ) v)/2 := by
  rw [selectionCoefficient_sign]
  simp only [sourceSubsetCode,Equiv.trans_apply,Equiv.finsetCongr_apply,Finset.prod_map]
  apply Finset.prod_congr rfl
  intro j _
  rw [sourceTreeLeafBool_sign]
  rfl

/-- The real canonical-oracle coefficient difference is the exact source
 polynomial coefficient whose forced-tree energy has been proved. -/
theorem source_canonical_coefficient {Side : Type*} (T n : ℕ → ℕ) (s : ℕ)
    (center : ℕ → ℤ) (b : ℕ) (incoming : ℤ)
    (z : Reports Side (SourceTrialCount T n (b+1)))
    (σ : Fin (SourceLeafCount T (b+1)) → Bool) :
    averagedCoefficient (PairedMechanisms.orientationsGiven z)
      (sourceFlatLeafType T n s center (b+1) incoming false) σ -
    averagedCoefficient (PairedMechanisms.orientationsGiven z)
      (sourceFlatLeafType T n s center (b+1) incoming true) σ =
    sourceCoefficient T n (sourceScheduledTrials T n) s center (sourceScheduledShift T n)
      b (sourceReportFlags T n (b+1) z) incoming (sourceSubsetCode T (b+1) σ) := by
  unfold averagedCoefficient sourceFlatLeafType
  rw [source_posterior_code_expect T n (b+1) z
    (fun bits => selectionCoefficient
      (fun j => sourceTreeLeafBool T n s center (b+1) bits incoming false (finEnumeration _ j)) σ),
    source_posterior_code_expect T n (b+1) z
    (fun bits => selectionCoefficient
      (fun j => sourceTreeLeafBool T n s center (b+1) bits incoming true (finEnumeration _ j)) σ)]
  simp_rw [source_leaf_selection]
  rfl

/-- Reindexing preserves the entire degree-r square sum, including zero
 and degrees larger than the number of real leaves. -/
theorem source_canonical_degree_sum {Side : Type*} (T n : ℕ → ℕ) (s : ℕ)
    (center : ℕ → ℤ) (b r : ℕ) (incoming : ℤ)
    (z : Reports Side (SourceTrialCount T n (b+1))) :
    (∑σ : Fin (SourceLeafCount T (b+1)) → Bool, if monomialDegree σ=r then
      (averagedCoefficient (PairedMechanisms.orientationsGiven z)
        (sourceFlatLeafType T n s center (b+1) incoming false) σ -
       averagedCoefficient (PairedMechanisms.orientationsGiven z)
        (sourceFlatLeafType T n s center (b+1) incoming true) σ)^2 else 0) =
    ∑S : DegreeLeafSubset T b r,
      (sourceCoefficient T n (sourceScheduledTrials T n) s center (sourceScheduledShift T n)
        b (sourceReportFlags T n (b+1) z) incoming S.val)^2 := by
  simp_rw [source_canonical_coefficient,←sourceSubsetCode_card]
  rw [(sourceSubsetCode T (b+1)).sum_comp
    (fun S => if S.card=r then (sourceCoefficient T n (sourceScheduledTrials T n) s center
      (sourceScheduledShift T n) b (sourceReportFlags T n (b+1) z) incoming S)^2 else 0)]
  let f : DegreeLeafSubset T b r → ℝ := fun S =>
    (sourceCoefficient T n (sourceScheduledTrials T n) s center (sourceScheduledShift T n)
      b (sourceReportFlags T n (b+1) z) incoming S.val)^2
  simpa only [f, dite_eq_ite] using
    sum_subtype_zero_extend (fun S : Finset (WindowLeaf T (b+1)) => S.card=r) f

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace PairedMechanisms
variable {Side : Type*} [Fintype Side] {m : ℕ} (M : PairedMechanisms Side m)

def hiddenSubset (S : Finset (Fin m)) (z : Reports Side m) : ℕ := ∑i : S,hiddenTrial (z i.val).1

theorem hiddenSubset_mgf (S : Finset (Fin m)) {ω t : ℝ} (hw : ∀i,M.hiddenWeight i=ω)
    (hp : ω^2∈Set.Icc 0 1) (ht : |t|≤1) :
    M.reports.expect (fun z => Real.exp (t*((hiddenSubset S z:ℕ)-(S.card:ℝ)*ω^2)))≤
      Real.exp ((S.card:ℝ)*t^2) := by
  have he (z : Reports Side m) :
      Real.exp (t*((hiddenSubset S z:ℕ)-(S.card:ℝ)*ω^2))=
        ∏i : S,Real.exp (t*((hiddenTrial (z i.val).1:ℕ)-ω^2)) := by
    rw [←Real.exp_sum]
    congr 1
    simp only [mul_sub,Finset.mul_sum,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_coe,
      nsmul_eq_mul,hiddenSubset,Nat.cast_sum]
    ring
  simp_rw [he]
  rw [reports,FiniteLaw.coordinateProduct_expect_subtype _ S
    (fun (_ : S) (z : Option Bool × (Side × Side)) => Real.exp (t*((hiddenTrial z.1:ℕ)-ω^2)))]
  calc
    _ ≤ ∏i : S,Real.exp (t^2) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.sum_nonneg (fun z _ => mul_nonneg
          ((FiniteLaw.pairedReport (M.first i.val) (M.second i.val) (M.common i.val) (M.weight_nonneg i.val)
            (M.common_first i.val) (M.common_second i.val)).nonneg z) (Real.exp_nonneg _))
      · intro i _
        have h := FiniteLaw.pairedReport_hidden_mgf (M.first i.val) (M.second i.val) (M.common i.val)
          (M.weight_nonneg i.val) (M.common_first i.val) (M.common_second i.val) (by simpa [hw i.val] using hp) ht
        simpa only [hw i.val] using h
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_coe,Real.exp_nat_mul]

/-- A quantitative unconditional bound for failure of a source hidden-count
 condition. The exponent ω⁴m is sufficient for the uniform scale margins. -/
theorem hiddenSubset_small (S : Finset (Fin m)) {ω : ℝ} (hw : ∀i,M.hiddenWeight i=ω) (hp : ω^2∈Set.Icc 0 1) :
    M.reports.expect (fun z => if (hiddenSubset S z:ℝ)<(S.card:ℝ)*ω^2/2 then 1 else 0)≤
      Real.exp (-(S.card:ℝ)*ω^4/16) := by
  have ht : 0≤ω^2/4 := by positivity
  have ht' : |-(ω^2/4)|≤1 := by rw [abs_neg,abs_of_nonneg ht]; linarith [hp.2]
  have H := finite_exp_markov Finset.univ M.reports.mass
    (fun z => -((hiddenSubset S z:ℕ)-(S.card:ℝ)*ω^2)) (fun z _ => M.reports.nonneg z)
    ((S.card:ℝ)*ω^2/2) (ω^2/4) ht
  have hm := M.hiddenSubset_mgf S hw hp ht'
  have hsub : M.reports.expect (fun z => if (hiddenSubset S z:ℝ)<(S.card:ℝ)*ω^2/2 then 1 else 0)≤
      ∑z∈Finset.univ.filter (fun z => (S.card:ℝ)*ω^2/2≤-((hiddenSubset S z:ℕ)-(S.card:ℝ)*ω^2)),M.reports.mass z := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro z _
    dsimp only
    by_cases hz : (hiddenSubset S z:ℝ)<(S.card:ℝ)*ω^2/2
    · rw [ite_eq_left hz,ite_eq_left (by linarith : (S.card:ℝ)*ω^2/2≤-((hiddenSubset S z:ℕ)-(S.card:ℝ)*ω^2)),mul_one]
    · rw [ite_eq_right hz,mul_zero]; split_ifs <;> positivity [M.reports.nonneg z]
  calc
    _ ≤ _ := hsub.trans H
    _ ≤ Real.exp (-(ω^2/4)*((S.card:ℝ)*ω^2/2))*Real.exp ((S.card:ℝ)*(-(ω^2/4))^2) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      simpa only [FiniteLaw.expect,neg_mul,mul_neg,neg_neg] using hm
    _ = _ := by rw [←Real.exp_add]; congr 1; ring


end PairedMechanisms
end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- IDs for precisely one local and one global collection at every genuine
 nonleaf of the complete source window tree. -/
def WindowCollection (T : ℕ → ℕ) : ℕ → Type
  | 0 => PEmpty
  | b+1 => Bool ⊕ (Fin (T b) × WindowCollection T b)

noncomputable instance windowCollectionFintype (T : ℕ → ℕ) :
    (b : ℕ) → Fintype (WindowCollection T b)
  | 0 => inferInstanceAs (Fintype PEmpty)
  | b+1 => by
    letI := windowCollectionFintype T b
    exact inferInstanceAs (Fintype (Bool ⊕ (Fin (T b) × WindowCollection T b)))

def collectionCount (T n g : ℕ → ℕ) : (b : ℕ) → WindowCollection T b → ℕ
  | b+1, .inl false => n b
  | b+1, .inl true => g b
  | b+1, .inr (_,v) => collectionCount T n g b v

def collectionTrial (T n g : ℕ → ℕ) :
    (b : ℕ) → (v : WindowCollection T b) → Fin (collectionCount T n g b v) → WindowTrial T n g b
  | _+1, .inl false, j => .inl j
  | _+1, .inl true, j => .inr (.inl j)
  | b+1, .inr (u,v), j => .inr (.inr (u,collectionTrial T n g b v j))

theorem collectionTrial_injective (T n g : ℕ → ℕ) (b : ℕ) (v : WindowCollection T b) :
    Function.Injective (collectionTrial T n g b v) := by
  induction b with
  | zero => exact PEmpty.elim v
  | succ b ih =>
    rcases v with v | ⟨u,v⟩
    · cases v
      · intro i j h
        exact Sum.inl.inj h
      · intro i j h
        exact Sum.inl.inj (Sum.inr.inj h)
    · intro i j h
      apply ih v
      exact congrArg Prod.snd (Sum.inr.inj (Sum.inr.inj h))

def collectionFlags (T n g : ℕ → ℕ) {A : Type} :
    (b : ℕ) → WindowAssignments T n g A b → (v : WindowCollection T b) →
      Fin (collectionCount T n g b v) → A
  | _+1, d, .inl false => d.1
  | _+1, d, .inl true => d.2.1
  | b+1, d, .inr (u,v) => collectionFlags T n g b (d.2.2 u) v

theorem collectionFlags_trial (T n g : ℕ → ℕ) {A : Type} (b : ℕ)
    (d : WindowAssignments T n g A b) (v : WindowCollection T b)
    (j : Fin (collectionCount T n g b v)) :
    collectionFlags T n g b d v j=
      windowAssignmentEquiv T n g A b d (collectionTrial T n g b v j) := by
  induction b with
  | zero => exact PEmpty.elim v
  | succ b ih =>
    rcases v with v | ⟨u,v⟩
    · cases v <;> rfl
    · exact ih (d.2.2 u) v j

/-- This is the source hidden-count predicate, before any conditioning on fit. -/
def HiddenCollectionConditions (T n g : ℕ → ℕ) (ω : ℝ) :
    (b : ℕ) → WindowAssignments T n g (Option Bool) b → Prop
  | 0, _ => True
  | b+1, d =>
      (n b:ℝ)*ω^2/2≤∑i,(hiddenTrial (d.1 i):ℝ) ∧
      (g b:ℝ)*ω^2/2≤∑i,(hiddenTrial (d.2.1 i):ℝ) ∧
      ∀u,HiddenCollectionConditions T n g ω b (d.2.2 u)

theorem hiddenCollectionConditions_iff (T n g : ℕ → ℕ) (ω : ℝ) (b : ℕ)
    (d : WindowAssignments T n g (Option Bool) b) :
    HiddenCollectionConditions T n g ω b d ↔
      ∀v : WindowCollection T b,(collectionCount T n g b v:ℝ)*ω^2/2≤
        ∑i,(hiddenTrial (collectionFlags T n g b d v i):ℝ) := by
  induction b with
  | zero => simp [HiddenCollectionConditions,WindowCollection]
  | succ b ih =>
    constructor
    · intro h v
      rcases v with v | ⟨u,v⟩
      · cases v
        · exact h.1
        · exact h.2.1
      · exact (ih (d.2.2 u)).mp (h.2.2 u) v
    · intro h
      refine ⟨h (.inl false),h (.inl true),fun u => (ih (d.2.2 u)).mpr ?_⟩
      intro v
      exact h (.inr (u,v))

def sourceCollectionIndex (T n : ℕ → ℕ) (b : ℕ) (v : WindowCollection T b) :
    Fin (collectionCount T n (sourceScheduledTrials T n) b v) → Fin (SourceTrialCount T n b) :=
  fun j => (finEnumeration _).symm (collectionTrial T n (sourceScheduledTrials T n) b v j)

theorem sourceCollectionIndex_injective (T n : ℕ → ℕ) (b : ℕ) (v : WindowCollection T b) :
    Function.Injective (sourceCollectionIndex T n b v) :=
  (finEnumeration _).symm.injective.comp (collectionTrial_injective T n _ b v)

def sourceCollectionSet (T n : ℕ → ℕ) (b : ℕ) (v : WindowCollection T b) :
    Finset (Fin (SourceTrialCount T n b)) := Finset.univ.image (sourceCollectionIndex T n b v)

theorem sourceCollectionSet_card (T n : ℕ → ℕ) (b : ℕ) (v : WindowCollection T b) :
    (sourceCollectionSet T n b v).card=collectionCount T n (sourceScheduledTrials T n) b v := by
  rw [sourceCollectionSet,Finset.card_image_of_injective _ (sourceCollectionIndex_injective T n b v)]
  simp only [Finset.card_univ,Fintype.card_fin]

theorem sourceCollection_flags {Side : Type*} (T n : ℕ → ℕ) (b : ℕ)
    (z : Reports Side (SourceTrialCount T n b)) (v : WindowCollection T b)
    (j : Fin (collectionCount T n (sourceScheduledTrials T n) b v)) :
    collectionFlags T n (sourceScheduledTrials T n) b (sourceReportFlags T n b z) v j=
      (z (sourceCollectionIndex T n b v j)).1 := by
  rw [collectionFlags_trial]
  have h := sourceAssignmentCode_eval T n (Option Bool) b (fun j => (z j).1)
    (sourceCollectionIndex T n b v j)
  simpa only [sourceCollectionIndex,Equiv.apply_symm_apply,sourceReportFlags] using h

theorem sourceCollection_hidden {Side : Type*} (T n : ℕ → ℕ) (b : ℕ)
    (z : Reports Side (SourceTrialCount T n b)) (v : WindowCollection T b) :
    PairedMechanisms.hiddenSubset (sourceCollectionSet T n b v) z=
      ∑i,hiddenTrial (collectionFlags T n (sourceScheduledTrials T n) b (sourceReportFlags T n b z) v i) := by
  unfold PairedMechanisms.hiddenSubset
  rw [←Finset.sum_subtype (sourceCollectionSet T n b v) (fun _ => Iff.rfl)
    (fun j => hiddenTrial (z j).1)]
  rw [sourceCollectionSet,Finset.sum_image]
  · simp_rw [sourceCollection_flags]
  · exact (sourceCollectionIndex_injective T n b v).injOn

/-- Exact finite-union metadata cost; it contains no postulated typical
 event and no independence assertion between different collections. -/
def sourceHiddenTail (T n : ℕ → ℕ) (b : ℕ) (ω : ℝ) : ℝ :=
  ∑v : WindowCollection T b,Real.exp (-(collectionCount T n (sourceScheduledTrials T n) b v:ℝ)*ω^4/16)

theorem source_hidden_conditions_tail {Side : Type*} [Fintype Side]
    (T n : ℕ → ℕ) (b : ℕ) (M : PairedMechanisms Side (SourceTrialCount T n b))
    (ω : ℝ) (hw : ∀i,M.hiddenWeight i=ω) (hp : ω^2∈Set.Icc 0 1) :
    M.reports.expect (fun z => if HiddenCollectionConditions T n (sourceScheduledTrials T n) ω b
      (sourceReportFlags T n b z) then 0 else 1) ≤ sourceHiddenTail T n b ω := by
  calc
    _ ≤ M.reports.expect (fun z => ∑v : WindowCollection T b,
      if (collectionCount T n (sourceScheduledTrials T n) b v:ℝ)*ω^2/2≤
        ∑i,(hiddenTrial (collectionFlags T n (sourceScheduledTrials T n) b (sourceReportFlags T n b z) v i):ℝ)
      then 0 else 1) := by
        apply FiniteLaw.expect_mono
        intro z
        simp only [hiddenCollectionConditions_iff]
        exact failure_forall_le_sum _
    _ = ∑v : WindowCollection T b,M.reports.expect (fun z =>
      if (PairedMechanisms.hiddenSubset (sourceCollectionSet T n b v) z:ℝ)<
        ((sourceCollectionSet T n b v).card:ℝ)*ω^2/2 then 1 else 0) := by
        rw [FiniteLaw.expect_fintype_sum]
        apply Finset.sum_congr rfl
        intro v _
        apply congrArg (FiniteLaw.expect M.reports)
        funext z
        rw [sourceCollectionSet_card,sourceCollection_hidden,Nat.cast_sum]
        by_cases h : (collectionCount T n (sourceScheduledTrials T n) b v:ℝ)*ω^2/2≤
          ∑i,(hiddenTrial (collectionFlags T n (sourceScheduledTrials T n) b (sourceReportFlags T n b z) v i):ℝ)
        · simp [h,not_lt.mpr h]
        · simp [h,lt_of_not_ge h]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro v _
      simpa only [sourceCollectionSet_card] using M.hiddenSubset_small (sourceCollectionSet T n b v) hw hp

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Numerical cap forced by at least half the mean number of hidden pairs. -/
def hiddenBinomialCap (m : ℕ) (ω : ℝ) : ℝ := Real.sqrt (4/((m:ℝ)*ω^2+2))

theorem hiddenBinomialCap_nonneg (m : ℕ) (ω : ℝ) : 0≤hiddenBinomialCap m ω :=
  Real.sqrt_nonneg _

theorem hidden_binomial_bound (m G : ℕ) (ω : ℝ)
    (h : (m:ℝ)*ω^2/2≤G) : binomialBound G≤hiddenBinomialCap m ω := by
  apply Real.sqrt_le_sqrt
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<G+1)
    (by positivity : (0:ℝ)<(m:ℝ)*ω^2+2)).mpr
  nlinarith

def hiddenSmoothingBound (m s : ℕ) (ω : ℝ) : ℝ :=
  (2:ℝ)^(s*s)*((2*Real.sqrt (4*((s:ℝ)+1)/((m:ℝ)*ω^2+2)))^s *
    Real.sqrt (4*((s:ℝ)+1)/((m:ℝ)*ω^2+2)))

theorem hiddenSmoothingBound_nonneg (m s : ℕ) (ω : ℝ) :
    0≤hiddenSmoothingBound m s ω := by unfold hiddenSmoothingBound; positivity

theorem hidden_smoothing_bound {m : ℕ} (d : Fin m → Option Bool) (s : ℕ) (ω : ℝ)
    (h : (m:ℝ)*ω^2/2≤∑i,(hiddenTrial (d i):ℝ)) :
    posteriorSmoothingCost s d≤hiddenSmoothingBound m s ω := by
  have hn : (m:ℝ)*ω^2/2≤((∑i,hiddenTrial (d i):ℕ):ℝ) := by simpa only [Nat.cast_sum] using h
  have hb : binomialBound ((∑i,hiddenTrial (d i))/(s+1))≤
      Real.sqrt (4*((s:ℝ)+1)/((m:ℝ)*ω^2+2)) := by
    apply (binomialBound_quotient_le _ s).trans
    apply Real.sqrt_le_sqrt
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<((∑i,hiddenTrial (d i):ℕ):ℝ)+1)
      (by positivity : (0:ℝ)<(m:ℝ)*ω^2+2)).mpr
    have hh := mul_le_mul_of_nonneg_left hn (by positivity : (0:ℝ)≤4*((s:ℝ)+1))
    nlinarith
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ)≤2^(s*s))
  have hnon : 0≤binomialBound ((∑i,hiddenTrial (d i))/(s+1)) := Real.sqrt_nonneg _
  exact mul_le_mul
    (pow_le_pow_left₀ (mul_nonneg (by norm_num) hnon) (mul_le_mul_of_nonneg_left hb (by norm_num)) s)
    hb hnon (by positivity)

/-- Hidden-count typicality implies every local/global anchor cap, for the
 actual source metadata and without a coefficient-dependent event. -/
theorem hiddenConditions_binomialCaps (T n g : ℕ → ℕ) (ω : ℝ) (b : ℕ)
    (d : WindowAssignments T n g (Option Bool) b)
    (h : HiddenCollectionConditions T n g ω b d) :
    MetadataBinomialCaps T n g (fun j => hiddenBinomialCap (n j) ω)
      (fun j => hiddenBinomialCap (g j) ω) b d := by
  induction b with
  | zero => trivial
  | succ b ih =>
    refine ⟨hidden_binomial_bound (n b) _ ω ?_,hidden_binomial_bound (g b) _ ω ?_,fun u => ih _ (h.2.2 u)⟩
    · simpa only [Nat.cast_sum] using h.1
    · simpa only [Nat.cast_sum] using h.2.1

theorem hiddenConditions_smoothingCap (T n g : ℕ → ℕ) (ω η : ℝ) (s b : ℕ)
    (hη : ∀j<b,hiddenSmoothingBound (n j) s ω≤η)
    (d : WindowAssignments T n g (Option Bool) b)
    (h : HiddenCollectionConditions T n g ω b d) :
    MetadataSmoothingCap T n g s η b d := by
  induction b with
  | zero => trivial
  | succ b ih =>
    exact ⟨(hidden_smoothing_bound d.1 s ω h.1).trans (hη b (by omega)),
      fun u => ih (fun j hj => hη j (by omega)) _ (h.2.2 u)⟩

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The actual noncentral posterior mass has the unconditional honest
 fit-error bound. Impossible reports cause no problem in Bayes averaging. -/
theorem source_noncentral_average {Side : Type*} [Fintype Side]
    (T n : ℕ → ℕ) (s b : ℕ) (M : PairedMechanisms Side (SourceTrialCount T n (b+1)))
    (hn : ∀j,j<b → 0<n j) (hne : ∀j,j<b → Even (n j))
    (hT : ∀j≤b,24≤T j) (he : ∀j≤b,Even (T j)) (hL : ∀j≤b,24*2^s≤T j)
    (hroot : 4*(n b+1)≤T b) :
    M.reports.expect (fun z => sourceNoncentralMass T n (sourceScheduledTrials T n) s
      (sourceLocalCenter T n) (sourceScheduledShift T n) (fun j => centralThird (T j))
      (b+1) (sourceReportFlags T n (b+1) z) 0) ≤ sourceFitTail T n (b+1) := by
  calc
    _ ≤ M.reports.expect (fun z =>
        (windowPosteriorLaw T n (sourceScheduledTrials T n) (b+1) (sourceReportFlags T n (b+1) z)).expect
          (fun bits => if SourceTreeFit T n (b+1) bits then 0 else 1)) := by
      apply FiniteLaw.expect_mono
      intro z
      exact sourceNoncentralMass_le_fit T n s b (sourceLocalCenter T n) (fun _ _ => rfl)
        hT he hL hroot _
    _ = M.reports.expect (fun z => (PairedMechanisms.orientationsGiven z).expect
        (fun bits => if SourceTreeFit T n (b+1) ((sourceAssignmentCode T n Bool (b+1)).symm bits) then 0 else 1)) := by
      apply congrArg (FiniteLaw.expect M.reports)
      funext z
      exact (source_posterior_code_expect T n (b+1) z
        (fun bits => if SourceTreeFit T n (b+1) bits then 0 else 1)).symm
    _ = _ := M.posterior_average _
    _ ≤ _ := source_flat_fit_tail T n (b+1) (fun j hj => hn j (by omega)) (fun j hj => hne j (by omega))

/-- Markov for a genuine finite law, stated for the exact failure indicator. -/
theorem FiniteLaw.positive_markov {α : Type*} [Fintype α] (P : FiniteLaw α)
    (f : α → ℝ) (hf : ∀x,0≤f x) {a : ℝ} (ha : 0<a) :
    P.expect (fun x => if a≤f x then 1 else 0) ≤ P.expect f/a := by
  apply (le_div_iff₀ ha).mpr
  rw [mul_comm,←FiniteLaw.expect_const_mul]
  apply FiniteLaw.expect_mono
  intro x
  split_ifs with hx
  · simpa only [mul_one] using hx
  · simpa only [mul_zero] using hf x

/-- One metadata event, fixed before choosing a coefficient, controls
 local and global smoothing and all internal central-third tests. -/
def SourceTypical {Side : Type*} (T n : ℕ → ℕ) (s b : ℕ) (ω a : ℝ)
    (z : Reports Side (SourceTrialCount T n (b+1))) : Prop :=
  HiddenCollectionConditions T n (sourceScheduledTrials T n) ω (b+1)
    (sourceReportFlags T n (b+1) z) ∧
  sourceNoncentralMass T n (sourceScheduledTrials T n) s (sourceLocalCenter T n)
    (sourceScheduledShift T n) (fun j => centralThird (T j)) (b+1)
    (sourceReportFlags T n (b+1) z) 0<a

theorem source_typical_failure {Side : Type*} [Fintype Side]
    (T n : ℕ → ℕ) (s b : ℕ) (M : PairedMechanisms Side (SourceTrialCount T n (b+1)))
    (ω a : ℝ) (ha : 0<a) (hw : ∀i,M.hiddenWeight i=ω) (hp : ω^2∈Set.Icc 0 1)
    (hn : ∀j,j<b → 0<n j) (hne : ∀j,j<b → Even (n j))
    (hT : ∀j≤b,24≤T j) (he : ∀j≤b,Even (T j)) (hL : ∀j≤b,24*2^s≤T j)
    (hroot : 4*(n b+1)≤T b) :
    M.reports.expect (fun z => if SourceTypical T n s b ω a z then 0 else 1) ≤
      sourceHiddenTail T n (b+1) ω+sourceFitTail T n (b+1)/a := by
  let f := fun z : Reports Side (SourceTrialCount T n (b+1)) =>
    sourceNoncentralMass T n (sourceScheduledTrials T n) s (sourceLocalCenter T n)
      (sourceScheduledShift T n) (fun j => centralThird (T j)) (b+1)
      (sourceReportFlags T n (b+1) z) 0
  calc
    _ ≤ M.reports.expect (fun z =>
        (if HiddenCollectionConditions T n (sourceScheduledTrials T n) ω (b+1)
          (sourceReportFlags T n (b+1) z) then 0 else 1)+(if a≤f z then 1 else 0)) := by
      apply FiniteLaw.expect_mono
      intro z
      by_cases H : SourceTypical T n s b ω a z
      · rw [ite_eq_left H]
        split_ifs <;> norm_num
      · rw [ite_eq_right H]
        by_cases h : HiddenCollectionConditions T n (sourceScheduledTrials T n) ω (b+1)
          (sourceReportFlags T n (b+1) z)
        · have hf : ¬f z<a := fun hf => H ⟨h,hf⟩
          rw [ite_eq_left h,ite_eq_left (le_of_not_gt hf)]
          norm_num
        · rw [ite_eq_right h]
          split_ifs <;> norm_num
    _ ≤ _ := by
      rw [FiniteLaw.expect_add]
      apply add_le_add (source_hidden_conditions_tail T n (b+1) M ω hw hp)
      apply (M.reports.positive_markov f (fun z => sourceNoncentralMass_nonneg T n _ s _ _ _ _ _ _) ha).trans
      exact div_le_div_of_nonneg_right
        (source_noncentral_average T n s b M hn hne hT he hL hroot) ha.le

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Exact common plateau with integer half-count centering. Unlike the
 simplified g/2 formula, this identity needs no parity assumption. -/
theorem scheduledGlobalShift_plateau_exact (N t : ℕ)
    (bits : Fin ((N/4)*t) → Bool) (u : Fin N) (hu : u∈centralThird N) :
    scheduledGlobalShift N t bits u = (∑i,(bitIndex (bits i):ℤ))-(N/4:ℕ)*(t/2:ℕ) := by
  calc
    _ = ∑v : Fin (N/4),
        ((∑a : Fin t, (bitIndex (bits (globalTrialIndex N t v a)):ℤ))-(t/2:ℕ)) := by
      apply Finset.sum_congr rfl
      intro v _
      exact ite_eq_left (centralThird_active N u hu v)
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      congr 1
      · exact globalTrial_sum N t (fun i => (bitIndex (bits i):ℤ))
      · simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

def sourcePlateauCenter (T n : ℕ → ℕ) : ℕ → ℤ
  | 0 => 0
  | b+1 => (T (b+1)/4:ℕ)*(n b/2:ℕ)

theorem sourceScheduledShift_hasPlateau (T n : ℕ → ℕ) :
    HasGlobalPlateau T (sourceScheduledTrials T n) (fun j => centralThird (T j))
      (sourcePlateauCenter T n) (sourceScheduledShift T n) := by
  intro b bits u hu
  cases b with
  | zero =>
      change (0:ℤ)=(∑i : Fin 0,(bitIndex (bits i):ℤ))-0
      simp
  | succ b => exact scheduledGlobalShift_plateau_exact (T (b+1)) (n b) bits u hu

def sourceForcedBudget (T n : ℕ → ℕ) (s b r : ℕ) (ω : ℝ) : ℝ :=
  (OccupiedParityTree.shapeRoleConstant r (b+1):ℝ)*interiorLabelBudget T b r *
    ((2^s:ℕ):ℝ)^(2*(r-2^(b+1))) *
    ((2*((2^s:ℕ):ℝ)^3*hiddenBinomialCap (n b) ω)*
      binaryTreeBudget (fun j => 4*((2^s:ℕ):ℝ)^6*
        hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω*hiddenBinomialCap (n j) ω) b)

theorem sourceForcedBudget_nonneg (T n : ℕ → ℕ) (s b r : ℕ) (ω : ℝ) :
    0 ≤ sourceForcedBudget T n s b r ω := by
  have hB := fun j => hiddenBinomialCap_nonneg (n j) ω
  have hC := fun j => hiddenBinomialCap_nonneg (sourceScheduledTrials T n j) ω
  have ht := binaryTreeBudget_nonneg (fun j => 4*((2^s:ℕ):ℝ)^6*
      hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω*hiddenBinomialCap (n j) ω)
    (fun j => mul_nonneg (mul_nonneg (by positivity) (hC (j+1))) (hB j)) b
  have hb := hB b
  unfold sourceForcedBudget interiorLabelBudget
  positivity

/-- Full unabsorbed bound, now with no placeholder anchor-energy hypothesis. -/
def sourceDegreeBudget (T n : ℕ → ℕ) (s b r : ℕ) (ω η a : ℝ) : ℝ :=
  4*(3^((b+1)*r):ℕ)*
    (((SourceLeafCount T (b+1)).choose r:ℕ)*(3^((b+1)*r):ℕ)*(η^2+a^2)+
      sourceForcedBudget T n s b r ω)

theorem sourceDegreeBudget_nonneg (T n : ℕ → ℕ) (s b r : ℕ) (ω η a : ℝ) :
    0 ≤ sourceDegreeBudget T n s b r ω η a := by
  have h := sourceForcedBudget_nonneg T n s b r ω
  unfold sourceDegreeBudget
  positivity

theorem source_canonical_degree_bound {Side : Type*} (T n : ℕ → ℕ) (hT : ∀j,0<T j)
    (s b r : ℕ) (ω η a : ℝ) (ha : 0≤a)
    (hη : ∀j<b+1,hiddenSmoothingBound (n j) s ω≤η)
    (z : Reports Side (SourceTrialCount T n (b+1))) (hz : SourceTypical T n s b ω a z) :
    (∑σ : Fin (SourceLeafCount T (b+1)) → Bool, if monomialDegree σ=r then
      (averagedCoefficient (PairedMechanisms.orientationsGiven z)
        (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 false) σ -
       averagedCoefficient (PairedMechanisms.orientationsGiven z)
        (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 true) σ)^2 else 0) ≤
      sourceDegreeBudget T n s b r ω η a := by
  rw [source_canonical_degree_sum]
  apply (sourceCoefficient_degree_energy T n _ s _ _ (fun j => centralThird (T j)) b r
    (sourceReportFlags T n (b+1) z) 0 η
    (hiddenConditions_smoothingCap T n _ ω η s (b+1) hη _ hz.1)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add_right
    exact (sq_le_sq₀ (sourceNoncentralMass_nonneg T n _ s _ _ _ _ _ _) ha).mpr hz.2.le
  · exact degreeForcedRoleEnergy_bound T n _ hT s (sourceLocalCenter T n) _ _ _ (sourceScheduledShift_hasPlateau T n)
      (fun j => hiddenBinomialCap (n j) ω) (fun j => hiddenBinomialCap (sourceScheduledTrials T n j) ω)
      (fun j => hiddenBinomialCap_nonneg _ _) (fun j => hiddenBinomialCap_nonneg _ _)
      b r _ (hiddenConditions_binomialCaps T n _ ω (b+1) _ hz.1) 0

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Pointwise equality of the literal source types and the signed tree types.
 This holds for every assignment, including overflowing windows. -/
theorem sourceFlatLeafType_window (T n : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (b : ℕ) (incoming : ℤ) (τ : Bool) (bits : Fin (SourceTrialCount T n b) → Bool) :
    sourceFlatLeafType T n s center b incoming τ bits =
      windowFinType T s (sourceTreeAnchors T n (sourceScheduledTrials T n) center
        (sourceScheduledShift T n) b ((sourceAssignmentCode T n Bool b).symm bits) incoming)
        b (boolTypeSign τ) := by
  funext j
  unfold sourceFlatLeafType windowFinType windowLeafType
  rw [←sourceTreeLeafSign_eq,←sourceTreeLeafBool_sign]
  change sourceTreeLeafBool T n s center b _ incoming τ (finEnumeration _ j)=
    decide (boolTypeSign (sourceTreeLeafBool T n s center b _ incoming τ (finEnumeration _ j))= -1)
  cases sourceTreeLeafBool T n s center b _ incoming τ (finEnumeration _ j) <;> norm_num [boolTypeSign]

def sourceSparseCount (T : ℕ → ℕ) (s b : ℕ) : ℕ :=
  2^s*∏j∈Finset.range b,T (j+1)

theorem sourceFlatLeafType_sparse (T n : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (b : ℕ) (incoming : ℤ) (τ : Bool) (bits : Fin (SourceTrialCount T n (b+1)) → Bool) :
    monomialDegree (sourceFlatLeafType T n s center (b+1) incoming τ bits) ≤ sourceSparseCount T s b := by
  rw [sourceFlatLeafType_window,windowFinType_degree]
  exact windowMinusCount_bound T s _ b [] _

def sourceOracleCoefficient {Side : Type*} (T n : ℕ → ℕ) (s b : ℕ)
    (z : Reports Side (SourceTrialCount T n (b+1))) (τ : Bool) :
    (Fin (SourceLeafCount T (b+1)) → Bool) → ℝ :=
  averagedCoefficient (PairedMechanisms.orientationsGiven z)
    (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 τ)

theorem sourceOracleCoefficient_empty {Side : Type*} (T n : ℕ → ℕ) (s b : ℕ)
    (z : Reports Side (SourceTrialCount T n (b+1))) (τ : Bool) :
    sourceOracleCoefficient T n s b z τ (fun _ => false)=1 := averagedCoefficient_empty _ _

theorem sourceOracleCoefficient_degree {Side : Type*} (T n : ℕ → ℕ) (s b r : ℕ)
    (z : Reports Side (SourceTrialCount T n (b+1))) (τ : Bool) :
    (∑σ, if monomialDegree σ=r then (sourceOracleCoefficient T n s b z τ σ)^2 else 0) ≤
      ((sourceSparseCount T s b).choose r:ℝ) :=
  averaged_sparse_degree _ _ (sourceFlatLeafType_sparse T n s _ b 0 τ) r

def sourceSignedCoefficient {Side : Type*} (T n : ℕ → ℕ) (s b : ℕ)
    (z : Reports Side (SourceTrialCount T n (b+1))) (σ : Fin (SourceLeafCount T (b+1)) → Bool) : ℝ :=
  sourceOracleCoefficient T n s b z false σ-sourceOracleCoefficient T n s b z true σ

theorem sourceSignedCoefficient_zero {Side : Type*} (T n : ℕ → ℕ) (s b : ℕ)
    (z : Reports Side (SourceTrialCount T n (b+1))) :
    (∑σ, if monomialDegree σ=0 then sourceSignedCoefficient T n s b z σ^2 else 0)=0 := by
  simp [monomialDegree_eq_zero_iff,sourceSignedCoefficient,sourceOracleCoefficient_empty]

theorem sourceSignedCoefficient_degree_geometric {Side : Type*} (T n : ℕ → ℕ) (s b r : ℕ)
    (z : Reports Side (SourceTrialCount T n (b+1))) (w : ℝ) :
    w^(2*r)*(∑σ, if monomialDegree σ=r then sourceSignedCoefficient T n s b z σ^2 else 0) ≤
      4*(w^2*sourceSparseCount T s b)^r := by
  have h0 : 0 ≤ w^(2*r) := by rw [pow_mul]; positivity
  have hp := sourceOracleCoefficient_degree T n s b r z false
  have hm := sourceOracleCoefficient_degree T n s b r z true
  have hc : ((sourceSparseCount T s b).choose r:ℝ) ≤ (sourceSparseCount T s b:ℝ)^r := by
    exact_mod_cast Nat.choose_le_pow (sourceSparseCount T s b) r
  have hd := degree_square_sub_le (sourceOracleCoefficient T n s b z false)
    (sourceOracleCoefficient T n s b z true) r
  calc
    _ ≤ w^(2*r)*(4*(sourceSparseCount T s b:ℝ)^r) :=
      mul_le_mul_of_nonneg_left (by dsimp only [sourceSignedCoefficient]; linarith) h0
    _ = _ := by rw [pow_mul,mul_pow]; ring

def sourceEnergyBudget (T n : ℕ → ℕ) (s b R : ℕ) (ω η a w : ℝ) : ℝ :=
  (∑r∈Finset.range R, w^(2*r)*(if r=0 then 0 else sourceDegreeBudget T n s b r ω η a))+
    4*(w^2*sourceSparseCount T s b)^R/(1-w^2*sourceSparseCount T s b)

/-- Complete signed energy, with finite low-degree forced-tree bound and
 the geometric high tail. No coefficient estimates remain as hypotheses. -/
theorem source_canonical_energy {Side : Type*} (T n : ℕ → ℕ) (hT : ∀j,0<T j)
    (s b R : ℕ) (ω η a w : ℝ) (ha : 0 ≤ a) (hw : 0 ≤ w)
    (hsmall : w^2*sourceSparseCount T s b<1)
    (hη : ∀j<b+1,hiddenSmoothingBound (n j) s ω ≤ η)
    (z : Reports Side (SourceTrialCount T n (b+1))) (hz : SourceTypical T n s b ω a z) :
    multilinearEnergy (sourceSignedCoefficient T n s b z) w ≤ sourceEnergyBudget T n s b R ω η a w := by
  apply multilinearEnergy_low_high _ w (w^2*sourceSparseCount T s b) 4 hw (by positivity) hsmall
    (by norm_num) (fun r => if r=0 then 0 else sourceDegreeBudget T n s b r ω η a)
  · intro r _
    by_cases hr : r=0
    · subst r
      rw [sourceSignedCoefficient_zero,ite_eq_left rfl]
    · rw [ite_eq_right hr]
      exact source_canonical_degree_bound T n hT s b r ω η a ha hη z hz
  · intro r _
    exact sourceSignedCoefficient_degree_geometric T n s b r z w
  · intro r
    split_ifs
    · rfl
    · exact sourceDegreeBudget_nonneg T n s b r ω η a

theorem nonconstant_eq_degreeTail {l : ℕ} (A : (Fin l → Bool) → ℝ) :
    nonconstantCoefficient A=degreeTail A 1 := by
  funext σ
  by_cases h : σ=(fun _ => false)
  · subst σ; simp [nonconstantCoefficient,degreeTail,monomialDegree]
  · have hd : 1 ≤ monomialDegree σ := by
      have := (monomialDegree_eq_zero_iff σ).not.mpr h
      omega
    simp [nonconstantCoefficient,degreeTail,h,hd]

/-- The individual density is close to the pure reference without any
 metadata typicality assumption. -/
theorem source_canonical_centered_energy {Side : Type*} (T n : ℕ → ℕ) (s b : ℕ)
    (z : Reports Side (SourceTrialCount T n (b+1))) (τ : Bool) {w : ℝ} (hw : 0 ≤ w)
    (hsmall : w^2*sourceSparseCount T s b<1) :
    multilinearEnergy (nonconstantCoefficient (sourceOracleCoefficient T n s b z τ)) w ≤
      (w^2*sourceSparseCount T s b)/(1-w^2*sourceSparseCount T s b) := by
  rw [nonconstant_eq_degreeTail]
  simpa only [pow_one,sourceOracleCoefficient] using averaged_sparse_tail_energy _ _
    (sourceFlatLeafType_sparse T n s _ b 0 τ) 1 hw hsmall

end TraceReconstruction

noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α : Type*} [Fintype α]

theorem abs_expect_pow_le (P : FiniteLaw α) (F : α → ℝ) (t : ℕ) :
    |P.expect F|^t ≤ P.expect (fun a => |F a|^t) := by
  have habs : |P.expect F| ≤ P.expect (fun a => |F a|) := by
    calc
      _ ≤ ∑a, |P.mass a*F a| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp only [abs_mul,abs_of_nonneg (P.nonneg _)]; rfl
  apply (pow_le_pow_left₀ (abs_nonneg _) habs t).trans
  simpa only [smul_eq_mul,expect] using
    (convexOn_pow (𝕜:=ℝ) t).map_sum_le (t:=Finset.univ)
      (w:=P.mass) (p:=fun a => |F a|) (fun a _ => P.nonneg a) P.total (fun a _ => (show |F a| ∈ Set.Ici (0:ℝ) from abs_nonneg (F a)))

theorem density_score_centered (P Q : FiniteLaw α) (Z : α → ℝ)
    (hZ : ∀a,Q.mass a=P.mass a*(1+Z a)) : P.expect Z=0 := by
  have h := Q.total
  simp_rw [hZ,mul_add,mul_one,Finset.sum_add_distrib,P.total] at h
  change _+P.expect Z=1 at h
  linarith

/-- Common-event mass difference is controlled by the restricted density
 difference at every moment, by finite Jensen rather than a pointwise bound. -/
theorem clipping_mass_difference (R : FiniteLaw α) (f g : α → ℝ)
    (hf : ∀a,0 ≤ f a) (hg : ∀a,0 ≤ g a) (hfm : R.expect f=1) (hgm : R.expect g=1)
    (A : Finset α) (t : ℕ) :
    |(R.withDensity f hf hfm).eventMass A-(R.withDensity g hg hgm).eventMass A|^t ≤
      R.expect (fun a => |if a∈A then g a-f a else 0|^t) := by
  have he : (R.withDensity f hf hfm).eventMass A-(R.withDensity g hg hgm).eventMass A=
      -(R.expect (fun a => if a∈A then g a-f a else 0)) := by
    simp only [expect,mul_ite,mul_zero,←Finset.sum_filter,
      Finset.filter_mem_eq_inter,Finset.univ_inter,eventMass,withDensity,mul_sub,
      Finset.sum_sub_distrib]
    ring
  rw [he,abs_neg]
  exact R.abs_expect_pow_le _ t

theorem clipped_raw_moment_restricted (R : FiniteLaw α) (f g : α → ℝ)
    (hf : ∀a,0 ≤ f a) (hfm : R.expect f=1)
    (A : Finset α) (hAf : ∀a∈A,1/2 ≤ f a)
    (hP : 0<(R.withDensity f hf hfm).eventMass A) (k : ℕ) :
    (condition (R.withDensity f hf hfm) A hP).expect (fun a => |g a/f a-1|^(k+1)) ≤
      2^k/(R.withDensity f hf hfm).eventMass A *
        R.expect (fun a => |if a∈A then g a-f a else 0|^(k+1)) := by
  let g' : α → ℝ := fun a => if a∈A then g a else f a
  have H := clipped_raw_moment R f g' hf hfm A hAf hP k
  have he : (condition (R.withDensity f hf hfm) A hP).expect (fun a => |g a/f a-1|^(k+1))=
      (condition (R.withDensity f hf hfm) A hP).expect (fun a => |g' a/f a-1|^(k+1)) := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a∈A <;> simp [condition,g',ha]
  rw [he]
  convert H using 1
  congr 2
  funext a
  by_cases ha : a∈A <;> simp [g',ha]

/-- Explicit normalized clipping, at half of any positive even moment. This
 constructs the actual conditioned score; no bounded-score hypothesis. -/
theorem clipped_score_moment (R : FiniteLaw α) (f g : α → ℝ)
    (hf : ∀a,0 ≤ f a) (hg : ∀a,0 ≤ g a) (hfm : R.expect f=1) (hgm : R.expect g=1)
    (A : Finset α) (hAf : ∀a∈A,1/2 ≤ f a)
    (hp : 1/2 ≤ (R.withDensity f hf hfm).eventMass A)
    (hq : 1/2 ≤ (R.withDensity g hg hgm).eventMass A)
    (k : ℕ) (hk : 1 ≤ k) (V : ℝ) (hV : 0 ≤ V)
    (hM : R.expect (fun a => |if a∈A then g a-f a else 0|^(2*k)) ≤ V^k) :
    let p := (R.withDensity f hf hfm).eventMass A
    let q := (R.withDensity g hg hgm).eventMass A
    let hP : 0 < p := lt_of_lt_of_le (by norm_num) hp
    (condition (R.withDensity f hf hfm) A hP).evenMomentSq (fun a => p/q*(g a/f a)-1) k ≤64*V := by
  dsimp only
  let p := (R.withDensity f hf hfm).eventMass A
  let q := (R.withDensity g hg hgm).eventMass A
  have hp0 : 0<p := lt_of_lt_of_le (by norm_num) hp
  have hq0 : 0<q := lt_of_lt_of_le (by norm_num) hq
  have hp1 : p ≤ 1 := eventMass_le_one _ _
  have hratio : p/q ≤ 2 := (div_le_iff₀ hq0).mpr (by linarith)
  have hden : (1:ℝ)/p ≤ 2 := (div_le_iff₀ hp0).mpr (by linarith)
  have ht : 2*k-1+1=2*k := by omega
  have hraw := clipped_raw_moment_restricted R f g hf hfm A hAf hp0 (2*k-1)
  rw [ht] at hraw
  have hraw' : (condition (R.withDensity f hf hfm) A hp0).expect (fun a => |g a/f a-1|^(2*k)) ≤
      2^(2*k)*V^k := by
    apply hraw.trans
    calc
      _ ≤ (2^(2*k-1)/p)*V^k := mul_le_mul_of_nonneg_left hM (by positivity)
      _ ≤ (2^(2*k-1)*2)*V^k := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hV _)
        simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ (2:ℝ)^(2*k-1))
      _ = _ := by rw [←pow_succ,ht]
  have hnorm : |p/q-1|^(2*k) ≤ 2^(2*k)*V^k := by
    rw [div_sub_one hq0.ne',abs_div,abs_of_pos hq0,div_pow]
    apply (div_le_iff₀ (pow_pos hq0 _)).mpr
    have hd := (clipping_mass_difference R f g hf hg hfm hgm A (2*k)).trans hM
    have hqpow : 1 ≤ (2*q)^(2*k) := one_le_pow₀ (by linarith)
    calc
      _ ≤ V^k := hd
      _ ≤ (2*q)^(2*k)*V^k := by nlinarith [pow_nonneg hV k]
      _ = _ := by rw [mul_pow]; ring
  have hs := score_rescaling_moment (condition (R.withDensity f hf hfm) A hp0)
    (fun a => g a/f a) (p/q) (div_nonneg hp0.le hq0.le) (2*k-1)
  rw [ht] at hs
  have hpower : (p/q)^(2*k) ≤ (2:ℝ)^(2*k) :=
    pow_le_pow_left₀ (div_nonneg hp0.le hq0.le) hratio _
  have hs' : (condition (R.withDensity f hf hfm) A hp0).expect (fun a => |p/q*(g a/f a)-1|^(2*k)) ≤
      (64*V)^k := by
    apply hs.trans
    calc
      _ ≤ 2^(2*k-1)*(2^(2*k)*(2^(2*k)*V^k)+2^(2*k)*V^k) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (mul_le_mul hpower hraw' (by
          apply Finset.sum_nonneg; intro a _; positivity [(condition (R.withDensity f hf hfm) A hp0).nonneg a]) (by positivity)) hnorm
      _ ≤ 2^(2*k-1)*(2^(2*k)*(2^(2*k)*V^k)+2^(2*k)*(2^(2*k)*V^k)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add_right
        have htwo : (1:ℝ) ≤ 2^(2*k) := one_le_pow₀ (by norm_num)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right htwo
          (by positivity : 0 ≤ (2:ℝ)^(2*k)*V^k)
      _ = (64*V)^k := by
        have hm : 2^(2*k-1)*2= (2:ℝ)^(2*k) := by rw [←pow_succ,ht]
        calc
          _ = (2^(2*k-1)*2)*(2:ℝ)^(2*k)*(2:ℝ)^(2*k)*V^k := by ring
          _ = _ := by rw [hm,←pow_add,←pow_add,mul_pow]; congr 1; rw [show 2*k+2*k+2*k=6*k by omega,pow_mul]; norm_num
  unfold evenMomentSq
  calc
    _ ≤ ((64*V)^k)^(1/(k:ℝ)) := Real.rpow_le_rpow
      (by apply Finset.sum_nonneg; intro a _; positivity [(condition (R.withDensity f hf hfm) A hp0).nonneg a]) hs' (by positivity)
    _ = _ := by rw [←Real.rpow_natCast,one_div,Real.rpow_rpow_inv (by positivity) (by positivity)]

end TraceReconstruction.FiniteLaw

noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α : Type*} [Fintype α]

theorem eventMass_indicator (P : FiniteLaw α) (A : Finset α) :
    P.eventMass A=P.expect (fun a => if a∈A then 1 else 0) := by
  simp only [expect,mul_ite,mul_one,mul_zero,←Finset.sum_filter,
    Finset.filter_mem_eq_inter,Finset.univ_inter,eventMass]

theorem eventMass_compl (P : FiniteLaw α) (A : Finset α) :
    P.eventMass Aᶜ=1-P.eventMass A := by
  rw [eventMass_indicator,eventMass_indicator]
  have he : P.expect (fun a => (if a∈Aᶜ then (1:ℝ) else 0)+(if a∈A then 1 else 0))=1 := by
    convert P.expect_const 1 using 1
    congr 1; funext a
    by_cases ha : a∈A <;> simp [ha]
  rw [expect_add] at he
  linarith

theorem density_second_moment_le_six (R : FiniteLaw α) (f : α → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hM : R.expect (fun a => |f a-1|^(2*k)) ≤ 1) :
    R.expect (fun a => f a^2) ≤ 6 := by
  have h := R.expect_lower_moment_le_two (fun a => f a-1) (2*k) hM 2 (by omega)
  calc
    _ ≤ R.expect (fun a => 2*(f a-1)^2+2) := R.expect_mono (fun a => by nlinarith [sq_nonneg (f a-2)])
    _ = 2*R.expect (fun a => (f a-1)^2)+2 := by rw [expect_add,expect_const_mul,expect_const]
    _ ≤ _ := by linarith [le_abs_self (R.expect (fun a => (f a-1)^2))]

/-- Cauchy--Schwarz loss on the actual low-reference-density event, for
 either density. The same clipping event is used for both hypotheses. -/
theorem density_low_event_mass (R : FiniteLaw α) (f g : α → ℝ)
    (hg : ∀a,0 ≤ g a) (hgm : R.expect g=1) (k : ℕ) (hk : 1 ≤ k) (U : ℝ)
    (hU : 0 ≤ U) (hU1 : U ≤ 1)
    (hfM : R.expect (fun a => |f a-1|^(2*k)) ≤ U^k)
    (hgM : R.expect (fun a => |g a-1|^(2*k)) ≤ U^k) :
    (R.withDensity g hg hgm).eventMass (Finset.univ.filter (fun a => f a<1/2)) ≤
      Real.sqrt (6*(4*U)^k) := by
  let A := Finset.univ.filter (fun a => f a<1/2)
  have hR : R.eventMass A ≤ (4*U)^k := by
    calc
      _ ≤ 2^(2*k)*R.expect (fun a => |f a-1|^(2*k)) :=
        R.low_density_reference_mass f (2*k) A (fun a ha => (Finset.mem_filter.mp ha).2)
      _ ≤ 2^(2*k)*U^k := mul_le_mul_of_nonneg_left hfM (by positivity)
      _ = _ := by rw [pow_mul,mul_pow]; norm_num
  have hsecond := R.density_second_moment_le_six g k hk (hgM.trans (pow_le_one₀ hU hU1))
  have hsq : ((R.withDensity g hg hgm).eventMass A)^2 ≤ 6*(4*U)^k := by
    apply (R.density_bad_mass_sq g A).trans
    calc
      _ ≤ R.eventMass A*6 := mul_le_mul_of_nonneg_left hsecond (R.eventMass_nonneg A)
      _ ≤ _ := by nlinarith
  exact (Real.le_sqrt ((R.withDensity g hg hgm).eventMass_nonneg A) (by positivity)).mpr hsq

def commonClipEvent (B : Finset α) (f : α → ℝ) : Finset α :=
  B.filter (fun a => 1/2 ≤ f a)

theorem commonClipEvent_loss (P : FiniteLaw α) (B : Finset α) (f : α → ℝ) :
    1-P.eventMass (commonClipEvent B f) ≤
      P.eventMass Bᶜ+P.eventMass (Finset.univ.filter (fun a => f a<1/2)) := by
  rw [←eventMass_compl,eventMass_indicator,eventMass_indicator,eventMass_indicator,←expect_add]
  apply P.expect_mono
  intro a
  simp only [commonClipEvent,Finset.mem_compl,Finset.mem_filter,Finset.mem_univ,true_and]
  split_ifs <;> simp_all


/-- Quantitative common clipping on any genuine good event. Both bad-event
 costs below are measured under the actual normalized laws, not reference mass. -/
theorem commonClipEvent_mass (R : FiniteLaw α) (f g : α → ℝ)
    (hf : ∀a,0 ≤ f a) (hg : ∀a,0 ≤ g a) (hfm : R.expect f=1) (hgm : R.expect g=1)
    (B : Finset α) (e : ℝ) (hfB : (R.withDensity f hf hfm).eventMass Bᶜ ≤ e)
    (hgB : (R.withDensity g hg hgm).eventMass Bᶜ ≤ e)
    (k : ℕ) (hk : 1 ≤ k) (U : ℝ) (hU : 0 ≤ U) (hU1 : U ≤ 1)
    (hfM : R.expect (fun a => |f a-1|^(2*k)) ≤ U^k)
    (hgM : R.expect (fun a => |g a-1|^(2*k)) ≤ U^k) :
    1-(R.withDensity f hf hfm).eventMass (commonClipEvent B f) ≤ e+Real.sqrt (6*(4*U)^k) ∧
    1-(R.withDensity g hg hgm).eventMass (commonClipEvent B f) ≤ e+Real.sqrt (6*(4*U)^k) := by
  constructor
  · exact (commonClipEvent_loss _ B f).trans (add_le_add hfB
      (density_low_event_mass R f f hf hfm k hk U hU hU1 hfM hfM))
  · exact (commonClipEvent_loss _ B f).trans (add_le_add hgB
      (density_low_event_mass R f g hg hgm k hk U hU hU1 hfM hgM))

end TraceReconstruction.FiniteLaw

noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- A pair produced by genuine common-event normalized conditioning. The
 outcome space and public decoder remain unchanged. -/
structure ClippedOracle {α : Type*} [Fintype α] (P Q : FiniteLaw α) (k : ℕ) (e V : ℝ) where
  first : FiniteLaw α
  second : FiniteLaw α
  score : α → ℝ
  density : ∀a,second.mass a=first.mass a*(1+score a)
  likelihood_nonneg : ∀a,0 ≤ 1+score a
  centered : first.expect score=0
  moment : first.evenMomentSq score k ≤ V
  first_tv : first.tv P ≤ e
  second_tv : second.tv Q ≤ e

namespace FiniteLaw
variable {α : Type*} [Fintype α]

theorem exists_clippedOracle (R : FiniteLaw α) (f g : α → ℝ)
    (hf : ∀a,0 ≤ f a) (hg : ∀a,0 ≤ g a) (hfm : R.expect f=1) (hgm : R.expect g=1)
    (B : Finset α) (e : ℝ) (hfB : (R.withDensity f hf hfm).eventMass Bᶜ ≤ e)
    (hgB : (R.withDensity g hg hgm).eventMass Bᶜ ≤ e)
    (k : ℕ) (hk : 1 ≤ k) (U : ℝ) (hU : 0 ≤ U) (hU1 : U ≤ 1)
    (hfM : R.expect (fun a => |f a-1|^(2*k)) ≤ U^k)
    (hgM : R.expect (fun a => |g a-1|^(2*k)) ≤ U^k)
    (V : ℝ) (hV : 0 ≤ V)
    (hM : R.expect (fun a => |if a∈B then g a-f a else 0|^(2*k)) ≤ V^k)
    (hsmall : e+Real.sqrt (6*(4*U)^k) ≤ 1/2) :
    Nonempty (ClippedOracle (R.withDensity f hf hfm) (R.withDensity g hg hgm)
      k (e+Real.sqrt (6*(4*U)^k)) (64*V)) := by
  let A := commonClipEvent B f
  let P := R.withDensity f hf hfm
  let Q := R.withDensity g hg hgm
  have hA (a : α) (ha : a∈A) : 1/2 ≤ f a := (Finset.mem_filter.mp ha).2
  have hloss := commonClipEvent_mass R f g hf hg hfm hgm B e hfB hgB k hk U hU hU1 hfM hgM
  have hp : 1/2 ≤ P.eventMass A := by linarith [hloss.1]
  have hq : 1/2 ≤ Q.eventMass A := by linarith [hloss.2]
  have hp0 : 0<P.eventMass A := lt_of_lt_of_le (by norm_num) hp
  have hq0 : 0<Q.eventMass A := lt_of_lt_of_le (by norm_num) hq
  let Z : α → ℝ := fun a => P.eventMass A/Q.eventMass A*(g a/f a)-1
  have hden (a : α) : (Q.condition A hq0).mass a=(P.condition A hp0).mass a*(1+Z a) := by
    dsimp only [Z]
    rw [show 1+(P.eventMass A/Q.eventMass A*(g a/f a)-1)=P.eventMass A/Q.eventMass A*(g a/f a) by ring]
    exact conditioned_density_identity R f g hf hg hfm hgm A
      (fun a ha => lt_of_lt_of_le (by norm_num) (hA a ha)) hp0 hq0 a
  have hAM : R.expect (fun a => |if a∈A then g a-f a else 0|^(2*k)) ≤ V^k := by
    apply le_trans (R.expect_mono _) hM
    intro a
    by_cases ha : a∈A
    · have hb := (Finset.mem_filter.mp ha).1
      simp only [ite_eq_left ha,ite_eq_left hb,le_refl]
    · rw [ite_eq_right ha]
      simp only [abs_zero,zero_pow (by omega : 2*k≠0)]
      exact pow_nonneg (abs_nonneg _) _
  exact ⟨{
    first := P.condition A hp0
    second := Q.condition A hq0
    score := Z
    density := hden
    likelihood_nonneg := fun a => by
      dsimp only [Z]
      have hh := mul_nonneg (div_nonneg hp0.le hq0.le) (div_nonneg (hg a) (hf a))
      linarith
    centered := density_score_centered _ _ Z hden
    moment := clipped_score_moment R f g hf hg hfm hgm A hA hp hq k hk V hV hAM
    first_tv := by rw [tv_symm,tv_condition]; exact hloss.1
    second_tv := by rw [tv_symm,tv_condition]; exact hloss.2
  }⟩

end FiniteLaw
end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Exact finite-union metadata cost; it contains no postulated typical
 event and no independence assertion between different collections. -/
def sourceEffectiveHiddenTail (T n : ℕ → ℕ) (b : ℕ) (ω : ℝ) : ℝ :=
  ∑v : WindowCollection T b,if collectionCount T n (sourceScheduledTrials T n) b v=0 then 0 else Real.exp (-(collectionCount T n (sourceScheduledTrials T n) b v:ℝ)*ω^4/16)

theorem source_hidden_conditions_effective_tail {Side : Type*} [Fintype Side]
    (T n : ℕ → ℕ) (b : ℕ) (M : PairedMechanisms Side (SourceTrialCount T n b))
    (ω : ℝ) (hw : ∀i,M.hiddenWeight i=ω) (hp : ω^2∈Set.Icc 0 1) :
    M.reports.expect (fun z => if HiddenCollectionConditions T n (sourceScheduledTrials T n) ω b
      (sourceReportFlags T n b z) then 0 else 1) ≤ sourceEffectiveHiddenTail T n b ω := by
  calc
    _ ≤ M.reports.expect (fun z => ∑v : WindowCollection T b,
      if (collectionCount T n (sourceScheduledTrials T n) b v:ℝ)*ω^2/2≤
        ∑i,(hiddenTrial (collectionFlags T n (sourceScheduledTrials T n) b (sourceReportFlags T n b z) v i):ℝ)
      then 0 else 1) := by
        apply FiniteLaw.expect_mono
        intro z
        simp only [hiddenCollectionConditions_iff]
        exact failure_forall_le_sum _
    _ = ∑v : WindowCollection T b,M.reports.expect (fun z =>
      if (PairedMechanisms.hiddenSubset (sourceCollectionSet T n b v) z:ℝ)<
        ((sourceCollectionSet T n b v).card:ℝ)*ω^2/2 then 1 else 0) := by
        rw [FiniteLaw.expect_fintype_sum]
        apply Finset.sum_congr rfl
        intro v _
        apply congrArg (FiniteLaw.expect M.reports)
        funext z
        rw [sourceCollectionSet_card,sourceCollection_hidden,Nat.cast_sum]
        by_cases h : (collectionCount T n (sourceScheduledTrials T n) b v:ℝ)*ω^2/2≤
          ∑i,(hiddenTrial (collectionFlags T n (sourceScheduledTrials T n) b (sourceReportFlags T n b z) v i):ℝ)
        · simp [h,not_lt.mpr h]
        · simp [h,lt_of_not_ge h]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hc : collectionCount T n (sourceScheduledTrials T n) b v=0
      · rw [ite_eq_left hc]
        have hz : M.reports.expect (fun z =>
            if (PairedMechanisms.hiddenSubset (sourceCollectionSet T n b v) z:ℝ)<
              ((sourceCollectionSet T n b v).card:ℝ)*ω^2/2 then 1 else 0)=0 := by
          have h (z : Reports Side (SourceTrialCount T n b)) :
              ¬(PairedMechanisms.hiddenSubset (sourceCollectionSet T n b v) z:ℝ)<
                ((sourceCollectionSet T n b v).card:ℝ)*ω^2/2 := by
            rw [sourceCollectionSet_card,hc]
            simp only [Nat.cast_zero,zero_mul,zero_div]
            exact not_lt.mpr (Nat.cast_nonneg _)
          simp_rw [ite_eq_right (h _)]
          exact FiniteLaw.expect_const _ 0
        exact hz.le
      · rw [ite_eq_right hc]
        simpa only [sourceCollectionSet_card] using M.hiddenSubset_small (sourceCollectionSet T n b v) hw hp

theorem source_typical_effective_failure {Side : Type*} [Fintype Side]
    (T n : ℕ → ℕ) (s b : ℕ) (M : PairedMechanisms Side (SourceTrialCount T n (b+1)))
    (ω a : ℝ) (ha : 0<a) (hw : ∀i,M.hiddenWeight i=ω) (hp : ω^2∈Set.Icc 0 1)
    (hn : ∀j,j<b → 0<n j) (hne : ∀j,j<b → Even (n j))
    (hT : ∀j≤b,24≤T j) (he : ∀j≤b,Even (T j)) (hL : ∀j≤b,24*2^s≤T j)
    (hroot : 4*(n b+1)≤T b) :
    M.reports.expect (fun z => if SourceTypical T n s b ω a z then 0 else 1) ≤
      sourceEffectiveHiddenTail T n (b+1) ω+sourceFitTail T n (b+1)/a := by
  let f := fun z : Reports Side (SourceTrialCount T n (b+1)) =>
    sourceNoncentralMass T n (sourceScheduledTrials T n) s (sourceLocalCenter T n)
      (sourceScheduledShift T n) (fun j => centralThird (T j)) (b+1)
      (sourceReportFlags T n (b+1) z) 0
  calc
    _ ≤ M.reports.expect (fun z =>
        (if HiddenCollectionConditions T n (sourceScheduledTrials T n) ω (b+1)
          (sourceReportFlags T n (b+1) z) then 0 else 1)+(if a≤f z then 1 else 0)) := by
      apply FiniteLaw.expect_mono
      intro z
      by_cases H : SourceTypical T n s b ω a z
      · rw [ite_eq_left H]
        split_ifs <;> norm_num
      · rw [ite_eq_right H]
        by_cases h : HiddenCollectionConditions T n (sourceScheduledTrials T n) ω (b+1)
          (sourceReportFlags T n (b+1) z)
        · have hf : ¬f z<a := fun hf => H ⟨h,hf⟩
          rw [ite_eq_left h,ite_eq_left (le_of_not_gt hf)]
          norm_num
        · rw [ite_eq_right h]
          split_ifs <;> norm_num
    _ ≤ _ := by
      rw [FiniteLaw.expect_add]
      apply add_le_add (source_hidden_conditions_effective_tail T n (b+1) M ω hw hp)
      apply (M.reports.positive_markov f (fun z => sourceNoncentralMass_nonneg T n _ s _ _ _ _ _ _) ha).trans
      exact div_le_div_of_nonneg_right
        (source_noncentral_average T n s b M hn hne hT he hL hroot) ha.le


end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Literal density of the source's unconditioned finite canonical oracle. -/
def sourceOracleDensity {Side Leaf : Type*} (T n : ℕ → ℕ) (s b : ℕ)
    (Z : Leaf → ℝ) (τ : Bool)
    (zx : Reports Side (SourceTrialCount T n (b+1)) × (Fin (SourceLeafCount T (b+1)) → Leaf)) : ℝ :=
  averagedDensity (PairedMechanisms.orientationsGiven zx.1)
    (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 τ) Z zx.2

theorem sourceOracleDensity_expansion {Side Leaf : Type*} (T n : ℕ → ℕ) (s b : ℕ)
    (Z : Leaf → ℝ) (τ : Bool)
    (z : Reports Side (SourceTrialCount T n (b+1))) (x : Fin (SourceLeafCount T (b+1)) → Leaf) :
    sourceOracleDensity T n s b Z τ (z,x)=multilinear (sourceOracleCoefficient T n s b z τ) Z x :=
  averagedDensity_expansion _ _ _ _

theorem sourceOracleDensity_nonneg {Side Leaf : Type*} (T n : ℕ → ℕ) (s b : ℕ)
    (Z : Leaf → ℝ) (hZ : ∀a,0 ≤ 1+Z a) (τ : Bool)
    (zx : Reports Side (SourceTrialCount T n (b+1)) × (Fin (SourceLeafCount T (b+1)) → Leaf)) :
    0 ≤ sourceOracleDensity T n s b Z τ zx := averagedDensity_nonneg _ _ _ hZ _

theorem sourceOracleDensity_mean {Side Leaf : Type*} [Fintype Leaf] (T n : ℕ → ℕ) (s b : ℕ)
    (P : FiniteLaw Leaf) (Z : Leaf → ℝ) (hZ : P.expect Z=0) (τ : Bool)
    (z : Reports Side (SourceTrialCount T n (b+1))) :
    (P.product (SourceLeafCount T (b+1))).expect (fun x => sourceOracleDensity T n s b Z τ (z,x))=1 :=
  averagedDensity_mean P (PairedMechanisms.orientationsGiven z) Z hZ
    (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 τ)

theorem source_canonical_centered_moment {Side Leaf : Type*} [Fintype Leaf]
    (T n : ℕ → ℕ) (s b k : ℕ) (P : FiniteLaw Leaf) (Z : Leaf → ℝ)
    (hk : 1 ≤ k) (hcenter : P.expect Z=0) {L : ℝ} (hL : 0<L)
    (hMoment : P.expect (fun a => |Z a|^(2*k)) ≤ L^(2*k))
    (hsmall : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b<1)
    (z : Reports Side (SourceTrialCount T n (b+1))) (τ : Bool) :
    (P.product (SourceLeafCount T (b+1))).expect
      (fun x => |sourceOracleDensity T n s b Z τ (z,x)-1|^(2*k)) ≤
        ((((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b)/
          (1-((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b))^k := by
  have he (x : Fin (SourceLeafCount T (b+1)) → Leaf) :
      sourceOracleDensity T n s b Z τ (z,x)-1=
        multilinear (nonconstantCoefficient (sourceOracleCoefficient T n s b z τ)) Z x := by
    rw [nonconstant_multilinear,sourceOracleCoefficient_empty,sourceOracleDensity_expansion]
  simp_rw [he]
  apply (multilinear_moment_scaled P Z k hk hcenter hL hMoment _ _).trans
  exact pow_le_pow_left₀ (multilinearEnergy_nonneg _ _)
    (source_canonical_centered_energy T n s b z τ (by positivity) hsmall) k

theorem source_canonical_signed_moment {Side Leaf : Type*} [Fintype Leaf]
    (T n : ℕ → ℕ) (hT : ∀j,0<T j) (s b R k : ℕ) (ω η a : ℝ) (ha : 0 ≤ a)
    (hη : ∀j<b+1,hiddenSmoothingBound (n j) s ω ≤ η)
    (P : FiniteLaw Leaf) (Z : Leaf → ℝ) (hk : 1 ≤ k) (hcenter : P.expect Z=0)
    {L : ℝ} (hL : 0<L) (hMoment : P.expect (fun a => |Z a|^(2*k)) ≤ L^(2*k))
    (hsmall : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b<1)
    (z : Reports Side (SourceTrialCount T n (b+1))) (hz : SourceTypical T n s b ω a z) :
    (P.product (SourceLeafCount T (b+1))).expect
      (fun x => |sourceOracleDensity T n s b Z true (z,x)-sourceOracleDensity T n s b Z false (z,x)|^(2*k)) ≤
        (sourceEnergyBudget T n s b R ω η a ((6*(2*k:ℕ):ℝ)*L))^k := by
  have he (x : Fin (SourceLeafCount T (b+1)) → Leaf) :
      |sourceOracleDensity T n s b Z true (z,x)-sourceOracleDensity T n s b Z false (z,x)|=
        |multilinear (sourceSignedCoefficient T n s b z) Z x| := by
    unfold sourceSignedCoefficient
    rw [multilinear_sub,←sourceOracleDensity_expansion,←sourceOracleDensity_expansion,abs_sub_comm]
  simp_rw [he]
  apply (multilinear_moment_scaled P Z k hk hcenter hL hMoment _ _).trans
  exact pow_le_pow_left₀ (multilinearEnergy_nonneg _ _)
    (source_canonical_energy T n hT s b R ω η a _ ha (by positivity) hsmall hη z hz) k

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem degreeForcedRoleEnergy_zero_of_lt (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b r : ℕ) (hr : r<2^(b+1))
    (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ) :
    degreeForcedRoleEnergy T n g s center globalShift A b r d incoming=0 := by
  have hi : IsEmpty (DegreeForcedRole T b r) := ⟨fun w => by
    obtain ⟨F⟩ := w.property.2
    have hh := F.leaf_lower
    rw [occupiedWindowTerm_leafCount,w.property.1] at hh
    omega⟩
  let := hi
  exact Finset.sum_eq_zero (fun w _ => isEmptyElim w)

/-- Below the genuine forced binary leaf threshold there is NO forced
 contribution; retaining even its coarse bound would lose the main exponent. -/
def sourceSharpDegreeBudget (T n : ℕ → ℕ) (s b r : ℕ) (ω η a : ℝ) : ℝ :=
  4*(3^((b+1)*r):ℕ)*
    (((SourceLeafCount T (b+1)).choose r:ℕ)*(3^((b+1)*r):ℕ)*(η^2+a^2)+
      if 2^(b+1)≤r then sourceForcedBudget T n s b r ω else 0)

theorem sourceSharpDegreeBudget_nonneg (T n : ℕ → ℕ) (s b r : ℕ) (ω η a : ℝ) :
    0 ≤ sourceSharpDegreeBudget T n s b r ω η a := by
  have h := sourceForcedBudget_nonneg T n s b r ω
  unfold sourceSharpDegreeBudget
  split_ifs <;> positivity

theorem source_canonical_sharp_degree_bound {Side : Type*} (T n : ℕ → ℕ) (hT : ∀j,0<T j)
    (s b r : ℕ) (ω η a : ℝ) (ha : 0≤a)
    (hη : ∀j<b+1,hiddenSmoothingBound (n j) s ω≤η)
    (z : Reports Side (SourceTrialCount T n (b+1))) (hz : SourceTypical T n s b ω a z) :
    (∑σ : Fin (SourceLeafCount T (b+1)) → Bool, if monomialDegree σ=r then
      (averagedCoefficient (PairedMechanisms.orientationsGiven z)
        (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 false) σ -
       averagedCoefficient (PairedMechanisms.orientationsGiven z)
        (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 true) σ)^2 else 0) ≤
      sourceSharpDegreeBudget T n s b r ω η a := by
  rw [source_canonical_degree_sum]
  apply (sourceCoefficient_degree_energy T n _ s _ _ (fun j => centralThird (T j)) b r
    (sourceReportFlags T n (b+1) z) 0 η
    (hiddenConditions_smoothingCap T n _ ω η s (b+1) hη _ hz.1)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add_right
    exact (sq_le_sq₀ (sourceNoncentralMass_nonneg T n _ s _ _ _ _ _ _) ha).mpr hz.2.le
  · by_cases hr : 2^(b+1)≤r
    · rw [ite_eq_left hr]
      exact degreeForcedRoleEnergy_bound T n _ hT s (sourceLocalCenter T n) _ _ _ (sourceScheduledShift_hasPlateau T n)
        (fun j => hiddenBinomialCap (n j) ω) (fun j => hiddenBinomialCap (sourceScheduledTrials T n j) ω)
        (fun j => hiddenBinomialCap_nonneg _ _) (fun j => hiddenBinomialCap_nonneg _ _)
        b r _ (hiddenConditions_binomialCaps T n _ ω (b+1) _ hz.1) 0
    · rw [ite_eq_right hr,degreeForcedRoleEnergy_zero_of_lt T n _ s _ _ _ b r (lt_of_not_ge hr)]
def sourceSharpEnergyBudget (T n : ℕ → ℕ) (s b R : ℕ) (ω η a w : ℝ) : ℝ :=
  (∑r∈Finset.range R, w^(2*r)*(if r=0 then 0 else sourceSharpDegreeBudget T n s b r ω η a))+
    4*(w^2*sourceSparseCount T s b)^R/(1-w^2*sourceSparseCount T s b)

/-- Complete signed energy, with finite low-degree forced-tree bound and
 the geometric high tail. No coefficient estimates remain as hypotheses. -/
theorem source_canonical_sharp_energy {Side : Type*} (T n : ℕ → ℕ) (hT : ∀j,0<T j)
    (s b R : ℕ) (ω η a w : ℝ) (ha : 0 ≤ a) (hw : 0 ≤ w)
    (hsmall : w^2*sourceSparseCount T s b<1)
    (hη : ∀j<b+1,hiddenSmoothingBound (n j) s ω ≤ η)
    (z : Reports Side (SourceTrialCount T n (b+1))) (hz : SourceTypical T n s b ω a z) :
    multilinearEnergy (sourceSignedCoefficient T n s b z) w ≤ sourceSharpEnergyBudget T n s b R ω η a w := by
  apply multilinearEnergy_low_high _ w (w^2*sourceSparseCount T s b) 4 hw (by positivity) hsmall
    (by norm_num) (fun r => if r=0 then 0 else sourceSharpDegreeBudget T n s b r ω η a)
  · intro r _
    by_cases hr : r=0
    · subst r
      rw [sourceSignedCoefficient_zero,ite_eq_left rfl]
    · rw [ite_eq_right hr]
      exact source_canonical_sharp_degree_bound T n hT s b r ω η a ha hη z hz
  · intro r _
    exact sourceSignedCoefficient_degree_geometric T n s b r z w
  · intro r
    split_ifs
    · rfl
    · exact sourceSharpDegreeBudget_nonneg T n s b r ω η a

theorem sourceSharpEnergyBudget_nonneg (T n : ℕ → ℕ) (s b R : ℕ) (ω η a w : ℝ)
    (hsmall : w^2*sourceSparseCount T s b<1) :
    0 ≤ sourceSharpEnergyBudget T n s b R ω η a w := by
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro r _
    apply mul_nonneg (pow_nonneg (sq_nonneg w) r |>.trans_eq (pow_mul w 2 r).symm)
    split_ifs
    · rfl
    · exact sourceSharpDegreeBudget_nonneg T n s b r ω η a
  · exact div_nonneg (by positivity) (sub_nonneg.mpr hsmall.le)

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

local instance (priority := 10000) {α β : Type*} : DecidableEq (α × β) := Classical.decEq _

theorem source_canonical_sharp_signed_moment {Side Leaf : Type*} [Fintype Leaf]
    (T n : ℕ → ℕ) (hT : ∀j,0<T j) (s b R k : ℕ) (ω η a : ℝ) (ha : 0 ≤ a)
    (hη : ∀j<b+1,hiddenSmoothingBound (n j) s ω ≤ η)
    (P : FiniteLaw Leaf) (Z : Leaf → ℝ) (hk : 1 ≤ k) (hcenter : P.expect Z=0)
    {L : ℝ} (hL : 0<L) (hMoment : P.expect (fun a => |Z a|^(2*k)) ≤ L^(2*k))
    (hsmall : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b<1)
    (z : Reports Side (SourceTrialCount T n (b+1))) (hz : SourceTypical T n s b ω a z) :
    (P.product (SourceLeafCount T (b+1))).expect
      (fun x => |sourceOracleDensity T n s b Z true (z,x)-sourceOracleDensity T n s b Z false (z,x)|^(2*k)) ≤
        (sourceSharpEnergyBudget T n s b R ω η a ((6*(2*k:ℕ):ℝ)*L))^k := by
  have he (x : Fin (SourceLeafCount T (b+1)) → Leaf) :
      |sourceOracleDensity T n s b Z true (z,x)-sourceOracleDensity T n s b Z false (z,x)|=
        |multilinear (sourceSignedCoefficient T n s b z) Z x| := by
    unfold sourceSignedCoefficient
    rw [multilinear_sub,←sourceOracleDensity_expansion,←sourceOracleDensity_expansion,abs_sub_comm]
  simp_rw [he]
  apply (multilinear_moment_scaled P Z k hk hcenter hL hMoment _ _).trans
  exact pow_le_pow_left₀ (multilinearEnergy_nonneg _ _)
    (source_canonical_sharp_energy T n hT s b R ω η a _ ha (by positivity) hsmall hη z hz) k


def sourceReferenceLaw {Side Leaf : Type*} [Fintype Side] [Fintype Leaf]
    (T n : ℕ → ℕ) (b : ℕ) (M : PairedMechanisms Side (SourceTrialCount T n (b+1)))
    (P : FiniteLaw Leaf) :
    FiniteLaw (Reports Side (SourceTrialCount T n (b+1)) × (Fin (SourceLeafCount T (b+1)) → Leaf)) :=
  M.reports.prod (P.product (SourceLeafCount T (b+1)))

theorem sourceOracleDensity_total {Side Leaf : Type*} [Fintype Side] [Fintype Leaf]
    (T n : ℕ → ℕ) (s b : ℕ) (M : PairedMechanisms Side (SourceTrialCount T n (b+1)))
    (P : FiniteLaw Leaf) (Z : Leaf → ℝ) (hZ : P.expect Z=0) (τ : Bool) :
    (sourceReferenceLaw T n b M P).expect (sourceOracleDensity T n s b Z τ)=1 := by
  rw [sourceReferenceLaw,FiniteLaw.expect_prod]
  simp_rw [sourceOracleDensity_mean T n s b P Z hZ τ]
  exact M.reports.expect_const 1

theorem sourceOracle_withDensity {Side Leaf : Type*} [Fintype Side] [Fintype Leaf]
    (T n : ℕ → ℕ) (s b : ℕ) (M : PairedMechanisms Side (SourceTrialCount T n (b+1)))
    (P Q : FiniteLaw Leaf) (Z : Leaf → ℝ) (hden : ∀a,Q.mass a=P.mass a*(1+Z a))
    (hZ : ∀a,0 ≤ 1+Z a) (hc : P.expect Z=0) (τ : Bool) :
    M.canonicalOracle P Q (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 τ)=
      (sourceReferenceLaw T n b M P).withDensity (sourceOracleDensity T n s b Z τ)
        (sourceOracleDensity_nonneg T n s b Z hZ τ)
        (sourceOracleDensity_total T n s b M P Z hc τ) := by
  apply FiniteLaw.ext
  funext zx
  exact M.canonicalOracle_density P Q Z hden _ zx.1 zx.2

def sourceTypicalSet {Side Leaf : Type*} [Fintype Side] [Fintype Leaf]
    (T n : ℕ → ℕ) (s b : ℕ) (ω a : ℝ) :
    Finset (Reports Side (SourceTrialCount T n (b+1)) × (Fin (SourceLeafCount T (b+1)) → Leaf)) :=
  Finset.univ.filter (fun x => SourceTypical T n s b ω a x.1)

theorem sourceTypicalSet_mass {Side Leaf : Type*} [Fintype Side] [Fintype Leaf]
    (T n : ℕ → ℕ) (s b : ℕ) (M : PairedMechanisms Side (SourceTrialCount T n (b+1)))
    (P Q : FiniteLaw Leaf) (ω a : ℝ) (τ : Bool) :
    (M.canonicalOracle P Q (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 τ)).eventMass
      (sourceTypicalSet T n s b ω a)ᶜ=
      M.reports.expect (fun z => if SourceTypical T n s b ω a z then 0 else 1) := by
  rw [FiniteLaw.eventMass_indicator]
  calc
    _ = (M.canonicalOracle P Q (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 τ)).expect
        (fun zx => if SourceTypical T n s b ω a zx.1 then 0 else 1) := by
      apply congrArg (FiniteLaw.expect _)
      funext zx
      simp [sourceTypicalSet]
    _ = _ := M.canonicalOracle_metadata P Q
      (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 τ)
      (fun z => if SourceTypical T n s b ω a z then 0 else 1)

def sourceCenteredBudget (T : ℕ → ℕ) (s b k : ℕ) (L : ℝ) : ℝ :=
  (((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b)/
    (1-((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b)

def sourceClippingCost (T n : ℕ → ℕ) (s b k : ℕ) (ω a L : ℝ) : ℝ :=
  sourceEffectiveHiddenTail T n (b+1) ω+sourceFitTail T n (b+1)/a+
    Real.sqrt (6*(4*sourceCenteredBudget T s b k L)^k)

theorem sourceCenteredBudget_nonneg (T : ℕ → ℕ) (s b k : ℕ) (L : ℝ)
    (hsmall : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b<1) :
    0 ≤ sourceCenteredBudget T s b k L :=
  div_nonneg (by positivity) (sub_nonneg.mpr hsmall.le)

theorem sourceCenteredBudget_le_one (T : ℕ → ℕ) (s b k : ℕ) (L : ℝ)
    (hscale : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b≤1/2) :
    sourceCenteredBudget T s b k L ≤ 1 := by
  have hsmall : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b<1 := by linarith
  apply (div_le_iff₀ (sub_pos.mpr hsmall)).mpr
  linarith

theorem source_reference_centered_moment {Side Leaf : Type*} [Fintype Side] [Fintype Leaf]
    (T n : ℕ → ℕ) (s b k : ℕ) (M : PairedMechanisms Side (SourceTrialCount T n (b+1)))
    (P : FiniteLaw Leaf) (Z : Leaf → ℝ) (hk : 1 ≤ k) (hc : P.expect Z=0)
    {L : ℝ} (hL : 0<L) (hMoment : P.expect (fun a => |Z a|^(2*k)) ≤ L^(2*k))
    (hsmall : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b<1) (τ : Bool) :
    (sourceReferenceLaw T n b M P).expect
      (fun zx => |sourceOracleDensity T n s b Z τ zx-1|^(2*k)) ≤ (sourceCenteredBudget T s b k L)^k := by
  rw [sourceReferenceLaw,FiniteLaw.expect_prod]
  calc
    _ ≤ M.reports.expect (fun _ => (sourceCenteredBudget T s b k L)^k) :=
      M.reports.expect_mono (fun z => source_canonical_centered_moment T n s b k P Z hk hc hL hMoment hsmall z τ)
    _ = _ := M.reports.expect_const _

theorem source_reference_signed_moment {Side Leaf : Type*} [Fintype Side] [Fintype Leaf]
    (T n : ℕ → ℕ) (hTpos : ∀j,0<T j) (s b R k : ℕ)
    (M : PairedMechanisms Side (SourceTrialCount T n (b+1))) (P : FiniteLaw Leaf)
    (Z : Leaf → ℝ) (ω a η L : ℝ) (ha : 0≤a) (hL : 0<L) (hk : 1 ≤ k) (hc : P.expect Z=0)
    (hMoment : P.expect (fun a => |Z a|^(2*k)) ≤ L^(2*k))
    (hsmall : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b<1)
    (hη : ∀j<b+1,hiddenSmoothingBound (n j) s ω ≤ η) :
    (sourceReferenceLaw T n b M P).expect (fun zx =>
      |if zx∈sourceTypicalSet T n s b ω a then sourceOracleDensity T n s b Z true zx-
        sourceOracleDensity T n s b Z false zx else 0|^(2*k)) ≤
      (sourceSharpEnergyBudget T n s b R ω η a ((6*(2*k:ℕ):ℝ)*L))^k := by
  rw [sourceReferenceLaw,FiniteLaw.expect_prod]
  have hV := sourceSharpEnergyBudget_nonneg T n s b R ω η a ((6*(2*k:ℕ):ℝ)*L) hsmall
  calc
    _ ≤ M.reports.expect (fun _ => (sourceSharpEnergyBudget T n s b R ω η a ((6*(2*k:ℕ):ℝ)*L))^k) := by
      apply M.reports.expect_mono
      intro z
      by_cases hz : SourceTypical T n s b ω a z
      · simp only [sourceTypicalSet,Finset.mem_filter,Finset.mem_univ,true_and,hz,ite_true]
        exact source_canonical_sharp_signed_moment T n hTpos s b R k ω η a ha hη P Z hk hc hL hMoment hsmall z hz
      · simp only [sourceTypicalSet,Finset.mem_filter,Finset.mem_univ,true_and,hz,ite_false,
          abs_zero,zero_pow (by omega : 2*k≠0),FiniteLaw.expect_const]
        exact pow_nonneg hV k
    _ = _ := M.reports.expect_const _

theorem source_reference_clipped_exists {Side Leaf : Type*} [Fintype Side] [Fintype Leaf]
    (T n : ℕ → ℕ) (hTpos : ∀j,0<T j) (s b R k : ℕ)
    (M : PairedMechanisms Side (SourceTrialCount T n (b+1))) (P : FiniteLaw Leaf)
    (Z : Leaf → ℝ) (hZ : ∀a,0 ≤ 1+Z a) (hc : P.expect Z=0)
    (ω a η L : ℝ) (ha : 0≤a) (hL : 0<L) (hk : 1≤k)
    (hMoment : P.expect (fun a => |Z a|^(2*k)) ≤ L^(2*k))
    (hscale : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b ≤ 1/2)
    (hη : ∀j<b+1,hiddenSmoothingBound (n j) s ω ≤ η)
    (hB : ∀τ,((sourceReferenceLaw T n b M P).withDensity (sourceOracleDensity T n s b Z τ)
      (sourceOracleDensity_nonneg T n s b Z hZ τ) (sourceOracleDensity_total T n s b M P Z hc τ)).eventMass
        (sourceTypicalSet T n s b ω a)ᶜ ≤ sourceEffectiveHiddenTail T n (b+1) ω+sourceFitTail T n (b+1)/a)
    (herror : sourceClippingCost T n s b k ω a L ≤ 1/2) :
    Nonempty (ClippedOracle
      ((sourceReferenceLaw T n b M P).withDensity (sourceOracleDensity T n s b Z false)
        (sourceOracleDensity_nonneg T n s b Z hZ false) (sourceOracleDensity_total T n s b M P Z hc false))
      ((sourceReferenceLaw T n b M P).withDensity (sourceOracleDensity T n s b Z true)
        (sourceOracleDensity_nonneg T n s b Z hZ true) (sourceOracleDensity_total T n s b M P Z hc true))
      k (sourceClippingCost T n s b k ω a L)
      (64*sourceSharpEnergyBudget T n s b R ω η a ((6*(2*k:ℕ):ℝ)*L))) := by
  have hsmall : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b<1 := by linarith
  exact FiniteLaw.exists_clippedOracle (sourceReferenceLaw T n b M P)
    (sourceOracleDensity T n s b Z false) (sourceOracleDensity T n s b Z true)
    (sourceOracleDensity_nonneg T n s b Z hZ false) (sourceOracleDensity_nonneg T n s b Z hZ true)
    (sourceOracleDensity_total T n s b M P Z hc false) (sourceOracleDensity_total T n s b M P Z hc true)
    (sourceTypicalSet T n s b ω a) _ (hB false) (hB true) k hk (sourceCenteredBudget T s b k L)
    (sourceCenteredBudget_nonneg T s b k L hsmall) (sourceCenteredBudget_le_one T s b k L hscale)
    (source_reference_centered_moment T n s b k M P Z hk hc hL hMoment hsmall false)
    (source_reference_centered_moment T n s b k M P Z hk hc hL hMoment hsmall true)
    _ (sourceSharpEnergyBudget_nonneg T n s b R ω η a ((6*(2*k:ℕ):ℝ)*L) hsmall)
    (source_reference_signed_moment T n hTpos s b R k M P Z ω a η L ha hL hk hc hMoment hsmall hη) herror

/-- Complete finite quantitative clipping of the actual recursive source
 oracle. All analytic budgets here are explicit arithmetic in the literal
 branching/trial counts; no coefficient or oracle-existence premise remains. -/
theorem source_clippedOracle_exists {Side Leaf : Type*} [Fintype Side] [Fintype Leaf]
    (T n : ℕ → ℕ) (hTpos : ∀j,0<T j) (s b R k : ℕ)
    (M : PairedMechanisms Side (SourceTrialCount T n (b+1))) (P Q : FiniteLaw Leaf)
    (Z : Leaf → ℝ) (hden : ∀a,Q.mass a=P.mass a*(1+Z a)) (hZ : ∀a,0 ≤ 1+Z a)
    (ω a η L : ℝ) (ha : 0<a) (hL : 0<L)
    (hw : ∀i,M.hiddenWeight i=ω) (hp : ω^2∈Set.Icc 0 1)
    (hn : ∀j,j<b → 0<n j) (hne : ∀j,j<b → Even (n j))
    (hT : ∀j≤b,24≤T j) (he : ∀j≤b,Even (T j)) (hMotif : ∀j≤b,24*2^s≤T j)
    (hroot : 4*(n b+1)≤T b) (hk : 1 ≤ k)
    (hMoment : P.expect (fun a => |Z a|^(2*k)) ≤ L^(2*k))
    (hscale : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b ≤ 1/2)
    (hη : ∀j<b+1,hiddenSmoothingBound (n j) s ω ≤ η)
    (herror : sourceClippingCost T n s b k ω a L ≤ 1/2) :
    Nonempty (ClippedOracle
      (M.canonicalOracle P Q (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 false))
      (M.canonicalOracle P Q (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 true))
      k (sourceClippingCost T n s b k ω a L)
      (64*sourceSharpEnergyBudget T n s b R ω η a ((6*(2*k:ℕ):ℝ)*L))) := by
  have hc := FiniteLaw.density_score_centered P Q Z hden
  have hB (τ : Bool) : ((sourceReferenceLaw T n b M P).withDensity (sourceOracleDensity T n s b Z τ)
      (sourceOracleDensity_nonneg T n s b Z hZ τ) (sourceOracleDensity_total T n s b M P Z hc τ)).eventMass
        (sourceTypicalSet T n s b ω a)ᶜ ≤ sourceEffectiveHiddenTail T n (b+1) ω+sourceFitTail T n (b+1)/a := by
    rw [←sourceOracle_withDensity T n s b M P Q Z hden hZ hc τ,sourceTypicalSet_mass]
    exact source_typical_effective_failure T n s b M ω a ha hw hp hn hne hT he hMotif hroot
  rw [sourceOracle_withDensity T n s b M P Q Z hden hZ hc false,
    sourceOracle_withDensity T n s b M P Q Z hden hZ hc true]
  exact source_reference_clipped_exists T n hTpos s b R k M P Z hZ hc ω a η L ha.le hL hk hMoment hscale hη hB herror

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

namespace ClippedOracle
variable {α β : Type*} [Fintype α] [Fintype β]
    {P Q : FiniteLaw α} {k : ℕ} {e V : ℝ}

def prod (C : ClippedOracle P Q k e V) (R : FiniteLaw β) :
    ClippedOracle (P.prod R) (Q.prod R) k e V where
  first := C.first.prod R
  second := C.second.prod R
  score := fun x => C.score x.1
  density x := by
    change C.second.mass x.1*R.mass x.2=(C.first.mass x.1*R.mass x.2)*(1+C.score x.1)
    rw [C.density]; ring
  likelihood_nonneg x := C.likelihood_nonneg x.1
  centered := by
    rw [FiniteLaw.expect_prod]
    simp_rw [FiniteLaw.expect_const]
    exact C.centered
  moment := by
    unfold FiniteLaw.evenMomentSq
    rw [FiniteLaw.expect_prod]
    simp_rw [FiniteLaw.expect_const]
    exact C.moment
  first_tv := by rw [FiniteLaw.tv_prod_eq_left]; exact C.first_tv
  second_tv := by rw [FiniteLaw.tv_prod_eq_left]; exact C.second_tv
end ClippedOracle

theorem ApproximatesTrace.of_tv {α : Type*} [Fintype α]
    {q E e : ℝ} {P Q : FiniteLaw α} {f : α → List Bool} {w : List Bool}
    (hP : ApproximatesTrace q P f w E) (htv : Q.tv P ≤ e) :
    ApproximatesTrace q Q f w (e+E) := by
  intro F hF
  exact (abs_sub_le (Q.expect (fun a => F (f a))) (P.expect (fun a => F (f a)))
    (listDeletionExpectation q w F)).trans (add_le_add
      ((FiniteLaw.abs_expect_sub_le_tv Q P _ (fun a => hF _)).trans htv) (hP F hF))

/-- A finite genuine approximate oracle pair with a common complete-trace
 decoder. It does not include an overlap or any unproved scale conclusion. -/
structure OracleTracePair (q : ℝ) (x y : List Bool) (k : ℕ) (E V : ℝ) where
  Outcome : Type
  finiteOutcome : Fintype Outcome
  first : @FiniteLaw Outcome finiteOutcome
  second : @FiniteLaw Outcome finiteOutcome
  decode : Outcome → List Bool
  first_simulation : @ApproximatesTrace Outcome finiteOutcome q first decode x E
  second_simulation : @ApproximatesTrace Outcome finiteOutcome q second decode y E
  score : Outcome → ℝ
  density : ∀a,second.mass a=first.mass a*(1+score a)
  likelihood_nonneg : ∀a,0≤1+score a
  centered : first.expect score=0
  moment : @FiniteLaw.evenMomentSq Outcome finiteOutcome first score k ≤ V

/-- The clipping and independent filler metadata preserve the source's fixed
 public trace decoder. -/
theorem source_clipped_simulation {Side Leaf : Type} [Fintype Side] [Fintype Leaf]
    {q E e V : ℝ} (hq : q∈Set.Icc 0 1) (hE : 0≤E)
    (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool) (b k : ℕ)
    (H : SourceLayoutMargins s P T n h b)
    (hP : P b=n b*(2*h b+1)+T b) (hT : Even (T b))
    (hlarge : 4*(n b+1)≤T b) (hmotif : 8*2^s≤T b)
    (hn : ∀j<b,0<n j)
    (M : PairedMechanisms Side (SourceTrialCount T n (b+1)))
    (R : Fin (SourceFillerCount T (b+1)) → FiniteLaw Side) (A B : FiniteLaw Leaf)
    (f : Side → List Bool) (g : Leaf → List Bool)
    (hU : ∀j,SimulatesTrace q (M.first j) f (sourceFlatTrialWord s P T n h atom (b+1) false j))
    (hV : ∀j,SimulatesTrace q (M.second j) f (sourceFlatTrialWord s P T n h atom (b+1) true j))
    (hW : ∀j,SimulatesTrace q (R j) f (sourceFlatFillerWord s P T n h atom (b+1) j))
    (hA : ApproximatesTrace q A g (atom false) E) (hB : ApproximatesTrace q B g (atom true) E)
    (C : ClippedOracle
      (M.canonicalOracle A B (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 false))
      (M.canonicalOracle A B (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 true)) k e V) :
    Nonempty (OracleTracePair q (sourceBlockWord s P atom (b+1) false)
      (sourceBlockWord s P atom (b+1) true) k
      (e+(SourceLeafCount T (b+1):ℝ)*E+sourceFitTail T n (b+1)) V) := by
  let D := C.prod (FiniteLaw.coordinateProduct R)
  refine ⟨{
    Outcome := (Reports Side (SourceTrialCount T n (b+1)) × (Fin (SourceLeafCount T (b+1)) → Leaf)) ×
      (Fin (SourceFillerCount T (b+1)) → Side)
    finiteOutcome := inferInstance
    first := D.first
    second := D.second
    decode := sourceOracleDecode T n (b+1) f g
    score := D.score
    density := D.density
    likelihood_nonneg := D.likelihood_nonneg
    centered := D.centered
    moment := D.moment
    first_simulation := ?_
    second_simulation := ?_
  }⟩
  · simpa only [add_assoc] using
      (source_canonical_simulation hq hE s P T n h atom b H hP hT hlarge hmotif hn M R A B f g hU hV hW hA hB false).of_tv D.first_tv
  · simpa only [add_assoc] using
      (source_canonical_simulation hq hE s P T n h atom b H hP hT hlarge hmotif hn M R A B f g hU hV hW hA hB true).of_tv D.second_tv

end TraceReconstruction


noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α : Type*} [Fintype α]

theorem expect_nonneg (P : FiniteLaw α) (F : α → ℝ) (hF : ∀a,0≤F a) : 0≤P.expect F :=
  Finset.sum_nonneg (fun a _ => mul_nonneg (P.nonneg a) (hF a))

theorem evenMomentSq_nonneg (P : FiniteLaw α) (F : α → ℝ) (k : ℕ) :
    0≤P.evenMomentSq F k := Real.rpow_nonneg (P.expect_nonneg _ (fun _ => by positivity)) _

theorem evenMomentSq_pow (P : FiniteLaw α) (F : α → ℝ) (k : ℕ) (hk : 1≤k) :
    (P.evenMomentSq F k)^k=P.expect (fun a => |F a|^(2*k)) := by
  unfold evenMomentSq
  rw [one_div,Real.rpow_inv_natCast_pow (P.expect_nonneg _ (fun _ => by positivity)) (by omega)]

theorem expect_even_pow_le_of_moment (P : FiniteLaw α) (F : α → ℝ) (k : ℕ) (hk : 1≤k)
    {V : ℝ} (h : P.evenMomentSq F k≤V) :
    P.expect (fun a => |F a|^(2*k))≤V^k := by
  rw [←P.evenMomentSq_pow F k hk]
  exact pow_le_pow_left₀ (P.evenMomentSq_nonneg F k) h k

theorem secondMoment_le_evenMomentSq (P : FiniteLaw α) (F : α → ℝ) (k : ℕ) (hk : 1≤k) :
    P.expect (fun a => F a^2)≤P.evenMomentSq F k := by
  have hn : 0≤P.expect (fun a => F a^2) := P.expect_nonneg _ (fun _ => sq_nonneg _)
  have hj := P.abs_expect_pow_le (fun a => F a^2) k
  simp only [abs_of_nonneg hn,abs_pow,←pow_mul] at hj
  have hr := Real.rpow_le_rpow (pow_nonneg hn k) hj (by positivity : 0≤(k:ℝ)⁻¹)
  rw [Real.pow_rpow_inv_natCast hn (by omega)] at hr
  simpa only [evenMomentSq,one_div] using hr

theorem affinity_coordinateProduct {n : ℕ} (P Q : Fin n → FiniteLaw α) :
    (coordinateProduct P).affinity (coordinateProduct Q)=∏i,(P i).affinity (Q i) := by
  unfold affinity coordinateProduct
  simp only
  have he (a : Fin n → α) :
      Real.sqrt (∏i,(P i).mass (a i))*Real.sqrt (∏i,(Q i).mass (a i))=
        ∏i,Real.sqrt ((P i).mass (a i))*Real.sqrt ((Q i).mass (a i)) := by
    rw [Real.sqrt_prod _ (fun i _ => (P i).nonneg (a i)),
      Real.sqrt_prod _ (fun i _ => (Q i).nonneg (a i)),Finset.prod_mul_distrib]
  simp_rw [he]
  exact (Fintype.prod_sum (fun (i : Fin n) a => Real.sqrt ((P i).mass a)*Real.sqrt ((Q i).mass a))).symm

theorem one_sub_prod_le_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (h0 : ∀i∈S,0≤f i) (h1 : ∀i∈S,f i≤1) :
    1-∏i∈S,f i≤∑i∈S,(1-f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha,Finset.sum_insert ha]
    have H := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hs : 0≤∑i∈S,(1-f i) := Finset.sum_nonneg (fun i hi => sub_nonneg.mpr (h1 i (Finset.mem_insert_of_mem hi)))
    have hm := mul_le_mul_of_nonneg_left H (h0 a (Finset.mem_insert_self a S))
    have hm' := mul_le_mul_of_nonneg_right (h1 a (Finset.mem_insert_self a S)) hs
    nlinarith

theorem hellingerSq_coordinateProduct_le {n : ℕ} (P Q : Fin n → FiniteLaw α) :
    (coordinateProduct P).hellingerSq (coordinateProduct Q)≤∑i,(P i).hellingerSq (Q i) := by
  simp_rw [hellingerSq_eq]
  rw [affinity_coordinateProduct]
  have h := one_sub_prod_le_sum Finset.univ (fun i => (P i).affinity (Q i))
    (fun i _ => affinity_nonneg _ _) (fun i _ => affinity_le_one _ _)
  have he : (∑i,(2-2*(P i).affinity (Q i)))=2*∑i,(1-(P i).affinity (Q i)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  rw [he]
  linarith

@[simp] theorem hellingerSq_self (P : FiniteLaw α) : P.hellingerSq P=0 := by
  simp [hellingerSq]

theorem hellingerSq_symm (P Q : FiniteLaw α) : P.hellingerSq Q=Q.hellingerSq P := by
  apply Finset.sum_congr rfl; intro a _; ring

/-- Only differing coordinates cost squared Hellinger distance. This estimate
 does not pay for pure filler coordinates, nor assume independence of traces
 after their common concatenating decoder. -/
theorem tv_mixedProduct_le {n : ℕ} (P Q : FiniteLaw α) (Z : α → ℝ)
    (hden : ∀a,Q.mass a=P.mass a*(1+Z a)) (k : ℕ) (hk : 1≤k)
    {V : ℝ} (hM : P.evenMomentSq Z k≤V) (τ σ : Fin n → Bool) :
    (coordinateProduct (fun i => if τ i then Q else P)).tv
      (coordinateProduct (fun i => if σ i then Q else P))≤
        Real.sqrt ((∑i,if τ i=σ i then (0:ℝ) else 1)*V) := by
  have hH : P.hellingerSq Q≤V := (P.hellingerSq_le_score Q Z hden).trans
    ((P.secondMoment_le_evenMomentSq Z k hk).trans hM)
  apply (tv_le_sqrt_hellingerSq _ _).trans
  apply Real.sqrt_le_sqrt
  apply (hellingerSq_coordinateProduct_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  cases τ i <;> cases σ i <;> simp only [Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true,
    zero_mul,one_mul,hellingerSq_self,le_refl]
  · exact hH
  · rw [hellingerSq_symm]; exact hH

end TraceReconstruction.FiniteLaw


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Literal recursive source oracle with actual complete-trace side laws.
 All remaining hypotheses here are explicit parameter inequalities, the old
 leaf oracle, and its genuine repeated-word overlap invariant. -/
theorem actual_source_oracle {Leaf : Type} [Fintype Leaf]
    {q E : ℝ} (hq : q∈Set.Icc 0 1) (hE : 0≤E)
    (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool) (b R k : ℕ)
    (H : SourceLayoutMargins s P T n h b)
    (hTpos : ∀j,0<T j) (hP : P b=n b*(2*h b+1)+T b)
    (hn : ∀j<b,0<n j) (hT : ∀j≤b,24≤T j) (he : ∀j≤b,Even (T j))
    (hMotif : ∀j≤b,24*2^s≤T j) (hroot : 4*(n b+1)≤T b)
    (A B : FiniteLaw Leaf) (g : Leaf → List Bool) (Z : Leaf → ℝ)
    (hden : ∀a,B.mass a=A.mass a*(1+Z a)) (hZ : ∀a,0≤1+Z a)
    (hA : ApproximatesTrace q A g (atom false) E) (hB : ApproximatesTrace q B g (atom true) E)
    (ω a η L : ℝ) (ha : 0<a) (hL : 0<L) (hω : ω∈Set.Ioo 0 1)
    (hov : ∀j<b+1,ω≤listTraceOverlap q hq
      (pureAtomRun (sourceBlockWord s P atom j false) (h j))
      (pureAtomRun (sourceBlockWord s P atom j false) (h j+1)))
    (hk : 1≤k) (hMoment : A.expect (fun a => |Z a|^(2*k))≤L^(2*k))
    (hscale : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b≤1/2)
    (hη : ∀j<b+1,hiddenSmoothingBound (n j) s ω≤η)
    (herror : sourceClippingCost T n s b k ω a L≤1/2) :
    Nonempty (OracleTracePair q (sourceBlockWord s P atom (b+1) false)
      (sourceBlockWord s P atom (b+1) true) k
      (sourceClippingCost T n s b k ω a L+(SourceLeafCount T (b+1):ℝ)*E+sourceFitTail T n (b+1))
      (64*sourceSharpEnergyBudget T n s b R ω η a ((6*(2*k:ℕ):ℝ)*L))) := by
  let U := sourceFlatTrialWord s P T n h atom (b+1) false
  let V := sourceFlatTrialWord s P T n h atom (b+1) true
  let W := sourceFlatFillerWord s P T n h atom (b+1)
  obtain ⟨mU,hmU⟩ := finite_word_bound U
  obtain ⟨mV,hmV⟩ := finite_word_bound V
  obtain ⟨mW,hmW⟩ := finite_word_bound W
  let m := max mU (max mV mW)
  have hU (j) : (U j).length ≤ m := (hmU j).trans (le_max_left _ _)
  have hV (j) : (V j).length ≤ m := (hmV j).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hW (j) : (W j).length ≤ m := (hmW j).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hov' (j) : ω≤listTraceOverlap q hq (U j) (V j) :=
    sourceTrialWord_overlap hq s P T n h atom (b+1) hov (finEnumeration _ j)
  let M := tracePairedMechanisms hq hω.1 U V m hU hV hov'
  let F : Fin (SourceFillerCount T (b+1)) → FiniteLaw (BoundedTrace m) :=
    fun j => listTraceLaw q hq (W j) m (hW j)
  have hp : ω^2∈Set.Icc 0 1 := ⟨sq_nonneg ω,by nlinarith [hω.1,hω.2]⟩
  obtain ⟨C⟩ := source_clippedOracle_exists T n hTpos s b R k M A B Z hden hZ ω a η L ha hL
    (fun _ => rfl) hp hn H.even_trials hT he hMotif hroot hk hMoment hscale hη herror
  apply source_clipped_simulation hq hE s P T n h atom b k H hP (he b le_rfl) hroot
    (by nlinarith [hMotif b le_rfl]) hn M F A B Subtype.val g
    (fun j => listTraceLaw_simulates q hq (U j) m (hU j))
    (fun j => listTraceLaw_simulates q hq (V j) m (hV j))
    (fun j => listTraceLaw_simulates q hq (W j) m (hW j)) hA hB C

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
