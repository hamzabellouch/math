import Mathlib
import OAI.Probability.SKFluctuations.ClockPairRepresentation

namespace OAI

/-! Clock Zero Refinement. -/

noncomputable section


namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S]

 theorem shiftedContinuation_zero_clock (F : (ι → ℝ) → ℝ) {m : ℝ} (hm : m ≠ 0) :
    shiftedContinuation (Measure.pi fun _ : ι => gaussianReal 0 0) m F = F := by
  funext x
  rw [isotropicGaussian_zero]
  simp [shiftedContinuation,hm]

 theorem shiftedMean_zero_clock (F A : (ι → ℝ) → ℝ) (m : ℝ) :
    shiftedMean (Measure.pi fun _ : ι => gaussianReal 0 0) m F A = A := by
  funext x
  rw [isotropicGaussian_zero]
  simp [shiftedMean,tiltedMean]

 theorem prefixContinuation_zero_insert (pre post : List (GaussianStep ι))
    (F : (ι → ℝ) → ℝ) {m : ℝ} (hm : m ≠ 0) :
    prefixContinuation (pre++(m,0)::post) F = prefixContinuation (pre++post) F := by
  rw [prefixContinuation_append,prefixContinuation_append]
  simp only [prefixContinuation,Pi.zero_apply,shiftedContinuation_zero_clock _ hm]

 theorem prefixTest_zero_insert (pre post : List (GaussianStep ι))
    (F A : (ι → ℝ) → ℝ) {m : ℝ} (hm : m ≠ 0) :
    prefixTest (pre++(m,0)::post) F A = prefixTest (pre++post) F A := by
  rw [prefixTest_append,prefixTest_append]
  simp only [prefixContinuation,prefixTest,Pi.zero_apply,
    shiftedContinuation_zero_clock _ hm,shiftedMean_zero_clock]

 

inductive ZeroClockRefinement : List (GaussianStep ι) → List (GaussianStep ι) → Prop
  | refl (L) : ZeroClockRefinement L L
  | insert (pre post : List (GaussianStep ι)) (m : ℝ) (hm : 0 < m) :
      ZeroClockRefinement (pre++post) (pre++(m,0)::post)
  | trans {L M N} : ZeroClockRefinement L M → ZeroClockRefinement M N → ZeroClockRefinement L N

 theorem ZeroClockRefinement.continuation_test {L M : List (GaussianStep ι)}
    (h : ZeroClockRefinement L M) (F A : (ι → ℝ) → ℝ) :
    prefixContinuation L F = prefixContinuation M F ∧ prefixTest L F A = prefixTest M F A := by
  induction h with
  | refl => exact ⟨rfl,rfl⟩
  | insert pre post m hm =>
    exact ⟨(prefixContinuation_zero_insert pre post F hm.ne').symm,
      (prefixTest_zero_insert pre post F A hm.ne').symm⟩
  | trans h₁ h₂ ih₁ ih₂ => exact ⟨ih₁.1.trans ih₂.1,ih₁.2.trans ih₂.2⟩

 theorem ZeroClockRefinement.hierarchy {L M : List (GaussianStep ι)}
    (h : ZeroClockRefinement L M) (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) :
    gaussianHierarchy w φ L = gaussianHierarchy w φ M ∧
    gaussianHierarchyMean w φ A L = gaussianHierarchyMean w φ A M := by
  have hh := h.continuation_test (gaussianHierarchy w φ []) (gaussianHierarchyMean w φ A [])
  simpa only [prefixContinuation_hierarchy,gaussianHierarchyMean_prefix,List.append_nil] using hh

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*}

 theorem ZeroClockRefinement.cons {L M : List (GaussianStep ι)}
    (h : ZeroClockRefinement L M) (s : GaussianStep ι) :
    ZeroClockRefinement (s::L) (s::M) := by
  induction h with
  | refl L => exact .refl _
  | insert pre post m hm =>
    simpa only [List.cons_append] using ZeroClockRefinement.insert (s::pre) post m hm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

abbrev PairedClockStep (ι : Type*) := ℝ × ((ι → ℝ≥0) × (ι → ℝ≥0))

def commonClockSteps : List (GaussianStep ι) → List (GaussianStep ι) → List (PairedClockStep ι)
  | [], B => B.map (fun b => (b.1,0,b.2))
  | A, [] => A.map (fun a => (a.1,a.2,0))
  | a::A, b::B => if a.1 ≤ b.1 then (a.1,a.2,0)::commonClockSteps A (b::B)
      else (b.1,0,b.2)::commonClockSteps (a::A) B
termination_by A B => A.length+B.length

def leftClockSteps (L : List (PairedClockStep ι)) : List (GaussianStep ι) :=
  L.map (fun t => (t.1,t.2.1))

def rightClockSteps (L : List (PairedClockStep ι)) : List (GaussianStep ι) :=
  L.map (fun t => (t.1,t.2.2))

 theorem zeroClockSteps_refines (L : List (GaussianStep ι))
    (hL : ∀ s ∈ L, 0 < s.1) : ZeroClockRefinement (ι := ι) [] (L.map fun s => (s.1,0)) := by
  induction L with
  | nil => exact .refl _
  | cons s L ih =>
    have ht := ih (fun t ht => hL t (by simp [ht]))
    apply ht.trans
    simpa using ZeroClockRefinement.insert [] (L.map fun t => (t.1,0)) s.1 (hL s (by simp))

 theorem commonClockSteps_refines (A B : List (GaussianStep ι))
    (hA : ∀ s ∈ A, 0 < s.1) (hB : ∀ s ∈ B, 0 < s.1) :
    ZeroClockRefinement A (leftClockSteps (commonClockSteps A B)) ∧
    ZeroClockRefinement B (rightClockSteps (commonClockSteps A B)) := by
  cases A with
  | nil =>
    simp only [commonClockSteps,leftClockSteps,rightClockSteps,List.map_map,Function.comp_def]
    constructor
    · exact zeroClockSteps_refines B hB
    · simpa only [Prod.mk.eta,List.map_id_fun', id_eq] using (ZeroClockRefinement.refl B)
  | cons a A =>
    cases B with
    | nil =>
      simp only [commonClockSteps,leftClockSteps,rightClockSteps,List.map_map,Function.comp_def]
      constructor
      · simpa only [Prod.mk.eta,List.map_id_fun', id_eq] using (ZeroClockRefinement.refl (a::A))
      · exact zeroClockSteps_refines (a::A) hA
    | cons b B =>
      rw [commonClockSteps]
      split_ifs with hab
      · have ih := commonClockSteps_refines A (b::B) (fun s hs => hA s (by simp [hs])) hB
        constructor
        · exact ih.1.cons a
        · exact ih.2.trans (by simpa [rightClockSteps] using (ZeroClockRefinement.insert []
            (rightClockSteps (commonClockSteps A (b::B))) a.1 (hA a (by simp))))
      · have ih := commonClockSteps_refines (a::A) B hA (fun s hs => hB s (by simp [hs]))
        constructor
        · exact ih.1.trans (by simpa [leftClockSteps] using (ZeroClockRefinement.insert []
            (leftClockSteps (commonClockSteps (a::A) B)) b.1 (hB b (by simp))))
        · exact ih.2.cons b
termination_by A.length+B.length

 theorem commonClockSteps_same_masses (A B : List (GaussianStep ι)) :
    (leftClockSteps (commonClockSteps A B)).map Prod.fst =
      (rightClockSteps (commonClockSteps A B)).map Prod.fst := by
  simp only [leftClockSteps,rightClockSteps,List.map_map,Function.comp_def]

 theorem OrderedSteps.map_variance {κ : Type*} {a : ℝ} {L : List (GaussianStep ι)}
    (hL : OrderedSteps a L) (f : GaussianStep ι → κ → ℝ≥0) :
    OrderedSteps a (L.map fun s => (s.1,f s)) := by
  induction L generalizing a with
  | nil => exact hL
  | cons s L ih => exact ⟨hL.1,hL.2.1,hL.2.2.1,ih hL.2.2.2⟩

 theorem commonClockSteps_ordered {a : ℝ} (A B : List (GaussianStep ι))
    (hA : OrderedSteps a A) (hB : OrderedSteps a B) :
    OrderedSteps a (leftClockSteps (commonClockSteps A B)) ∧
      OrderedSteps a (rightClockSteps (commonClockSteps A B)) := by
  cases A with
  | nil =>
    simp only [commonClockSteps,leftClockSteps,rightClockSteps,List.map_map,Function.comp_def]
    constructor
    · exact hB.map_variance (fun _ => 0)
    · simpa only [Prod.mk.eta,List.map_id_fun',id_eq] using hB
  | cons b A =>
    cases B with
    | nil =>
      simp only [commonClockSteps,leftClockSteps,rightClockSteps,List.map_map,Function.comp_def]
      constructor
      · simpa only [Prod.mk.eta,List.map_id_fun',id_eq] using hA
      · exact hA.map_variance (fun _ => 0)
    | cons c B =>
      rw [commonClockSteps]
      split_ifs with hbc
      · have hB' : OrderedSteps b.1 (c::B) := ⟨hA.2.2.1.le,hbc,hB.2.2⟩
        have hh := commonClockSteps_ordered A (c::B) hA.2.2.2 hB'
        exact ⟨⟨hA.1,hA.2.1,hA.2.2.1,hh.1⟩,⟨hA.1,hA.2.1,hA.2.2.1,hh.2⟩⟩
      · have hA' : OrderedSteps c.1 (b::A) := ⟨hB.2.2.1.le,(le_of_not_ge hbc),hA.2.2⟩
        have hh := commonClockSteps_ordered (b::A) B hA' hB.2.2.2
        exact ⟨⟨hB.1,hB.2.1,hB.2.2.1,hh.1⟩,⟨hB.1,hB.2.1,hB.2.2.1,hh.2⟩⟩
termination_by A.length+B.length

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*}

 def positiveStepMasses : (L : List (GaussianStep ι)) →
    (∀ s ∈ L, 0 < s.1) → List PositiveMass
  | [], _ => []
  | s::L, h => ⟨s.1,h s (by simp)⟩::positiveStepMasses L (fun t ht => h t (by simp [ht]))

 theorem positiveStepMasses_length (L : List (GaussianStep ι))
    (h : ∀ s ∈ L, 0 < s.1) : (positiveStepMasses L h).length=L.length := by
  induction L with
  | nil => rfl
  | cons s L ih => exact congrArg Nat.succ (ih _)

 theorem positiveStepMasses_ordered {a : ℝ} {L : List (GaussianStep ι)}
    (hL : OrderedSteps a L) (hp : ∀ s ∈ L, 0 < s.1) :
    MassOrdered a (positiveStepMasses L hp) := by
  induction L generalizing a with
  | nil => exact hL
  | cons s L ih => exact ⟨hL.1,hL.2.1,ih hL.2.2.2 _⟩

 def stepClockValues (q₀ : ι → ℝ) : List (GaussianStep ι) → ℕ → ι → ℝ
  | [], _ => q₀
  | _::_, 0 => q₀
  | s::L, j+1 => stepClockValues (fun i => q₀ i+s.2 i) L j

 theorem stepClockValues_zero (q₀ : ι → ℝ) (L : List (GaussianStep ι)) :
    stepClockValues q₀ L 0=q₀ := by cases L <;> rfl

 theorem stepClockValues_mono (q₀ : ι → ℝ) (L : List (GaussianStep ι)) (i : ι) :
    Monotone (fun j => stepClockValues q₀ L j i) := by
  induction L generalizing q₀ with
  | nil => exact monotone_const
  | cons s L ih =>
    apply monotone_nat_of_le_succ
    intro j
    cases j with
    | zero => simp only [stepClockValues,stepClockValues_zero]; exact le_add_of_nonneg_right (s.2 i).coe_nonneg
    | succ j => exact ih (fun i => q₀ i+s.2 i) (Nat.le_succ j)

 theorem stepClockValues_initial_le (q₀ : ι → ℝ) (L : List (GaussianStep ι)) (j : ℕ) (i : ι) :
    q₀ i ≤ stepClockValues q₀ L j i := by
  have h := stepClockValues_mono q₀ L i (Nat.zero_le j)
  simpa only [stepClockValues_zero] using h

 theorem diagonalBoundarySteps_stepClockValues (q₀ : ι → ℝ) (L : List (GaussianStep ι))
    (hp : ∀ s ∈ L, 0 < s.1) :
    diagonalBoundarySteps (positiveStepMasses L hp) q₀
      (fun j => stepClockValues q₀ L (j+1)) = L := by
  induction L generalizing q₀ with
  | nil => rfl
  | cons s L ih =>
    simp only [positiveStepMasses,diagonalBoundarySteps,stepClockValues,stepClockValues_zero]
    have hi : (fun i => Real.toNNReal (q₀ i+(s.2 i:ℝ)-q₀ i)) = s.2 := by
      funext i
      simp only [add_sub_cancel_left,Real.toNNReal_coe]
    rw [hi,ih]

 theorem stepClockValues_terminal (q₀ : ι → ℝ) (L : List (GaussianStep ι)) (i : ι) :
    stepClockValues q₀ L L.length i = q₀ i+(L.map (fun s => (s.2 i:ℝ))).sum := by
  induction L generalizing q₀ with
  | nil => simp [stepClockValues]
  | cons s L ih => simp only [List.length_cons,stepClockValues,ih,List.map_cons,List.sum_cons]; ring

 theorem ZeroClockRefinement.total_variance {L M : List (GaussianStep ι)}
    (h : ZeroClockRefinement L M) (i : ι) :
    (L.map (fun s => (s.2 i:ℝ))).sum = (M.map (fun s => (s.2 i:ℝ))).sum := by
  induction h with
  | refl => rfl
  | insert pre post m hm => simp
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι]

 theorem ClockTree.singleMean_eq_hierarchy {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} {a : ℝ}
    (ho : MassOrdered a as) (q : ℕ → ι → ℝ≥0) (P : S → ℝ) :
    ClockTree.singleMean w φ as q P = gaussianHierarchyMean w φ P (clockSteps as q) := by
  funext x
  induction as generalizing a q x with
  | nil => rfl
  | cons b as ih =>
    rw [ClockTree.singleMean_step hw φ b ho.2.2]
    change shiftedMean _ _ _ _ x = shiftedMean _ _ _ _ x
    congr 1
    funext y
    exact ih ho.2.2 _ y

 def stepPairMean (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre post : List (GaussianStep ι)) (P : S → S → ℝ) : (ι → ℝ) → ℝ :=
  prefixTest pre (gaussianHierarchy w φ post)
    (fun x => gaussianHierarchyMean w φ
      (fun σ => gaussianHierarchyMean w φ (P σ) post x) post x)

 theorem ClockTree.pairMean_prefix {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (as bs : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a (as++bs)) (q : ℕ → ι → ℝ≥0) (P : S → S → ℝ) :
    ClockTree.pairMean w φ (as++bs) q as.length P =
      stepPairMean w φ (clockSteps as q) (clockSteps bs (fun j => q (as.length+j))) P := by
  induction as generalizing a q with
  | nil =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      funext x
      simp only [List.length_nil,Nat.zero_add]
      change ClockTree.singleMean w φ (b::bs) q
        (fun σ => ClockTree.singleMean w φ (b::bs) q (P σ) x) x = _
      rw [ClockTree.singleMean_eq_hierarchy hw φ (as := b::bs) ho]
      congr 1
      funext σ
      simpa only [List.length_nil,Nat.zero_add] using
        congrFun (ClockTree.singleMean_eq_hierarchy hw φ (as := b::bs) ho q (P σ)) x
  | cons b as ih =>
    funext x
    simp only [List.cons_append,List.length_cons,ClockTree.pairMean,clockSteps,
      stepPairMean,prefixTest]
    have hindex : (fun j => q (as.length+1+j)) = (fun j => q (as.length+j+1)) := by
      funext j
      congr 1
      omega
    rw [hindex]
    congr 1
    · rw [prefixContinuation_hierarchy,clockSteps_append]
    · exact ih ho.2.2 (fun j => q (j+1))

omit [Nonempty S] in
 theorem ZeroClockRefinement.pairMean {L M A B : List (GaussianStep ι)}
    (h₁ : ZeroClockRefinement L M) (h₂ : ZeroClockRefinement A B)
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (P : S → S → ℝ) :
    stepPairMean w φ L A P = stepPairMean w φ M B P := by
  unfold stepPairMean
  rw [(h₁.continuation_test _ _).2,(h₂.hierarchy w φ (fun _ => 0)).1]
  congr 1
  funext x
  simp_rw [(h₂.hierarchy w φ _).2]

 theorem ClockTree.disorderExpect_integral {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ho : MassOrdered a as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (P : T.Assignment → ℝ) (x : ι → ℝ) :
    T.disorderExpect w φ v q P x =
      zeroContinuation (Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q 0 i-v i)))
        (T.expect w φ (cumulativeIncrements (q 0) (fun j => q (j+1))) P) x := by
  unfold ClockTree.disorderExpect ClockTree.disorderWeight zeroContinuation ClockTree.expect
  rw [integral_finsetSum]
  · simp only [integral_mul_const]
  · intro σ hσ
    exact ((T.weight_smooth hw φ ho _ σ 0).integrable_zero_shift x).mul_const (P σ)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι]

omit [Fintype ι] in
 theorem length_clockSteps (as : List PositiveMass) (q : ℕ → ι → ℝ≥0) :
    (clockSteps as q).length=as.length := by
  induction as generalizing q with
  | nil => rfl
  | cons a as ih => exact congrArg Nat.succ (ih _)

omit [Fintype ι] in
 theorem positiveStepMasses_append (L M : List (GaussianStep ι))
    (hL : ∀ s ∈ L, 0<s.1) (hM : ∀ s ∈ M, 0<s.1) :
    positiveStepMasses (L++M) (fun s hs => (List.mem_append.mp hs).elim (hL s) (hM s)) =
      positiveStepMasses L hL ++ positiveStepMasses M hM := by
  induction L with
  | nil => rfl
  | cons s L ih => exact congrArg (List.cons _) (ih _)

omit [Fintype ι] in
 theorem clockSteps_stepClockValues (q₀ : ι → ℝ) (L : List (GaussianStep ι))
    (hp : ∀ s ∈ L, 0<s.1) :
    clockSteps (positiveStepMasses L hp)
      (cumulativeIncrements q₀ (fun j => stepClockValues q₀ L (j+1))) = L := by
  rw [clockSteps_cumulative,diagonalBoundarySteps_stepClockValues]

 def stepPairDisorder (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (v : ι → ℝ≥0) (pre post : List (GaussianStep ι)) (P : S → S → ℝ) :
    (ι → ℝ) → ℝ :=
  zeroContinuation (Measure.pi fun i => gaussianReal 0 (v i))
    (stepPairMean w φ pre post P)

 theorem ClockTree.pairDisorder_coordinates {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre post : List (GaussianStep ι))
    (hpre : ∀ s ∈ pre, 0<s.1) (hpost : ∀ s ∈ post, 0<s.1)
    (ho : OrderedSteps 0 (pre++post)) (v : ι → ℝ≥0) (P : S → S → ℝ) :
    let as := positiveStepMasses pre hpre
    let bs := positiveStepMasses post hpost
    let q := stepClockValues (fun i => (v i:ℝ)) (pre++post)
    (fun x => (pairClock (as++bs) as.length).disorderExpect w φ (fun _ => 0) q
      (fun σ => P (pairSpin (as++bs) as.length σ).1 (pairSpin (as++bs) as.length σ).2) x) =
      stepPairDisorder w φ v pre post P := by
  dsimp only
  let as := positiveStepMasses pre hpre
  let bs := positiveStepMasses post hpost
  let q := stepClockValues (fun i => (v i:ℝ)) (pre++post)
  have hpos : ∀ s ∈ pre++post, 0<s.1 :=
    fun s hs => (List.mem_append.mp hs).elim (hpre s) (hpost s)
  have heq : positiveStepMasses (pre++post) hpos=as++bs := positiveStepMasses_append _ _ _ _
  have hordered : MassOrdered 0 (as++bs) := heq ▸ positiveStepMasses_ordered ho hpos
  have hc : clockSteps as (cumulativeIncrements (q 0) (fun j => q (j+1))) = pre ∧
      clockSteps bs (fun j => cumulativeIncrements (q 0) (fun j => q (j+1)) (as.length+j)) = post := by
    have hc := clockSteps_stepClockValues (fun i => (v i:ℝ)) (pre++post) hpos
    rw [heq,clockSteps_append] at hc
    have hq : q 0=(fun i => (v i:ℝ)) := stepClockValues_zero _ _
    rw [hq]
    apply List.append_inj hc
    rw [length_clockSteps,positiveStepMasses_length]
  have hex (c : ℕ → ι → ℝ≥0) :
      (pairClock (as++bs) as.length).expect w φ c
        (fun σ => P (pairSpin (as++bs) as.length σ).1 (pairSpin (as++bs) as.length σ).2) =
        pairMean w φ (as++bs) c as.length P := by
    funext z
    exact pairClock_expect hw φ _ hordered c _ P z
  funext x
  rw [disorderExpect_integral hw φ _ hordered,hex]
  rw [pairMean_prefix hw φ as bs hordered,hc.1,hc.2]
  change zeroContinuation _ _ x=zeroContinuation _ _ x
  congr 2
  funext i
  simp only [stepClockValues_zero,sub_zero,Real.toNNReal_coe]

omit [Nonempty S] in
 theorem ZeroClockRefinement.pairDisorder {L M A B : List (GaussianStep ι)}
    (h₁ : ZeroClockRefinement L M) (h₂ : ZeroClockRefinement A B)
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ≥0) (P : S → S → ℝ) :
    stepPairDisorder w φ v L A P = stepPairDisorder w φ v M B P := by
  unfold stepPairDisorder
  rw [h₁.pairMean h₂]

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

 theorem ClockTree.disorderProfileJets_oneError_pointwise {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (ho : MassOrdered 0 as)
    (pre post : List (ℕ → S → S → ℝ)) (E : ℕ → S → S → ℝ)
    (T : ClockTree S as) {r : ℕ} (hT : T.leaves ≤ r)
    (P : T.Assignment → ℝ) {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hP : ∀ σ, |P σ| ≤ C)
    (hpre : ∀ K ∈ pre, ∀ j σ τ, |K j σ τ| ≤ M)
    (hpost : ∀ K ∈ post, ∀ j σ τ, |K j σ τ| ≤ M)
    {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j) (hE : ∀ j σ τ, |E j σ τ| ≤ f j)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    |ClockTree.disorderProfileJets w φ v q x (pre++E::post) T P| ≤
      ClockTree.errorJetVariation r pre.length post.length*C*M^(pre.length+post.length)*
        (T.forkCost f+ClockTree.edgeBudget 0 as f+f as.length) := by
  let e := finiteJetEquiv ι
  have he (j : ℕ) : ClockTree.pairRootMean w (reindexFeature e φ) as
      (fun i => q 0 (e i)-v (e i)) (fun j i => q (j+1) (e i)-q j (e i)) j
      (fun σ τ => |E j σ τ|) ((coordinateEquiv e).symm x) ≤ f j := by
    rw [ClockTree.pairRootMean_eq_rootExpect hw (reindexFeature e φ) as ho]
    exact (le_abs_self _).trans ((ClockTree.pairClock as j).rootExpect_abs_le hw
      (reindexFeature e φ) ho (fun σ => by simpa only [abs_abs] using hE j _ _) _ _ _)
  have hd := ClockTree.rootProfileJets_oneError_abs_le hw (reindexFeature e φ) ho pre post E T hT P
    hC hM hP hpre hpost (fun i => q 0 (e i)-v (e i))
    (fun j i => q (j+1) (e i)-q j (e i)) hf (hf as.length)
    (fun σ => hE as.length σ σ) ((coordinateEquiv e).symm x) he
  rw [T.rootProfileJets_eq_disorderProfileJets hw (reindexFeature e φ) ho (pre++E::post) P
    (fun i => v (e i)) (fun j i => q j (e i)),
    T.disorderProfileJets_reindex e w φ (pre++E::post) P v q,
    ContinuousLinearEquiv.apply_symm_apply] at hd
  exact hd

 

theorem ClockTree.disorderProfileJets_l1_comparison {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (ho : MassOrdered 0 as)
    (Ks : List (ℕ → S → S → ℝ)) (T : ClockTree S as)
    {r : ℕ} (hT : T.leaves ≤ r) (P : T.Assignment → ℝ)
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hP : ∀ σ, |P σ| ≤ C)
    (hKs : ∀ K ∈ Ks, ∀ j σ τ, |K j σ τ| ≤ M)
    (v : ι → ℝ) (q K : ℕ → ι → ℝ) {a b : ℝ}
    (hp : ∀ u ∈ Ioo a b, ∀ i, Monotone (fun j => q j i+u*K j i))
    (hr : ∀ u ∈ Ioo a b, ∀ i, v i ≤ q 0 i+u*K 0 i)
    {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j)
    (hE : ∀ j σ τ, |ReplicaTree.coordinateProfile φ K j σ τ| ≤ f j)
    (x : ι → ℝ) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    |ClockTree.disorderProfileJets w φ v (fun j i => q j i+s*K j i) x Ks T P -
        ClockTree.disorderProfileJets w φ v (fun j i => q j i+t*K j i) x Ks T P| ≤
      (ClockTree.errorJetVariation r Ks.length 0*C*M^Ks.length*
        (T.forkCost f+ClockTree.edgeBudget 0 as f+f as.length))*|s-t| := by
  have hc := ClockTree.disorderProfileJets_continuous hw φ ho v
    (fun u j i => q j i+u*K j i) (by intro j; fun_prop) (fun _ => x) continuous_const Ks T P
  have hd (u : ℝ) (hu : u ∈ Ioo a b) :=
    ClockTree.hasDerivAt_finiteProfileJets hw φ ho v q K hp hr Ks T P x hu
  apply abs_sub_le_of_bounded_derivative hc.continuousOn hd _ hs ht
  intro u hu
  simpa only [List.length_nil,add_zero] using
    T.disorderProfileJets_oneError_pointwise hw φ ho Ks [] (ReplicaTree.coordinateProfile φ K)
      hT P hC hM hP hKs (by simp) hf hE v (fun j i => q j i+u*K j i) x

 

attribute [local instance] Classical.propDecidable

omit [Fintype S] [Nonempty S] [Nonempty ι] in
theorem ReplicaTree.coordinateProfile_abs_le_sum (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (K : ℕ → ι → ℝ) (D : ι → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)| ≤ D i) (j : ℕ) (σ τ : S) :
    |ReplicaTree.coordinateProfile φ K j σ τ| ≤ ∑ i, |K j i| *(D i)^2 := by
  classical
  unfold ReplicaTree.coordinateProfile
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul,abs_mul, mul_assoc]
  have hh := mul_le_mul (hφ σ i) (hφ τ i) (abs_nonneg _) (hD i)
  simpa only [sq] using mul_le_mul_of_nonneg_left hh (abs_nonneg (K j i))

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

omit [Fintype S] [Nonempty S] in
 theorem ClockTree.single_leaves_exact (as : List PositiveMass) :
    (ClockTree.single (S:=S) as).leaves = 1 := by
  induction as with
  | nil => rfl
  | cons a as ih => exact ih

omit [Fintype S] [Nonempty S] in
 theorem ClockTree.pairClock_leaves (as : List PositiveMass) (j : ℕ) :
    (ClockTree.pairClock (S:=S) as j).leaves = 2 := by
  induction as generalizing j with
  | nil => rfl
  | cons a as ih =>
    cases j with
    | zero => simp [ClockTree.pairClock,ClockTree.leaves,ClockTree.single_leaves_exact]
    | succ j => exact ih j

omit [Fintype S] [Nonempty S] in
 theorem ClockTree.pairClock_forkCost (as : List PositiveMass) (j : ℕ) (f : ℕ → ℝ) :
    (ClockTree.pairClock (S:=S) as j).forkCost f = f (min j as.length) := by
  induction as generalizing j f with
  | nil => simp [ClockTree.pairClock,ClockTree.forkCost]
  | cons a as ih =>
    cases j with
    | zero => simp [ClockTree.pairClock,ClockTree.forkCost,ClockTree.single_forkCost]
    | succ j =>
      change (pairClock as j).forkCost (fun k => f (1+k)) = f (min (j+1) (as.length+1))
      rw [ih]
      congr 1
      omega

 theorem ClockTree.pairDisorder_l1_comparison {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (j : ℕ) (P : S → S → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hP : ∀ σ τ, |P σ τ| ≤ C)
    (v : ι → ℝ) (q K : ℕ → ι → ℝ) {a b : ℝ}
    (hp : ∀ u ∈ Ioo a b, ∀ i, Monotone (fun j => q j i+u*K j i))
    (hr : ∀ u ∈ Ioo a b, ∀ i, v i ≤ q 0 i+u*K 0 i)
    {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j)
    (hE : ∀ j σ τ, |ReplicaTree.coordinateProfile φ K j σ τ| ≤ f j)
    (x : ι → ℝ) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    |(ClockTree.pairClock as j).disorderExpect w φ v (fun j i => q j i+s*K j i)
        (fun σ => P (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2) x -
      (ClockTree.pairClock as j).disorderExpect w φ v (fun j i => q j i+t*K j i)
        (fun σ => P (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2) x| ≤
      ClockTree.errorJetVariation 2 0 0*C*
        (f (min j as.length)+ClockTree.edgeBudget 0 as f+f as.length)*|s-t| := by
  have h := ClockTree.disorderProfileJets_l1_comparison hw φ ho []
    (ClockTree.pairClock as j) (by rw [ClockTree.pairClock_leaves])
    (fun σ => P (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2)
    hC (show 0 ≤ (1:ℝ) by norm_num) (fun σ => hP _ _) (by simp)
    v q K hp hr hf hE x hs ht
  simpa only [ClockTree.disorderProfileJets,List.length_nil,pow_zero,mul_one,
    ClockTree.pairClock_forkCost] using h

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S]

 def stepDisorderPressure (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (C : ι → ℝ) (q₀ : ι → ℝ≥0) (L : List (GaussianStep ι)) (x : ι → ℝ) : ℝ :=
  zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i)) (gaussianHierarchy w φ L) x -
    (1/2:ℝ)*∑ i, ((q₀ i:ℝ)+(L.map fun s => (s.2 i:ℝ)).sum)*C i

 theorem stepDisorderPressure_eq (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (C : ι → ℝ) (q₀ : ι → ℝ≥0) (L : List (GaussianStep ι)) (hp : ∀ s ∈ L, 0 < s.1)
    (x : ι → ℝ) :
    stepDisorderPressure w φ C q₀ L x = disorderPressure w φ C (positiveStepMasses L hp)
      0 (stepClockValues (fun i => (q₀ i:ℝ)) L) x := by
  simp only [disorderPressure,stepClockValues_zero,Pi.zero_apply,sub_zero,
    Real.toNNReal_coe,diagonalBoundarySteps_stepClockValues,positiveStepMasses_length,
    stepClockValues_terminal,stepDisorderPressure]

 theorem ZeroClockRefinement.pressure {L M : List (GaussianStep ι)}
    (h : ZeroClockRefinement L M) (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (C : ι → ℝ) (q₀ : ι → ℝ≥0) (x : ι → ℝ) :
    stepDisorderPressure w φ C q₀ L x = stepDisorderPressure w φ C q₀ M x := by
  unfold stepDisorderPressure
  rw [(h.hierarchy w φ (fun _ => 0)).1]
  simp_rw [h.total_variance]

omit [Fintype ι] in
 theorem positiveStepMasses_values (L : List (GaussianStep ι)) (hp : ∀ s ∈ L, 0 < s.1) :
    (positiveStepMasses L hp).map Subtype.val=L.map Prod.fst := by
  induction L with
  | nil => rfl
  | cons s L ih => exact congrArg (List.cons s.1) (ih _)

omit [Fintype ι] in
 theorem positiveStepMasses_eq {A B : List (GaussianStep ι)}
    (hA : ∀ s ∈ A, 0 < s.1) (hB : ∀ s ∈ B, 0 < s.1)
    (he : A.map Prod.fst=B.map Prod.fst) : positiveStepMasses A hA=positiveStepMasses B hB := by
  apply (List.map_injective_iff.mpr Subtype.val_injective)
  rw [positiveStepMasses_values,positiveStepMasses_values,he]

 theorem stepDisorderPressure_comparison [Nonempty S] [Nonempty ι] [DecidableEq ι]
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (C D : ι → ℝ) (hC : ∀ σ i, (φ σ (Pi.single i 1))^2 = C i)
    (hD : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q₀ r₀ : ι → ℝ≥0) (A B : List (GaussianStep ι))
    (hA : OrderedSteps 0 A) (hB : OrderedSteps 0 B) (x : ι → ℝ) :
    |stepDisorderPressure w φ C q₀ A x-stepDisorderPressure w φ C r₀ B x| ≤
      (1/2:ℝ)*∑ i, (D i)^2*rootBoundaryCost
        ((positiveStepMasses (leftClockSteps (commonClockSteps A B))
          (commonClockSteps_ordered A B hA hB).1.mem_pos)++[⟨1,by norm_num⟩])
        (fun j => stepClockValues (fun i => (q₀ i:ℝ)) (leftClockSteps (commonClockSteps A B)) j i)
        (fun j => stepClockValues (fun i => (r₀ i:ℝ)) (rightClockSteps (commonClockSteps A B)) j i) := by
  have hadd := commonClockSteps_refines A B hA.mem_pos hB.mem_pos
  rw [hadd.1.pressure w φ C q₀ x,hadd.2.pressure w φ C r₀ x]
  have ho := commonClockSteps_ordered A B hA hB
  rw [stepDisorderPressure_eq w φ C q₀ _ ho.1.mem_pos,
    stepDisorderPressure_eq w φ C r₀ _ ho.2.mem_pos,
    ← positiveStepMasses_eq ho.1.mem_pos ho.2.mem_pos (commonClockSteps_same_masses A B)]
  have hx := positiveStepMasses_ordered ho.1 ho.1.mem_pos
  exact disorderPressure_comparison hw φ C D hC hD _ hx.pairwise
    hx.members_le_one
    (stepClockValues_mono _ _) (stepClockValues_mono _ _)
    (fun i => by simp only [stepClockValues_zero,Pi.zero_apply]; exact (q₀ i).coe_nonneg)
    (fun i => by simp only [stepClockValues_zero,Pi.zero_apply]; exact (r₀ i).coe_nonneg) x

end SKFluctuations.Hierarchy

end

end OAI
