import OAI.Geometry.BundleTests.Normalized
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma

namespace OAI

noncomputable section

/-! Retained bundle labels, positive multiplicities, regrouping, and complement rank. -/

section
open scoped BigOperators
namespace Kaplansky

def labelFiberProdEquiv {A B C : Type*} (f : B → C) (c : C) :
    {p : A×B // f p.2=c} ≃ A×{b : B // f b=c} where
  toFun p := (p.1.1,⟨p.1.2,p.2⟩)
  invFun p := ⟨(p.1,p.2.1),p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def labelFiberSigmaEquiv {J C : Type*} {A : J → Type*} (f : ∀ j, A j → C) (c : C) :
    {p : Σ j, A j // f p.1 p.2=c} ≃ Σ j, {a : A j // f j a=c} where
  toFun p := ⟨p.1.1,⟨p.1.2,p.2⟩⟩
  invFun p := ⟨⟨p.1,p.2.1⟩,p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem labelFiberProd_card {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    (f : B → C) (c : C) :
    Fintype.card {p : A×B // f p.2=c} = Fintype.card A * Fintype.card {b : B // f b=c} := by
  rw [Fintype.card_congr (labelFiberProdEquiv (A := A) f c),Fintype.card_prod]

theorem labelFiberSigma_card {J C : Type*} [Fintype J] [DecidableEq C] {A : J → Type*} [∀ j, Fintype (A j)]
    (f : ∀ j, A j → C) (c : C) :
    Fintype.card {p : Σ j, A j // f p.1 p.2=c} = ∑ j, Fintype.card {a : A j // f j a=c} := by
  rw [Fintype.card_congr (labelFiberSigmaEquiv f c),Fintype.card_sigma]

theorem constantLabelFiber_card {A C : Type*} [Fintype A] [DecidableEq C] (c d : C) :
    Fintype.card (Subtype (fun _ : A => c=d)) = if c=d then Fintype.card A else 0 := by
  by_cases h : c=d <;> simp [h]

end Kaplansky

end

section
open Bundle Topology
open scoped BigOperators
namespace Kaplansky
open ComplexGrassmann

abbrev RetainedSlot (m R : ℕ) := Fin m × (Σ j : Fin (R+1), TestBundleSlot m R j.val)

def retainedLabel (m R : ℕ) (s : RetainedSlot m R) : Option (Fin R) :=
  testSummandLineIndex (Nat.le_of_lt_succ s.2.1.isLt) s.2.2.1

def retainedBundleCore (m R : ℕ) :=
  smoothLineSumCore (testProjectiveDimension m R) (retainedLabel m R)
abbrev RetainedBundle (m R : ℕ) := (retainedBundleCore m R).Fiber

instance retainedBundle_norm (m R : ℕ) (P : SmoothTestBase m R) :
    NormedAddCommGroup (RetainedBundle m R P) := smoothLineSum_norm _ _ P
instance retainedBundle_inner (m R : ℕ) (P : SmoothTestBase m R) :
    InnerProductSpace ℂ (RetainedBundle m R P) := smoothLineSum_inner _ _ P

/-- Grouping the fiber coordinates recovers m copies of every stage bundle. -/
def retainedFiberEquiv (m R : ℕ) (P : SmoothTestBase m R) :
    RetainedBundle m R P ≃ₗ[ℂ] (∀ _ : Fin m, ∀ j : Fin (R+1),
      SmoothTestBundle m R R j.val (Nat.le_refl R) (Nat.le_of_lt_succ j.isLt) P) where
  toFun v a j := WithLp.toLp 2 (fun s => (show EuclideanSpace ℂ (RetainedSlot m R) from v) (a,⟨j,s⟩))
  invFun v := WithLp.toLp 2 (fun s => (show EuclideanSpace ℂ (TestBundleSlot m R s.2.1.val) from v s.1 s.2.1) s.2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := by
    apply (EuclideanSpace.equiv (RetainedSlot m R) ℂ).injective
    rfl
  right_inv v := by
    funext a j
    apply (EuclideanSpace.equiv (TestBundleSlot m R j.val) ℂ).injective
    rfl

/-- Each stage projection is continuous for the actual total-space topology. -/
theorem continuous_retainedStage (m R : ℕ) (a : Fin m) (j : Fin (R+1)) :
    Continuous (fun z : TotalSpace (EuclideanSpace ℂ (RetainedSlot m R)) (RetainedBundle m R) =>
      TotalSpace.mk' (EuclideanSpace ℂ (TestBundleSlot m R j.val)) z.proj
        (retainedFiberEquiv m R z.proj z.2 a j)) := by
  apply (continuous_finiteLineSum_iff _ _).mpr
  refine ⟨FiberBundle.continuous_proj _ _,?_⟩
  intro s
  exact continuous_finiteLineSumComponent
    (fun s : RetainedSlot m R => productLineCore (testProjectiveDimension m R) (retainedLabel m R s)) (a,⟨j,s⟩)

theorem retainedBundle_finrank (m R : ℕ) (P : SmoothTestBase m R) :
    Module.finrank ℂ (RetainedBundle m R P)=m*∑ j : Fin (R+1),testRank m R j.val := by
  change Module.finrank ℂ (EuclideanSpace ℂ (RetainedSlot m R)) = _
  simp only [finrank_euclideanSpace,RetainedSlot,Fintype.card_prod,Fintype.card_fin,Fintype.card_sigma]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simpa [TestBundleSlot] using (sum_testMultiplicity (m := m) (Nat.le_of_lt_succ j.isLt))

end Kaplansky

end

section
open scoped BigOperators
namespace Kaplansky

theorem testSummandLineIndex_eq_none {R j : ℕ} (hj : j≤R) (s : Fin (j+1)) :
    testSummandLineIndex hj s = none ↔ s=0 := by
  unfold testSummandLineIndex
  by_cases h : s.val=0
  · rw [dite_eq_left h]
    exact iff_of_true rfl (Fin.ext h)
  · rw [dite_eq_right h]
    simp only [Option.some_ne_none,false_iff]
    intro hs
    exact h (congrArg Fin.val hs)

theorem retainedLabel_card_sum (m R : ℕ) (i : Option (Fin R)) :
    Fintype.card {s : RetainedSlot m R // retainedLabel m R s=i} =
      m * ∑ j : Fin (R+1), ∑ a : Fin (j.val+1),
        if testSummandLineIndex (Nat.le_of_lt_succ j.isLt) a=i
        then testMultiplicity m R j.val a else 0 := by
  change Fintype.card {s : Fin m × (Σ j : Fin (R+1), TestBundleSlot m R j.val) //
    testSummandLineIndex (Nat.le_of_lt_succ s.2.1.isLt) s.2.2.1=i} = _
  rw [labelFiberProd_card (A := Fin m)
    (fun s : Σ j : Fin (R+1), TestBundleSlot m R j.val =>
      testSummandLineIndex (Nat.le_of_lt_succ s.1.isLt) s.2.1) i,Fintype.card_fin,
    labelFiberSigma_card (A := fun j : Fin (R+1) => TestBundleSlot m R j.val) (fun (j : Fin (R+1)) (s : TestBundleSlot m R j.val) =>
      testSummandLineIndex (Nat.le_of_lt_succ j.isLt) s.1) i]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [labelFiberSigma_card (fun a (_ : Fin (testMultiplicity m R j.val a)) =>
    testSummandLineIndex (Nat.le_of_lt_succ j.isLt) a) i]
  apply Finset.sum_congr rfl
  intro a _
  rw [constantLabelFiber_card,Fintype.card_fin]

theorem retainedLabel_none_card (m R : ℕ) :
    Fintype.card {s : RetainedSlot m R // retainedLabel m R s=none} = retainedTrivialMultiplicity m R := by
  rw [retainedLabel_card_sum]
  simp_rw [testSummandLineIndex_eq_none]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  unfold retainedTrivialMultiplicity
  congr 1
  let e : Fin (R+1) ≃ Fin (R+1) := ⟨Fin.rev,Fin.rev,Fin.rev_involutive,Fin.rev_involutive⟩
  apply Fintype.sum_equiv e
  intro j
  have he : R-(e j).val=j.val := by
    change R-((R+1)-(j.val+1))=j.val
    have hj := j.isLt
    omega
  change 64*m*4^(R-j.val) = 64*m*4^(R-(R-(e j).val))
  rw [he]

theorem testSummandLineIndex_eq_some {R j : ℕ} (hj : j≤R) (s : Fin (j+1)) (i : Fin R) :
    testSummandLineIndex hj s = some i ↔ s.val=i.val+1 := by
  unfold testSummandLineIndex
  split
  · simp_all
  · simp only [Option.some.injEq,Fin.ext_iff]
    omega

theorem retainedLabel_some_stage_sum (m R : ℕ) (i : Fin R) (j : Fin (R+1)) :
    (∑ a : Fin (j.val+1), if testSummandLineIndex (Nat.le_of_lt_succ j.isLt) a=some i
      then testMultiplicity m R j.val a else 0) =
      if h : i.val<j.val then testMultiplicity m R j.val ⟨i.val+1,by omega⟩ else 0 := by
  by_cases h : i.val<j.val
  · rw [dite_eq_left h]
    let a : Fin (j.val+1) := ⟨i.val+1,by omega⟩
    have he : ∀ b : Fin (j.val+1), testSummandLineIndex (Nat.le_of_lt_succ j.isLt) b=some i ↔ b=a := by
      intro b
      rw [testSummandLineIndex_eq_some,Fin.ext_iff]
    simp_rw [he]
    simp [a]
  · rw [dite_eq_right h]
    apply Finset.sum_eq_zero
    intro a _
    rw [ite_eq_right]
    rw [testSummandLineIndex_eq_some]
    omega

def suffixReverseEquiv {R : ℕ} (i : Fin R) :
    {j : Fin (R+1) // i.val<j.val} ≃ Fin (R-i.val) where
  toFun j := ⟨R-j.1.val,by have h := j.2; have h' := j.1.isLt; omega⟩
  invFun t := ⟨⟨R-t.val,by omega⟩,by change i.val<R-t.val; omega⟩
  left_inv j := by
    apply Subtype.ext
    apply Fin.ext
    dsimp
    have h := j.1.isLt
    omega
  right_inv t := by
    apply Fin.ext
    dsimp
    omega

theorem sum_suffix_reverse {R : ℕ} (i : Fin R)
    (f : ∀ j : Fin (R+1), i.val<j.val → ℕ) :
    (∑ j : Fin (R+1), if h : i.val<j.val then f j h else 0) =
      ∑ t : Fin (R-i.val), f ⟨R-t.val,by omega⟩ (by change i.val<R-t.val; omega) := by
  let g := fun j : Fin (R+1) => if h : i.val<j.val then f j h else 0
  let s := Finset.univ.filter (fun j : Fin (R+1) => i.val<j.val)
  have hg : (∑ j, g j) = ∑ j ∈ s, g j := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i.val<j.val <;> simp [g,h]
  change (∑ j, g j)=_
  rw [hg,Finset.sum_subtype (p := fun j : Fin (R+1) => i.val<j.val) s (by intro j; simp [s]) g]
  apply Fintype.sum_equiv (suffixReverseEquiv i)
  intro j
  have h := j.2
  simp only [g,dite_eq_left h]
  congr 1
  apply Fin.ext
  dsimp [suffixReverseEquiv]
  have hj := j.1.isLt
  omega

/-- Each K_i is the count of actual occurrences of its hyperplane line in
G, including all m copies and every retained stage. -/
theorem retainedLabel_some_card (m R : ℕ) (i : Fin R) :
    Fintype.card {s : RetainedSlot m R // retainedLabel m R s=some i} = testProjectiveDimension m R i := by
  rw [retainedLabel_card_sum]
  simp_rw [retainedLabel_some_stage_sum]
  rw [sum_suffix_reverse]
  exact retainedHyperplaneMultiplicity_eq m R i

end Kaplansky

end

section
open Bundle Topology
open scoped BigOperators
namespace Kaplansky
open ComplexGrassmann

def groupingByLabel {S I : Type*} (label : S → I) :
    S ≃ Σ i, {s : S // label s=i} where
  toFun s := ⟨label s,⟨s,rfl⟩⟩
  invFun p := p.2.1
  left_inv _ := rfl
  right_inv p := by
    obtain ⟨i,s,h⟩ := p
    subst i
    rfl

def retainedLineRank (m R : ℕ) : Option (Fin R) → ℕ
  | none => retainedTrivialMultiplicity m R
  | some i => testProjectiveDimension m R i

abbrev RetainedGroupedSlot (m R : ℕ) := Σ i : Option (Fin R), Fin (retainedLineRank m R i)

theorem retainedLabel_card (m R : ℕ) (i : Option (Fin R)) :
    Fintype.card {s : RetainedSlot m R // retainedLabel m R s=i}=retainedLineRank m R i := by
  cases i with
  | none => exact retainedLabel_none_card m R
  | some i => exact retainedLabel_some_card m R i

/-- Every retained line occurrence is accounted for exactly once. -/
def retainedGroupingEquiv (m R : ℕ) : RetainedSlot m R ≃ RetainedGroupedSlot m R :=
  (groupingByLabel (retainedLabel m R)).trans (Equiv.sigmaCongrRight (fun i =>
    (Fintype.equivFin {s : RetainedSlot m R // retainedLabel m R s=i}).trans
      (finCongr (retainedLabel_card m R i))))

theorem retainedGrouping_label (m R : ℕ) (s : RetainedSlot m R) :
    (retainedGroupingEquiv m R s).1=retainedLabel m R s := rfl

/-- Relabeling justified by an exact slot bijection preserves topology and
metric, as well as the fiber linear structure. -/
def lineSumRelabelUnitary {S T ι : Type*} [Fintype S] [Fintype T] [Fintype ι]
    (K : ι → ℕ) (a : T → Option ι) (b : S → Option ι) (e : T ≃ S)
    (h : ∀ t, a t=b (e t)) :
    UnitaryBundleEquiv (EuclideanSpace ℂ T) (EuclideanSpace ℂ S)
      (SmoothLineSumBundle K a) (SmoothLineSumBundle K b) := by
  have he : a = fun t => b (e t) := funext h
  subst a
  exact lineSumReindexUnitary (fun s => productLineCore K (b s)) e

def retainedRegroupingUnitary (m R : ℕ) :
    UnitaryBundleEquiv (EuclideanSpace ℂ (RetainedSlot m R))
      (EuclideanSpace ℂ (RetainedGroupedSlot m R)) (RetainedBundle m R)
      (SmoothLineSumBundle (testProjectiveDimension m R) (fun s : RetainedGroupedSlot m R => s.1)) :=
  lineSumRelabelUnitary (testProjectiveDimension m R) (retainedLabel m R) (fun s : RetainedGroupedSlot m R => s.1)
    (retainedGroupingEquiv m R) (fun s => (retainedGrouping_label m R s).symm)

/-- The total rank in the actual Chern-decomposition presentation. -/
theorem retainedBundle_rank_decomposition (m R : ℕ) (y : SmoothTestBase m R) :
    Module.finrank ℂ (RetainedBundle m R y) = retainedTrivialMultiplicity m R +
      ∑ i : Fin R, testProjectiveDimension m R i := by
  change Module.finrank ℂ (EuclideanSpace ℂ (RetainedSlot m R)) = _
  rw [finrank_euclideanSpace,Fintype.card_congr (retainedGroupingEquiv m R)]
  change Fintype.card (Σ i : Option (Fin R), Fin (retainedLineRank m R i)) = _
  rw [Fintype.card_sigma]
  calc
    _ = ∑ i : Option (Fin R), retainedLineRank m R i :=
      Finset.sum_congr rfl (fun i _ => Fintype.card_fin _)
    _ = _ := by simp [retainedLineRank]

end Kaplansky

end

open scoped BigOperators
namespace Kaplansky

theorem retained_complement_rank_lt {m R : ℕ} (hm : 0<m) (y : SmoothTestBase m R)
    (V : Submodule ℂ (RetainedBundle m R y))
    (hV : 2*m*testRank m R 0 ≤ Module.finrank ℂ V) :
    Module.finrank ℂ Vᗮ < ∑ i : Fin R, testProjectiveDimension m R i := by
  let W : Submodule ℂ (EuclideanSpace ℂ (RetainedSlot m R)) := V
  have hW : 2*m*testRank m R 0 ≤ Module.finrank ℂ W := hV
  change Module.finrank ℂ Wᗮ < _
  have he := W.finrank_add_finrank_orthogonal
  have hd := retainedBundle_rank_decomposition m R y
  change Module.finrank ℂ (EuclideanSpace ℂ (RetainedSlot m R)) = _ at hd
  rw [hd] at he
  have ht := retainedTrivialMultiplicity_bound (R := R) hm
  omega

end Kaplansky

end

end OAI
