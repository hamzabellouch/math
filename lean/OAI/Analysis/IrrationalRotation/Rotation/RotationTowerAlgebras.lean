import OAI.Analysis.IrrationalRotation.Operators.TowerBlockAlgebras
import OAI.Analysis.IrrationalRotation.Analysis.TowerRefinement
import OAI.Analysis.IrrationalRotation.Rotation.RotationSetProjections

namespace OAI

noncomputable section
open scoped BigOperators

namespace Invariant233.Rotation

variable {β : Type*}

def towerLevel (θ : ℝ) (s : Set Circle) (n : ℕ) : Set Circle :=
  action θ (n : ℤ) '' s

theorem measurableSet_towerLevel (θ : ℝ) (s : Set Circle)
    (hs : MeasurableSet s) (n : ℕ) : MeasurableSet (towerLevel θ s n) := by
  rw [towerLevel, ← action_neg_preimage_eq_image]
  exact hs.preimage (action_continuous θ (-(n : ℤ))).measurable

theorem powerProjection_mul_eq_zero_of_disjoint (θ : ℝ) (s t : Set Circle)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (i j : ℕ)
    (hdisj : Disjoint (towerLevel θ s i) (towerLevel θ t j)) :
    (U ^ i * setProjection θ s hs * star (U ^ i)) *
      (U ^ j * setProjection θ t ht * star (U ^ j)) = 0 := by
  obtain ⟨hsi, hi⟩ := U_pow_setProjection_star_image θ i s hs
  obtain ⟨htj, hj⟩ := U_pow_setProjection_star_image θ j t ht
  rw [hi, hj]
  exact setProjection_mul_eq_zero_of_disjoint θ _ _ hsi htj hdisj

def towerMatrixEntries (θ : ℝ) (s : β → Set Circle)
    (hs : ∀ b, MeasurableSet (s b)) (height : β → ℕ)
    (b : β) (i j : Fin (height b)) : Hilbert →L[ℂ] Hilbert :=
  U ^ (i : ℕ) * setProjection θ (s b) (hs b) * star (U ^ (j : ℕ))

theorem towerMatrixEntries_isBlockMatrixUnitFamily (θ : ℝ) (s : β → Set Circle)
    (hs : ∀ b, MeasurableSet (s b)) (height : β → ℕ)
    (hdisj : Pairwise (fun a b : Σ c, Fin (height c) =>
      Disjoint (towerLevel θ (s a.1) a.2) (towerLevel θ (s b.1) b.2))) :
    TowerMatrixUnits.IsBlockMatrixUnitFamily (towerMatrixEntries θ s hs height) := by
  apply TowerMatrixUnits.towerEntry_isBlockMatrixUnitFamily
    (fun b (i : Fin (height b)) => U ^ (i : ℕ)) (fun b => setProjection θ (s b) (hs b))
  · intro b i
    exact (unitary _).pow_mem U_mem_unitary i.val
  · intro b
    exact isStarProjection_setProjection θ (s b) (hs b)
  · intro b i j hij
    apply powerProjection_mul_eq_zero_of_disjoint
    apply hdisj (i := ⟨b, i⟩) (j := ⟨b, j⟩)
    intro h
    cases h
    exact hij rfl
  · intro b c hbc i j
    apply powerProjection_mul_eq_zero_of_disjoint
    exact hdisj (i := ⟨b, i⟩) (j := ⟨c, j⟩) (fun h => hbc (congrArg Sigma.fst h))

def finiteTowerAlgebra (θ : ℝ) (s : β → Set Circle)
    (hs : ∀ b, MeasurableSet (s b)) (height : β → ℕ) :
    StarSubalgebra ℂ (Hilbert →L[ℂ] Hilbert) :=
  StarAlgebra.adjoin ℂ
    (TowerRefinement.towerGenerators U (fun b => setProjection θ (s b) (hs b)) height)

theorem towerMatrixEntries_range (θ : ℝ) (s : β → Set Circle)
    (hs : ∀ b, MeasurableSet (s b)) (height : β → ℕ) :
    (Set.range fun t : Σ b, Fin (height b) × Fin (height b) =>
      towerMatrixEntries θ s hs height t.1 t.2.1 t.2.2) =
    TowerRefinement.towerGenerators U (fun b => setProjection θ (s b) (hs b)) height := by
  ext x
  constructor
  · rintro ⟨⟨b, i, j⟩, rfl⟩
    exact ⟨b, i.val, j.val, i.isLt, j.isLt, rfl⟩
  · rintro ⟨b, i, j, hi, hj, rfl⟩
    exact ⟨⟨b, ⟨i, hi⟩, ⟨j, hj⟩⟩, rfl⟩

theorem finiteTowerAlgebra_eq_blockMatrixAlgebra (θ : ℝ) (s : β → Set Circle)
    (hs : ∀ b, MeasurableSet (s b)) (height : β → ℕ)
    (hdisj : Pairwise (fun a b : Σ c, Fin (height c) =>
      Disjoint (towerLevel θ (s a.1) a.2) (towerLevel θ (s b.1) b.2))) :
    finiteTowerAlgebra θ s hs height =
      TowerMatrixUnits.blockMatrixAlgebra (towerMatrixEntries θ s hs height)
        (towerMatrixEntries_isBlockMatrixUnitFamily θ s hs height hdisj) := by
  rw [TowerMatrixUnits.blockMatrixAlgebra_eq_adjoin, towerMatrixEntries_range]
  rfl

theorem finiteTowerAlgebra_finiteDimensional [Finite β] (θ : ℝ)
    (s : β → Set Circle) (hs : ∀ b, MeasurableSet (s b)) (height : β → ℕ)
    (hdisj : Pairwise (fun a b : Σ c, Fin (height c) =>
      Disjoint (towerLevel θ (s a.1) a.2) (towerLevel θ (s b.1) b.2))) :
    FiniteDimensional ℂ (finiteTowerAlgebra θ s hs height) := by
  rw [finiteTowerAlgebra_eq_blockMatrixAlgebra θ s hs height hdisj]
  exact TowerMatrixUnits.blockMatrixAlgebra_finiteDimensional _ _

theorem finiteTowerAlgebra_le (θ : ℝ) (s : β → Set Circle)
    (hs : ∀ b, MeasurableSet (s b)) (height : β → ℕ) :
    finiteTowerAlgebra θ s hs height ≤ (algebra θ).toStarSubalgebra := by
  apply StarAlgebra.adjoin_le
  rintro _ ⟨b, i, j, hi, hj, rfl⟩
  exact mul_mem (mul_mem (pow_mem (U_mem_algebra θ) i)
    (setProjection_mem_algebra θ (s b) (hs b))) (star_mem (pow_mem (U_mem_algebra θ) j))

theorem towerEntry_mem_finiteTowerAlgebra (θ : ℝ) (s : β → Set Circle)
    (hs : ∀ b, MeasurableSet (s b)) (height : β → ℕ)
    (b : β) {i j : ℕ} (hi : i < height b) (hj : j < height b) :
    U ^ i * setProjection θ (s b) (hs b) * star (U ^ j) ∈
      finiteTowerAlgebra θ s hs height :=
  StarAlgebra.subset_adjoin ℂ _ ⟨b, i, j, hi, hj, rfl⟩

theorem finiteTowerAlgebra_le_of_refinement {κ τ : Type*}
    (θ : ℝ) (s : β → Set Circle) (t : κ → Set Circle)
    (hs : ∀ b, MeasurableSet (s b)) (ht : ∀ c, MeasurableSet (t c))
    (oldHeight : β → ℕ) (newHeight : κ → ℕ)
    (pieces : β → Finset τ) (index : β → τ → κ) (offset : β → τ → ℕ)
    (hdecomp : ∀ b, setProjection θ (s b) (hs b) = ∑ a ∈ pieces b,
      U ^ offset b a * setProjection θ (t (index b a)) (ht (index b a)) *
        star (U ^ offset b a))
    (hfit : ∀ b a, a ∈ pieces b →
      offset b a + oldHeight b ≤ newHeight (index b a)) :
    finiteTowerAlgebra θ s hs oldHeight ≤ finiteTowerAlgebra θ t ht newHeight :=
  TowerRefinement.adjoin_towerGenerators_le_of_refinement U _ _ oldHeight newHeight
    pieces index offset hdecomp hfit

theorem setProjection_eq_sum_shifted_of_partition {τ : Type*}
    (θ : ℝ) (s : Set Circle) (hs : MeasurableSet s)
    (t : τ → Set Circle) (ht : ∀ a, MeasurableSet (t a))
    (pieces : Finset τ) (offset : τ → ℕ)
    (hdisj : ∀ a ∈ pieces, ∀ b ∈ pieces, a ≠ b →
      Disjoint (towerLevel θ (t a) (offset a)) (towerLevel θ (t b) (offset b)))
    (hcover : s = ⋃ a ∈ pieces, towerLevel θ (t a) (offset a)) :
    setProjection θ s hs = ∑ a ∈ pieces,
      U ^ offset a * setProjection θ (t a) (ht a) * star (U ^ offset a) := by
  let levels := fun a => towerLevel θ (t a) (offset a)
  have hm : ∀ a, MeasurableSet (levels a) :=
    fun a => measurableSet_towerLevel θ (t a) (ht a) (offset a)
  calc
    setProjection θ s hs = setProjection θ (⋃ a ∈ pieces, levels a)
        (Finset.measurableSet_biUnion pieces (fun a _ => hm a)) := by
      congr 1
    _ = ∑ a ∈ pieces, setProjection θ (levels a) (hm a) :=
      setProjection_biUnion θ pieces levels hm hdisj
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      obtain ⟨himage, heq⟩ := U_pow_setProjection_star_image θ (offset a) (t a) (ht a)
      exact heq.symm

theorem finiteTowerAlgebra_le_of_set_refinement {κ τ : Type*}
    (θ : ℝ) (s : β → Set Circle) (t : κ → Set Circle)
    (hs : ∀ b, MeasurableSet (s b)) (ht : ∀ c, MeasurableSet (t c))
    (oldHeight : β → ℕ) (newHeight : κ → ℕ)
    (pieces : β → Finset τ) (index : β → τ → κ) (offset : β → τ → ℕ)
    (hdisj : ∀ b a, a ∈ pieces b → ∀ a', a' ∈ pieces b → a ≠ a' →
      Disjoint (towerLevel θ (t (index b a)) (offset b a))
        (towerLevel θ (t (index b a')) (offset b a')))
    (hcover : ∀ b, s b = ⋃ a ∈ pieces b, towerLevel θ (t (index b a)) (offset b a))
    (hfit : ∀ b a, a ∈ pieces b →
      offset b a + oldHeight b ≤ newHeight (index b a)) :
    finiteTowerAlgebra θ s hs oldHeight ≤ finiteTowerAlgebra θ t ht newHeight := by
  apply finiteTowerAlgebra_le_of_refinement θ s t hs ht oldHeight newHeight
    pieces index offset _ hfit
  intro b
  exact setProjection_eq_sum_shifted_of_partition θ (s b) (hs b)
    (fun a => t (index b a)) (fun a => ht (index b a))
    (pieces b) (offset b) (hdisj b) (hcover b)

end Invariant233.Rotation

end

end OAI
