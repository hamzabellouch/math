import OAI.NumberTheory.Ostmann.Arithmetic.HistoryActiveCoordinates
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairPattern

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairGiantCoordinates
open Construction HistoryOccurrenceVariables HistoryPairPattern HistoryActiveCoordinates
attribute [local instance] Classical.propDecidable
variable {l : ℕ}

def giantCoordinates (h k : History l) : Finset (PairKey h k) :=
  Finset.univ.image (fun b : Bool => leftMap h k (.inl b))

theorem giant_mem (h k : History l) (b : Bool) :
    leftMap h k (.inl b) ∈ giantCoordinates h k :=
  Finset.mem_image.mpr ⟨b,Finset.mem_univ b,rfl⟩

theorem giantMap_injective (h k : History l) :
    Function.Injective (fun b : Bool => leftMap h k (.inl b)) := by
  intro b c he
  have hv := congrArg Subtype.val he
  exact Sum.inl.inj hv

def boolEquiv (h k : History l) : Bool ≃ giantCoordinates h k :=
  Equiv.ofBijective (fun b => ⟨leftMap h k (.inl b),giant_mem h k b⟩) ⟨by
    intro b c he
    exact giantMap_injective h k (congrArg Subtype.val he),by
    intro i
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp i.property
    exact ⟨b,Subtype.ext he⟩⟩

@[simp] theorem boolEquiv_apply (h k : History l) (b : Bool) :
    (boolEquiv h k b).val = leftMap h k (.inl b) := rfl

theorem left_small_not_mem (h k : History l)
    (i : Fin h.root.small.length ⊕ InternalKey h) :
    leftMap h k (.inr i) ∉ giantCoordinates h k := by
  intro hi
  obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hi
  have hv := congrArg Subtype.val he
  cases hv

theorem right_small_not_mem (h k : History l)
    (i : Fin k.root.small.length ⊕ InternalKey k) :
    rightMap h k (.inr i) ∉ giantCoordinates h k := by
  intro hi
  obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hi
  exact left_giant_ne_right_small h k b i he

def pairBackground (h k : History l) : PairKey h k → ℝ := fun i => (pairSample h k i:ℝ)

def insertGiants (h k : History l) (u : Bool → ℝ) : PairKey h k → ℝ :=
  HistoryActiveCoordinates.insert (giantCoordinates h k) (pairBackground h k) (fun i => u ((boolEquiv h k).symm i))

@[simp] theorem insertGiants_giant (h k : History l) (u : Bool → ℝ) (b : Bool) :
    insertGiants h k u (leftMap h k (.inl b)) = u b := by
  unfold insertGiants HistoryActiveCoordinates.insert
  rw [dite_eq_left (giant_mem h k b)]
  change u ((boolEquiv h k).symm (boolEquiv h k b)) = u b
  rw [Equiv.symm_apply_apply]

@[simp] theorem insertGiants_right_giant (h k : History l) (u : Bool → ℝ) (b : Bool) :
    insertGiants h k u (rightMap h k (.inl b)) = u b := by
  rw [← shared_giant h k b,insertGiants_giant]

@[simp] theorem insertGiants_left_small (h k : History l) (u : Bool → ℝ)
    (i : Fin h.root.small.length ⊕ InternalKey h) :
    insertGiants h k u (leftMap h k (.inr i)) = (integerSample h (.inr i):ℝ) := by
  simp only [insertGiants,HistoryActiveCoordinates.insert,dite_eq_right (left_small_not_mem h k i),pairBackground,leftMap_sample]

@[simp] theorem insertGiants_right_small (h k : History l) (u : Bool → ℝ)
    (i : Fin k.root.small.length ⊕ InternalKey k) :
    insertGiants h k u (rightMap h k (.inr i)) = (integerSample k (.inr i):ℝ) := by
  simp only [insertGiants,HistoryActiveCoordinates.insert,dite_eq_right (right_small_not_mem h k i),pairBackground]
  rfl

def realGiantSample (h : History l) (u : Bool → ℝ) : Key h → ℝ
  | .inl b => u b
  | .inr i => (integerSample h (.inr i):ℝ)

theorem insertGiants_leftMap (h k : History l) (u : Bool → ℝ) :
    (fun i => insertGiants h k u (leftMap h k i)) = realGiantSample h u := by
  funext i
  rcases i with b | i
  · exact insertGiants_giant h k u b
  · exact insertGiants_left_small h k u i

theorem insertGiants_rightMap (h k : History l) (u : Bool → ℝ) :
    (fun i => insertGiants h k u (rightMap h k i)) = realGiantSample k u := by
  funext i
  rcases i with b | i
  · exact insertGiants_right_giant h k u b
  · exact insertGiants_right_small h k u i

end Ostmann.Arithmetic.HistoryPairGiantCoordinates

end

end OAI
