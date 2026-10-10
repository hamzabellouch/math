import OAI.Analysis.FreeEntropy.EquidiscreteSignal

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

omit [Group G] in
theorem semicircularB_selfAdjoint [Group G] (b : B) : IsSelfAdjoint (semicircularB (N := N) (G := G) b) :=
  IsSelfAdjoint.add_star_self (creationB (N := N) (G := G) b)
 theorem semicircularN_selfAdjoint (i : N) : IsSelfAdjoint (semicircularN (B := B) (G := G) i) :=
  IsSelfAdjoint.add_star_self (creationN (B := B) (G := G) i)

 theorem backgroundAlgebra_le (J : Set N) :
    backgroundAlgebra (B := B) (G := G) J ≤ (algebra B N G).toStarSubalgebra.toSubalgebra := by
  apply Algebra.adjoin_le
  rintro _ ((⟨b,rfl⟩ | ⟨g,rfl⟩) | ⟨i,_,rfl⟩)
  · exact semicircularB_mem b
  · exact unitaryG_mem g
  · exact semicircularN_mem i

 theorem semicircularB_mem_background (J : Set N) (b : B) :
    semicircularB (N := N) (G := G) b ∈ backgroundAlgebra J :=
  Algebra.subset_adjoin (Or.inl (Or.inl ⟨b,rfl⟩))
 theorem semicircularN_mem_background (J : Set N) {i : N} (hi : i ∈ J) :
    semicircularN (B := B) (G := G) i ∈ backgroundAlgebra J :=
  Algebra.subset_adjoin (Or.inr ⟨i,hi,rfl⟩)

 theorem heatTuple_selfAdjoint {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {n : ℕ} (X S : Fin n → H →L[ℂ] H)
    (hX : ∀ i, IsSelfAdjoint (X i)) (hS : ∀ i, IsSelfAdjoint (S i)) (u : ℝ) (i : Fin n) :
    IsSelfAdjoint (heatTuple X S u i) := by
  change star (X i + (Real.sqrt u : ℂ) • S i) = _
  simp only [star_add, star_smul, Complex.star_def, Complex.conj_ofReal, (hX i).star_eq,
    (hS i).star_eq, heatTuple]

 theorem heatTuple_mem_background {n : ℕ} (J : Set N)
    (X S : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J) (hS : ∀ i, S i ∈ backgroundAlgebra J)
    (u : ℝ) (i : Fin n) : heatTuple X S u i ∈ backgroundAlgebra J :=
  (backgroundAlgebra J).add_mem (hX i) ((backgroundAlgebra J).smul_mem (hS i) _)

end FreeTensor

namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
abbrev H := Space (Fin p) (Fin ((p+1)+(p+1))) (Multiplicative (ZMod p))
abbrev M : VonNeumannAlgebra (H p) := algebra (Fin p) (Fin ((p+1)+(p+1))) (Multiplicative (ZMod p))
abbrev τ : TracialVector (M p) := tracialVector _ _ _
def C : Fin (p+1) → H p →L[ℂ] H p :=
  Fin.lastCases (equidiscreteSignal p) (fun i => semicircularB i)
def initialIndex (i : Fin (p+1)) : Fin ((p+1)+(p+1)) := Fin.castAdd (p+1) i
def auxiliaryIndex (i : Fin (p+1)) : Fin ((p+1)+(p+1)) := Fin.natAdd (p+1) i
def initialNoise (i : Fin (p+1)) : H p →L[ℂ] H p := semicircularN (initialIndex p i)
def auxiliaryNoise (i : Fin (p+1)) : H p →L[ℂ] H p := semicircularN (auxiliaryIndex p i)
def oldNoise : Set (Fin ((p+1)+(p+1))) := Set.range (initialIndex p)
def X (h : ℝ) : Fin (p+1) → H p →L[ℂ] H p := heatTuple (C p) (initialNoise p) h

omit [NeZero p] in
theorem initialIndex_injective [NeZero p] : Function.Injective (initialIndex p) := Fin.castAdd_injective (p+1) (p+1)

omit [NeZero p] in
theorem auxiliaryIndex_injective [NeZero p] : Function.Injective (auxiliaryIndex p) := Fin.natAdd_injective (p+1) (p+1)

omit [NeZero p] in
theorem auxiliaryIndex_fresh [NeZero p] (i : Fin (p+1)) : auxiliaryIndex p i ∉ oldNoise p := by
  rintro ⟨j,h⟩
  have hv := congrArg Fin.val h
  simp only [initialIndex, auxiliaryIndex, Fin.val_castAdd, Fin.val_natAdd] at hv
  have hj := j.isLt
  omega

@[simp] theorem C_last : C p (Fin.last p) = equidiscreteSignal p := by simp [C]
@[simp] theorem C_castSucc (i : Fin p) : C p i.castSucc = semicircularB i := by simp [C]

 theorem C_selfAdjoint (i : Fin (p+1)) : IsSelfAdjoint (C p i) := by
  induction i using Fin.lastCases with
  | last => rw [C_last]; exact equidiscreteSignal_selfAdjoint p
  | cast i => rw [C_castSucc]; exact semicircularB_selfAdjoint i

 theorem C_mem_background (J : Set (Fin ((p+1)+(p+1)))) (i : Fin (p+1)) :
    C p i ∈ backgroundAlgebra J := by
  induction i using Fin.lastCases with
  | last => rw [C_last]; exact equidiscreteSignal_mem_background p J
  | cast i => rw [C_castSucc]; exact semicircularB_mem_background J i

 theorem C_mem (i : Fin (p+1)) : C p i ∈ M p := backgroundAlgebra_le ∅ (C_mem_background p ∅ i)

 theorem C_norm_le (hp : 2 ≤ p) (i : Fin (p+1)) : ‖C p i‖ ≤ 2 := by
  induction i using Fin.lastCases with
  | last => rw [C_last]; exact (equidiscreteSignal_norm_le p hp).trans (by norm_num)
  | cast i => rw [C_castSucc]; exact semicircularB_norm_le i

 theorem initialNoise_free : FreeStandardNoise (τ p) (C p) (initialNoise p) :=
  freeStandardNoise ∅ (C p) (C_mem_background p ∅) (initialIndex p)
    (initialIndex_injective p) (by simp)

 theorem X_mem_background (h : ℝ) (i : Fin (p+1)) :
    X p h i ∈ backgroundAlgebra (oldNoise p) := by
  apply heatTuple_mem_background _ _ _ (C_mem_background p (oldNoise p))
  intro j
  exact semicircularN_mem_background _ ⟨j,rfl⟩

 theorem auxiliaryNoise_free (h : ℝ) : FreeStandardNoise (τ p) (X p h) (auxiliaryNoise p) :=
  freeStandardNoise (oldNoise p) (X p h) (X_mem_background p h) (auxiliaryIndex p)
    (auxiliaryIndex_injective p) (auxiliaryIndex_fresh p)

 theorem X_mem (h : ℝ) (i : Fin (p+1)) : X p h i ∈ M p :=
  backgroundAlgebra_le _ (X_mem_background p h i)
 theorem X_selfAdjoint (h : ℝ) (i : Fin (p+1)) : IsSelfAdjoint (X p h i) :=
  heatTuple_selfAdjoint (C p) (initialNoise p) (C_selfAdjoint p)
    (fun _index => semicircularN_selfAdjoint _) h i

omit [NeZero p] in
theorem auxiliaryNoise_mem [NeZero p] (i : Fin (p+1)) : auxiliaryNoise p i ∈ M p := semicircularN_mem _

omit [NeZero p] in
theorem auxiliaryNoise_selfAdjoint [NeZero p] (i : Fin (p+1)) : IsSelfAdjoint (auxiliaryNoise p i) :=
  semicircularN_selfAdjoint _

 theorem X_norm_le (hp : 2 ≤ p) (h : ℝ) (i : Fin (p+1)) :
    ‖X p h i‖ ≤ 2 + 2 * Real.sqrt h := by
  apply (norm_add_le _ _).trans
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg h)]
  exact add_le_add (C_norm_le p hp i)
    (by
      have hn : ‖initialNoise p i‖ ≤ 2 := semicircularN_norm_le _
      nlinarith [Real.sqrt_nonneg h])

 theorem heat_fisher_le (h s : ℝ) (hs : 0 < s) :
    freeFisher (τ p) (heatTuple (X p h) (auxiliaryNoise p) s) ≤ ENNReal.ofReal ((p+1 : ℕ)/s) :=
  heat_freeFisher_le (oldNoise p) (X p h) (X_mem_background p h)
    (auxiliaryIndex p) (auxiliaryIndex_injective p) (auxiliaryIndex_fresh p) s hs

 theorem heat_fisher_measurable (h : ℝ) : Measurable (fun s : Set.Ioi (0 : ℝ) =>
    freeFisher (τ p) (heatTuple (X p h) (auxiliaryNoise p) s)) :=
  heat_freeFisher_measurable (oldNoise p) (X p h) (X_mem_background p h)
    (auxiliaryIndex p) (auxiliaryIndex_injective p) (auxiliaryIndex_fresh p)

end Model
end FiniteEntropySeparation

end

end OAI
