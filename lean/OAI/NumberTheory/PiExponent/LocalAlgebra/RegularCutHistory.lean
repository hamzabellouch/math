import OAI.NumberTheory.PiExponent.LocalAlgebra.CompleteIntersectionComponentBound
import OAI.NumberTheory.PiExponent.LocalAlgebra.MultiplicityCycles

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {k σ : Type u} [Field k] [Fintype σ]

abbrev HomogeneousPolynomialIdeal (k σ : Type u) [Field k] :=
  {I : Ideal (MvPolynomial σ k) // I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)}

noncomputable def zeroHomogeneousIdeal : HomogeneousPolynomialIdeal k σ :=
  ⟨⊥, Ideal.IsHomogeneous.bot (MvPolynomial.homogeneousSubmodule σ k)⟩

structure RegularPrefixCut
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (S : HomogeneousPolynomialIdeal k σ) where
  polynomial : MvPolynomial σ k
  polynomialDegree : ℕ
  positiveDegree : 0 < polynomialDegree
  homogeneous : polynomial.IsHomogeneous polynomialDegree
  avoidsParent : ∀ P : RetainedMinimalPrime S.val T, polynomial ∉ P.val
  dimensionIndex : ℕ
  parentDegree : ∀ P : RetainedMinimalPrime S.val T,
    (actualHP P.val (RetainedMinimalPrime.toComponent S.property v hv P).homogeneous).natDegree =
      dimensionIndex+1
  localDimension : ∀ Q : RetainedMinimalPrime (S.val ⊔ Ideal.span {polynomial}) T,
    ringKrullDim (Localization.AtPrime Q.val ⧸
      S.val.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val))) = 1
  regularAtChild : ∀ Q : RetainedMinimalPrime (S.val ⊔ Ideal.span {polynomial}) T,
    Function.Injective (W28.LocalIntersection.quotientMul
      (S.val.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val)))
      (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val) polynomial))

namespace RegularPrefixCut

variable {T : Ideal (MvPolynomial σ k)} {v : σ} {hv : MvPolynomial.X v ∉ T}
  {S : HomogeneousPolynomialIdeal k σ}

noncomputable def next (F : RegularPrefixCut T v hv S) : HomogeneousPolynomialIdeal k σ :=
  ⟨S.val ⊔ Ideal.span {F.polynomial}, cut_ideal_homogeneous S.val S.property F.polynomial F.homogeneous⟩

theorem degree_step (F : RegularPrefixCut T v hv S) :
    (actualMultiplicityCycle F.next.val F.next.property T v hv).degree ≤
      (F.polynomialDegree : ℚ) * (actualMultiplicityCycle S.val S.property T v hv).degree :=
  actualMultiplicityCycle_cut_degree_le S.val S.property F.polynomial F.polynomialDegree
    F.positiveDegree F.homogeneous T v hv F.avoidsParent F.dimensionIndex F.parentDegree
    F.localDimension F.regularAtChild

end RegularPrefixCut

inductive ActualRegularCutHistory
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (S₀ : HomogeneousPolynomialIdeal k σ) : HomogeneousPolynomialIdeal k σ → ℕ → Prop
  | nil : ActualRegularCutHistory T v hv S₀ S₀ 1
  | step {S : HomogeneousPolynomialIdeal k σ} {e : ℕ}
      (previous : ActualRegularCutHistory T v hv S₀ S e)
      (F : RegularPrefixCut T v hv S) :
      ActualRegularCutHistory T v hv S₀ F.next (e * F.polynomialDegree)

theorem ActualRegularCutHistory.degree_bound
    {T : Ideal (MvPolynomial σ k)} {v : σ} {hv : MvPolynomial.X v ∉ T}
    {S₀ S : HomogeneousPolynomialIdeal k σ} {e : ℕ}
    (h : ActualRegularCutHistory T v hv S₀ S e) :
    (actualMultiplicityCycle S.val S.property T v hv).degree ≤
      (e : ℚ) * (actualMultiplicityCycle S₀.val S₀.property T v hv).degree := by
  induction h with
  | nil => simp
  | @step S e previous F ih =>
    calc
      _ ≤ (F.polynomialDegree : ℚ) *
          (actualMultiplicityCycle S.val S.property T v hv).degree := F.degree_step
      _ ≤ (F.polynomialDegree : ℚ) * ((e : ℚ) *
          (actualMultiplicityCycle S₀.val S₀.property T v hv).degree) :=
        mul_le_mul_of_nonneg_left ih (Nat.cast_nonneg _)
      _ = _ := by rw [Nat.cast_mul]; ring

theorem actualMultiplicityCycle_zero_degree
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T) :
    (actualMultiplicityCycle (⊥ : Ideal (MvPolynomial σ k))
      (Ideal.IsHomogeneous.bot (MvPolynomial.homogeneousSubmodule σ k)) T v hv).degree = 1 := by
  let hbot := Ideal.IsHomogeneous.bot (MvPolynomial.homogeneousSubmodule σ k)
  have hminimal : (⊥ : Ideal (MvPolynomial σ k)) ∈ (⊥ : Ideal (MvPolynomial σ k)).minimalPrimes :=
    ⟨⟨inferInstance, le_rfl⟩, fun _ _ _ => bot_le⟩
  let B : RetainedMinimalPrime (⊥ : Ideal (MvPolynomial σ k)) T := ⟨⊥, hminimal, bot_le⟩
  have hevery (P : RetainedMinimalPrime (⊥ : Ideal (MvPolynomial σ k)) T) : P = B := by
    apply Subtype.ext
    exact le_antisymm (P.property.1.2 ⟨inferInstance, le_rfl⟩ bot_le) bot_le
  have hlength : actualLocalLength (⊥ : Ideal (MvPolynomial σ k)) ⊥ = 1 := by
    unfold actualLocalLength
    rw [localized_prime_factor_length_one]
    exact ENat.toNat_natCast 1
  let degrees : Fin ([] : List (MvPolynomial σ k)).length → ℕ := fun i => Fin.elim0 i
  have hhom : ∀ i : Fin ([] : List (MvPolynomial σ k)).length,
      ([] : List (MvPolynomial σ k))[i].IsHomogeneous (degrees i) := fun i => Fin.elim0 i
  have hreg := RingTheory.Sequence.IsRegular.nil (MvPolynomial σ k) (MvPolynomial σ k)
  have hlen : ([] : List (MvPolynomial σ k)).length < Fintype.card σ :=
    Fintype.card_pos_iff.mpr ⟨v⟩
  have hnilhom : (Ideal.ofList ([] : List (MvPolynomial σ k))).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ k) := by simpa only [Ideal.ofList_nil] using hbot
  have hdegree : actualMultiplicity (⊥ : Ideal (MvPolynomial σ k)) hbot
      (actualHP ⊥ hbot).natDegree = 1 := by
    simpa only [Ideal.ofList_nil, List.length_nil, Finset.range_zero, Finset.prod_empty,
      Nat.cast_one] using actualMultiplicity_regular_sequence [] degrees hhom hreg hlen hnilhom
  unfold RetainedPrimeCycle.degree
  change (∑ P : RetainedMinimalPrime (⊥ : Ideal (MvPolynomial σ k)) T,
    (actualLocalLength (⊥ : Ideal (MvPolynomial σ k)) P.val : ℚ) *
      (RetainedMinimalPrime.toComponent hbot v hv P).hilbertDegree) = 1
  rw [Finset.sum_eq_single B]
  · change (actualLocalLength (⊥ : Ideal (MvPolynomial σ k)) ⊥ : ℚ) *
      actualMultiplicity (⊥ : Ideal (MvPolynomial σ k)) hbot (actualHP ⊥ hbot).natDegree = 1
    rw [hlength, Nat.cast_one, hdegree, one_mul]
  · intro P _ hne
    exact False.elim (hne (hevery P))
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ B))

theorem ActualRegularCutHistory.local_length_bound
    {T : Ideal (MvPolynomial σ k)} {v : σ} {hv : MvPolynomial.X v ∉ T}
    {S : HomogeneousPolynomialIdeal k σ} {e : ℕ}
    (h : ActualRegularCutHistory T v hv (zeroHomogeneousIdeal (k := k) (σ := σ)) S e)
    (Q : RetainedMinimalPrime S.val T) :
    Module.length (Localization.AtPrime Q.val)
      (Localization.AtPrime Q.val ⧸ S.val.map
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val))) ≤ (e : ℕ∞) := by
  let C := actualMultiplicityCycle S.val S.property T v hv
  have hc := C.coefficientAt_le_degree (RetainedMinimalPrime.toComponent S.property v hv Q)
  rw [actualMultiplicityCycle_coefficient S.val S.property T v hv Q] at hc
  have hd := h.degree_bound
  dsimp only [zeroHomogeneousIdeal] at hd
  rw [actualMultiplicityCycle_zero_degree T v hv, mul_one] at hd
  have hn : actualLocalLength S.val Q.val ≤ e := by exact_mod_cast hc.trans hd
  rw [actualLocalLength_spec S.val Q.val S.property Q.property.1]
  exact_mod_cast hn

end PiExponentJets.W22

end OAI
