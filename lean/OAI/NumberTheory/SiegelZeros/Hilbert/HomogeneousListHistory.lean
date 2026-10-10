import Mathlib.RingTheory.Localization.AtPrime.Basic
import OAI.NumberTheory.SiegelZeros.Intersection.IsolatedIntersectionSteps
import OAI.NumberTheory.SiegelZeros.Intersection.LocalPrefixCutDimension
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.RegularCutHistory

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W22

variable {k σ : Type*} [Field k]

theorem homogeneous_degrees_pos_of_local_regular
    (T : Ideal (MvPolynomial σ k)) [T.IsPrime]
    (gs : List (MvPolynomial σ k)) (degrees : Fin gs.length → ℕ)
    (hhom : ∀ i : Fin gs.length, gs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime T)
      (gs.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime T)))) :
    ∀ i, 0 < degrees i := by
  intro i
  let μ := algebraMap (MvPolynomial σ k) (Localization.AtPrime T)
  let imap : Fin (gs.map μ).length := ⟨i.val, by simpa only [List.length_map] using i.isLt⟩
  have hn : μ gs[i] ≠ 0 := by
    simpa only [List.getElem_map, Fin.getElem_fin] using
      SiegelZeros.W20.regular_sequence_term_ne_zero (gs.map μ) hreg imap
  have hu : ¬ IsUnit (μ gs[i]) := by
    simpa only [List.getElem_map, Fin.getElem_fin] using
      SiegelZeros.W20.regular_sequence_term_not_isUnit (gs.map μ) hreg imap
  by_contra hpos
  have hd : degrees i = 0 := Nat.eq_zero_of_not_pos hpos
  have hh : gs[i].IsHomogeneous 0 := by simpa only [hd] using hhom i
  have hg : gs[i] = MvPolynomial.C ((gs[i]).coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (σ := σ)).mpr hh)
  have hc : (gs[i]).coeff 0 ≠ 0 := by
    intro hc
    apply hn
    rw [hg, hc, map_zero, map_zero]
  apply hu
  rw [hg]
  exact ((isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C).map μ

end WeightedTorusJets.W22

end

section

namespace WeightedTorusJets.W22

open WeightedTorusJets.W64
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {k σ : Type u} [Field k] [Fintype σ]

noncomputable def homogeneousListPrefix
    (gs : List (MvPolynomial σ k)) (degrees : Fin gs.length → ℕ)
    (hhom : ∀ i : Fin gs.length, gs[i].IsHomogeneous (degrees i)) (j : ℕ) :
    HomogeneousPolynomialIdeal k σ :=
  ⟨Ideal.ofList (gs.take j), SiegelZeros.W20.prefixIdeal_homogeneous gs degrees hhom j⟩

omit [Fintype σ] in
theorem homogeneousListPrefix_succ
    (gs : List (MvPolynomial σ k)) (degrees : Fin gs.length → ℕ)
    (hhom : ∀ i : Fin gs.length, gs[i].IsHomogeneous (degrees i))
    (j : ℕ) (hj : j < gs.length) :
    (homogeneousListPrefix gs degrees hhom (j+1)).val =
      (homogeneousListPrefix gs degrees hhom j).val ⊔ Ideal.span {gs[j]} := by
  simpa only [homogeneousListPrefix, Fin.getElem_fin, sup_comm] using
    SiegelZeros.W20.prefixIdeal_succ gs ⟨j,hj⟩

omit [Fintype σ] in
theorem local_regular_list_avoids_parent
    (T : Ideal (MvPolynomial σ k)) [T.IsPrime]
    (gs : List (MvPolynomial σ k))
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime T)
      (gs.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime T))))
    (j : ℕ) (hj : j < gs.length)
    (P : Ideal (MvPolynomial σ k))
    (hP : P ∈ (Ideal.ofList (gs.take j)).minimalPrimes) (hPT : P ≤ T) : gs[j] ∉ P := by
  have hregular : IsSMulRegular
      (Localization.AtPrime T ⧸ (Ideal.ofList (gs.take j)).map
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime T)))
      (algebraMap (MvPolynomial σ k) (Localization.AtPrime T) gs[j]) :=
    W16.regularPrefix_quotientMul_injective T T le_rfl gs hreg j hj
  exact SiegelZeros.W17.IsolatedIntersection.local_regular_avoids_retained_minimalPrime
    (Ideal.ofList (gs.take j)) T hP hPT hregular

theorem actualHP_zero_natDegree
    (v : σ) (hbot : (⊥ : Ideal (MvPolynomial σ k)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ k)) :
    (actualHP ⊥ hbot).natDegree = Fintype.card σ - 1 := by
  let degrees : Fin ([] : List (MvPolynomial σ k)).length → ℕ := fun i => Fin.elim0 i
  have hhom : ∀ i : Fin ([] : List (MvPolynomial σ k)).length,
      ([] : List (MvPolynomial σ k))[i].IsHomogeneous (degrees i) := fun i => Fin.elim0 i
  have hreg := RingTheory.Sequence.IsRegular.nil (MvPolynomial σ k) (MvPolynomial σ k)
  have hlen : ([] : List (MvPolynomial σ k)).length < Fintype.card σ :=
    Fintype.card_pos_iff.mpr ⟨v⟩
  have hnil : (Ideal.ofList ([] : List (MvPolynomial σ k))).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ k) := by simpa only [Ideal.ofList_nil] using hbot
  simpa only [Ideal.ofList_nil, List.length_nil, Nat.sub_zero] using
    actualHP_regular_sequence_natDegree [] degrees hhom hreg hlen hnil

theorem homogeneous_prefix_hilbert_degree
    (T : Ideal (MvPolynomial σ k)) [T.IsPrime] (v : σ) (hv : MvPolynomial.X v ∉ T)
    (gs : List (MvPolynomial σ k)) (degrees : Fin gs.length → ℕ)
    (hhom : ∀ i : Fin gs.length, gs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime T)
      (gs.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime T))))
    (hlen : gs.length < Fintype.card σ) (j : ℕ) (hj : j ≤ gs.length) :
    ∀ P : RetainedMinimalPrime (homogeneousListPrefix gs degrees hhom j).val T,
      (actualHP P.val (RetainedMinimalPrime.toComponent
        (homogeneousListPrefix gs degrees hhom j).property v hv P).homogeneous).natDegree =
          Fintype.card σ - j - 1 := by
  induction j with
  | zero =>
    intro P
    have hPbot : P.val ∈ (⊥ : Ideal (MvPolynomial σ k)).minimalPrimes := by
      simpa only [homogeneousListPrefix, List.take_zero, Ideal.ofList_nil] using P.property.1
    have heq : P.val = ⊥ := le_antisymm (hPbot.2 ⟨inferInstance,le_rfl⟩ bot_le) bot_le
    have hbot := Ideal.IsHomogeneous.bot (MvPolynomial.homogeneousSubmodule σ k)
    exact (congrArg Polynomial.natDegree (actualHP_congr _ hbot heq)).trans
      (by simpa only [Nat.sub_zero] using actualHP_zero_natDegree v hbot)
  | succ j ih =>
    intro Q
    have hjlt : j < gs.length := by omega
    have hprev := ih (by omega)
    let S := homogeneousListPrefix gs degrees hhom j
    let C := actualMultiplicityCycle S.val S.property T v hv
    let s := Fintype.card σ - j - 2
    have hparent : ∀ P : RetainedMinimalPrime S.val T,
        (actualHP P.val (C.component P).homogeneous).natDegree = s+1 := by
      intro P
      rw [hprev P]
      dsimp [s]
      omega
    have havoid : ∀ P : RetainedMinimalPrime S.val T, gs[j] ∉ P.val := fun P =>
      local_regular_list_avoids_parent T gs hreg j hjlt P.val P.property.1 P.property.2
    have hQcut : Q.val ∈ (S.val ⊔ Ideal.span {gs[j]}).minimalPrimes := by
      have heq := homogeneousListPrefix_succ gs degrees hhom j hjlt
      simpa only [heq] using Q.property.1
    obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hQcut.1.2)
    let P' : RetainedMinimalPrime S.val T := ⟨P,hP,hPQ.trans Q.property.2⟩
    have hQP : Q.val ∈ (Ideal.span {gs[j]} ⊔ P).minimalPrimes := by
      simpa only [sup_comm] using minimal_cut_of_intermediate_parent S.val P Q.val gs[j]
        hQcut hP.1.2 hPQ
    have hdim := RetainedPrimeCycle.retainedChild_dimension C gs[j] havoid s hparent T P'
      ⟨Q.val,hQP,Q.property.2⟩
    have hdeg := actualHP_natDegree_of_prime_dimension Q.val
      (RetainedMinimalPrime.toComponent
        (homogeneousListPrefix gs degrees hhom (j+1)).property v hv Q).homogeneous
      v (fun hx => hv (Q.property.2 hx)) s hdim
    have hs : s = Fintype.card σ - (j+1) - 1 := by dsimp [s]; omega
    exact hs ▸ hdeg

theorem homogeneous_list_actual_history
    (T : Ideal (MvPolynomial σ k)) [T.IsPrime] (v : σ) (hv : MvPolynomial.X v ∉ T)
    (gs : List (MvPolynomial σ k)) (degrees : Fin gs.length → ℕ)
    (hhom : ∀ i : Fin gs.length, gs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime T)
      (gs.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime T))))
    (hlen : gs.length < Fintype.card σ) (j : ℕ) (hj : j ≤ gs.length) :
    ActualRegularCutHistory T v hv (zeroHomogeneousIdeal (k := k) (σ := σ))
      (homogeneousListPrefix gs degrees hhom j)
      (∏ i ∈ Finset.range j, degreeAt degrees i) := by
  induction j with
  | zero =>
    have hzero : homogeneousListPrefix gs degrees hhom 0 = zeroHomogeneousIdeal := by
      apply Subtype.ext
      simp only [homogeneousListPrefix, zeroHomogeneousIdeal, List.take_zero, Ideal.ofList_nil]
    rw [hzero]
    simpa only [Finset.range_zero, Finset.prod_empty] using
      (ActualRegularCutHistory.nil (T := T) (v := v) (hv := hv)
        (S₀ := zeroHomogeneousIdeal (k := k) (σ := σ)))
  | succ j ih =>
    have hjlt : j < gs.length := by omega
    let S := homogeneousListPrefix gs degrees hhom j
    let F : RegularPrefixCut T v hv S :=
      { polynomial := gs[j]
        polynomialDegree := degrees ⟨j,hjlt⟩
        positiveDegree := homogeneous_degrees_pos_of_local_regular T gs degrees hhom hreg ⟨j,hjlt⟩
        homogeneous := by simpa only [Fin.getElem_fin] using hhom ⟨j,hjlt⟩
        avoidsParent := fun P =>
          local_regular_list_avoids_parent T gs hreg j hjlt P.val P.property.1 P.property.2
        dimensionIndex := Fintype.card σ - j - 2
        parentDegree := by
          intro P
          rw [homogeneous_prefix_hilbert_degree T v hv gs degrees hhom hreg hlen j (by omega) P]
          omega
        localDimension := fun Q => W29.regularPrefix_local_cut_dimension_one T Q.val Q.property.2
          gs hreg j hjlt Q.property.1
        regularAtChild := fun Q => W16.regularPrefix_quotientMul_injective T Q.val Q.property.2
          gs hreg j hjlt }
    have hnext : F.next = homogeneousListPrefix gs degrees hhom (j+1) := by
      apply Subtype.ext
      exact (homogeneousListPrefix_succ gs degrees hhom j hjlt).symm
    have hs := ActualRegularCutHistory.step (ih (by omega)) F
    rw [hnext] at hs
    simpa only [Finset.prod_range_succ, degreeAt, dite_eq_left hjlt] using hs

theorem homogeneous_local_regular_bezout
    (T : Ideal (MvPolynomial σ k)) [T.IsPrime] (v : σ) (hv : MvPolynomial.X v ∉ T)
    (gs : List (MvPolynomial σ k)) (degrees : Fin gs.length → ℕ)
    (hhom : ∀ i : Fin gs.length, gs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime T)
      (gs.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime T))))
    (hlen : gs.length < Fintype.card σ)
    (hT : T ∈ (Ideal.ofList gs).minimalPrimes) :
    Module.length (Localization.AtPrime T)
      (Localization.AtPrime T ⧸ (Ideal.ofList gs).map
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime T))) ≤
      ((∏ i ∈ Finset.range gs.length, degreeAt degrees i : ℕ) : ℕ∞) := by
  have hh := homogeneous_list_actual_history T v hv gs degrees hhom hreg hlen gs.length le_rfl
  have hT' : T ∈ (homogeneousListPrefix gs degrees hhom gs.length).val.minimalPrimes := by
    simpa only [homogeneousListPrefix, List.take_length] using hT
  have hbound := hh.local_length_bound (⟨T,hT',le_rfl⟩ :
    RetainedMinimalPrime (homogeneousListPrefix gs degrees hhom gs.length).val T)
  change Module.length (Localization.AtPrime T)
    (Localization.AtPrime T ⧸ (Ideal.ofList (gs.take gs.length)).map
      (algebraMap (MvPolynomial σ k) (Localization.AtPrime T))) ≤
      ((∏ i ∈ Finset.range gs.length, degreeAt degrees i : ℕ) : ℕ∞) at hbound
  have hlength := congrArg
    (fun js : List (MvPolynomial σ k) =>
      Module.length (Localization.AtPrime T)
        (Localization.AtPrime T ⧸ (Ideal.ofList js).map
          (algebraMap (MvPolynomial σ k) (Localization.AtPrime T))))
    (List.take_length (l := gs))
  exact hlength.symm.le.trans hbound

end WeightedTorusJets.W22

end

end SiegelZeros

end OAI
