import OAI.MathematicalPhysics.Heisenberg.PinSplicing

namespace OAI

section
noncomputable section
open scoped Classical Topology
open Set Filter Metric
open scoped ComplexConjugate
noncomputable section
open scoped Classical

noncomputable section
open scoped Classical
namespace Heisenberg.Return
open Equiv
variable {V : Type*}

variable [Fintype V]

end Heisenberg.Return

noncomputable section
open scoped Classical
namespace Heisenberg.Transport
open Equiv
open Heisenberg.Cycle Heisenberg.Return
variable {V W : Type*} [Fintype V] [Fintype W]

omit [Fintype V] [Fintype W] in
lemma pow_congr (e : V ≃ W) (π : Perm V) (n : ℕ) (x : V) :
    (e.permCongr π ^ n) (e x) = e ((π ^ n) x) := by
  induction n with
  | zero => rfl
  | succ n hn => simp only [pow_succ', Perm.mul_apply, hn, permCongr_apply, symm_apply_apply]

lemma sameCycle_congr (e : V ≃ W) (π : Perm V) (i j : V) :
    π.SameCycle i j ↔ (e.permCongr π).SameCycle (e i) (e j) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have he : (e.permCongr π ^ n) (e i) = e j := by rw [pow_congr, hn]
    rw [← he]
    exact (Perm.SameCycle.refl _ _).pow_right
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [pow_congr] at hn
    have he := e.injective hn
    rw [← he]
    exact (Perm.SameCycle.refl _ _).pow_right

def classCongr (e : V ≃ W) (π : Perm V) : Classes π ≃ Classes (e.permCongr π) :=
  Quotient.congr e (sameCycle_congr e π)

@[simp] lemma classCongr_mk (e : V ≃ W) (π : Perm V) (i : V) :
    classCongr e π (classOf π i) = classOf (e.permCongr π) (e i) := rfl

lemma missing_pred_congr (e : V ≃ W) (π : Perm V) (P : Set V) (Q : Set W)
    (h : ∀ i, i ∈ P ↔ e i ∈ Q) (c : Classes π) :
    (∀ i ∈ P, c ≠ classOf π i) ↔
      ∀ j ∈ Q, classCongr e π c ≠ classOf (e.permCongr π) j := by
  constructor
  · intro hc j hj he
    have hm : e.symm j ∈ P := (h _).mpr (by simpa using hj)
    apply hc _ hm
    apply (classCongr e π).injective
    simpa using he
  · intro hc i hi he
    apply hc (e i) ((h i).mp hi)
    rw [he, classCongr_mk]

lemma missingCount_congr (e : V ≃ W) (π : Perm V) (P : Set V) (Q : Set W)
    (h : ∀ i, i ∈ P ↔ e i ∈ Q) :
    missingCount π P = missingCount (e.permCongr π) Q :=
  Nat.card_congr ((classCongr e π).subtypeEquiv (missing_pred_congr e π P Q h))

lemma firstValue_congr_at_hit (e : V ≃ W) (π : Perm V) (P : Set V) (Q : Set W)
    (h : ∀ i, i ∈ P ↔ e i ∈ Q) (x : V) (hx : HasHit π P x) :
    firstValue (e.permCongr π) Q (e x) = (firstValue π P x).map e := by
  apply firstValue_unique π P (fun x => firstValue (e.permCongr π) Q (e x)) e
  · intro i hi
    exact firstValue_of_mem _ ((h i).mp hi)
  · intro i hi
    have he := firstValue_step (e.permCongr π) Q (e i) (mt (h i).mpr hi)
    simpa using he
  · exact hx

lemma nextPoint_congr (e : V ≃ W) (π : Perm V) (P : Set V) (Q : Set W)
    (h : ∀ i, i ∈ P ↔ e i ∈ Q) (i : P) :
    nextPoint (e.permCongr π) Q (e.subtypeEquiv h i) =
      e.subtypeEquiv h (nextPoint π P i) := by
  apply Subtype.ext
  have hh := firstValue_congr_at_hit e π P Q h (π i)
    ((hasHit_apply π P i).mpr (hasHit_of_mem π i.property))
  have he : e (π i) = (e.permCongr π) (e.subtypeEquiv h i : W) := by simp
  rw [he, nextValue_eq_nextPoint, nextValue_eq_nextPoint] at hh
  exact Option.some.inj hh

lemma nextPermutation_congr (e : V ≃ W) (π : Perm V) (P : Set V) (Q : Set W)
    (h : ∀ i, i ∈ P ↔ e i ∈ Q) :
    (e.subtypeEquiv h).permCongr (nextPermutation π P) =
      nextPermutation (e.permCongr π) Q := by
  apply Equiv.ext
  intro j
  obtain ⟨i, rfl⟩ := (e.subtypeEquiv h).surjective j
  simpa only [permCongr_apply, symm_apply_apply, nextPermutation, Equiv.ofBijective_apply] using (nextPoint_congr e π P Q h i).symm

def somePins (P : Set V) : P ≃ (some '' P : Set (Option V)) :=
  Equiv.ofBijective (fun i => ⟨some (i : V), ⟨i, i.property, rfl⟩⟩)
    ⟨by intro i j h; exact Subtype.ext (Option.some.inj (congrArg Subtype.val h)),
      by rintro ⟨_, i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩⟩

omit [Fintype V] in
@[simp] lemma somePins_apply (P : Set V) (i : P) :
    (somePins P i : Option V) = some i := rfl

lemma nextPoint_splice (π : Perm (Option V)) (P : Set V) (i : P) :
    nextPoint π (some '' P) (somePins P i) =
      somePins P (nextPoint (removeNone π) P i) := by
  apply Subtype.ext
  have hh := nextValue_splice π P (i : V) i.property
  change firstValue π (some '' P) (π (somePins P i : Option V)) = _ at hh
  rw [nextValue_eq_nextPoint, nextValue_eq_nextPoint] at hh
  exact Option.some.inj hh

lemma nextPermutation_splice (π : Perm (Option V)) (P : Set V) :
    (somePins P).permCongr (nextPermutation (removeNone π) P) =
      nextPermutation π (some '' P) := by
  apply Equiv.ext
  intro j
  obtain ⟨i, rfl⟩ := (somePins P).surjective j
  simpa only [permCongr_apply, symm_apply_apply, nextPermutation, Equiv.ofBijective_apply] using (nextPoint_splice π P i).symm

omit [Fintype V] in
lemma missingCount_univ (π : Perm V) : missingCount π Set.univ = 0 := by
  let : IsEmpty (MissingClasses π Set.univ) := ⟨by
    rintro ⟨c, hc⟩
    induction c using Quotient.inductionOn with | _ i => exact hc i (Set.mem_univ i) rfl⟩
  exact Nat.card_of_isEmpty

lemma nextPoint_all (π : Perm V) (i : V) :
    (nextPoint π Set.univ ⟨i, Set.mem_univ i⟩ : V) = π i := by
  have h := firstValue_of_mem π (P := Set.univ) (x := π i) (Set.mem_univ _)
  rw [nextValue_eq_nextPoint π Set.univ ⟨i, Set.mem_univ i⟩] at h
  exact Option.some.inj h

lemma nextPermutation_all (π : Perm V) :
    (Equiv.Set.univ V).symm.permCongr π = nextPermutation π Set.univ := by
  apply Equiv.ext
  intro i
  apply Subtype.ext
  change π (i : V) = (nextPoint π Set.univ i : V)
  exact (nextPoint_all π i).symm

end Heisenberg.Transport

noncomputable section
open scoped Classical
namespace Heisenberg.Pin
open Heisenberg.Cycle Heisenberg.Return Heisenberg.Transport
open Equiv
variable {V W Ω : Type*} [Fintype V] [Fintype W] [Fintype Ω]

lemma permutationSymbol_congr (e : V ≃ W) (π : Perm V) :
    MvPolynomial.rename (Sum.map e e) (permutationSymbol π) =
      permutationSymbol (e.permCongr π) := by
  simp only [permutationSymbol, map_prod, map_add, MvPolynomial.rename_X,
    Sum.map_inl, Sum.map_inr]
  rw [← e.prod_comp (fun j => MvPolynomial.X (Sum.inl j) +
    MvPolynomial.X (Sum.inr (e.permCongr π j)))]
  simp only [permCongr_apply, symm_apply_apply]

lemma lawSymbol_congr (e : V ≃ W) (μ : Ω → ℝ) (π : Ω → Perm V) :
    MvPolynomial.rename (Sum.map e e) (lawSymbol μ π) =
      lawSymbol μ (fun ω => e.permCongr (π ω)) := by
  simp only [lawSymbol, map_sum, map_mul, MvPolynomial.rename_C, permutationSymbol_congr]

lemma stable_law_congr (e : V ≃ W) (μ : Ω → ℝ) (π : Ω → Perm V)
    (hs : Stable (lawSymbol μ π)) : Stable (lawSymbol μ (fun ω => e.permCongr (π ω))) := by
  rw [← lawSymbol_congr]
  exact hs.rename (Sum.map e e)

def pinLaw (μ : Ω → ℝ) (π : Ω → Perm V) (P : Set V) : MvPolynomial (P ⊕ P) ℂ :=
  lawSymbol (fun ω => μ ω * (2 : ℝ) ^ missingCount (π ω) P)
    (fun ω => nextPermutation (π ω) P)

lemma pinLaw_all (μ : Ω → ℝ) (π : Ω → Perm V) :
    pinLaw μ π Set.univ = MvPolynomial.rename
      (Sum.map (Equiv.Set.univ V).symm (Equiv.Set.univ V).symm) (lawSymbol μ π) := by
  rw [lawSymbol_congr]
  unfold pinLaw
  simp only [missingCount_univ, pow_zero, mul_one, nextPermutation_all]
  exact congrArg (fun f : Fintype (Set.univ : Set V) =>
    @lawSymbol (Set.univ : Set V) Ω f inferInstance μ
      (fun ω => nextPermutation (π ω) Set.univ)) (Subsingleton.elim _ _)

lemma stable_pinLaw_all (μ : Ω → ℝ) (π : Ω → Perm V)
    (hs : Stable (lawSymbol μ π)) : Stable (pinLaw μ π Set.univ) := by
  rw [pinLaw_all]
  exact hs.rename _

omit [Fintype V] [Fintype Ω] in
lemma splice_mass_nonneg (μ : Ω → ℝ) (π : Ω → Perm (Option V))
    (hμ : ∀ ω, 0 ≤ μ ω) (ω : Ω) : 0 ≤ μ ω * spliceWeight (π ω) :=
  mul_nonneg (hμ ω) (le_trans zero_le_one (spliceWeight_ge_one (π ω)))

omit [Fintype V] in
lemma splice_mass_pos (μ : Ω → ℝ) (π : Ω → Perm (Option V))
    (hμ : ∀ ω, 0 ≤ μ ω) (hpos : 0 < ∑ ω, μ ω) :
    0 < ∑ ω, μ ω * spliceWeight (π ω) := by
  apply hpos.trans_le
  apply Finset.sum_le_sum
  intro ω _
  exact le_mul_of_one_le_right (hμ ω) (spliceWeight_ge_one (π ω))

universe u

theorem stable_pinLaw {V : Type u} [Fintype V] (μ : Ω → ℝ) (π : Ω → Perm V)
    (hμ : ∀ ω, 0 ≤ μ ω) (hpos : 0 < ∑ ω, μ ω) (hs : Stable (lawSymbol μ π))
    (P : Set V) : Stable (pinLaw μ π P) := by
  have hall (n : ℕ) : ∀ (V : Type u) [Fintype V], Fintype.card V = n →
      ∀ (μ : Ω → ℝ) (π : Ω → Perm V), (∀ ω, 0 ≤ μ ω) →
      0 < ∑ ω, μ ω → Stable (lawSymbol μ π) →
      ∀ P : Set V, Stable (pinLaw μ π P) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ hn μ π hμ hpos hs P
      by_cases hP : P = Set.univ
      · subst P
        exact stable_pinLaw_all μ π hs
      obtain ⟨q, hq⟩ : ∃ q : V, q ∉ P := by
        by_contra h
        apply hP
        exact Set.eq_univ_of_forall (by simpa only [not_exists, not_not] using h)
      let W := {i : V // i ≠ q}
      let e : Option W ≃ V := Equiv.optionSubtypeNe q
      let π' : Ω → Perm (Option W) := fun ω => e.symm.permCongr (π ω)
      let P' : Set W := {i | (i : V) ∈ P}
      have heπ (ω : Ω) : e.permCongr (π' ω) = π ω := by
        exact e.permCongr.apply_symm_apply (π ω)
      have heP : ∀ i : Option W, i ∈ some '' P' ↔ e i ∈ P := by
        intro i
        cases i with
        | none =>
          change (none ∈ some '' P') ↔ (Equiv.optionSubtypeNe q) none ∈ P
          rw [Equiv.optionSubtypeNe_none]
          simp [hq]
        | some i =>
          change (some i ∈ some '' P') ↔ (Equiv.optionSubtypeNe q) (some i) ∈ P
          rw [Equiv.optionSubtypeNe_some]
          simp [P']
      have hs' := stable_law_congr e.symm μ π hs
      have hss := stable_spliced_law μ π' hμ hpos hs'
      let μ' : Ω → ℝ := fun ω => μ ω * spliceWeight (π' ω)
      let π'' : Ω → Perm W := fun ω => Equiv.removeNone (π' ω)
      have hcard : Fintype.card W < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (x := q) (by simp)
      have hi := ih (Fintype.card W) hcard W rfl μ' π''
        (splice_mass_nonneg μ π' hμ) (splice_mass_pos μ π' hμ hpos) hss P'
      let ep : P' ≃ P := (somePins P').trans (e.subtypeEquiv heP)
      have hnext (ω : Ω) : ep.permCongr (nextPermutation (π'' ω) P') =
          nextPermutation (π ω) P := by
        have he := nextPermutation_congr e (π' ω) (some '' P') P heP
        rw [heπ] at he
        rw [← he, ← nextPermutation_splice]
        rfl
      have hweight (ω : Ω) : μ' ω * (2 : ℝ) ^ missingCount (π'' ω) P' =
          μ ω * (2 : ℝ) ^ missingCount (π ω) P := by
        have hc := missingCount_congr e (π' ω) (some '' P') P heP
        rw [heπ] at hc
        rw [← hc, cycle_weight_splice]
        simp only [μ', π'', spliceWeight, mul_assoc]
      have ht := stable_law_congr ep
        (fun ω => μ' ω * (2 : ℝ) ^ missingCount (π'' ω) P')
        (fun ω => nextPermutation (π'' ω) P') hi
      simpa only [hnext, hweight, pinLaw] using ht
  exact hall (Fintype.card V) V rfl μ π hμ hpos hs P

end Heisenberg.Pin
end
end
end
end
end
end

end OAI
