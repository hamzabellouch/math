import OAI.Combinatorics.ProgressionColoring.AnchoredPatternDefinitions
import OAI.Combinatorics.ProgressionColoring.AdaptiveMeshBreakpoints
import OAI.Combinatorics.ProgressionColoring.LabelIncidences
import OAI.Combinatorics.ProgressionColoring.ComparisonOutputs

namespace OAI

noncomputable section

universe uLabel

namespace QuantitativeVanDerWaerden.AnchoredPatterns

open Set
open scoped BigOperators

variable {D h : ℕ}

/-- Only rotating coordinates can produce a dummy scalar output. -/
def secondOutput (A : AdaptiveMesh) (eta : ℝ) (R : Realization D) (lambda : ℕ)
    (t : Fin D → Fin h) (i : Fin D) (z : Fin h) : Option A.Label := by
  classical
  exact if stationary lambda t i then some (A.meshLabel (secondPath R lambda t z i))
    else if eta ≤ rho (secondPath R lambda t z i) then
      some (A.meshLabel (secondPath R lambda t z i)) else none

theorem secondOutput_eq_some_of_regular (A : AdaptiveMesh) (eta : ℝ)
    (R : Realization D) (lambda : ℕ) (t : Fin D → Fin h) (z : Fin h)
    (hz : regular eta R lambda t z) (i : Fin D) :
    secondOutput A eta R lambda t i z = some (A.meshLabel (secondPath R lambda t z i)) := by
  classical
  by_cases hi : stationary lambda t i
  · simp [secondOutput, hi]
  · simp [secondOutput, hi, hz i hi]

/-- Scalar outputs determine the whole recorded word, including its mask.
There is no extra independent factor `2^h`. -/
theorem recordedWord_eq_assembleWord (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh)
    (eta : ℝ) (R : Realization D) (lambda : ℕ) (t : Fin D → Fin h) :
    recordedWord n hn A eta R lambda t =
      assembleWord (fun i z => UniformMesh.label n hn (firstPath R t z i))
        (secondOutput A eta R lambda t) := by
  classical
  funext z
  by_cases hz : regular eta R lambda t z
  · have hs : (fun i => secondOutput A eta R lambda t i z) =
        fun i => some (A.meshLabel (secondPath R lambda t z i)) :=
      funext (secondOutput_eq_some_of_regular A eta R lambda t z hz)
    simp only [recordedWord, ite_eq_left hz, assembleWord, hs, assembleLabel_some, fullLabel]
  · have hi : ∃ i, secondOutput A eta R lambda t i z = none := by
      obtain ⟨i, hi⟩ := not_forall.mp hz
      have hstationary : ¬ stationary lambda t i := by
        intro hs
        exact hi (fun hn => False.elim (hn hs))
      have hcut : ¬ eta ≤ rho (secondPath R lambda t z i) := by
        intro hc
        exact hi (fun _ => hc)
      exact ⟨i, by simp [secondOutput, hstationary, hcut]⟩
    rw [recordedWord, ite_eq_right hz]
    exact ((assembleWord_dummy_iff _ _ z).mpr hi).symm

def anchorCoefficient (z0 z : Fin h) : ℝ := ((z.val : ℝ) - z0.val) / h

def anchoredFirst (R : Realization D) (t : Fin D → Fin h)
    (z0 z : Fin h) (i : Fin D) : ℝ :=
  Int.fract (firstPath R t z0 i) + anchorCoefficient z0 z * (t i).val +
    anchorCoefficient z0 z * R.u i

def anchoredSecond (R : Realization D) (lambda : ℕ) (t : Fin D → Fin h)
    (z0 z : Fin h) (i : Fin D) : ℝ :=
  centered (secondPath R lambda t z0 i) +
    anchorCoefficient z0 z * ((lambda : ℝ) * (t i).val) +
    anchorCoefficient z0 z * R.v i

theorem firstPath_reanchor (R : Realization D) (t : Fin D → Fin h)
    (z0 z : Fin h) (i : Fin D) :
    firstPath R t z i = anchoredFirst R t z0 z i + (⌊firstPath R t z0 i⌋ : ℤ) := by
  simp only [anchoredFirst, firstPath, anchorCoefficient, Int.fract, div_eq_mul_inv]
  ring

theorem secondPath_reanchor (R : Realization D) (lambda : ℕ) (t : Fin D → Fin h)
    (z0 z : Fin h) (i : Fin D) :
    secondPath R lambda t z i = anchoredSecond R lambda t z0 z i +
      (⌊secondPath R lambda t z0 i + 1 / 2⌋ : ℤ) := by
  simp only [anchoredSecond, secondPath, anchorCoefficient, centered, div_eq_mul_inv]
  ring

theorem firstLabel_reanchor (n : ℕ) (hn : 0 < n) (R : Realization D)
    (t : Fin D → Fin h) (z0 z : Fin h) (i : Fin D) :
    UniformMesh.label n hn (firstPath R t z i) =
      UniformMesh.label n hn (anchoredFirst R t z0 z i) := by
  rw [firstPath_reanchor R t z0 z i]
  exact UniformMesh.label_add_int n hn _ _

theorem secondLabel_reanchor (A : AdaptiveMesh) (R : Realization D) (lambda : ℕ)
    (t : Fin D → Fin h) (z0 z : Fin h) (i : Fin D) :
    A.meshLabel (secondPath R lambda t z i) = A.meshLabel (anchoredSecond R lambda t z0 z i) := by
  rw [secondPath_reanchor R lambda t z0 z i]
  exact A.meshLabel_add_int _ _

theorem rho_reanchor (R : Realization D) (lambda : ℕ)
    (t : Fin D → Fin h) (z0 z : Fin h) (i : Fin D) :
    rho (secondPath R lambda t z i) = rho (anchoredSecond R lambda t z0 z i) := by
  rw [secondPath_reanchor R lambda t z0 z i]
  exact rho_add_int _ _

theorem abs_anchorCoefficient_lt_one (hh : 0 < h) (z0 z : Fin h) :
    |anchorCoefficient z0 z| < 1 := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hz0 : (0 : ℝ) ≤ z0.val := by positivity
  have hz : (0 : ℝ) ≤ z.val := by positivity
  have hz0h : (z0.val : ℝ) < h := by exact_mod_cast z0.isLt
  have hzh : (z.val : ℝ) < h := by exact_mod_cast z.isLt
  rw [anchorCoefficient, abs_div, abs_of_pos hhR, div_lt_one hhR, abs_lt]
  constructor <;> linarith

/-- Stationary rational translations are integer shifts, even though the
drift may be nonzero. -/
theorem stationary_translation_integer (lambda : ℕ) (t : Fin D → Fin h)
    (hh : 0 < h) (i : Fin D) (hi : stationary lambda t i) (z0 z : Fin h) :
    ∃ m : ℤ, anchorCoefficient z0 z * ((lambda : ℝ) * (t i).val) = m := by
  obtain ⟨r, hr⟩ := hi
  have hrR : (lambda : ℝ) * (t i).val = (h : ℝ) * r := by exact_mod_cast hr
  refine ⟨((z.val : ℤ) - z0.val) * r, ?_⟩
  rw [hrR]
  have hhR : (h : ℝ) ≠ 0 := by positivity
  simp only [anchorCoefficient, Int.cast_mul, Int.cast_sub, Int.cast_natCast]
  field_simp [hhR]

/-- The two genuinely free scalar parameters are anchor position and drift. -/
def scalarDomain (left right width : ℝ) : Set (Fin 2 → ℝ) :=
  {p | left ≤ p 0 ∧ p 0 ≤ right ∧ |p 1| ≤ width}

def scalarValue (c tau : Fin h → ℝ) (p : Fin 2 → ℝ) (z : Fin h) : ℝ :=
  p 0 + tau z + c z * p 1

private theorem scalarValue_mem (left right width : ℝ) (c tau : Fin h → ℝ)
    (hc : ∀ z, |c z| ≤ 1) (p : Fin 2 → ℝ)
    (hp : p ∈ scalarDomain left right width) (z : Fin h) :
    scalarValue c tau p z ∈ Icc (left + tau z - width) (right + tau z + width) := by
  have hb : |c z * p 1| ≤ width := by
    calc
      |c z * p 1| = |c z| * |p 1| := abs_mul _ _
      _ ≤ 1 * |p 1| := mul_le_mul_of_nonneg_right (hc z) (abs_nonneg _)
      _ ≤ width := by simpa only [one_mul] using hp.2.2
  have hab := abs_le.mp hb
  change left + tau z - width ≤ p 0 + tau z + c z * p 1 ∧
    p 0 + tau z + c z * p 1 ≤ right + tau z + width
  constructor <;> linarith [hp.1, hp.2.1]

private def comparisonForm (c tau b : ℝ) : AffineForm 2 where
  linear := fun j => if j = 0 then 1 else c
  constant := tau - b

private theorem comparisonForm_eval (c tau b : ℝ) (p : Fin 2 → ℝ) :
    (comparisonForm c tau b).eval p = p 0 + tau + c * p 1 - b := by
  simp [AffineForm.eval, comparisonForm, Fin.sum_univ_two]
  ring

/-- A scalar word is counted by its actual affine comparisons. The breakpoint
sets are fixed before the two real parameters are selected. -/
private theorem scalar_family {K : ℕ} {Label : Type uLabel}
    (c tau : Fin h → ℝ) (domain : Set (Fin 2 → ℝ))
    (output : Fin h → ℝ → Label) (B : Fin h → Finset ℝ)
    (hB : ∀ z, (B z).card ≤ K)
    (hfactor : ∀ p ∈ domain, ∀ q ∈ domain, ∀ z,
      (∀ b ∈ B z,
        ternarySign (scalarValue c tau p z - b) =
          ternarySign (scalarValue c tau q z - b)) →
      output z (scalarValue c tau p z) = output z (scalarValue c tau q z)) :
    ∃ S : Finset (Fin h → Label),
      (∀ w, w ∈ S ↔ ∃ p ∈ domain, (fun z => output z (scalarValue c tau p z)) = w) ∧
      S.card ≤ 16 * (K * h + 1) ^ 6 := by
  classical
  let Index := Σ z : Fin h, {b : ℝ // b ∈ B z}
  let e := Fintype.equivFin Index
  let forms : Fin (Fintype.card Index) → AffineForm 2 := fun j =>
    comparisonForm (c (e.symm j).1) (tau (e.symm j).1) (e.symm j).2.val
  obtain ⟨S, hS, hcard⟩ := finite_outputs_of_comparisons forms domain
    (fun p z => output z (scalarValue c tau p z)) (by
      intro p hp q hq hs
      funext z
      apply hfactor p hp q hq z
      intro b hb
      have hj := congrFun hs (e ⟨z, ⟨b, hb⟩⟩)
      have hforms : forms (e ⟨z, ⟨b, hb⟩⟩) = comparisonForm (c z) (tau z) b := by
        dsimp only [forms]
        rw [e.symm_apply_apply]
      change ternarySign ((forms (e ⟨z, ⟨b, hb⟩⟩)).eval p) =
        ternarySign ((forms (e ⟨z, ⟨b, hb⟩⟩)).eval q) at hj
      rw [hforms, comparisonForm_eval, comparisonForm_eval] at hj
      exact hj)
  have hIndex : Fintype.card Index ≤ K * h := by
    calc
      Fintype.card Index = ∑ z : Fin h, (B z).card := by simp [Index]
      _ ≤ ∑ _z : Fin h, K := Finset.sum_le_sum (fun z _ => hB z)
      _ = K * h := by simp [Nat.mul_comm]
  refine ⟨S, hS, ?_⟩
  exact hcard.trans (Nat.mul_le_mul_left 16
    (Nat.pow_le_pow_left (Nat.add_le_add_right hIndex 1) 6))

private theorem uniform_scalar_family (n : ℕ) (hn : 0 < n) (hD : 0 < D)
    (anchor : Fin n) (c tau : Fin h → ℝ) (hc : ∀ z, |c z| ≤ 1) :
    ∃ S : Finset (Fin h → Fin n),
      (∀ w, w ∈ S ↔ ∃ p ∈ scalarDomain (UniformMesh.left n anchor)
        (UniformMesh.right n anchor) (1 / (n : ℝ)),
        (fun z => UniformMesh.label n hn (scalarValue c tau p z)) = w) ∧
      S.card ≤ 16 * (16004 * D * h + 1) ^ 6 := by
  classical
  let lo := fun z => UniformMesh.left n anchor + tau z - 1 / (n : ℝ)
  let hi := fun z => UniformMesh.right n anchor + tau z + 1 / (n : ℝ)
  let B := fun z => (UniformMesh.liftedEndpoints n (lo z) (hi z)).image
    (fun j : ℤ => (j : ℝ) / n)
  apply scalar_family c tau _ (fun _ => UniformMesh.label n hn) B
  · intro z
    have hwidth : hi z - lo z ≤ 3 / (n : ℝ) := by
      have hw := UniformMesh.width_eq n anchor
      dsimp [hi, lo]
      simp only [div_eq_mul_inv] at hw ⊢
      linarith
    calc
      (B z).card ≤ (UniformMesh.liftedEndpoints n (lo z) (hi z)).card :=
        Finset.card_image_le
      _ ≤ 4 := UniformMesh.card_liftedEndpoints_le_four n hn _ _ hwidth
      _ ≤ 16004 * D := by omega
  · intro p hp q hq z hs
    apply UniformMesh.label_eq_of_signs_eq n hn (lo z) (hi z) _ _
      (scalarValue_mem _ _ _ c tau hc p hp z) (scalarValue_mem _ _ _ c tau hc q hq z)
    intro j hj
    exact hs _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)

private theorem stationary_scalar_family (A : AdaptiveMesh) (hD : 0 < D)
    (anchor : A.Label) (c : Fin h → ℝ) (m : Fin h → ℤ)
    (hc : ∀ z, |c z| ≤ 1) :
    ∃ S : Finset (Fin h → Option A.Label),
      (∀ w, w ∈ S ↔ ∃ p ∈ scalarDomain (A.left anchor) (A.right anchor) (A.width anchor),
        (fun z => some (A.meshLabel (scalarValue c (fun z => (m z : ℝ)) p z))) = w) ∧
      S.card ≤ 16 * (16004 * D * h + 1) ^ 6 := by
  classical
  choose B hB hfactor using (fun z => A.stationary_breakpoint_factorization anchor (m z))
  apply scalar_family c (fun z => (m z : ℝ)) _ (fun _ x => some (A.meshLabel x)) B
  · intro z
    exact (hB z).trans (by omega)
  · intro p hp q hq z hs
    exact congrArg some (hfactor z _ _
      (scalarValue_mem _ _ _ c (fun z => (m z : ℝ)) hc p hp z)
      (scalarValue_mem _ _ _ c (fun z => (m z : ℝ)) hc q hq z) hs)

private theorem rotating_scalar_family (A : AdaptiveMesh) (hD : 0 < D)
    (anchor : A.Label) (c tau : Fin h → ℝ) (hc : ∀ z, |c z| ≤ 1) :
    ∃ S : Finset (Fin h → Option A.Label),
      (∀ w, w ∈ S ↔ ∃ p ∈ scalarDomain (A.left anchor) (A.right anchor) A.H,
        (fun z => A.truncatedLabel (1 / (1000 * (D : ℝ))) (scalarValue c tau p z)) = w) ∧
      S.card ≤ 16 * (16004 * D * h + 1) ^ 6 := by
  classical
  let lo := fun z => A.left anchor + tau z - A.H
  let hi := fun z => A.right anchor + tau z + A.H
  have hlen : ∀ z, lo z ≤ hi z ∧ hi z - lo z ≤ 4 * A.H := by
    intro z
    have hw := A.width_le_two_H anchor
    have hwpos := A.width_pos anchor
    dsimp [lo, hi]
    change A.left anchor + tau z - A.H ≤ A.right anchor + tau z + A.H ∧ _
    constructor <;> linarith [A.H_pos, show A.width anchor =
      A.right anchor - A.left anchor from rfl]
  choose B hB hfactor using (fun z =>
    A.rotating_breakpoint_factorization D hD (lo z) (hi z) (hlen z).1 (hlen z).2)
  apply scalar_family c tau _ (fun _ => A.truncatedLabel (1 / (1000 * (D : ℝ)))) B hB
  intro p hp q hq z hs
  exact hfactor z _ _ (scalarValue_mem _ _ _ c tau hc p hp z)
    (scalarValue_mem _ _ _ c tau hc q hq z) hs

/-- The first-coordinate family depends only on the fixed literal anchor,
step vector, and anchor position, not on a realizing path. -/
theorem first_anchored_family (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh)
    (lambda : ℕ) (beta : FullLabel D (Fin n) A.Label) (hD : 0 < D) (hh : 0 < h)
    (t : Fin D → Fin h) (z0 : Fin h) (i : Fin D) :
    ∃ S : Finset (Fin h → Fin n),
      S.card ≤ 16 * (16004 * D * h + 1) ^ 6 ∧
      ∀ R : Realization D,
        EligibleRealization n hn A (1 / (1000 * (D : ℝ))) lambda t R →
        recordedWord n hn A (1 / (1000 * (D : ℝ))) R lambda t z0 = some beta →
        (fun z => UniformMesh.label n hn (firstPath R t z i)) ∈ S := by
  classical
  obtain ⟨S, hS, hcard⟩ := uniform_scalar_family n hn hD (beta.1 i)
    (anchorCoefficient z0) (fun z => anchorCoefficient z0 z * (t i).val)
    (fun z => (abs_anchorCoefficient_lt_one hh z0 z).le)
  refine ⟨S, hcard, ?_⟩
  intro R hR hanchor
  obtain ⟨_, hlabel⟩ := (recordedWord_eq_some_iff n hn A _ R lambda t z0 beta).mp hanchor
  have hlabeli : UniformMesh.label n hn (firstPath R t z0 i) = beta.1 i :=
    congrArg (fun label => label.1 i) hlabel
  have ha := (UniformMesh.label_mem_iff n hn (firstPath R t z0 i) (beta.1 i)).mp hlabeli
  let p : Fin 2 → ℝ := ![Int.fract (firstPath R t z0 i), R.u i]
  apply (hS _).mpr
  refine ⟨p, ⟨ha.1, ha.2.le, hR.first_drift i⟩, ?_⟩
  funext z
  exact (firstLabel_reanchor n hn R t z0 z i).symm

/-- Stationary coordinates use an untruncated mesh label; rotating coordinates
use the actual distance-to-cut truncation. Both have the same uniform bound. -/
theorem second_anchored_family (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh)
    (lambda : ℕ) (beta : FullLabel D (Fin n) A.Label) (hD : 0 < D) (hh : 0 < h)
    (t : Fin D → Fin h) (z0 : Fin h) (i : Fin D) :
    ∃ S : Finset (Fin h → Option A.Label),
      S.card ≤ 16 * (16004 * D * h + 1) ^ 6 ∧
      ∀ R : Realization D,
        EligibleRealization n hn A (1 / (1000 * (D : ℝ))) lambda t R →
        recordedWord n hn A (1 / (1000 * (D : ℝ))) R lambda t z0 = some beta →
        secondOutput A (1 / (1000 * (D : ℝ))) R lambda t i ∈ S := by
  classical
  by_cases hi : stationary lambda t i
  · choose m hm using (fun z => stationary_translation_integer lambda t hh i hi z0 z)
    obtain ⟨S, hS, hcard⟩ := stationary_scalar_family A hD (beta.2 i)
      (anchorCoefficient z0) m (fun z => (abs_anchorCoefficient_lt_one hh z0 z).le)
    refine ⟨S, hcard, ?_⟩
    intro R hR hanchor
    obtain ⟨hz0, hlabel⟩ :=
      (recordedWord_eq_some_iff n hn A _ R lambda t z0 beta).mp hanchor
    have hlabeli : A.meshLabel (secondPath R lambda t z0 i) = beta.2 i :=
      congrArg (fun label => label.2 i) hlabel
    have ha := (A.meshLabel_eq_iff (secondPath R lambda t z0 i) (beta.2 i)).mp hlabeli
    have hb : |R.v i| ≤ A.width (beta.2 i) := by
      rw [← hlabeli]
      exact hR.stationary_drift i hi z0 hz0
    let p : Fin 2 → ℝ := ![centered (secondPath R lambda t z0 i), R.v i]
    apply (hS _).mpr
    refine ⟨p, ⟨ha.1, ha.2.le, hb⟩, ?_⟩
    funext z
    have he : scalarValue (anchorCoefficient z0) (fun z => (m z : ℝ)) p z =
        anchoredSecond R lambda t z0 z i := by
      dsimp [scalarValue, p, anchoredSecond]
      rw [hm z]
    rw [he, secondOutput, ite_eq_left hi, secondLabel_reanchor A R lambda t z0 z i]
  · obtain ⟨S, hS, hcard⟩ := rotating_scalar_family A hD (beta.2 i)
      (anchorCoefficient z0)
      (fun z => anchorCoefficient z0 z * ((lambda : ℝ) * (t i).val))
      (fun z => (abs_anchorCoefficient_lt_one hh z0 z).le)
    refine ⟨S, hcard, ?_⟩
    intro R hR hanchor
    obtain ⟨_, hlabel⟩ :=
      (recordedWord_eq_some_iff n hn A _ R lambda t z0 beta).mp hanchor
    have hlabeli : A.meshLabel (secondPath R lambda t z0 i) = beta.2 i :=
      congrArg (fun label => label.2 i) hlabel
    have ha := (A.meshLabel_eq_iff (secondPath R lambda t z0 i) (beta.2 i)).mp hlabeli
    let p : Fin 2 → ℝ := ![centered (secondPath R lambda t z0 i), R.v i]
    apply (hS _).mpr
    refine ⟨p, ⟨ha.1, ha.2.le, hR.rotating_drift i hi⟩, ?_⟩
    funext z
    change A.truncatedLabel _ (anchoredSecond R lambda t z0 z i) =
      secondOutput A _ R lambda t i z
    simp only [secondOutput, ite_eq_right hi, AdaptiveMesh.truncatedLabel,
      rho_reanchor R lambda t z0 z i, secondLabel_reanchor A R lambda t z0 z i]

/-- The actual union incidence count. The literal eligibility predicate is
filtered before counting. Its pairwise distinctness and half-regular conditions
are retained in the family, although this bound only needs a regular anchor.
No family-cardinality, label-factorization, or independent-mask premise occurs
in this theorem. -/
theorem card_through_le (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (lambda : ℕ)
    (beta : FullLabel D (Fin n) A.Label) (hD : 0 < D) (hh : 0 < h) :
    (through (h := h) n hn A (1 / (1000 * (D : ℝ))) lambda beta).card ≤
      (16005 * D * h) ^ (14 * D) := by
  classical
  choose firstS hfirstcard hfirstmem using
    (fun t z0 i => first_anchored_family n hn A lambda beta hD hh t z0 i)
  choose secondS hsecondcard hsecondmem using
    (fun t z0 i => second_anchored_family n hn A lambda beta hD hh t z0 i)
  refine (Finset.card_le_card (t := anchoredIncidences firstS secondS) ?_).trans
    (card_anchoredIncidences_polynomial_le hD hh firstS secondS hfirstcard hsecondcard)
  intro p hp
  obtain ⟨⟨R, hR, hword⟩, z0, hz0⟩ :=
    (mem_through n hn A _ lambda beta p).mp hp
  have hanchor : recordedWord n hn A (1 / (1000 * (D : ℝ))) R lambda p.1 z0 =
      some beta := by rw [hword]; exact hz0
  have hmem := mem_anchoredIncidences_of_mem firstS secondS p.1 z0
    (fun i z => UniformMesh.label n hn (firstPath R p.1 z i))
    (secondOutput A (1 / (1000 * (D : ℝ))) R lambda p.1)
    (fun i => hfirstmem p.1 z0 i R hR hanchor)
    (fun i => hsecondmem p.1 z0 i R hR hanchor)
  have heq : assembleWord (fun i z => UniformMesh.label n hn (firstPath R p.1 z i))
      (secondOutput A (1 / (1000 * (D : ℝ))) R lambda p.1) = p.2 :=
    (recordedWord_eq_assembleWord n hn A _ R lambda p.1).symm.trans hword
  simpa only [heq, Prod.eta] using hmem

end QuantitativeVanDerWaerden.AnchoredPatterns

end

end OAI
