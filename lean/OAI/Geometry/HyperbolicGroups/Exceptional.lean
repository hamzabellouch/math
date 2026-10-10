import Mathlib
import OAI.Geometry.HyperbolicGroups.GraphLimit

namespace OAI

section
section


noncomputable section
open Filter Topology
namespace HyperbolicObstruction
namespace CoreGeometry.MetricCore
variable {Y : Type*} [MetricSpace Y] {z : CoreGeometry.Vertex → Y}
  (D : CoreGeometry.MetricCore z) (h : CATZero Y)
include D

lemma exceptional_radius :
    dist (z (.inr 4)) (CATZero.mid h (z (.inl 2)) (z (.inl 9))) ^ 2 = 1 / 2 := by
  have hm := CATZero.square_mid h
    (D.side (.inl 2) (.inr 4) (by decide))
    (D.side (.inr 4) (.inl 9) (by decide))
    (D.side (.inl 9) (.inr 1) (by decide))
    (D.side (.inr 1) (.inl 2) (by decide))
    (D.twoStep (.inl 2) (.inr 4) (.inl 9) (by decide) (by decide) (by decide))
    (D.twoStep (.inr 4) (.inl 2) (.inr 1) (by decide) (by decide) (by decide))
  rw [hm, CATZero.mid, CATZero.segment_left h _ _ (by norm_num)]
  have hd := D.twoStep (.inr 4) (.inl 2) (.inr 1) (by decide) (by decide) (by decide)
  nlinarith
end CoreGeometry.MetricCore

namespace MasterGraph
open IncidenceTemplate OrbitLimit

def excC : Edge := ⟨(2,4), by decide⟩
def excY : Edge := ⟨(9,4), by decide⟩
def excD : Edge := ⟨(3,4), by decide⟩
def excI : Finset Field := { .inl excC, .inl excY }

lemma exc_not : (.inl excD : Field) ∉ excI := by decide
lemma exc_admissible : Admissible (insert (.inl excD) excI) := by
  left
  constructor
  · decide
  · unfold CoreAdmissible
    decide

universe u v w
variable {L Ω : ℕ → Type u} [∀ n, Fintype (L n)]
  {label : ∀ n, Ω n → Field → L n}
  {X : ℕ → Type v} [∀ n, MetricSpace (X n)] {M : ℝ}
  (O : ∀ n, EnergyOrbit (L n) (X n) M)
  {G : ℕ → Type w} [∀ n, Group (G n)]
  (A : ∀ n, G n →* (X n ≃ᵢ X n)) (letter : ∀ n, L n → G n)
  (hact : ∀ n i, A n (letter n i) = (O n).isom i)
  (g : ∀ n m, Potential (label n m) (letter n)) (hM : 0 ≤ M)
  (inv : ∀ n, L n ≃ L n) (hinv : ∀ n i, letter n (inv n i) = (letter n i)⁻¹)

include hinv in
lemma array_inverse (e : Edge) (n : ℕ) (m : Ω n) :
    (array O A letter hact g hM (.inl (.inl e.val.1))).val n m =
      A n ((g n m).val (.inl (.inr e.val.2)))
        ((O n).isom (inv n (label n m (.inl e))) (O n).base) := by
  have he := (g n m).step (Step.neg (.inl e))
  simp only [source, target, Step.value, Step.neg, Bool.false_eq_true, ↓reduceIte] at he
  change A n ((g n m).val (.inl (.inl e.val.1))) (O n).base = _
  rw [he, map_mul, IsometryEquiv.mul_apply, ← hinv, hact]

def excTest (n : ℕ) (m : Ω n) : X n :=
  CATZero.mid (O n).cat
    ((O n).isom (inv n (label n m (.inl excC))) (O n).base)
    ((O n).isom (inv n (label n m (.inl excY))) (O n).base)

lemma excTest_depends (n : ℕ) (a b : Ω n)
    (hab : ∀ i ∈ excI, label n a i = label n b i) :
    excTest (label := label) O inv n a = excTest (label := label) O inv n b := by
  have hc := hab (.inl excC) (by simp [excI])
  have hy := hab (.inl excY) (by simp [excI])
  simp only [excTest, hc, hy]

lemma excTest_bound (n : ℕ) (m : Ω n) : dist (O n).base (excTest (label := label) O inv n m) ≤ 2 * M := by
  let x := (O n).isom (inv n (label n m (.inl excC))) (O n).base
  let y := (O n).isom (inv n (label n m (.inl excY))) (O n).base
  have hx : dist (O n).base x ≤ M := (O n).bound _
  have hy : dist (O n).base y ≤ M := (O n).bound _
  have hxy : dist x y ≤ 2 * M := by
    have ht := dist_triangle x (O n).base y
    rw [dist_comm x (O n).base] at ht
    linarith
  have ht := dist_triangle (O n).base x (excTest (label := label) O inv n m)
  change dist (O n).base (excTest (label := label) O inv n m) ≤ _
  change dist (O n).base (excTest (label := label) O inv n m) ≤ dist (O n).base x +
    dist x (CATZero.segment (O n).cat x y (1/2)) at ht
  rw [CATZero.segment_left _ _ _ (by norm_num)] at ht
  linarith

variable [∀ index, Nonempty (L index)] [∀ index, DecidableEq (L index)]
  [∀ index, Fintype (Ω index)] [∀ index, Nonempty (Ω index)]
  (S : SamplingSequence Field Admissible L Ω label)
  {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ atTop)

include hinv S hU in
/-- The source's decisive test is applied to the two actual C fields and
loose D field; its test depends only on the indicated two labels. -/
theorem exceptionalTest : CoreGeometry.ExceptionalTest (OrbitLimit.catZero O U)
    (fun v => limit (U := U) O A letter hact g hM (.inl v)) := by
  let p := array O A letter hact g hM (.inl (.inl 2))
  let q := array O A letter hact g hM (.inl (.inl 9))
  let o := array O A letter hact g hM (.inl (.inr 4))
  let z := array O A letter hact g hM (.inl (.inl 3))
  let J := OrbitLimit.segment p q (1/2)
  let frame (n : ℕ) (m : Ω n) := A n ((g n m).val (.inl (.inr 4)))
  have hhalf : (1/2 : ℝ) ∈ Set.Icc 0 1 := by norm_num
  have hp (n : ℕ) (m : Ω n) : p.val n m =
      frame n m ((O n).isom (inv n (label n m (.inl excC))) (O n).base) :=
    array_inverse O A letter hact g hM inv hinv excC n m
  have hq (n : ℕ) (m : Ω n) : q.val n m =
      frame n m ((O n).isom (inv n (label n m (.inl excY))) (O n).base) :=
    array_inverse O A letter hact g hM inv hinv excY n m
  have hJ (n : ℕ) (m : Ω n) : J.val n m = frame n m (excTest (label := label) O inv n m) := by
    rw [OrbitLimit.segment_val p q hhalf, hp, hq]
    exact (CATZero.isometry_segment (O n).cat (frame n m) _ _ hhalf).symm
  have hz (n : ℕ) (m : Ω n) : z.val n m =
      frame n m ((O n).isom (inv n (label n m (.inl excD))) (O n).base) :=
    array_inverse O A letter hact g hM inv hinv excD n m
  have hJlim : point O U J = CATZero.mid (OrbitLimit.catZero O U) (point O U p) (point O U q) :=
    OrbitLimit.point_segment p q hhalf
  have D := metricCore O A letter hact g hM S hU inv hinv
  have hrad : dist (point O U o) (point O U J) ^ 2 = 1 / 2 := by
    rw [hJlim]
    exact D.exceptional_radius (OrbitLimit.catZero O U)
  have hside : dist (point O U o) (point O U z) ^ 2 = 1 :=
    D.side (.inr 4) (.inl 3) (by decide)
  intro t ht
  have he := S.limit_fractional O hU exc_not exc_admissible inv (excTest (label := label) O inv)
    (excTest_depends O inv) hM (show 0 ≤ 2 * M by positivity) (excTest_bound O inv) frame
    o J z (fun _ _ => rfl) hJ hz (a := t) (b := t) ⟨ht.1.le,ht.2⟩ ⟨ht.1.le,ht.2⟩
  rw [hrad, hside, hJlim] at he
  convert he using 1
  ring

include O A letter hact g hM hinv S hU in
/-- No sequence of consistent literal-master-pattern actions with the
sampling conclusions can exist. -/
theorem impossible_sequence : False :=
  (metricCore O A letter hact g hM S hU inv hinv).impossible (OrbitLimit.catZero O U)
    (exceptionalTest O A letter hact g hM inv hinv S hU)

end MasterGraph
end HyperbolicObstruction
end
end

section

end
end

end OAI
