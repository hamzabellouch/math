import Mathlib
import OAI.Analysis.CoulombRadii.Localization.AtomicHistory
import OAI.Analysis.CoulombRadii.Screening.ScreenUnits
import OAI.Analysis.CoulombRadii.RandomFields.RawCap

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def AtomicScaleWindow (a q : ℝ) (y : Space) : Prop :=
  a ≤ q*atomicCellScale y ∧ atomicCellScale y ≤ q*a

lemma AtomicScaleWindow.nonzero {a q : ℝ} {y : Space} (h : AtomicScaleWindow a q y)
    (ha : 0<a) : y≠0 := by
  intro hy
  subst y
  have hz : atomicCellScale (0:Space)=0 := by norm_num [atomicCellScale]
  dsimp [AtomicScaleWindow] at h
  rw [hz,mul_zero] at h
  linarith [h.1]

lemma AtomicScaleWindow.div_lower {a q : ℝ} {y : Space} (h : AtomicScaleWindow a q y)
    (hq : 0<q) : a/q ≤ atomicCellScale y := by
  rw [div_le_iff₀ hq]
  simpa only [mul_comm] using h.1

lemma AtomicScaleWindow.enlarge {a q r : ℝ} {y : Space} (h : AtomicScaleWindow a q y)
    (ha : 0 ≤ a) (hqr : q ≤ r) : AtomicScaleWindow a r y :=
  ⟨h.1.trans (mul_le_mul_of_nonneg_right hqr (atomicCellScale_nonneg _)),
    h.2.trans (mul_le_mul_of_nonneg_right hqr ha)⟩

lemma AtomicScaleWindow.near {a q : ℝ} {y z : Space} (h : AtomicScaleWindow a q y)
    (hq : 0 ≤ q) (hnear : ‖z-y‖ ≤ 82*atomicCellScale y) : AtomicScaleWindow a (2*q) z := by
  have H := atomicCellScale_comparable hnear
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left H.1 hq,h.1]
  · nlinarith [h.2]

lemma AtomicScaleWindow.mesh {a q : ℝ} {y z : Space} (h : AtomicScaleWindow a q y)
    (hq : 0 ≤ q) (hz : z∈atomicPatchMesh) : AtomicScaleWindow a (2*q) (atomicMeshCenter y z) :=
  h.near hq (by nlinarith [atomicMeshCenter_distance y z hz,atomicCellScale_nonneg y])

lemma AtomicScaleWindow.mesh_near {a q : ℝ} {y z v : Space} (h : AtomicScaleWindow a q y)
    (hq : 0 ≤ q) (hz : z∈atomicPatchMesh)
    (hv : ‖v-atomicMeshCenter y z‖ ≤ 2*atomicCellScale (atomicMeshCenter y z)) :
    AtomicScaleWindow a (4*q) v := by
  have H := (h.mesh hq hz).near (by positivity)
    (show ‖v-atomicMeshCenter y z‖ ≤ 82*atomicCellScale (atomicMeshCenter y z) by
      nlinarith [atomicCellScale_nonneg (atomicMeshCenter y z)])
  convert H using 1; ring

lemma AtomicScaleWindow.mass {a q δ : ℝ} {y : Space} (h : AtomicScaleWindow a q y)
    (ha : 0<a) (hq : 1 ≤ q) (hδ : 0 ≤ δ) :
    screenMass δ (atomicCellScale y) ≤ q^3*screenMass δ a :=
  screenMass_comparable hδ ha hq (h.div_lower (by linarith)) (by simpa only [mul_comm] using h.2)

lemma AtomicScaleWindow.energy {a q δ : ℝ} {y : Space} (h : AtomicScaleWindow a q y)
    (ha : 0<a) (hq : 1 ≤ q) (hδ : 0 ≤ δ) :
    screenEnergy δ (atomicCellScale y) ≤ q^7*screenEnergy δ a :=
  screenEnergy_comparable hδ ha hq (h.div_lower (by linarith)) (by simpa only [mul_comm] using h.2)

def atomicRawValues {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n) (a w : ℝ) (j : ℕ) : Set ℝ :=
  insert 0 {r | ∃ k ≤ j, ∃ T : AtomicCutHistory S ψ k,
    (∀ i, AtomicScaleWindow a (4^j) (T.target i)) ∧
    ∃ y, AtomicScaleWindow a (4^j) y ∧ r=Real.sqrt (T.ensemble.rawSquare S y (atomicCellScale y))/w}

def atomicRawSup {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n) (a w : ℝ) (j : ℕ) : ℝ :=
  sSup (atomicRawValues S ψ a w j)

lemma atomicRawValues_nonempty {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n) (a w : ℝ) (j : ℕ) :
    (atomicRawValues S ψ a w j).Nonempty := ⟨0,Set.mem_insert _ _⟩

lemma totalCharge_nonneg {J : ℕ} (S : Nuclei J) : 0 ≤ totalCharge S :=
  Finset.sum_nonneg (fun i _ => le_trans (by norm_num) (S.charge_ge_one i))

lemma atomicRawValues_cap {J n : ℕ} (S : Nuclei J) (hatom : ∀ i, S.position i=0)
    (ψ : H1Vector n) (hm : mass ψ=1) {a w : ℝ} (ha : 0<a) (hw : 0<w) (j : ℕ) :
    ∀ r ∈ atomicRawValues S ψ a w j, r ≤ (totalCharge S/(100000*a*w))*4^j := by
  intro r hr
  rcases hr with (rfl|⟨k,hk,T,hT,y,hy,rfl⟩)
  · exact mul_nonneg (div_nonneg (totalCharge_nonneg S) (by positivity)) (by positivity)
  · have hy0 := hy.nonzero ha
    have hay := atomicCellScale_pos hy0
    have hcap := T.ensemble.rawSquare_atomic_cap S hatom (T.mass_eq.trans hm) hy0
    have hb : Real.sqrt (T.ensemble.rawSquare S y (atomicCellScale y)) ≤
        totalCharge S/(100000*atomicCellScale y) := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨div_nonneg (totalCharge_nonneg S) (by positivity),hcap⟩
    apply (div_le_iff₀ hw).mpr
    calc
      _ ≤ totalCharge S/(100000*atomicCellScale y) := hb
      _ ≤ totalCharge S/(100000*(a/4^j)) := div_le_div_of_nonneg_left (totalCharge_nonneg S)
        (by positivity) (mul_le_mul_of_nonneg_left (hy.div_lower (by positivity)) (by norm_num))
      _ = _ := by field_simp

lemma atomicRawValues_bdd {J n : ℕ} (S : Nuclei J) (hatom : ∀ i, S.position i=0)
    (ψ : H1Vector n) (hm : mass ψ=1) {a w : ℝ} (ha : 0<a) (hw : 0<w) (j : ℕ) :
    BddAbove (atomicRawValues S ψ a w j) := ⟨_,atomicRawValues_cap S hatom ψ hm ha hw j⟩

lemma atomicRawSup_nonneg {J n : ℕ} (S : Nuclei J) (hatom : ∀ i, S.position i=0)
    (ψ : H1Vector n) (hm : mass ψ=1) {a w : ℝ} (ha : 0<a) (hw : 0<w) (j : ℕ) :
    0 ≤ atomicRawSup S ψ a w j :=
  le_csSup (atomicRawValues_bdd S hatom ψ hm ha hw j) (Set.mem_insert 0 _)

lemma atomicRawSup_cap {J n : ℕ} (S : Nuclei J) (hatom : ∀ i, S.position i=0)
    (ψ : H1Vector n) (hm : mass ψ=1) {a w : ℝ} (ha : 0<a) (hw : 0<w) (j : ℕ) :
    atomicRawSup S ψ a w j ≤ (totalCharge S/(100000*a*w))*4^j :=
  csSup_le (atomicRawValues_nonempty S ψ a w j) (atomicRawValues_cap S hatom ψ hm ha hw j)

end Coulomb
end

end
end

end OAI
