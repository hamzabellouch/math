import Mathlib
import OAI.Analysis.AffineBernstein.ParametricGraphJets

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma contDiffAt_inverse_matrix_entry_param {P ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype ι] [DecidableEq ι]
    {A : P → Matrix ι ι ℝ} {p : P}
    (hA : ContDiffAt ℝ ∞ (fun q i j => A q i j) p) (hd : (A p).det ≠ 0) (i j : ι) :
    ContDiffAt ℝ ∞ (fun q => (A q)⁻¹ i j) p := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  exact (((continuousDetRows (ι := ι)).contDiff.contDiffAt.comp p hA).inv hd).mul
    ((contDiff_adjugate_entry i j).contDiffAt.comp p hA)

def graphVariationJacobian {n : ℕ} (a : Fin n → Space n → ℝ) (p : ℝ × Space n) :
    Matrix (Fin n) (Fin n) ℝ := 1 + p.1 • horizontalJacobian a p.2

def graphVariationSecond {n : ℕ} (u β : Space n → ℝ) (a : Fin n → Space n → ℝ)
    (p : ℝ × Space n) : Matrix (Fin n) (Fin n) ℝ :=
  variationSecondForm (hessian u p.2) (hessian β p.2) (horizontalJacobian a p.2)
    (fun i => dirDeriv (coordinateVector n i) u p.2)
    (fun i => dirDeriv (coordinateVector n i) β p.2) (fun k => hessian (a k) p.2) p.1

lemma contDiffAt_graphVariationJacobian {n : ℕ} {a : Fin n → Space n → ℝ}
    {p : ℝ × Space n} (ha : ∀ k, ContDiffAt ℝ ∞ (a k) p.2) :
    ContDiffAt ℝ ∞ (fun q i j => graphVariationJacobian a q i j) p := by
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro j
  simp only [graphVariationJacobian, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    horizontalJacobian]
  exact contDiffAt_const.add (contDiffAt_fst.mul
    ((contDiffAt_dirDeriv (ha i) _).comp p contDiffAt_snd))

lemma contDiffAt_graphVariationSecond {n : ℕ} {u β : Space n → ℝ}
    {a : Fin n → Space n → ℝ} {p : ℝ × Space n}
    (hu : ContDiffAt ℝ ∞ u p.2) (hβ : ContDiffAt ℝ ∞ β p.2)
    (ha : ∀ k, ContDiffAt ℝ ∞ (a k) p.2)
    (hJ : (graphVariationJacobian a p).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun q i j => graphVariationSecond u β a q i j) p := by
  have hC (k : Fin n) : ContDiffAt ℝ ∞ (fun q : ℝ × Space n =>
      variationConormal (horizontalJacobian a q.2)
        (fun l => dirDeriv (coordinateVector n l) u q.2)
        (fun l => dirDeriv (coordinateVector n l) β q.2) q.1 k) p := by
    apply ContDiffAt.sum
    intro l _
    apply ContDiffAt.mul
    · exact ((contDiffAt_dirDeriv hu _).comp p contDiffAt_snd).add
        (contDiffAt_fst.mul ((contDiffAt_dirDeriv hβ _).comp p contDiffAt_snd))
    · exact contDiffAt_inverse_matrix_entry_param (contDiffAt_graphVariationJacobian ha) hJ l k
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro j
  simp only [graphVariationSecond, variationSecondForm, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  apply ContDiffAt.sub
    (((contDiffAt_hessian_entry hu i j).comp p contDiffAt_snd).add
      (contDiffAt_fst.mul ((contDiffAt_hessian_entry hβ i j).comp p contDiffAt_snd)))
  apply ContDiffAt.mul contDiffAt_fst
  apply ContDiffAt.sum
  intro k _
  exact (hC k).mul ((contDiffAt_hessian_entry (ha k) i j).comp p contDiffAt_snd)

def graphVariationRegular {n : ℕ} (Ω : Set (Space n)) (u β : Space n → ℝ)
    (a : Fin n → Space n → ℝ) : Set (ℝ × Space n) :=
  {p | p.2 ∈ Ω ∧ (graphVariationJacobian a p).det ≠ 0 ∧ (graphVariationSecond u β a p).det ≠ 0}

lemma isOpen_graphVariationRegular {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u β : Space n → ℝ} {a : Fin n → Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hβ : ContDiffOn ℝ ∞ β Ω)
    (ha : ∀ k, ContDiffOn ℝ ∞ (a k) Ω) :
    IsOpen (graphVariationRegular Ω u β a) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hJ := (continuousDetRows (ι := Fin n)).contDiff.contDiffAt.comp p
    (contDiffAt_graphVariationJacobian (fun k => (ha k).contDiffAt (hΩ.mem_nhds hp.1)))
  have hH := (continuousDetRows (ι := Fin n)).contDiff.contDiffAt.comp p
    (contDiffAt_graphVariationSecond (hu.contDiffAt (hΩ.mem_nhds hp.1))
      (hβ.contDiffAt (hΩ.mem_nhds hp.1))
      (fun k => (ha k).contDiffAt (hΩ.mem_nhds hp.1)) hp.2.1)
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (hΩ.mem_nhds hp.1),
    hJ.continuousAt.eventually_ne hp.2.1, hH.continuousAt.eventually_ne hp.2.2] with q hq hj hh
  exact ⟨hq,hj,hh⟩

lemma contDiffOn_graphVariationArea {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u β : Space n → ℝ} {a : Fin n → Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hβ : ContDiffOn ℝ ∞ β Ω)
    (ha : ∀ k, ContDiffOn ℝ ∞ (a k) Ω) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Space n => graphVariationArea u β a p.2 p.1)
      (graphVariationRegular Ω u β a) := by
  intro p hp
  have hJ := (continuousDetRows (ι := Fin n)).contDiff.contDiffAt.comp p
    (contDiffAt_graphVariationJacobian (fun k => (ha k).contDiffAt (hΩ.mem_nhds hp.1)))
  have hH := (continuousDetRows (ι := Fin n)).contDiff.contDiffAt.comp p
    (contDiffAt_graphVariationSecond (hu.contDiffAt (hΩ.mem_nhds hp.1))
      (hβ.contDiffAt (hΩ.mem_nhds hp.1))
      (fun k => (ha k).contDiffAt (hΩ.mem_nhds hp.1)) hp.2.1)
  exact ((hH.rpow_const_of_ne hp.2.2).mul
    ((hJ.abs hp.2.1).rpow_const_of_ne (abs_ne_zero.mpr hp.2.1))).contDiffWithinAt

lemma zero_mem_graphVariationRegular {n : ℕ} {Ω : Set (Space n)}
    {u β : Space n → ℝ} {a : Fin n → Space n → ℝ} {x : Space n}
    (hx : x ∈ Ω) (hp : (hessian u x).PosDef) : (0,x) ∈ graphVariationRegular Ω u β a := by
  refine ⟨hx, ?_, ?_⟩
  · simp [graphVariationJacobian]
  · simpa [graphVariationSecond] using ne_of_gt hp.det_pos

end AffineBernstein
end

end OAI
