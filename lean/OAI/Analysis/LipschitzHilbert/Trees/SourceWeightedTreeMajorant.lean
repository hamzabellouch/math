import OAI.Analysis.LipschitzHilbert.Packets.SourceFrozenCellIntegral
import OAI.Analysis.LipschitzHilbert.Trees.SourcePlanarPolynomial

namespace OAI

/-! The actual polynomially weighted tree maximum is a bounded
measurable majorant. Its L2 energy is inherited from the stronger product
weight, without adding a maximal-function premise. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def transverseTreeMajorant (b : ℝ) (q : ℕ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (z : ℝ×ℝ) : ℝ :=
  polynomialWeight b (2*P.width) q z.2*P.physicalTreeMaximal 0 c z

theorem transverseTreeMajorant_nonneg (b : ℝ) (q : ℕ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (z : ℝ×ℝ) :
    0≤P.transverseTreeMajorant b q c z :=
  mul_nonneg ((polynomialWeight_one_le b (2*P.width) q z.2).trans' (by norm_num))
    (intervalOscillation_nonneg _ _ _ _)

theorem transverseTreeMajorant_continuous (b : ℝ) (q : ℕ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    Continuous (P.transverseTreeMajorant b q c) := by
  have hw : Continuous (fun z : ℝ×ℝ => polynomialWeight b (2*P.width) q z.2) := by
    unfold polynomialWeight
    fun_prop
  exact hw.mul (P.physicalTreeMaximal_continuous 0 c)

/-- Boundedness is obtained from the finitely many actual weighted
Schwartz partial sums; the bound is needed only for representatives. -/
theorem transverseTreeMajorant_bounded (b : ℝ) (q : ℕ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    ∃ B : ℝ, 0≤B ∧ ∀ z, ‖P.transverseTreeMajorant b q c z‖≤B := by
  let f := fun n : Fin (N+1) =>
    planarPolynomialLocalization b (2*P.width) q (P.physicalTreePartialSchwartz 0 c n)
  let v := fun n : Fin (N+1) => SchwartzMap.seminorm ℝ 0 0 (f n)
  let S := ∑ n, v n
  have hv (n : Fin (N+1)) : 0≤v n := apply_nonneg _ _
  have hS : 0≤S := Finset.sum_nonneg (fun n _ => hv n)
  have hb (n : ℕ) (hn : n≤N) (z : ℝ×ℝ) :
      polynomialWeight b (2*P.width) q z.2*‖P.physicalTreePartial 0 c n z‖≤S := by
    have hn' : n<N+1 := by omega
    have hs := Finset.single_le_sum (f:=v) (fun n _ => hv n)
      (Finset.mem_univ (⟨n,hn'⟩ : Fin (N+1)))
    have hnrm := SchwartzMap.norm_le_seminorm ℝ (f ⟨n,hn'⟩) z
    rw [planarPolynomialLocalization_norm,physicalTreePartialSchwartz_apply] at hnrm
    exact hnrm.trans hs
  refine ⟨2*S,by positivity,?_⟩
  intro z
  obtain ⟨lo,hi,_hlo,horder,hhi,hmax⟩ :=
    exists_intervalOscillation_eq (fun n => P.physicalTreePartial 0 c n z) N 0 N (Nat.zero_le _)
  have hlow := hb lo (horder.trans hhi) z
  have hhigh := hb hi hhi z
  rw [Real.norm_eq_abs,abs_of_nonneg (P.transverseTreeMajorant_nonneg b q c z)]
  change polynomialWeight b (2*P.width) q z.2*P.physicalTreeMaximal 0 c z≤2*S
  change P.physicalTreeMaximal 0 c z=_ at hmax
  rw [hmax]
  have hp : 0≤polynomialWeight b (2*P.width) q z.2 :=
    (polynomialWeight_one_le b (2*P.width) q z.2).trans' (by norm_num)
  calc
    _ ≤ polynomialWeight b (2*P.width) q z.2*
        (‖P.physicalTreePartial 0 c hi z‖+‖P.physicalTreePartial 0 c lo z‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) hp
    _ ≤ _ := by rw [mul_add]; linarith

/-- The stronger product-weight estimate supplies the exact L2
majorant needed by the compiled cell-energy theorem. -/
theorem transverseTreeMajorant_energy (a b r : ℝ) (q : ℕ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (E0 : ℝ)
    (hI : Integrable (fun z : ℝ×ℝ =>
      (polynomialWeight a (2*r) q z.1*polynomialWeight b (2*P.width) q z.2)^2*
        P.physicalTreeMaximal 0 c z^2) (volume.prod volume))
    (hE : (∫ z : ℝ×ℝ,
      (polynomialWeight a (2*r) q z.1*polynomialWeight b (2*P.width) q z.2)^2*
        P.physicalTreeMaximal 0 c z^2 ∂volume.prod volume)≤E0) :
    MemLp (P.transverseTreeMajorant b q c) 2 (volume.prod volume) ∧
      (∫ z, (P.transverseTreeMajorant b q c z)^2 ∂volume.prod volume)≤E0 := by
  have hc := (P.transverseTreeMajorant_continuous b q c).pow 2
  have hle (z : ℝ×ℝ) : (P.transverseTreeMajorant b q c z)^2≤
      (polynomialWeight a (2*r) q z.1*polynomialWeight b (2*P.width) q z.2)^2*
        P.physicalTreeMaximal 0 c z^2 := by
    have hx : 1≤(polynomialWeight a (2*r) q z.1)^2 :=
      one_le_pow₀ (polynomialWeight_one_le a (2*r) q z.1)
    simp only [transverseTreeMajorant,mul_pow]
    nlinarith [sq_nonneg (polynomialWeight b (2*P.width) q z.2*P.physicalTreeMaximal 0 c z)]
  have hi : Integrable (fun z => (P.transverseTreeMajorant b q c z)^2) (volume.prod volume) :=
    hI.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact hle z))
  exact ⟨(memLp_two_iff_integrable_sq
    (P.transverseTreeMajorant_continuous b q c).aestronglyMeasurable).mpr hi,
    (integral_mono hi hI hle).trans hE⟩

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
