import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourcePolyDivTendsto
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.IntegerResiduesAdd

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open Finset Classical Filter OrdinaryCorrelations.FiniteIntegration

def affineResidueEquiv (S : PrimeSystem) (q : ℕ)
    (hq : ∀ p : S.Index, Nat.Coprime q (p:ℕ)) (z : ℤ) : S.Residues ≃ S.Residues :=
  Equiv.piCongrRight (fun p =>
    (Units.mulLeft (ZMod.unitOfCoprime q (hq p))).trans (Equiv.addRight (z : ZMod (p:ℕ))))

lemma affineResidueEquiv_apply (S : PrimeSystem) (q : ℕ)
    (hq : ∀ p : S.Index, Nat.Coprime q (p:ℕ)) (z : ℤ) (x : S.Residues) (p : S.Index) :
    S.affineResidueEquiv q hq z x p = (q : ZMod (p:ℕ))*x p + z := rfl

lemma affineResidueEquiv_integer (S : PrimeSystem) (q : ℕ)
    (hq : ∀ p : S.Index, Nat.Coprime q (p:ℕ)) (z n : ℤ) :
    S.affineResidueEquiv q hq z (S.integerResidues n) = S.integerResidues (q*n+z) := by
  funext p
  simp only [affineResidueEquiv_apply,integerResidues,Int.cast_add,Int.cast_mul,Int.cast_natCast]

theorem real_affine_origin_discrepancy (S : PrimeSystem) (F : S.Residues → ℝ)
    (q : ℕ) (hq : ∀ p : S.Index, Nat.Coprime q (p:ℕ)) (z : ℤ)
    (X : ℝ) (hX : 0 < X) :
    |(∑ n ∈ range ⌊X⌋₊, F (S.integerResidues (q*(n:ℤ)+z)))/X - avg F| ≤
      (2*∑ x, |F x| + |avg F|)/X := by
  let e := S.affineResidueEquiv q hq z
  have hm : avg (fun x => F (e x)) = avg F := by
    unfold avg
    rw [e.sum_comp F]
  have hs : (∑ x, |F (e x)|) = ∑ x, |F x| := e.sum_comp (fun x => |F x|)
  have hh := S.real_origin_discrepancy (fun x => F (e x)) 0 X hX
  rw [hm,hs] at hh
  simpa only [add_zero,e,affineResidueEquiv_integer] using hh

theorem real_affine_origin_tendsto (S : PrimeSystem) (F : S.Residues → ℝ)
    (q : ℕ) (hq : ∀ p : S.Index, Nat.Coprime q (p:ℕ)) (z : ℝ → ℤ) :
    Tendsto (fun X : ℝ => (∑ n ∈ range ⌊X⌋₊,
      F (S.integerResidues (q*(n:ℤ)+z X)))/X) atTop (𝓝 (avg F)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
    simpa only [Real.norm_eq_abs] using S.real_affine_origin_discrepancy F q hq (z X) X hX
  · exact tendsto_const_nhds.div_atTop tendsto_id

lemma source_eventually_coprime (q : ℕ) (hq : 0 < q) :
    ∀ᶠ B : ℝ in atTop, ∀ p : (sourceSystem B).Index, Nat.Coprime q (p:ℕ) := by
  filter_upwards [source_eventually_large q] with B hB
  intro p
  apply Nat.Coprime.symm
  apply (Nat.Prime.coprime_iff_not_dvd ((sourceSystem B).prime_mem p.val p.property)).mpr
  intro hd
  exact (not_le_of_gt (hB.2 p).2) (Nat.le_of_dvd hq hd)

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
