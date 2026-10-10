import OAI.Probability.DilutedSpin.MatrixEnergy
import OAI.Probability.DilutedSpin.Polarization

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators Classical
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {L N : ℕ}

noncomputable def matrixObservableHistory (T : PrescribedTree L) (q : C → T.Leaf)
    (K : KernelTower Ω L) (m : Fin (L+1) → ℝ) (cs : List C) (S : PrescribedTree L)
    (x : S.Leaf) (A : (C → FinitePath Ω L) → ℝ) (f : Sample Ω S → ℝ) : ℝ :=
  weightedMatrixHistory T q
    (fun D pos g => (D.sampleLaw K).expect (fun z => g z*A (fun b => D.pathAt (pos b) z)))
    m cs S (Finset.univ.erase x) id (fun _ => x) f

noncomputable def matrixProjectionError (T : PrescribedTree L) (q : C → T.Leaf)
    (K : KernelTower Ω L) (a c : C) (A : (C → FinitePath Ω L) → ℝ)
    (X : FinitePath Ω L → Fin N → ℝ) : ℝ :=
  (T.sampleLaw K).l2 (fun z => A (fun b => T.pathAt (q b) z)-
    FiniteLaw.dot (X (T.pathAt (q a) z)) (X (T.pathAt (q c) z)))

noncomputable def oldProjectionError (S : PrescribedTree L) (K : KernelTower Ω L)
    (x y : S.Leaf) (f : Sample Ω S → ℝ) (X : FinitePath Ω L → Fin N → ℝ) : ℝ :=
  (S.sampleLaw K).l2 (fun z => FiniteLaw.dot (X (S.pathAt x z)) (X (S.pathAt y z))-f z)

noncomputable def shiftedCharge (Q : Finset ℕ) (T S : PrescribedTree L) (k : ℕ) : ℝ :=
  chargeBound (2*(leaves S+k:ℕ)) ((Q.card:ℝ)*(leaves S+k:ℕ)) k (branchingCount T (· ∈ Q)) *
    (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))

section Root
variable {Z : Type} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (T S : PrescribedTree L) (q : C → T.Leaf)
    (K : (z : Z) → KernelTower (Ω z) L) (m : Fin (L+1) → ℝ) (cs : List C)
    (x : S.Leaf) (A : (z : Z) → (C → FinitePath (Ω z) L) → ℝ)
    (f : (z : Z) → Sample (Ω z) S → ℝ)

noncomputable def matrixRootCovariance : ℝ :=
  (∫ z, matrixObservableHistory T q (K z) m cs S x (A z) (f z) ∂μ) -
  (∫ z, (S.sampleLaw (K z)).expect (f z) ∂μ) *
    (∫ z, matrixObservableHistory T q (K z) m cs S x (A z) (fun _ => 1) ∂μ)

end Root

/-- The full shifted-matrix/three-copy estimate after root averaging. The
only analytic errors are actual target and old single-copy L2 projection
errors. The prescribed-tree identity appears as ONE centered root covariance,
not any stronger conditional or absolute pointwise concentration claim. -/
theorem root_matrix_energy {Z : Type} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (hL : 0 < L) (Q : Finset ℕ) (T S : PrescribedTree L)
    (q : C → T.Leaf) (hq : Function.Bijective q) (hS : branchingCount S (· ∈ Q) = 0)
    (K : (z : Z) → KernelTower (Ω z) L)
    (a c : C) (hac : a ≠ c) (cs : List C) (hcs : cs.Nodup)
    (hdis : ∀ b ∈ cs, b ∉ insert c ({a} : Finset C))
    (hfull : insert c ({a} : Finset C) ∪ cs.toFinset = Finset.univ)
    (x y : S.Leaf) (v : S.Internal) (d : ℕ) (hd : d < L)
    (hqd : splitDepth T (q a) (q c) = d) (hxy : splitDepth S x y = d)
    (hxv : freshSplitDepth S v x = d) (hyv : freshSplitDepth S v y = d)
    (X : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ) (hX : ∀ z w i, |X z w i| ≤ 1)
    (hOld : ∀ z b, splitDepth S x b = d → ∀ w : Sample (Ω z) S,
      X z (S.pathAt b w) = X z (S.pathAt y w))
    (A : (z : Z) → (C → FinitePath (Ω z) L) → ℝ) (hA : ∀ z w, |A z w| ≤ 1)
    (f : (z : Z) → Sample (Ω z) S → ℝ) (hf : ∀ z w, |f z w| ≤ 1)
    (hE : Integrable (fun z => KernelTower.prefixEnergyAt L (K z) d (X z)) μ)
    (hH : Integrable (fun z => matrixObservableHistory T q (K z) (grid L 0 L) (c::cs) S x (A z) (f z)) μ)
    (hEt : Integrable (fun z => matrixProjectionError T q (K z) a c (A z) (X z)) μ)
    (hEo : Integrable (fun z => oldProjectionError S (K z) x y (f z) (X z)) μ)
    (hMean : Integrable (fun z => (T.sampleLaw (K z)).expect (fun w => A z (fun b => T.pathAt (q b) w))) μ) :
    let m := grid L 0 L
    let J := partialKappa T m (Finset.univ.image q) /
      partialKappa T m ((insert c ({a} : Finset C)).image q)
    (-gamma S m v)*(∫ z, KernelTower.prefixEnergyAt L (K z) d (X z) ∂μ) ≤
      2*(m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) +
        |matrixRootCovariance μ Ω T S q K m (c::cs) x A f|/|J| +
        (∫ z, matrixProjectionError T q (K z) a c (A z) (X z) ∂μ)*shiftedCharge Q T S (c::cs).length/|J| +
        pairHistoryMass S m x*(∫ z, oldProjectionError S (K z) x y (f z) (X z) ∂μ) := by
  dsimp only
  let m := grid L 0 L
  let J := partialKappa T m (Finset.univ.image q) /
    partialKappa T m ((insert c ({a} : Finset C)).image q)
  have hm := grid_strictMono hL
  have hp : ∀ j, 0 ≤ m j := grid_nonneg
  have hend : m (Fin.last L) = 1 := grid_last hL
  have hJ : J ≠ 0 := div_ne_zero (partialKappa_ne_zero T m hm hp _)
    (partialKappa_ne_zero T m hm hp _)
  apply root_matrix_error_bound μ
    (fun z => KernelTower.prefixEnergyAt L (K z) d (X z))
    (fun z => matrixObservableHistory T q (K z) m (c::cs) S x (A z) (f z))
    (fun z => matrixObservableHistory T q (K z) m (c::cs) S x (A z) (fun _ => 1))
    (fun z => (S.sampleLaw (K z)).expect (f z))
    (fun z => (T.sampleLaw (K z)).expect (fun w => A z (fun b => T.pathAt (q b) w)))
    (fun z => matrixProjectionError T q (K z) a c (A z) (X z))
    (fun z => oldProjectionError S (K z) x y (f z) (X z))
    J (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) (-gamma S m v)
    (shiftedCharge Q T S (c::cs).length) (pairHistoryMass S m x) hJ
    (sub_nonneg.mpr (hm.monotone (by simp)))
    (fun z => (S.sampleLaw (K z)).abs_expect_le (hf z))
    (fun z => (T.sampleLaw (K z)).abs_expect_le (fun w => hA z _))
    ?_ hE hH hMean hEt hEo ?_
  · intro z
    have he := matrixHistory_one_div T q hq (K z) m hm hp hend a c hac cs hcs hdis hfull S x (A z) d hd hqd
    simpa only [matrixObservableHistory, J, neg_sub] using he
  · intro z
    exact matrix_energy_pointwise hL Q T S q hq hS (K z) a c hac cs hcs hdis hfull
      x y v d hd hqd hxy hxv hyv (X z) (hX z) (hOld z) (A z) (f z) (hf z)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
