import OAI.Probability.DilutedSpin.HeterogeneousProjection
import OAI.Probability.DilutedSpin.MatrixTriple

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators Classical
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {L N : ℕ}

/-- The full shifted-matrix/three-copy estimate after root averaging. The
only analytic errors are actual target and old single-copy L2 projection
errors. The prescribed-tree identity appears as ONE centered root covariance,
not any stronger conditional or absolute pointwise concentration claim. -/
theorem root_matrix_three_copy {Z : Type} [MeasurableSpace Z] (μ : Measure Z)
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
    (hE : Integrable (fun z => KernelTower.halfTripleDifferenceAt L (K z) d (X z)) μ)
    (hH : Integrable (fun z => matrixObservableHistory T q (K z) (grid L 0 L) (c::cs) S x (A z) (f z)) μ)
    (hEt : Integrable (fun z => matrixProjectionError T q (K z) a c (A z) (X z)) μ)
    (hEo : Integrable (fun z => oldProjectionError S (K z) x y (f z) (X z)) μ)
    (hMean : Integrable (fun z => (T.sampleLaw (K z)).expect (fun w => A z (fun b => T.pathAt (q b) w))) μ) :
    let m := grid L 0 L
    let J := partialKappa T m (Finset.univ.image q) /
      partialKappa T m ((insert c ({a} : Finset C)).image q)
    (-gamma S m v)*(∫ z, KernelTower.halfTripleDifferenceAt L (K z) d (X z) ∂μ) ≤
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
    (fun z => KernelTower.halfTripleDifferenceAt L (K z) d (X z))
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
    exact matrix_three_copy_pointwise hL Q T S q hq hS (K z) a c hac cs hcs hdis hfull
      x y v d hd hqd hxy hxv hyv (X z) (hX z) (hOld z) (A z) (f z) (hf z)

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators Classical
variable {L : ℕ}

lemma partialKappa_grid_pair (hL : 0 < L) (T : PrescribedTree L)
    (a b : T.Leaf) (hab : a ≠ b) :
    partialKappa T (grid L 0 L) {b,a} = -(L:ℝ)⁻¹ := by
  rw [partialKappa_pair T _ (grid_strictMono hL) grid_nonneg (grid_last hL) a b hab]
  simp [grid,Nat.cast_add,add_div]

/-- The separation vertex is the protected pair factor, leaving exactly the
powers charged at the shifted internal branching vertices. -/
theorem protectedKappa_grid_lower (hL : 0 < L) (T : PrescribedTree L)
    (a b : T.Leaf) (hab : a ≠ b) (η : ℝ) (hη : 0 ≤ η)
    (hr : BranchRegular T (grid L 0 L) η) (k : ℕ)
    (hk : branchingCount T (fun _ => True) = k+1) :
    (L:ℝ)⁻¹^k*η^(branchExcess T) ≤
      |partialKappa T (grid L 0 L) Finset.univ / partialKappa T (grid L 0 L) {b,a}| := by
  have hδ : 0 < (L:ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hL)
  rw [abs_div,partialKappa_grid_pair hL T a b hab,abs_neg,abs_of_pos hδ]
  apply (le_div_iff₀ (inv_pos.mpr (Nat.cast_pos.mpr hL))).mpr
  have h := partialKappa_grid_lower T 0 L η hη hr
  rw [hk,pow_succ] at h
  nlinarith [h]

/-- The manuscript's relative absolute-cost bound. Its dimensional power of
L cancels EXACTLY, including distinct target vertices sharing a depth. -/
theorem shiftedCharge_relative_bound (hL : 0 < L) (Q : Finset ℕ)
    (T S : PrescribedTree L) (k : ℕ) (a b : T.Leaf) (hab : a ≠ b)
    (η : ℝ) (hη : 0 < η) (hr : BranchRegular T (grid L 0 L) η)
    (hb : branchingCount T (fun _ => True) = branchingCount T (· ∈ Q)+1) :
    shiftedCharge Q T S k /
        |partialKappa T (grid L 0 L) Finset.univ / partialKappa T (grid L 0 L) {b,a}| ≤
      chargeBound (2*(leaves S+k:ℕ)) ((Q.card:ℝ)*(leaves S+k:ℕ)) k
        (branchingCount T (· ∈ Q)) / η^(branchExcess T) := by
  let J := |partialKappa T (grid L 0 L) Finset.univ / partialKappa T (grid L 0 L) {b,a}|
  let A := chargeBound (2*(leaves S+k:ℕ)) ((Q.card:ℝ)*(leaves S+k:ℕ)) k
    (branchingCount T (· ∈ Q))
  let D := (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))
  let E := η^(branchExcess T)
  have hD : 0 < D := pow_pos (inv_pos.mpr (Nat.cast_pos.mpr hL)) _
  have hE : 0 < E := pow_pos hη _
  have hA : 0 ≤ A := chargeBound_nonneg (by positivity) (by positivity) _ _
  have hlo : D*E ≤ J := protectedKappa_grid_lower hL T a b hab η hη.le hr _ hb
  have hJ : 0 < J := (mul_pos hD hE).trans_le hlo
  change A*D/J ≤ A/E
  apply (div_le_div_iff₀ hJ hE).mpr
  have hh := mul_le_mul_of_nonneg_left hlo hA
  nlinarith [hh]

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω] {N : ℕ}

noncomputable def pairProjectionSq (P : FiniteLaw Ω) (X Y : Ω → Fin N → ℝ) : ℝ :=
  P.expect (fun x => P.expect (fun y => (dot (X x) (X y)-dot (Y x) (Y y))^2))

/-- Exact three-copy transfer for a coupled true vector and projected vector.
This prevents the invalid inference from only projected covariance energy. -/
theorem covariance_projection_transfer (P : FiniteLaw Ω) (X Y : Ω → Fin N → ℝ) :
    P.covarianceEnergy X ≤
      P.expect (fun x => P.expect (fun y => P.expect (fun z =>
        (dot (Y x) (Y y)-dot (Y x) (Y z))^2)))+4*pairProjectionSq P X Y := by
  have hthree := P.three_copy_bound X
  have hthree' : 2*P.covarianceEnergy X ≤
      P.expect (fun x => P.expect (fun y => P.expect (fun z =>
        (dot (X x) (X y)-dot (X x) (X z))^2))) := by
    convert hthree using 1
    unfold covarianceEnergy
    ring
  have hp (x y z : Ω) :
      (dot (X x) (X y)-dot (X x) (X z))^2 ≤
        2*(dot (Y x) (Y y)-dot (Y x) (Y z))^2+
        4*(dot (X x) (X y)-dot (Y x) (Y y))^2+
        4*(dot (X x) (X z)-dot (Y x) (Y z))^2 := by
    nlinarith [sq_nonneg ((dot (X x) (X y)-dot (Y x) (Y y))+
        (dot (X x) (X z)-dot (Y x) (Y z))),
      sq_nonneg ((dot (X x) (X y)-dot (X x) (X z))-
        2*(dot (Y x) (Y y)-dot (Y x) (Y z)))]
  have h := P.expect_mono (fun x => P.expect_mono (fun y => P.expect_mono (fun z => hp x y z)))
  simp only [expect_add,expect_mul_left,expect_const] at h
  unfold pairProjectionSq
  linarith

lemma pairProjectionSq_eq_l2 (P : FiniteLaw Ω) (X Y : Ω → Fin N → ℝ) :
    pairProjectionSq P X Y = (P.bind (fun _ => P)).l2
      (fun z => dot (X z.1) (X z.2)-dot (Y z.1) (Y z.2)) ^ 2 := by
  rw [l2_sq,expect_bind]
  rfl

/-- Since both contractions are in [-1,1], their squared L2 error is at
most twice their L2 error. This is the linear error used in the induction. -/
lemma pairProjectionSq_le_l2 (P : FiniteLaw Ω) (X Y : Ω → Fin N → ℝ)
    (hX : ∀ z i, |X z i| ≤ 1) (hY : ∀ z i, |Y z i| ≤ 1) :
    pairProjectionSq P X Y ≤ 2*(P.bind (fun _ => P)).l2
      (fun z => dot (X z.1) (X z.2)-dot (Y z.1) (Y z.2)) := by
  let F := fun z : Ω×Ω => dot (X z.1) (X z.2)-dot (Y z.1) (Y z.2)
  have hF (z : Ω×Ω) : |F z| ≤ 2 := by
    calc
      _ ≤ |dot (X z.1) (X z.2)|+|dot (Y z.1) (Y z.2)| := abs_sub _ _
      _ ≤ 1+1 := add_le_add (abs_dot_le_one _ _ (hX _) (hX _)) (abs_dot_le_one _ _ (hY _) (hY _))
      _ = 2 := by norm_num
  have hn : 0 ≤ (P.bind (fun _ => P)).l2 F := l2_nonneg _ _
  have hb : (P.bind (fun _ => P)).l2 F ≤ 2 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by norm_num,?_⟩
    calc
      _ ≤ (P.bind (fun _ => P)).expect (fun _ => (2:ℝ)^2) := expect_mono _ (fun z =>
        sq_le_sq.mpr (by simpa using hF z))
      _ = _ := expect_const _ _
  rw [pairProjectionSq_eq_l2]
  change (P.bind (fun _ => P)).l2 F^2 ≤ 2*(P.bind (fun _ => P)).l2 F
  nlinarith

end DilutedSpinGlass.FiniteLaw
end

end

end OAI
