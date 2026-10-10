import OAI.Probability.DilutedSpin.MatrixConstant
import OAI.Probability.DilutedSpin.MatrixPair
import OAI.Probability.DilutedSpin.SingletonRoot
import OAI.Probability.DilutedSpin.TripleMarginal

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance matrixEnergyPropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {L N : ℕ}

lemma grid_strictMono (hL : 0 < L) : StrictMono (grid L 0 L) := by
  intro i j hij
  dsimp only [grid]
  simp only [Nat.zero_add]
  exact div_lt_div_of_pos_right (Nat.cast_lt.mpr hij) (Nat.cast_pos.mpr hL)

lemma grid_nonneg : ∀ j, 0 ≤ grid L 0 L j := by
  intro j
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma grid_last (hL : 0 < L) : grid L 0 L (Fin.last L) = 1 := by
  simp [grid,ne_of_gt hL]

/-- The old test may be the physical overlap, rather than the projected
one. Its replacement costs precisely its L2 projection error. -/
theorem pair_energy_test_bound (n d : ℕ) (hd : d < n) (K : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hp : ∀ j, 0 ≤ m j)
    (hend : m (Fin.last n) = 1) (S : PrescribedTree n) (x y : S.Leaf) (v : S.Internal)
    (hxy : splitDepth S x y = d) (hxv : freshSplitDepth S v x = d) (hyv : freshSplitDepth S v y = d)
    (X : FinitePath Ω n → Fin N → ℝ) (hX : ∀ z i, |X z i| ≤ 1)
    (hOld : ∀ z, splitDepth S x z = d → ∀ w : Sample Ω S, X (S.pathAt z w) = X (S.pathAt y w))
    (f : Sample Ω S → ℝ) :
    (-gamma S m v)*KernelTower.prefixEnergyAt n K d X ≤
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) +
      pairObservableHistory K m S x d (fun z w => FiniteLaw.dot (X z) (X w)) f +
      pairHistoryMass S m x * (S.sampleLaw K).l2
        (fun z => FiniteLaw.dot (X (S.pathAt x z)) (X (S.pathAt y z))-f z) := by
  let R := fun z w => FiniteLaw.dot (X z) (X w)
  let F := fun z : Sample Ω S => R (S.pathAt x z) (S.pathAt y z)
  have hR : ∀ z w, |R z w| ≤ 1 := fun z w => FiniteLaw.abs_dot_le_one _ _ (hX z) (hX w)
  have hδ : 0 ≤ m ⟨d+1,by omega⟩-m ⟨d,by omega⟩ := sub_nonneg.mpr (hm (by simp))
  have hF : (S.sampleLaw K).expect (fun z => F z^2) ≤ 1 := by
    calc
      _ ≤ (S.sampleLaw K).expect (fun _ => 1) := FiniteLaw.expect_mono _ (fun z =>
        (sq_le_one_iff_abs_le_one _).mpr (hR _ _))
      _ = _ := FiniteLaw.expect_const _ _
  have henergy := general_decorrelation_bound_at n d hd K m hm hp hend S x y v
    hxy hxv hyv X hOld
  have htest := pairObservableHistory_l2 K m S x d R (fun z => F z-f z) hR
  rw [pairObservableHistory_sub_test] at htest
  have htest' := (le_abs_self _).trans htest
  have hsq := mul_le_mul_of_nonneg_left hF hδ
  change (-gamma S m v)*KernelTower.prefixEnergyAt n K d X ≤
    (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)*(S.sampleLaw K).expect (fun z => F z^2)+
      pairObservableHistory K m S x d R F at henergy
  change (-gamma S m v)*KernelTower.prefixEnergyAt n K d X ≤
    (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)+pairObservableHistory K m S x d R f+
      pairHistoryMass S m x*(S.sampleLaw K).l2 (fun z => F z-f z)
  linarith

lemma signed_approximation {H HP J E : ℝ} (hJ : J ≠ 0) (h : |H-HP| ≤ E) :
    HP/J ≤ H/J+E/|J| := by
  have he : HP/J-H/J = (HP-H)/J := by ring
  have hh : HP/J-H/J ≤ E/|J| := by
    rw [he]
    calc
      _ ≤ |(HP-H)/J| := le_abs_self _
      _ = |H-HP|/|J| := by rw [abs_div,abs_sub_comm]
      _ ≤ E/|J| := div_le_div_of_nonneg_right h (le_of_lt (abs_pos.mpr hJ))
  linarith

/-- Pointwise-in-the-root crux of the shifted-shape induction. The first term
is SIGNED (not the expectation of its absolute value), so the physical
perturbation identity can be used after root averaging. Every error is an
actual single-copy L2 error and has the literal protected-history charge. -/
theorem matrix_energy_pointwise (hL : 0 < L) (Q : Finset ℕ)
    (T S : PrescribedTree L) (q : C → T.Leaf) (hq : Function.Bijective q)
    (hS : branchingCount S (· ∈ Q) = 0) (K : KernelTower Ω L)
    (a c : C) (hac : a ≠ c) (cs : List C) (hcs : cs.Nodup)
    (hdis : ∀ d ∈ cs, d ∉ insert c ({a} : Finset C))
    (hfull : insert c ({a} : Finset C) ∪ cs.toFinset = Finset.univ)
    (x y : S.Leaf) (v : S.Internal) (d : ℕ) (hd : d < L)
    (hqd : splitDepth T (q a) (q c) = d) (hxy : splitDepth S x y = d)
    (hxv : freshSplitDepth S v x = d) (hyv : freshSplitDepth S v y = d)
    (X : FinitePath Ω L → Fin N → ℝ) (hX : ∀ z i, |X z i| ≤ 1)
    (hOld : ∀ z, splitDepth S x z = d → ∀ w : Sample Ω S, X (S.pathAt z w) = X (S.pathAt y w))
    (A : (C → FinitePath Ω L) → ℝ) (f : Sample Ω S → ℝ) (hf : ∀ z, |f z| ≤ 1) :
    let m := grid L 0 L
    let J := partialKappa T m (Finset.univ.image q) /
      partialKappa T m ((insert c ({a} : Finset C)).image q)
    let H := weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect (fun z => g z*A (fun b => D.pathAt (pos b) z)))
      m (c::cs) S (Finset.univ.erase x) id (fun _ => x) f
    let E := (T.sampleLaw K).l2 (fun z => A (fun b => T.pathAt (q b) z)-
      FiniteLaw.dot (X (T.pathAt (q a) z)) (X (T.pathAt (q c) z)))
    let B := chargeBound (2*(leaves S+(c::cs).length:ℕ))
      ((Q.card:ℝ)*(leaves S+(c::cs).length:ℕ)) (c::cs).length (branchingCount T (· ∈ Q)) *
      (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))
    (-gamma S m v)*KernelTower.prefixEnergyAt L K d X ≤
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) + H/J + E*B/|J| +
      pairHistoryMass S m x * (S.sampleLaw K).l2
        (fun z => FiniteLaw.dot (X (S.pathAt x z)) (X (S.pathAt y z))-f z) := by
  dsimp only
  let m := grid L 0 L
  let J := partialKappa T m (Finset.univ.image q) /
      partialKappa T m ((insert c ({a} : Finset C)).image q)
  let R := fun z w => FiniteLaw.dot (X z) (X w)
  let F := fun z : Sample Ω S => R (S.pathAt x z) (S.pathAt y z)
  let H := weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect (fun z => g z*A (fun b => D.pathAt (pos b) z)))
      m (c::cs) S (Finset.univ.erase x) id (fun _ => x) f
  let HP := weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect (fun z => g z*R (D.pathAt (pos a) z) (D.pathAt (pos c) z)))
      m (c::cs) S (Finset.univ.erase x) id (fun _ => x) f
  let E := (T.sampleLaw K).l2 (fun z => A (fun b => T.pathAt (q b) z)-R (T.pathAt (q a) z) (T.pathAt (q c) z))
  let B := chargeBound (2*(leaves S+(c::cs).length:ℕ))
      ((Q.card:ℝ)*(leaves S+(c::cs).length:ℕ)) (c::cs).length (branchingCount T (· ∈ Q)) *
      (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))
  have hm := grid_strictMono hL
  have hp : ∀ j, 0 ≤ m j := grid_nonneg
  have hend : m (Fin.last L) = 1 := grid_last hL
  have hJ : J ≠ 0 := div_ne_zero (partialKappa_ne_zero T m hm hp _)
    (partialKappa_ne_zero T m hm hp _)
  have henergy := pair_energy_test_bound L d hd K m hm.monotone hp hend S x y v
    hxy hxv hyv X hX hOld f
  have hU : (Finset.univ.erase x).card ≤ leaves S := by
    exact (Finset.card_erase_le).trans (by simp only [Finset.card_univ, card_leaf]; rfl)
  have hproj : |H-HP| ≤ E*B := by
    simpa only [H, HP, E, B, m, weightedMatrixHistory] using
      (projection_history_difference hL Q T S q hq.2 hS K A
        (fun z => R (z a) (z c)) (c::cs) (Finset.univ.erase x) id (fun _ => x) f hf hU)
  have hpair : HP = J*pairObservableHistory K m S x d R f := by
    have h := matrixHistory_first_pair T q hq.1 K m hm hp hend a c hac cs hcs hdis hfull S x R f
    simpa only [hqd] using h
  have happrox := signed_approximation hJ hproj
  rw [hpair,mul_div_cancel_left₀ _ hJ] at happrox
  change (-gamma S m v)*KernelTower.prefixEnergyAt L K d X ≤
    (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)+H/J+E*B/|J|+
      pairHistoryMass S m x*(S.sampleLaw K).l2 (fun z => F z-f z)
  change (-gamma S m v)*KernelTower.prefixEnergyAt L K d X ≤
    (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)+pairObservableHistory K m S x d R f+
      pairHistoryMass S m x*(S.sampleLaw K).l2 (fun z => F z-f z) at henergy
  linarith

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance matrixEnergyCoefficientPropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {n : ℕ}

omit [Fintype C] in
lemma complete_list_nodup (a c : C) (hac : a ≠ c) (cs : List C)
    (hcs : cs.Nodup) (hdis : ∀ d ∈ cs, d ∉ insert c ({a} : Finset C)) :
    (c::cs).Nodup ∧ (∀ d ∈ c::cs, d ≠ a) := by
  refine ⟨List.nodup_cons.mpr ⟨?_,hcs⟩,?_⟩
  · intro h; exact hdis c h (by simp)
  · intro d hd
    rcases List.mem_cons.mp hd with h|h
    · exact h ▸ hac.symm
    · intro he; subst d; exact hdis a h (by simp)

lemma complete_list_union (a c : C) (cs : List C)
    (hfull : insert c ({a} : Finset C) ∪ cs.toFinset = Finset.univ) :
    ({a} : Finset C) ∪ (c::cs).toFinset = Finset.univ := by
  rw [List.toFinset_cons]
  simpa only [Finset.union_insert,Finset.insert_union,Finset.union_singleton,Finset.insert_comm] using hfull

lemma kappa_pair_quotient (T : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Injective q) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
    (a c : C) (hac : a ≠ c) (d : ℕ) (hd : d < n)
    (hqd : splitDepth T (q a) (q c) = d) :
    partialKappa T m (Finset.univ.image q) /
      (partialKappa T m (Finset.univ.image q) / partialKappa T m ((insert c ({a} : Finset C)).image q)) =
      m ⟨d,by omega⟩-m ⟨d+1,by omega⟩ := by
  rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ (partialKappa_ne_zero T m hm hp _)]
  rw [Finset.image_insert,Finset.image_singleton,partialKappa_pair T m hm hp hend (q a) (q c)
    (fun h => hac (hq h))]
  simp only [hqd]

/-- Exact centering coefficient of an actual matrix-observable history. The
normalizer uses the protected PAIR, so one factor -delta remains. -/
theorem matrixHistory_one_div (T : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Bijective q) (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
    (a c : C) (hac : a ≠ c) (cs : List C) (hcs : cs.Nodup)
    (hdis : ∀ d ∈ cs, d ∉ insert c ({a} : Finset C))
    (hfull : insert c ({a} : Finset C) ∪ cs.toFinset = Finset.univ)
    (S : PrescribedTree n) (x : S.Leaf) (A : (C → FinitePath Ω n) → ℝ)
    (d : ℕ) (hd : d < n) (hqd : splitDepth T (q a) (q c) = d) :
    weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect (fun z => g z*A (fun b => D.pathAt (pos b) z)))
      m (c::cs) S (Finset.univ.erase x) id (fun _ => x) (fun _ => 1) /
      (partialKappa T m (Finset.univ.image q) / partialKappa T m ((insert c ({a} : Finset C)).image q)) =
    (m ⟨d,by omega⟩-m ⟨d+1,by omega⟩) *
      (T.sampleLaw K).expect (fun z => A (fun b => T.pathAt (q b) z)) := by
  have hc := complete_list_nodup a c hac cs hcs hdis
  rw [weightedMatrixHistory_one T q hq K m hm hp hend a (c::cs) hc.1 hc.2
    (complete_list_union a c cs hfull) S x A, mul_div_right_comm,
    kappa_pair_quotient T q hq.1 m hm hp hend a c hac d hd hqd]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
