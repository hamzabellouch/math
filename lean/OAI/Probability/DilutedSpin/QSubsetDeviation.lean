import OAI.Probability.DilutedSpin.DeviationLimitTools
import OAI.Probability.DilutedSpin.PhysicalSubtreeConcentration
import OAI.Probability.DilutedSpin.RootOverlapDeviation

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory ReducedTopology Filter
open scoped BigOperators Topology
noncomputable local instance qSubsetDeviationDecidableEq (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
noncomputable local instance qSubsetDeviationDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Z : Type} [MeasurableSpace Z] {n N : ℕ}

noncomputable def shapeDeviation (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (S : PrescribedTree n) (K : (z : Z) → KernelTower (Ω z) n)
    (V : (z : Z) → FinitePath (Ω z) n → Fin N → ℝ) : ℝ :=
  ∑ A : Finset S.Leaf, if A.Nonempty then subsetDeviation μ Ω S A K V else 0

lemma shapeDeviation_nonneg (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (S : PrescribedTree n) (K : (z : Z) → KernelTower (Ω z) n)
    (V : (z : Z) → FinitePath (Ω z) n → Fin N → ℝ) :
    0 ≤ shapeDeviation μ Ω S K V := by
  apply Finset.sum_nonneg
  intro A _
  split_ifs
  · exact FiniteLaw.mixedDeviation_nonneg _ _ _ _
  · rfl

lemma shapeDeviation_le_subtree (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (K : (z : Z) → KernelTower (Ω z) n)
    (V : (z : Z) → FinitePath (Ω z) n → Fin N → ℝ)
    (F : PrescribedTree n → ℝ) (hF : ∀ S, 0≤F S) {t : ℝ} (ht : 0<t)
    (hdev : ∀ S, overlapDeviation μ Ω S K V≤F S/(2*t)+t/2)
    (S : PrescribedTree n) (b : ℕ) (hS : S.leaves=b) :
    shapeDeviation μ Ω S K V ≤ (2:ℝ)^b*(subtreePotential b F S/(2*t)+t/2) := by
  have hle (A : Finset S.Leaf) :
      (if A.Nonempty then subsetDeviation μ Ω S A K V else 0)≤ subtreePotential b F S/(2*t)+t/2 := by
    by_cases ha : A.Nonempty
    · rw [ite_eq_left ha]
      obtain ⟨U,f,hf⟩ := exists_subset_tree S A ha
      rw [f.subsetDeviation_eq μ Ω A hf K V]
      apply (hdev U).trans
      exact add_le_add (div_le_div_of_nonneg_right
        (le_subtreePotential F hF f (f.leaves_le.trans_eq hS)) (by positivity)) le_rfl
    · rw [ite_eq_right ha]
      have := subtreePotential_nonneg F hF S (K := b)
      positivity
  unfold shapeDeviation
  apply (Finset.sum_le_sum (fun A _ => hle A)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_finset,card_leaf,hS,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]

lemma qExpect_add {n : ℕ} (m : Fin (n+1) → ℝ) (F G : PrescribedTree n → ℝ)
    (k : ℕ) (S : PrescribedTree n) :
    qExpect m (fun T => F T+G T) k S=qExpect m F k S+qExpect m G k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih => simp only [qExpect,ih,mul_add,Finset.sum_add_distrib]

lemma qExpect_div_const {n : ℕ} (m : Fin (n+1) → ℝ) (F : PrescribedTree n → ℝ)
    (c : ℝ) (k : ℕ) (S : PrescribedTree n) :
    qExpect m (fun T => F T/c) k S=qExpect m F k S/c := by
  simpa only [div_eq_mul_inv] using qExpect_mul_const m F c⁻¹ k S

lemma subtreePotential_le_card {L b : ℕ} (F : PrescribedTree L → ℝ) (hF : ∀ S, F S≤1)
    (S : PrescribedTree L) : subtreePotential b F S≤
      ∑ R∈boundedTopologies b, (Fintype.card (R.Vertex → Fin L):ℝ) := by
  unfold subtreePotential
  apply Finset.sum_le_sum
  intro R _
  calc
    _ ≤ ∑ _q : R.Vertex → Fin L, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro q _
      split_ifs <;> first | exact hF _ | norm_num
    _ = _ := by simp

lemma qExpect_subtree_bounded {L : ℕ} [NeZero L] (b k : ℕ)
    (F : ℕ → PrescribedTree L → ℝ) (hF : ∀ n S, F n S≤1) :
    IsBoundedUnder (·≤·) atTop (fun n => qExpect (grid L 0 L) (subtreePotential b (F n)) k (single L)) := by
  apply isBoundedUnder_of_eventually_le (a := ∑ R∈boundedTopologies b, (Fintype.card (R.Vertex → Fin L):ℝ))
  apply Eventually.of_forall
  intro n
  have hh := qExpect_mono (grid L 0 L) (grid_strictMono (NeZero.pos L)).monotone grid_nonneg
    (fun S => subtreePotential_le_card (F n) (hF n) S (b := b)) k (single L)
  simpa only [qExpect_const _ (show grid L 0 L 0=0 by simp [grid]) (grid_last (NeZero.pos L))] using hh

lemma qExpect_shapeDeviation_le {L : ℕ} [NeZero L]
    (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (K : (z : Z) → KernelTower (Ω z) L)
    (V : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ)
    (F : PrescribedTree L → ℝ) (hF : ∀ S, 0≤F S) {t : ℝ} (ht : 0<t)
    (hdev : ∀ S, overlapDeviation μ Ω S K V≤F S/(2*t)+t/2) (k : ℕ) :
    qExpect (grid L 0 L) (fun S => shapeDeviation μ Ω S K V) k (single L) ≤
      (2:ℝ)^(k+1)*(qExpect (grid L 0 L) (subtreePotential (k+1) F) k (single L)/(2*t)+t/2) := by
  have hh := qExpect_mono_leaves (grid L 0 L) (grid_strictMono (NeZero.pos L)).monotone grid_nonneg
    (fun S => shapeDeviation μ Ω S K V)
    (fun S => (subtreePotential (k+1) F S/(2*t)+t/2)*(2:ℝ)^(k+1)) k (single L)
    (fun S hS => by
      rw [leaves_single] at hS
      have he : S.leaves=k+1 := by omega
      simpa only [mul_comm] using shapeDeviation_le_subtree μ Ω K V F hF ht hdev S (k+1) he)
  rw [qExpect_mul_const,qExpect_add,qExpect_div_const,
    qExpect_const _ (show grid L 0 L 0=0 by simp [grid]) (grid_last (NeZero.pos L))] at hh
  simpa only [mul_comm] using hh

end DilutedSpinGlass.PrescribedTree

end

end OAI
