import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.PrefixScoreNonneg
import OAI.Probability.CriticalPercolation.Entropy.BinaryWords
import OAI.Probability.CriticalPercolation.Entropy.BinaryMarks

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest FiniteEntropy ExactExposure

variable {V E : Type*}

abbrev FixedDescriptor (n : ℕ) := Fin n → Bool × Bool × Bool

lemma fixedDescriptor_card (n : ℕ) : Fintype.card (FixedDescriptor n) = 8^n := by
  simp only [FixedDescriptor,Fintype.card_fun,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]

noncomputable def descriptor (G : BondGraph V E) (d : ℕ) (x : ℕ → V)
    (n : ℕ) (h : History E n) (ω : Set E) : FixedDescriptor n := fun i =>
  (sides n h i, decide (marks n h i ≠ none), decide (i.val+2 ∈ activeNodes G d x n h ω))

lemma descriptor_sides (G : BondGraph V E) (d : ℕ) (x : ℕ → V)
    (n : ℕ) (h : History E n) (ω : Set E) (D : FixedDescriptor n)
    (hD : descriptor G d x n h ω = D) : sides n h = fun i => (D i).1 := by
  funext i
  exact congrArg (fun D : FixedDescriptor n => (D i).1) hD

lemma sum_history_words [Fintype E] (n : ℕ) (f : History E n → ℝ) :
    (∑ h, f h) = ∑ b : Fin n → Bool, ∑ m : Fin n → Option E, f (fromWords n b m) := by
  rw [← (wordsEquiv (E := E) n).symm.sum_comp f,Fintype.sum_prod_type]
  rfl

section Finite
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ)

noncomputable def jointMass (z : (E → Bool) × History E n) : ℝ :=
  FiniteProduct.density (QueryTree.bitWeight p) z.1 *
    density G order d x p w (seed G w (x 0) (x d) s) n z.2 (configuration z.1)

lemma jointMass_nonneg (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p)
    (h1 : ∀ e, w e True = p) (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (z : (E → Bool) × History E n) : 0 ≤ jointMass G order d x p w s n z := by
  exact mul_nonneg (FiniteProduct.density_nonneg (fun e b => (QueryTree.bitWeight_pos hp e b).le) _)
    (density_nonneg G order d x p w _ hp h0 h1 (seed_nonneg G w _ _ s hδ) n z.2 _)

lemma jointMass_normalized (ho : LazyDFS.Exhaustive G order) (hd : 2 ≤ d)
    (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0<c)
    (hconn : ∀ j k, j<k → k≤d → k-j<d →
      c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x j) (x k)))
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s)) :
    ∑ z, jointMass G order d x p w s n z = 1 := by
  have hw : QueryTree.bitWeight p = fun e (b : Bool) => w e (b = true) := by
    funext e b
    cases b <;> simp [QueryTree.bitWeight,h0,h1]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp only [jointMass]
  have ht := endpoint_density_normalized G order ho hd x hp w h0 h1 hc hconn s hδ n
  rw [← ht]
  apply Finset.sum_congr rfl
  intro h _
  have he := expect_configuration w
    (fun η : Set E => density G order d x p w (seed G w (x 0) (x d) s) n h η)
  rw [← hw] at he
  refine Eq.trans ?_ he
  unfold expect
  apply Finset.sum_congr
  · ext f; simp only [Finset.mem_univ]
  · intro f _; rfl

noncomputable def descriptorMass (D : FixedDescriptor n) : ℝ :=
  pushMass (fun z : (E → Bool) × History E n => descriptor G d x n z.2 (configuration z.1))
    (jointMass G order d x p w s n) D

lemma descriptorMass_sum :
    (∑ D, descriptorMass G order d x p w s n D) = ∑ z, jointMass G order d x p w s n z :=
  pushMass_sum _ _

theorem exists_descriptor (hZ : ∑ z, jointMass G order d x p w s n z = 1) :
    ∃ D : FixedDescriptor n, (8:ℝ)^(- (n:ℤ)) ≤ descriptorMass G order d x p w s n D := by
  obtain ⟨D,hD,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (FixedDescriptor n))
    (descriptorMass G order d x p w s n) Finset.univ_nonempty
  have hs : 1 ≤ (8:ℝ)^n * descriptorMass G order d x p w s n D := by
    calc
      1 = ∑ D', descriptorMass G order d x p w s n D' := (descriptorMass_sum G order d x p w s n).trans hZ |>.symm
      _ ≤ ∑ _D' : FixedDescriptor n, descriptorMass G order d x p w s n D :=
        Finset.sum_le_sum (fun D' hD' => hmax D' hD')
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,fixedDescriptor_card,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  refine ⟨D,?_⟩
  rw [zpow_neg, zpow_natCast]
  rw [← one_div]
  exact (div_le_iff₀ (pow_pos (by norm_num : (0:ℝ)<8) n)).mpr (by simpa only [mul_comm] using hs)

noncomputable def fixedMass (D : FixedDescriptor n) (z : (E → Bool) × (Fin n → Option E)) : ℝ :=
  let h := fromWords n (fun i => (D i).1) z.2
  if descriptor G d x n h (configuration z.1) = D then
    jointMass G order d x p w s n (z.1,h) else 0

lemma fixedMass_sum (D : FixedDescriptor n) :
    (∑ z, fixedMass G order d x p w s n D z) = descriptorMass G order d x p w s n D := by
  unfold descriptorMass pushMass
  conv_rhs => rw [Fintype.sum_prod_type]
  simp_rw [sum_history_words]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  symm
  apply (Finset.sum_eq_single (fun i => (D i).1) ?_ ?_).trans
  · apply Finset.sum_congr rfl
    intro m _
    unfold fixedMass
    dsimp only
    split_ifs <;> rfl
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro m _
    have hne : descriptor G d x n (fromWords n b m) (configuration ω) ≠ D := by
      intro he
      have hs := descriptor_sides G d x n _ _ D he
      rw [sides_fromWords] at hs
      exact hb hs
    rw [ite_eq_right hne]
  · simp

noncomputable def conditionedMass (D : FixedDescriptor n)
    (z : (E → Bool) × (Fin n → Option E)) : ℝ :=
  fixedMass G order d x p w s n D z / descriptorMass G order d x p w s n D

lemma conditionedMass_normalized (D : FixedDescriptor n)
    (hD : 0 < descriptorMass G order d x p w s n D) :
    ∑ z, conditionedMass G order d x p w s n D z = 1 := by
  simp only [conditionedMass,← Finset.sum_div,fixedMass_sum,div_self hD.ne']

lemma conditionedMass_nonneg (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p)
    (h1 : ∀ e, w e True = p) (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (D : FixedDescriptor n) (hD : 0 < descriptorMass G order d x p w s n D)
    (z : (E → Bool) × (Fin n → Option E)) : 0 ≤ conditionedMass G order d x p w s n D z := by
  apply div_nonneg _ hD.le
  unfold fixedMass
  dsimp only
  split_ifs
  · exact jointMass_nonneg G order d x p w s n hp h0 h1 hδ _
  · rfl

lemma conditionedMass_support (D : FixedDescriptor n)
    (z : (E → Bool) × (Fin n → Option E))
    (hz : conditionedMass G order d x p w s n D z ≠ 0) :
    let h := fromWords n (fun i => (D i).1) z.2
    descriptor G d x n h (configuration z.1) = D ∧
    density G order d x p w (seed G w (x 0) (x d) s) n h (configuration z.1) ≠ 0 := by
  have hf := (div_ne_zero_iff.mp hz).1
  unfold fixedMass at hf
  dsimp only at hf ⊢
  split_ifs at hf with ht
  · exact ⟨ht,(mul_ne_zero_iff.mp hf).2⟩
  · exact (hf rfl).elim

end Finite
end CriticalPercolation.BinaryLaw
end
end

end OAI
