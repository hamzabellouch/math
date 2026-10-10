import OAI.Probability.DilutedSpin.ActualTreeSelector
import OAI.Probability.DilutedSpin.ConcreteAnalyticSelection
import OAI.Probability.DilutedSpin.CountableFullSupport

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators

 
abbrev Table (L r : ℕ) := {g : (Fin L → Fin r → Bool) → ℚ // ∀ y, |g y| ≤ 1}

/-- Two bounded mark tables and the choice of spin or marker anchor. -/
abbrev Spec (L : ℕ) := Σ r : ℕ, Table L r × Table L r × Bool

instance tableCountable (L r : ℕ) : Countable (Table L r) := inferInstance
instance specCountable (L : ℕ) : Countable (Spec L) := inferInstance
instance tableNonempty (L r : ℕ) : Nonempty (Table L r) := ⟨⟨fun _ => 0,by simp⟩⟩
instance specNonempty (L : ℕ) : Nonempty (Spec L) := ⟨⟨0,Classical.choice inferInstance,
  Classical.choice inferInstance,false⟩⟩
instance specMeasurable (L : ℕ) : MeasurableSpace (Spec L) := ⊤
instance specSingleton (L : ℕ) : MeasurableSingletonClass (Spec L) := ⟨fun _ => trivial⟩
noncomputable instance specDecidable (L : ℕ) : DecidableEq (Spec L) := Classical.decEq _

abbrev Alphabet {L : ℕ} (q : Spec L) := Fin q.1 → Bool
noncomputable def prior {L : ℕ} (q : Spec L) (_ : Fin (L+1)) : FiniteLaw (Alphabet q) :=
  FiniteLaw.pi (fun _ => MarkSelector.rademacher)

def interior {L r : ℕ} (y : FinitePath (Fin r → Bool) (L+1)) : Fin L → Fin r → Bool :=
  fun d => pathCoordinate (L+1) y d.castSucc

noncomputable def direction {L : ℕ} (q : Spec L) (σ : Spin)
    (y : FinitePath (Alphabet q) (L+1)) : ℝ :=
  (q.2.1.1 (interior y) : ℝ) * spin σ
noncomputable def anchor {L : ℕ} (q : Spec L) (σ : Spin)
    (y : FinitePath (Alphabet q) (L+1)) : ℝ :=
  (q.2.2.1.1 (interior y) : ℝ) * (if q.2.2.2 then spin σ else 1)

lemma table_bound {L r : ℕ} (g : Table L r) (y : Fin L → Fin r → Bool) :
    |(g.1 y : ℝ)| ≤ 1 := by exact_mod_cast g.2 y
lemma direction_bound {L : ℕ} (q : Spec L) (σ : Spin) (y) :
    |direction q σ y| ≤ 1 := by
  rw [direction,abs_mul]
  have hs : |spin σ| = 1 := by cases σ <;> norm_num [spin]
  rw [hs,mul_one]
  exact table_bound _ _
lemma anchor_bound {L : ℕ} (q : Spec L) (σ : Spin) (y) :
    |anchor q σ y| ≤ 1 := by
  rw [anchor,abs_mul]
  have hs : |(if q.2.2.2 then spin σ else 1 : ℝ)| = 1 := by
    split <;> cases σ <;> norm_num [spin]
  rw [hs,mul_one]
  exact table_bound _ _

/-- One fixed countable full-support law suffices for all finitely many
colors/requirements and their signed rational polarizations. -/
noncomputable def weights (L : ℕ) : Measure (Spec L × ℕ) :=
  (exists_countable_full_support (Spec L × ℕ)).choose
instance weightsProbability (L : ℕ) : IsProbabilityMeasure (weights L) :=
  (exists_countable_full_support (Spec L × ℕ)).choose_spec.1
lemma weights_pos {L : ℕ} (i : Spec L × ℕ) : 0 < (weights L).real {i} :=
  (exists_countable_full_support (Spec L × ℕ)).choose_spec.2 i

 
def signQ (b : Bool) : ℚ := if b then 1 else -1
@[simp] lemma abs_signQ (b : Bool) : |signQ b| = 1 := by cases b <;> norm_num [signQ]
@[simp] lemma cast_signQ (b : Bool) : (signQ b : ℝ) = MarkSelector.sign b := by
  cases b <;> norm_num [signQ,MarkSelector.sign]

noncomputable def selector {L r : ℕ} {C : Type} [DecidableEq C]
    (a b : Fin r → C) (d : Fin r → Fin L) (c : C) : Table L r :=
  ⟨fun y => ∏ j, (if c = a j then signQ (y (d j) j) else 1) *
      (if c = b j then signQ (y (d j) j) else 1), by
    intro y
    rw [Finset.abs_prod]
    have he : (∏ j : Fin r, |(if c = a j then signQ (y (d j) j) else 1) *
        (if c = b j then signQ (y (d j) j) else 1)|) = 1 := by
      apply Finset.prod_eq_one
      intro j _
      rw [abs_mul]
      split_ifs <;> simp
    exact he.le⟩

lemma selector_eq_pathColor {L r : ℕ} {C : Type} [DecidableEq C]
    (a b : Fin r → C) (d : Fin r → Fin L) (c : C)
    (y : FinitePath (Fin r → Bool) (L+1)) :
    ((selector a b d c).1 (interior y) : ℝ) =
      MarkSelector.pathColor a b (fun j => (d j).castSucc) c y := by
  simp only [selector,MarkSelector.pathColor,interior,Rat.cast_prod,Rat.cast_mul]
  apply Finset.prod_congr rfl
  intro j _
  split_ifs <;> simp

/-- Signed averages needed by polarization stay in the SAME finite
alphabet and in the unit-bounded rational table family. -/
noncomputable def average {L r k : ℕ} (hk : 0 < k) (ε : Fin k → Bool)
    (g : Fin k → Table L r) : Table L r :=
  ⟨fun y => (k:ℚ)⁻¹ * ∑ j, signQ (ε j) * (g j).1 y, by
    intro y
    rw [abs_mul,abs_inv,abs_of_nonneg (Nat.cast_nonneg k)]
    have h : |∑ j, signQ (ε j) * (g j).1 y| ≤ (k:ℚ) := by
      calc
        _ ≤ ∑ j, |signQ (ε j) * (g j).1 y| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin k, (1:ℚ) := by
          apply Finset.sum_le_sum
          intro j _
          simpa only [abs_mul,abs_signQ,one_mul] using (g j).2 y
        _ = _ := by simp
    have hk' : (0:ℚ) < k := by exact_mod_cast hk
    calc
      _ ≤ (k:ℚ)⁻¹ * k := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hk'.le)
      _ = 1 := inv_mul_cancel₀ hk'.ne'⟩

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
