import Mathlib
import OAI.Probability.Ballisticity.Estimates.BufferRestorationScript
import OAI.Probability.Ballisticity.Coupling.SeedOrder

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

def injectionKey {d k : ℕ} (f : Direction d) (x : Fin k → Lattice d) (j : Fin k) : Lex (ℤ × Fin k) :=
  toLex (signedHeight f (x j),j)

lemma injectionKey_injective {d k : ℕ} (f : Direction d) (x : Fin k → Lattice d) :
    Function.Injective (injectionKey f x) := by
  intro i j h
  exact congrArg Prod.snd (toLex.injective h)

noncomputable def injectionRank {d k : ℕ} (f : Direction d) (x : Fin k → Lattice d) (j : Fin k) : ℕ :=
  (Finset.univ.filter (fun i => injectionKey f x i < injectionKey f x j)).card

lemma injectionRank_lt {d k : ℕ} (f : Direction d) (x : Fin k → Lattice d) (j : Fin k) :
    injectionRank f x j < k := by
  have hs : Finset.univ.filter (fun i => injectionKey f x i < injectionKey f x j) ⊂ Finset.univ :=
    Finset.filter_ssubset.mpr ⟨j,Finset.mem_univ _,lt_irrefl _⟩
  simpa only [injectionRank,Finset.card_univ,Fintype.card_fin] using Finset.card_lt_card hs

lemma injectionRank_strict {d k : ℕ} (f : Direction d) (x : Fin k → Lattice d) (i j : Fin k)
    (hij : injectionKey f x i < injectionKey f x j) : injectionRank f x i < injectionRank f x j := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hl).2.trans hij⟩
  · intro he
    have hi : i∈Finset.univ.filter (fun l => injectionKey f x l < injectionKey f x j) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩
    rw [←he] at hi
    exact (lt_irrefl _ (Finset.mem_filter.mp hi).2)

noncomputable def injectionOffset {d k : ℕ} (f : Direction d) (M : ℕ)
    (x : Fin k → Lattice d) (j : Fin k) : ℕ := (injectionRank f x j+1)*M

noncomputable def injectTuple {d k : ℕ} (e f : Direction d) (M : ℕ) (x : Fin k → Lattice d) : Fin k → Lattice d :=
  fun j => x j + injectionOffset f M x j • step f + step e

lemma injectionOffset_le {d k : ℕ} (f : Direction d) (M : ℕ) (x : Fin k → Lattice d) (j : Fin k) :
    injectionOffset f M x j  ≤  k*M :=
  Nat.mul_le_mul_right M (injectionRank_lt f x j)

lemma injectTuple_height {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (M : ℕ) (x : Fin k → Lattice d) (a : ℝ) (hx : x∈TupleAtHeight (realPosition (step e)) a) :
    injectTuple e f M x ∈ TupleAtHeight (realPosition (step e)) (a+1) := by
  intro j
  change dot (realPosition (x j + injectionOffset f M x j • step f + step e)) (realPosition (step e))=a+1
  rw [signedHeight_projection,signedHeight_add_step_self,signedHeight_add_nsmul_other e f hef,
    Int.cast_add,Int.cast_one,←signedHeight_projection,hx j]

lemma injectTuple_separated {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (M : ℕ) (x : Fin k → Lattice d) : TupleSeparated f (M:ℝ) (injectTuple e f M x) := by
  have hg {i j : Fin k} (hij : injectionKey f x i < injectionKey f x j) :
      (M:ℤ)  ≤  signedHeight f (injectTuple e f M x j)-signedHeight f (injectTuple e f M x i) := by
    have hc : signedHeight f (x i)  ≤  signedHeight f (x j) := by
      rcases Prod.Lex.toLex_lt_toLex.mp hij with h|h
      · exact h.le
      · exact h.1.le
    have hr : (injectionRank f x i : ℤ)+1 ≤ injectionRank f x j := by
      exact_mod_cast injectionRank_strict f x i j hij
    simp only [injectTuple,signedHeight_add_step_other f e hef.symm,signedHeight_add_nsmul_step,
      injectionOffset,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    nlinarith [Int.natCast_nonneg M]
  intro i j hij
  rw [←signedHeight_cast_coordinate,←signedHeight_cast_coordinate,←Int.cast_sub,←Int.cast_abs]
  apply Int.cast_le.mpr
  rcases lt_or_gt_of_ne ((injectionKey_injective f x).ne hij) with h|h
  · exact le_trans (hg h) (by rw [abs_sub_comm]; exact le_abs_self _)
  · exact le_trans (hg h) (le_abs_self _)

lemma injectTuple_atom {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (M : ℕ) (ω : Environment d) (x : Fin k → Lattice d) (κ : ℝ≥0)
    (hκ : ∀ y u, κ ≤ (ω y).val u) :
    (κ : ℝ≥0∞)^(k*(k*M+1))  ≤  rawTupleEndpointLaw (realPosition (step e)) 1 ω x {injectTuple e f M x} := by
  have hk1 : (κ : ℝ≥0∞) ≤ 1 := (ENNReal.coe_le_coe.mpr (hκ 0 e)).trans (by exact_mod_cast row_entry_le_one (ω 0) e)
  rw [rawTupleEndpointLaw_singleton,mul_comm k (k*M+1),pow_mul]
  calc
    ((κ : ℝ≥0∞)^(k*M+1))^k = ∏ _j : Fin k, (κ : ℝ≥0∞)^(k*M+1) := by simp
    _  ≤  _ := by
      apply Finset.prod_le_prod
      intro j _
      have h := elliptic_lateral_script ω e f hef (x j) (injectionOffset f M x j) hκ {injectTuple e f M x j}
      have hp : (κ : ℝ≥0∞)^(k*M+1)  ≤  (κ : ℝ≥0∞)^(injectionOffset f M x j+1) :=
        pow_le_pow_right_of_le_one' hk1 (Nat.add_le_add_right (injectionOffset_le f M x j) 1)
      apply hp.trans
      simpa only [injectTuple,Measure.smul_apply,smul_eq_mul,Measure.dirac_apply_of_mem (Set.mem_singleton _),mul_one,
        variableHitKernel,Kernel.coe_mk,Nat.cast_one] using h

lemma injectTuple_endpoint_le {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (M : ℕ) (ω : Environment d) (x : Fin k → Lattice d) (κ : ℝ≥0)
    (hκ : ∀ y u, κ ≤ (ω y).val u) :
    (κ : ℝ≥0∞)^(k*(k*M+1)) • Measure.dirac (injectTuple e f M x) ≤
      rawTupleEndpointLaw (realPosition (step e)) 1 ω x := by
  have h : (κ : ℝ≥0∞)^(k*(k*M+1)) • Measure.dirac (injectTuple e f M x) ≤
      rawTupleEndpointLaw (realPosition (step e)) 1 ω x {injectTuple e f M x} •
        Measure.dirac (injectTuple e f M x) := by
    intro U
    simp only [Measure.smul_apply,smul_eq_mul]
    exact mul_le_mul_left (injectTuple_atom e f hef M ω x κ hκ) _
  rw [←Measure.restrict_singleton] at h
  exact h.trans Measure.restrict_le_self

noncomputable def injectionLaw {d k : ℕ} (e f : Direction d) (M : ℕ) (κ : ℝ≥0)
    (π : Measure (Fin k → Lattice d)) : Measure (Fin k → Lattice d) :=
  (κ : ℝ≥0∞)^(k*(k*M+1)) • π.map (injectTuple e f M)

lemma injectionLaw_le {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (M : ℕ) (ω : Environment d) (π : Measure (Fin k → Lattice d)) (κ : ℝ≥0)
    (hκ : ∀ y u, κ ≤ (ω y).val u) :
    injectionLaw e f M κ π ≤ rawTupleMixture (realPosition (step e)) 1 π ω := by
  rw [injectionLaw,←Measure.bind_dirac_eq_map π (measurable_of_countable _),
    ←Measure.bind_smul _ _ (measurable_of_countable _).aemeasurable]
  apply Measure.le_iff.mpr
  intro U hU
  rw [Measure.bind_apply hU (measurable_of_countable _).aemeasurable,rawTupleMixture_apply,
    lintegral_smul_measure,smul_eq_mul]
  rw [←lintegral_const_mul _ (measurable_of_countable _)]
  apply lintegral_mono
  intro x
  exact injectTuple_endpoint_le e f hef M ω x κ hκ U

lemma injectionLaw_mass {d k : ℕ} (e f : Direction d) (M : ℕ) (κ : ℝ≥0)
    (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π] :
    injectionLaw e f M κ π Set.univ = (κ : ℝ≥0∞)^(k*(k*M+1)) := by
  simp only [injectionLaw,Measure.smul_apply,smul_eq_mul,Measure.map_apply
    (measurable_of_countable _) MeasurableSet.univ,Set.preimage_univ,measure_univ,mul_one]

lemma injectionProfile_support {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (M : ℕ) (π : Measure (Fin k → Lattice d)) (a : ℝ)
    (hπ : ∀ᵐ x ∂π,x∈TupleAtHeight (realPosition (step e)) a) :
    ∀ᵐ y ∂π.map (injectTuple e f M),
      y∈TupleAtHeight (realPosition (step e)) (a+1) ∧ TupleSeparated f (M:ℝ) y := by
  rw [ae_map_iff (measurable_of_countable _).aemeasurable (Set.to_countable _).measurableSet]
  filter_upwards [hπ] with x hx
  exact ⟨injectTuple_height e f hef M x a hx,injectTuple_separated e f hef M x⟩

end DirectionalTransience

end

end OAI
