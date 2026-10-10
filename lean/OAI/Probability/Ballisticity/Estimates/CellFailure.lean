import Mathlib
import OAI.Probability.Ballisticity.Estimates.ProtectionFirstFailure
import OAI.Probability.Ballisticity.Estimates.CellAttempt

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

noncomputable def cellLateInitial {d k : ℕ} (e f : Direction d) (hef : e.1≠f.1)
    (a c ρ : ℝ) (hc : 0 ≤ c) (hρ : 0 ≤ ρ) (Hs He : ℕ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (ω : Environment d) :
    BudgetProfile (k:=k) e f (a+Hs+He) (3*c*ρ/4) := by
  let p := cellEarlyProfile e f hef a (c*ρ) (mul_nonneg hc hρ) Hs He π ω
  refine ⟨p.val,p.property.1,?_⟩
  have heq : 3*(c*ρ)/4=3*c*ρ/4 := by ring
  simpa only [heq] using p.property.2

lemma cellLateInitial_measurable {d k : ℕ} (e f : Direction d) (hef : e.1≠f.1)
    (a c ρ : ℝ) (hc : 0 ≤ c) (hρ : 0 ≤ ρ) (Hs He : ℕ)
    (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+Hs+He))) _
      (cellLateInitial e f hef a c ρ hc hρ Hs He π) := by
  let : MeasurableSpace (Environment d) := rowSigma (BelowHeight (realPosition (step e)) (a+Hs+He))
  exact (measurable_subtype_coe.comp
    (cellEarlyProfile_measurable e f hef a (c*ρ) (mul_nonneg hc hρ) Hs He π hπ)).subtype_mk

def consumedCellFailure {Ω : Type*} (seed : Ω → ℝ≥0∞) (early : Ω → ℝ)
    (q : ℕ → Ω → ℝ) (g₀ g₁ kA : ℝ) (s m n : ℕ) : Set Ω :=
  {ω | n=1 ∧ seed ω < ENNReal.ofReal g₀} ∪
  {ω | n=min s m ∧ ENNReal.ofReal g₀ ≤ seed ω ∧ early ω < g₁} ∪
  {ω | s  <  n ∧ n  ≤  m ∧ ENNReal.ofReal g₀ ≤ seed ω ∧ g₁ ≤ early ω ∧
    ω∈firstProtectionFailure q kA s (n-s-1)}

lemma triple_exp_failure {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    3*Real.exp (-5*(k:ℝ)*n)  ≤  Real.exp (-2*(k:ℝ)*n) := by
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hkn : 1 ≤ (k:ℝ)*n := one_le_mul_of_one_le_of_one_le hk' hn'
  have hh : 3 ≤ Real.exp (3*(k:ℝ)*n) := by
    have ht := Real.add_one_le_exp (3*(k:ℝ)*n)
    nlinarith only [hkn,ht]
  calc
    _  ≤  Real.exp (3*(k:ℝ)*n)*Real.exp (-5*(k:ℝ)*n) :=
      mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

lemma consumedCellFailure_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (seed : Ω → ℝ≥0∞) (early : Ω → ℝ) (q : ℕ → Ω → ℝ)
    (g₀ g₁ kA : ℝ) (s m n k : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n)
    (E : Set Ω)
    (hseed : μ (E∩{ω | seed ω < ENNReal.ofReal g₀}) ≤ ENNReal.ofReal (Real.exp (-6*(k:ℝ)))*μ E)
    (hearly : μ (E∩{ω | early ω < g₁}) ≤ ENNReal.ofReal (Real.exp (-6*(k:ℝ)*s))*μ E)
    (hlate : s  <  n → n  ≤  m → μ (E∩firstProtectionFailure q kA s (n-s-1)) ≤
      ENNReal.ofReal (Real.exp (-5*(k:ℝ)*n))*μ E) :
    μ (E∩consumedCellFailure seed early q g₀ g₁ kA s m n) ≤
      ENNReal.ofReal (Real.exp (-2*(k:ℝ)*n))*μ E := by
  let b := ENNReal.ofReal (Real.exp (-5*(k:ℝ)*n))*μ E
  have hs : μ (E∩{ω | n=1 ∧ seed ω < ENNReal.ofReal g₀}) ≤ b := by
    by_cases he : n=1
    · subst n
      calc
        _ ≤ μ (E∩{ω | seed ω < ENNReal.ofReal g₀}) :=
          measure_mono (fun ω hω => ⟨hω.1,hω.2.2⟩)
        _ ≤ ENNReal.ofReal (Real.exp (-6*(k:ℝ)))*μ E := hseed
        _ ≤ b := by
          dsimp [b]
          apply mul_le_mul_left
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          simp only [Nat.cast_one,mul_one]
          linarith [Nat.cast_nonneg (α:=ℝ) k]
    · simp [he,b]
  have he : μ (E∩{ω | n=min s m ∧ ENNReal.ofReal g₀ ≤ seed ω ∧ early ω < g₁}) ≤ b := by
    by_cases hnm : n=min s m
    · have hns : n ≤ s := hnm ▸ min_le_left _ _
      have hns' : (n:ℝ) ≤ s := by exact_mod_cast hns
      calc
        _ ≤ μ (E∩{ω | early ω < g₁}) :=
          measure_mono (fun ω hω => ⟨hω.1,hω.2.2.2⟩)
        _ ≤ ENNReal.ofReal (Real.exp (-6*(k:ℝ)*s))*μ E := hearly
        _ ≤ b := by
          dsimp [b]
          apply mul_le_mul_left
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
          nlinarith [mul_le_mul_of_nonneg_left hns' (Nat.cast_nonneg (α:=ℝ) k),
            mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) hn0]
    · simp [hnm,b]
  have hl : μ (E∩{ω | s < n ∧ n ≤ m ∧ ENNReal.ofReal g₀ ≤ seed ω ∧ g₁ ≤ early ω ∧
      ω∈firstProtectionFailure q kA s (n-s-1)}) ≤ b := by
    by_cases hs : s < n
    · by_cases hm : n ≤ m
      · calc
          _ ≤ μ (E∩firstProtectionFailure q kA s (n-s-1)) :=
            measure_mono (fun ω hω => ⟨hω.1,hω.2.2.2.2.2⟩)
          _ ≤ b := hlate hs hm
      · simp [hm,b]
    · simp [hs,b]
  have ht : μ (E∩consumedCellFailure seed early q g₀ g₁ kA s m n) ≤ b+b+b := by
    unfold consumedCellFailure
    rw [Set.inter_union_distrib_left,Set.inter_union_distrib_left]
    exact (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add hs he)) hl)
  apply ht.trans
  dsimp [b]
  rw [←add_mul,←add_mul,←ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
    ←ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le]
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  convert triple_exp_failure hk hn using 1
  ring

end DirectionalTransience

end

end OAI
