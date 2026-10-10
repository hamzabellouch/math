import OAI.NumberTheory.Ostmann.Construction.SourcePriors
import OAI.NumberTheory.Ostmann.Reuse.Mertens

namespace OAI

open Erdos970

noncomputable section
open Filter
open scoped BigOperators
namespace Ostmann.Construction

def primePrefix (x : ℝ) : Finset ℕ :=
  (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime

def logLogPrimeBand (a b : ℝ) : Finset ℕ :=
  primePrefix (Real.exp (Real.exp b)) \ primePrefix (Real.exp (Real.exp a))

lemma primePrefix_mono {x y : ℝ} (hxy : x≤y) : primePrefix x ⊆ primePrefix y := by
  intro p hp
  obtain ⟨hp,hprime⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
    ⟨(Finset.mem_Ioc.mp hp).1,(Finset.mem_Ioc.mp hp).2.trans (Nat.floor_mono hxy)⟩,hprime⟩

lemma logLogPrimeBand_prime {a b : ℝ} {p : ℕ} (hp : p∈logLogPrimeBand a b) :
    Nat.Prime p := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2

lemma harmonicPrimeMass_band {a b : ℝ} (hab : a≤b) :
    harmonicPrimeMass (logLogPrimeBand a b) =
      harmonicPrimeMass (primePrefix (Real.exp (Real.exp b))) -
      harmonicPrimeMass (primePrefix (Real.exp (Real.exp a))) := by
  have hs := Finset.sum_sdiff (f := fun p : ℕ => (1:ℝ)/p)
    (primePrefix_mono (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hab)))
  dsimp [harmonicPrimeMass, logLogPrimeBand]
  linarith

lemma reciprocal_nat_le_one (p : ℕ) : (1:ℝ)/p≤1 := by
  by_cases hp : p=0
  · simp [hp]
  · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hp)).mpr
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp)

theorem logLogPrimeBand_mass_error :
    ∃ C : ℝ, 0<C ∧ ∀ a b : ℝ, 0≤a → a≤b → ∀ E : Finset ℕ, E.card≤2 →
      |harmonicPrimeMass (logLogPrimeBand a b \ E)-(b-a)|≤C := by
  obtain ⟨C,hC,hM⟩ := Ostmann.Reuse.primeReciprocal_abs_error_bound
  refine ⟨2*C+2,by linarith,?_⟩
  intro a b ha hab E hE
  have he (t : ℝ) (ht : 0≤t) : 2≤Real.exp (Real.exp t) := by
    have h₁ : (1:ℝ)≤Real.exp t := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr ht
    have h₂ : (2:ℝ)≤Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
    exact h₂.trans (Real.exp_le_exp.mpr h₁)
  have haM := hM (Real.exp (Real.exp a)) (he a ha)
  have hbM := hM (Real.exp (Real.exp b)) (he b (ha.trans hab))
  simp only [Real.log_exp] at haM hbM
  change |harmonicPrimeMass (primePrefix (Real.exp (Real.exp a)))-a|≤C at haM
  change |harmonicPrimeMass (primePrefix (Real.exp (Real.exp b)))-b|≤C at hbM
  have hdel := finite_deletion_bound (logLogPrimeBand a b) E (fun p => (1:ℝ)/p)
    (by norm_num : (0:ℝ)≤1) (fun p => div_nonneg zero_le_one (Nat.cast_nonneg p))
    reciprocal_nat_le_one
  change 0≤harmonicPrimeMass (logLogPrimeBand a b)-
      harmonicPrimeMass (logLogPrimeBand a b \ E) ∧
    harmonicPrimeMass (logLogPrimeBand a b)-harmonicPrimeMass (logLogPrimeBand a b \ E)
      ≤(E.card:ℝ)*1 at hdel
  have hcard : (E.card:ℝ)≤2 := by exact_mod_cast hE
  have hid := harmonicPrimeMass_band hab
  obtain ⟨hal,hau⟩ := abs_le.mp haM
  obtain ⟨hbl,hbu⟩ := abs_le.mp hbM
  apply abs_le.mpr
  constructor <;> linarith [hdel.1,hdel.2]

theorem logLogPrimeBand_mass_eventually {α β : ℝ} (hα : 0≤α) (hαβ : α<β) :
    ∀ᶠ L : ℝ in atTop, ∀ E : Finset ℕ, E.card≤2 →
      0<harmonicPrimeMass (logLogPrimeBand (α*L) (β*L) \ E) ∧
      (β-α)*L/2≤harmonicPrimeMass (logLogPrimeBand (α*L) (β*L) \ E) ∧
      harmonicPrimeMass (logLogPrimeBand (α*L) (β*L) \ E)≤2*(β-α)*L := by
  obtain ⟨C,hC,hbound⟩ := logLogPrimeBand_mass_error
  have hd : 0<β-α := sub_pos.mpr hαβ
  filter_upwards [eventually_ge_atTop (max 1 (2*C/(β-α)))] with L hL
  have hL1 : 1≤L := (le_max_left _ _).trans hL
  have hLC : 2*C≤(β-α)*L := by
    have := (le_max_right _ _).trans hL
    exact (div_le_iff₀ hd).mp this |>.trans_eq (mul_comm _ _)
  intro E hE
  have h := hbound (α*L) (β*L) (mul_nonneg hα (by linarith))
    (mul_le_mul_of_nonneg_right hαβ.le (by linarith)) E hE
  obtain ⟨hlo,hhi⟩ := abs_le.mp h
  have hprod : 0<(β-α)*L := mul_pos hd (by linarith)
  constructor
  · nlinarith
  constructor <;> nlinarith

end Ostmann.Construction

end

end OAI
