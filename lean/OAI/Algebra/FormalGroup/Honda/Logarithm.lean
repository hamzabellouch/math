import OAI.Algebra.FormalGroup.Honda.PTypical
import OAI.Algebra.FormalGroup.Honda.Target

namespace OAI

noncomputable section

namespace HeightThree.LogarithmicConstruction

open MvPowerSeries

variable {R : Type*} [CommRing R]

structure StrictLog where
  series : PowerSeries R
  constant_zero : series.constantCoeff = 0
  linear_one : series.coeff 1 = 1

namespace StrictLog

variable (l : StrictLog (R := R))

lemma hasSubst : PowerSeries.HasSubst l.series :=
  PowerSeries.HasSubst.of_constantCoeff_zero l.constant_zero

lemma linear_unit : IsUnit (l.series.coeff 1) := l.linear_one ▸ isUnit_one

def inv : PowerSeries R := l.series.substInvOfIsUnit l.linear_unit

@[simp] lemma inv_constant : l.inv.constantCoeff = 0 :=
  PowerSeries.constantCoeff_substInvOfIsUnit _ _

lemma inv_hasSubst : PowerSeries.HasSubst l.inv :=
  PowerSeries.HasSubst.of_constantCoeff_zero l.inv_constant

@[simp] lemma subst_inv : l.series.subst l.inv = PowerSeries.X :=
  PowerSeries.subst_substInvOfIsUnit_right _ l.constant_zero l.linear_unit

@[simp] lemma inv_subst : l.inv.subst l.series = PowerSeries.X :=
  PowerSeries.subst_substInvOfIsUnit_left _ l.constant_zero l.linear_unit

@[simp] lemma inv_linear : l.inv.coeff 1 = 1 := by
  rw [inv, PowerSeries.coeff_one_substInvOfIsUnit]
  have h : l.linear_unit.unit = 1 := by
    apply Units.ext
    simpa using l.linear_one
  rw [h]
  rfl

lemma log_exp {σ : Type*} (a : MvPowerSeries σ R) (ha : PowerSeries.HasSubst a) :
    l.series.subst (l.inv.subst a) = a := by
  rw [← PowerSeries.subst_comp_subst_apply l.inv_hasSubst ha, l.subst_inv,
    PowerSeries.subst_X ha]

lemma exp_log {σ : Type*} (a : MvPowerSeries σ R) (ha : PowerSeries.HasSubst a) :
    l.inv.subst (l.series.subst a) = a := by
  rw [← PowerSeries.subst_comp_subst_apply l.hasSubst ha, l.inv_subst,
    PowerSeries.subst_X ha]

lemma subst_injective {σ : Type*} {a b : MvPowerSeries σ R}
    (ha : PowerSeries.HasSubst a) (hb : PowerSeries.HasSubst b)
    (h : l.series.subst a = l.series.subst b) : a = b := by
  have := congrArg (fun x : MvPowerSeries σ R => l.inv.subst x) h
  simpa only [l.exp_log a ha, l.exp_log b hb] using this

def sumSeries : MvPowerSeries (Fin 2) R :=
  l.series.subst (X 0) + l.series.subst (X 1)

@[simp] lemma sumSeries_constant : l.sumSeries.constantCoeff = 0 := by
  simp only [sumSeries, map_add]
  rw [PowerSeries.constantCoeff_subst_eq_zero (by simp) l.series l.constant_zero,
    PowerSeries.constantCoeff_subst_eq_zero (by simp) l.series l.constant_zero, add_zero]

lemma sumSeries_hasSubst : PowerSeries.HasSubst l.sumSeries :=
  PowerSeries.HasSubst.of_constantCoeff_zero l.sumSeries_constant

def law : MvPowerSeries (Fin 2) R := l.inv.subst l.sumSeries

@[simp] lemma law_constant : l.law.constantCoeff = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero l.sumSeries_constant l.inv l.inv_constant

@[simp] lemma log_law : l.series.subst l.law = l.sumSeries :=
  l.log_exp _ l.sumSeries_hasSubst

lemma coeff_subst_linear {σ : Type*} (f : PowerSeries R)
    (a : MvPowerSeries σ R) (ha : a.constantCoeff = 0) (i : σ) :
    coeff (Finsupp.single i 1) (f.subst a) =
      f.coeff 1 * coeff (Finsupp.single i 1) a := by
  classical
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha),
    finsum_eq_single _ 1]
  · simp
  · intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [MvPowerSeries.coeff_one]
    · have hlt : ((Finsupp.degree (Finsupp.single i 1 : σ →₀ ℕ) : ℕ) : ℕ∞) < (n : ℕ∞) := by
        simpa using (show (1 : ℕ∞) < (n : ℕ∞) by exact_mod_cast (by omega : 1 < n))
      rw [coeff_of_lt_order (lt_of_lt_of_le hlt
        (le_order_pow_of_constantCoeff_eq_zero n ha)), smul_zero]

@[simp] lemma sumSeries_linear (i : Fin 2) :
    coeff (Finsupp.single i 1) l.sumSeries = 1 := by
  simp only [sumSeries, map_add]
  rw [coeff_subst_linear _ _ (by simp), coeff_subst_linear _ _ (by simp),
    l.linear_one, one_mul, one_mul]
  fin_cases i <;> simp [coeff_index_single_X]

@[simp] lemma law_linear (i : Fin 2) :
    coeff (Finsupp.single i 1) l.law = 1 := by
  rw [law, coeff_subst_linear _ _ l.sumSeries_constant, l.inv_linear,
    l.sumSeries_linear, one_mul]

lemma subst_after_mv {σ τ : Type*} (f : PowerSeries R)
    (a : MvPowerSeries σ R) (ha : PowerSeries.HasSubst a)
    (b : σ → MvPowerSeries τ R) (hb : MvPowerSeries.HasSubst b) :
    (f.subst a).subst b = f.subst (a.subst b) := by
  exact MvPowerSeries.subst_comp_subst_apply ha.const hb f

lemma law_pair {σ : Type*} (a b : MvPowerSeries σ R)
    (ha : a.constantCoeff = 0) (hb : b.constantCoeff = 0) :
    l.law.subst ![a, b] = l.inv.subst (l.series.subst a + l.series.subst b) := by
  have hab : MvPowerSeries.HasSubst ![a, b] :=
    hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> assumption)
  rw [law, subst_after_mv _ _ l.sumSeries_hasSubst _ hab]
  congr 1
  rw [sumSeries, MvPowerSeries.subst_add hab,
    subst_after_mv _ _ (PowerSeries.HasSubst.X 0) _ hab,
    subst_after_mv _ _ (PowerSeries.HasSubst.X 1) _ hab,
    MvPowerSeries.subst_X hab, MvPowerSeries.subst_X hab]
  rfl

lemma law_pair_constant {σ : Type*} (a b : MvPowerSeries σ R)
    (ha : a.constantCoeff = 0) (hb : b.constantCoeff = 0) :
    (l.law.subst ![a, b]).constantCoeff = 0 := by
  apply MvPowerSeries.constantCoeff_subst_eq_zero
    (hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> assumption))
    (by intro i; fin_cases i <;> assumption) l.law_constant

lemma log_law_pair {σ : Type*} (a b : MvPowerSeries σ R)
    (ha : a.constantCoeff = 0) (hb : b.constantCoeff = 0) :
    l.series.subst (l.law.subst ![a, b]) = l.series.subst a + l.series.subst b := by
  rw [l.law_pair a b ha hb]
  exact l.log_exp _ (PowerSeries.HasSubst.of_constantCoeff_zero (by
    rw [map_add, PowerSeries.constantCoeff_subst_eq_zero ha _ l.constant_zero,
      PowerSeries.constantCoeff_subst_eq_zero hb _ l.constant_zero, add_zero]))

def formalGroup : FormalGroup R where
  toPowerSeries := l.law
  zero_constantCoeff := l.law_constant
  lin_coeff_X := l.law_linear 0
  lin_coeff_Y := l.law_linear 1
  assoc := by
    have hX (i : Fin 3) : (X i : MvPowerSeries (Fin 3) R).constantCoeff = 0 := by simp
    apply l.subst_injective
      (PowerSeries.HasSubst.of_constantCoeff_zero
        (l.law_pair_constant _ _ (l.law_pair_constant _ _ (hX 0) (hX 1)) (hX 2)))
      (PowerSeries.HasSubst.of_constantCoeff_zero
        (l.law_pair_constant _ _ (hX 0) (l.law_pair_constant _ _ (hX 1) (hX 2))))
    rw [l.log_law_pair _ _ (l.law_pair_constant _ _ (hX 0) (hX 1)) (hX 2),
      l.log_law_pair _ _ (hX 0) (l.law_pair_constant _ _ (hX 1) (hX 2)),
      l.log_law_pair _ _ (hX 0) (hX 1), l.log_law_pair _ _ (hX 1) (hX 2), add_assoc]

instance formalGroup_isComm : l.formalGroup.IsComm where
  comm := by
    change l.law = l.law.subst ![X 1, X 0]
    rw [l.law_pair _ _ (by simp) (by simp)]
    exact congrArg (PowerSeries.subst · l.inv) (add_comm _ _)

end StrictLog
end HeightThree.LogarithmicConstruction

end

end OAI
