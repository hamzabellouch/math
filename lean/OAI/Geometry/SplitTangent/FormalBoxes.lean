import Mathlib
import OAI.Geometry.SplitTangent.BoxTransportBase
import OAI.Geometry.SplitTangent.BracketIntegrability
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.RationalTrivialization

namespace OAI

/-! Formal Boxes. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle Filter Topology
universe u
namespace SplitTangent

 

namespace FormalCauchy

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

 
def Causal (Φ : (ℕ → V) → ℕ → V) : Prop :=
  ∀ n f g, (∀ k, k ≤ n → f k = g k) → Φ f n = Φ g n

 

def coefficients (v : V) (Φ : (ℕ → V) → ℕ → V) : ℕ → V
  | 0 => v
  | n + 1 => ((n + 1 : ℂ)⁻¹) •
      Φ (fun k => if _ : k < n + 1 then coefficients v Φ k else 0) n
termination_by n => n

@[simp] theorem coefficients_zero (v : V) (Φ : (ℕ → V) → ℕ → V) :
    coefficients v Φ 0 = v := by rw [coefficients]

theorem coefficients_succ (v : V) (Φ : (ℕ → V) → ℕ → V)
    (hΦ : Causal Φ) (n : ℕ) :
    (n + 1 : ℂ) • coefficients v Φ (n + 1) = Φ (coefficients v Φ) n := by
  rw [coefficients, smul_smul, mul_inv_cancel₀ (by exact_mod_cast Nat.succ_ne_zero n : (n + 1 : ℂ) ≠ 0), one_smul]
  apply hΦ
  intro k hk
  simp [Nat.lt_succ_of_le hk]

 

theorem existsUnique_coefficients (v : V) (Φ : (ℕ → V) → ℕ → V)
    (hΦ : Causal Φ) :
    ∃! f : ℕ → V, f 0 = v ∧ ∀ n : ℕ, (n + 1 : ℂ) • f (n + 1) = Φ f n := by
  refine ⟨coefficients v Φ, ⟨coefficients_zero v Φ, coefficients_succ v Φ hΦ⟩, ?_⟩
  intro f hf
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact hf.1.trans (coefficients_zero v Φ).symm
    | succ n =>
      have hR : Φ f n = Φ (coefficients v Φ) n :=
        hΦ n f _ (fun k hk => ih k (Nat.lt_succ_of_le hk))
      apply (smul_right_injective V (by exact_mod_cast Nat.succ_ne_zero n : (n + 1 : ℂ) ≠ 0))
      exact (hf.2 n).trans (hR.trans (coefficients_succ v Φ hΦ n).symm)

 

section PowerSeriesCausality
variable {R : Type*} [CommRing R]

 
def Agree (n : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ k, k ≤ n → PowerSeries.coeff k f = PowerSeries.coeff k g

theorem Agree.refl {n : ℕ} (f : PowerSeries R) : Agree n f f := fun _ _ => rfl

theorem Agree.mul {n : ℕ} {f f' g g' : PowerSeries R}
    (hf : Agree n f f') (hg : Agree n g g') : Agree n (f * g) (f' * g') := by
  intro k hk
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ab hab
  have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  rw [hf ab.1 (by omega), hg ab.2 (by omega)]

theorem Agree.pow {n : ℕ} {f g : PowerSeries R} (h : Agree n f g) (m : ℕ) :
    Agree n (f ^ m) (g ^ m) := by
  induction m with
  | zero => exact Agree.refl _
  | succ m ih => simpa only [pow_succ] using ih.mul h

theorem Agree.prod {n : ℕ} {ι : Type*} (s : Finset ι)
    {f g : ι → PowerSeries R} (h : ∀ i ∈ s, Agree n (f i) (g i)) :
    Agree n (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Agree.refl _
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem Agree.sum {n : ℕ} {ι : Type*} (s : Finset ι)
    {f g : ι → PowerSeries R} (h : ∀ i ∈ s, Agree n (f i) (g i)) :
    Agree n (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  intro k hk
  simp only [map_sum]
  exact Finset.sum_congr rfl (fun i hi => h i hi k hk)

 

theorem Agree.subst {n : ℕ} {σ : Type*} {a b : σ → PowerSeries R}
    (ha : MvPowerSeries.HasSubst a) (hb : MvPowerSeries.HasSubst b)
    (h : ∀ i, Agree n (a i) (b i)) (p : MvPowerSeries σ R) :
    Agree n (MvPowerSeries.subst a p) (MvPowerSeries.subst b p) := by
  intro k hk
  change MvPowerSeries.coeff (Finsupp.single () k) (MvPowerSeries.subst a p) =
    MvPowerSeries.coeff (Finsupp.single () k) (MvPowerSeries.subst b p)
  rw [MvPowerSeries.coeff_subst ha, MvPowerSeries.coeff_subst hb]
  apply finsum_congr
  intro d
  congr 1
  exact (Agree.prod d.support (fun i _ => (h i).pow (d i))) k hk

end PowerSeriesCausality

section FormalSystem
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {σ : Type*} [Fintype σ]

 
def series (f : ℕ → σ → A) (i : σ) : PowerSeries A :=
  PowerSeries.mk (fun n => f n i)

 
def tailSeries (f : ℕ → σ → A) (i : σ) : PowerSeries A :=
  PowerSeries.mk (fun n => if n = 0 then 0 else f n i)

omit [Algebra ℂ A] in
theorem tailSeries_hasSubst (f : ℕ → σ → A) :
    MvPowerSeries.HasSubst (tailSeries f) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro i
  change PowerSeries.constantCoeff (tailSeries f i) = 0
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [tailSeries]

 
def coefficientwise (δ : A →ₗ[ℂ] A) (F : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk (fun n => δ (PowerSeries.coeff n F))

 

def rhs (P : σ → σ → MvPowerSeries σ A) (δ : A →ₗ[ℂ] A)
    (f : ℕ → σ → A) (i : σ) : PowerSeries A :=
  ∑ j : σ, MvPowerSeries.subst (tailSeries f) (P i j) * coefficientwise δ (series f j)

def operator (P : σ → σ → MvPowerSeries σ A) (δ : A →ₗ[ℂ] A)
    (f : ℕ → σ → A) (n : ℕ) (i : σ) : A :=
  PowerSeries.coeff n (rhs P δ f i)

 
theorem operator_causal (P : σ → σ → MvPowerSeries σ A) (δ : A →ₗ[ℂ] A) :
    Causal (operator P δ) := by
  intro n f g h
  funext i
  apply Agree.sum Finset.univ (fun j _ => ?_) n le_rfl
  apply Agree.mul
  · apply Agree.subst (tailSeries_hasSubst f) (tailSeries_hasSubst g)
    intro j k hk
    simp [tailSeries, h k hk]
  · intro k hk
    simp [coefficientwise, series, h k hk]

 

theorem existsUnique_formalCoefficients
    (g : σ → A) (P : σ → σ → MvPowerSeries σ A) (δ : A →ₗ[ℂ] A) :
    ∃! f : ℕ → σ → A, f 0 = g ∧
      ∀ n : ℕ, (n + 1 : ℂ) • f (n + 1) = operator P δ f n :=
  existsUnique_coefficients g (operator P δ) (operator_causal P δ)

 

omit [Algebra ℂ A] [Fintype σ] in
theorem tailSeries_eq_sub (f : ℕ → σ → A) (i : σ) :
    tailSeries f i = series f i - PowerSeries.C (f 0 i) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp [tailSeries, series]
  · simp [tailSeries, series, PowerSeries.coeff_C, hn]

 
def IsSolution (g : σ → A) (P : σ → σ → MvPowerSeries σ A) (δ : A →ₗ[ℂ] A)
    (F : σ → PowerSeries A) : Prop :=
  (∀ i, PowerSeries.constantCoeff (F i) = g i) ∧
    ∀ i, PowerSeries.derivative (F i) =
      ∑ j : σ, MvPowerSeries.subst (fun k => F k - PowerSeries.C (g k)) (P i j) *
        coefficientwise δ (F j)

theorem isSolution_series_iff
    (g : σ → A) (P : σ → σ → MvPowerSeries σ A) (δ : A →ₗ[ℂ] A)
    (f : ℕ → σ → A) :
    IsSolution g P δ (series f) ↔
      f 0 = g ∧ ∀ n : ℕ, (n + 1 : ℂ) • f (n + 1) = operator P δ f n := by
  have hconst : (∀ i, PowerSeries.constantCoeff (series f i) = g i) ↔ f 0 = g := by
    simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply, series, PowerSeries.coeff_mk]
    exact funext_iff.symm
  constructor
  · intro hF
    have h0 := hconst.mp hF.1
    refine ⟨h0, ?_⟩
    have ht : tailSeries f = fun k => series f k - PowerSeries.C (g k) := by
      funext k
      rw [tailSeries_eq_sub, h0]
    intro n
    funext i
    have hder : PowerSeries.derivative (series f i) = rhs P δ f i := by
      simpa only [rhs, ht] using hF.2 i
    have hc := congrArg (PowerSeries.coeff n) hder
    simpa [PowerSeries.coeff_derivative, series, operator, Algebra.smul_def, mul_comm] using hc
  · rintro ⟨h0, hf⟩
    refine ⟨hconst.mpr h0, ?_⟩
    have ht : tailSeries f = fun k => series f k - PowerSeries.C (g k) := by
      funext k
      rw [tailSeries_eq_sub, h0]
    intro i
    have hder : PowerSeries.derivative (series f i) = rhs P δ f i := by
      ext n
      have hc := congrFun (hf n) i
      simpa [PowerSeries.coeff_derivative, series, operator, Algebra.smul_def, mul_comm] using hc
    simpa only [rhs, ht] using hder

 

theorem existsUnique_solution
    (g : σ → A) (P : σ → σ → MvPowerSeries σ A) (δ : A →ₗ[ℂ] A) :
    ∃! F : σ → PowerSeries A, IsSolution g P δ F := by
  obtain ⟨f, hf, huniq⟩ := existsUnique_formalCoefficients g P δ
  refine ⟨series f, (isSolution_series_iff g P δ f).mpr hf, ?_⟩
  intro F hF
  let fF : ℕ → σ → A := fun n i => PowerSeries.coeff n (F i)
  have he : series fF = F := by
    funext i
    ext n
    simp [series, fF]
  have hsol : IsSolution g P δ (series fF) := he.symm ▸ hF
  have heq := huniq fF ((isSolution_series_iff g P δ fF).mp hsol)
  exact he.symm.trans (congrArg series heq)

end FormalSystem

 

 

def analyticAlgebra (U : Set ℂ) : Subalgebra ℂ (ℂ → ℂ) where
  carrier := {f | AnalyticOnNhd ℂ f U}
  zero_mem' := analyticOnNhd_const
  one_mem' := analyticOnNhd_const
  add_mem' := fun hf hg => hf.add hg
  mul_mem' := fun hf hg => hf.mul hg
  algebraMap_mem' := fun _ => analyticOnNhd_const

abbrev AnalyticFunction (U : Set ℂ) := analyticAlgebra U

instance (U : Set ℂ) : CoeFun (AnalyticFunction U) (fun _ => ℂ → ℂ) := ⟨Subtype.val⟩

 

def analyticDerivative {U : Set ℂ} (hU : IsOpen U) :
    AnalyticFunction U →ₗ[ℂ] AnalyticFunction U := by
  classical
  exact {
  toFun f := ⟨fun z => if z ∈ U then deriv (f : ℂ → ℂ) z else 0, by
    apply AnalyticOnNhd.congr hU f.property.deriv
    intro z hz
    simp [hz]⟩
  map_add' f g := by
    apply Subtype.ext
    funext z
    change (if z ∈ U then deriv (fun w => f w + g w) z else 0) =
      (if z ∈ U then deriv (f : ℂ → ℂ) z else 0) +
        (if z ∈ U then deriv (g : ℂ → ℂ) z else 0)
    by_cases hz : z ∈ U
    · simp only [ite_eq_left hz]
      exact deriv_add (f.property z hz).differentiableAt (g.property z hz).differentiableAt
    · simp [hz]
  map_smul' c f := by
    apply Subtype.ext
    funext z
    change (if z ∈ U then deriv (fun w => c * f w) z else 0) =
      c * (if z ∈ U then deriv (f : ℂ → ℂ) z else 0)
    by_cases hz : z ∈ U
    · simp only [ite_eq_left hz]
      exact deriv_const_mul c (f.property z hz).differentiableAt
    · simp [hz] }

@[simp] theorem analyticDerivative_apply {U : Set ℂ} (hU : IsOpen U)
    (f : AnalyticFunction U) {z : ℂ} (hz : z ∈ U) :
    analyticDerivative hU f z = deriv (f : ℂ → ℂ) z := by
  simp [analyticDerivative, hz]

theorem analyticDerivative_mul {U : Set ℂ} (hU : IsOpen U)
    (f g : AnalyticFunction U) :
    analyticDerivative hU (f * g) =
      f * analyticDerivative hU g + g * analyticDerivative hU f := by
  classical
  apply Subtype.ext
  funext z
  change (if z ∈ U then deriv (fun w => f w * g w) z else 0) =
    f z * (if z ∈ U then deriv (g : ℂ → ℂ) z else 0) +
      g z * (if z ∈ U then deriv (f : ℂ → ℂ) z else 0)
  by_cases hz : z ∈ U
  · simp only [ite_eq_left hz]
    simpa only [Pi.mul_apply, mul_comm, add_comm] using
      deriv_fun_mul (f.property z hz).differentiableAt (g.property z hz).differentiableAt
  · simp [hz]

 

theorem existsUnique_holomorphic_solution {U : Set ℂ} (hU : IsOpen U)
    {σ : Type*} [Fintype σ]
    (g : σ → AnalyticFunction U)
    (P : σ → σ → MvPowerSeries σ (AnalyticFunction U)) :
    ∃! F : σ → PowerSeries (AnalyticFunction U),
      IsSolution g P (analyticDerivative hU) F :=
  existsUnique_solution g P (analyticDerivative hU)

 
def analyticEvaluation (U : Set ℂ) (z : ℂ) : AnalyticFunction U →+* ℂ :=
  (Pi.evalRingHom (fun _ : ℂ => ℂ) z).comp (analyticAlgebra U).val.toRingHom

@[simp] theorem analyticEvaluation_apply (U : Set ℂ) (z : ℂ) (f : AnalyticFunction U) :
    analyticEvaluation U z f = f z := rfl

 

theorem analyticDerivative_eqOn {U U' W : Set ℂ} (hU : IsOpen U) (hU' : IsOpen U')
    (hW : IsOpen W) (hWU : W ⊆ U) (hWU' : W ⊆ U')
    {f : AnalyticFunction U} {g : AnalyticFunction U'}
    (hfg : EqOn (f : ℂ → ℂ) (g : ℂ → ℂ) W) :
    EqOn (analyticDerivative hU f : ℂ → ℂ) (analyticDerivative hU' g : ℂ → ℂ) W := by
  intro z hz
  rw [analyticDerivative_apply hU f (hWU hz), analyticDerivative_apply hU' g (hWU' hz)]
  have he : (f : ℂ → ℂ) =ᶠ[nhds z] (g : ℂ → ℂ) :=
    Filter.mem_of_superset (hW.mem_nhds hz) (fun w hw => hfg hw)
  exact he.deriv_eq

 

theorem operator_eqOn {U U' W : Set ℂ} (hU : IsOpen U) (hU' : IsOpen U')
    (hW : IsOpen W) (hWU : W ⊆ U) (hWU' : W ⊆ U')
    {σ : Type*} [Fintype σ]
    (P : σ → σ → MvPowerSeries σ (AnalyticFunction U))
    (P' : σ → σ → MvPowerSeries σ (AnalyticFunction U'))
    (hP : ∀ i j d, EqOn
      (MvPowerSeries.coeff d (P i j)).val
      (MvPowerSeries.coeff d (P' i j)).val W)
    (n : ℕ) (f : ℕ → σ → AnalyticFunction U) (f' : ℕ → σ → AnalyticFunction U')
    (hf : ∀ k, k ≤ n → ∀ i, EqOn (f k i : ℂ → ℂ) (f' k i : ℂ → ℂ) W) (i : σ) :
    EqOn (operator P (analyticDerivative hU) f n i).val
      (operator P' (analyticDerivative hU') f' n i).val W := by
  intro z hz
  let e := analyticEvaluation U z
  let e' := analyticEvaluation U' z
  have hp (i j : σ) : MvPowerSeries.map e (P i j) = MvPowerSeries.map e' (P' i j) := by
    ext d
    exact hP i j d hz
  change e (PowerSeries.coeff n (rhs P (analyticDerivative hU) f i)) =
    e' (PowerSeries.coeff n (rhs P' (analyticDerivative hU') f' i))
  rw [← PowerSeries.coeff_map, ← PowerSeries.coeff_map]
  simp only [rhs, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro j _
  refine Agree.mul (n := n) ?_ ?_ n le_rfl
  · rw [show PowerSeries.map e (MvPowerSeries.subst (tailSeries f) (P i j)) =
        MvPowerSeries.subst (fun k => PowerSeries.map e (tailSeries f k))
          (MvPowerSeries.map e (P i j)) from
        MvPowerSeries.map_subst (tailSeries_hasSubst f) (P i j)]
    rw [show PowerSeries.map e' (MvPowerSeries.subst (tailSeries f') (P' i j)) =
        MvPowerSeries.subst (fun k => PowerSeries.map e' (tailSeries f' k))
          (MvPowerSeries.map e' (P' i j)) from
        MvPowerSeries.map_subst (tailSeries_hasSubst f') (P' i j), hp]
    apply Agree.subst ((tailSeries_hasSubst f).map e) ((tailSeries_hasSubst f').map e')
    intro k l hl
    change e (PowerSeries.coeff l (tailSeries f k)) =
      e' (PowerSeries.coeff l (tailSeries f' k))
    simp only [tailSeries, PowerSeries.coeff_mk]
    by_cases hl0 : l = 0
    · simp [hl0]
    · simpa [hl0, e, e'] using hf l hl k hz
  · intro l hl
    simp only [PowerSeries.coeff_map, coefficientwise, PowerSeries.coeff_mk,
      series]
    exact analyticDerivative_eqOn hU hU' hW hWU hWU' (hf l hl j) hz

 

theorem holomorphic_coefficients_eqOn {U U' W : Set ℂ} (hU : IsOpen U) (hU' : IsOpen U')
    (hW : IsOpen W) (hWU : W ⊆ U) (hWU' : W ⊆ U')
    {σ : Type*} [Fintype σ]
    (g : σ → AnalyticFunction U) (g' : σ → AnalyticFunction U')
    (hg : ∀ i, EqOn (g i : ℂ → ℂ) (g' i : ℂ → ℂ) W)
    (P : σ → σ → MvPowerSeries σ (AnalyticFunction U))
    (P' : σ → σ → MvPowerSeries σ (AnalyticFunction U'))
    (hP : ∀ i j d, EqOn
      (MvPowerSeries.coeff d (P i j)).val
      (MvPowerSeries.coeff d (P' i j)).val W) :
    ∀ n i, EqOn
      (coefficients g (operator P (analyticDerivative hU)) n i).val
      (coefficients g' (operator P' (analyticDerivative hU')) n i).val W := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa using hg
    | succ n =>
      intro i z hz
      have heq := operator_eqOn hU hU' hW hWU hWU' P P' hP n
        (coefficients g (operator P (analyticDerivative hU)))
        (coefficients g' (operator P' (analyticDerivative hU')))
        (fun k hk j => ih k (Nat.lt_succ_of_le hk) j) i hz
      have hu := coefficients_succ g _ (operator_causal P (analyticDerivative hU)) n
      have hu' := coefficients_succ g' _ (operator_causal P' (analyticDerivative hU')) n
      have huval := congrArg (fun a : σ → AnalyticFunction U => a i z) hu
      have huval' := congrArg (fun a : σ → AnalyticFunction U' => a i z) hu'
      have hmul : (n + 1 : ℂ) *
          coefficients g (operator P (analyticDerivative hU)) (n + 1) i z =
          (n + 1 : ℂ) *
          coefficients g' (operator P' (analyticDerivative hU')) (n + 1) i z :=
        huval.trans (heq.trans huval'.symm)
      exact mul_left_cancel₀ (by exact_mod_cast Nat.succ_ne_zero n : (n + 1 : ℂ) ≠ 0) hmul

open scoped MvPowerSeries.WithPiTopology

section
variable {R σ τ : Type*} [CommRing R] [Fintype σ]

theorem polynomial_chain_rule (a : σ → MvPowerSeries τ R) (i : τ)
    (p : MvPolynomial σ R) :
    MvPowerSeries.pderiv i (MvPolynomial.aeval a p) =
      ∑ j : σ, MvPolynomial.aeval a (MvPolynomial.pderiv j p) *
        MvPowerSeries.pderiv i (a j) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.aeval_X, Derivation.leibniz, smul_eq_mul,
      map_add, MvPolynomial.pderiv_X, apply_ite, map_one, map_zero, Pi.single_apply]
    rw [hp]
    simp [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_comm, mul_assoc]

section Topology
variable [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_formal_pderiv (i : τ) :
    Continuous (MvPowerSeries.pderiv i : MvPowerSeries τ R → MvPowerSeries τ R) := by
  apply continuous_pi
  intro d
  change Continuous (fun p : MvPowerSeries τ R =>
    MvPowerSeries.coeff d (MvPowerSeries.pderiv i p))
  simp_rw [MvPowerSeries.coeff_pderiv]
  exact (MvPowerSeries.WithPiTopology.continuous_coeff R _).mul continuous_const

end Topology

 

theorem formal_chain_rule (a : σ → MvPowerSeries τ R) (ha : MvPowerSeries.HasSubst a)
    (i : τ) (p : MvPowerSeries σ R) :
    MvPowerSeries.pderiv i (MvPowerSeries.subst a p) =
      ∑ j : σ, MvPowerSeries.subst a (MvPowerSeries.pderiv j p) *
        MvPowerSeries.pderiv i (a j) := by
  let : UniformSpace R := ⊥
  have hleft : Continuous (fun p : MvPowerSeries σ R =>
      MvPowerSeries.pderiv i (MvPowerSeries.subst a p)) :=
    (continuous_formal_pderiv i).comp (MvPowerSeries.continuous_subst ha)
  have hright : Continuous (fun p : MvPowerSeries σ R =>
      ∑ j : σ, MvPowerSeries.subst a (MvPowerSeries.pderiv j p) *
        MvPowerSeries.pderiv i (a j)) := by
    apply continuous_finsetSum
    intro j _
    exact ((MvPowerSeries.continuous_subst ha).comp
      (continuous_formal_pderiv j)).mul continuous_const
  have heq := MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries.equalizer hleft hright
    (show _ = _ from funext fun q => by
      simpa only [Function.comp_apply, MvPowerSeries.pderiv_coe, MvPowerSeries.subst_coe] using
        polynomial_chain_rule a i q)
  exact congrFun heq p

end

variable {R A σ : Type*} [CommRing R] [CommRing A] [Algebra R A]

 

def deriveCoefficients (δ : Derivation R A A) (f : MvPowerSeries σ A) : MvPowerSeries σ A :=
  fun d => δ (MvPowerSeries.coeff d f)

@[simp] theorem coeff_deriveCoefficients (δ : Derivation R A A) (f : MvPowerSeries σ A)
    (d : σ →₀ ℕ) : MvPowerSeries.coeff d (deriveCoefficients δ f) = δ (MvPowerSeries.coeff d f) := rfl

def coefficientDerivation (δ : Derivation R A A) :
    Derivation R (MvPowerSeries σ A) (MvPowerSeries σ A) where
  toFun := deriveCoefficients δ
  map_add' f g := by ext d; simp
  map_smul' r f := by
    ext d
    change δ (r • MvPowerSeries.coeff d f) = r • δ (MvPowerSeries.coeff d f)
    exact δ.map_smul r (MvPowerSeries.coeff d f)
  map_one_eq_zero' := by
    classical
    ext d
    simp [MvPowerSeries.coeff_one, apply_ite]
  leibniz' f g := by
    classical
    change deriveCoefficients δ (f * g) = f * deriveCoefficients δ g + g * deriveCoefficients δ f
    rw [mul_comm g]
    ext d
    simp only [coeff_deriveCoefficients, map_add, MvPowerSeries.coeff_mul, map_sum,
      Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
    apply congrArg₂ (· + ·)
    · rfl
    · apply Finset.sum_congr rfl
      intro x hx
      ring

@[simp] theorem coefficientDerivation_apply (δ : Derivation R A A)
    (f : MvPowerSeries σ A) : coefficientDerivation δ f = deriveCoefficients δ f := rfl

@[simp] theorem deriveCoefficients_C (δ : Derivation R A A) (a : A) :
    deriveCoefficients (σ := σ) δ (MvPowerSeries.C a) = MvPowerSeries.C (δ a) := by
  classical
  ext d
  by_cases hd : d = 0
  · subst d; simp
  · simp [MvPowerSeries.coeff_C, hd]

@[simp] theorem deriveCoefficients_X (δ : Derivation R A A) (i : σ) :
    deriveCoefficients δ (MvPowerSeries.X i) = 0 := by
  classical
  ext d
  simp [MvPowerSeries.coeff_X, apply_ite]

theorem deriveCoefficients_add (δ : Derivation R A A) (f g : MvPowerSeries σ A) :
    deriveCoefficients δ (f + g) = deriveCoefficients δ f + deriveCoefficients δ g :=
  (coefficientDerivation δ).map_add f g

theorem deriveCoefficients_mul (δ : Derivation R A A) (f g : MvPowerSeries σ A) :
    deriveCoefficients δ (f * g) =
      f * deriveCoefficients δ g + g * deriveCoefficients δ f :=
  (coefficientDerivation δ).leibniz f g

section Topology
variable [TopologicalSpace A] [IsTopologicalRing A]

omit [IsTopologicalRing A] in
theorem continuous_deriveCoefficients (δ : Derivation R A A) (hδ : Continuous δ) :
    Continuous (deriveCoefficients (σ := σ) δ) := by
  apply continuous_pi
  intro d
  exact hδ.comp (MvPowerSeries.WithPiTopology.continuous_coeff A d)

end Topology
variable {τ : Type*} [Fintype σ]

theorem polynomial_coefficient_chain_rule (δ : Derivation R A A)
    (a : σ → MvPowerSeries τ A) (ha : MvPowerSeries.HasSubst a)
    (p : MvPolynomial σ A) :
    deriveCoefficients δ (MvPowerSeries.subst a (p : MvPowerSeries σ A)) =
      MvPowerSeries.subst a (deriveCoefficients δ (p : MvPowerSeries σ A)) +
        ∑ j : σ, MvPowerSeries.subst a (MvPowerSeries.pderiv j (p : MvPowerSeries σ A)) *
          deriveCoefficients δ (a j) := by
  classical
  have hz : MvPowerSeries.subst a (0 : MvPowerSeries σ A) = 0 := by
    simpa using (MvPowerSeries.substAlgHom ha).map_zero
  have h1 : MvPowerSeries.subst a (1 : MvPowerSeries σ A) = 1 := by
    simpa using (MvPowerSeries.substAlgHom ha).map_one
  induction p using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.coe_C, hz]
  | add p q hp hq =>
    simp only [MvPolynomial.coe_add, MvPowerSeries.subst_add ha, deriveCoefficients_add,
      map_add, add_mul, Finset.sum_add_distrib] at *
    rw [hp, hq]
    ring
  | mul_X p x hp =>
    simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, deriveCoefficients_mul, deriveCoefficients_X,
      mul_zero, zero_add, Derivation.leibniz, smul_eq_mul, MvPowerSeries.pderiv_X, MvPowerSeries.subst_add ha, MvPowerSeries.subst_mul ha,
      MvPowerSeries.subst_X ha, hz, h1,
      apply_ite, Pi.single_apply]
    rw [hp]
    simp [mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_comm, mul_left_comm, add_left_comm]

 

theorem formal_coefficient_chain_rule (δ : Derivation R A A)
    (a : σ → MvPowerSeries τ A) (ha : MvPowerSeries.HasSubst a)
    (p : MvPowerSeries σ A) :
    deriveCoefficients δ (MvPowerSeries.subst a p) =
      MvPowerSeries.subst a (deriveCoefficients δ p) +
        ∑ j : σ, MvPowerSeries.subst a (MvPowerSeries.pderiv j p) *
          deriveCoefficients δ (a j) := by
  let : UniformSpace A := ⊥
  have hδ : Continuous δ := continuous_of_discreteTopology
  have hleft : Continuous (fun p : MvPowerSeries σ A =>
      deriveCoefficients δ (MvPowerSeries.subst a p)) :=
    (continuous_deriveCoefficients δ hδ).comp (MvPowerSeries.continuous_subst ha)
  have hright : Continuous (fun p : MvPowerSeries σ A =>
      MvPowerSeries.subst a (deriveCoefficients δ p) +
        ∑ j : σ, MvPowerSeries.subst a (MvPowerSeries.pderiv j p) *
          deriveCoefficients δ (a j)) := by
    apply Continuous.add
    · exact (MvPowerSeries.continuous_subst ha).comp (continuous_deriveCoefficients δ hδ)
    · apply continuous_finsetSum
      intro j _
      exact ((MvPowerSeries.continuous_subst ha).comp
        (continuous_formal_pderiv j)).mul continuous_const
  have heq := MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries.equalizer hleft hright
    (show _ = _ from funext fun q => polynomial_coefficient_chain_rule δ a ha q)
  exact congrFun heq p



end FormalCauchy
end SplitTangent
section ReconstructionImports

open Set Filter Topology
namespace SplitTangent.DiagonalRationality

 

theorem iteratedDeriv_zero_of_growth {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {n : ℕ} {C : ℝ} (hbound : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ n)
    {k : ℕ} (hk : n < k) : iteratedDeriv k f 0 = 0 := by
  have hb : ∀ R : ℝ, 1 ≤ R →
      ‖iteratedDeriv k f 0‖ ≤ (k.factorial : ℝ) * C / R ^ (k - n) := by
    intro R hR
    have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0) k hR0
      hf.diffContOnCl (fun z hz => by
        have hzR : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_zero_right] using hz
        simpa only [hzR] using hbound z (hzR ▸ hR))
    convert h using 1
    rw [pow_sub₀ R hR0.ne' hk.le]
    field_simp
  apply norm_le_zero_iff.mp
  apply ge_of_tendsto (show Tendsto (fun R : ℝ => (k.factorial : ℝ) * C / R ^ (k - n))
      atTop (nhds 0) from tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega)))
  exact (eventually_ge_atTop 1).mono (fun R hR => hb R hR)

 
def taylorPolynomial (f : ℂ → ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.monomial k ((k.factorial : ℂ)⁻¹ * iteratedDeriv k f 0)

theorem eq_taylorPolynomial_of_growth {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {n : ℕ} {C : ℝ} (hbound : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ n)
    (z : ℂ) : f z = (taylorPolynomial f n).eval z := by
  rw [← Complex.taylorSeries_eq_of_entire' 0 z hf]
  rw [tsum_eq_sum (s := Finset.range (n + 1)) (fun k hk => by
    have hnk : n < k := by simpa using hk
    rw [iteratedDeriv_zero_of_growth hf hbound hnk]
    simp)]
  simp [taylorPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem degree_taylorPolynomial (f : ℂ → ℂ) (n : ℕ) :
    (taylorPolynomial f n).degree < (n + 1 : ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro k hk
  simp only [taylorPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro i hi
  have hik : i ≠ k := by
    have hi' := Finset.mem_range.mp hi
    omega
  simp [hik]

 

def lineSections (d : ℤ) : Submodule ℂ ((ℂ → ℂ) × (ℂ → ℂ)) where
  carrier := {fg | Differentiable ℂ fg.1 ∧ Differentiable ℂ fg.2 ∧
    ∀ z : ℂ, z ≠ 0 → fg.1 z = z ^ d * fg.2 z⁻¹}
  zero_mem' := by simp
  add_mem' := by
    rintro f g ⟨hf,hf',htf⟩ ⟨hg,hg',htg⟩
    refine ⟨hf.add hg, hf'.add hg', ?_⟩
    intro z hz
    change f.1 z + g.1 z = z ^ d * (f.2 z⁻¹ + g.2 z⁻¹)
    rw [htf z hz, htg z hz, mul_add]
  smul_mem' := by
    rintro c f ⟨hf,hf',htf⟩
    refine ⟨hf.const_mul c, hf'.const_mul c, ?_⟩
    intro z hz
    change c * f.1 z = z ^ d * (c * f.2 z⁻¹)
    rw [htf z hz]
    ring

 
theorem lineSections_growth {d : ℤ} (s : lineSections d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 1 ≤ ‖z‖ → ‖s.val.1 z‖ ≤ C * ‖z‖ ^ d := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ℂ) 1).image s.property.2.1.continuous).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hz
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; norm_num at hz
  rw [s.property.2.2 z hz0, norm_mul, norm_zpow]
  rw [mul_comm (max C 0)]
  apply mul_le_mul_of_nonneg_left _ (zpow_nonneg (norm_nonneg _) _)
  apply (hC _ ?_).trans (le_max_left _ _)
  refine ⟨z⁻¹, ?_, rfl⟩
  simp only [Metric.mem_closedBall, dist_zero_right, norm_inv]
  exact inv_le_one_of_one_le₀ hz

 
theorem lineSections_ext {d : ℤ} {s t : lineSections d}
    (h : s.val.1 = t.val.1) : s = t := by
  apply Subtype.ext
  apply Prod.ext h
  apply Continuous.ext_on (dense_compl_singleton (0 : ℂ))
    s.property.2.1.continuous t.property.2.1.continuous
  intro z hz
  have hz0 : z ≠ 0 := hz
  have hs := s.property.2.2 z⁻¹ (inv_ne_zero hz0)
  have ht := t.property.2.2 z⁻¹ (inv_ne_zero hz0)
  simp only [inv_inv] at hs ht
  have he : (z⁻¹) ^ d * s.val.2 z = (z⁻¹) ^ d * t.val.2 z := by
    rw [← hs, ← ht, h]
  exact mul_left_cancel₀ (zpow_ne_zero _ (inv_ne_zero hz0)) he

 
theorem lineSections_eq_zero_of_neg {d : ℤ} (hd : d < 0) (s : lineSections d) : s = 0 := by
  obtain ⟨C, hC, hb⟩ := lineSections_growth s
  have hb0 : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖s.val.1 z‖ ≤ C * ‖z‖ ^ (0 : ℕ) := by
    intro z hz
    simpa using (hb z hz).trans (mul_le_mul_of_nonneg_left
      (zpow_le_one_of_nonpos₀ hz hd.le) hC)
  have hc : ∀ z : ℂ, s.val.1 z = s.val.1 0 := by
    intro z
    simpa [taylorPolynomial, Polynomial.eval_monomial] using
      eq_taylorPolynomial_of_growth s.property.1 hb0 z
  have hzero : s.val.1 0 = 0 := by
    apply norm_le_zero_iff.mp
    apply ge_of_tendsto (show Tendsto (fun R : ℝ => C * R ^ d) atTop (nhds 0) by
      simpa using (tendsto_zpow_atTop_zero hd).const_mul C)
    apply (eventually_ge_atTop (1 : ℝ)).mono
    intro R hR
    have hnorm : ‖(R : ℂ)‖ = R := by simp [abs_of_nonneg (by linarith : 0 ≤ R)]
    have hh := hb (R : ℂ) (by rw [hnorm]; exact hR)
    simpa only [hnorm, hc] using hh
  apply lineSections_ext
  funext z
  exact (hc z).trans hzero

 
def sectionJet (d : ℤ) (n : ℕ) : lineSections d →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun s i := iteratedDeriv i.val s.val.1 0
  map_add' s t := by
    funext i
    exact iteratedDeriv_add s.property.1.contDiff.contDiffAt t.property.1.contDiff.contDiffAt
  map_smul' c s := by
    funext i
    exact iteratedDeriv_const_mul_field c s.val.1

theorem sectionJet_injective (n : ℕ) : Function.Injective (sectionJet (n : ℤ) n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro s hs
  obtain ⟨C, hC, hb⟩ := lineSections_growth s
  have hb' : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖s.val.1 z‖ ≤ C * ‖z‖ ^ n := by
    simpa only [zpow_natCast] using hb
  apply lineSections_ext
  funext z
  rw [eq_taylorPolynomial_of_growth s.property.1 hb' z]
  simp only [taylorPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  apply Finset.sum_eq_zero
  intro k hk
  have hc : iteratedDeriv k s.val.1 0 = 0 := congrFun hs ⟨k, Finset.mem_range.mp hk⟩
  simp [hc]

instance lineSections_finite (d : ℤ) : Module.Finite ℂ (lineSections d) := by
  by_cases hd : 0 ≤ d
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hd
    exact Module.Finite.of_injective (sectionJet (n : ℤ) n) (sectionJet_injective n)
  · have : Subsingleton (lineSections d) := ⟨fun s t =>
      (lineSections_eq_zero_of_neg (lt_of_not_ge hd) s).trans
        (lineSections_eq_zero_of_neg (lt_of_not_ge hd) t).symm⟩
    infer_instance

theorem finrank_lineSections_le (d : ℤ) :
    Module.finrank ℂ (lineSections d) ≤ (d + 1).toNat := by
  by_cases hd : 0 ≤ d
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hd
    simpa using LinearMap.finrank_le_finrank_of_injective (sectionJet_injective n)
  · have : Subsingleton (lineSections d) := ⟨fun s t =>
      (lineSections_eq_zero_of_neg (lt_of_not_ge hd) s).trans
        (lineSections_eq_zero_of_neg (lt_of_not_ge hd) t).symm⟩
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _

open PowerSeries

 

def reciprocalNormal (z : ℂ) : PowerSeries ℂ :=
  (C z + X)⁻¹ - C z⁻¹

@[simp] theorem reciprocalNormal_constant (z : ℂ) :
    constantCoeff (reciprocalNormal z) = 0 := by
  simp [reciprocalNormal]

theorem reciprocalNormal_hasSubst (z : ℂ) : HasSubst (reciprocalNormal z) :=
  HasSubst.of_constantCoeff_zero' (reciprocalNormal_constant z)

@[simp] theorem reciprocalNormal_linear (z : ℂ) :
    coeff 1 (reciprocalNormal z) = -(z⁻¹ ^ 2) := by
  rw [reciprocalNormal, map_sub, coeff_C]
  norm_num only [show (1 : ℕ) ≠ 0 by decide, ite_false, sub_zero]
  rw [coeff_inv]
  simp [Finset.Nat.antidiagonal_succ,
    PowerSeries.coeff_X, PowerSeries.coeff_C, coeff_zero_eq_constantCoeff, pow_two]

theorem constant_subst {b f : PowerSeries ℂ} (hb : constantCoeff b = 0) :
    constantCoeff (subst b f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff, coeff_subst' (HasSubst.of_constantCoeff_zero' hb)]
  rw [finsum_eq_single _ 0]
  · simp [coeff_zero_eq_constantCoeff]
  · intro i hi
    simp [coeff_zero_eq_constantCoeff, hb, hi]

 
theorem leading_subst {k : ℕ} {b f T : PowerSeries ℂ}
    (hb : constantCoeff b = 0) (hf : ∀ j < k, coeff j f = 0) :
    coeff k (T * subst b f) = constantCoeff T * coeff 1 b ^ k * coeff k f := by
  obtain ⟨g, rfl⟩ := (X_pow_dvd_iff.mpr hf)
  obtain ⟨c, hc⟩ := (X_dvd_iff.mpr hb)
  have hbs : HasSubst b := HasSubst.of_constantCoeff_zero' hb
  rw [PowerSeries.subst_mul hbs, PowerSeries.subst_pow hbs, PowerSeries.subst_X hbs]
  rw [hc, mul_pow]
  have he : T * (X ^ k * c ^ k * subst (X * c) g) =
      X ^ k * (T * c ^ k * subst (X * c) g) := by ring
  rw [he, coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self]
  simp only [coeff_zero_eq_constantCoeff, map_mul, map_pow]
  rw [constant_subst (by simp)]
  have hc1 : coeff 1 (X * c) = constantCoeff c := by
    simp
  rw [hc1, coeff_X_pow_mul']
  simp [coeff_zero_eq_constantCoeff]

 
def evaluateCoefficients (z : ℂ) : PowerSeries (ℂ → ℂ) →ₐ[ℂ] PowerSeries ℂ :=
  PowerSeries.mapAlgHom (Pi.evalAlgHom ℂ (fun _ : ℂ => ℂ) z)

@[simp] theorem coeff_evaluateCoefficients (z : ℂ) (f : PowerSeries (ℂ → ℂ)) (k : ℕ) :
    coeff k (evaluateCoefficients z f) = coeff k f z := rfl

 

def formalSections (T : ℂ → PowerSeries ℂ) :
    Submodule ℂ (PowerSeries (ℂ → ℂ) × PowerSeries (ℂ → ℂ)) where
  carrier := {fg | (∀ k, Differentiable ℂ (coeff k fg.1)) ∧
    (∀ k, Differentiable ℂ (coeff k fg.2)) ∧
    ∀ z : ℂ, z ≠ 0 → evaluateCoefficients z fg.1 =
      T z * subst (reciprocalNormal z) (evaluateCoefficients z⁻¹ fg.2)}
  zero_mem' := by
    refine ⟨fun k => by simp, fun k => by simp, ?_⟩
    intro z hz
    simp [← coe_substAlgHom (reciprocalNormal_hasSubst z)]
  add_mem' := by
    rintro f g ⟨hf, hf', hfg⟩ ⟨hg, hg', hgg⟩
    refine ⟨fun k => (hf k).add (hg k), fun k => (hf' k).add (hg' k), ?_⟩
    intro z hz
    change evaluateCoefficients z (f.1 + g.1) =
      T z * subst (reciprocalNormal z) (evaluateCoefficients z⁻¹ (f.2 + g.2))
    rw [map_add, map_add, subst_add (reciprocalNormal_hasSubst z), mul_add,
      hfg z hz, hgg z hz]
  smul_mem' := by
    rintro c f ⟨hf, hf', hfg⟩
    refine ⟨fun k => ?_, fun k => ?_, ?_⟩
    · change Differentiable ℂ (coeff k (c • f.1))
      rw [coeff_smul]
      exact (hf k).const_smul c
    · change Differentiable ℂ (coeff k (c • f.2))
      rw [coeff_smul]
      exact (hf' k).const_smul c
    · intro z hz
      change evaluateCoefficients z (c • f.1) =
        T z * subst (reciprocalNormal z) (evaluateCoefficients z⁻¹ (c • f.2))
      rw [map_smul, map_smul, subst_smul (reciprocalNormal_hasSubst z), hfg z hz,
        mul_smul_comm]

 
def orderFiltration (T : ℂ → PowerSeries ℂ) (k : ℕ) : Submodule ℂ (formalSections T) where
  carrier := {s | ∀ j < k, coeff j s.val.1 = 0 ∧ coeff j s.val.2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro s t hs ht j hj
    have hs' := hs j hj
    have ht' := ht j hj
    simpa using And.intro (congrArg₂ (· + ·) hs'.1 ht'.1) (congrArg₂ (· + ·) hs'.2 ht'.2)
  smul_mem' := by
    intro c s hs j hj
    obtain ⟨h1,h2⟩ := hs j hj
    constructor <;> simp [h1,h2]

 
def leadingSection {T : ℂ → PowerSeries ℂ} {d : ℤ}
    (hT : ∀ z : ℂ, z ≠ 0 → constantCoeff (T z) = z ^ d) (k : ℕ) :
    orderFiltration T k →ₗ[ℂ] lineSections (d - 2 * (k : ℤ)) where
  toFun s := ⟨(coeff k s.val.val.1, fun z => (-1 : ℂ) ^ k * coeff k s.val.val.2 z),
    s.val.property.1 k, (s.val.property.2.1 k).const_mul _, by
      intro z hz
      have he := congrArg (coeff k) (s.val.property.2.2 z hz)
      rw [leading_subst (reciprocalNormal_constant z) (fun j hj => by
          simp only [coeff_evaluateCoefficients]
          exact congrFun (s.property j hj).2 z⁻¹), hT z hz,
        reciprocalNormal_linear, coeff_evaluateCoefficients, coeff_evaluateCoefficients] at he
      change coeff k s.val.val.1 z = z ^ (d - 2 * (k : ℤ)) *
        ((-1 : ℂ) ^ k * coeff k s.val.val.2 z⁻¹)
      rw [he, neg_pow, zpow_sub₀ hz, zpow_mul, zpow_natCast]
      simp only [zpow_ofNat, inv_pow, div_eq_mul_inv]
      ring⟩
  map_add' s t := by
    apply Subtype.ext
    ext z <;> simp [mul_add]
  map_smul' c s := by
    apply Subtype.ext
    ext z <;> simp [mul_left_comm]

theorem leadingSection_eq_zero_iff {T : ℂ → PowerSeries ℂ} {d : ℤ}
    (hT : ∀ z : ℂ, z ≠ 0 → constantCoeff (T z) = z ^ d) (k : ℕ)
    (s : orderFiltration T k) :
    leadingSection hT k s = 0 ↔ coeff k s.val.val.1 = 0 ∧ coeff k s.val.val.2 = 0 := by
  constructor
  · intro h
    have he := congrArg Subtype.val h
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    refine ⟨h1, ?_⟩
    funext z
    have hz : (-1 : ℂ) ^ k * coeff k s.val.val.2 z = 0 := congrFun h2 z
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  · rintro ⟨h1,h2⟩
    apply Subtype.ext
    ext z <;> simp [leadingSection, h1, h2]

 
def leadingKernelEquiv {T : ℂ → PowerSeries ℂ} {d : ℤ}
    (hT : ∀ z : ℂ, z ≠ 0 → constantCoeff (T z) = z ^ d) (k : ℕ) :
    LinearMap.ker (leadingSection hT k) ≃ₗ[ℂ] orderFiltration T (k+1) where
  toFun s := ⟨s.val.val, fun j hj => by
    by_cases hjk : j < k
    · exact s.val.property j hjk
    · have hjk' : j = k := by omega
      subst j
      exact (leadingSection_eq_zero_iff hT k s.val).mp s.property⟩
  invFun s := ⟨⟨s.val, fun j hj => s.property j (by omega)⟩,
    (leadingSection_eq_zero_iff hT k _).mpr (s.property k (by omega))⟩
  left_inv s := rfl
  right_inv s := rfl
  map_add' s t := rfl
  map_smul' c s := rfl

 
theorem orderFiltration_eq_zero {T : ℂ → PowerSeries ℂ} {d : ℤ}
    (hT : ∀ z : ℂ, z ≠ 0 → constantCoeff (T z) = z ^ d) {k : ℕ}
    (hk : d - 2 * (k : ℤ) < 0) (s : orderFiltration T k) : s = 0 := by
  have hcoeff : ∀ n, coeff n s.val.val.1 = 0 ∧ coeff n s.val.val.2 = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hnk : n < k
      · exact s.property n hnk
      · let t : orderFiltration T n := ⟨s.val, fun j hj => ih j hj⟩
        have ht := lineSections_eq_zero_of_neg (d := d - 2 * (n : ℤ)) (by omega)
          (leadingSection hT n t)
        exact (leadingSection_eq_zero_iff hT n t).mp ht
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact PowerSeries.ext (fun n => (hcoeff n).1)
  · exact PowerSeries.ext (fun n => (hcoeff n).2)

theorem finite_of_kernel {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
    (f : V →ₗ[ℂ] W) [Module.Finite ℂ (LinearMap.ker f)] : Module.Finite ℂ V := by
  have : Module.Finite ℂ (V ⧸ LinearMap.ker f) :=
    Module.Finite.of_injective f.quotKerEquivRange.toLinearMap f.quotKerEquivRange.injective
  exact Module.Finite.of_submodule_quotient (LinearMap.ker f)

 

theorem filtration_dimension_bound {T : ℂ → PowerSeries ℂ} {d : ℤ}
    (hT : ∀ z : ℂ, z ≠ 0 → constantCoeff (T z) = z ^ d) (N k : ℕ)
    (hN : d - 2 * ((k+N : ℕ) : ℤ) < 0) :
    Module.Finite ℂ (orderFiltration T k) ∧
      Module.finrank ℂ (orderFiltration T k) ≤
        ∑ j ∈ Finset.range N, (d - 2 * ((k+j : ℕ) : ℤ) + 1).toNat := by
  induction N generalizing k with
  | zero =>
    have : Subsingleton (orderFiltration T k) := ⟨fun s t =>
      (orderFiltration_eq_zero hT (by simpa using hN) s).trans
        (orderFiltration_eq_zero hT (by simpa using hN) t).symm⟩
    exact ⟨inferInstance, by simp [Module.finrank_zero_of_subsingleton]⟩
  | succ N ih =>
    have hn : d - 2 * ((k+1+N : ℕ) : ℤ) < 0 := by convert hN using 1; omega
    obtain ⟨hfinite, hbound⟩ := ih (k+1) hn
    have : Module.Finite ℂ (orderFiltration T (k+1)) := hfinite
    have : Module.Finite ℂ (LinearMap.ker (leadingSection hT k)) :=
      Module.Finite.equiv (leadingKernelEquiv hT k).symm
    have : Module.Finite ℂ (orderFiltration T k) := finite_of_kernel (V := orderFiltration T k) (W := lineSections (d - 2 * (k : ℤ))) (leadingSection hT k)
    refine ⟨inferInstance, ?_⟩
    have hrank := LinearMap.finrank_range_add_finrank_ker (K := ℂ)
      (V := orderFiltration T k) (V₂ := lineSections (d - 2 * (k : ℤ))) (leadingSection hT k)
    have hrange := (LinearMap.range (leadingSection hT k)).finrank_le
    have hline := finrank_lineSections_le (d - 2 * (k : ℤ))
    have hker := (leadingKernelEquiv hT k).finrank_eq
    rw [Finset.sum_range_succ']
    have hshift : (∑ j ∈ Finset.range N, (d - 2 * ((k+(j+1) : ℕ) : ℤ) + 1).toNat) =
        ∑ j ∈ Finset.range N, (d - 2 * ((k+1+j : ℕ) : ℤ) + 1).toNat := by
      apply Finset.sum_congr rfl
      intro j hj
      congr 2
      omega
    rw [hshift]
    simp only [Nat.add_zero]
    omega

def zeroFiltrationEquiv (T : ℂ → PowerSeries ℂ) :
    orderFiltration T 0 ≃ₗ[ℂ] formalSections T where
  toFun := Subtype.val
  invFun s := ⟨s, by simp [orderFiltration]⟩
  left_inv s := rfl
  right_inv s := rfl
  map_add' s t := rfl
  map_smul' c s := rfl

theorem sum_descending_odds (N : ℕ) :
    ∑ j ∈ Finset.range N, (2 * (N-j) - 1) = N ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero]
    rw [ih]
    have h : 2 * (N+1) - 1 = 2*N+1 := by omega
    rw [h]
    ring

 

theorem formalSections_dimension_bound {T : ℂ → PowerSeries ℂ} (d m : ℕ)
    (hT : ∀ z : ℂ, z ≠ 0 → constantCoeff (T z) = z ^ ((d : ℤ) + 2 * (m : ℤ))) :
    Module.Finite ℂ (formalSections T) ∧
      Module.finrank ℂ (formalSections T) ≤ (m+d+1)^2 := by
  obtain ⟨hf,hb⟩ := filtration_dimension_bound hT (m+d+1) 0 (by push_cast; omega)
  have : Module.Finite ℂ (orderFiltration T 0) := hf
  refine ⟨Module.Finite.equiv (zeroFiltrationEquiv T), ?_⟩
  rw [← (zeroFiltrationEquiv T).finrank_eq]
  apply hb.trans
  rw [← sum_descending_odds (m+d+1)]
  apply Finset.sum_le_sum
  intro j hj
  have hj' := Finset.mem_range.mp hj
  simp only [Nat.zero_add]
  omega

 

theorem twice_polynomial_dimension_gt (d : ℕ) :
    (4*(d+1)+d+1)^2 < 2*(4*(d+1)+1)^2 := by ring_nf; omega

 
def entireSeries : Subalgebra ℂ (PowerSeries (ℂ → ℂ)) where
  carrier := {f | ∀ k, Differentiable ℂ (coeff k f)}
  zero_mem' := by simp
  one_mem' := by intro k; simp [coeff_one]; split <;> simp
  add_mem' := by intro f g hf hg k; simpa using (hf k).add (hg k)
  mul_mem' := by
    intro f g hf hg k
    rw [coeff_mul]
    exact Differentiable.sum (fun ij hij => (hf ij.1).mul (hg ij.2))
  algebraMap_mem' := by
    intro c k
    simp only [PowerSeries.algebraMap_apply, coeff_C]
    split <;> exact differentiable_const _

theorem C_mem_entireSeries {f : ℂ → ℂ} (hf : Differentiable ℂ f) : C f ∈ entireSeries := by
  intro k
  rw [coeff_C]
  split
  · exact hf
  · exact differentiable_const _

theorem X_mem_entireSeries : (X : PowerSeries (ℂ → ℂ)) ∈ entireSeries := by
  intro k
  rw [coeff_X]
  split <;> exact differentiable_const _

 
def twistTransition (m : ℕ) (z : ℂ) : PowerSeries ℂ :=
  (C z * (C z + X)) ^ m

@[simp] theorem twistTransition_constant (m : ℕ) (z : ℂ) :
    constantCoeff (twistTransition m z) = z ^ (2*m) := by
  simp [twistTransition, ← pow_two, ← pow_mul]

abbrev BiCoefficients (m : ℕ) := Fin (m+1) → Fin (m+1) → ℂ

def normalPolynomialSection (m : ℕ) (a : BiCoefficients m) : PowerSeries (ℂ → ℂ) :=
  ∑ j, C (fun z => ∑ i, a i j * z ^ i.val) * (C id + X) ^ j.val

def infinityPolynomialSection (m : ℕ) (a : BiCoefficients m) : PowerSeries (ℂ → ℂ) :=
  ∑ j, C (fun z => ∑ i, a i j * z ^ (m-i.val)) * (C id + X) ^ (m-j.val)

theorem normalPolynomialSection_entire (m : ℕ) (a : BiCoefficients m) :
    normalPolynomialSection m a ∈ entireSeries := by
  apply Subalgebra.sum_mem
  intro j hj
  apply Subalgebra.mul_mem
  · apply C_mem_entireSeries
    exact Differentiable.fun_sum (fun i hi => (differentiable_id.pow i.val).const_mul _)
  · exact Subalgebra.pow_mem _ (Subalgebra.add_mem _ (C_mem_entireSeries differentiable_id)
      X_mem_entireSeries) _

theorem infinityPolynomialSection_entire (m : ℕ) (a : BiCoefficients m) :
    infinityPolynomialSection m a ∈ entireSeries := by
  apply Subalgebra.sum_mem
  intro j hj
  apply Subalgebra.mul_mem
  · apply C_mem_entireSeries
    exact Differentiable.fun_sum (fun i hi => (differentiable_id.pow _).const_mul _)
  · exact Subalgebra.pow_mem _ (Subalgebra.add_mem _ (C_mem_entireSeries differentiable_id)
      X_mem_entireSeries) _

@[simp] theorem evaluateCoefficients_C (z : ℂ) (f : ℂ → ℂ) :
    evaluateCoefficients z (C f) = C (f z) := by
  exact PowerSeries.map_C _ _

@[simp] theorem evaluateCoefficients_X (z : ℂ) :
    evaluateCoefficients z X = X := by
  exact PowerSeries.map_X _

theorem cancel_complementary_powers {R : Type*} [CommRing R] {x y : R}
    (hxy : x*y=1) {m i : ℕ} (hi : i ≤ m) : x^m*y^(m-i) = x^i := by
  calc
    x^m*y^(m-i) = x^i * (x*y)^(m-i) := by
      rw [mul_pow, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hi]
    _ = x^i := by rw [hxy, one_pow, mul_one]

 

theorem polynomialSection_gluing (m : ℕ) (a : BiCoefficients m) (z : ℂ) (hz : z ≠ 0) :
    evaluateCoefficients z (normalPolynomialSection m a) =
      twistTransition m z * subst (reciprocalNormal z)
        (evaluateCoefficients z⁻¹ (infinityPolynomialSection m a)) := by
  have hc : (C z : PowerSeries ℂ) * C z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hz, map_one]
  have hx : (C z + X : PowerSeries ℂ) * (C z + X)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simpa using hz)
  have hn : C z⁻¹ + reciprocalNormal z = (C z + X)⁻¹ := by simp [reciprocalNormal]
  simp only [normalPolynomialSection, infinityPolynomialSection, map_sum, map_mul, map_pow, map_add,
    evaluateCoefficients_C, evaluateCoefficients_X, id_eq]
  rw [← coe_substAlgHom (reciprocalNormal_hasSubst z)]
  simp only [map_sum, map_mul, map_pow, map_add, coe_substAlgHom, PowerSeries.subst_C,
    PowerSeries.subst_X (reciprocalNormal_hasSubst z)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change (∑ i, C (a i j) * C z ^ i.val) * (C z + X) ^ j.val =
    twistTransition m z * ((∑ i, C (a i j) * C z⁻¹ ^ (m-i.val)) *
      (C z⁻¹ + reciprocalNormal z) ^ (m-j.val))
  rw [hn]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [twistTransition, mul_pow]
  calc
    C (a i j) * C z ^ i.val * (C z + X) ^ j.val =
        C (a i j) * (C z ^ m * C z⁻¹ ^ (m-i.val)) *
          ((C z+X)^m * ((C z+X)⁻¹)^(m-j.val)) := by
      rw [cancel_complementary_powers hc (Nat.le_of_lt_succ i.isLt),
        cancel_complementary_powers hx (Nat.le_of_lt_succ j.isLt)]
    _ = _ := by ring

def polynomialFunction : Polynomial ℂ →ₐ[ℂ] (ℂ → ℂ) :=
  AlgHom.pi (fun z => Polynomial.aeval z)

@[simp] theorem polynomialFunction_apply (p : Polynomial ℂ) (z : ℂ) :
    polynomialFunction p z = p.eval z := by simp [polynomialFunction]

theorem polynomialFunction_injective : Function.Injective polynomialFunction := by
  intro p q h
  exact Polynomial.funext (fun z => by simpa using congrFun h z)

def biPolynomial (m : ℕ) (a : BiCoefficients m) : Polynomial (Polynomial ℂ) :=
  ∑ j, Polynomial.monomial j.val (∑ i, Polynomial.monomial i.val (a i j))

@[simp] theorem biPolynomial_coeff (m : ℕ) (a : BiCoefficients m) (i j : Fin (m+1)) :
    ((biPolynomial m a).coeff j.val).coeff i.val = a i j := by
  simp [biPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    ← Fin.ext_iff]

theorem biPolynomial_injective (m : ℕ) : Function.Injective (biPolynomial m) := by
  intro a b h
  funext i j
  simpa using congrArg (fun p : Polynomial (Polynomial ℂ) => (p.coeff j.val).coeff i.val) h

def expandPolynomial (p : Polynomial (Polynomial ℂ)) : PowerSeries (ℂ → ℂ) :=
  (p.map polynomialFunction.toRingHom).comp (Polynomial.X + Polynomial.C id)

theorem expandPolynomial_injective : Function.Injective expandPolynomial := by
  intro p q h
  have he := Polynomial.coe_injective (ℂ → ℂ) h
  have he' := congrArg (fun f : Polynomial (ℂ → ℂ) => f.comp (Polynomial.X - Polynomial.C id)) he
  have hc : (Polynomial.X + Polynomial.C id : Polynomial (ℂ → ℂ)).comp
      (Polynomial.X - Polynomial.C id) = Polynomial.X := by simp
  simp only [Polynomial.comp_assoc, hc, Polynomial.comp_X] at he'
  exact Polynomial.map_injective polynomialFunction.toRingHom polynomialFunction_injective he'

theorem polynomial_coe_sum {ι R : Type*} [Semiring R] (s : Finset ι)
    (f : ι → Polynomial R) :
    ((∑ i ∈ s, f i : Polynomial R) : PowerSeries R) = ∑ i ∈ s, (f i : PowerSeries R) :=
  map_sum Polynomial.coeToPowerSeries.ringHom f s

theorem normalPolynomialSection_eq_expand (m : ℕ) (a : BiCoefficients m) :
    normalPolynomialSection m a = expandPolynomial (biPolynomial m a) := by
  simp only [normalPolynomialSection, expandPolynomial, biPolynomial,
    Polynomial.map_sum, Polynomial.map_monomial, Polynomial.sum_comp,
    Polynomial.monomial_comp, polynomial_coe_sum, Polynomial.coe_mul,
    Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_C, Polynomial.coe_X]
  apply Finset.sum_congr rfl
  intro j hj
  have he : polynomialFunction (∑ i, Polynomial.monomial i.val (a i j)) =
      fun z => ∑ i, a i j * z ^ i.val := by
    ext z
    simp [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  change C (fun z => ∑ i, a i j * z ^ i.val) * (C id + X) ^ j.val =
    C (polynomialFunction (∑ i, Polynomial.monomial i.val (a i j))) * (X + C id) ^ j.val
  rw [he, add_comm (C id) X]

theorem normalPolynomialSection_injective (m : ℕ) :
    Function.Injective (normalPolynomialSection m) := by
  intro a b h
  rw [normalPolynomialSection_eq_expand, normalPolynomialSection_eq_expand] at h
  exact biPolynomial_injective m (expandPolynomial_injective h)

theorem C_complex_smul (c : ℂ) (f : ℂ → ℂ) : C (c • f) = c • C f := by
  ext k
  simp only [coeff_C, coeff_smul]
  split <;> simp

def chartPolynomialLinear (m : ℕ) (e h : Fin (m+1) → ℕ) :
    BiCoefficients m →ₗ[ℂ] PowerSeries (ℂ → ℂ) where
  toFun a := ∑ j, C (∑ i, a i j • (fun z : ℂ => z ^ e i)) * (C id + X) ^ h j
  map_add' a b := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add, add_mul]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_eq_mul, ← smul_smul, ← Finset.smul_sum, C_complex_smul,
      smul_mul_assoc]
    simp only [RingHom.id_apply, Finset.smul_sum]

theorem normalPolynomialSection_eq_linear (m : ℕ) (a : BiCoefficients m) :
    normalPolynomialSection m a = chartPolynomialLinear m Fin.val Fin.val a := by
  unfold normalPolynomialSection chartPolynomialLinear
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  funext z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem infinityPolynomialSection_eq_linear (m : ℕ) (a : BiCoefficients m) :
    infinityPolynomialSection m a = chartPolynomialLinear m (fun i => m-i.val) (fun j => m-j.val) a := by
  unfold infinityPolynomialSection chartPolynomialLinear
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  funext z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

 

def polynomialSection (m : ℕ) : BiCoefficients m →ₗ[ℂ] formalSections (twistTransition m) where
  toFun a := ⟨(normalPolynomialSection m a, infinityPolynomialSection m a),
    normalPolynomialSection_entire m a, infinityPolynomialSection_entire m a,
    polynomialSection_gluing m a⟩
  map_add' a b := by
    apply Subtype.ext
    apply Prod.ext
    · exact (normalPolynomialSection_eq_linear m (a+b)).trans (by
        rw [map_add]; congr 1 <;> symm <;> apply normalPolynomialSection_eq_linear)
    · exact (infinityPolynomialSection_eq_linear m (a+b)).trans (by
        rw [map_add]; congr 1 <;> symm <;> apply infinityPolynomialSection_eq_linear)
  map_smul' c a := by
    apply Subtype.ext
    apply Prod.ext
    · exact (normalPolynomialSection_eq_linear m (c • a)).trans (by
        rw [map_smul]; congr 1; symm; apply normalPolynomialSection_eq_linear)
    · exact (infinityPolynomialSection_eq_linear m (c • a)).trans (by
        rw [map_smul]; congr 1; symm; apply infinityPolynomialSection_eq_linear)

theorem polynomialSection_injective (m : ℕ) : Function.Injective (polynomialSection m) := by
  intro a b h
  exact normalPolynomialSection_injective m (congrArg (fun s => s.val.1) h)

 
def multiplySection {T U : ℂ → PowerSeries ℂ} (s : formalSections T) (t : formalSections U) :
    formalSections (fun z => T z * U z) :=
  ⟨(s.val.1*t.val.1, s.val.2*t.val.2),
    entireSeries.mul_mem s.property.1 t.property.1,
    entireSeries.mul_mem s.property.2.1 t.property.2.1, by
      intro z hz
      change evaluateCoefficients z (s.val.1*t.val.1) =
        (T z * U z) * subst (reciprocalNormal z) (evaluateCoefficients z⁻¹ (s.val.2*t.val.2))
      rw [map_mul, map_mul, subst_mul (reciprocalNormal_hasSubst z),
        s.property.2.2 z hz, t.property.2.2 z hz]
      ring⟩

 
def relationMap {T : ℂ → PowerSeries ℂ} (s t : formalSections T) (m : ℕ) :
    (BiCoefficients m × BiCoefficients m) →ₗ[ℂ]
      formalSections (fun z => twistTransition m z * T z) where
  toFun ab := multiplySection (polynomialSection m ab.1) s +
    multiplySection (polynomialSection m ab.2) t
  map_add' a b := by
    apply Subtype.ext
    apply Prod.ext <;> simp [multiplySection, map_add, add_mul] <;> ring
  map_smul' c a := by
    apply Subtype.ext
    apply Prod.ext <;> simp [multiplySection, map_smul, smul_add]

theorem finrank_biCoefficients (m : ℕ) : Module.finrank ℂ (BiCoefficients m) = (m+1)^2 := by
  simp [BiCoefficients, Module.finrank_pi_fintype, pow_two]

theorem exists_polynomial_relation {T : ℂ → PowerSeries ℂ} (d : ℕ)
    (hT : ∀ z : ℂ, z ≠ 0 → constantCoeff (T z) = z ^ (d : ℤ))
    (s t : formalSections T) :
    ∃ ab : BiCoefficients (4*(d+1)) × BiCoefficients (4*(d+1)),
      ab ≠ 0 ∧ relationMap s t (4*(d+1)) ab = 0 := by
  let m := 4*(d+1)
  have hTw : ∀ z : ℂ, z ≠ 0 →
      constantCoeff (twistTransition m z * T z) = z ^ ((d : ℤ) + 2*(m : ℤ)) := by
    intro z hz
    simp only [map_mul, twistTransition, map_pow, constantCoeff_C, map_add,
      constantCoeff_X, add_zero]
    rw [hT z hz, mul_pow]
    rw [zpow_add₀ hz]
    rw [show (2 : ℤ) * (m : ℤ) = ((2*m : ℕ) : ℤ) by omega]
    simp only [zpow_natCast, pow_mul, pow_two]
    ring
  obtain ⟨hf, hb⟩ := formalSections_dimension_bound d m hTw
  let : Module.Finite ℂ (formalSections (fun z => twistTransition m z * T z)) := hf
  have hdim : Module.finrank ℂ (formalSections (fun z => twistTransition m z * T z)) <
      Module.finrank ℂ (BiCoefficients m × BiCoefficients m) := by
    rw [Module.finrank_prod, finrank_biCoefficients]
    have h := twice_polynomial_dimension_gt d
    dsimp [m] at hb ⊢
    omega
  obtain ⟨ab, hab, hne⟩ := (Submodule.ne_bot_iff _).mp
    (LinearMap.ker_ne_bot_of_finrank_lt (f := relationMap s t m) hdim)
  exact ⟨ab, hne, hab⟩

 

theorem entireSeries_cancel {f g : PowerSeries (ℂ → ℂ)}
    (hf : ∀ k, Differentiable ℂ (coeff k f))
    (hg : Differentiable ℂ (constantCoeff g))
    (hg0 : ∃ z : ℂ, constantCoeff g z ≠ 0) (hfg : f*g = 0) : f = 0 := by
  obtain ⟨z₀,hz₀⟩ := hg0
  have he : ∀ᶠ z in nhds z₀, constantCoeff g z ≠ 0 :=
    hg.continuous.continuousAt.eventually_ne hz₀
  apply PowerSeries.ext
  intro k
  change coeff k f = fun _ => 0
  apply AnalyticOnNhd.eq_of_eventuallyEq
    (fun z _ => (hf k).analyticAt z) analyticOnNhd_const
  filter_upwards [he] with z hz
  have hg' : evaluateCoefficients z g ≠ 0 := by
    intro h
    have hc := congrArg (coeff 0) h
    apply hz
    simpa only [coeff_evaluateCoefficients, coeff_zero_eq_constantCoeff, map_zero] using hc
  have h := congrArg (evaluateCoefficients z) hfg
  simp only [map_mul, map_zero] at h
  have hf' := (mul_eq_zero.mp h).resolve_right hg'
  simpa using congrArg (coeff k) hf'

 

theorem exists_rational_relation {T : ℂ → PowerSeries ℂ} (d : ℕ)
    (hT : ∀ z : ℂ, z ≠ 0 → constantCoeff (T z) = z ^ (d : ℤ))
    (s t : formalSections T) (hs : ∃ z : ℂ, constantCoeff s.val.1 z ≠ 0) :
    ∃ a b : BiCoefficients (4*(d+1)), b ≠ 0 ∧
      normalPolynomialSection (4*(d+1)) a * s.val.1 +
      normalPolynomialSection (4*(d+1)) b * t.val.1 = 0 := by
  obtain ⟨⟨a,b⟩,hne,hrel⟩ := exists_polynomial_relation d hT s t
  have hfirst : normalPolynomialSection (4*(d+1)) a * s.val.1 +
      normalPolynomialSection (4*(d+1)) b * t.val.1 = 0 :=
    congrArg (fun w => w.val.1) hrel
  refine ⟨a,b,?_,hfirst⟩
  intro hb
  subst b
  have hzero : normalPolynomialSection (4*(d+1)) 0 = 0 := by
    rw [normalPolynomialSection_eq_linear, map_zero]
  rw [hzero, zero_mul, add_zero] at hfirst
  have ha := entireSeries_cancel (normalPolynomialSection_entire _ a)
    (by simpa only [coeff_zero_eq_constantCoeff] using s.property.1 0) hs hfirst
  have ha' : a = 0 := normalPolynomialSection_injective _ (ha.trans hzero.symm)
  exact hne (by simp [ha'])

 

theorem entireSeries_vanishing_of_mul {f g : PowerSeries (ℂ → ℂ)}
    (hf : ∀ k, Differentiable ℂ (coeff k f))
    (hg : Differentiable ℂ (constantCoeff g))
    (hg0 : ∃ z : ℂ, constantCoeff g z ≠ 0) {r : ℕ}
    (hmul : ∀ k < r, coeff k (f*g) = 0) : ∀ k < r, coeff k f = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hkr
    obtain ⟨q,hq⟩ := X_pow_dvd_iff.mpr (fun j hj => ih j hj (hj.trans hkr))
    have hc : coeff k (f*g) = coeff k f * constantCoeff g := by
      rw [hq, mul_assoc]
      rw [coeff_X_pow_mul', coeff_X_pow_mul']
      simp [coeff_zero_eq_constantCoeff]
    have hzero : coeff k f * constantCoeff g = 0 := hc.symm.trans (hmul k hkr)
    obtain ⟨z₀,hz₀⟩ := hg0
    apply AnalyticOnNhd.eq_of_eventuallyEq
      (fun z _ => (hf k).analyticAt z) analyticOnNhd_const
    filter_upwards [hg.continuous.continuousAt.eventually_ne hz₀] with z hz
    exact (mul_eq_zero.mp (congrFun hzero z)).resolve_right hz

 

def normalPolynomial (m : ℕ) (a : BiCoefficients m) : Polynomial (ℂ → ℂ) :=
  ∑ j, Polynomial.C (fun z => ∑ i, a i j * z ^ i.val) *
    (Polynomial.C id + Polynomial.X) ^ j.val

@[simp] theorem normalPolynomial_coe (m : ℕ) (a : BiCoefficients m) :
    (normalPolynomial m a : PowerSeries (ℂ → ℂ)) = normalPolynomialSection m a := by
  simp [normalPolynomial, normalPolynomialSection, polynomial_coe_sum]

 
theorem cancel_normal_order {A B : Polynomial (ℂ → ℂ)}
    {s t : PowerSeries (ℂ → ℂ)}
    (hA : ∀ k, Differentiable ℂ (A.coeff k))
    (hs : Differentiable ℂ (constantCoeff s))
    (hs0 : ∃ z : ℂ, constantCoeff s z ≠ 0)
    (hrel : (A : PowerSeries (ℂ → ℂ))*s + (B : PowerSeries (ℂ → ℂ))*t = 0) :
    Polynomial.X ^ B.natTrailingDegree ∣ A := by
  have hB : X ^ B.natTrailingDegree ∣ (B : PowerSeries (ℂ → ℂ)) :=
    X_pow_dvd_iff.mpr (by
      intro k hk
      simpa only [Polynomial.coeff_coe] using
        (Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hk))
  have hAs : X ^ B.natTrailingDegree ∣ (A : PowerSeries (ℂ → ℂ))*s := by
    have h := dvd_mul_of_dvd_left hB t
    have he : (A : PowerSeries (ℂ → ℂ))*s = -((B : PowerSeries (ℂ → ℂ))*t) :=
      eq_neg_of_add_eq_zero_left hrel
    rw [he]
    exact dvd_neg.mpr h
  apply Polynomial.X_pow_dvd_iff.mpr
  simpa only [Polynomial.coeff_coe] using
    (entireSeries_vanishing_of_mul
      (by simpa only [Polynomial.coeff_coe] using hA) hs hs0 (X_pow_dvd_iff.mp hAs))

 

theorem exists_reduced_polynomial_relation {A B : Polynomial (ℂ → ℂ)}
    {s t : PowerSeries (ℂ → ℂ)}
    (hA : ∀ k, Differentiable ℂ (A.coeff k))
    (hB : ∀ k, Differentiable ℂ (B.coeff k)) (hB0 : B ≠ 0)
    (hs : Differentiable ℂ (constantCoeff s))
    (hs0 : ∃ z : ℂ, constantCoeff s z ≠ 0)
    (hrel : (A : PowerSeries (ℂ → ℂ))*s + (B : PowerSeries (ℂ → ℂ))*t = 0) :
    ∃ (r : ℕ) (A' B' : Polynomial (ℂ → ℂ)),
      A = Polynomial.X ^ r * A' ∧ B = Polynomial.X ^ r * B' ∧
      B'.coeff 0 ≠ 0 ∧ (∀ k, Differentiable ℂ (A'.coeff k)) ∧
      (∀ k, Differentiable ℂ (B'.coeff k)) ∧
      (A' : PowerSeries (ℂ → ℂ))*s + (B' : PowerSeries (ℂ → ℂ))*t = 0 := by
  let r := B.natTrailingDegree
  obtain ⟨A',hA'⟩ := cancel_normal_order hA hs hs0 hrel
  change A = Polynomial.X ^ r * A' at hA'
  obtain ⟨B',hB'⟩ := Polynomial.X_pow_dvd_iff.mpr
    (fun k hk => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hk :
      ∀ k < r, B.coeff k = 0)
  have hca (k : ℕ) : A'.coeff k = A.coeff (k+r) := by
    rw [hA', Polynomial.coeff_X_pow_mul]
  have hcb (k : ℕ) : B'.coeff k = B.coeff (k+r) := by
    rw [hB', Polynomial.coeff_X_pow_mul]
  refine ⟨r,A',B',hA',hB',?_,fun k => ?_,fun k => ?_,?_⟩
  · rw [hcb 0, Nat.zero_add]
    exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hB0
  · rw [hca k]
    exact hA (k+r)
  · rw [hcb k]
    exact hB (k+r)
  · apply X_pow_mul_cancel (k := r)
    rw [mul_zero]
    rw [hA',hB'] at hrel
    simpa only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, mul_add,
      mul_assoc] using hrel

 

theorem exists_common_nonzero {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf0 : f ≠ 0) (hg0 : ∃ z : ℂ, g z ≠ 0) :
    ∃ z : ℂ, f z ≠ 0 ∧ g z ≠ 0 := by
  obtain ⟨z₀,hz₀⟩ := hg0
  by_contra h
  have he : f =ᶠ[nhds z₀] (fun _ => 0) := by
    filter_upwards [hg.continuous.continuousAt.eventually_ne hz₀] with z hz
    by_contra hfz
    exact h ⟨z,hfz,hz⟩
  apply hf0
  exact AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => hf.analyticAt z) analyticOnNhd_const he

 

def polynomialEvaluation (p : Polynomial (ℂ → ℂ)) (w : ℂ × ℂ) : ℂ :=
  p.eval₂ (Pi.evalRingHom (fun _ : ℂ => ℂ) w.1) w.2

@[simp] theorem polynomialEvaluation_diagonal (p : Polynomial (ℂ → ℂ)) (z : ℂ) :
    polynomialEvaluation p (z,0) = p.coeff 0 z := by
  simp [polynomialEvaluation, Polynomial.eval₂_at_zero]

theorem polynomialEvaluation_analytic (p : Polynomial (ℂ → ℂ))
    (hp : ∀ k, Differentiable ℂ (p.coeff k)) (w : ℂ × ℂ) :
    AnalyticAt ℂ (polynomialEvaluation p) w := by
  have ht (k : ℕ) : AnalyticAt ℂ (fun u : ℂ × ℂ => p.coeff k u.1 * u.2 ^ k) w :=
    (((hp k).analyticAt w.1).comp
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt w)).mul
        (((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt w).pow k)
  have he : polynomialEvaluation p =
      ∑ k ∈ p.support, (fun u : ℂ × ℂ => p.coeff k u.1 * u.2 ^ k) := by
    funext u
    simp [polynomialEvaluation, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  rw [he]
  exact Finset.analyticAt_sum p.support (fun k _ => ht k)

 

theorem polynomial_quotient_analytic {A B : Polynomial (ℂ → ℂ)}
    (hA : ∀ k, Differentiable ℂ (A.coeff k))
    (hB : ∀ k, Differentiable ℂ (B.coeff k)) {z : ℂ} (hz : B.coeff 0 z ≠ 0) :
    AnalyticAt ℂ (fun w => -polynomialEvaluation A w / polynomialEvaluation B w) (z,0) := by
  exact (polynomialEvaluation_analytic A hA (z,0)).neg.div
    (polynomialEvaluation_analytic B hB (z,0)) (by simpa using hz)

 
def taylorSeries (f : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n => iteratedDeriv n f 0 / (n.factorial : ℂ))

@[simp] theorem coeff_taylorSeries (f : ℂ → ℂ) (n : ℕ) :
    coeff n (taylorSeries f) = iteratedDeriv n f 0 / (n.factorial : ℂ) := by
  rw [taylorSeries, coeff_mk]

theorem taylorSeries_congr {f g : ℂ → ℂ} (h : f =ᶠ[nhds 0] g) :
    taylorSeries f = taylorSeries g := by
  apply PowerSeries.ext
  intro n
  rw [coeff_taylorSeries, coeff_taylorSeries, h.iteratedDeriv_eq n]

@[simp] theorem taylorSeries_zero : taylorSeries (fun _ => 0) = 0 := by
  ext n
  simp [taylorSeries]

theorem taylorSeries_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorSeries (f+g) = taylorSeries f + taylorSeries g := by
  ext n
  simp only [map_add, coeff_taylorSeries]
  rw [iteratedDeriv_add hf.contDiffAt hg.contDiffAt, add_div]

theorem taylorSeries_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorSeries (f*g) = taylorSeries f * taylorSeries g := by
  apply PowerSeries.ext
  intro n
  rw [coeff_taylorSeries, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff i (taylorSeries f) * coeff j (taylorSeries g)) n]
  simp only [coeff_taylorSeries]
  rw [iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.cast_choose ℂ (by have := Finset.mem_range.mp hi; omega)]
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp

 
theorem hasFPowerSeries_taylorSeries {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun n => coeff n (taylorSeries f))) 0 := by
  simpa only [coeff_taylorSeries] using hf.hasFPowerSeriesAt

theorem polynomial_analyticAt (p : Polynomial ℂ) (z : ℂ) :
    AnalyticAt ℂ (fun w => p.eval w) z :=
  (AnalyticOnNhd.eval_polynomial p) z (Set.mem_univ z)

@[simp] theorem taylorSeries_polynomial (p : Polynomial ℂ) :
    taylorSeries (fun z => p.eval z) = (p : PowerSeries ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add, Polynomial.coe_add]
    rw [show (fun z => p.eval z + q.eval z) = (fun z => p.eval z) + (fun z => q.eval z) from rfl,
      taylorSeries_add (polynomial_analyticAt p 0) (polynomial_analyticAt q 0), hp, hq]
  | monomial n a =>
    apply PowerSeries.ext
    intro k
    simp only [coeff_taylorSeries, Polynomial.eval_monomial, Polynomial.coeff_coe,
      Polynomial.coeff_monomial]
    rw [iteratedDeriv_const_mul a (by fun_prop), iteratedDeriv_fun_pow_zero]
    by_cases h : k = n
    · subst k
      simp [Nat.factorial_ne_zero]
    · simp [h, Ne.symm h]

 
theorem taylorSeries_quotient_relation (A B : Polynomial ℂ) (hB : B.coeff 0 ≠ 0) :
    taylorSeries (fun z => -A.eval z / B.eval z) * (B : PowerSeries ℂ) + A = 0 := by
  have ha := polynomial_analyticAt A 0
  have hb := polynomial_analyticAt B 0
  have hb0 : B.eval 0 ≠ 0 := by simpa only [← Polynomial.coeff_zero_eq_eval_zero] using hB
  have hq : AnalyticAt ℂ (fun z => -A.eval z / B.eval z) 0 := ha.neg.div hb hb0
  have he : (fun z => (-A.eval z / B.eval z) * B.eval z + A.eval z) =ᶠ[nhds 0]
      (fun _ => (0 : ℂ)) := by
    filter_upwards [hb.continuousAt.eventually_ne hb0] with z hz
    field_simp
    ring
  have ht := taylorSeries_congr he
  rw [taylorSeries_zero] at ht
  change taylorSeries ((fun z => -A.eval z / B.eval z) * (fun z => B.eval z) +
    (fun z => A.eval z)) = 0 at ht
  rw [taylorSeries_add (hq.mul hb) ha, taylorSeries_mul hq hb,
    taylorSeries_polynomial, taylorSeries_polynomial] at ht
  exact ht

 

theorem taylorSeries_quotient_eq (A B : Polynomial ℂ) (hB : B.coeff 0 ≠ 0)
    (s t : PowerSeries ℂ) (hs : constantCoeff s ≠ 0)
    (hrel : (A : PowerSeries ℂ)*s + (B : PowerSeries ℂ)*t = 0) :
    taylorSeries (fun z => -A.eval z / B.eval z) = t * s⁻¹ := by
  have hq := taylorSeries_quotient_relation A B hB
  have hBn : (B : PowerSeries ℂ) ≠ 0 := by
    intro h
    apply hB
    simpa only [Polynomial.coeff_coe, map_zero] using congrArg (coeff 0) h
  have he : taylorSeries (fun z => -A.eval z / B.eval z) * s = t := by
    apply mul_left_cancel₀ hBn
    calc
      (B : PowerSeries ℂ) * (taylorSeries (fun z => -A.eval z / B.eval z) * s) =
          (taylorSeries (fun z => -A.eval z / B.eval z) * B) * s := by ring
      _ = (-A) * s := by rw [eq_neg_of_add_eq_zero_left hq]
      _ = B * t := by linear_combination -hrel
  calc
    taylorSeries (fun z => -A.eval z / B.eval z) =
        (taylorSeries (fun z => -A.eval z / B.eval z) * s) * s⁻¹ := by
          rw [mul_assoc, PowerSeries.mul_inv_cancel s hs, mul_one]
    _ = t * s⁻¹ := by rw [he]

 
theorem hasFPowerSeries_formal_quotient (A B : Polynomial ℂ) (hB : B.coeff 0 ≠ 0)
    (s t : PowerSeries ℂ) (hs : constantCoeff s ≠ 0)
    (hrel : (A : PowerSeries ℂ)*s + (B : PowerSeries ℂ)*t = 0) :
    HasFPowerSeriesAt (fun z => -A.eval z / B.eval z)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => coeff n (t*s⁻¹))) 0 := by
  have hq : AnalyticAt ℂ (fun z => -A.eval z / B.eval z) 0 :=
    (polynomial_analyticAt A 0).neg.div (polynomial_analyticAt B 0)
      (by simpa only [← Polynomial.coeff_zero_eq_eval_zero] using hB)
  convert hasFPowerSeries_taylorSeries hq using 1
  rw [taylorSeries_quotient_eq A B hB s t hs hrel]

 
def polynomialFiber (p : Polynomial (ℂ → ℂ)) (z : ℂ) : Polynomial ℂ :=
  p.map (Pi.evalRingHom (fun _ : ℂ => ℂ) z)

@[simp] theorem polynomialFiber_coeff (p : Polynomial (ℂ → ℂ)) (z : ℂ) (n : ℕ) :
    (polynomialFiber p z).coeff n = p.coeff n z := by
  simp [polynomialFiber]

@[simp] theorem polynomialFiber_eval (p : Polynomial (ℂ → ℂ)) (z v : ℂ) :
    (polynomialFiber p z).eval v = polynomialEvaluation p (z,v) := by
  simp [polynomialFiber, polynomialEvaluation, Polynomial.eval_map]

@[simp] theorem evaluateCoefficients_polynomial (p : Polynomial (ℂ → ℂ)) (z : ℂ) :
    evaluateCoefficients z (p : PowerSeries (ℂ → ℂ)) =
      (polynomialFiber p z : PowerSeries ℂ) := by
  ext n
  simp

 

theorem reduced_relation_converges {A B : Polynomial (ℂ → ℂ)}
    {s t : PowerSeries (ℂ → ℂ)} {z : ℂ}
    (hB : B.coeff 0 z ≠ 0) (hs : constantCoeff s z ≠ 0)
    (hrel : (A : PowerSeries (ℂ → ℂ))*s + (B : PowerSeries (ℂ → ℂ))*t = 0) :
    HasFPowerSeriesAt
      (fun v => -polynomialEvaluation A (z,v) / polynomialEvaluation B (z,v))
      (FormalMultilinearSeries.ofScalars ℂ (fun n =>
        coeff n (evaluateCoefficients z t * (evaluateCoefficients z s)⁻¹))) 0 := by
  have he := congrArg (evaluateCoefficients z) hrel
  simp only [map_add, map_mul, map_zero, evaluateCoefficients_polynomial] at he
  have hs' : constantCoeff (evaluateCoefficients z s) ≠ 0 := by
    simpa only [← coeff_zero_eq_constantCoeff, coeff_evaluateCoefficients] using hs
  simpa only [polynomialFiber_eval] using
    hasFPowerSeries_formal_quotient (polynomialFiber A z) (polynomialFiber B z)
      (by simpa using hB) (evaluateCoefficients z s) (evaluateCoefficients z t) hs' he

 

theorem exists_convergent_rational_quotient {T : ℂ → PowerSeries ℂ} (d : ℕ)
    (hT : ∀ z : ℂ, z ≠ 0 → constantCoeff (T z) = z ^ (d : ℤ))
    (s t : formalSections T) (hs : ∃ z : ℂ, constantCoeff s.val.1 z ≠ 0) :
    ∃ (a b : BiCoefficients (4*(d+1))) (r : ℕ)
      (A B : Polynomial (ℂ → ℂ)) (z : ℂ),
      b ≠ 0 ∧ normalPolynomial (4*(d+1)) a = Polynomial.X ^ r * A ∧
      normalPolynomial (4*(d+1)) b = Polynomial.X ^ r * B ∧
      (∀ k, Differentiable ℂ (A.coeff k)) ∧
      (∀ k, Differentiable ℂ (B.coeff k)) ∧
      B.coeff 0 z ≠ 0 ∧ constantCoeff s.val.1 z ≠ 0 ∧
      AnalyticAt ℂ (fun w => -polynomialEvaluation A w / polynomialEvaluation B w) (z,0) ∧
      (∀ w : ℂ, B.coeff 0 w ≠ 0 → constantCoeff s.val.1 w ≠ 0 →
        HasFPowerSeriesAt
          (fun v => -polynomialEvaluation A (w,v) / polynomialEvaluation B (w,v))
          (FormalMultilinearSeries.ofScalars ℂ (fun n => coeff n
            (evaluateCoefficients w t.val.1 * (evaluateCoefficients w s.val.1)⁻¹))) 0) := by
  obtain ⟨a,b,hb,hrel⟩ := exists_rational_relation d hT s t hs
  have hal (k : ℕ) : Differentiable ℂ ((normalPolynomial (4*(d+1)) a).coeff k) := by
    simpa only [← Polynomial.coeff_coe, normalPolynomial_coe] using
      normalPolynomialSection_entire (4*(d+1)) a k
  have hbl (k : ℕ) : Differentiable ℂ ((normalPolynomial (4*(d+1)) b).coeff k) := by
    simpa only [← Polynomial.coeff_coe, normalPolynomial_coe] using
      normalPolynomialSection_entire (4*(d+1)) b k
  have hbn : normalPolynomial (4*(d+1)) b ≠ 0 := by
    intro h
    apply hb
    apply normalPolynomialSection_injective (4*(d+1))
    rw [← normalPolynomial_coe, h, Polynomial.coe_zero]
    simp [normalPolynomialSection_eq_linear]
  have hsD : Differentiable ℂ (constantCoeff s.val.1) := by
    simpa only [coeff_zero_eq_constantCoeff] using s.property.1 0
  obtain ⟨r,A,B,hA,hB,hB0,hAD,hBD,hrel'⟩ :=
    exists_reduced_polynomial_relation hal hbl hbn hsD hs
      (by simpa only [normalPolynomial_coe] using hrel)
  obtain ⟨z,hBz,hsz⟩ := exists_common_nonzero (hBD 0) hsD hB0 hs
  exact ⟨a,b,r,A,B,z,hb,hA,hB,hAD,hBD,hBz,hsz,
    polynomial_quotient_analytic hAD hBD hBz,
    fun w hwB hws => reduced_relation_converges hwB hws hrel'⟩

 

theorem exists_common_nonzero_finset {ι : Type*} (q : Finset ι)
    (f : ι → ℂ → ℂ) (g : ℂ → ℂ)
    (hf : ∀ i ∈ q, Differentiable ℂ (f i)) (hg : Differentiable ℂ g)
    (hf0 : ∀ i ∈ q, f i ≠ 0) (hg0 : ∃ z, g z ≠ 0) :
    ∃ z, g z ≠ 0 ∧ ∀ i ∈ q, f i z ≠ 0 := by
  classical
  induction q using Finset.induction_on with
  | empty =>
    obtain ⟨z,hz⟩ := hg0
    exact ⟨z,hz,by simp⟩
  | @insert i q hi ih =>
    obtain ⟨z₀,hg₀,hf₀⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hf0 j (Finset.mem_insert_of_mem hj))
    let h : ℂ → ℂ := fun z => g z * ∏ j ∈ q, f j z
    have hD : Differentiable ℂ h := hg.mul
      (Differentiable.fun_finsetProd (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    have hh0 : ∃ z, h z ≠ 0 := ⟨z₀, mul_ne_zero hg₀ (Finset.prod_ne_zero_iff.mpr hf₀)⟩
    obtain ⟨z,hiz,hz⟩ := exists_common_nonzero (hf i (Finset.mem_insert_self i q))
      hD (hf0 i (Finset.mem_insert_self i q)) hh0
    have hz' : g z ≠ 0 ∧ ∀ j ∈ q, f j z ≠ 0 := by
      simpa only [h, mul_ne_zero_iff, Finset.prod_ne_zero_iff] using hz
    exact ⟨z,hz'.1,fun j hj => by
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hiz
      · exact hz'.2 j hj⟩

 

theorem simultaneous_rational_reconstruction {ι : Type*} [Fintype ι]
    {T : ℂ → PowerSeries ℂ} (d : ℕ)
    (hT : ∀ z : ℂ, z ≠ 0 → constantCoeff (T z) = z ^ (d : ℤ))
    (s : formalSections T) (t : ι → formalSections T)
    (hs : ∃ z : ℂ, constantCoeff s.val.1 z ≠ 0) :
    ∃ (a b : ι → BiCoefficients (4*(d+1))) (r : ι → ℕ)
      (A B : ι → Polynomial (ℂ → ℂ)) (z : ℂ),
      constantCoeff s.val.1 z ≠ 0 ∧ ∀ i,
      b i ≠ 0 ∧ normalPolynomial (4*(d+1)) (a i) = Polynomial.X ^ r i * A i ∧
      normalPolynomial (4*(d+1)) (b i) = Polynomial.X ^ r i * B i ∧
      (B i).coeff 0 z ≠ 0 ∧
      AnalyticAt ℂ (fun w => -polynomialEvaluation (A i) w / polynomialEvaluation (B i) w) (z,0) ∧
      HasFPowerSeriesAt
        (fun v => -polynomialEvaluation (A i) (z,v) / polynomialEvaluation (B i) (z,v))
        (FormalMultilinearSeries.ofScalars ℂ (fun n => coeff n
          (evaluateCoefficients z (t i).val.1 * (evaluateCoefficients z s.val.1)⁻¹))) 0 := by
  classical
  choose a b r A B z hb ha hbP hAD hBD hBz hsZ hq hc using
    fun i => exists_convergent_rational_quotient d hT s (t i) hs
  have hsD : Differentiable ℂ (constantCoeff s.val.1) := by
    simpa only [coeff_zero_eq_constantCoeff] using s.property.1 0
  obtain ⟨w,hsw,hw⟩ := exists_common_nonzero_finset Finset.univ
    (fun i => (B i).coeff 0) (constantCoeff s.val.1)
    (fun i _ => hBD i 0) hsD
    (fun i _ he => hBz i (congrFun he (z i))) hs
  refine ⟨a,b,r,A,B,w,hsw,fun i => ?_⟩
  have hi := hw i (Finset.mem_univ i)
  exact ⟨hb i,ha i,hbP i,hi,polynomial_quotient_analytic (hAD i) (hBD i) hi,
    hc i w hi hsw⟩

end SplitTangent.DiagonalRationality

open Set Filter Topology Polynomial PowerSeries
namespace SplitTangent.FormalProjective
section

 
def AnalyticSeriesAt (f : ℂ → PowerSeries ℂ) (z : ℂ) : Prop :=
  ∀ n : ℕ, AnalyticAt ℂ (fun w => PowerSeries.coeff n (f w)) z

namespace AnalyticSeriesAt

variable {f g : ℂ → PowerSeries ℂ} {z : ℂ}

theorem add (hf : AnalyticSeriesAt f z) (hg : AnalyticSeriesAt g z) :
    AnalyticSeriesAt (fun w => f w + g w) z := by
  intro n
  simp only [map_add]
  exact (hf n).add (hg n)

theorem mul (hf : AnalyticSeriesAt f z) (hg : AnalyticSeriesAt g z) :
    AnalyticSeriesAt (fun w => f w * g w) z := by
  intro n
  simp only [PowerSeries.coeff_mul]
  exact Finset.analyticAt_fun_sum _ (fun ij _ => (hf ij.1).mul (hg ij.2))

theorem constant {a : ℂ → ℂ} (ha : AnalyticAt ℂ a z) :
    AnalyticSeriesAt (fun w => PowerSeries.C (a w)) z := by
  intro n
  simp only [PowerSeries.coeff_C]
  split_ifs
  · exact ha
  · exact analyticAt_const

theorem sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → PowerSeries ℂ}
    (hf : ∀ i ∈ s, AnalyticSeriesAt (f i) z) :
    AnalyticSeriesAt (fun w => ∑ i ∈ s, f i w) z := by
  intro n
  simp only [map_sum]
  exact Finset.analyticAt_fun_sum _ (fun i hi => hf i hi n)

theorem inv (hf : AnalyticSeriesAt f z) (h0 : PowerSeries.constantCoeff (f z) ≠ 0) :
    AnalyticSeriesAt (fun w => (f w)⁻¹) z := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hc0 : AnalyticAt ℂ (fun w => PowerSeries.constantCoeff (f w)) z := by
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hf 0
    have hconst : AnalyticAt ℂ (fun w => (PowerSeries.constantCoeff (f w))⁻¹) z :=
      hc0.fun_inv h0
    by_cases hn : n = 0
    · subst n
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.constantCoeff_inv] using hconst
    · have heq : (fun w => PowerSeries.coeff n ((f w)⁻¹)) =
          (fun w => -(PowerSeries.constantCoeff (f w))⁻¹ *
            ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, if ij.2 < n then
              PowerSeries.coeff ij.1 (f w) * PowerSeries.coeff ij.2 ((f w)⁻¹) else 0) := by
        funext w
        exact (PowerSeries.coeff_inv n (f w)).trans (ite_eq_right hn)
      rw [heq]
      apply hconst.neg.mul
      apply Finset.analyticAt_fun_sum
      intro ij _
      split_ifs with hj
      · exact (hf ij.1).mul (ih ij.2 hj)
      · exact analyticAt_const

end AnalyticSeriesAt

 

structure ChartData {ι : Type*} [Fintype ι] (p : ι → ℂ[X]) where
  basepoint_free : ∀ z : ℂ, ∃ k, (p k).eval z ≠ 0
  ratio : ι → ι → ℂ → PowerSeries ℂ
  analytic : ∀ k j z, (p k).eval z ≠ 0 → AnalyticSeriesAt (ratio k j) z
  diagonal : ∀ k j z, (p k).eval z ≠ 0 →
    PowerSeries.constantCoeff (ratio k j z) = (p j).eval z / (p k).eval z
  identity : ∀ k z, (p k).eval z ≠ 0 → ratio k k z = 1
  overlap : ∀ k l j z, (p k).eval z ≠ 0 → (p l).eval z ≠ 0 →
    ratio k l z * ratio l j z = ratio k j z

namespace ChartData
variable {ι : Type*} [Fintype ι] {p : ι → ℂ[X]} (F : ChartData p)
  (a : ι → ℂ[X]) (ha : ∑ i, a i * p i = 1)

 

def frame (k : ι) (z : ℂ) : PowerSeries ℂ :=
  ∑ i, PowerSeries.C ((a i).eval z) * F.ratio k i z

include ha in
theorem frame_constant (k : ι) (z : ℂ) (hk : (p k).eval z ≠ 0) :
    PowerSeries.constantCoeff (F.frame a k z) = ((p k).eval z)⁻¹ := by
  have he := congrArg (Polynomial.eval z) ha
  simp only [Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_one] at he
  simp only [frame,map_sum,map_mul,PowerSeries.constantCoeff_C,F.diagonal k _ z hk,div_eq_mul_inv,← mul_assoc]
  rw [← Finset.sum_mul,he,one_mul]

include ha in
theorem frame_unit (k : ι) (z : ℂ) (hk : (p k).eval z ≠ 0) :
    PowerSeries.constantCoeff (F.frame a k z) ≠ 0 := by
  rw [F.frame_constant a ha k z hk]
  exact inv_ne_zero hk

theorem frame_analytic (k : ι) (z : ℂ) (hk : (p k).eval z ≠ 0) :
    AnalyticSeriesAt (F.frame a k) z := by
  apply AnalyticSeriesAt.sum
  intro i _
  apply AnalyticSeriesAt.mul
  · exact AnalyticSeriesAt.constant (AnalyticOnNhd.eval_polynomial (a i) z (mem_univ z))
  · exact F.analytic k i z hk

theorem frame_overlap (k l : ι) (z : ℂ) (hk : (p k).eval z ≠ 0)
    (hl : (p l).eval z ≠ 0) : F.ratio k l z * F.frame a l z = F.frame a k z := by
  simp only [frame,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_left_comm,F.overlap k l i z hk hl]

 
def localSection (k j : ι) (z : ℂ) : PowerSeries ℂ :=
  (F.frame a k z)⁻¹ * F.ratio k j z

include ha in
theorem frame_mul_localSection (k j : ι) (z : ℂ) (hk : (p k).eval z ≠ 0) :
    F.frame a k z * F.localSection a k j z = F.ratio k j z := by
  rw [localSection,← mul_assoc,PowerSeries.mul_inv_cancel _ (F.frame_unit a ha k z hk),one_mul]

include ha in
theorem localSection_overlap (k l j : ι) (z : ℂ) (hk : (p k).eval z ≠ 0)
    (hl : (p l).eval z ≠ 0) : F.localSection a k j z = F.localSection a l j z := by
  have he : F.frame a k z * F.localSection a l j z = F.ratio k j z := by
    rw [← F.frame_overlap a k l z hk hl,mul_assoc,F.frame_mul_localSection a ha l j z hl,
      F.overlap k l j z hk hl]
  calc
    F.localSection a k j z = (F.frame a k z)⁻¹ * F.ratio k j z := rfl
    _ = (F.frame a k z)⁻¹ * (F.frame a k z * F.localSection a l j z) := by rw [he]
    _ = F.localSection a l j z := by
      rw [← mul_assoc,PowerSeries.inv_mul_cancel _ (F.frame_unit a ha k z hk),one_mul]

include ha in
theorem localSection_constant (k j : ι) (z : ℂ) (hk : (p k).eval z ≠ 0) :
    PowerSeries.constantCoeff (F.localSection a k j z) = (p j).eval z := by
  simp only [localSection,map_mul,PowerSeries.constantCoeff_inv,
    F.frame_constant a ha k z hk,inv_inv,F.diagonal k j z hk]
  field_simp

include ha in
theorem localSection_analytic (k j : ι) (z : ℂ) (hk : (p k).eval z ≠ 0) :
    AnalyticSeriesAt (F.localSection a k j) z :=
  ((F.frame_analytic a k z hk).inv (F.frame_unit a ha k z hk)).mul (F.analytic k j z hk)

 

def active (z : ℂ) : ι := Classical.choose (F.basepoint_free z)

theorem active_nonzero (z : ℂ) : (p (F.active z)).eval z ≠ 0 :=
  Classical.choose_spec (F.basepoint_free z)

def sectionValue (j : ι) (z : ℂ) : PowerSeries ℂ := F.localSection a (F.active z) j z

include ha in
theorem sectionValue_eq (k j : ι) (z : ℂ) (hk : (p k).eval z ≠ 0) :
    F.sectionValue a j z = F.localSection a k j z :=
  F.localSection_overlap a ha (F.active z) k j z (F.active_nonzero z) hk

include ha in
theorem sectionValue_analytic (j : ι) (z : ℂ) : AnalyticSeriesAt (F.sectionValue a j) z := by
  intro n
  let k := F.active z
  have hk : (p k).eval z ≠ 0 := F.active_nonzero z
  apply (F.localSection_analytic a ha k j z hk n).congr
  have hnear : ∀ᶠ w in nhds z, (p k).eval w ≠ 0 := (p k).continuous.continuousAt.eventually_ne hk
  filter_upwards [hnear] with w hw
  exact congrArg (PowerSeries.coeff n) (F.sectionValue_eq a ha k j w hw).symm

include ha in
theorem sectionValue_constant (j : ι) (z : ℂ) :
    PowerSeries.constantCoeff (F.sectionValue a j z) = (p j).eval z :=
  F.localSection_constant a ha (F.active z) j z (F.active_nonzero z)

 

def sectionSeries (j : ι) : PowerSeries (ℂ → ℂ) :=
  PowerSeries.mk (fun n z => PowerSeries.coeff n (F.sectionValue a j z))

include ha in
theorem sectionSeries_entire (j : ι) (n : ℕ) :
    Differentiable ℂ (PowerSeries.coeff n (F.sectionSeries a j)) := by
  intro z
  simpa only [sectionSeries,PowerSeries.coeff_mk] using
    (F.sectionValue_analytic a ha j z n).differentiableAt

end ChartData

open SplitTangent.DiagonalRationality

 

structure TwoChartData {ι : Type*} [Fintype ι] (d : ℕ) (p q : ι → ℂ[X]) where
  finite : ChartData p
  infinity : ChartData q
  diagonal_transition : ∀ z : ℂ, z ≠ 0 → ∀ j,
    (p j).eval z = z^d * (q j).eval z⁻¹
  overlap : ∀ k j z, z ≠ 0 → (p k).eval z ≠ 0 →
    finite.ratio k j z = PowerSeries.subst (reciprocalNormal z) (infinity.ratio k j z⁻¹)

namespace TwoChartData
variable {ι : Type*} [Fintype ι] {d : ℕ} {p q : ι → ℂ[X]} (F : TwoChartData d p q)
  (a b : ι → ℂ[X]) (ha : ∑ i, a i * p i = 1) (hb : ∑ i, b i * q i = 1)

include F in
theorem infinity_nonzero (z : ℂ) (hz : z ≠ 0) (k : ι) (hk : (p k).eval z ≠ 0) :
    (q k).eval z⁻¹ ≠ 0 := by
  rw [F.diagonal_transition z hz k] at hk
  exact (mul_ne_zero_iff.mp hk).2

 

def normalizedTransition (z : ℂ) : PowerSeries ℂ :=
  (F.finite.frame a (F.finite.active z) z)⁻¹ *
    PowerSeries.subst (reciprocalNormal z) (F.infinity.frame b (F.finite.active z) z⁻¹)

include ha hb in
theorem normalizedTransition_constant (z : ℂ) (hz : z ≠ 0) :
    PowerSeries.constantCoeff (F.normalizedTransition a b z) = z ^ (d : ℤ) := by
  let k := F.finite.active z
  have hk : (p k).eval z ≠ 0 := F.finite.active_nonzero z
  have hq := F.infinity_nonzero z hz k hk
  change PowerSeries.constantCoeff ((F.finite.frame a k z)⁻¹ *
    PowerSeries.subst (reciprocalNormal z) (F.infinity.frame b k z⁻¹)) = _
  rw [map_mul,PowerSeries.constantCoeff_inv,
    constant_subst (reciprocalNormal_constant z),F.finite.frame_constant a ha k z hk,
    F.infinity.frame_constant b hb k z⁻¹ hq,inv_inv,F.diagonal_transition z hz k,
    mul_assoc,mul_inv_cancel₀ hq,mul_one,zpow_natCast]

 
theorem sectionSeries_evaluate {r : ι → ℂ[X]} (G : ChartData r)
    (c : ι → ℂ[X]) (j : ι) (z : ℂ) :
    evaluateCoefficients z (G.sectionSeries c j) = G.sectionValue c j z := by
  ext n
  simp only [coeff_evaluateCoefficients,ChartData.sectionSeries,PowerSeries.coeff_mk]

include ha hb in
theorem normalized_gluing (j : ι) (z : ℂ) (hz : z ≠ 0) :
    evaluateCoefficients z (F.finite.sectionSeries a j) =
      F.normalizedTransition a b z * PowerSeries.subst (reciprocalNormal z)
        (evaluateCoefficients z⁻¹ (F.infinity.sectionSeries b j)) := by
  let k := F.finite.active z
  have hk : (p k).eval z ≠ 0 := F.finite.active_nonzero z
  have hq := F.infinity_nonzero z hz k hk
  rw [sectionSeries_evaluate,sectionSeries_evaluate,
    F.finite.sectionValue_eq a ha k j z hk,F.infinity.sectionValue_eq b hb k j z⁻¹ hq]
  change (F.finite.frame a k z)⁻¹ * F.finite.ratio k j z =
    ((F.finite.frame a k z)⁻¹ * PowerSeries.subst (reciprocalNormal z)
      (F.infinity.frame b k z⁻¹)) * PowerSeries.subst (reciprocalNormal z)
        (F.infinity.localSection b k j z⁻¹)
  rw [mul_assoc,← PowerSeries.subst_mul (reciprocalNormal_hasSubst z),
    F.infinity.frame_mul_localSection b hb k j z⁻¹ hq,← F.overlap k j z hz hk]

 

def normalizedSection (j : ι) : formalSections (F.normalizedTransition a b) :=
  ⟨(F.finite.sectionSeries a j,F.infinity.sectionSeries b j),
    F.finite.sectionSeries_entire a ha j,F.infinity.sectionSeries_entire b hb j,
    F.normalized_gluing a b ha hb j⟩

include ha hb in
theorem normalizedSection_constant (j : ι) (z : ℂ) :
    PowerSeries.constantCoeff (F.normalizedSection a b ha hb j).val.1 z = (p j).eval z := by
  change PowerSeries.constantCoeff (F.finite.sectionSeries a j) z = _
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simpa only [ChartData.sectionSeries,PowerSeries.coeff_mk,
    PowerSeries.coeff_zero_eq_constantCoeff] using F.finite.sectionValue_constant a ha j z

end TwoChartData
end

open SplitTangent.DiagonalRationality
namespace ChartData
variable {ι : Type*} [Fintype ι] {p : ι → ℂ[X]} (F : ChartData p)
  (a : ι → ℂ[X]) (ha : ∑ i, a i * p i = 1)

include ha in
theorem sectionValue_ratio (k j : ι) (z : ℂ) (hk : (p k).eval z ≠ 0) :
    F.sectionValue a j z * (F.sectionValue a k z)⁻¹ = F.ratio k j z := by
  have hs : PowerSeries.constantCoeff (F.sectionValue a k z) ≠ 0 := by
    rw [F.sectionValue_constant a ha k z]; exact hk
  have hmul : F.sectionValue a j z = F.ratio k j z * F.sectionValue a k z := by
    rw [F.sectionValue_eq a ha k j z hk,F.sectionValue_eq a ha k k z hk,
      localSection,localSection,F.identity k z hk,mul_one,mul_comm]
  rw [hmul,mul_assoc,PowerSeries.mul_inv_cancel _ hs,mul_one]

end ChartData
end SplitTangent.FormalProjective

namespace SplitTangent.DiagonalRationality

 

theorem simultaneous_reconstruction_on_diagonal_patch {ι : Type*} [Fintype ι]
    {T : ℂ → PowerSeries ℂ} (d : ℕ)
    (hT : ∀ z : ℂ, z ≠ 0 → PowerSeries.constantCoeff (T z) = z ^ (d : ℤ))
    (s : formalSections T) (t : ι → formalSections T)
    (hs : ∃ z : ℂ, PowerSeries.constantCoeff s.val.1 z ≠ 0) :
    ∃ (a b : ι → BiCoefficients (4*(d+1))) (r : ι → ℕ)
      (A B : ι → Polynomial (ℂ → ℂ)) (U : Set ℂ),
      IsOpen U ∧ U.Nonempty ∧
      (∀ i, b i ≠ 0 ∧ normalPolynomial (4*(d+1)) (a i) = Polynomial.X ^ r i * A i ∧
        normalPolynomial (4*(d+1)) (b i) = Polynomial.X ^ r i * B i) ∧
      ∀ z ∈ U, PowerSeries.constantCoeff s.val.1 z ≠ 0 ∧ ∀ i,
        (B i).coeff 0 z ≠ 0 ∧
        AnalyticAt ℂ (fun w => -polynomialEvaluation (A i) w / polynomialEvaluation (B i) w) (z,0) ∧
        HasFPowerSeriesAt
          (fun v => -polynomialEvaluation (A i) (z,v) / polynomialEvaluation (B i) (z,v))
          (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n
            (evaluateCoefficients z (t i).val.1 * (evaluateCoefficients z s.val.1)⁻¹))) 0 := by
  classical
  choose a b r A B z hb ha hbP hAD hBD hBz hsZ hq hc using
    fun i => exists_convergent_rational_quotient d hT s (t i) hs
  have hsD : Differentiable ℂ (PowerSeries.constantCoeff s.val.1) := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using s.property.1 0
  obtain ⟨w,hsw,hw⟩ := exists_common_nonzero_finset Finset.univ
    (fun i => (B i).coeff 0) (PowerSeries.constantCoeff s.val.1)
    (fun i _ => hBD i 0) hsD
    (fun i _ he => hBz i (congrFun he (z i))) hs
  let H : ℂ → ℂ := fun z => PowerSeries.constantCoeff s.val.1 z * ∏ i, (B i).coeff 0 z
  have hHD : Differentiable ℂ H := hsD.mul (Differentiable.fun_finsetProd (fun i _ => hBD i 0))
  let U : Set ℂ := {z | H z ≠ 0}
  refine ⟨a,b,r,A,B,U,isOpen_ne_fun hHD.continuous continuous_const,
    ⟨w,mul_ne_zero hsw (Finset.prod_ne_zero_iff.mpr hw)⟩,
    fun i => ⟨hb i,ha i,hbP i⟩,?_⟩
  intro z hz
  have hz' : PowerSeries.constantCoeff s.val.1 z ≠ 0 ∧ ∀ i, (B i).coeff 0 z ≠ 0 := by
    simpa only [U,H,mem_ofPred_eq,mul_ne_zero_iff,Finset.prod_ne_zero_iff,Finset.mem_univ,true_implies] using hz
  refine ⟨hz'.1,fun i => ⟨hz'.2 i,polynomial_quotient_analytic (hAD i) (hBD i) (hz'.2 i),
    hc i z (hz'.2 i) hz'.1⟩⟩

end SplitTangent.DiagonalRationality

namespace SplitTangent.FormalProjective
open SplitTangent.DiagonalRationality

 

theorem reconstruct_projective_map {ι : Type*} [Fintype ι] {d : ℕ}
    {p q : ι → ℂ[X]} (F : TwoChartData d p q)
    (a b : ι → ℂ[X]) (ha : ∑ i, a i * p i = 1) (hb : ∑ i, b i * q i = 1) :
    ∃ (k : ι) (A B : ι → Polynomial (ℂ → ℂ)) (U : Set ℂ),
      IsOpen U ∧ U.Nonempty ∧ ∀ z ∈ U, (p k).eval z ≠ 0 ∧ ∀ j,
        (B j).coeff 0 z ≠ 0 ∧
        AnalyticAt ℂ (fun w => -polynomialEvaluation (A j) w / polynomialEvaluation (B j) w) (z,0) ∧
        HasFPowerSeriesAt
          (fun v => -polynomialEvaluation (A j) (z,v) / polynomialEvaluation (B j) (z,v))
          (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n
            (F.finite.ratio k j z))) 0 := by
  obtain ⟨k,hk⟩ := F.finite.basepoint_free 0
  let s := F.normalizedSection a b ha hb k
  let t := F.normalizedSection a b ha hb
  have hs : ∃ z : ℂ, PowerSeries.constantCoeff s.val.1 z ≠ 0 := by
    exact ⟨0, by simpa only [s,F.normalizedSection_constant a b ha hb k 0] using hk⟩
  obtain ⟨A',B',r,A,B,U,hU,hUn,_,h⟩ := simultaneous_reconstruction_on_diagonal_patch d
    (F.normalizedTransition_constant a b ha hb) s t hs
  refine ⟨k,A,B,U,hU,hUn,?_⟩
  intro z hz
  obtain ⟨hsk,hr⟩ := h z hz
  have hp : (p k).eval z ≠ 0 := by
    simpa only [s,F.normalizedSection_constant a b ha hb k z] using hsk
  refine ⟨hp,fun j => ⟨(hr j).1,(hr j).2.1,?_⟩⟩
  have hq : evaluateCoefficients z (t j).val.1 * (evaluateCoefficients z s.val.1)⁻¹ =
      F.finite.ratio k j z := by
    change evaluateCoefficients z (F.finite.sectionSeries a j) *
      (evaluateCoefficients z (F.finite.sectionSeries a k))⁻¹ = _
    rw [TwoChartData.sectionSeries_evaluate,TwoChartData.sectionSeries_evaluate,
      F.finite.sectionValue_ratio a ha k j z hp]
  simpa only [hq] using (hr j).2.2

end SplitTangent.FormalProjective

end ReconstructionImports
open Set Filter Topology

namespace SplitTangent.HolomorphicJets
section
open SplitTangent.DiagonalRationality

 
def normalDeriv (H : ℂ × ℂ → ℂ) : ℂ × ℂ → ℂ :=
  fun w => fderiv ℂ H w (0,1)

def normalIterate : ℕ → (ℂ × ℂ → ℂ) → (ℂ × ℂ → ℂ)
  | 0, H => H
  | n+1, H => normalDeriv (normalIterate n H)

theorem normalDeriv_analytic {H : ℂ × ℂ → ℂ} {w : ℂ × ℂ}
    (hH : AnalyticAt ℂ H w) : AnalyticAt ℂ (normalDeriv H) w := by
  exact ((ContinuousLinearMap.apply ℂ ℂ ((0,1) : ℂ × ℂ)).analyticAt _).comp hH.fderiv

theorem normalIterate_analytic {H : ℂ × ℂ → ℂ} {w : ℂ × ℂ}
    (hH : AnalyticAt ℂ H w) (n : ℕ) : AnalyticAt ℂ (normalIterate n H) w := by
  induction n with
  | zero => exact hH
  | succ n ih => exact normalDeriv_analytic ih

theorem normalDeriv_eq {H : ℂ × ℂ → ℂ} {w : ℂ × ℂ}
    (hH : AnalyticAt ℂ H w) :
    deriv (fun v => H (w.1,v)) w.2 = normalDeriv H w := by
  have hd := hH.differentiableAt.hasFDerivAt.comp_hasDerivAt w.2
    ((hasDerivAt_const w.2 w.1).prodMk (hasDerivAt_id w.2))
  exact hd.deriv

theorem normalIterate_eq {H : ℂ × ℂ → ℂ} {w : ℂ × ℂ}
    (hH : AnalyticAt ℂ H w) (n : ℕ) :
    iteratedDeriv n (fun v => H (w.1,v)) w.2 = normalIterate n H w := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (fun v => H (w.1,v)) =ᶠ[nhds w.2]
        (fun v => normalIterate n H (w.1,v)) := by
      have hc : ContinuousAt (fun v : ℂ => (w.1,v)) w.2 := by fun_prop
      filter_upwards [hc hH.eventually_analyticAt] with v hv
      exact ih hv
    rw [he.deriv_eq]
    exact normalDeriv_eq (normalIterate_analytic hH n)

 

theorem normalCoefficient_analytic {H : ℂ × ℂ → ℂ} {u : ℂ}
    (hH : AnalyticAt ℂ H (u,0)) (n : ℕ) :
    AnalyticAt ℂ (fun z => PowerSeries.coeff n (taylorSeries (fun v => H (z,v)))) u := by
  have hN0 : AnalyticAt ℂ (fun z => normalIterate n H (z,0)) u :=
    AnalyticAt.comp (f := fun z : ℂ => (z,(0 : ℂ))) (x := u)
      (normalIterate_analytic hH n) (analyticAt_id.prod analyticAt_const)
  have hN : AnalyticAt ℂ (fun z => normalIterate n H (z,0) / (n.factorial : ℂ)) u :=
    hN0.div_const
  apply hN.congr
  have hc : ContinuousAt (fun z : ℂ => (z,(0 : ℂ))) u := by fun_prop
  filter_upwards [hc hH.eventually_analyticAt] with z hz
  simp only [coeff_taylorSeries,normalIterate_eq hz n]

variable {σ : Type*} [Fintype σ]

 
def jetPolynomial (f : ℕ → σ → ℂ) (n : ℕ) (v : ℂ) : σ → ℂ :=
  fun i => ∑ k ∈ Finset.range (n+1), v^k * f k i

omit [Fintype σ] in
@[simp] theorem jetPolynomial_zero (f : ℕ → σ → ℂ) (n : ℕ) :
    jetPolynomial f n 0 = f 0 := by
  funext i
  unfold jetPolynomial
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0; simp [zero_pow hk0]
  · intro h; exact (h (Finset.mem_range.mpr (by omega))).elim

omit [Fintype σ] in
theorem jetPolynomial_congr {f g : ℕ → σ → ℂ} {n : ℕ}
    (h : ∀ k, k ≤ n → f k = g k) : jetPolynomial f n = jetPolynomial g n := by
  funext v i
  apply Finset.sum_congr rfl
  intro k hk
  rw [h k (by have := Finset.mem_range.mp hk; omega)]

 

def composeCoefficient (h : (σ → ℂ) → ℂ) (f : ℕ → σ → ℂ) (n : ℕ) : ℂ :=
  PowerSeries.coeff n (taylorSeries (fun v => h (jetPolynomial f n v)))

omit [Fintype σ] in
theorem composeCoefficient_causal (h : (σ → ℂ) → ℂ) {f g : ℕ → σ → ℂ} {n : ℕ}
    (hfg : ∀ k, k ≤ n → f k = g k) :
    composeCoefficient h f n = composeCoefficient h g n := by
  rw [composeCoefficient,composeCoefficient,jetPolynomial_congr hfg]

 

theorem jetPolynomial_analytic {f : ℕ → ℂ → σ → ℂ} {u v : ℂ} (n : ℕ)
    (hf : ∀ k, k ≤ n → ∀ i, AnalyticAt ℂ (fun z => f k z i) u) :
    AnalyticAt ℂ (fun w : ℂ × ℂ => jetPolynomial (fun k => f k w.1) n w.2) (u,v) := by
  apply AnalyticAt.pi
  intro i
  apply Finset.analyticAt_fun_sum
  intro k hk
  have hf' := (hf k (by have := Finset.mem_range.mp hk; omega) i).comp
    (show AnalyticAt ℂ (fun w : ℂ × ℂ => w.1) (u,v) from analyticAt_fst)
  exact (analyticAt_snd.pow k).fun_mul hf'

 

theorem composeCoefficient_analytic {h : (σ → ℂ) → ℂ} {f : ℕ → ℂ → σ → ℂ}
    {u : ℂ} (n : ℕ)
    (hf : ∀ k, k ≤ n → ∀ i, AnalyticAt ℂ (fun z => f k z i) u)
    (hh : AnalyticAt ℂ h (f 0 u)) :
    AnalyticAt ℂ (fun z => composeCoefficient h (fun k => f k z) n) u := by
  unfold composeCoefficient
  refine normalCoefficient_analytic (H := fun w : ℂ × ℂ =>
    h (jetPolynomial (fun k => f k w.1) n w.2)) ?_ n
  exact hh.comp_of_eq (jetPolynomial_analytic n hf) (jetPolynomial_zero _ n)

end

section
open SplitTangent.DiagonalRationality
variable {σ : Type*} [Fintype σ]

 

def jetSeries (f : ℕ → σ → ℂ) : FormalMultilinearSeries ℂ ℂ (σ → ℂ) :=
  FormalMultilinearSeries.pi (fun i => FormalMultilinearSeries.ofScalars ℂ (fun n => f n i))

omit [Fintype σ] in
@[simp] theorem jetSeries_apply (f : ℕ → σ → ℂ) (n : ℕ) (v : Fin n → ℂ) (i : σ) :
    jetSeries f n v i = f n i * ∏ j, v j := by
  simp [jetSeries,FormalMultilinearSeries.pi,FormalMultilinearSeries.ofScalars,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, Fin.prod_ofFn]

def polynomialJet (f : ℕ → σ → ℂ) (n : ℕ) (i : σ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n+1), Polynomial.monomial k (f k i)

omit [Fintype σ] in
@[simp] theorem polynomialJet_coeff (f : ℕ → σ → ℂ) (n k : ℕ) (i : σ) :
    (polynomialJet f n i).coeff k = if k ≤ n then f k i else 0 := by
  classical
  simp [polynomialJet,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,
    Finset.mem_range]

omit [Fintype σ] in
theorem polynomialJet_eval (f : ℕ → σ → ℂ) (n : ℕ) (i : σ) (v : ℂ) :
    (polynomialJet f n i).eval v = jetPolynomial f n v i := by
  simp [polynomialJet,jetPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_monomial,mul_comm]

theorem jetPolynomial_hasSeries (f : ℕ → σ → ℂ) (n : ℕ) :
    HasFPowerSeriesAt (jetPolynomial f n)
      (jetSeries (fun k i => if k ≤ n then f k i else 0)) 0 := by
  apply HasFPowerSeriesAt.pi
  intro i
  have h := hasFPowerSeries_taylorSeries (polynomial_analyticAt (polynomialJet f n i) 0)
  rw [taylorSeries_polynomial] at h
  simpa only [Polynomial.coeff_coe,polynomialJet_coeff,polynomialJet_eval] using h

 
theorem formalComposition_causal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (q : FormalMultilinearSeries ℂ E G) {p p' : FormalMultilinearSeries ℂ ℂ E} {n : ℕ}
    (h : ∀ k, k ≤ n → p k = p' k) : (q.comp p) n = (q.comp p') n := by
  unfold FormalMultilinearSeries.comp
  apply Finset.sum_congr rfl
  intro c _
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [FormalMultilinearSeries.compAlongComposition_apply]
  congr 1
  funext i
  exact congrArg (fun L => L (v ∘ c.embedding i)) (h (c.blocksFun i) (c.blocksFun_le i))

 

theorem composeCoefficient_eq_formal {h : (σ → ℂ) → ℂ} (f : ℕ → σ → ℂ)
    {q : FormalMultilinearSeries ℂ (σ → ℂ) ℂ}
    (hq : HasFPowerSeriesAt h q (f 0)) (n : ℕ) :
    composeCoefficient h f n = (q.comp (jetSeries f)) n (fun _ => 1) := by
  have hq' : HasFPowerSeriesAt h q (jetPolynomial f n 0) := by
    simpa only [jetPolynomial_zero] using hq
  have hc := hq'.comp (jetPolynomial_hasSeries f n)
  have ht := hasFPowerSeries_taylorSeries hc.analyticAt
  have he := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p n (fun _ => 1))
    (ht.eq_formalMultilinearSeries hc)
  have heq : (q.comp (jetSeries (fun k i => if k ≤ n then f k i else 0))) n =
      (q.comp (jetSeries f)) n := by
    apply formalComposition_causal
    intro k hk
    ext v
    simp only [jetSeries_apply,ite_eq_left hk]
  rw [heq] at he
  simpa [composeCoefficient,FormalMultilinearSeries.ofScalars,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, Function.comp_def] using he

 

theorem composeCoefficient_eq_laterJet {h : (σ → ℂ) → ℂ} (f : ℕ → σ → ℂ)
    (hh : AnalyticAt ℂ h (f 0)) {n m : ℕ} (hnm : n ≤ m) :
    composeCoefficient h f n =
      PowerSeries.coeff n (taylorSeries (fun v => h (jetPolynomial f m v))) := by
  obtain ⟨q,hq⟩ := hh
  have hc := (show HasFPowerSeriesAt h q (jetPolynomial f m 0) by
    simpa only [jetPolynomial_zero] using hq).comp (jetPolynomial_hasSeries f m)
  have ht := hasFPowerSeries_taylorSeries hc.analyticAt
  have he := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p n (fun _ => 1))
    (ht.eq_formalMultilinearSeries hc)
  have heq : (q.comp (jetSeries (fun k i => if k ≤ m then f k i else 0))) n =
      (q.comp (jetSeries f)) n := by
    apply formalComposition_causal
    intro k hk
    ext v
    simp only [jetSeries_apply,ite_eq_left (hk.trans hnm)]
  rw [heq] at he
  rw [composeCoefficient_eq_formal f hq n]
  simpa [FormalMultilinearSeries.ofScalars,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, Function.comp_def] using he.symm

end
section
open SplitTangent.DiagonalRationality
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

def composeJet (H : (σ → ℂ) → τ → ℂ) (f : ℕ → σ → ℂ) : ℕ → τ → ℂ :=
  fun n i => composeCoefficient (fun x => H x i) f n

omit [Fintype τ] in
omit [Fintype σ] in
@[simp] theorem composeJet_zero (H : (σ → ℂ) → τ → ℂ) (f : ℕ → σ → ℂ) :
    composeJet H f 0 = H (f 0) := by
  funext i
  simp [composeJet,composeCoefficient,coeff_taylorSeries]

 

theorem composeJet_eq_formal (H : (σ → ℂ) → τ → ℂ) (f : ℕ → σ → ℂ)
    {q : FormalMultilinearSeries ℂ (σ → ℂ) (τ → ℂ)}
    (hq : HasFPowerSeriesAt H q (f 0)) :
    jetSeries (composeJet H f) = q.comp (jetSeries f) := by
  funext n
  have hc := (show HasFPowerSeriesAt H q (jetPolynomial f n 0) by
    simpa only [jetPolynomial_zero] using hq).comp (jetPolynomial_hasSeries f n)
  have ht : HasFPowerSeriesAt (H ∘ jetPolynomial f n)
      (jetSeries (fun k i => PowerSeries.coeff k
        (taylorSeries (fun v => H (jetPolynomial f n v) i)))) 0 := by
    apply HasFPowerSeriesAt.pi
    intro i
    exact hasFPowerSeries_taylorSeries (analyticAt_pi_iff.mp hc.analyticAt i)
  have he := congrArg (fun p : FormalMultilinearSeries ℂ ℂ (τ → ℂ) => p n)
    (ht.eq_formalMultilinearSeries hc)
  have heq : (q.comp (jetSeries (fun k i => if k ≤ n then f k i else 0))) n =
      (q.comp (jetSeries f)) n := by
    apply formalComposition_causal
    intro k hk
    ext v
    simp [jetSeries_apply,hk]
  rw [heq] at he
  exact he

 

theorem composeCoefficient_assoc (H : (σ → ℂ) → τ → ℂ)
    (h : (τ → ℂ) → ℂ) (f : ℕ → σ → ℂ)
    (hH : AnalyticAt ℂ H (f 0)) (hh : AnalyticAt ℂ h (H (f 0))) (n : ℕ) :
    composeCoefficient h (composeJet H f) n =
      composeCoefficient (h ∘ H) f n := by
  obtain ⟨q,hq⟩ := hH
  obtain ⟨r,hr⟩ := hh
  have hr' : HasFPowerSeriesAt h r (composeJet H f 0) := by
    simpa only [composeJet_zero] using hr
  rw [composeCoefficient_eq_formal _ hr',composeJet_eq_formal H f hq,
    ← FormalMultilinearSeries.comp_assoc,composeCoefficient_eq_formal _ (hr.comp hq)]

end
section
open SplitTangent.DiagonalRationality

 

theorem taylorSeries_deriv (h : ℂ → ℂ) :
    taylorSeries (deriv h) = PowerSeries.derivative (taylorSeries h) := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_taylorSeries,PowerSeries.coeff_derivative]
  rw [← iteratedDeriv_succ']
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  have hn : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

 
def directionDeriv (a : ℂ × ℂ) (H : ℂ × ℂ → ℂ) : ℂ × ℂ → ℂ :=
  fun w => fderiv ℂ H w a

theorem directionDeriv_analytic {H : ℂ × ℂ → ℂ} {w : ℂ × ℂ}
    (hH : AnalyticAt ℂ H w) (a : ℂ × ℂ) :
    AnalyticAt ℂ (directionDeriv a H) w := by
  exact ((ContinuousLinearMap.apply ℂ ℂ a).analyticAt _).comp hH.fderiv

 

theorem directionDeriv_comm {H : ℂ × ℂ → ℂ} {w : ℂ × ℂ}
    (hH : AnalyticAt ℂ H w) (a b : ℂ × ℂ) :
    directionDeriv a (directionDeriv b H) w =
      directionDeriv b (directionDeriv a H) w := by
  unfold directionDeriv
  rw [fderiv_clm_apply hH.fderiv.differentiableAt (differentiableAt_const b),
    fderiv_clm_apply hH.fderiv.differentiableAt (differentiableAt_const a)]
  simpa using hH.contDiffAt.isSymmSndFDerivAt_of_omega a b

theorem directionDeriv_congr {H K : ℂ × ℂ → ℂ} {w : ℂ × ℂ}
    (h : H =ᶠ[nhds w] K) (a : ℂ × ℂ) : directionDeriv a H w = directionDeriv a K w := by
  exact congrArg (fun L => L a) (h.fderiv_eq (𝕜 := ℂ))

 
theorem normalIterate_directionDeriv {H : ℂ × ℂ → ℂ} {w : ℂ × ℂ}
    (hH : AnalyticAt ℂ H w) (a : ℂ × ℂ) (n : ℕ) :
    normalIterate n (directionDeriv a H) w = directionDeriv a (normalIterate n H) w := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    change directionDeriv (0,1) (normalIterate n (directionDeriv a H)) w = _
    have he : normalIterate n (directionDeriv a H) =ᶠ[nhds w]
        directionDeriv a (normalIterate n H) := by
      filter_upwards [hH.eventually_analyticAt] with z hz
      exact ih hz
    rw [directionDeriv_congr he]
    exact directionDeriv_comm (normalIterate_analytic hH n) (0,1) a

 
def tangentDeriv (H : ℂ × ℂ → ℂ) : ℂ × ℂ → ℂ := directionDeriv (1,0) H

theorem tangentDeriv_eq {H : ℂ × ℂ → ℂ} {w : ℂ × ℂ}
    (hH : AnalyticAt ℂ H w) :
    deriv (fun u => H (u,w.2)) w.1 = tangentDeriv H w := by
  exact (hH.differentiableAt.hasFDerivAt.comp_hasDerivAt w.1
    ((hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2))).deriv

 

theorem deriv_normalCoefficient {H : ℂ × ℂ → ℂ} {u : ℂ}
    (hH : AnalyticAt ℂ H (u,0)) (n : ℕ) :
    deriv (fun z => PowerSeries.coeff n (taylorSeries (fun v => H (z,v)))) u =
      PowerSeries.coeff n (taylorSeries (fun v => tangentDeriv H (u,v))) := by
  have he : (fun z => PowerSeries.coeff n (taylorSeries (fun v => H (z,v)))) =ᶠ[nhds u]
      (fun z => normalIterate n H (z,0) / (n.factorial : ℂ)) := by
    have hc : ContinuousAt (fun z : ℂ => (z,(0 : ℂ))) u := by fun_prop
    filter_upwards [hc hH.eventually_analyticAt] with z hz
    simp only [coeff_taylorSeries,normalIterate_eq hz n]
  rw [he.deriv_eq,deriv_div_const]
  rw [tangentDeriv_eq (normalIterate_analytic hH n),coeff_taylorSeries]
  change directionDeriv (1,0) (normalIterate n H) (u,0) / _ =
    iteratedDeriv n (fun v => directionDeriv (1,0) H (u,v)) 0 / _
  rw [normalIterate_eq (directionDeriv_analytic hH (1,0)),normalIterate_directionDeriv hH]

end
section
open SplitTangent.DiagonalRationality
variable {σ : Type*} [Fintype σ]

omit [Fintype σ] in
@[simp] theorem composeCoefficient_zero (f : ℕ → σ → ℂ) (n : ℕ) :
    composeCoefficient (fun _ => 0) f n = 0 := by
  simp [composeCoefficient]

omit [Fintype σ] in
@[simp] theorem composeCoefficient_coordinate (f : ℕ → σ → ℂ) (n : ℕ) (i : σ) :
    composeCoefficient (fun x => x i) f n = f n i := by
  unfold composeCoefficient
  simp_rw [← polynomialJet_eval]
  rw [taylorSeries_polynomial,Polynomial.coeff_coe,polynomialJet_coeff]
  simp

theorem composeCoefficient_add {h k : (σ → ℂ) → ℂ} (f : ℕ → σ → ℂ)
    (hh : AnalyticAt ℂ h (f 0)) (hk : AnalyticAt ℂ k (f 0)) (n : ℕ) :
    composeCoefficient (fun x => h x + k x) f n =
      composeCoefficient h f n + composeCoefficient k f n := by
  unfold composeCoefficient
  change PowerSeries.coeff n (taylorSeries ((h ∘ jetPolynomial f n) + (k ∘ jetPolynomial f n))) = _
  rw [taylorSeries_add]
  · exact map_add _ _ _
  · exact hh.comp_of_eq (jetPolynomial_hasSeries f n).analyticAt (jetPolynomial_zero ..)
  · exact hk.comp_of_eq (jetPolynomial_hasSeries f n).analyticAt (jetPolynomial_zero ..)

theorem composeCoefficient_mul {h k : (σ → ℂ) → ℂ} (f : ℕ → σ → ℂ)
    (hh : AnalyticAt ℂ h (f 0)) (hk : AnalyticAt ℂ k (f 0)) (n : ℕ) :
    composeCoefficient (fun x => h x * k x) f n =
      ∑ l ∈ Finset.range (n+1), composeCoefficient h f l * composeCoefficient k f (n-l) := by
  unfold composeCoefficient
  change PowerSeries.coeff n (taylorSeries ((h ∘ jetPolynomial f n) * (k ∘ jetPolynomial f n))) = _
  rw [taylorSeries_mul]
  · rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a (taylorSeries (h ∘ jetPolynomial f n)) *
        PowerSeries.coeff b (taylorSeries (k ∘ jetPolynomial f n))) n]
    apply Finset.sum_congr rfl
    intro l hl
    have hln : l ≤ n := by have := Finset.mem_range.mp hl; omega
    simp only [Function.comp_def]
    rw [← composeCoefficient_eq_laterJet f hh hln,
      ← composeCoefficient_eq_laterJet f hk (Nat.sub_le ..)]
    rfl
  · exact hh.comp_of_eq (jetPolynomial_hasSeries f n).analyticAt (jetPolynomial_zero ..)
  · exact hk.comp_of_eq (jetPolynomial_hasSeries f n).analyticAt (jetPolynomial_zero ..)

theorem composeCoefficient_sum {ι : Type*} (s : Finset ι)
    (h : ι → (σ → ℂ) → ℂ) (f : ℕ → σ → ℂ)
    (hh : ∀ i ∈ s, AnalyticAt ℂ (h i) (f 0)) (n : ℕ) :
    composeCoefficient (fun x => ∑ i ∈ s, h i x) f n =
      ∑ i ∈ s, composeCoefficient (h i) f n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    rw [composeCoefficient_add f (hh a (by simp))
      (Finset.analyticAt_fun_sum s (fun i hi => hh i (by simp [hi]))) n,
      ih (fun i hi => hh i (by simp [hi]))]

end
section
open SplitTangent.DiagonalRationality
variable {σ : Type*} [Fintype σ]

 
def analyticJet (g : ℂ → σ → ℂ) : ℕ → σ → ℂ :=
  fun n i => PowerSeries.coeff n (taylorSeries (fun z => g z i))

omit [Fintype σ] in
@[simp] theorem analyticJet_zero (g : ℂ → σ → ℂ) : analyticJet g 0 = g 0 := by
  funext i
  simp [analyticJet,coeff_taylorSeries]

theorem analyticJet_hasSeries {g : ℂ → σ → ℂ} (hg : AnalyticAt ℂ g 0) :
    HasFPowerSeriesAt g (jetSeries (analyticJet g)) 0 := by
  apply HasFPowerSeriesAt.pi
  intro i
  exact hasFPowerSeries_taylorSeries (analyticAt_pi_iff.mp hg i)

 

theorem composeCoefficient_analyticJet {g : ℂ → σ → ℂ} {h : (σ → ℂ) → ℂ}
    (hg : AnalyticAt ℂ g 0) (hh : AnalyticAt ℂ h (g 0)) (n : ℕ) :
    composeCoefficient h (analyticJet g) n = PowerSeries.coeff n (taylorSeries (h ∘ g)) := by
  obtain ⟨q,hq⟩ := hh
  have hq' : HasFPowerSeriesAt h q (analyticJet g 0) := by simpa using hq
  rw [composeCoefficient_eq_formal _ hq']
  have hc := hq.comp (analyticJet_hasSeries hg)
  have ht := hasFPowerSeries_taylorSeries hc.analyticAt
  have he := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n)
    (ht.eq_formalMultilinearSeries hc)
  exact he.symm.trans (FormalMultilinearSeries.coeff_ofScalars
    (p := fun k => PowerSeries.coeff k (taylorSeries (h ∘ g))) (n := n))

theorem taylorSeries_sum {ι : Type*} (s : Finset ι) (h : ι → ℂ → ℂ)
    (hh : ∀ i ∈ s, AnalyticAt ℂ (h i) 0) :
    taylorSeries (fun z => ∑ i ∈ s, h i z) = ∑ i ∈ s, taylorSeries (h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    change taylorSeries (h a + (fun z => ∑ i ∈ s, h i z)) = _
    rw [taylorSeries_add (hh a (by simp))
      (Finset.analyticAt_fun_sum s (fun i hi => hh i (by simp [hi]))),
      ih (fun i hi => hh i (by simp [hi]))]

 
def coordinatePartial [DecidableEq σ] (h : (σ → ℂ) → ℂ) (j : σ) (x : σ → ℂ) : ℂ :=
  fderiv ℂ h x (Pi.single j 1)

theorem partial_analytic [DecidableEq σ] {h : (σ → ℂ) → ℂ} {x : σ → ℂ}
    (hh : AnalyticAt ℂ h x) (j : σ) : AnalyticAt ℂ (coordinatePartial h j) x := by
  exact ((ContinuousLinearMap.apply ℂ ℂ (Pi.single j (1 : ℂ))).analyticAt _).comp hh.fderiv

theorem linearMap_eq_sum [DecidableEq σ] (L : (σ → ℂ) →L[ℂ] ℂ) (v : σ → ℂ) :
    L v = ∑ j, L (Pi.single j 1) * v j := by
  have hv : v = ∑ j, v j • Pi.single j (1 : ℂ) := by
    funext i
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _; ring

theorem deriv_comp_eq_sum [DecidableEq σ] {h : (σ → ℂ) → ℂ} {g : ℂ → σ → ℂ} {z : ℂ}
    (hh : DifferentiableAt ℂ h (g z)) (hg : DifferentiableAt ℂ g z) :
    deriv (h ∘ g) z = ∑ j, coordinatePartial h j (g z) * deriv (fun w => g w j) z := by
  rw [(hh.hasFDerivAt.comp_hasDerivAt z hg.hasDerivAt).deriv,linearMap_eq_sum,
    deriv_pi (fun i => (differentiableAt_pi.mp hg i))]
  rfl

 
theorem taylor_deriv_comp [DecidableEq σ] {g : ℂ → σ → ℂ} {h : (σ → ℂ) → ℂ}
    (hg : AnalyticAt ℂ g 0) (hh : AnalyticAt ℂ h (g 0)) (n : ℕ) :
    PowerSeries.coeff n (taylorSeries (deriv (h ∘ g))) =
      ∑ j, ∑ k ∈ Finset.range (n+1),
        PowerSeries.coeff k (taylorSeries (coordinatePartial h j ∘ g)) *
        PowerSeries.coeff (n-k) (taylorSeries (deriv (fun z => g z j))) := by
  have he : deriv (h ∘ g) =ᶠ[nhds 0]
      (fun z => ∑ j, coordinatePartial h j (g z) * deriv (fun w => g w j) z) := by
    filter_upwards [hg.eventually_analyticAt,hg.continuousAt hh.eventually_analyticAt] with z hz hhz
    exact deriv_comp_eq_sum hhz.differentiableAt hz.differentiableAt
  rw [taylorSeries_congr he,taylorSeries_sum]
  · simp only [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show (fun z => coordinatePartial h j (g z) * deriv (fun w => g w j) z) =
      (coordinatePartial h j ∘ g) * deriv (fun w => g w j) from rfl,
      taylorSeries_mul ((partial_analytic hh j).comp hg) (analyticAt_pi_iff.mp hg j).deriv,
      PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => PowerSeries.coeff a (taylorSeries (coordinatePartial h j ∘ g)) *
          PowerSeries.coeff b (taylorSeries (deriv (fun z => g z j)))) n]
  · intro j _
    exact ((partial_analytic hh j).comp hg).fun_mul (analyticAt_pi_iff.mp hg j).deriv

 

theorem composeCoefficient_normal_chain [DecidableEq σ] {h : (σ → ℂ) → ℂ}
    (f : ℕ → σ → ℂ) (hh : AnalyticAt ℂ h (f 0)) (n : ℕ) :
    (n+1 : ℂ) * composeCoefficient h f (n+1) =
      ∑ j, ∑ k ∈ Finset.range (n+1),
        composeCoefficient (coordinatePartial h j) f k * (((n-k+1 : ℕ) : ℂ) * f (n-k+1) j) := by
  have hg := (jetPolynomial_hasSeries f (n+1)).analyticAt
  have hh' : AnalyticAt ℂ h (jetPolynomial f (n+1) 0) := by simpa using hh
  have he := taylor_deriv_comp hg hh' n
  rw [taylorSeries_deriv,PowerSeries.coeff_derivative] at he
  rw [mul_comm] at he
  change (n+1 : ℂ) * composeCoefficient h f (n+1) = _ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
  have hp := composeCoefficient_eq_laterJet f (partial_analytic hh j) (hkn.trans (Nat.le_succ n))
  simp only [Function.comp_def] at hp ⊢
  rw [← hp]
  congr 1
  rw [taylorSeries_deriv,PowerSeries.coeff_derivative]
  simp_rw [← polynomialJet_eval]
  rw [taylorSeries_polynomial,Polynomial.coeff_coe,polynomialJet_coeff,ite_eq_left (by omega)]
  push_cast
  ring

end
section
open SplitTangent.DiagonalRationality
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

 
theorem tangentDeriv_comp {h : (σ → ℂ) → ℂ} {F : ℂ × ℂ → σ → ℂ} {w : ℂ × ℂ}
    (hh : AnalyticAt ℂ h (F w)) (hF : AnalyticAt ℂ F w) :
    tangentDeriv (h ∘ F) w =
      ∑ j, coordinatePartial h j (F w) * tangentDeriv (fun z => F z j) w := by
  have hFs : AnalyticAt ℂ (fun z => F (z,w.2)) w.1 :=
    AnalyticAt.comp (f := fun z : ℂ => (z,w.2)) hF
      (analyticAt_id.prod analyticAt_const)
  have he := deriv_comp_eq_sum hh.differentiableAt hFs.differentiableAt
  change deriv (fun z => (h ∘ F) (z,w.2)) w.1 = _ at he
  rw [tangentDeriv_eq (hh.comp hF)] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro j _
  rw [tangentDeriv_eq (analyticAt_pi_iff.mp hF j)]

 
theorem taylor_tangent_comp {h : (σ → ℂ) → ℂ} {F : ℂ × ℂ → σ → ℂ} {u : ℂ}
    (hh : AnalyticAt ℂ h (F (u,0))) (hF : AnalyticAt ℂ F (u,0)) (n : ℕ) :
    PowerSeries.coeff n (taylorSeries (fun v => tangentDeriv (h ∘ F) (u,v))) =
      ∑ j, ∑ k ∈ Finset.range (n+1),
        PowerSeries.coeff k (taylorSeries (fun v => coordinatePartial h j (F (u,v)))) *
        PowerSeries.coeff (n-k) (taylorSeries (fun v => tangentDeriv (fun z => F z j) (u,v))) := by
  have hi : AnalyticAt ℂ (fun v : ℂ => (u,v)) 0 := analyticAt_const.prod analyticAt_id
  have hFs : AnalyticAt ℂ (fun v => F (u,v)) 0 := hF.comp hi
  have he : (fun v => tangentDeriv (h ∘ F) (u,v)) =ᶠ[nhds 0]
      (fun v => ∑ j, coordinatePartial h j (F (u,v)) * tangentDeriv (fun z => F z j) (u,v)) := by
    filter_upwards [hi.continuousAt hF.eventually_analyticAt,
      hFs.continuousAt hh.eventually_analyticAt] with v hv hhv
    exact tangentDeriv_comp hhv hv
  rw [taylorSeries_congr he,taylorSeries_sum]
  · simp only [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hT : AnalyticAt ℂ (fun v => tangentDeriv (fun z => F z j) (u,v)) 0 :=
      (directionDeriv_analytic (analyticAt_pi_iff.mp hF j) (1,0)).comp hi
    have hP : AnalyticAt ℂ (fun v => coordinatePartial h j (F (u,v))) 0 :=
      AnalyticAt.comp (f := fun v => F (u,v)) (partial_analytic hh j) hFs
    rw [show (fun v => coordinatePartial h j (F (u,v)) * tangentDeriv (fun z => F z j) (u,v)) =
      (fun v => coordinatePartial h j (F (u,v))) *
        (fun v => tangentDeriv (fun z => F z j) (u,v)) from rfl,
      taylorSeries_mul hP hT,
      PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => PowerSeries.coeff a (taylorSeries (fun v => coordinatePartial h j (F (u,v)))) *
          PowerSeries.coeff b (taylorSeries (fun v => tangentDeriv (fun z => F z j) (u,v)))) n]
  · intro j _
    exact (AnalyticAt.comp (f := fun v => F (u,v)) (partial_analytic hh j) hFs).fun_mul
      ((directionDeriv_analytic (analyticAt_pi_iff.mp hF j) (1,0)).comp hi)

 

theorem composeCoefficient_tangent_chain {h : (σ → ℂ) → ℂ}
    (f : ℕ → ℂ → σ → ℂ) {u : ℂ} (n : ℕ)
    (hf : ∀ k, k ≤ n → ∀ i, AnalyticAt ℂ (fun z => f k z i) u)
    (hh : AnalyticAt ℂ h (f 0 u)) :
    deriv (fun z => composeCoefficient h (fun k => f k z) n) u =
      ∑ j, ∑ k ∈ Finset.range (n+1),
        composeCoefficient (coordinatePartial h j) (fun l => f l u) k *
          deriv (fun z => f (n-k) z j) u := by
  let F : ℂ × ℂ → σ → ℂ := fun w => jetPolynomial (fun k => f k w.1) n w.2
  have hF : AnalyticAt ℂ F (u,0) := jetPolynomial_analytic n hf
  have hh' : AnalyticAt ℂ h (F (u,0)) := by simpa [F] using hh
  change deriv (fun z => PowerSeries.coeff n (taylorSeries (fun v => (h ∘ F) (z,v)))) u = _
  rw [deriv_normalCoefficient (hh'.comp hF) n,taylor_tangent_comp hh' hF]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
  have hp := composeCoefficient_eq_laterJet (fun l => f l u) (partial_analytic hh j) hkn
  change PowerSeries.coeff k (taylorSeries (fun v => coordinatePartial h j
    (jetPolynomial (fun l => f l u) n v))) * _ = _
  rw [← hp]
  congr 1
  rw [← deriv_normalCoefficient (analyticAt_pi_iff.mp hF j) (n-k)]
  congr 1
  funext z
  change PowerSeries.coeff (n-k) (taylorSeries (fun v => jetPolynomial (fun l => f l z) n v j)) = _
  simp_rw [← polynomialJet_eval]
  rw [taylorSeries_polynomial,Polynomial.coeff_coe,polynomialJet_coeff,ite_eq_left (Nat.sub_le ..)]

end
section
open SplitTangent.DiagonalRationality
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

 

def formalSubst (h : (σ → ℂ) → ℂ) (f : ℕ → σ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (composeCoefficient h f)

omit [Fintype σ] in
@[simp] theorem coeff_formalSubst (h : (σ → ℂ) → ℂ) (f : ℕ → σ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (formalSubst h f) = composeCoefficient h f n := by
  simp [formalSubst]

theorem formalSubst_congr {h k : (σ → ℂ) → ℂ} (f : ℕ → σ → ℂ)
    (he : h =ᶠ[nhds (f 0)] k) : formalSubst h f = formalSubst k f := by
  ext n
  simp only [coeff_formalSubst,composeCoefficient]
  apply congrArg (PowerSeries.coeff n)
  apply taylorSeries_congr
  exact he.comp_tendsto (by simpa only [ContinuousAt,jetPolynomial_zero] using
    (jetPolynomial_hasSeries f n).analyticAt.continuousAt)

theorem formalSubst_mul {h k : (σ → ℂ) → ℂ} (f : ℕ → σ → ℂ)
    (hh : AnalyticAt ℂ h (f 0)) (hk : AnalyticAt ℂ k (f 0)) :
    formalSubst (fun x => h x * k x) f = formalSubst h f * formalSubst k f := by
  ext n
  rw [coeff_formalSubst,composeCoefficient_mul f hh hk,PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a (formalSubst h f) * PowerSeries.coeff b (formalSubst k f)) n]
  simp only [coeff_formalSubst]

theorem formalSubst_sum {ι : Type*} (s : Finset ι)
    (h : ι → (σ → ℂ) → ℂ) (f : ℕ → σ → ℂ)
    (hh : ∀ i ∈ s, AnalyticAt ℂ (h i) (f 0)) :
    formalSubst (fun x => ∑ i ∈ s, h i x) f = ∑ i ∈ s, formalSubst (h i) f := by
  ext n
  simp only [coeff_formalSubst,composeCoefficient_sum s h f hh,map_sum]

theorem formalSubst_assoc (H : (σ → ℂ) → τ → ℂ)
    (h : (τ → ℂ) → ℂ) (f : ℕ → σ → ℂ)
    (hH : AnalyticAt ℂ H (f 0)) (hh : AnalyticAt ℂ h (H (f 0))) :
    formalSubst h (composeJet H f) = formalSubst (h ∘ H) f := by
  ext n
  simp only [coeff_formalSubst,composeCoefficient_assoc H h f hH hh]

 
def normalVector (f : ℕ → σ → ℂ) : σ → PowerSeries ℂ :=
  fun i => PowerSeries.derivative (PowerSeries.mk (fun n => f n i))

 
def tangentVector (f : ℕ → ℂ → σ → ℂ) (u : ℂ) : σ → PowerSeries ℂ :=
  fun i => PowerSeries.mk (fun n => deriv (fun z => f n z i) u)

 
def substitutedJacobian [DecidableEq σ] (H : (σ → ℂ) → τ → ℂ)
    (f : ℕ → σ → ℂ) : Matrix τ σ (PowerSeries ℂ) :=
  fun i j => formalSubst (coordinatePartial (fun x => H x i) j) f

theorem normalVector_compose [DecidableEq σ] (H : (σ → ℂ) → τ → ℂ)
    (f : ℕ → σ → ℂ) (hH : AnalyticAt ℂ H (f 0)) :
    normalVector (composeJet H f) = (substitutedJacobian H f).mulVec (normalVector f) := by
  funext i
  ext n
  simp only [normalVector,PowerSeries.coeff_derivative,PowerSeries.coeff_mk,composeJet,
    Matrix.mulVec,dotProduct,map_sum,PowerSeries.coeff_mul]
  rw [mul_comm,composeCoefficient_normal_chain f (analyticAt_pi_iff.mp hH i) n]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a (substitutedJacobian H f i j) *
      (f (b+1) j * (b+1 : ℂ))) n]
  apply Finset.sum_congr rfl
  intro k hk
  simp [substitutedJacobian,mul_comm]

theorem tangentVector_compose [DecidableEq σ] (H : (σ → ℂ) → τ → ℂ)
    (f : ℕ → ℂ → σ → ℂ) (u : ℂ)
    (hf : ∀ n i, AnalyticAt ℂ (fun z => f n z i) u)
    (hH : AnalyticAt ℂ H (f 0 u)) :
    tangentVector (fun n z => composeJet H (fun k => f k z) n) u =
      (substitutedJacobian H (fun k => f k u)).mulVec (tangentVector f u) := by
  funext i
  ext n
  simp only [tangentVector,PowerSeries.coeff_mk,composeJet,Matrix.mulVec,dotProduct,
    map_sum,PowerSeries.coeff_mul]
  rw [composeCoefficient_tangent_chain f n (fun k _ i => hf k i) (analyticAt_pi_iff.mp hH i)]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a (substitutedJacobian H (fun k => f k u) i j) *
      deriv (fun z => f b z j) u) n]
  simp only [substitutedJacobian,coeff_formalSubst]

 
def substitutedMatrix (P : σ → σ → (σ → ℂ) → ℂ)
    (f : ℕ → σ → ℂ) : Matrix σ σ (PowerSeries ℂ) :=
  fun i j => formalSubst (P i j) f

 

theorem substituted_intertwining [DecidableEq σ] [DecidableEq τ]
    (H : (σ → ℂ) → τ → ℂ) (P : σ → σ → (σ → ℂ) → ℂ)
    (Q : τ → τ → (τ → ℂ) → ℂ) (f : ℕ → σ → ℂ)
    (hH : AnalyticAt ℂ H (f 0))
    (hP : ∀ i j, AnalyticAt ℂ (P i j) (f 0))
    (hQ : ∀ i j, AnalyticAt ℂ (Q i j) (H (f 0)))
    (he : ∀ i j, (fun x => ∑ k, coordinatePartial (fun y => H y i) k x * P k j x)
      =ᶠ[nhds (f 0)] (fun x => ∑ k, Q i k (H x) * coordinatePartial (fun y => H y k) j x)) :
    substitutedJacobian H f * substitutedMatrix P f =
      substitutedMatrix Q (composeJet H f) * substitutedJacobian H f := by
  funext i j
  simp only [Matrix.mul_apply,substitutedJacobian,substitutedMatrix]
  have hah i j := partial_analytic (analyticAt_pi_iff.mp hH i) j
  have hleft := formalSubst_sum Finset.univ
    (fun k x => coordinatePartial (fun y => H y i) k x * P k j x) f
    (fun k _ => (hah i k).mul (hP k j))
  have hright := formalSubst_sum Finset.univ
    (fun k x => Q i k (H x) * coordinatePartial (fun y => H y k) j x) f
    (fun k _ => ((hQ i k).comp hH).mul (hah k j))
  rw [formalSubst_congr f (he i j)] at hleft
  rw [hright] at hleft
  simp only [formalSubst_mul f (hah i _) (hP _ j)] at hleft
  rw [← hleft]
  apply Finset.sum_congr rfl
  intro k _
  exact (formalSubst_mul f ((hQ i k).comp hH) (hah k j)).trans
    (congrArg (fun a => a * formalSubst (coordinatePartial (fun x => H x k) j) f)
      (formalSubst_assoc H (Q i k) f hH (hQ i k)).symm)

 

theorem cauchy_target_covariance [DecidableEq σ] [DecidableEq τ]
    (H : (σ → ℂ) → τ → ℂ) (P : σ → σ → (σ → ℂ) → ℂ)
    (Q : τ → τ → (τ → ℂ) → ℂ) (f : ℕ → ℂ → σ → ℂ) (u : ℂ)
    (hf : ∀ n i, AnalyticAt ℂ (fun z => f n z i) u)
    (hH : AnalyticAt ℂ H (f 0 u))
    (hP : ∀ i j, AnalyticAt ℂ (P i j) (f 0 u))
    (hQ : ∀ i j, AnalyticAt ℂ (Q i j) (H (f 0 u)))
    (he : ∀ i j, (fun x => ∑ k, coordinatePartial (fun y => H y i) k x * P k j x)
      =ᶠ[nhds (f 0 u)] (fun x => ∑ k, Q i k (H x) * coordinatePartial (fun y => H y k) j x))
    (hsol : normalVector (fun k => f k u) =
      (substitutedMatrix P (fun k => f k u)).mulVec (tangentVector f u)) :
    normalVector (composeJet H (fun k => f k u)) =
      (substitutedMatrix Q (composeJet H (fun k => f k u))).mulVec
        (tangentVector (fun n z => composeJet H (fun k => f k z) n) u) := by
  rw [normalVector_compose H _ hH,hsol,Matrix.mulVec_mulVec,
    substituted_intertwining H P Q _ hH hP hQ he,← Matrix.mulVec_mulVec,
    tangentVector_compose H f u hf hH]

end
section
open SplitTangent.DiagonalRationality
open PowerSeries

 
theorem formalComposition_outer_causal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (p : FormalMultilinearSeries ℂ E F) {q r : FormalMultilinearSeries ℂ F G} {n : ℕ}
    (h : ∀ k, k ≤ n → q k = r k) : (q.comp p) n = (r.comp p) n := by
  unfold FormalMultilinearSeries.comp
  apply Finset.sum_congr rfl
  intro c _
  ext v
  simp only [FormalMultilinearSeries.compAlongComposition_apply]
  rw [h c.length c.length_le]

 
theorem coeff_subst_trunc {R : Type*} [CommRing R] (b f : PowerSeries R)
    (hb : constantCoeff b = 0) (n : ℕ) :
    coeff n (subst b f) = coeff n (subst b (trunc (n+1) f : PowerSeries R)) := by
  have hs := HasSubst.of_constantCoeff_zero' hb
  obtain ⟨c,hc⟩ := (X_dvd_iff.mpr hb)
  have he := congrArg (subst b) (eq_X_pow_mul_shift_add_trunc (n+1) f)
  rw [subst_add hs,subst_mul hs,subst_pow hs,subst_X hs,hc,mul_pow] at he
  rw [hc,he,map_add,mul_assoc,coeff_X_pow_mul']
  simp

 

theorem coeff_subst_congr {R : Type*} [CommRing R] (b f g : PowerSeries R)
    (hb : constantCoeff b = 0) (n : ℕ) (h : ∀ k, k ≤ n → coeff k f = coeff k g) :
    coeff n (subst b f) = coeff n (subst b g) := by
  rw [coeff_subst_trunc b f hb n,coeff_subst_trunc b g hb n]
  have ht : trunc (n+1) f = trunc (n+1) g := by
    ext k
    simp only [coeff_trunc]
    split_ifs with hk
    · exact h k (by omega)
    · rfl
  rw [ht]

@[simp] theorem taylorSeries_const (c : ℂ) : taylorSeries (fun _ => c) = C c := by
  simpa using taylorSeries_polynomial (Polynomial.C c)

 
theorem taylorSeries_polynomial_comp (p : Polynomial ℂ) {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) :
    taylorSeries (fun z => p.eval (g z)) = Polynomial.aeval (taylorSeries g) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add,map_add]
    change taylorSeries ((fun z => p.eval (g z)) + (fun z => q.eval (g z))) = _
    rw [taylorSeries_add (f := fun z => p.eval (g z)) (g := fun z => q.eval (g z))
      ((polynomial_analyticAt p (g 0)).comp hg) ((polynomial_analyticAt q (g 0)).comp hg),hp,hq]
  | monomial n c =>
    simp only [Polynomial.eval_monomial,Polynomial.aeval_monomial]
    change taylorSeries ((fun _ => c) * (fun z => g z ^ n)) = _
    rw [taylorSeries_mul (f := fun _ => c) (g := fun z => g z ^ n) analyticAt_const (hg.pow n),taylorSeries_const]
    congr 1
    induction n with
    | zero => simp [taylorSeries_const]
    | succ n ih =>
      simp only [pow_succ]
      change taylorSeries ((fun z => g z ^ n) * g) = _
      rw [taylorSeries_mul (f := fun z => g z ^ n) (g := g) (hg.pow n) hg,ih]

 

theorem coeff_taylor_comp_trunc {h g : ℂ → ℂ} (hh : AnalyticAt ℂ h 0)
    (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0) (n : ℕ) :
    coeff n (taylorSeries (h ∘ g)) =
      coeff n (taylorSeries (fun z => (trunc (n+1) (taylorSeries h)).eval (g z))) := by
  let p := trunc (n+1) (taylorSeries h)
  have hha : HasFPowerSeriesAt h
      (FormalMultilinearSeries.ofScalars ℂ (fun k => coeff k (taylorSeries h))) (g 0) := by
    rw [hg0]; exact hasFPowerSeries_taylorSeries hh
  have hpa : HasFPowerSeriesAt (fun z => p.eval z)
      (FormalMultilinearSeries.ofScalars ℂ (fun k => p.coeff k)) (g 0) := by
    rw [hg0]
    simpa only [taylorSeries_polynomial,Polynomial.coeff_coe] using
      hasFPowerSeries_taylorSeries (polynomial_analyticAt p 0)
  let q := FormalMultilinearSeries.ofScalars ℂ (fun k => coeff k (taylorSeries g))
  have hq : HasFPowerSeriesAt g q 0 := hasFPowerSeries_taylorSeries hg
  have hc := hha.comp hq
  have hd := hpa.comp hq
  have he : (FormalMultilinearSeries.ofScalars ℂ (fun k => coeff k (taylorSeries h))).comp q n =
      (FormalMultilinearSeries.ofScalars ℂ (fun k => p.coeff k)).comp q n := by
    apply formalComposition_outer_causal
    intro k hk
    simp only [FormalMultilinearSeries.ofScalars,p,coeff_trunc,ite_eq_left (by omega : k < n+1)]
  have ht := (hasFPowerSeries_taylorSeries hc.analyticAt).eq_formalMultilinearSeries hc
  have hu := (hasFPowerSeries_taylorSeries hd.analyticAt).eq_formalMultilinearSeries hd
  have het := congrArg (fun s : FormalMultilinearSeries ℂ ℂ ℂ => s.coeff n) ht
  have heu := congrArg (fun s : FormalMultilinearSeries ℂ ℂ ℂ => s.coeff n) hu
  rw [FormalMultilinearSeries.coeff_ofScalars] at het heu
  exact het.trans ((congrArg (fun L : ContinuousMultilinearMap ℂ (fun _ : Fin n => ℂ) ℂ =>
    L (fun _ => 1)) he).trans heu.symm)

 

theorem taylorSeries_comp_zero {h g : ℂ → ℂ} (hh : AnalyticAt ℂ h 0)
    (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0) :
    taylorSeries (h ∘ g) = subst (taylorSeries g) (taylorSeries h) := by
  have hzero : constantCoeff (taylorSeries g) = 0 := by
    rw [← coeff_zero_eq_constantCoeff,coeff_taylorSeries]; simpa using hg0
  have hs := HasSubst.of_constantCoeff_zero' hzero
  ext n
  rw [coeff_taylor_comp_trunc hh hg hg0 n,taylorSeries_polynomial_comp _ hg,
    coeff_subst_trunc _ _ hzero n,subst_coe hs]

end
open SplitTangent.DiagonalRationality PowerSeries
variable {σ : Type*} [Fintype σ]

 
def reparamJet (b : PowerSeries ℂ) (f : ℕ → σ → ℂ) : ℕ → σ → ℂ :=
  fun n i => coeff n (subst b (PowerSeries.mk (fun k => f k i)))

omit [Fintype σ] in
@[simp] theorem reparamJet_zero (b : PowerSeries ℂ) (f : ℕ → σ → ℂ)
    (hb : constantCoeff b = 0) : reparamJet b f 0 = f 0 := by
  funext i
  rw [reparamJet,coeff_subst_trunc b _ hb 0,trunc_one_left]
  simp; rfl

 

omit [Fintype σ] in
theorem reparamJet_eq_analyticJet (f : ℕ → σ → ℂ) {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0) {k n : ℕ} (hkn : k ≤ n) :
    reparamJet (taylorSeries g) f k =
      analyticJet (fun v => jetPolynomial f n (g v)) k := by
  have hb : constantCoeff (taylorSeries g) = 0 := by
    rw [← coeff_zero_eq_constantCoeff,coeff_taylorSeries]; simpa using hg0
  funext i
  unfold reparamJet analyticJet
  simp_rw [← polynomialJet_eval]
  have he := coeff_subst_congr (taylorSeries g) (PowerSeries.mk (fun l => f l i))
    (polynomialJet f n i : PowerSeries ℂ) hb k (by
      intro l hl
      simp only [coeff_mk,Polynomial.coeff_coe,polynomialJet_coeff,
        ite_eq_left (hl.trans hkn)])
  rw [he]
  have ht := taylorSeries_comp_zero (polynomial_analyticAt (polynomialJet f n i) 0) hg hg0
  rw [taylorSeries_polynomial] at ht
  exact (congrArg (coeff k) ht).symm

 

theorem formalSubst_reparam (f : ℕ → σ → ℂ) {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0) {h : (σ → ℂ) → ℂ}
    (hh : AnalyticAt ℂ h (f 0)) :
    formalSubst h (reparamJet (taylorSeries g) f) =
      subst (taylorSeries g) (formalSubst h f) := by
  have hb : constantCoeff (taylorSeries g) = 0 := by
    rw [← coeff_zero_eq_constantCoeff,coeff_taylorSeries]; simpa using hg0
  ext n
  rw [coeff_formalSubst,composeCoefficient_causal h
    (fun k hk => reparamJet_eq_analyticJet f hg hg0 hk)]
  have hpoly : AnalyticAt ℂ (jetPolynomial f n) (g 0) := by
    rw [hg0]; exact (jetPolynomial_hasSeries f n).analyticAt
  have hG : AnalyticAt ℂ (fun v => jetPolynomial f n (g v)) 0 := hpoly.comp hg
  have hhG : AnalyticAt ℂ h (jetPolynomial f n (g 0)) := by simpa [hg0] using hh
  rw [composeCoefficient_analyticJet hG hhG]
  have hhF : AnalyticAt ℂ h (jetPolynomial f n 0) := by simpa using hh
  have hF := (jetPolynomial_hasSeries f n).analyticAt
  have ht := taylorSeries_comp_zero (hhF.comp hF) hg hg0
  change coeff n (taylorSeries ((h ∘ jetPolynomial f n) ∘ g)) = _
  rw [ht]
  apply coeff_subst_congr _ _ _ hb n
  intro k hk
  rw [coeff_formalSubst]
  exact (composeCoefficient_eq_laterJet f hh hk).symm

end SplitTangent.HolomorphicJets
namespace SplitTangent.FormalCauchy
open PowerSeries

 

def analyticDerivation {U : Set ℂ} (hU : IsOpen U) :
    Derivation ℂ (AnalyticFunction U) (AnalyticFunction U) where
  toLinearMap := analyticDerivative hU
  map_one_eq_zero' := by
    classical
    apply Subtype.ext
    funext z
    change (if z ∈ U then deriv (fun _ : ℂ => (1 : ℂ)) z else 0) = 0
    simp
  leibniz' := analyticDerivative_mul hU

 
def dCoeff {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (δ : Derivation R A A) (f : PowerSeries A) : PowerSeries A :=
  deriveCoefficients δ f

@[simp] theorem coeff_dCoeff {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (δ : Derivation R A A) (f : PowerSeries A) (n : ℕ) :
    coeff n (dCoeff δ f) = δ (coeff n f) := rfl

 
theorem dCoeff_subst {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (δ : Derivation R A A) (b f : PowerSeries A) (hb : HasSubst b) :
    dCoeff δ (subst b f) = subst b (dCoeff δ f) +
      subst b (derivative f) * dCoeff δ b := by
  simpa only [dCoeff,PowerSeries.subst,PowerSeries.derivative,
    Finset.univ_unique,Finset.sum_singleton] using
    formal_coefficient_chain_rule δ (fun _ : Unit => b) hb.const f

@[simp] theorem coeff_eval_dCoeff {U : Set ℂ} (hU : IsOpen U) {u : ℂ} (hu : u ∈ U)
    (f : PowerSeries (AnalyticFunction U)) (n : ℕ) :
    coeff n (PowerSeries.map (analyticEvaluation U u) (dCoeff (analyticDerivation hU) f)) =
      deriv (fun z => coeff n f z) u := by
  rw [coeff_map,coeff_dCoeff]
  exact analyticDerivative_apply hU _ hu

 
theorem eval_dCoeff_subst {U : Set ℂ} (hU : IsOpen U) (u : ℂ)
    (b f : PowerSeries (AnalyticFunction U)) (hb : HasSubst b) :
    PowerSeries.map (analyticEvaluation U u) (dCoeff (analyticDerivation hU) (subst b f)) =
      subst (PowerSeries.map (analyticEvaluation U u) b)
        (PowerSeries.map (analyticEvaluation U u) (dCoeff (analyticDerivation hU) f)) +
      subst (PowerSeries.map (analyticEvaluation U u) b)
        (derivative (PowerSeries.map (analyticEvaluation U u) f)) *
      PowerSeries.map (analyticEvaluation U u) (dCoeff (analyticDerivation hU) b) := by
  have hm (g : PowerSeries (AnalyticFunction U)) :
      PowerSeries.map (analyticEvaluation U u) (subst b g) =
        subst (PowerSeries.map (analyticEvaluation U u) b)
          (PowerSeries.map (analyticEvaluation U u) g) := PowerSeries.map_subst hb g
  have hd : PowerSeries.map (analyticEvaluation U u) (derivative f) =
      derivative (PowerSeries.map (analyticEvaluation U u) f) := by
    ext n
    simp only [coeff_map,coeff_derivative,map_mul,map_add,map_natCast,map_one]
  rw [dCoeff_subst _ _ _ hb,map_add,map_mul,hm,hm,hd]


 

def analyticPullback {U W : Set ℂ} (α : ℂ → ℂ)
    (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U) :
    AnalyticFunction U →ₐ[ℂ] AnalyticFunction W where
  toFun f := ⟨fun z => f (α z), fun z hz => (f.property (α z) (hαU hz)).comp (hα z hz)⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

 

theorem eval_dCoeff_pullback {U W : Set ℂ} (hU : IsOpen U) (hW : IsOpen W)
    (α : ℂ → ℂ) (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U)
    {u : ℂ} (hu : u ∈ W) (f : PowerSeries (AnalyticFunction U)) :
    PowerSeries.map (analyticEvaluation W u) (dCoeff (analyticDerivation hW)
      (PowerSeries.map (analyticPullback α hα hαU).toRingHom f)) =
      C (deriv α u) * PowerSeries.map (analyticEvaluation U (α u))
        (dCoeff (analyticDerivation hU) f) := by
  ext n
  rw [coeff_eval_dCoeff hW hu,coeff_C_mul,coeff_eval_dCoeff hU (hαU hu)]
  simp only [coeff_map,analyticPullback,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom]
  change deriv ((coeff n f).val ∘ α) u = deriv α u * deriv (coeff n f).val (α u)
  rw [deriv_comp u ((coeff n f).property _ (hαU hu)).differentiableAt
    (hα u hu).differentiableAt,mul_comm]

end SplitTangent.FormalCauchy
namespace SplitTangent.HolomorphicJets
section
open PowerSeries SplitTangent.DiagonalRationality SplitTangent.FormalCauchy

 
def sourceDifference (α : ℂ → ℂ) : ℂ × ℂ → ℂ := fun w => α (w.1+w.2) - α w.1

def sourceNormal (α : ℂ → ℂ) (u : ℂ) : PowerSeries ℂ :=
  taylorSeries (fun v => sourceDifference α (u,v))

theorem sourceDifference_analytic {α : ℂ → ℂ} {u v : ℂ}
    (hα : AnalyticAt ℂ α u) (hα' : AnalyticAt ℂ α (u+v)) :
    AnalyticAt ℂ (sourceDifference α) (u,v) := by
  exact (AnalyticAt.comp (f := fun w : ℂ × ℂ => w.1+w.2) (x := (u,v)) hα'
    (analyticAt_fst.add analyticAt_snd)).sub
      (AnalyticAt.comp (f := fun w : ℂ × ℂ => w.1) (x := (u,v)) hα analyticAt_fst)

@[simp] theorem sourceNormal_constant (α : ℂ → ℂ) (u : ℂ) :
    constantCoeff (sourceNormal α u) = 0 := by
  rw [← coeff_zero_eq_constantCoeff,sourceNormal,coeff_taylorSeries]
  simp [sourceDifference]

 

def sourceNormalFamily {W : Set ℂ} (α : ℂ → ℂ) (hα : AnalyticOnNhd ℂ α W) :
    PowerSeries (AnalyticFunction W) :=
  PowerSeries.mk (fun n => ⟨fun u => coeff n (sourceNormal α u), fun u hu => by
    exact normalCoefficient_analytic
      (sourceDifference_analytic (hα u hu) (by simpa using hα u hu : AnalyticAt ℂ α (u+0))) n⟩)

@[simp] theorem sourceNormalFamily_eval {W : Set ℂ} (α : ℂ → ℂ)
    (hα : AnalyticOnNhd ℂ α W) (u : ℂ) :
    PowerSeries.map (analyticEvaluation W u) (sourceNormalFamily α hα) = sourceNormal α u := by
  ext n
  simp [sourceNormalFamily]

theorem sourceNormalFamily_hasSubst {W : Set ℂ} (α : ℂ → ℂ)
    (hα : AnalyticOnNhd ℂ α W) : HasSubst (sourceNormalFamily α hα) := by
  apply HasSubst.of_constantCoeff_zero'
  apply Subtype.ext
  funext u
  change coeff 0 (sourceNormal α u) = 0
  rw [coeff_zero_eq_constantCoeff_apply,sourceNormal_constant]

 

theorem sourceDifference_tangent {α : ℂ → ℂ} {u v : ℂ}
    (hα : AnalyticAt ℂ α u) (hα' : AnalyticAt ℂ α (u+v)) :
    tangentDeriv (sourceDifference α) (u,v) =
      normalDeriv (sourceDifference α) (u,v) - deriv α u := by
  have hD := sourceDifference_analytic hα hα'
  rw [← tangentDeriv_eq hD,← normalDeriv_eq hD]
  have h₁ := ((hα'.differentiableAt.hasDerivAt.comp u
    ((hasDerivAt_id u).add_const v)).sub hα.differentiableAt.hasDerivAt).deriv
  have h₂ := ((hα'.differentiableAt.hasDerivAt.comp v
    ((hasDerivAt_const v u).add (hasDerivAt_id v))).sub_const (α u)).deriv
  simp only [zero_add,mul_one] at h₁ h₂
  convert h₁.trans (congrArg (fun z => z - deriv α u) h₂.symm) using 1 <;>
    congr 1

theorem taylorSeries_sub {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorSeries (f-g) = taylorSeries f - taylorSeries g := by
  ext n
  simp only [map_sub,coeff_taylorSeries]
  rw [iteratedDeriv_sub hf.contDiffAt hg.contDiffAt,sub_div]

 

theorem eval_dCoeff_sourceNormal {W : Set ℂ} (hW : IsOpen W)
    (α : ℂ → ℂ) (hα : AnalyticOnNhd ℂ α W) {u : ℂ} (hu : u ∈ W) :
    PowerSeries.map (analyticEvaluation W u)
        (dCoeff (analyticDerivation hW) (sourceNormalFamily α hα)) =
      derivative (sourceNormal α u) - C (deriv α u) := by
  have hD := sourceDifference_analytic (hα u hu) (by simpa using hα u hu : AnalyticAt ℂ α (u+0))
  have hi : AnalyticAt ℂ (fun v : ℂ => (u,v)) 0 := analyticAt_const.prod analyticAt_id
  have hn : AnalyticAt ℂ (fun v => normalDeriv (sourceDifference α) (u,v)) 0 :=
    (normalDeriv_analytic hD).comp hi
  have he : (fun v => tangentDeriv (sourceDifference α) (u,v)) =ᶠ[nhds 0]
      (fun v => normalDeriv (sourceDifference α) (u,v) - deriv α u) := by
    have hs : ContinuousAt (fun v : ℂ => u+v) 0 := by fun_prop
    have ha0 : ∀ᶠ z in nhds u, AnalyticAt ℂ α z := (hα u hu).eventually_analyticAt
    have ha : ∀ᶠ v in nhds (0 : ℂ), AnalyticAt ℂ α (u+v) :=
      Filter.Tendsto.eventually (by simpa only [ContinuousAt,add_zero] using hs : Tendsto (fun v : ℂ => u+v) (nhds 0) (nhds u)) ha0
    filter_upwards [ha] with v hv
    exact sourceDifference_tangent (hα u hu) hv
  have hd : (fun v => normalDeriv (sourceDifference α) (u,v)) =ᶠ[nhds 0]
      deriv (fun v => sourceDifference α (u,v)) := by
    filter_upwards [hi.continuousAt hD.eventually_analyticAt] with v hv
    exact (normalDeriv_eq hv).symm
  ext n
  rw [coeff_eval_dCoeff hW hu]
  simp only [sourceNormalFamily,coeff_mk]
  change deriv (fun z => coeff n (taylorSeries (fun v => sourceDifference α (z,v)))) u = _
  rw [deriv_normalCoefficient hD,taylorSeries_congr he]
  change coeff n (taylorSeries ((fun v => normalDeriv (sourceDifference α) (u,v)) -
    (fun _ => deriv α u))) = _
  rw [taylorSeries_sub hn analyticAt_const,taylorSeries_const,taylorSeries_congr hd,taylorSeries_deriv]
  rfl

end
section
open PowerSeries SplitTangent.DiagonalRationality SplitTangent.FormalCauchy
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

 

omit [DecidableEq σ] in
theorem substitutedMatrix_idempotent (P : σ → σ → (σ → ℂ) → ℂ)
    (f : ℕ → σ → ℂ) (hP : ∀ i j, AnalyticAt ℂ (P i j) (f 0))
    (he : ∀ i j, (fun x => ∑ k, P i k x * P k j x) =ᶠ[nhds (f 0)] P i j) :
    substitutedMatrix P f * substitutedMatrix P f = substitutedMatrix P f := by
  funext i j
  simp only [substitutedMatrix,Matrix.mul_apply]
  have hs := formalSubst_sum Finset.univ (fun k x => P i k x * P k j x) f
    (fun k _ => (hP i k).mul (hP k j))
  rw [formalSubst_congr f (he i j)] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro k _
  exact (formalSubst_mul f (hP i k) (hP k j)).symm

 
omit [DecidableEq σ] in
theorem projector_source_identity {R : Type*} [CommRing R]
    (M : Matrix σ σ R) (a b : R) (v w : σ → R)
    (hM : M*M=M) (hv : v=M.mulVec w) :
    b • v = M.mulVec (a • w + (b-a) • v) := by
  have hm : M.mulVec v = v := by
    rw [hv,Matrix.mulVec_mulVec,hM]
  rw [Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul,hm,← hv]
  rw [← add_smul]
  simp

 

def sourceTransform {U W : Set ℂ} (α : ℂ → ℂ)
    (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U)
    (F : σ → PowerSeries (AnalyticFunction U)) : σ → PowerSeries (AnalyticFunction W) :=
  fun i => subst (sourceNormalFamily α hα)
    (PowerSeries.map (analyticPullback α hα hαU).toRingHom (F i))

 
theorem eval_pullback {U W : Set ℂ} (α : ℂ → ℂ)
    (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U) (u : ℂ)
    (f : PowerSeries (AnalyticFunction U)) :
    PowerSeries.map (analyticEvaluation W u)
      (PowerSeries.map (analyticPullback α hα hαU).toRingHom f) =
      PowerSeries.map (analyticEvaluation U (α u)) f := by
  ext n
  rfl

omit [Fintype σ] [DecidableEq σ] in
theorem eval_sourceTransform {U W : Set ℂ} (α : ℂ → ℂ)
    (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U)
    (F : σ → PowerSeries (AnalyticFunction U)) (u : ℂ) (i : σ) :
    PowerSeries.map (analyticEvaluation W u) (sourceTransform α hα hαU F i) =
      subst (sourceNormal α u) (PowerSeries.map (analyticEvaluation U (α u)) (F i)) := by
  have hm := PowerSeries.map_subst (h := analyticEvaluation W u)
    (sourceNormalFamily_hasSubst α hα)
    (PowerSeries.map (analyticPullback α hα hαU).toRingHom (F i))
  change PowerSeries.map (analyticEvaluation W u) (sourceTransform α hα hαU F i) =
    subst (PowerSeries.map (analyticEvaluation W u) (sourceNormalFamily α hα))
      (PowerSeries.map (analyticEvaluation W u)
        (PowerSeries.map (analyticPullback α hα hαU).toRingHom (F i))) at hm
  rw [sourceNormalFamily_eval,eval_pullback] at hm
  exact hm

omit [Fintype σ] [DecidableEq σ] in
theorem normal_sourceTransform {U W : Set ℂ} (α : ℂ → ℂ)
    (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U)
    (F : σ → PowerSeries (AnalyticFunction U)) (u : ℂ) (i : σ) :
    derivative (PowerSeries.map (analyticEvaluation W u) (sourceTransform α hα hαU F i)) =
      derivative (sourceNormal α u) * subst (sourceNormal α u)
        (derivative (PowerSeries.map (analyticEvaluation U (α u)) (F i))) := by
  rw [eval_sourceTransform,derivative_subst
    (HasSubst.of_constantCoeff_zero' (sourceNormal_constant α u)),mul_comm]

 
omit [Fintype σ] [DecidableEq σ] in
theorem tangent_sourceTransform {U W : Set ℂ} (hU : IsOpen U) (hW : IsOpen W)
    (α : ℂ → ℂ) (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U)
    (F : σ → PowerSeries (AnalyticFunction U)) {u : ℂ} (hu : u ∈ W) (i : σ) :
    PowerSeries.map (analyticEvaluation W u)
      (dCoeff (analyticDerivation hW) (sourceTransform α hα hαU F i)) =
      C (deriv α u) * subst (sourceNormal α u)
        (PowerSeries.map (analyticEvaluation U (α u)) (dCoeff (analyticDerivation hU) (F i))) +
      (derivative (sourceNormal α u) - C (deriv α u)) * subst (sourceNormal α u)
        (derivative (PowerSeries.map (analyticEvaluation U (α u)) (F i))) := by
  rw [sourceTransform,eval_dCoeff_subst hW u _ _ (sourceNormalFamily_hasSubst α hα),
    sourceNormalFamily_eval,eval_dCoeff_pullback hU hW α hα hαU hu,
    eval_pullback,eval_dCoeff_sourceNormal hW α hα hu,
    subst_mul (HasSubst.of_constantCoeff_zero' (sourceNormal_constant α u)),subst_C]
  congr 1
  exact mul_comm _ _

 

omit [DecidableEq σ] in
theorem substitutedMatrix_sourceTransform {U W : Set ℂ} (α : ℂ → ℂ)
    (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U)
    (F : σ → PowerSeries (AnalyticFunction U)) {u : ℂ} (hu : u ∈ W)
    (P : σ → σ → (σ → ℂ) → ℂ)
    (hP : ∀ i j, AnalyticAt ℂ (P i j) (fun l => coeff 0 (F l) (α u))) :
    substitutedMatrix P (fun n i => coeff n (sourceTransform α hα hαU F i) u) =
      (substitutedMatrix P (fun n i => coeff n (F i) (α u))).map (subst (sourceNormal α u)) := by
  have hb : AnalyticAt ℂ (fun v => sourceDifference α (u,v)) 0 :=
    (sourceDifference_analytic (hα u hu) (by simpa using hα u hu : AnalyticAt ℂ α (u+0))).comp
      (analyticAt_const.prod analyticAt_id)
  have hz : sourceDifference α (u,0) = 0 := by simp [sourceDifference]
  have hf : (fun n i => coeff n (sourceTransform α hα hαU F i) u) =
      reparamJet (sourceNormal α u) (fun n i => coeff n (F i) (α u)) := by
    funext n i
    have he := congrArg (coeff n) (eval_sourceTransform α hα hαU F u i)
    have hm : PowerSeries.map (analyticEvaluation U (α u)) (F i) =
        PowerSeries.mk (fun k => coeff k (F i) (α u)) := by
      ext k
      simp
    rw [hm] at he
    exact he
  rw [hf]
  funext i j
  exact formalSubst_reparam _ hb hz (hP i j)

end
open PowerSeries SplitTangent.FormalCauchy
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

 

omit [DecidableEq σ] in
theorem cauchy_source_covariance {U W : Set ℂ} (hU : IsOpen U) (hW : IsOpen W)
    (α : ℂ → ℂ) (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U)
    (F : σ → PowerSeries (AnalyticFunction U)) {u : ℂ} (hu : u ∈ W)
    (P : σ → σ → (σ → ℂ) → ℂ)
    (hP : ∀ i j, AnalyticAt ℂ (P i j) (fun l => coeff 0 (F l) (α u)))
    (hidem : ∀ i j, (fun x => ∑ k, P i k x * P k j x)
      =ᶠ[nhds (fun l => coeff 0 (F l) (α u))] P i j)
    (hsol : (fun i => derivative (PowerSeries.map (analyticEvaluation U (α u)) (F i))) =
      (substitutedMatrix P (fun n i => coeff n (F i) (α u))).mulVec
        (fun i => PowerSeries.map (analyticEvaluation U (α u)) (dCoeff (analyticDerivation hU) (F i)))) :
    (fun i => derivative (PowerSeries.map (analyticEvaluation W u) (sourceTransform α hα hαU F i))) =
      (substitutedMatrix P (fun n i => coeff n (sourceTransform α hα hαU F i) u)).mulVec
        (fun i => PowerSeries.map (analyticEvaluation W u)
          (dCoeff (analyticDerivation hW) (sourceTransform α hα hαU F i))) := by
  let M₀ := substitutedMatrix P (fun n i => coeff n (F i) (α u))
  have hb := HasSubst.of_constantCoeff_zero' (sourceNormal_constant α u)
  let r : PowerSeries ℂ →+* PowerSeries ℂ := (substAlgHom hb).toRingHom
  have hr : (r : PowerSeries ℂ → PowerSeries ℂ) = subst (sourceNormal α u) := coe_substAlgHom hb
  let M := M₀.map r
  let v : σ → PowerSeries ℂ := fun i => r (derivative (PowerSeries.map (analyticEvaluation U (α u)) (F i)))
  let w : σ → PowerSeries ℂ := fun i => r (PowerSeries.map (analyticEvaluation U (α u))
    (dCoeff (analyticDerivation hU) (F i)))
  have hM₀ : M₀*M₀=M₀ := substitutedMatrix_idempotent P _ hP hidem
  have hM : M*M=M := by
    change M₀.map r * M₀.map r = M₀.map r
    rw [← Matrix.map_mul,hM₀]
  have hv : v=M.mulVec w := by
    funext i
    have hs := congrArg r (congrFun hsol i)
    exact hs.trans (r.map_mulVec M₀ _ i)
  have hn : (fun i => derivative (PowerSeries.map (analyticEvaluation W u)
      (sourceTransform α hα hαU F i))) = derivative (sourceNormal α u) • v := by
    funext i
    simpa only [Pi.smul_apply,smul_eq_mul,v,hr] using normal_sourceTransform α hα hαU F u i
  have ht : (fun i => PowerSeries.map (analyticEvaluation W u)
      (dCoeff (analyticDerivation hW) (sourceTransform α hα hαU F i))) =
      C (deriv α u) • w + (derivative (sourceNormal α u) - C (deriv α u)) • v := by
    funext i
    simpa only [Pi.smul_apply,Pi.add_apply,smul_eq_mul,v,w,hr] using
      tangent_sourceTransform hU hW α hα hαU F hu i
  have hm : substitutedMatrix P (fun n i => coeff n (sourceTransform α hα hαU F i) u) = M := by
    simpa only [M,M₀,hr] using substitutedMatrix_sourceTransform α hα hαU F hu P hP
  rw [hn,ht,hm]
  exact projector_source_identity M (C (deriv α u)) (derivative (sourceNormal α u)) v w hM hv

end SplitTangent.HolomorphicJets
namespace SplitTangent.ActualCauchy
open SplitTangent.HolomorphicJets SplitTangent.FormalCauchy
variable {σ : Type*} [Fintype σ] {U : Set ℂ}

 

def seed (g : σ → AnalyticFunction U) (f : ℕ → σ → AnalyticFunction U) :
    ℕ → σ → AnalyticFunction U := fun k => if k = 0 then g else f k

omit [Fintype σ] in
@[simp] theorem seed_zero (g : σ → AnalyticFunction U) (f : ℕ → σ → AnalyticFunction U) :
    seed g f 0 = g := by simp [seed]

omit [Fintype σ] in
theorem seed_eq {g : σ → AnalyticFunction U} {f : ℕ → σ → AnalyticFunction U}
    (hf : f 0 = g) : seed g f = f := by
  funext n; by_cases hn : n = 0
  · subst n; simpa using hf.symm
  · simp [seed,hn]

 
def actualComposition (g : σ → AnalyticFunction U) (h : (σ → ℂ) → ℂ)
    (hh : ∀ u ∈ U, AnalyticAt ℂ h (fun i => g i u))
    (f : ℕ → σ → AnalyticFunction U) (n : ℕ) : AnalyticFunction U :=
  ⟨fun u => composeCoefficient h (fun k i => seed g f k i u) n, by
    intro u hu
    apply composeCoefficient_analytic n
    · intro k _ i; exact (seed g f k i).property u hu
    · simpa using hh u hu⟩

@[simp] theorem actualComposition_apply (g : σ → AnalyticFunction U)
    (h : (σ → ℂ) → ℂ) (hh : ∀ u ∈ U, AnalyticAt ℂ h (fun i => g i u))
    (f : ℕ → σ → AnalyticFunction U) (n : ℕ) (u : ℂ) :
    actualComposition g h hh f n u =
      composeCoefficient h (fun k i => seed g f k i u) n := rfl

theorem actualComposition_causal (g : σ → AnalyticFunction U)
    (h : (σ → ℂ) → ℂ) (hh : ∀ u ∈ U, AnalyticAt ℂ h (fun i => g i u))
    {f f' : ℕ → σ → AnalyticFunction U} {n : ℕ}
    (hff : ∀ k, k ≤ n → f k = f' k) :
    actualComposition g h hh f n = actualComposition g h hh f' n := by
  apply Subtype.ext; funext u
  apply composeCoefficient_causal
  intro k hk
  by_cases hk0 : k = 0
  · simp [seed,hk0]
  · simp [seed,hk0,hff k hk]

 

def actualOperator (hU : IsOpen U) (g : σ → AnalyticFunction U)
    (P : σ → σ → (σ → ℂ) → ℂ)
    (hP : ∀ i j u, u ∈ U → AnalyticAt ℂ (P i j) (fun r => g r u))
    (f : ℕ → σ → AnalyticFunction U) (n : ℕ) : σ → AnalyticFunction U :=
  fun i => ∑ j, ∑ k ∈ Finset.range (n+1),
    actualComposition g (P i j) (hP i j) f k * analyticDerivative hU (f (n-k) j)

theorem actualOperator_causal (hU : IsOpen U) (g : σ → AnalyticFunction U)
    (P : σ → σ → (σ → ℂ) → ℂ)
    (hP : ∀ i j u, u ∈ U → AnalyticAt ℂ (P i j) (fun r => g r u)) :
    Causal (actualOperator hU g P hP) := by
  intro n f f' hff
  funext i
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
  rw [actualComposition_causal g (P i j) (hP i j) (fun l hl => hff l (hl.trans hkn)),
    hff (n-k) (Nat.sub_le ..)]

 

def IsActualSolution (hU : IsOpen U) (g : σ → AnalyticFunction U)
    (P : σ → σ → (σ → ℂ) → ℂ)
    (hP : ∀ i j u, u ∈ U → AnalyticAt ℂ (P i j) (fun r => g r u))
    (f : ℕ → σ → AnalyticFunction U) : Prop :=
  f 0 = g ∧ ∀ n : ℕ, (n+1 : ℂ) • f (n+1) = actualOperator hU g P hP f n

 

theorem existsUnique_actualSolution (hU : IsOpen U) (g : σ → AnalyticFunction U)
    (P : σ → σ → (σ → ℂ) → ℂ)
    (hP : ∀ i j u, u ∈ U → AnalyticAt ℂ (P i j) (fun r => g r u)) :
    ∃! f : ℕ → σ → AnalyticFunction U, IsActualSolution hU g P hP f :=
  existsUnique_coefficients g _ (actualOperator_causal hU g P hP)

theorem IsActualSolution.pointwise {hU : IsOpen U} {g : σ → AnalyticFunction U}
    {P : σ → σ → (σ → ℂ) → ℂ}
    {hP : ∀ i j u, u ∈ U → AnalyticAt ℂ (P i j) (fun r => g r u)}
    {f : ℕ → σ → AnalyticFunction U} (hf : IsActualSolution hU g P hP f)
    (n : ℕ) (i : σ) {u : ℂ} (hu : u ∈ U) :
    (n+1 : ℂ) * f (n+1) i u = ∑ j, ∑ k ∈ Finset.range (n+1),
      composeCoefficient (P i j) (fun l r => f l r u) k * deriv (f (n-k) j : ℂ → ℂ) u := by
  have he := congrArg (fun a : σ → AnalyticFunction U => a i u) (hf.2 n)
  simpa [actualOperator,actualComposition_apply,seed_eq hf.1,analyticDerivative_apply hU _ hu]
    using he

end SplitTangent.ActualCauchy
namespace SplitTangent.HolomorphicJets
section
open PowerSeries SplitTangent.FormalCauchy SplitTangent.ActualCauchy
variable {σ : Type*} [Fintype σ]

 

def CauchyOn (U : Set ℂ) (g : ℂ → σ → ℂ)
    (P : σ → σ → (σ → ℂ) → ℂ) (f : ℕ → ℂ → σ → ℂ) : Prop :=
  (∀ n i, AnalyticOnNhd ℂ (fun u => f n u i) U) ∧
  (∀ u ∈ U, f 0 u = g u) ∧
  ∀ u ∈ U, normalVector (fun n => f n u) =
    (substitutedMatrix P (fun n => f n u)).mulVec (tangentVector f u)

theorem cauchyOn_recurrence {U : Set ℂ} {g : ℂ → σ → ℂ}
    {P : σ → σ → (σ → ℂ) → ℂ} {f : ℕ → ℂ → σ → ℂ}
    (hf : CauchyOn U g P f) {u : ℂ} (hu : u ∈ U) (n : ℕ) (i : σ) :
    (n+1 : ℂ) * f (n+1) u i = ∑ j, ∑ k ∈ Finset.range (n+1),
      composeCoefficient (P i j) (fun l => f l u) k * deriv (fun z => f (n-k) z j) u := by
  have he := congrArg (coeff n) (congrFun (hf.2.2 u hu) i)
  simp only [normalVector,coeff_derivative,coeff_mk,Matrix.mulVec,dotProduct,
    map_sum,coeff_mul,substitutedMatrix,coeff_formalSubst,tangentVector] at he
  rw [mul_comm] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro j _
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => composeCoefficient (P i j) (fun l => f l u) a *
      deriv (fun z => f b z j) u) n).symm

 
theorem exists_cauchyOn {U : Set ℂ} (hU : IsOpen U) (g : ℂ → σ → ℂ)
    (hg : ∀ i, AnalyticOnNhd ℂ (fun u => g u i) U)
    (P : σ → σ → (σ → ℂ) → ℂ)
    (hP : ∀ i j u, u ∈ U → AnalyticAt ℂ (P i j) (g u)) :
    ∃ f, CauchyOn U g P f := by
  let g' : σ → AnalyticFunction U := fun i => ⟨fun u => g u i, hg i⟩
  obtain ⟨f,hf,-⟩ := existsUnique_actualSolution hU g' P hP
  refine ⟨fun n u i => f n i u, ?_, ?_, ?_⟩
  · intro n i; exact (f n i).property
  · intro u hu; exact congrArg (fun a : σ → AnalyticFunction U => fun i => a i u) hf.1
  · intro u hu; funext i; ext n
    simp only [normalVector,coeff_derivative,coeff_mk,Matrix.mulVec,dotProduct,
      map_sum,coeff_mul,substitutedMatrix,coeff_formalSubst,tangentVector]
    rw [mul_comm, hf.pointwise n i hu]
    apply Finset.sum_congr rfl
    intro j _
    exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => composeCoefficient (P i j) (fun l r => f l r u) a *
        deriv (f b j : ℂ → ℂ) u) n).symm

 
theorem cauchyOn_unique {U : Set ℂ} (hU : IsOpen U) {g : ℂ → σ → ℂ}
    {P : σ → σ → (σ → ℂ) → ℂ} {f f' : ℕ → ℂ → σ → ℂ}
    (hf : CauchyOn U g P f) (hf' : CauchyOn U g P f') :
    ∀ n u, u ∈ U → f n u = f' n u := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u hu
    cases n with
    | zero => exact (hf.2.1 u hu).trans (hf'.2.1 u hu).symm
    | succ n =>
      funext i
      have hcoef (k : ℕ) (hk : k ≤ n) : (fun l => f l u) k = (fun l => f' l u) k :=
        ih k (by omega) u hu
      have hder (k : ℕ) (hk : k ≤ n) (j : σ) :
          deriv (fun z => f k z j) u = deriv (fun z => f' k z j) u := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [hU.mem_nhds hu] with z hz
        exact congrFun (ih k (by omega) z hz) j
      apply mul_left_cancel₀ (show (n+1 : ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero n)
      rw [cauchyOn_recurrence hf hu, cauchyOn_recurrence hf' hu]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
      rw [composeCoefficient_causal _ (fun l hl => hcoef l (hl.trans hkn)),
        hder (n-k) (Nat.sub_le ..) j]

 

theorem CauchyOn.mono {U W : Set ℂ} {g : ℂ → σ → ℂ}
    {P : σ → σ → (σ → ℂ) → ℂ} {f : ℕ → ℂ → σ → ℂ}
    (hf : CauchyOn U g P f) (hWU : W ⊆ U) : CauchyOn W g P f :=
  ⟨fun n i => (hf.1 n i).mono hWU, fun u hu => hf.2.1 u (hWU hu),
    fun u hu => hf.2.2 u (hWU hu)⟩

end
section
open PowerSeries SplitTangent.FormalCauchy SplitTangent.DiagonalRationality
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

 

theorem CauchyOn.target [DecidableEq σ] [DecidableEq τ]
    {U : Set ℂ} {g : ℂ → σ → ℂ} {P : σ → σ → (σ → ℂ) → ℂ}
    {f : ℕ → ℂ → σ → ℂ} (hf : CauchyOn U g P f)
    (H : (σ → ℂ) → τ → ℂ) (Q : τ → τ → (τ → ℂ) → ℂ)
    (hH : ∀ u ∈ U, AnalyticAt ℂ H (g u))
    (hP : ∀ i j u, u ∈ U → AnalyticAt ℂ (P i j) (g u))
    (hQ : ∀ i j u, u ∈ U → AnalyticAt ℂ (Q i j) (H (g u)))
    (he : ∀ u ∈ U, ∀ i j,
      (fun x => ∑ k, coordinatePartial (fun y => H y i) k x * P k j x)
        =ᶠ[nhds (g u)]
      (fun x => ∑ k, Q i k (H x) * coordinatePartial (fun y => H y k) j x)) :
    CauchyOn U (H ∘ g) Q (fun n u => composeJet H (fun k => f k u) n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n i u hu
    apply composeCoefficient_analytic n (fun k _ j => hf.1 k j u hu)
    rw [hf.2.1 u hu]
    exact analyticAt_pi_iff.mp (hH u hu) i
  · intro u hu
    simp only [composeJet_zero,hf.2.1 u hu,Function.comp_apply]
  · intro u hu
    apply cauchy_target_covariance H P Q f u (fun n i => hf.1 n i u hu)
    · rw [hf.2.1 u hu]; exact hH u hu
    · intro i j; rw [hf.2.1 u hu]; exact hP i j u hu
    · intro i j; rw [hf.2.1 u hu]; exact hQ i j u hu
    · rw [hf.2.1 u hu]; exact he u hu
    · exact hf.2.2 u hu

 

theorem cauchyOn_target_glue [DecidableEq σ] [DecidableEq τ]
    {U : Set ℂ} (hU : IsOpen U) {g : ℂ → σ → ℂ}
    {P : σ → σ → (σ → ℂ) → ℂ} {f : ℕ → ℂ → σ → ℂ}
    (hf : CauchyOn U g P f) (H : (σ → ℂ) → τ → ℂ)
    (Q : τ → τ → (τ → ℂ) → ℂ) {f' : ℕ → ℂ → τ → ℂ}
    (hf' : CauchyOn U (H ∘ g) Q f')
    (hH : ∀ u ∈ U, AnalyticAt ℂ H (g u))
    (hP : ∀ i j u, u ∈ U → AnalyticAt ℂ (P i j) (g u))
    (hQ : ∀ i j u, u ∈ U → AnalyticAt ℂ (Q i j) (H (g u)))
    (he : ∀ u ∈ U, ∀ i j,
      (fun x => ∑ k, coordinatePartial (fun y => H y i) k x * P k j x)
        =ᶠ[nhds (g u)]
      (fun x => ∑ k, Q i k (H x) * coordinatePartial (fun y => H y k) j x)) :
    ∀ n u, u ∈ U → composeJet H (fun k => f k u) n = f' n u :=
  cauchyOn_unique hU (hf.target H Q hH hP hQ he) hf'

 
def familySeries {U : Set ℂ} (f : ℕ → ℂ → σ → ℂ)
    (hf : ∀ n i, AnalyticOnNhd ℂ (fun u => f n u i) U) :
    σ → PowerSeries (AnalyticFunction U) :=
  fun i => PowerSeries.mk (fun n => ⟨fun u => f n u i, hf n i⟩)

omit [Fintype σ] in
@[simp] theorem familySeries_eval {U : Set ℂ} (f : ℕ → ℂ → σ → ℂ)
    (hf : ∀ n i, AnalyticOnNhd ℂ (fun u => f n u i) U) (u : ℂ) (i : σ) :
    PowerSeries.map (analyticEvaluation U u) (familySeries f hf i) =
      PowerSeries.mk (fun n => f n u i) := by
  ext n; simp [familySeries]

omit [Fintype σ] in
@[simp] theorem familySeries_coeff {U : Set ℂ} (f : ℕ → ℂ → σ → ℂ)
    (hf : ∀ n i, AnalyticOnNhd ℂ (fun u => f n u i) U) (u : ℂ) (i : σ) (n : ℕ) :
    coeff n (familySeries f hf i) u = f n u i := by simp [familySeries]

theorem sourceNormal_inv (u : ℂ) (hu : u ≠ 0) :
    sourceNormal (fun z : ℂ => z⁻¹) u = (C u + X)⁻¹ - C u⁻¹ := by
  have ha : AnalyticAt ℂ (fun v : ℂ => u+v) 0 := analyticAt_const.add analyticAt_id
  have hi : AnalyticAt ℂ (fun v : ℂ => (u+v)⁻¹) 0 := ha.fun_inv (by simpa using hu)
  have hl : taylorSeries (fun v : ℂ => u+v) = C u + X := by
    have he : (fun v : ℂ => u+v) =
        (fun v => Polynomial.eval v ((Polynomial.C u + Polynomial.X) : Polynomial ℂ)) := by
      funext v
      simp
    rw [he,taylorSeries_polynomial]
    simp
  have he : (fun v : ℂ => (u+v)⁻¹ * (u+v)) =ᶠ[nhds 0] (fun _ => 1) := by
    filter_upwards [ha.continuousAt.eventually_ne (by simpa using hu : u+(0:ℂ)≠0)] with v hv
    exact inv_mul_cancel₀ hv
  have hp := taylorSeries_congr he
  change taylorSeries ((fun v : ℂ => (u+v)⁻¹) * (fun v : ℂ => u+v)) = _ at hp
  rw [taylorSeries_mul hi ha,hl,taylorSeries_const] at hp
  have hc : constantCoeff (C u + X) ≠ 0 := by simpa using hu
  have hinv : taylorSeries (fun v : ℂ => (u+v)⁻¹) = (C u+X)⁻¹ := by
    calc
      _ = (taylorSeries (fun v : ℂ => (u+v)⁻¹) * (C u+X)) * (C u+X)⁻¹ := by
        rw [mul_assoc,PowerSeries.mul_inv_cancel _ hc,mul_one]
      _ = _ := by rw [hp]; simp
  unfold sourceNormal sourceDifference
  change taylorSeries ((fun v : ℂ => (u+v)⁻¹) - (fun _ => u⁻¹)) = _
  rw [taylorSeries_sub hi analyticAt_const,hinv,taylorSeries_const]

end
section
open PowerSeries SplitTangent.FormalCauchy SplitTangent.DiagonalRationality
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [Fintype σ] [DecidableEq σ] in
theorem normalVector_of_series {U : Set ℂ} (F : σ → PowerSeries (AnalyticFunction U)) (u : ℂ) :
    normalVector (fun n i => coeff n (F i) u) =
      fun i => derivative (PowerSeries.map (analyticEvaluation U u) (F i)) := by
  funext i
  change derivative (PowerSeries.mk (fun n => coeff n (F i) u)) = _
  congr 1
  ext n
  rw [coeff_mk,coeff_map]
  rfl

omit [Fintype σ] [DecidableEq σ] in
theorem tangentVector_of_series {U : Set ℂ} (hU : IsOpen U)
    (F : σ → PowerSeries (AnalyticFunction U)) {u : ℂ} (hu : u ∈ U) :
    tangentVector (fun n z i => coeff n (F i) z) u =
      fun i => PowerSeries.map (analyticEvaluation U u) (dCoeff (analyticDerivation hU) (F i)) := by
  funext i; ext n
  simp only [tangentVector,coeff_mk,coeff_eval_dCoeff hU hu]

def sourceFamily {U W : Set ℂ} (α : ℂ → ℂ)
    (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U)
    (f : ℕ → ℂ → σ → ℂ) (hf : ∀ n i, AnalyticOnNhd ℂ (fun u => f n u i) U) :
    ℕ → ℂ → σ → ℂ :=
  fun n u i => coeff n (sourceTransform α hα hαU (familySeries f hf) i) u

omit [Fintype σ] [DecidableEq σ] in
theorem sourceFamily_eval {U W : Set ℂ} (α : ℂ → ℂ)
    (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U)
    (f : ℕ → ℂ → σ → ℂ) (hf : ∀ n i, AnalyticOnNhd ℂ (fun u => f n u i) U)
    (u : ℂ) :
    (fun n => sourceFamily α hα hαU f hf n u) =
      reparamJet (sourceNormal α u) (fun n => f n (α u)) := by
  funext n i
  have he := eval_sourceTransform α hα hαU (familySeries f hf) u i
  rw [familySeries_eval] at he
  have hc := congrArg (coeff n) he
  change coeff n (sourceTransform α hα hαU (familySeries f hf) i) u = _ at hc
  exact hc

 

omit [DecidableEq σ] in
theorem CauchyOn.source {U W : Set ℂ} (hU : IsOpen U) (hW : IsOpen W)
    {g : ℂ → σ → ℂ} {P : σ → σ → (σ → ℂ) → ℂ}
    {f : ℕ → ℂ → σ → ℂ} (hf : CauchyOn U g P f)
    (α : ℂ → ℂ) (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U)
    (hP : ∀ i j u, u ∈ U → AnalyticAt ℂ (P i j) (g u))
    (hidem : ∀ u ∈ U, ∀ i j, (fun x => ∑ k, P i k x * P k j x) =ᶠ[nhds (g u)] P i j) :
    CauchyOn W (g ∘ α) P (sourceFamily α hα hαU f hf.1) := by
  let F := familySeries f hf.1
  let G := sourceTransform α hα hαU F
  refine ⟨?_, ?_, ?_⟩
  · intro n i; exact (coeff n (G i)).property
  · intro u hu
    change (fun n => sourceFamily α hα hαU f hf.1 n u) 0 = (g ∘ α) u
    rw [sourceFamily_eval,reparamJet_zero _ _ (sourceNormal_constant α u),hf.2.1 _ (hαU hu)]
    rfl
  · intro u hu
    change normalVector (fun n i => coeff n (G i) u) =
      (substitutedMatrix P (fun n i => coeff n (G i) u)).mulVec
        (tangentVector (fun n z i => coeff n (G i) z) u)
    rw [normalVector_of_series,tangentVector_of_series hW G hu]
    apply cauchy_source_covariance hU hW α hα hαU F hu P
    · intro i j
      simpa only [F,familySeries_coeff,hf.2.1 _ (hαU hu)] using hP i j (α u) (hαU hu)
    · intro i j
      simpa only [F,familySeries_coeff,hf.2.1 _ (hαU hu)] using hidem (α u) (hαU hu) i j
    · have hs := hf.2.2 (α u) (hαU hu)
      have he : (fun n z i => coeff n (F i) z) = f := by
        funext n z i; exact familySeries_coeff f hf.1 z i n
      rw [← he,normalVector_of_series,tangentVector_of_series hU F (hαU hu)] at hs
      exact hs

 

omit [DecidableEq σ] in
theorem cauchyOn_source_glue {U W : Set ℂ} (hU : IsOpen U) (hW : IsOpen W)
    {g : ℂ → σ → ℂ} {P : σ → σ → (σ → ℂ) → ℂ}
    {f : ℕ → ℂ → σ → ℂ} (hf : CauchyOn U g P f)
    (α : ℂ → ℂ) (hα : AnalyticOnNhd ℂ α W) (hαU : MapsTo α W U)
    {f' : ℕ → ℂ → σ → ℂ} (hf' : CauchyOn W (g ∘ α) P f')
    (hP : ∀ i j u, u ∈ U → AnalyticAt ℂ (P i j) (g u))
    (hidem : ∀ u ∈ U, ∀ i j, (fun x => ∑ k, P i k x * P k j x) =ᶠ[nhds (g u)] P i j) :
    ∀ n u, u ∈ W → reparamJet (sourceNormal α u) (fun k => f k (α u)) n = f' n u := by
  intro n u hu
  have he := cauchyOn_unique hW (hf.source hU hW α hα hαU hP hidem) hf' n u hu
  exact (congrFun (sourceFamily_eval α hα hαU f hf.1 u) n).symm.trans he

end

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem CauchyOn.congr_initial {U : Set ℂ} {g g' : ℂ → σ → ℂ}
    {P : σ → σ → (σ → ℂ) → ℂ} {f : ℕ → ℂ → σ → ℂ}
    (hf : CauchyOn U g P f) (he : Set.EqOn g g' U) : CauchyOn U g' P f :=
  ⟨hf.1,fun u hu => (hf.2.1 u hu).trans (he hu),hf.2.2⟩
end SplitTangent.HolomorphicJets

namespace SplitTangent.TangentSplitting
section
open HolomorphicJets
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

theorem coordinateMatrix_intertwining (x y : X.Carrier) {z : Model X}
    (hz : z ∈ (chartAt (Model X) x).target)
    (hzy : (chartAt (Model X) x).symm z ∈ (chartAt (Model X) y).source)
    (i j : Fin X.dim) :
    ∑ k, coordinatePartial (fun w => coordinateTransition x y w i) k z *
      S.coordinateMatrix x k j z =
    ∑ k, S.coordinateMatrix y i k (coordinateTransition x y z) *
      coordinatePartial (fun w => coordinateTransition x y w k) j z := by
  have hD := (coordinateTransition_analytic x y hz hzy).differentiableAt
  have he := congrArg (fun L : Model X →L[ℂ] Model X => LinearMap.toMatrix' L.toLinearMap)
    (S.coordinateProjector_intertwining x y hz hzy)
  change LinearMap.toMatrix' ((fderiv ℂ (coordinateTransition x y) z).toLinearMap.comp
    (S.coordinateProjector x z).toLinearMap) =
    LinearMap.toMatrix' ((S.coordinateProjector y (coordinateTransition x y z)).toLinearMap.comp
      (fderiv ℂ (coordinateTransition x y) z).toLinearMap) at he
  rw [LinearMap.toMatrix'_comp,LinearMap.toMatrix'_comp] at he
  have hj (i j : Fin X.dim) :
      coordinatePartial (fun w => coordinateTransition x y w i) j z =
        LinearMap.toMatrix' (fderiv ℂ (coordinateTransition x y) z).toLinearMap i j := by
    rw [coordinatePartial, fderiv_apply hD]
    rfl
  simpa only [Matrix.mul_apply,← hj,coordinateMatrix] using congrFun (congrFun he i) j

def coordinateDomain (g : ℂ → X.Carrier) (x : X.Carrier) : Set ℂ :=
  g ⁻¹' (chartAt (Model X) x).source

def coordinateCurve (g : ℂ → X.Carrier) (x : X.Carrier) : ℂ → Model X :=
  (chartAt (Model X) x) ∘ g

theorem coordinateDomain_open {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) (x : X.Carrier) :
    IsOpen (coordinateDomain g x) := (chartAt (Model X) x).open_source.preimage hg.continuous

theorem coordinateCurve_analytic_formal {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) (x : X.Carrier) :
    AnalyticOnNhd ℂ (coordinateCurve g x) (coordinateDomain g x) := by
  intro z hz
  have hc := contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hz
  exact (hc.comp z (hg z)).contDiffAt.analyticAt

 

def localJet {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) (x : X.Carrier) :
    ℕ → ℂ → Model X := Classical.choose
  (exists_cauchyOn (coordinateDomain_open hg x) (coordinateCurve g x)
    (fun i z hz => analyticAt_pi_iff.mp (coordinateCurve_analytic_formal hg x z hz) i)
    (S.coordinateMatrix x) (fun i j _ hz => S.coordinateMatrix_analytic x i j _
      ((chartAt (Model X) x).map_source hz)))

theorem localJet_solution {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) (x : X.Carrier) :
    CauchyOn (coordinateDomain g x) (coordinateCurve g x) (S.coordinateMatrix x)
      (S.localJet hg x) := Classical.choose_spec _

 

theorem localJet_target_glue {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) (x y : X.Carrier)
    (n : ℕ) {u : ℂ} (hx : u ∈ coordinateDomain g x) (hy : u ∈ coordinateDomain g y) :
    composeJet (coordinateTransition x y) (fun k => S.localJet hg x k u) n =
      S.localJet hg y n u := by
  let U := coordinateDomain g x ∩ coordinateDomain g y
  have hU : IsOpen U := (coordinateDomain_open hg x).inter (coordinateDomain_open hg y)
  have hgxy : Set.EqOn (coordinateCurve g y)
      (coordinateTransition x y ∘ coordinateCurve g x) U := by
    intro u hu
    change (chartAt (Model X) y) (g u) =
      (chartAt (Model X) y) ((chartAt (Model X) x).symm ((chartAt (Model X) x) (g u)))
    rw [(chartAt (Model X) x).left_inv hu.1]
  have htarget (u : ℂ) (hu : u ∈ U) :
      coordinateTransition x y (coordinateCurve g x u) = coordinateCurve g y u :=
    (hgxy hu).symm
  have hH : ∀ u ∈ U, AnalyticAt ℂ (coordinateTransition x y) (coordinateCurve g x u) := by
    intro u hu
    apply coordinateTransition_analytic x y ((chartAt (Model X) x).map_source hu.1)
    simpa only [coordinateCurve,Function.comp_apply,(chartAt (Model X) x).left_inv hu.1]
      using (show g u ∈ (chartAt (Model X) y).source from hu.2)
  have hP : ∀ i j u, u ∈ U → AnalyticAt ℂ (S.coordinateMatrix x i j) (coordinateCurve g x u) := by
    intro i j u hu
    exact S.coordinateMatrix_analytic x i j _ ((chartAt (Model X) x).map_source hu.1)
  have hQ : ∀ i j u, u ∈ U → AnalyticAt ℂ (S.coordinateMatrix y i j)
      (coordinateTransition x y (coordinateCurve g x u)) := by
    intro i j u hu
    rw [htarget u hu]
    exact S.coordinateMatrix_analytic y i j _ ((chartAt (Model X) y).map_source hu.2)
  apply cauchyOn_target_glue hU ((S.localJet_solution hg x).mono Set.inter_subset_left)
    (coordinateTransition x y) (S.coordinateMatrix y)
    (((S.localJet_solution hg y).mono Set.inter_subset_right).congr_initial hgxy)
    hH hP hQ ?_ n u ⟨hx,hy⟩
  intro u hu i j
  have hcx := (chartAt (Model X) x).map_source hu.1
  have hcy : (chartAt (Model X) x).symm (coordinateCurve g x u) ∈
      (chartAt (Model X) y).source := by
    simpa only [coordinateCurve,Function.comp_apply,(chartAt (Model X) x).left_inv hu.1] using (show g u ∈ (chartAt (Model X) y).source from hu.2)
  have hnear := ((chartAt (Model X) x).symm.continuousAt hcx).preimage_mem_nhds
    ((chartAt (Model X) y).open_source.mem_nhds hcy)
  filter_upwards [(chartAt (Model X) x).open_target.mem_nhds hcx,hnear] with z hz hzy
  exact S.coordinateMatrix_intertwining x y hz hzy i j

end

section
open HolomorphicJets PowerSeries
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

def scalarCoordinate (h : X.Carrier → ℂ) (x : X.Carrier) : Model X → ℂ :=
  h ∘ (chartAt (Model X) x).symm

theorem scalarCoordinate_analytic {h : X.Carrier → ℂ} {x a : X.Carrier}
    (ha : a ∈ (chartAt (Model X) x).source)
    (hh : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω h a) :
    AnalyticAt ℂ (scalarCoordinate h x) ((chartAt (Model X) x) a) := by
  have ht := (chartAt (Model X) x).map_source ha
  have hc := contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) ht
  have hh' : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω h
      ((chartAt (Model X) x).symm ((chartAt (Model X) x) a)) := by
    rw [(chartAt (Model X) x).left_inv ha]
    exact hh
  exact (hh'.comp _ hc).contDiffAt.analyticAt

 

theorem localJet_scalar_glue {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (h : X.Carrier → ℂ) (x y : X.Carrier) {u : ℂ}
    (hx : u ∈ coordinateDomain g x) (hy : u ∈ coordinateDomain g y)
    (hh : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω h (g u)) :
    formalSubst (scalarCoordinate h y) (fun k => S.localJet hg y k u) =
      formalSubst (scalarCoordinate h x) (fun k => S.localJet hg x k u) := by
  have hf0 : S.localJet hg x 0 u = coordinateCurve g x u := (S.localJet_solution hg x).2.1 u hx
  have htx : coordinateTransition x y (coordinateCurve g x u) = coordinateCurve g y u := by
    simp only [coordinateTransition,coordinateCurve,Function.comp_apply,
      (chartAt (Model X) x).left_inv hx]
  have hH : AnalyticAt ℂ (coordinateTransition x y) (S.localJet hg x 0 u) := by
    rw [hf0]
    apply coordinateTransition_analytic x y ((chartAt (Model X) x).map_source hx)
    simpa only [coordinateCurve,Function.comp_apply,(chartAt (Model X) x).left_inv hx]
      using (show g u ∈ (chartAt (Model X) y).source from hy)
  have hh' : AnalyticAt ℂ (scalarCoordinate h y)
      (coordinateTransition x y (S.localJet hg x 0 u)) := by
    rw [hf0,htx]
    exact scalarCoordinate_analytic hy hh
  have hj : (fun k => S.localJet hg y k u) =
      composeJet (coordinateTransition x y) (fun k => S.localJet hg x k u) := by
    funext k
    exact (S.localJet_target_glue hg x y k hx hy).symm
  rw [hj,formalSubst_assoc _ _ _ hH hh']
  apply formalSubst_congr
  rw [hf0]
  have hcx := (chartAt (Model X) x).map_source hx
  have hcy : (chartAt (Model X) x).symm (coordinateCurve g x u) ∈
      (chartAt (Model X) y).source := by
    simpa only [coordinateCurve,Function.comp_apply,(chartAt (Model X) x).left_inv hx]
      using (show g u ∈ (chartAt (Model X) y).source from hy)
  have hnear := ((chartAt (Model X) x).symm.continuousAt hcx).preimage_mem_nhds
    ((chartAt (Model X) y).open_source.mem_nhds hcy)
  filter_upwards [hnear] with z hz
  change h ((chartAt (Model X) y).symm ((chartAt (Model X) y)
    ((chartAt (Model X) x).symm z))) = h ((chartAt (Model X) x).symm z)
  rw [(chartAt (Model X) y).left_inv hz]

 

def scalarJet {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (h : X.Carrier → ℂ) (u : ℂ) : PowerSeries ℂ :=
  formalSubst (scalarCoordinate h (g u)) (fun k => S.localJet hg (g u) k u)

theorem scalarJet_eq_local {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (h : X.Carrier → ℂ) (x : X.Carrier) {u : ℂ}
    (hx : u ∈ coordinateDomain g x)
    (hh : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω h (g u)) :
    S.scalarJet hg h u = formalSubst (scalarCoordinate h x) (fun k => S.localJet hg x k u) :=
  S.localJet_scalar_glue hg h x (g u) hx (mem_chart_source (Model X) (g u)) hh

@[simp] theorem scalarJet_constant {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (h : X.Carrier → ℂ) (u : ℂ) : constantCoeff (S.scalarJet hg h u) = h (g u) := by
  have hf0 := (S.localJet_solution hg (g u)).2.1 u (mem_chart_source (Model X) (g u))
  simp only [scalarJet,formalSubst,← coeff_zero_eq_constantCoeff,coeff_mk,
    composeCoefficient,DiagonalRationality.coeff_taylorSeries,iteratedDeriv_zero,
    Nat.factorial_zero,Nat.cast_one,div_one,jetPolynomial_zero]
  rw [hf0]
  simp only [scalarCoordinate,coordinateCurve,Function.comp_apply,
    (chartAt (Model X) (g u)).left_inv (mem_chart_source (Model X) (g u))]

 

theorem scalarJet_analytic {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    {V : Set X.Carrier} (hV : IsOpen V) (h : X.Carrier → ℂ)
    (hh : ContMDiffOn (ModelWithCorners X) 𝓘(ℂ,ℂ) ω h V)
    {u : ℂ} (hu : g u ∈ V) (n : ℕ) : AnalyticAt ℂ (fun z => coeff n (S.scalarJet hg h z)) u := by
  let x := g u
  have hx : u ∈ coordinateDomain g x := mem_chart_source (Model X) x
  have hf := S.localJet_solution hg x
  have hhAt := hh.contMDiffAt (hV.mem_nhds hu)
  have hcoord : AnalyticAt ℂ (scalarCoordinate h x) (S.localJet hg x 0 u) := by
    rw [hf.2.1 u hx]
    exact scalarCoordinate_analytic hx hhAt
  apply (composeCoefficient_analytic n (fun k _ i => hf.1 k i u hx) hcoord).congr
  have hnear := (coordinateDomain_open hg x).mem_nhds hx
  have hnearV := hg.continuous.continuousAt.preimage_mem_nhds (hV.mem_nhds hu)
  filter_upwards [hnear,hnearV] with z hzx hzV
  simpa only [coeff_formalSubst] using
    (congrArg (coeff n) (S.scalarJet_eq_local hg h x hzx
      (hh.contMDiffAt (hV.mem_nhds hzV)))).symm



 

theorem localJet_source_glue {g g' : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (hg' : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g')
    {W : Set ℂ} (hW : IsOpen W) (α : ℂ → ℂ) (hα : AnalyticOnNhd ℂ α W)
    (he : Set.EqOn g' (g ∘ α) W) (x : X.Carrier) {u : ℂ}
    (hu : u ∈ W) (hx : u ∈ coordinateDomain g' x) (n : ℕ) :
    reparamJet (sourceNormal α u) (fun k => S.localJet hg x k (α u)) n =
      S.localJet hg' x n u := by
  let U := coordinateDomain g x
  let W' := W ∩ coordinateDomain g' x
  have hU : IsOpen U := coordinateDomain_open hg x
  have hW' : IsOpen W' := hW.inter (coordinateDomain_open hg' x)
  have hα' : AnalyticOnNhd ℂ α W' := hα.mono Set.inter_subset_left
  have hαU : MapsTo α W' U := by
    intro z hz
    change g (α z) ∈ (chartAt (Model X) x).source
    rw [← (show g' z = g (α z) from he hz.1)]
    exact hz.2
  have he' : Set.EqOn (coordinateCurve g' x) (coordinateCurve g x ∘ α) W' := by
    intro z hz
    change (chartAt (Model X) x) (g' z) = (chartAt (Model X) x) (g (α z))
    exact congrArg (chartAt (Model X) x) (he hz.1)
  apply cauchyOn_source_glue hU hW' (S.localJet_solution hg x) α hα' hαU
    (((S.localJet_solution hg' x).mono Set.inter_subset_right).congr_initial he')
    ?_ ?_ n u ⟨hu,hx⟩
  · intro i j z hz
    exact S.coordinateMatrix_analytic x i j _ ((chartAt (Model X) x).map_source hz)
  · intro z hz i j
    have ht := (chartAt (Model X) x).map_source hz
    filter_upwards [(chartAt (Model X) x).open_target.mem_nhds ht] with w hw
    exact S.coordinateMatrix_idempotent x hw i j

 

theorem scalarJet_source_glue {g g' : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (hg' : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g')
    {W : Set ℂ} (hW : IsOpen W) (α : ℂ → ℂ) (hα : AnalyticOnNhd ℂ α W)
    (he : Set.EqOn g' (g ∘ α) W) {u : ℂ} (hu : u ∈ W)
    (h : X.Carrier → ℂ) (hh : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω h (g' u)) :
    subst (sourceNormal α u) (S.scalarJet hg h (α u)) = S.scalarJet hg' h u := by
  let x := g' u
  have hx : u ∈ coordinateDomain g' x := mem_chart_source (Model X) x
  have he0 : g' u = g (α u) := he hu
  have hxg : α u ∈ coordinateDomain g x := by
    change g (α u) ∈ (chartAt (Model X) x).source
    rw [← he0]
    exact hx
  have hhg : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω h (g (α u)) := by
    rw [← he0]; exact hh
  rw [S.scalarJet_eq_local hg h x hxg hhg, S.scalarJet_eq_local hg' h x hx hh]
  have hj : (fun n => S.localJet hg' x n u) =
      reparamJet (sourceNormal α u) (fun n => S.localJet hg x n (α u)) := by
    funext n
    exact (S.localJet_source_glue hg hg' hW α hα he x hu hx n).symm
  rw [hj]
  have hnormal : AnalyticAt ℂ (fun v => sourceDifference α (u,v)) 0 :=
    (sourceDifference_analytic (hα u hu) (by simpa using hα u hu)).comp
      (analyticAt_const.prod analyticAt_id)
  have h0 : sourceDifference α (u,0) = 0 := by simp [sourceDifference]
  have hcoord : AnalyticAt ℂ (scalarCoordinate h x) (S.localJet hg x 0 (α u)) := by
    rw [(S.localJet_solution hg x).2.1 (α u) hxg]
    exact scalarCoordinate_analytic hxg hhg
  exact (formalSubst_reparam _ hnormal h0 hcoord).symm

end

open HolomorphicJets PowerSeries
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 
theorem scalarJet_congr {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    {h k : X.Carrier → ℂ} (u : ℂ) (he : h =ᶠ[nhds (g u)] k) :
    S.scalarJet hg h u = S.scalarJet hg k u := by
  unfold scalarJet
  apply formalSubst_congr
  rw [(S.localJet_solution hg (g u)).2.1 u (mem_chart_source (Model X) (g u))]
  have hc := (chartAt (Model X) (g u)).symm.continuousAt
    ((chartAt (Model X) (g u)).map_source (mem_chart_source (Model X) (g u)))
  have ht : Tendsto (chartAt (Model X) (g u)).symm
      (nhds (coordinateCurve g (g u) u)) (nhds (g u)) := by
    simpa only [ContinuousAt,coordinateCurve,Function.comp_apply,
      (chartAt (Model X) (g u)).left_inv (mem_chart_source (Model X) (g u))] using hc
  exact he.comp_tendsto ht

theorem scalarJet_mul {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    {h k : X.Carrier → ℂ} (u : ℂ)
    (hh : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω h (g u))
    (hk : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω k (g u)) :
    S.scalarJet hg (fun x => h x * k x) u = S.scalarJet hg h u * S.scalarJet hg k u := by
  unfold scalarJet
  apply formalSubst_mul
  · rw [(S.localJet_solution hg (g u)).2.1 u (mem_chart_source (Model X) (g u))]
    exact scalarCoordinate_analytic (mem_chart_source (Model X) (g u)) hh
  · rw [(S.localJet_solution hg (g u)).2.1 u (mem_chart_source (Model X) (g u))]
    exact scalarCoordinate_analytic (mem_chart_source (Model X) (g u)) hk

@[simp] theorem scalarJet_const {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) (c : ℂ) (u : ℂ) :
    S.scalarJet hg (fun _ => c) u = C c := by
  ext n
  simp only [scalarJet,coeff_formalSubst,composeCoefficient,scalarCoordinate,Function.comp_apply]
  rw [taylorSeries_const]

end SplitTangent.TangentSplitting

section CurveImports

open Filter Topology Polynomial
namespace SplitTangent.ProjectiveLine

 
def MeromorphicAtInfinity (f : ℂ → ℂ) : Prop :=
  MeromorphicAt (fun z => f z⁻¹) 0

 

theorem finite_nonanalytic {f : ℂ → ℂ} (hf : Meromorphic f)
    (hInf : MeromorphicAtInfinity f) : {z : ℂ | ¬ AnalyticAt ℂ f z}.Finite := by
  have he : ∀ᶠ w in nhds 0, w ≠ 0 → AnalyticAt ℂ (fun z => f z⁻¹) w := by
    simpa only [eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff] using
      hInf.eventually_analyticAt
  obtain ⟨r,hr,hrsub⟩ := Metric.eventually_nhds_iff.mp he
  have hlarge : ∀ z : ℂ, r⁻¹ < ‖z‖ → AnalyticAt ℂ f z := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h; simp only [h, norm_zero] at hz
      exact (not_lt_of_ge (inv_nonneg.mpr hr.le)) hz
    have hinv : dist z⁻¹ 0 < r := by
      rw [dist_zero_right, norm_inv, inv_lt_comm₀ (norm_pos_iff.mpr hz0) hr]
      exact hz
    have ha := hrsub hinv (inv_ne_zero hz0)
    have hc := ha.comp (analyticAt_id.inv hz0)
    simpa only [Function.comp_def, inv_inv] using hc
  have hK := (isCompact_closedBall (0 : ℂ) r⁻¹).finite_sdiff_of_mem_codiscreteWithin
    ((hf.meromorphicOn (s := Metric.closedBall 0 r⁻¹)).analyticAt_mem_codiscreteWithin)
  apply hK.subset
  intro z hz
  exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using
    (not_lt.mp (fun h => hz (hlarge z h))), hz⟩

 

theorem exists_polynomial_denominator {f : ℂ → ℂ} (hf : Meromorphic f)
    (hInf : MeromorphicAtInfinity f) :
    ∃ q : ℂ[X], q ≠ 0 ∧ Differentiable ℂ (fun z => q.eval z * f z) := by
  classical
  let B := (finite_nonanalytic hf hInf).toFinset
  choose n hn using fun x => hf x
  let q : ℂ[X] := ∏ a ∈ B, (X - C a) ^ n a
  refine ⟨q, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr (fun a ha => pow_ne_zero _ (X_sub_C_ne_zero a))
  · intro z
    by_cases hz : z ∈ B
    · have hfactor : q = (X - C z) ^ n z * ∏ a ∈ B.erase z, (X - C a) ^ n a := by
        exact (Finset.mul_prod_erase B _ hz).symm
      have han : AnalyticAt ℂ
          (fun t => (∏ a ∈ B.erase z, (X - C a) ^ n a).eval t * ((t-z)^n z * f t)) z :=
        (AnalyticOnNhd.eval_polynomial (∏ a ∈ B.erase z, (X - C a) ^ n a) z (mem_univ z)).mul
          (by simpa only [smul_eq_mul] using hn z)
      apply han.differentiableAt.congr_of_eventuallyEq
      filter_upwards with t
      simp only [hfactor, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
      ring
    · have hz' : AnalyticAt ℂ f z := by simpa [B] using hz
      exact (by fun_prop : DifferentiableAt ℂ (fun t => q.eval t) z).mul hz'.differentiableAt

 

theorem polynomial_growth_atInfinity {f : ℂ → ℂ} (hInf : MeromorphicAtInfinity f) :
    ∃ (n : ℕ) (C R : ℝ), ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖^n := by
  obtain ⟨n,hn⟩ := hInf
  let h : ℂ → ℂ := fun w => w^n * f w⁻¹
  have hh : AnalyticAt ℂ h 0 := by simpa [h, smul_eq_mul] using hn
  have he : ∀ᶠ w in nhds 0, ‖h w‖ < ‖h 0‖ + 1 :=
    hh.continuousAt.norm.eventually_lt_const (by linarith)
  obtain ⟨r,hr,hrsub⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨n, ‖h 0‖+1, max 1 (r⁻¹+1), ?_⟩
  intro z hz
  have hzn : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hz)
  have hzlarge : r⁻¹ < ‖z‖ := by have := (le_max_right 1 (r⁻¹+1)).trans hz; linarith
  have hw : dist z⁻¹ 0 < r := by
    rw [dist_zero_right, norm_inv, inv_lt_comm₀ hzn hr]
    exact hzlarge
  have hb : ‖h z⁻¹‖ ≤ ‖h 0‖+1 := (hrsub hw).le
  have heq : ‖f z‖ = ‖z‖^n * ‖h z⁻¹‖ := by
    simp only [h, inv_inv, norm_mul, norm_pow, norm_inv]
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hzn.ne', one_pow, one_mul]
  rw [heq]
  exact (mul_le_mul_of_nonneg_left hb (pow_nonneg (norm_nonneg _) _)).trans_eq (mul_comm _ _)

 
theorem iteratedDeriv_zero_of_tail_growth {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {n : ℕ} {C R₀ : ℝ} (hbound : ∀ z : ℂ, R₀ ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖^n)
    {k : ℕ} (hk : n < k) : iteratedDeriv k f 0 = 0 := by
  have hb : ∀ R : ℝ, max 1 R₀ ≤ R →
      ‖iteratedDeriv k f 0‖ ≤ (k.factorial : ℝ) * C / R^(k-n) := by
    intro R hR
    have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hR)
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0) k hR0
      hf.diffContOnCl (fun z hz => by
        have hzR : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_zero_right] using hz
        simpa only [hzR] using hbound z (hzR ▸ ((le_max_right _ _).trans hR)))
    convert h using 1
    rw [pow_sub₀ R hR0.ne' hk.le]
    field_simp
  apply norm_le_zero_iff.mp
  apply ge_of_tendsto (show Tendsto (fun R : ℝ => (k.factorial : ℝ) * C / R^(k-n))
      atTop (nhds 0) from tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega)))
  exact (eventually_ge_atTop (max 1 R₀)).mono (fun R hR => hb R hR)

 

theorem exists_polynomial_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hInf : MeromorphicAtInfinity f) : ∃ p : ℂ[X], ∀ z, f z = p.eval z := by
  obtain ⟨n,C,R,hb⟩ := polynomial_growth_atInfinity hInf
  refine ⟨∑ k ∈ Finset.range (n+1), monomial k ((k.factorial : ℂ)⁻¹ * iteratedDeriv k f 0), ?_⟩
  intro z
  rw [← Complex.taylorSeries_eq_of_entire' 0 z hf]
  rw [tsum_eq_sum (s := Finset.range (n+1)) (fun k hk => by
    have hnk : n < k := by simpa using hk
    rw [iteratedDeriv_zero_of_tail_growth hf hb hnk]
    simp)]
  simp [Polynomial.eval_finsetSum, Polynomial.eval_monomial]

 
theorem meromorphicAt_polynomial_eval {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x)
    (p : ℂ[X]) : MeromorphicAt (fun z => p.eval (f z)) x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [eval_add, Pi.add_apply] using hp.fun_add hq
  | monomial n a => simpa only [eval_monomial, Pi.mul_apply, Pi.pow_apply] using (MeromorphicAt.const a x).fun_mul (hf.fun_pow n)

 

theorem rationality {f : ℂ → ℂ} (hf : Meromorphic f)
    (hInf : MeromorphicAtInfinity f) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z, q.eval z * f z = p.eval z) ∧
      ∀ z, q.eval z ≠ 0 → f z = p.eval z / q.eval z := by
  obtain ⟨q,hq,hqf⟩ := exists_polynomial_denominator hf hInf
  have hqInf : MeromorphicAtInfinity (fun z => q.eval z * f z) := by
    exact (meromorphicAt_polynomial_eval (MeromorphicAt.id 0).inv q).mul hInf
  obtain ⟨p,hp⟩ := exists_polynomial_of_entire hqf hqInf
  refine ⟨p,q,hq,hp,?_⟩
  intro z hz
  exact (eq_div_iff hz).mpr (by simpa only [mul_comm] using hp z)

end SplitTangent.ProjectiveLine

namespace SplitTangent

 

theorem projectiveCoordinates_change {N : ℕ} (p : ProjectiveSpace N)
    (i j k : Fin (N+1)) (hk : p.rep k ≠ 0) :
    projectiveCoordinates i p j = projectiveCoordinates k p j / projectiveCoordinates k p i := by
  simp only [projectiveCoordinates, div_eq_mul_inv, mul_inv_rev, inv_inv]
  calc
    (p.rep i)⁻¹ * p.rep j = ((p.rep k)⁻¹ * p.rep k) * ((p.rep i)⁻¹ * p.rep j) := by
      rw [inv_mul_cancel₀ hk, one_mul]
    _ = _ := by ring

 

theorem projective_ratio_meromorphic {X : ComplexManifold.{u}}
    (e : ProjectiveEmbedding X) (g : ℂ → X.Carrier)
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (i j : Fin (e.N+1)) : Meromorphic (fun z => projectiveCoordinates i (e.map (g z)) j) := by
  intro z
  obtain ⟨k,hk⟩ : ∃ k, (e.map (g z)).rep k ≠ 0 := by
    by_contra h
    push Not at h
    exact (e.map (g z)).rep_nonzero (funext h)
  have ha : AnalyticAt ℂ (fun w => projectiveCoordinates k (e.map (g w))) z :=
    (((e.holomorphic k).contMDiffAt ((e.open_patch k).mem_nhds hk)).comp z
      hg.contMDiffAt).contDiffAt.analyticAt
  have hj : AnalyticAt ℂ (fun w => projectiveCoordinates k (e.map (g w)) j) z :=
    (ContinuousLinearMap.proj j : (Fin (e.N+1) → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp ha
  have hi : AnalyticAt ℂ (fun w => projectiveCoordinates k (e.map (g w)) i) z :=
    (ContinuousLinearMap.proj i : (Fin (e.N+1) → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp ha
  apply (hj.meromorphicAt.div hi.meromorphicAt).congr
  apply Filter.EventuallyEq.filter_mono _ nhdsWithin_le_nhds
  filter_upwards [hg.continuous.continuousAt.preimage_mem_nhds ((e.open_patch k).mem_nhds hk)] with w hw
  exact (projectiveCoordinates_change (e.map (g w)) i j k hw).symm

 

theorem rationalCurve_ratio_meromorphicAtInfinity {X : ComplexManifold.{u}}
    (e : ProjectiveEmbedding X) (g : RationalCurve X) (i j : Fin (e.N+1)) :
    ProjectiveLine.MeromorphicAtInfinity (fun z => projectiveCoordinates i (e.map (g.finite z)) j) := by
  apply (projective_ratio_meromorphic e g.infinity g.infinity_holomorphic i j 0).congr
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := hz
  rw [g.overlap z⁻¹ (inv_ne_zero hz0), inv_inv]

 

theorem rationalCurve_ratios_are_rational {X : ComplexManifold.{u}}
    (e : ProjectiveEmbedding X) (g : RationalCurve X) (i j : Fin (e.N+1)) :
    ∃ p q : ℂ[X], q ≠ 0 ∧
      (∀ z, q.eval z * projectiveCoordinates i (e.map (g.finite z)) j = p.eval z) ∧
      ∀ z, q.eval z ≠ 0 → projectiveCoordinates i (e.map (g.finite z)) j = p.eval z / q.eval z :=
  ProjectiveLine.rationality
    (projective_ratio_meromorphic e g.finite g.finite_holomorphic i j)
    (rationalCurve_ratio_meromorphicAtInfinity e g i j)

namespace PolynomialTuple

 
theorem gcd_mem_span {ι : Type*} (p : ι → ℂ[X]) (s : Finset ι) :
    s.gcd p ∈ Ideal.span (Set.range p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.gcd_insert]
    obtain ⟨a,b,h⟩ := exists_gcd_eq_mul_add_mul (p i) (s.gcd p)
    rw [h]
    exact (Ideal.span (Set.range p)).add_mem
      ((Ideal.span (Set.range p)).mul_mem_right a (Ideal.subset_span ⟨i,rfl⟩))
      ((Ideal.span (Set.range p)).mul_mem_right b ih)

 
theorem bezout {ι : Type*} [Fintype ι] (p : ι → ℂ[X])
    (hp : Finset.univ.gcd p = 1) : ∃ a : ι → ℂ[X], ∑ i, a i * p i = 1 := by
  apply Ideal.mem_span_range_iff_exists_fun.mp
  rw [← hp]
  exact gcd_mem_span p Finset.univ

 
theorem basepoint_free {ι : Type*} [Fintype ι] (p : ι → ℂ[X])
    (hp : Finset.univ.gcd p = 1) (z : ℂ) : ∃ i, (p i).eval z ≠ 0 := by
  obtain ⟨a,ha⟩ := bezout p hp
  by_contra! h
  have he := congrArg (Polynomial.eval z) ha
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, h, mul_zero,
    Finset.sum_const_zero, Polynomial.eval_one, zero_ne_one] at he

 
theorem frequently_eval_ne_zero (p : ℂ[X]) (hp : p ≠ 0) (z : ℂ) :
    ∃ᶠ w in nhds z, p.eval w ≠ 0 := by
  by_contra h
  have he : ∀ᶠ w in nhds z, p.eval w = 0 := by simpa only [not_frequently, not_ne_iff] using h
  exact hp (p.eq_zero_of_infinite_isRoot (infinite_of_mem_nhds z he))

 

theorem common_denominator {ι : Type*} [Fintype ι] (f : ι → ℂ → ℂ)
    (hf : ∀ i, ∃ p q : ℂ[X], q ≠ 0 ∧ ∀ z, q.eval z * f i z = p.eval z) :
    ∃ (P : ι → ℂ[X]) (Q : ℂ[X]), Q ≠ 0 ∧ ∀ i z, Q.eval z * f i z = (P i).eval z := by
  classical
  choose p q hq he using hf
  let Q : ℂ[X] := ∏ j, q j
  let P : ι → ℂ[X] := fun i => p i * ∏ j ∈ Finset.univ.erase i, q j
  refine ⟨P,Q,Finset.prod_ne_zero_iff.mpr (fun i _ => hq i),?_⟩
  intro i z
  have hQ : Q = q i * ∏ j ∈ Finset.univ.erase i, q j :=
    (Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i)).symm
  simp only [P,hQ,Polynomial.eval_mul]
  rw [mul_assoc, mul_comm ((∏ j ∈ Finset.univ.erase i, q j).eval z), ← mul_assoc, he]

end PolynomialTuple

 

theorem rationalCurve_polynomial_presentation {X : ComplexManifold.{u}}
    (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ P : Fin (e.N+1) → ℂ[X], Finset.univ.gcd P = 1 ∧
      ∀ (z : ℂ) (k j : Fin (e.N+1)), (e.map (g.finite z)).rep k ≠ 0 →
        (P j).eval z = projectiveCoordinates k (e.map (g.finite z)) j * (P k).eval z := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, (e.map (g.finite 0)).rep i ≠ 0 := by
    by_contra! h
    exact (e.map (g.finite 0)).rep_nonzero (funext h)
  obtain ⟨A,Q,hQ,hA⟩ := PolynomialTuple.common_denominator
    (fun j z => projectiveCoordinates i (e.map (g.finite z)) j)
    (fun j => by
      obtain ⟨p,q,hq,hpq,_⟩ := rationalCurve_ratios_are_rational e g i j
      exact ⟨p,q,hq,hpq⟩)
  have hAi : A i = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply infinite_of_mem_nhds (0 : ℂ)
    filter_upwards [g.finite_holomorphic.continuous.continuousAt.preimage_mem_nhds
      ((e.open_patch i).mem_nhds hi)] with z hz
    rw [← hA i z]
    simp only [projectiveCoordinates, inv_mul_cancel₀ hz, mul_one]
  let D := Finset.univ.gcd A
  have hD : D ≠ 0 := Finset.gcd_ne_zero_iff.mpr ⟨i,Finset.mem_univ i,hAi ▸ hQ⟩
  obtain ⟨P,hAP,hP⟩ := Finset.extract_gcd A (Finset.univ_nonempty)
  have hAP' : ∀ j, A j = D * P j := fun j => hAP j (Finset.mem_univ j)
  refine ⟨P,hP,?_⟩
  intro z k j hk
  have hnear : ∀ᶠ w in nhds z, (e.map (g.finite w)).rep k ≠ 0 :=
    g.finite_holomorphic.continuous.continuousAt.preimage_mem_nhds ((e.open_patch k).mem_nhds hk)
  have hc : ContinuousAt (fun w => projectiveCoordinates k (e.map (g.finite w)) j) z :=
    (continuous_apply j).continuousAt.comp
      (((e.holomorphic k).contMDiffAt ((e.open_patch k).mem_nhds hk)).comp z
        g.finite_holomorphic.contMDiffAt).continuousAt
  apply tendsto_nhds_unique_of_frequently_eq
    (by fun_prop : ContinuousAt (fun w => (P j).eval w) z)
    (hc.mul (by fun_prop : ContinuousAt (fun w => (P k).eval w) z))
  apply ((PolynomialTuple.frequently_eval_ne_zero D hD z).and_eventually hnear).mono
  rintro w ⟨hw,hkw⟩
  have hAw : ∀ l, Q.eval w * projectiveCoordinates i (e.map (g.finite w)) l =
      D.eval w * (P l).eval w := by
    intro l
    rw [hA l w,hAP' l,Polynomial.eval_mul]
  have hiw : (e.map (g.finite w)).rep i ≠ 0 := by
    intro hzero
    obtain ⟨l,hl⟩ := PolynomialTuple.basepoint_free P hP w
    have he := hAw l
    simp only [projectiveCoordinates,hzero,inv_zero,zero_mul,mul_zero] at he
    exact hl ((mul_eq_zero.mp he.symm).resolve_left hw)
  have he : D.eval w * (P j).eval w =
      projectiveCoordinates k (e.map (g.finite w)) j * (D.eval w * (P k).eval w) := by
    rw [← hAw j,← hAw k]
    simp only [projectiveCoordinates]
    field_simp
  change (P j).eval w = projectiveCoordinates k (e.map (g.finite w)) j * (P k).eval w
  exact mul_left_cancel₀ hw (he.trans (by ring))

namespace PolynomialTuple

theorem primitive_of_basepoint_free {ι : Type*} [Fintype ι] (P : ι → ℂ[X])
    (hP : ∀ z : ℂ, ∃ i, (P i).eval z ≠ 0) : Finset.univ.gcd P = 1 := by
  classical
  rw [← Finset.normalize_gcd, normalize_eq_one]
  apply Polynomial.isUnit_iff_degree_eq_zero.mpr
  by_contra h
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_root (Finset.univ.gcd P) h
  obtain ⟨i,hi⟩ := hP z
  exact hi (hz.dvd (Finset.gcd_dvd (Finset.mem_univ i)))

 
theorem reflect_transition (p : ℂ[X]) (d : ℕ) (hp : p.natDegree ≤ d)
    (z : ℂ) (hz : z ≠ 0) : (p.reflect d).eval z⁻¹ * z^d = p.eval z := by
  let := invertibleOfNonzero hz
  simpa only [invOf_eq_inv, Polynomial.eval₂_id] using
    Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) z d p hp

 

theorem exists_primitive_reflection {ι : Type*} [Fintype ι] (P : ι → ℂ[X])
    (hP : Finset.univ.gcd P = 1) :
    ∃ d : ℕ, (∀ i, (P i).natDegree ≤ d) ∧
      Finset.univ.gcd (fun i => (P i).reflect d) = 1 := by
  classical
  let I := Finset.univ.filter (fun i => P i ≠ 0)
  have hI : I.Nonempty := by
    obtain ⟨i,hi⟩ := basepoint_free P hP 0
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,fun h => hi (h ▸ Polynomial.eval_zero)⟩⟩
  obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image I (fun j => (P j).natDegree) hI
  have hi0 := (Finset.mem_filter.mp hi).2
  have hbound : ∀ j, (P j).natDegree ≤ (P i).natDegree := by
    intro j
    by_cases hj : P j = 0
    · simp only [hj,Polynomial.natDegree_zero,Nat.zero_le]
    · exact hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ j,hj⟩)
  refine ⟨(P i).natDegree,hbound,primitive_of_basepoint_free _ ?_⟩
  intro z
  by_cases hz : z = 0
  · refine ⟨i,?_⟩
    simpa only [hz,← Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_reflect,Polynomial.revAt_zero,
      Polynomial.coeff_natDegree] using (Polynomial.leadingCoeff_ne_zero.mpr hi0)
  · obtain ⟨j,hj⟩ := basepoint_free P hP z⁻¹
    refine ⟨j,?_⟩
    intro he
    have ht := reflect_transition (P j) (P i).natDegree (hbound j) z⁻¹ (inv_ne_zero hz)
    rw [inv_inv,he,zero_mul] at ht
    exact hj ht.symm

end PolynomialTuple

 

theorem rationalCurve_two_chart_polynomials {X : ComplexManifold.{u}}
    (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ (d : ℕ) (P Q : Fin (e.N+1) → ℂ[X]),
      Finset.univ.gcd P = 1 ∧ Finset.univ.gcd Q = 1 ∧
      (∀ i, (P i).natDegree ≤ d ∧ Q i = (P i).reflect d) ∧
      (∀ z k j, (e.map (g.finite z)).rep k ≠ 0 →
        (P j).eval z = projectiveCoordinates k (e.map (g.finite z)) j * (P k).eval z) ∧
      (∀ z k j, (e.map (g.infinity z)).rep k ≠ 0 →
        (Q j).eval z = projectiveCoordinates k (e.map (g.infinity z)) j * (Q k).eval z) ∧
      (∀ z, z ≠ 0 → ∀ i, (P i).eval z = z^d * (Q i).eval z⁻¹) := by
  obtain ⟨P,hP,hfinite⟩ := rationalCurve_polynomial_presentation e g
  obtain ⟨d,hd,hQ⟩ := PolynomialTuple.exists_primitive_reflection P hP
  let Q : Fin (e.N+1) → ℂ[X] := fun i => (P i).reflect d
  have htrans : ∀ z, z ≠ 0 → ∀ i, (P i).eval z = z^d * (Q i).eval z⁻¹ := by
    intro z hz i
    exact (PolynomialTuple.reflect_transition (P i) d (hd i) z hz).symm.trans (mul_comm _ _)
  refine ⟨d,P,Q,hP,hQ,fun i => ⟨hd i,rfl⟩,hfinite,?_,htrans⟩
  intro z k j hk
  have hnear : ∀ᶠ w in nhds z, (e.map (g.infinity w)).rep k ≠ 0 :=
    g.infinity_holomorphic.continuous.continuousAt.preimage_mem_nhds ((e.open_patch k).mem_nhds hk)
  have hc : ContinuousAt (fun w => projectiveCoordinates k (e.map (g.infinity w)) j) z :=
    (continuous_apply j).continuousAt.comp
      (((e.holomorphic k).contMDiffAt ((e.open_patch k).mem_nhds hk)).comp z
        g.infinity_holomorphic.contMDiffAt).continuousAt
  apply tendsto_nhds_unique_of_frequently_eq
    (by fun_prop : ContinuousAt (fun w => (Q j).eval w) z)
    (hc.mul (by fun_prop : ContinuousAt (fun w => (Q k).eval w) z))
  have hfreq : ∃ᶠ w in nhds z, w ≠ (0 : ℂ) := by
    simpa only [Polynomial.eval_X] using
      PolynomialTuple.frequently_eval_ne_zero Polynomial.X Polynomial.X_ne_zero z
  apply (hfreq.and_eventually hnear).mono
  rintro w ⟨hw,hkw⟩
  change (Q j).eval w = projectiveCoordinates k (e.map (g.infinity w)) j * (Q k).eval w
  have ho := g.overlap w⁻¹ (inv_ne_zero hw)
  simp only [inv_inv] at ho
  have he := hfinite w⁻¹ k j (ho ▸ hkw)
  rw [ho,htrans w⁻¹ (inv_ne_zero hw) j,htrans w⁻¹ (inv_ne_zero hw) k,inv_inv] at he
  exact mul_left_cancel₀ (pow_ne_zero d (inv_ne_zero hw)) (he.trans (by ring))

end SplitTangent

end CurveImports

namespace SplitTangent
open HolomorphicJets FormalProjective PowerSeries
variable {X : ComplexManifold.{u}}

 

theorem ProjectiveEmbedding.scalar_holomorphic (e : ProjectiveEmbedding X)
    (k j : Fin (e.N+1)) : ContMDiffOn (ModelWithCorners X) 𝓘(ℂ,ℂ) ω
      (fun x => projectiveCoordinates k (e.map x) j) {x | (e.map x).rep k ≠ 0} :=
  (ContinuousLinearMap.proj j : (Fin (e.N+1) → ℂ) →L[ℂ] ℂ).contMDiff.comp_contMDiffOn
    (e.holomorphic k)

theorem projectiveCoordinates_mul {N : ℕ} (p : ProjectiveSpace N)
    (k l j : Fin (N+1)) (hl : p.rep l ≠ 0) :
    projectiveCoordinates k p l * projectiveCoordinates l p j = projectiveCoordinates k p j := by
  simp only [projectiveCoordinates]
  calc
    (p.rep k)⁻¹ * p.rep l * ((p.rep l)⁻¹ * p.rep j) =
      (p.rep k)⁻¹ * (p.rep l * (p.rep l)⁻¹) * p.rep j := by ring
    _ = _ := by rw [mul_inv_cancel₀ hl,mul_one]

 
theorem polynomial_presentation_patch (e : ProjectiveEmbedding X)
    {g : ℂ → X.Carrier} {p : Fin (e.N+1) → Polynomial ℂ}
    (hp : Finset.univ.gcd p = 1)
    (hpres : ∀ z k j, (e.map (g z)).rep k ≠ 0 →
      (p j).eval z = projectiveCoordinates k (e.map (g z)) j * (p k).eval z)
    (z : ℂ) (k : Fin (e.N+1)) : (p k).eval z ≠ 0 ↔ (e.map (g z)).rep k ≠ 0 := by
  constructor
  · intro hk hzero
    obtain ⟨l,hl⟩ : ∃ l, (e.map (g z)).rep l ≠ 0 := by
      by_contra! h
      exact (e.map (g z)).rep_nonzero (funext h)
    have he := hpres z l k hl
    simp only [projectiveCoordinates,hzero,mul_zero,zero_mul] at he
    exact hk he
  · intro hk hzero
    obtain ⟨j,hj⟩ := PolynomialTuple.basepoint_free p hp z
    have he := hpres z k j hk
    rw [hzero,mul_zero] at he
    exact hj he

namespace TangentSplitting
variable (S : TangentSplitting X)

 

def projectiveChartData (e : ProjectiveEmbedding X) {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (p : Fin (e.N+1) → Polynomial ℂ) (hp : Finset.univ.gcd p = 1)
    (hpres : ∀ z k j, (e.map (g z)).rep k ≠ 0 →
      (p j).eval z = projectiveCoordinates k (e.map (g z)) j * (p k).eval z) :
    ChartData p where
  basepoint_free := PolynomialTuple.basepoint_free p hp
  ratio k j z := S.scalarJet hg (fun x => projectiveCoordinates k (e.map x) j) z
  analytic k j z hk n := S.scalarJet_analytic hg (e.open_patch k) _
    (e.scalar_holomorphic k j) ((polynomial_presentation_patch e hp hpres z k).mp hk) n
  diagonal k j z hk := by
    rw [S.scalarJet_constant]
    exact (eq_div_iff hk).mpr (hpres z k j
      ((polynomial_presentation_patch e hp hpres z k).mp hk)).symm
  identity k z hk := by
    have ht := (polynomial_presentation_patch e hp hpres z k).mp hk
    calc
      S.scalarJet hg (fun x => projectiveCoordinates k (e.map x) k) z =
          S.scalarJet hg (fun _ => 1) z := by
        apply S.scalarJet_congr
        filter_upwards [(e.open_patch k).mem_nhds ht] with x hx
        exact inv_mul_cancel₀ hx
      _ = 1 := by simp
  overlap k l j z hk hl := by
    have htk := (polynomial_presentation_patch e hp hpres z k).mp hk
    have htl := (polynomial_presentation_patch e hp hpres z l).mp hl
    rw [← S.scalarJet_mul hg z
      ((e.scalar_holomorphic k l).contMDiffAt ((e.open_patch k).mem_nhds htk))
      ((e.scalar_holomorphic l j).contMDiffAt ((e.open_patch l).mem_nhds htl))]
    apply S.scalarJet_congr
    filter_upwards [(e.open_patch l).mem_nhds htl] with x hx
    exact projectiveCoordinates_mul (e.map x) k l j hx

 

theorem exists_projective_formal_data (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ (d : ℕ) (p q : Fin (e.N+1) → Polynomial ℂ) (a b : Fin (e.N+1) → Polynomial ℂ)
      (F : TwoChartData d p q),
      (∑ i, a i * p i = 1) ∧ (∑ i, b i * q i = 1) ∧
      (∀ k j z, F.finite.ratio k j z =
        S.scalarJet g.finite_holomorphic (fun x => projectiveCoordinates k (e.map x) j) z) ∧
      (∀ k j z, F.infinity.ratio k j z =
        S.scalarJet g.infinity_holomorphic (fun x => projectiveCoordinates k (e.map x) j) z) ∧
      (∀ k z, (p k).eval z ≠ 0 ↔ (e.map (g.finite z)).rep k ≠ 0) := by
  obtain ⟨d,p,q,hp,hq,_,hfinite,hinfinity,htrans⟩ := rationalCurve_two_chart_polynomials e g
  obtain ⟨a,ha⟩ := PolynomialTuple.bezout p hp
  obtain ⟨b,hb⟩ := PolynomialTuple.bezout q hq
  let F₀ := S.projectiveChartData e g.finite_holomorphic p hp hfinite
  let FInfty := S.projectiveChartData e g.infinity_holomorphic q hq hinfinity
  have ho : ∀ k j z, z ≠ 0 → (p k).eval z ≠ 0 →
      F₀.ratio k j z = subst (DiagonalRationality.reciprocalNormal z) (FInfty.ratio k j z⁻¹) := by
    intro k j z hz hk
    have ht := (polynomial_presentation_patch e hp hfinite z k).mp hk
    have he : Set.EqOn g.finite (g.infinity ∘ fun z : ℂ => z⁻¹) {z : ℂ | z ≠ 0} := by
      intro z hz; exact g.overlap z hz
    have hi : AnalyticOnNhd ℂ (fun z : ℂ => z⁻¹) {z : ℂ | z ≠ 0} := by
      intro z hz; exact analyticAt_id.fun_inv hz
    have hs := S.scalarJet_source_glue g.infinity_holomorphic g.finite_holomorphic
      (isOpen_ne_fun continuous_id continuous_const) (fun z : ℂ => z⁻¹) hi he hz
      (fun x => projectiveCoordinates k (e.map x) j)
      ((e.scalar_holomorphic k j).contMDiffAt ((e.open_patch k).mem_nhds ht))
    rw [sourceNormal_inv z hz] at hs
    exact hs.symm
  let F : TwoChartData d p q := ⟨F₀,FInfty,htrans,ho⟩
  exact ⟨d,p,q,a,b,F,ha,hb,fun _ _ _ => rfl,fun _ _ _ => rfl,
    fun k z => polynomial_presentation_patch e hp hfinite z k⟩

end TangentSplitting
end SplitTangent
namespace SplitTangent.TangentSplitting
open HolomorphicJets FormalProjective DiagonalRationality PowerSeries
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

theorem exists_convergent_projective_patch (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ (k : Fin (e.N+1)) (A B : Fin (e.N+1) → Polynomial (ℂ → ℂ)) (U : Set ℂ),
      IsOpen U ∧ U.Nonempty ∧ ∀ z ∈ U, (e.map (g.finite z)).rep k ≠ 0 ∧ ∀ j,
        (B j).coeff 0 z ≠ 0 ∧
        AnalyticAt ℂ (fun w => -polynomialEvaluation (A j) w / polynomialEvaluation (B j) w) (z,0) ∧
        HasFPowerSeriesAt
          (fun v => -polynomialEvaluation (A j) (z,v) / polynomialEvaluation (B j) (z,v))
          (FormalMultilinearSeries.ofScalars ℂ (fun n => coeff n
            (S.scalarJet g.finite_holomorphic (fun x => projectiveCoordinates k (e.map x) j) z))) 0 := by
  obtain ⟨d,p,q,a,b,F,ha,hb,hfinite,_,hpatch⟩ := S.exists_projective_formal_data e g
  obtain ⟨k,A,B,U,hU,hUn,hR⟩ := reconstruct_projective_map F a b ha hb
  refine ⟨k,A,B,U,hU,hUn,?_⟩
  intro z hz
  obtain ⟨hk,hj⟩ := hR z hz
  refine ⟨(hpatch k z).mp hk,fun j => ⟨(hj j).1,(hj j).2.1,?_⟩⟩
  simpa only [hfinite] using (hj j).2.2

end SplitTangent.TangentSplitting

open Filter Topology

namespace AnalyticRetraction
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]

 

omit [CompleteSpace F] in
theorem localInverse_analytic {f : E → F} {a : E} (hf : AnalyticAt ℂ f a)
    (i : E ≃L[ℂ] F) (hi : fderiv ℂ f a = i.toContinuousLinearMap) :
    AnalyticAt ℂ ((hi ▸ hf.hasStrictFDerivAt).localInverse f i a) (f a) := by
  have hd : HasStrictFDerivAt f i.toContinuousLinearMap a := hi ▸ hf.hasStrictFDerivAt
  let R := hd.toOpenPartialHomeomorph f
  have hx : a ∈ R.source := hd.mem_toOpenPartialHomeomorph_source
  obtain ⟨p,hp⟩ := hf
  have h1 : p 1 = (continuousMultilinearCurryFin1 ℂ E F).symm i.toContinuousLinearMap := by
    apply (continuousMultilinearCurryFin1 ℂ E F).injective
    rw [LinearIsometryEquiv.apply_symm_apply, ← hp.fderiv_eq, hi]
  exact (R.hasFPowerSeriesAt_symm hx hp h1).analyticAt

 

omit [CompleteSpace F] in
theorem exists_left_inverse [FiniteDimensional ℂ F] {f : E → F} {a : E}
    (hf : AnalyticAt ℂ f a) (hinj : Function.Injective (fderiv ℂ f a)) :
    ∃ r : F → E, AnalyticAt ℂ r (f a) ∧ r (f a) = a ∧
      ∀ᶠ x in 𝓝 a, r (f x) = x := by
  let D := fderiv ℂ f a
  obtain ⟨L,hL⟩ := LinearMap.exists_leftInverse_of_injective D.toLinearMap
    (LinearMap.ker_eq_bot.mpr hinj)
  let C : F →L[ℂ] E := L.toContinuousLinearMap
  have hC : C.comp D = ContinuousLinearMap.id ℂ E := by
    ext x
    exact congrArg (fun T : E →ₗ[ℂ] E => T x) hL
  let g : E → E := C ∘ f
  have hg : AnalyticAt ℂ g a := (C.analyticAt _).comp hf
  have hd : fderiv ℂ g a = (ContinuousLinearEquiv.refl ℂ E).toContinuousLinearMap := by
    rw [fderiv_comp a C.differentiableAt hf.differentiableAt, C.fderiv]
    exact hC
  have hs : HasStrictFDerivAt g (ContinuousLinearEquiv.refl ℂ E).toContinuousLinearMap a :=
    hd ▸ hg.hasStrictFDerivAt
  let r := hs.localInverse g (ContinuousLinearEquiv.refl ℂ E) a ∘ C
  refine ⟨r, ?_, hs.localInverse_apply_image, hs.eventually_left_inverse⟩
  have hr := localInverse_analytic hg (ContinuousLinearEquiv.refl ℂ E) hd
  change AnalyticAt ℂ (hs.localInverse g (ContinuousLinearEquiv.refl ℂ E) a ∘ C) (f a)
  apply AnalyticAt.comp (f := C)
  · exact hr
  · exact C.analyticAt _

end AnalyticRetraction

namespace SplitTangent.HolomorphicJets
section
open DiagonalRationality Filter Topology
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem composeJet_analyticJet {G : ℂ → σ → ℂ} {H : (σ → ℂ) → τ → ℂ}
    (hG : AnalyticAt ℂ G 0) (hH : AnalyticAt ℂ H (G 0)) :
    composeJet H (analyticJet G) = analyticJet (H ∘ G) := by
  funext n i
  exact composeCoefficient_analyticJet hG (analyticAt_pi_iff.mp hH i) n

omit [Fintype σ] in
@[simp] theorem composeJet_id (f : ℕ → σ → ℂ) : composeJet id f = f := by
  funext n i
  simp only [composeJet,composeCoefficient,Function.id_def]
  simp_rw [← polynomialJet_eval]
  rw [taylorSeries_polynomial,Polynomial.coeff_coe,polynomialJet_coeff,ite_eq_left le_rfl]

omit [Fintype τ] in
theorem composeJet_germ {H K : (σ → ℂ) → τ → ℂ} (f : ℕ → σ → ℂ)
    (h : H =ᶠ[𝓝 (f 0)] K) : composeJet H f = composeJet K f := by
  funext n i
  simpa only [coeff_formalSubst,composeJet] using
    congrArg (PowerSeries.coeff n) (formalSubst_congr f (h.mono fun x hx => congrFun hx i))

theorem composeJet_assoc {υ : Type*} [Fintype υ]
    (H : (σ → ℂ) → τ → ℂ) (K : (τ → ℂ) → υ → ℂ) (f : ℕ → σ → ℂ)
    (hH : AnalyticAt ℂ H (f 0)) (hK : AnalyticAt ℂ K (H (f 0))) :
    composeJet K (composeJet H f) = composeJet (K ∘ H) f := by
  funext n i
  exact composeCoefficient_assoc H (fun y => K y i) f hH (analyticAt_pi_iff.mp hK i) n

theorem analyticJet_eq_germ {G K : ℂ → σ → ℂ}
    (hG : AnalyticAt ℂ G 0) (hK : AnalyticAt ℂ K 0)
    (h : analyticJet G = analyticJet K) : G =ᶠ[𝓝 0] K := by
  have hp := analyticJet_hasSeries hG
  rw [h] at hp
  filter_upwards [hp.eventually_hasSum_sub,(analyticJet_hasSeries hK).eventually_hasSum_sub]
    with z hz hk
  exact hz.unique hk

 

theorem lift_convergent {H : (σ → ℂ) → τ → ℂ} (f : ℕ → σ → ℂ)
    (hH : AnalyticAt ℂ H (f 0)) (hi : Function.Injective (fderiv ℂ H (f 0)))
    {Q : ℂ → τ → ℂ} (hQ : AnalyticAt ℂ Q 0)
    (hj : analyticJet Q = composeJet H f) :
    ∃ G : ℂ → σ → ℂ, AnalyticAt ℂ G 0 ∧ analyticJet G = f ∧
      (H ∘ G) =ᶠ[𝓝 0] Q := by
  obtain ⟨r,hr,hr0,hri⟩ := AnalyticRetraction.exists_left_inverse hH hi
  have h0 : Q 0 = H (f 0) := by
    simpa only [analyticJet_zero,composeJet_zero] using congrFun hj 0
  have hG : AnalyticAt ℂ (r ∘ Q) 0 := (h0 ▸ hr).comp hQ
  have hjet : analyticJet (r ∘ Q) = f := by
    rw [← composeJet_analyticJet hQ (h0 ▸ hr),hj,composeJet_assoc H r f hH hr]
    exact (composeJet_germ f (H := r ∘ H) (K := id) hri).trans (composeJet_id f)
  refine ⟨r ∘ Q,hG,hjet,?_⟩
  have hG0 : (r ∘ Q) 0 = f 0 := by simpa using congrFun hjet 0
  apply analyticJet_eq_germ (hG0 ▸ hH |>.comp hG) hQ
  rw [← composeJet_analyticJet hG (hG0 ▸ hH),hjet,hj]

end

open DiagonalRationality Filter Topology
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

 

theorem lift_convergent_family {H : (σ → ℂ) → τ → ℂ} (f : ℕ → ℂ → σ → ℂ) {z : ℂ}
    (hH : AnalyticAt ℂ H (f 0 z)) (hi : Function.Injective (fderiv ℂ H (f 0 z)))
    (hf0 : ContinuousAt (f 0) z) {Q : ℂ × ℂ → τ → ℂ}
    (hQ : AnalyticAt ℂ Q (z,0))
    (hj : ∀ᶠ u in 𝓝 z, analyticJet (fun v => Q (u,v)) = composeJet H (fun n => f n u)) :
    ∃ G : ℂ × ℂ → σ → ℂ, AnalyticAt ℂ G (z,0) ∧
      ∀ᶠ u in 𝓝 z, analyticJet (fun v => G (u,v)) = fun n => f n u := by
  obtain ⟨r,hr,_,hri⟩ := AnalyticRetraction.exists_left_inverse hH hi
  have hzero (u : ℂ) (hu : analyticJet (fun v => Q (u,v)) = composeJet H (fun n => f n u)) :
      Q (u,0) = H (f 0 u) := by
    simpa only [analyticJet_zero,composeJet_zero] using congrFun hu 0
  have hrQ : AnalyticAt ℂ r (Q (z,0)) := hzero z hj.self_of_nhds ▸ hr
  have hG : AnalyticAt ℂ (r ∘ Q) (z,0) := hrQ.comp hQ
  refine ⟨r ∘ Q,hG,?_⟩
  have hHnear := hf0 hH.eventually_analyticAt
  have hrnear := (hH.continuousAt.comp hf0) hr.eventually_analyticAt
  have hinear := hf0 (eventually_eventually_nhds.mpr hri)
  have hc : ContinuousAt (fun u : ℂ => (u,(0:ℂ))) z := continuousAt_id.prodMk continuousAt_const
  have hQnear := hc hQ.eventually_analyticAt
  filter_upwards [hj,hHnear,hrnear,hinear,hQnear] with u hju hHu hru hiu hQu
  change AnalyticAt ℂ H (f 0 u) at hHu
  change AnalyticAt ℂ r (H (f 0 u)) at hru
  change (∀ᶠ y in 𝓝 (f 0 u), r (H y) = y) at hiu
  change AnalyticAt ℂ Q (u,0) at hQu
  have hQu' : AnalyticAt ℂ (fun v => Q (u,v)) 0 :=
    hQu.comp (analyticAt_const.prod analyticAt_id)
  have hru' : AnalyticAt ℂ r (Q (u,0)) := hzero u hju ▸ hru
  change analyticJet (r ∘ (fun v => Q (u,v))) = fun n => f n u
  rw [← composeJet_analyticJet hQu' hru',hju,composeJet_assoc H r (fun n => f n u) hHu hru]
  exact (composeJet_germ (fun n => f n u) (H := r ∘ H) (K := id) hiu).trans (composeJet_id _)

end SplitTangent.HolomorphicJets

namespace SplitTangent.ProjectiveEmbedding
variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)

 
def withinChart (i : Fin (e.N+1)) (x : X.Carrier) : Model X → Fin (e.N+1) → ℂ :=
  (fun y => projectiveCoordinates i (e.map y)) ∘ (chartAt (Model X) x).symm

theorem withinChart_analytic (i : Fin (e.N+1)) (x : X.Carrier) {a : X.Carrier}
    (ha : a ∈ (chartAt (Model X) x).source) (hi : (e.map a).rep i ≠ 0) :
    AnalyticAt ℂ (e.withinChart i x) ((chartAt (Model X) x) a) := by
  apply analyticAt_pi_iff.mpr
  intro j
  exact TangentSplitting.scalarCoordinate_analytic ha
    (e.scalar_holomorphic i j |>.contMDiffAt (e.open_patch i |>.mem_nhds hi))

theorem withinChart_immersion (i : Fin (e.N+1)) (x : X.Carrier) {a : X.Carrier}
    (ha : a ∈ (chartAt (Model X) x).source) (hi : (e.map a).rep i ≠ 0) :
    Function.Injective (fderiv ℂ (e.withinChart i x) ((chartAt (Model X) x) a)) := by
  let c := chartAt (Model X) x
  let t := trivializationAt (Model X) (Tangent X) x
  have hc := (contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x)
      (c.map_source ha)).mdifferentiableAt (by simp)
  have he := (e.holomorphic i |>.contMDiffAt (e.open_patch i |>.mem_nhds hi)).mdifferentiableAt (by simp)
  have he' : MDifferentiableAt (ModelWithCorners X) 𝓘(ℂ,Fin (e.N+1) → ℂ)
      (fun y => projectiveCoordinates i (e.map y)) (c.symm (c a)) := by
    rw [c.left_inv ha]
    exact he
  have ht : t.symmL ℂ a = mfderiv 𝓘(ℂ,Model X) (ModelWithCorners X) c.symm (c a) := by
    simpa [t,c,extChartAt_coe_symm,extChartAt_coe,ModelWithCorners] using
      (TangentBundle.symmL_trivializationAt (I := ModelWithCorners X) ha)
  have hd : fderiv ℂ (e.withinChart i x) (c a) =
      (mfderiv (ModelWithCorners X) 𝓘(ℂ,Fin (e.N+1) → ℂ)
        (fun y => projectiveCoordinates i (e.map y)) a).comp (t.symmL ℂ a) := by
    rw [ht]
    change fderiv ℂ ((fun y => projectiveCoordinates i (e.map y)) ∘ c.symm) (c a) = _
    rw [← mfderiv_eq_fderiv,mfderiv_comp _ he' hc,c.left_inv ha]
    rfl
  rw [hd]
  have hti : Function.Injective (t.symmL ℂ a) := by
    intro v w hv
    have ht' : a ∈ t.baseSet := ha
    calc
      v = t.continuousLinearMapAt ℂ a (t.symmL ℂ a v) := (t.continuousLinearMapAt_symmL ht' v).symm
      _ = t.continuousLinearMapAt ℂ a (t.symmL ℂ a w) := congrArg _ hv
      _ = w := t.continuousLinearMapAt_symmL ht' w
  exact (e.immersion a i hi).comp hti

end SplitTangent.ProjectiveEmbedding

namespace SplitTangent.TangentSplitting
open HolomorphicJets DiagonalRationality PowerSeries
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

theorem exists_convergent_manifold_jet (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ (z : ℂ) (G : ℂ × ℂ → Model X), AnalyticAt ℂ G (z,0) ∧
      ∀ᶠ u in nhds z, analyticJet (fun v => G (u,v)) =
        fun n => S.localJet g.finite_holomorphic (g.finite z) n u := by
  obtain ⟨k,A,B,U,hU,hUn,hR⟩ := S.exists_convergent_projective_patch e g
  obtain ⟨z,hz⟩ := hUn
  let x := g.finite z
  let f := S.localJet g.finite_holomorphic x
  let H := e.withinChart k x
  let Q : ℂ × ℂ → Fin (e.N+1) → ℂ :=
    fun w j => -polynomialEvaluation (A j) w / polynomialEvaluation (B j) w
  have hsol := S.localJet_solution g.finite_holomorphic x
  have hx : z ∈ coordinateDomain g.finite x := mem_chart_source (Model X) x
  have hzero : f 0 z = (chartAt (Model X) x) x := hsol.2.1 z hx
  have hf0 : ContinuousAt (f 0) z :=
    (analyticAt_pi_iff.mpr (fun i => hsol.1 0 i z hx)).continuousAt
  have hH : AnalyticAt ℂ H (f 0 z) := by
    rw [hzero]
    exact e.withinChart_analytic k x hx (hR z hz).1
  have hi : Function.Injective (fderiv ℂ H (f 0 z)) := by
    rw [hzero]
    exact e.withinChart_immersion k x hx (hR z hz).1
  have hQ : AnalyticAt ℂ Q (z,0) := analyticAt_pi_iff.mpr (fun j => ((hR z hz).2 j).2.1)
  have hj : ∀ᶠ u in nhds z,
      analyticJet (fun v => Q (u,v)) = composeJet H (fun n => f n u) := by
    filter_upwards [hU.mem_nhds hz,(coordinateDomain_open g.finite_holomorphic x).mem_nhds hx]
      with u hu hux
    funext n j
    have hp := ((hR u hu).2 j).2.2
    have ht := hasFPowerSeries_taylorSeries hp.analyticAt
    have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n)
      (ht.eq_formalMultilinearSeries hp)
    simp only [FormalMultilinearSeries.coeff_ofScalars] at hc
    change coeff n (taylorSeries (fun v => Q (u,v) j)) = _
    rw [hc,S.scalarJet_eq_local g.finite_holomorphic _ x hux
      ((e.scalar_holomorphic k j).contMDiffAt ((e.open_patch k).mem_nhds (hR u hu).1)),
      coeff_formalSubst]
    rfl
  obtain ⟨G,hG,hjG⟩ := lift_convergent_family f hH hi hf0 hQ hj
  exact ⟨z,G,hG,hjG⟩

 

theorem exists_holomorphic_cauchy_germ (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ (z : ℂ) (F : ℂ × ℂ → X.Carrier) (G : ℂ × ℂ → Model X),
      ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F (z,0) ∧
      AnalyticAt ℂ G (z,0) ∧ F (z,0) = g.finite z ∧
      (∀ᶠ w in nhds (z,0), (chartAt (Model X) (g.finite z)) (F w) = G w) ∧
      ∀ᶠ u in nhds z, analyticJet (fun v => G (u,v)) =
        fun n => S.localJet g.finite_holomorphic (g.finite z) n u := by
  obtain ⟨z,G,hG,hj⟩ := S.exists_convergent_manifold_jet e g
  let c := chartAt (Model X) (g.finite z)
  have hc := mem_chart_source (Model X) (g.finite z)
  have hG0 : G (z,0) = c (g.finite z) := by
    have h := congrFun hj.self_of_nhds 0
    rw [analyticJet_zero] at h
    exact h.trans ((S.localJet_solution g.finite_holomorphic (g.finite z)).2.1 z hc)
  have ht : G (z,0) ∈ c.target := hG0 ▸ c.map_source hc
  have hci := contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) (g.finite z)) ht
  refine ⟨z,c.symm ∘ G,G,hci.comp _ hG.contDiffAt.contMDiffAt,hG,?_,?_,hj⟩
  · change c.symm (G (z,0)) = _
    rw [hG0,c.left_inv hc]
  · filter_upwards [hG.continuousAt (c.open_target.mem_nhds ht)] with w hw
    exact c.right_inv hw

end SplitTangent.TangentSplitting

namespace SplitTangent.HolomorphicJets
open DiagonalRationality Filter Topology PowerSeries
variable {σ : Type*} [Fintype σ]

theorem taylorSeries_eq_germ {h k : ℂ → ℂ} (hh : AnalyticAt ℂ h 0)
    (hk : AnalyticAt ℂ k 0) (he : taylorSeries h = taylorSeries k) : h =ᶠ[𝓝 0] k := by
  have hp := hasFPowerSeries_taylorSeries hh
  rw [he] at hp
  filter_upwards [hp.eventually_hasSum_sub,(hasFPowerSeries_taylorSeries hk).eventually_hasSum_sub]
    with z hz hk
  exact hz.unique hk

 

theorem joint_germ_of_slice_germs {H K : ℂ × ℂ → ℂ} {z : ℂ}
    (hH : AnalyticAt ℂ H (z,0)) (hK : AnalyticAt ℂ K (z,0))
    (h : ∀ᶠ u in 𝓝 z, (fun v => H (u,v)) =ᶠ[𝓝 0] (fun v => K (u,v))) :
    H =ᶠ[𝓝 (z,0)] K := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hH.eventually_analyticAt.and hK.eventually_analyticAt)
  have hf : ∀ᶠ w : ℂ × ℂ in 𝓝 (z,0),
      (fun v => H (w.1,v)) =ᶠ[𝓝 0] (fun v => K (w.1,v)) :=
    (show ContinuousAt (fun w : ℂ × ℂ => w.1) (z,0) from continuousAt_fst) h
  filter_upwards [Metric.ball_mem_nhds (z,0) hr,hf] with w hw hwg
  have hw' : w.1 ∈ Metric.ball z r ∧ w.2 ∈ Metric.ball 0 r := by
    simpa only [← ball_prod_same,Set.mem_prod] using hw
  have hHa : AnalyticOnNhd ℂ (fun v => H (w.1,v)) (Metric.ball 0 r) := by
    intro v hv
    have ha := (hball (show (w.1,v) ∈ Metric.ball (z,0) r by
      rw [← ball_prod_same]; exact ⟨hw'.1,hv⟩)).1
    exact ha.comp (analyticAt_const.prod analyticAt_id)
  have hKa : AnalyticOnNhd ℂ (fun v => K (w.1,v)) (Metric.ball 0 r) := by
    intro v hv
    have ha := (hball (show (w.1,v) ∈ Metric.ball (z,0) r by
      rw [← ball_prod_same]; exact ⟨hw'.1,hv⟩)).2
    exact ha.comp (analyticAt_const.prod analyticAt_id)
  exact hHa.eqOn_of_preconnected_of_eventuallyEq hKa (convex_ball (0:ℂ) r).isPreconnected
    (Metric.mem_ball_self hr) hwg hw'.2

theorem normalVector_analyticJet {G : ℂ × ℂ → σ → ℂ} {u : ℂ}
    (hG : AnalyticAt ℂ G (u,0)) (i : σ) :
    normalVector (analyticJet (fun v => G (u,v))) i =
      taylorSeries (fun v => normalDeriv (fun w => G w i) (u,v)) := by
  have he : deriv (fun v => G (u,v) i) =ᶠ[𝓝 0]
      (fun v => normalDeriv (fun w => G w i) (u,v)) := by
    have hc : ContinuousAt (fun v : ℂ => (u,v)) 0 := continuousAt_const.prodMk continuousAt_id
    filter_upwards [hc hG.eventually_analyticAt] with v hv
    exact normalDeriv_eq (analyticAt_pi_iff.mp hv i)
  have hm : (PowerSeries.mk fun n => coeff n (taylorSeries (fun v => G (u,v) i))) =
      taylorSeries (fun v => G (u,v) i) := by ext n; simp
  simpa only [normalVector,analyticJet,hm] using
    (taylorSeries_deriv (fun v => G (u,v) i)).symm.trans (taylorSeries_congr he)

theorem tangentVector_analyticJet {G : ℂ × ℂ → σ → ℂ} {f : ℕ → ℂ → σ → ℂ}
    {u : ℂ} (hG : AnalyticAt ℂ G (u,0))
    (hf : ∀ᶠ z in 𝓝 u, analyticJet (fun v => G (z,v)) = fun n => f n z) (i : σ) :
    tangentVector f u i = taylorSeries (fun v => tangentDeriv (fun w => G w i) (u,v)) := by
  ext n
  simp only [tangentVector,coeff_mk]
  rw [← deriv_normalCoefficient (analyticAt_pi_iff.mp hG i)]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hf] with z hz
  exact (congrFun (congrFun hz n) i).symm

theorem substitutedMatrix_analyticJet {G : ℂ × ℂ → σ → ℂ} {u : ℂ}
    (hG : AnalyticAt ℂ G (u,0)) (P : σ → σ → (σ → ℂ) → ℂ)
    (hP : ∀ i j, AnalyticAt ℂ (P i j) (G (u,0))) (i j : σ) :
    substitutedMatrix P (analyticJet (fun v => G (u,v))) i j =
      taylorSeries (fun v => P i j (G (u,v))) := by
  ext n
  simp only [substitutedMatrix,coeff_formalSubst]
  have ha : AnalyticAt ℂ (fun v => G (u,v)) 0 :=
    hG.comp (analyticAt_const.prod analyticAt_id)
  exact composeCoefficient_analyticJet (g := fun v => G (u,v)) ha (hP i j) n

 

theorem cauchy_analytic_fiber {U : Set ℂ} {g : ℂ → σ → ℂ}
    {P : σ → σ → (σ → ℂ) → ℂ} {f : ℕ → ℂ → σ → ℂ}
    (hf : CauchyOn U g P f) {u : ℂ} (hu : u ∈ U)
    {G : ℂ × ℂ → σ → ℂ} (hG : AnalyticAt ℂ G (u,0))
    (hP : ∀ i j, AnalyticAt ℂ (P i j) (G (u,0)))
    (hj : ∀ᶠ z in 𝓝 u, analyticJet (fun v => G (z,v)) = fun n => f n z) (i : σ) :
    (fun v => normalDeriv (fun w => G w i) (u,v)) =ᶠ[𝓝 0]
      (fun v => ∑ j, P i j (G (u,v)) * tangentDeriv (fun w => G w j) (u,v)) := by
  have ha : AnalyticAt ℂ (fun v => G (u,v)) 0 :=
    hG.comp (analyticAt_const.prod analyticAt_id)
  have htan (j : σ) : AnalyticAt ℂ (fun v => tangentDeriv (fun w => G w j) (u,v)) 0 :=
    (directionDeriv_analytic (analyticAt_pi_iff.mp hG j) (1,0)).comp
      (analyticAt_const.prod analyticAt_id)
  apply taylorSeries_eq_germ
    ((normalDeriv_analytic (analyticAt_pi_iff.mp hG i)).comp
      (analyticAt_const.prod analyticAt_id))
    (Finset.univ.analyticAt_fun_sum fun j _ => ((hP i j).comp (f := fun v => G (u,v)) ha).fun_mul (htan j))
  have he := congrFun (hf.2.2 u hu) i
  rw [← hj.self_of_nhds,normalVector_analyticJet hG] at he
  refine he.trans ?_
  simp only [Matrix.mulVec,dotProduct]
  rw [taylorSeries_sum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [substitutedMatrix_analyticJet hG P hP,
      tangentVector_analyticJet hG hj]
    exact (taylorSeries_mul (f := fun v => P i j (G (u,v)))
      (g := fun v => tangentDeriv (fun w => G w j) (u,v))
      ((hP i j).comp (f := fun v => G (u,v)) ha) (htan j)).symm
  · intro j _
    exact ((hP i j).comp (f := fun v => G (u,v)) ha).fun_mul (htan j)

 

theorem cauchy_analytic_joint {U : Set ℂ} (hU : IsOpen U) {g : ℂ → σ → ℂ}
    {P : σ → σ → (σ → ℂ) → ℂ} {f : ℕ → ℂ → σ → ℂ}
    (hf : CauchyOn U g P f) {z : ℂ} (hz : z ∈ U)
    {G : ℂ × ℂ → σ → ℂ} (hG : AnalyticAt ℂ G (z,0))
    (hP : ∀ i j, AnalyticAt ℂ (P i j) (G (z,0)))
    (hj : ∀ᶠ u in 𝓝 z, analyticJet (fun v => G (u,v)) = fun n => f n u) :
    ∀ᶠ w in 𝓝 (z,0), ∀ i,
      normalDeriv (fun w => G w i) w =
        ∑ j, P i j (G w) * tangentDeriv (fun w => G w j) w := by
  have hc : ContinuousAt (fun u : ℂ => (u,(0:ℂ))) z :=
    continuousAt_id.prodMk continuousAt_const
  have hGa : ∀ᶠ u in 𝓝 z, AnalyticAt ℂ G (u,0) := hc hG.eventually_analyticAt
  have hPa : ∀ᶠ u in 𝓝 z, ∀ i j, AnalyticAt ℂ (P i j) (G (u,0)) := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    exact (hG.continuousAt.comp (f := fun u : ℂ => (u,(0:ℂ))) hc) (hP i j).eventually_analyticAt
  apply Filter.eventually_all.mpr
  intro i
  apply joint_germ_of_slice_germs
    (normalDeriv_analytic (analyticAt_pi_iff.mp hG i))
    (Finset.univ.analyticAt_fun_sum fun j _ => ((hP i j).comp hG).fun_mul
      (directionDeriv_analytic (analyticAt_pi_iff.mp hG j) (1,0)))
  filter_upwards [hU.mem_nhds hz,hGa,hPa,eventually_eventually_nhds.mpr hj]
    with u hu hGu hPu hju
  exact cauchy_analytic_fiber hf hu hGu hPu hju i

end SplitTangent.HolomorphicJets

namespace SplitTangent.TangentSplitting
open HolomorphicJets DiagonalRationality Filter Topology
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

theorem exists_cauchy_coordinates (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ (z : ℂ) (G : ℂ × ℂ → Model X), AnalyticAt ℂ G (z,0) ∧
      (∀ᶠ u in 𝓝 z, G (u,0) = (chartAt (Model X) (g.finite z)) (g.finite u)) ∧
      ∀ᶠ w in 𝓝 (z,0), G w ∈ (chartAt (Model X) (g.finite z)).target ∧
        fderiv ℂ G w (0,1) = S.coordinateProjector (g.finite z) (G w) (fderiv ℂ G w (1,0)) := by
  obtain ⟨z,G,hG,hj⟩ := S.exists_convergent_manifold_jet e g
  let x := g.finite z
  let c := chartAt (Model X) x
  have hx : z ∈ coordinateDomain g.finite x := mem_chart_source (Model X) x
  have hU := coordinateDomain_open g.finite_holomorphic x
  have hf := S.localJet_solution g.finite_holomorphic x
  have h0 : ∀ᶠ u in 𝓝 z, G (u,0) = c (g.finite u) := by
    filter_upwards [hj,hU.mem_nhds hx] with u hju hu
    have he := congrFun hju 0
    rw [analyticJet_zero] at he
    exact he.trans (hf.2.1 u hu)
  have ht : G (z,0) ∈ c.target := h0.self_of_nhds ▸ c.map_source hx
  have hP : ∀ i j, AnalyticAt ℂ (S.coordinateMatrix x i j) (G (z,0)) :=
    fun i j => S.coordinateMatrix_analytic x i j _ ht
  have hde := cauchy_analytic_joint hU hf hx hG hP hj
  refine ⟨z,G,hG,h0,?_⟩
  filter_upwards [hde,hG.eventually_analyticAt,hG.continuousAt (c.open_target.mem_nhds ht)]
    with w hw hGw htw
  refine ⟨htw,?_⟩
  rw [← S.coordinateMatrix_mulVec]
  funext i
  simpa only [normalDeriv,tangentDeriv,directionDeriv,fderiv_apply hGw.differentiableAt,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,Matrix.mulVec,dotProduct]
    using hw i

 

theorem cauchy_chart_inverse {x : X.Carrier} {G : ℂ × ℂ → Model X} {w : ℂ × ℂ}
    (hG : AnalyticAt ℂ G w) (ht : G w ∈ (chartAt (Model X) x).target)
    (hde : fderiv ℂ G w (0,1) = S.coordinateProjector x (G w) (fderiv ℂ G w (1,0))) :
    let F := (chartAt (Model X) x).symm ∘ G
    mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (0,1) =
      S.projector (F w) (mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (1,0)) := by
  let c := chartAt (Model X) x
  let t := trivializationAt (Model X) (Tangent X) x
  have hb : c.symm (G w) ∈ t.baseSet := c.map_target ht
  have hci := contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) ht
  have hcD : mfderiv 𝓘(ℂ,Model X) (ModelWithCorners X) c.symm (G w) =
      t.symmL ℂ (c.symm (G w)) := by
    have he := TangentBundle.symmL_trivializationAt (I := ModelWithCorners X) hb
    have he' : t.symmL ℂ (c.symm (G w)) =
        mfderiv 𝓘(ℂ,Model X) (ModelWithCorners X) c.symm (c (c.symm (G w))) := by
      simpa [extChartAt_coe_symm,extChartAt_coe,ModelWithCorners,c,t] using he
    rw [c.right_inv ht] at he'
    exact he'.symm
  change mfderiv _ _ (c.symm ∘ G) w (0,1) =
    S.projector _ (mfderiv _ _ (c.symm ∘ G) w (1,0))
  have hmG : MDifferentiableAt 𝓘(ℂ,ℂ × ℂ) 𝓘(ℂ,Model X) G w :=
    (show ContMDiffAt 𝓘(ℂ,ℂ × ℂ) 𝓘(ℂ,Model X) ω G w from
      hG.contDiffAt.contMDiffAt).mdifferentiableAt (by simp)
  have hmci : MDifferentiableAt 𝓘(ℂ,Model X) (ModelWithCorners X) c.symm (G w) :=
    hci.mdifferentiableAt (by simp)
  have he (v : ℂ × ℂ) : mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) (c.symm ∘ G) w v =
      t.symmL ℂ (c.symm (G w)) (fderiv ℂ G w v) := by
    rw [mfderiv_comp w hmci hmG]
    change mfderiv 𝓘(ℂ,Model X) (ModelWithCorners X) c.symm (G w)
      (mfderiv 𝓘(ℂ,ℂ × ℂ) 𝓘(ℂ,Model X) G w v) = _
    rw [mfderiv_eq_fderiv]
    exact congrArg (fun L => L (fderiv ℂ G w v)) hcD
  rw [he,he]
  rw [hde]
  simp only [coordinateProjector,ContinuousLinearMap.comp_apply]
  rw [t.symmL_continuousLinearMapAt hb]
  rfl

 

theorem exists_actual_cauchy_germ (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ (z : ℂ) (F : ℂ × ℂ → X.Carrier),
      ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F (z,0) ∧
      (∀ᶠ u in 𝓝 z, F (u,0) = g.finite u) ∧
      ∀ᶠ w in 𝓝 (z,0),
        mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (0,1) =
          S.projector (F w) (mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (1,0)) := by
  obtain ⟨z,G,hG,h0,hde⟩ := S.exists_cauchy_coordinates e g
  let c := chartAt (Model X) (g.finite z)
  let F := c.symm ∘ G
  have ht : G (z,0) ∈ c.target := hde.self_of_nhds.1
  have hci := contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) (g.finite z)) ht
  refine ⟨z,F,hci.comp _ hG.contDiffAt.contMDiffAt,?_,?_⟩
  · filter_upwards [h0,(coordinateDomain_open g.finite_holomorphic (g.finite z)).mem_nhds
      (mem_chart_source (Model X) (g.finite z))] with u hu hux
    change c.symm (G (u,0)) = _
    rw [hu,c.left_inv hux]
  · filter_upwards [hde,hG.eventually_analyticAt] with w hw hGw
    exact S.cauchy_chart_inverse hGw hw.1 hw.2

end SplitTangent.TangentSplitting

namespace SplitTangent.HolomorphicJets
open DiagonalRationality Filter Topology
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

 

theorem image_eq_of_jets {H : (σ → ℂ) → τ → ℂ} (f : ℕ → ℂ → σ → ℂ) {z : ℂ}
    (hH : AnalyticAt ℂ H (f 0 z)) (hf0 : ContinuousAt (f 0) z)
    {G : ℂ × ℂ → σ → ℂ} {Q : ℂ × ℂ → τ → ℂ}
    (hG : AnalyticAt ℂ G (z,0)) (hQ : AnalyticAt ℂ Q (z,0))
    (hjG : ∀ᶠ u in 𝓝 z, analyticJet (fun v => G (u,v)) = fun n => f n u)
    (hjQ : ∀ᶠ u in 𝓝 z, analyticJet (fun v => Q (u,v)) = composeJet H (fun n => f n u)) :
    (H ∘ G) =ᶠ[𝓝 (z,0)] Q := by
  have h0 (u : ℂ) (hu : analyticJet (fun v => G (u,v)) = fun n => f n u) :
      G (u,0) = f 0 u := by simpa only [analyticJet_zero] using congrFun hu 0
  have hHG : AnalyticAt ℂ (H ∘ G) (z,0) := (h0 z hjG.self_of_nhds ▸ hH).comp hG
  have hc : ContinuousAt (fun u : ℂ => (u,(0:ℂ))) z := continuousAt_id.prodMk continuousAt_const
  have hs : ∀ᶠ u in 𝓝 z, (fun v => H (G (u,v))) =ᶠ[𝓝 0] (fun v => Q (u,v)) := by
    filter_upwards [hjG,hjQ,hf0 hH.eventually_analyticAt,hc hG.eventually_analyticAt,
      hc hQ.eventually_analyticAt] with u hgu hqu hHu hGu hQu
    have hGu' : AnalyticAt ℂ (fun v => G (u,v)) 0 :=
      hGu.comp (analyticAt_const.prod analyticAt_id)
    have hQu' : AnalyticAt ℂ (fun v => Q (u,v)) 0 :=
      hQu.comp (analyticAt_const.prod analyticAt_id)
    have hHu' : AnalyticAt ℂ H (G (u,0)) := h0 u hgu ▸ hHu
    apply analyticJet_eq_germ (hHu'.comp (f := fun v => G (u,v)) hGu') hQu'
    rw [← composeJet_analyticJet hGu' hHu',hgu,hqu]
  suffices h : ∀ᶠ w in 𝓝 (z,0), ∀ j, H (G w) j = Q w j by
    exact h.mono fun w hw => funext hw
  apply Filter.eventually_all.mpr
  intro j
  have he := joint_germ_of_slice_germs (analyticAt_pi_iff.mp hHG j)
    (analyticAt_pi_iff.mp hQ j) (hs.mono fun u hu => hu.mono fun v hv => congrFun hv j)
  exact he

end SplitTangent.HolomorphicJets

namespace SplitTangent.DiagonalRationality
open Polynomial

 

def normalBiPolynomial (m : ℕ) (a : BiCoefficients m) : Polynomial (Polynomial ℂ) :=
  (biPolynomial m a).comp (Polynomial.X + Polynomial.C Polynomial.X)

@[simp] theorem polynomialFunction_X : polynomialFunction (Polynomial.X : Polynomial ℂ) = id := by
  ext z
  simp

theorem normalBiPolynomial_map (m : ℕ) (a : BiCoefficients m) :
    (normalBiPolynomial m a).map polynomialFunction.toRingHom = normalPolynomial m a := by
  apply Polynomial.coe_injective (ℂ → ℂ)
  rw [normalPolynomial_coe,normalPolynomialSection_eq_expand]
  simp only [normalBiPolynomial,Polynomial.map_comp,Polynomial.map_add,Polynomial.map_X,
    Polynomial.map_C,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,polynomialFunction_X,expandPolynomial]

 

theorem exists_bivariate_of_coefficients (A : Polynomial (ℂ → ℂ))
    (hA : ∀ n, ∃ p : Polynomial ℂ, polynomialFunction p = A.coeff n) :
    ∃ P : Polynomial (Polynomial ℂ), P.map polynomialFunction.toRingHom = A := by
  classical
  choose p hp using hA
  refine ⟨∑ n ∈ A.support, Polynomial.monomial n (p n),?_⟩
  simp only [Polynomial.map_sum,Polynomial.map_monomial]
  change ∑ n ∈ A.support, Polynomial.monomial n (polynomialFunction (p n)) = A
  simpa only [hp,Polynomial.sum] using Polynomial.sum_monomial_eq A

 

theorem bivariate_of_normal_division (m : ℕ) (a : BiCoefficients m)
    {r : ℕ} {A : Polynomial (ℂ → ℂ)}
    (hA : normalPolynomial m a = Polynomial.X ^ r * A) :
    ∃ P : Polynomial (Polynomial ℂ), P.map polynomialFunction.toRingHom = A := by
  apply exists_bivariate_of_coefficients
  intro n
  refine ⟨(normalBiPolynomial m a).coeff (n+r),?_⟩
  have he := congrArg (fun p : Polynomial (ℂ → ℂ) => p.coeff (n+r))
    ((normalBiPolynomial_map m a).trans hA)
  simpa only [Polynomial.coeff_map,Polynomial.coeff_X_pow_mul,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using he

 
def bivariateEvaluation (P : Polynomial (Polynomial ℂ)) (w : ℂ × ℂ) : ℂ :=
  P.eval₂ (Polynomial.evalRingHom w.1) w.2

@[simp] theorem evaluate_polynomial_map (P : Polynomial (Polynomial ℂ)) (w : ℂ × ℂ) :
    polynomialEvaluation (P.map polynomialFunction.toRingHom) w = bivariateEvaluation P w := by
  simp only [polynomialEvaluation,bivariateEvaluation]
  rw [Polynomial.eval₂_map]
  rfl

end SplitTangent.DiagonalRationality

namespace SplitTangent.FormalProjective
open SplitTangent.DiagonalRationality

 

theorem reconstruct_projective_bivariate {ι : Type*} [Fintype ι] {d : ℕ}
    {p q : ι → Polynomial ℂ} (F : TwoChartData d p q)
    (a b : ι → Polynomial ℂ) (ha : ∑ i, a i * p i = 1) (hb : ∑ i, b i * q i = 1) :
    ∃ (k : ι) (A B : ι → Polynomial (Polynomial ℂ)) (U : Set ℂ),
      IsOpen U ∧ U.Nonempty ∧ ∀ z ∈ U, (p k).eval z ≠ 0 ∧ ∀ j,
        ((B j).coeff 0).eval z ≠ 0 ∧
        AnalyticAt ℂ (fun w => -bivariateEvaluation (A j) w / bivariateEvaluation (B j) w) (z,0) ∧
        HasFPowerSeriesAt
          (fun v => -bivariateEvaluation (A j) (z,v) / bivariateEvaluation (B j) (z,v))
          (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n
            (F.finite.ratio k j z))) 0 := by
  obtain ⟨k,hk⟩ := F.finite.basepoint_free 0
  let s := F.normalizedSection a b ha hb k
  let t := F.normalizedSection a b ha hb
  have hs : ∃ z : ℂ, PowerSeries.constantCoeff s.val.1 z ≠ 0 := by
    exact ⟨0, by simpa only [s,F.normalizedSection_constant a b ha hb k 0] using hk⟩
  obtain ⟨A',B',r,A,B,U,hU,hUn,hpoly,h⟩ := simultaneous_reconstruction_on_diagonal_patch d
    (F.normalizedTransition_constant a b ha hb) s t hs
  choose AA hAA using fun j => bivariate_of_normal_division _ (A' j) (hpoly j).2.1
  choose BB hBB using fun j => bivariate_of_normal_division _ (B' j) (hpoly j).2.2
  refine ⟨k,AA,BB,U,hU,hUn,?_⟩
  intro z hz
  obtain ⟨hsk,hr⟩ := h z hz
  have hp : (p k).eval z ≠ 0 := by
    simpa only [s,F.normalizedSection_constant a b ha hb k z] using hsk
  refine ⟨hp,fun j => ⟨?_,?_,?_⟩⟩
  · simpa only [← hBB j,Polynomial.coeff_map,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
      polynomialFunction_apply] using (hr j).1
  · simpa only [← hAA j,← hBB j,evaluate_polynomial_map] using (hr j).2.1
  · have hq : evaluateCoefficients z (t j).val.1 * (evaluateCoefficients z s.val.1)⁻¹ =
        F.finite.ratio k j z := by
      change evaluateCoefficients z (F.finite.sectionSeries a j) *
        (evaluateCoefficients z (F.finite.sectionSeries a k))⁻¹ = _
      rw [TwoChartData.sectionSeries_evaluate,TwoChartData.sectionSeries_evaluate,
        F.finite.sectionValue_ratio a ha k j z hp]
    simpa only [← hAA j,← hBB j,evaluate_polynomial_map,hq] using (hr j).2.2

end SplitTangent.FormalProjective

namespace SplitTangent.TangentSplitting
section
open HolomorphicJets DiagonalRationality PowerSeries
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

theorem exists_bivariate_cauchy_patch (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ (k : Fin (e.N+1)) (A B : Fin (e.N+1) → Polynomial (Polynomial ℂ)) (U : Set ℂ),
      IsOpen U ∧ U.Nonempty ∧ ∀ z ∈ U, (e.map (g.finite z)).rep k ≠ 0 ∧ ∀ j,
        ((B j).coeff 0).eval z ≠ 0 ∧
        AnalyticAt ℂ (fun w => -bivariateEvaluation (A j) w / bivariateEvaluation (B j) w) (z,0) ∧
        HasFPowerSeriesAt
          (fun v => -bivariateEvaluation (A j) (z,v) / bivariateEvaluation (B j) (z,v))
          (FormalMultilinearSeries.ofScalars ℂ (fun n => coeff n
            (S.scalarJet g.finite_holomorphic (fun x => projectiveCoordinates k (e.map x) j) z))) 0 := by
  obtain ⟨d,p,q,a,b,F,ha,hb,hfinite,_,hpatch⟩ := S.exists_projective_formal_data e g
  obtain ⟨k,A,B,U,hU,hUn,hR⟩ := FormalProjective.reconstruct_projective_bivariate F a b ha hb
  refine ⟨k,A,B,U,hU,hUn,?_⟩
  intro z hz
  obtain ⟨hk,hj⟩ := hR z hz
  refine ⟨(hpatch k z).mp hk,fun j => ⟨(hj j).1,(hj j).2.1,?_⟩⟩
  simpa only [hfinite] using (hj j).2.2

end

open HolomorphicJets DiagonalRationality PowerSeries Filter Topology
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

theorem exists_rational_cauchy_coordinates (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ (z : ℂ) (k : Fin (e.N+1)) (A B : Fin (e.N+1) → Polynomial (Polynomial ℂ))
      (G : ℂ × ℂ → Model X), AnalyticAt ℂ G (z,0) ∧
      (∀ j, ((B j).coeff 0).eval z ≠ 0) ∧
      (e.map (g.finite z)).rep k ≠ 0 ∧
      (∀ᶠ w in nhds (z,0), e.withinChart k (g.finite z) (G w) =
        fun j => -bivariateEvaluation (A j) w / bivariateEvaluation (B j) w) ∧
      ∀ᶠ u in nhds z, analyticJet (fun v => G (u,v)) =
        fun n => S.localJet g.finite_holomorphic (g.finite z) n u := by
  obtain ⟨k,A,B,U,hU,hUn,hR⟩ := S.exists_bivariate_cauchy_patch e g
  obtain ⟨z,hz⟩ := hUn
  let x := g.finite z
  let f := S.localJet g.finite_holomorphic x
  let H := e.withinChart k x
  let Q : ℂ × ℂ → Fin (e.N+1) → ℂ :=
    fun w j => -bivariateEvaluation (A j) w / bivariateEvaluation (B j) w
  have hsol := S.localJet_solution g.finite_holomorphic x
  have hx : z ∈ coordinateDomain g.finite x := mem_chart_source (Model X) x
  have hzero : f 0 z = (chartAt (Model X) x) x := hsol.2.1 z hx
  have hf0 : ContinuousAt (f 0) z :=
    (analyticAt_pi_iff.mpr (fun i => hsol.1 0 i z hx)).continuousAt
  have hH : AnalyticAt ℂ H (f 0 z) := by
    rw [hzero]
    exact e.withinChart_analytic k x hx (hR z hz).1
  have hi : Function.Injective (fderiv ℂ H (f 0 z)) := by
    rw [hzero]
    exact e.withinChart_immersion k x hx (hR z hz).1
  have hQ : AnalyticAt ℂ Q (z,0) := analyticAt_pi_iff.mpr (fun j => ((hR z hz).2 j).2.1)
  have hj : ∀ᶠ u in nhds z,
      analyticJet (fun v => Q (u,v)) = composeJet H (fun n => f n u) := by
    filter_upwards [hU.mem_nhds hz,(coordinateDomain_open g.finite_holomorphic x).mem_nhds hx]
      with u hu hux
    funext n j
    have hp := ((hR u hu).2 j).2.2
    have ht := hasFPowerSeries_taylorSeries hp.analyticAt
    have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n)
      (ht.eq_formalMultilinearSeries hp)
    simp only [FormalMultilinearSeries.coeff_ofScalars] at hc
    change coeff n (taylorSeries (fun v => Q (u,v) j)) = _
    rw [hc,S.scalarJet_eq_local g.finite_holomorphic _ x hux
      ((e.scalar_holomorphic k j).contMDiffAt ((e.open_patch k).mem_nhds (hR u hu).1)),
      coeff_formalSubst]
    rfl
  obtain ⟨G,hG,hjG⟩ := lift_convergent_family f hH hi hf0 hQ hj
  refine ⟨z,k,A,B,G,hG,fun j => ((hR z hz).2 j).1,(hR z hz).1,?_,hjG⟩
  exact image_eq_of_jets f hH hf0 hG hQ hjG hj

end SplitTangent.TangentSplitting

section FiniteBaseImport
open Polynomial
namespace SplitTangent.RationalSurface

abbrev K := RatFunc ℂ
local instance formalBoxesDecidableEqRatFunc : DecidableEq K := Classical.decEq K

abbrev R := Polynomial ℂ
abbrev B := Polynomial R

def eval (p : B) (w : ℂ × ℂ) : ℂ := p.eval₂ (Polynomial.evalRingHom w.1) w.2

variable {ι : Type*} [Fintype ι]

 

theorem finite_common_zeros (p : ι → B) {q : R} (hq : q ≠ 0)
    (a : ι → B) (hbez : ∑ i, a i * p i = C q)
    (hvertical : ∀ s : ℂ, ∃ i, (p i).map (Polynomial.evalRingHom s) ≠ 0) :
    Set.Finite {w : ℂ × ℂ | ∀ i, eval (p i) w = 0} := by
  let Z : Set (ℂ × ℂ) := {w | ∀ i, eval (p i) w = 0}
  apply Set.Finite.of_finite_fibers Prod.fst
  · apply (Polynomial.finite_setOfPred_isRoot hq).subset
    rintro s ⟨w,hw,rfl⟩
    have he := congrArg (fun p : B => eval p w) hbez
    simpa only [eval,Polynomial.eval₂_finsetSum,Polynomial.eval₂_mul,
      show ∀ i, (p i).eval₂ (Polynomial.evalRingHom w.1) w.2 = 0 from hw,
      mul_zero,Finset.sum_const_zero,Polynomial.eval₂_C,Polynomial.IsRoot,Polynomial.coe_evalRingHom,Set.mem_ofPred_eq] using he.symm
  · intro s hs
    obtain ⟨i,hi⟩ := hvertical s
    apply ((Set.finite_singleton s).prod (Polynomial.finite_setOfPred_isRoot hi)).subset
    rintro w ⟨hw,hws⟩
    have he : w.1 = s := hws
    refine ⟨he,?_⟩
    change ((p i).map (Polynomial.evalRingHom s)).eval w.2 = 0
    rw [Polynomial.eval_map,← he]
    exact hw i

 
theorem common_denominator (p : ι → Polynomial K) :
    ∃ (q : R) (P : ι → B), q ≠ 0 ∧
      ∀ i, (P i).map (algebraMap R K) = C (algebraMap R K q) * p i := by
  let := Polynomial.algebra (R := R) (A := K)
  let := Polynomial.isLocalization (nonZeroDivisors R) K
  obtain ⟨q,hq⟩ := IsLocalization.exist_integer_multiples_of_finite
    ((nonZeroDivisors R).map (Polynomial.C : R →+* B)) p
  obtain ⟨r,hr,he⟩ := q.property
  have hqr : (q : B) = C r := he.symm
  choose P hP using hq
  refine ⟨r,P,nonZeroDivisors.ne_zero hr,?_⟩
  intro i
  have hh := hP i
  change (P i).map (algebraMap R K) = _ at hh
  rw [hqr] at hh
  rw [Algebra.smul_def] at hh
  change (P i).map (algebraMap R K) = (C r).map (algebraMap R K) * p i at hh
  simpa only [Polynomial.map_C] using hh

 
theorem no_vertical_component (p : ι → B) (hp : Finset.univ.gcd p = 1) (s : ℂ) :
    ∃ i, (p i).map (Polynomial.evalRingHom s) ≠ 0 := by
  by_contra! h
  have hd : C (X - C s : R) ∣ Finset.univ.gcd p := by
    apply Finset.dvd_gcd
    intro i hi
    rw [C_dvd_iff_dvd_coeff]
    intro n
    rw [Polynomial.dvd_iff_isRoot]
    have he := congrArg (fun q : Polynomial ℂ => q.coeff n) (h i)
    simpa [Polynomial.coeff_map,Polynomial.IsRoot] using he
  rw [hp] at hd
  have hu := Polynomial.isUnit_C.mp (isUnit_of_dvd_one hd)
  have hz := hu.map (Polynomial.evalRingHom s)
  simp at hz

 
theorem generic_gcd_eq_one (p : ι → B) (hp : Finset.univ.gcd p = 1) :
    Finset.univ.gcd (fun i => (p i).map (algebraMap R K)) = 1 := by
  classical
  let d := Finset.univ.gcd (fun i => (p i).map (algebraMap R K))
  have hd : d ≠ 0 := by
    intro he
    have hall := Finset.gcd_eq_zero_iff.mp he
    have hz : Finset.univ.gcd p = 0 := Finset.gcd_eq_zero_iff.mpr (by
      intro i hi
      exact (Polynomial.map_eq_zero_iff (IsFractionRing.injective R K)).mp (hall i hi))
    exact one_ne_zero (hp.symm.trans hz)
  let q := IsLocalization.integerNormalization (nonZeroDivisors R) d
  obtain ⟨b,hb,hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) d
  have hbunit : IsUnit (C (algebraMap R K b)) := Polynomial.isUnit_C.mpr
    (isUnit_iff_ne_zero.mpr (fun he => nonZeroDivisors.ne_zero hb ((IsFractionRing.injective R K) (he.trans (map_zero _).symm))))
  have hpd : q.primPart.map (algebraMap R K) ∣ d := by
    have hh := Polynomial.map_dvd (algebraMap R K) q.primPart_dvd
    change _ ∣ q.map (algebraMap R K) at hh
    rw [hq,Algebra.smul_def,Polynomial.algebraMap_apply] at hh
    exact hbunit.dvd_mul_left.mp hh
  have hqall : q.primPart ∣ Finset.univ.gcd p := by
    apply Finset.dvd_gcd
    intro i hi
    apply q.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (K := K)
    exact hpd.trans (Finset.gcd_dvd hi)
  rw [hp] at hqall
  have hdu : IsUnit d := Polynomial.isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart
    hd (isUnit_of_dvd_one hqall)
  simpa only [d,Finset.normalize_gcd] using normalize_eq_one.mpr hdu

 

omit [Fintype ι] in
theorem generic_gcd_mem_span (p : ι → Polynomial K) (s : Finset ι) :
    s.gcd p ∈ Ideal.span (Set.range p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.gcd_insert]
    obtain ⟨a,b,h⟩ := exists_gcd_eq_mul_add_mul (p i) (s.gcd p)
    rw [h]
    exact (Ideal.span (Set.range p)).add_mem
      ((Ideal.span (Set.range p)).mul_mem_right a (Ideal.subset_span ⟨i,rfl⟩))
      ((Ideal.span (Set.range p)).mul_mem_right b ih)

 

theorem vertical_bezout (p : ι → B) (hp : Finset.univ.gcd p = 1) :
    ∃ (q : R) (a : ι → B), q ≠ 0 ∧ ∑ i, a i * p i = C q := by
  have hg := generic_gcd_eq_one p hp
  have hm := generic_gcd_mem_span (fun i => (p i).map (algebraMap R K)) Finset.univ
  rw [hg] at hm
  obtain ⟨b,hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp hm
  obtain ⟨q,a,hq,ha⟩ := common_denominator b
  refine ⟨q,a,hq,?_⟩
  apply Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
  simp only [Polynomial.map_sum,Polynomial.map_mul,ha,Polynomial.map_C]
  simp only [mul_assoc,← Finset.mul_sum,hb,mul_one]

 

theorem finite_zero_set (p : ι → B) (hp : Finset.univ.gcd p = 1) :
    Set.Finite {w : ℂ × ℂ | ∀ i, eval (p i) w = 0} := by
  obtain ⟨q,a,hq,ha⟩ := vertical_bezout p hp
  exact finite_common_zeros p hq a ha (no_vertical_component p hp)

 
theorem eval_analytic (p : B) (w : ℂ × ℂ) : AnalyticAt ℂ (eval p) w := by
  have ht (n : ℕ) : AnalyticAt ℂ (fun u : ℂ × ℂ => (p.coeff n).eval u.1 * u.2 ^ n) w :=
    (((p.coeff n).differentiable.analyticAt w.1).comp
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt w)).mul
        (((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt w).pow n)
  have he : eval p = ∑ n ∈ p.support, (fun u : ℂ × ℂ => (p.coeff n).eval u.1 * u.2 ^ n) := by
    funext u
    simp [eval,Polynomial.eval₂_eq_sum,Polynomial.sum_def]
  rw [he]
  exact Finset.analyticAt_sum p.support (fun n _ => ht n)

 
theorem polynomial_ratio_tuple (A D : ι → B) :
    ∃ p : ι → B, ∀ (w : ℂ × ℂ), (∀ i, eval (D i) w ≠ 0) →
      ∀ j, eval (p j) w = (∏ i, eval (D i) w) * (-eval (A j) w / eval (D j) w) := by
  classical
  refine ⟨fun j => - A j * ∏ i ∈ Finset.univ.erase j, D i,?_⟩
  intro w hw j
  have hp : eval (D j) w * ∏ i ∈ Finset.univ.erase j, eval (D i) w =
      ∏ i, eval (D i) w := Finset.mul_prod_erase Finset.univ (fun i => eval (D i) w) (Finset.mem_univ j)
  simp only [eval,Polynomial.eval₂_mul,Polynomial.eval₂_neg,Polynomial.eval₂_finsetProd]
  change -eval (A j) w * (∏ i ∈ Finset.univ.erase j, eval (D i) w) =
    (∏ i, eval (D i) w) * (-eval (A j) w / eval (D j) w)
  rw [← hp]
  field_simp [hw j]

 

theorem primitive_ratio_tuple [Nonempty ι] (A D : ι → B) (k : ι) :
    ∃ (P : ι → B), Finset.univ.gcd P = 1 ∧
      Set.Finite {w : ℂ × ℂ | ∀ j, eval (P j) w = 0} ∧
      ∀ w, (∀ i, eval (D i) w ≠ 0) → -eval (A k) w / eval (D k) w = 1 →
        eval (P k) w ≠ 0 ∧ ∀ j, eval (P j) w / eval (P k) w =
          -eval (A j) w / eval (D j) w := by
  classical
  obtain ⟨p,hp⟩ := polynomial_ratio_tuple A D
  obtain ⟨P,hP,hg⟩ := Finset.extract_gcd p Finset.univ_nonempty
  let q := Finset.univ.gcd p
  have he (j : ι) (w : ℂ × ℂ) : eval (p j) w = eval q w * eval (P j) w := by
    rw [hP j (Finset.mem_univ j)]
    exact Polynomial.eval₂_mul _ _
  refine ⟨P,hg,finite_zero_set P hg,?_⟩
  intro w hw hk
  have hpk : eval (p k) w ≠ 0 := by
    rw [hp w hw k,hk,mul_one]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hw i)
  have hq : eval q w ≠ 0 := by
    intro hz
    exact hpk (by rw [he k w,hz,zero_mul])
  have hPk : eval (P k) w ≠ 0 := by
    intro hz
    exact hpk (by rw [he k w,hz,mul_zero])
  refine ⟨hPk,fun j => ?_⟩
  apply (div_eq_iff hPk).mpr
  apply mul_left_cancel₀ hq
  rw [← he j w,hp w hw j]
  have hh := he k w
  rw [hp w hw k,hk,mul_one] at hh
  rw [hh]
  ring

end SplitTangent.RationalSurface

end FiniteBaseImport
namespace SplitTangent.TangentSplitting
open HolomorphicJets DiagonalRationality Filter Topology
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

theorem exists_rational_tangent_germ (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ (z : ℂ) (k : Fin (e.N+1)) (P : Fin (e.N+1) → Polynomial (Polynomial ℂ))
      (F : ℂ × ℂ → X.Carrier),
      Finset.univ.gcd P = 1 ∧
      Set.Finite {w : ℂ × ℂ | ∀ j, RationalSurface.eval (P j) w = 0} ∧
      ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F (z,0) ∧
      (∀ᶠ u in 𝓝 z, F (u,0) = g.finite u) ∧
      (∀ᶠ w in 𝓝 (z,0), RationalSurface.eval (P k) w ≠ 0 ∧
        (e.map (F w)).rep k ≠ 0 ∧ ∀ j,
          RationalSurface.eval (P j) w / RationalSurface.eval (P k) w =
            projectiveCoordinates k (e.map (F w)) j) ∧
      ∀ᶠ w in 𝓝 (z,0),
        mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (0,1) =
          S.projector (F w) (mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (1,0)) := by
  obtain ⟨z,k,A,B,G,hG,hB,hk,hQ,hj⟩ := S.exists_rational_cauchy_coordinates e g
  let x := g.finite z
  let c := chartAt (Model X) x
  have hx : z ∈ coordinateDomain g.finite x := mem_chart_source (Model X) x
  have hU := coordinateDomain_open g.finite_holomorphic x
  have hf := S.localJet_solution g.finite_holomorphic x
  have h0 : ∀ᶠ u in 𝓝 z, G (u,0) = c (g.finite u) := by
    filter_upwards [hj,hU.mem_nhds hx] with u hju hu
    have he := congrFun hju 0
    rw [analyticJet_zero] at he
    exact he.trans (hf.2.1 u hu)
  have ht : G (z,0) ∈ c.target := h0.self_of_nhds ▸ c.map_source hx
  have hM : ∀ i j, AnalyticAt ℂ (S.coordinateMatrix x i j) (G (z,0)) :=
    fun i j => S.coordinateMatrix_analytic x i j _ ht
  have hde := cauchy_analytic_joint hU hf hx hG hM hj
  have hde' : ∀ᶠ w in 𝓝 (z,0), G w ∈ c.target ∧
      fderiv ℂ G w (0,1) = S.coordinateProjector x (G w) (fderiv ℂ G w (1,0)) := by
    filter_upwards [hde,hG.eventually_analyticAt,hG.continuousAt (c.open_target.mem_nhds ht)]
      with w hw hGw htw
    refine ⟨htw,?_⟩
    rw [← S.coordinateMatrix_mulVec]
    funext i
    simpa only [normalDeriv,tangentDeriv,directionDeriv,fderiv_apply hGw.differentiableAt,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,Matrix.mulVec,dotProduct]
      using hw i
  let F := c.symm ∘ G
  have hF : ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F (z,0) :=
    (contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) ht).comp _
        hG.contDiffAt.contMDiffAt
  have hFg : ∀ᶠ u in 𝓝 z, F (u,0) = g.finite u := by
    filter_upwards [h0,hU.mem_nhds hx] with u hu hux
    change c.symm (G (u,0)) = _
    rw [hu,c.left_inv hux]
  have hFk : ∀ᶠ w in 𝓝 (z,0), (e.map (F w)).rep k ≠ 0 := by
    have hk' : (e.map (F (z,0))).rep k ≠ 0 := by rw [hFg.self_of_nhds]; exact hk
    exact hF.continuousAt ((e.open_patch k).mem_nhds hk')
  have hBn : ∀ᶠ w in 𝓝 (z,0), ∀ j, RationalSurface.eval (B j) w ≠ 0 := by
    rw [Filter.eventually_all]
    intro j
    apply (RationalSurface.eval_analytic (B j) (z,0)).continuousAt.eventually_ne
    simpa only [RationalSurface.eval,Polynomial.eval₂_at_zero,Polynomial.coe_evalRingHom] using hB j
  obtain ⟨P,hP,hfinite,hPr⟩ := RationalSurface.primitive_ratio_tuple A B k
  refine ⟨z,k,P,F,hP,hfinite,hF,hFg,?_,?_⟩
  · filter_upwards [hQ,hFk,hBn] with w hw hkw hBw
    have he (j) : projectiveCoordinates k (e.map (F w)) j =
        -RationalSurface.eval (A j) w / RationalSurface.eval (B j) w := congrFun hw j
    have he1 : -RationalSurface.eval (A k) w / RationalSurface.eval (B k) w = 1 := by
      rw [← he k]
      exact inv_mul_cancel₀ hkw
    obtain ⟨hPk,hPj⟩ := hPr w hBw he1
    exact ⟨hPk,hkw,fun j => (hPj j).trans (he j).symm⟩
  · filter_upwards [hde',hG.eventually_analyticAt] with w hw hGw
    exact S.cauchy_chart_inverse hGw hw.1 hw.2

end SplitTangent.TangentSplitting

open Filter Topology

namespace SplitTangent.ProjectiveEmbedding
section
variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)

 
def Incidence (x : X.Carrier) (v : Fin (e.N+1) → ℂ) : Prop :=
  ∀ i j, (e.map x).rep i * v j = (e.map x).rep j * v i

 

theorem incidence_iff_coordinates {x : X.Carrier} {v : Fin (e.N+1) → ℂ}
    {i : Fin (e.N+1)} (hi : (e.map x).rep i ≠ 0) :
    e.Incidence x v ↔ ∀ j, v j = v i * projectiveCoordinates i (e.map x) j := by
  constructor
  · intro h j
    have hj := h i j
    dsimp [projectiveCoordinates]
    field_simp
    linear_combination hj
  · intro h j k
    rw [h j,h k]
    dsimp [projectiveCoordinates]
    ring

theorem incidence_iff_projective {x : X.Carrier} {v : Fin (e.N+1) → ℂ}
    (hv : v ≠ 0) : e.Incidence x v ↔ e.map x = Projectivization.mk ℂ v hv := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp (e.map x).rep_nonzero
  change (e.map x).rep i ≠ 0 at hi
  rw [e.incidence_iff_coordinates hi]
  constructor
  · intro h
    have hvi : v i ≠ 0 := by
      intro hz
      apply hv
      ext j
      rw [h j,hz,zero_mul]
      rfl
    rw [← Projectivization.mk_rep (e.map x),Projectivization.mk_eq_mk_iff']
    refine ⟨(e.map x).rep i / v i,?_⟩
    ext j
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [h j]
    dsimp [projectiveCoordinates]
    field_simp
  · intro h
    have hm := (Projectivization.mk_eq_mk_iff' ℂ _ _ (e.map x).rep_nonzero hv).mp
      ((Projectivization.mk_rep (e.map x)).trans h)
    obtain ⟨a,ha⟩ := hm
    have hai (j) : (e.map x).rep j = a * v j := (congrFun ha j).symm
    have ha0 : a ≠ 0 := by
      intro hz
      apply (e.map x).rep_nonzero
      rw [← ha,hz,zero_smul]
    have hva : v i ≠ 0 := by contrapose! hi; rw [hai i,hi,mul_zero]
    intro j
    dsimp [projectiveCoordinates]
    rw [hai i,hai j]
    field_simp

theorem incidence_unique {x y : X.Carrier} {v : Fin (e.N+1) → ℂ}
    (hv : v ≠ 0) (hx : e.Incidence x v) (hy : e.Incidence y v) : x = y :=
  e.injective ((e.incidence_iff_projective hv).mp hx |>.trans
    ((e.incidence_iff_projective hv).mp hy).symm)

theorem isClosed_incidence : IsClosed {q : X.Carrier × (Fin (e.N+1) → ℂ) |
    e.Incidence q.1 q.2} := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨x,v⟩ hx
  obtain ⟨i,hi⟩ := Function.ne_iff.mp (e.map x).rep_nonzero
  change (e.map x).rep i ≠ 0 at hi
  change ¬ e.Incidence x v at hx
  rw [e.incidence_iff_coordinates hi] at hx
  push Not at hx
  obtain ⟨j,hj⟩ := hx
  have hc : ContinuousAt (fun y => projectiveCoordinates i (e.map y) j) x :=
    (continuous_apply j).continuousAt.comp
      (e.holomorphic i |>.contMDiffAt ((e.open_patch i).mem_nhds hi)).continuousAt
  have hg : ContinuousAt (fun q : X.Carrier × (Fin (e.N+1) → ℂ) =>
      projectiveCoordinates i (e.map q.1) j) (x,v) := by
    have hfst : ContinuousAt (Prod.fst : X.Carrier × (Fin (e.N+1) → ℂ) → X.Carrier) (x,v) :=
      continuous_fst.continuousAt
    exact hc.comp_of_eq hfst rfl
  have he : ∀ᶠ q : X.Carrier × (Fin (e.N+1) → ℂ) in 𝓝 (x,v),
      q.2 j ≠ q.2 i * projectiveCoordinates i (e.map q.1) j :=
    (((continuous_apply j).comp continuous_snd).continuousAt.ne_iff_eventually_ne
      (((continuous_apply i).comp continuous_snd).continuousAt.mul hg)).mp hj
  have hp : ∀ᶠ q : X.Carrier × (Fin (e.N+1) → ℂ) in 𝓝 (x,v),
      (e.map q.1).rep i ≠ 0 :=
    (continuous_fst.tendsto (x,v)).eventually ((e.open_patch i).mem_nhds hi)
  filter_upwards [he,hp] with q hq hqi
  exact fun hh => hq ((e.incidence_iff_coordinates hqi).mp hh j)

 

theorem isClosed_cone [CompactSpace X.Carrier] :
    IsClosed {v : Fin (e.N+1) → ℂ | ∃ x, e.Incidence x v} := by
  have h := isClosedMap_snd_of_compactSpace _ e.isClosed_incidence
  convert h using 1
  ext v
  simp only [mem_image,mem_ofPred_eq,Prod.exists]
  aesop

 

theorem incidence_localizes [CompactSpace X.Carrier] {x : X.Carrier}
    {v : Fin (e.N+1) → ℂ} (hv : v ≠ 0) (hx : e.Incidence x v)
    {U : Set X.Carrier} (hU : IsOpen U) (hxU : x ∈ U) :
    ∀ᶠ w in 𝓝 v, ∀ y, e.Incidence y w → y ∈ U := by
  let A : Set (X.Carrier × (Fin (e.N+1) → ℂ)) :=
    {q | e.Incidence q.1 q.2} ∩ (Prod.fst ⁻¹' Uᶜ)
  have hA : IsClosed A := e.isClosed_incidence.inter (hU.isClosed_compl.preimage continuous_fst)
  have hB := isClosedMap_snd_of_compactSpace A hA
  have hvB : v ∈ (Prod.snd '' A)ᶜ := by
    rintro ⟨⟨y,w⟩,hy,rfl⟩
    exact hy.2 (e.incidence_unique hv hy.1 hx ▸ hxU)
  filter_upwards [hB.isOpen_compl.mem_nhds hvB] with w hw y hy
  by_contra hyU
  exact hw ⟨(y,w),⟨hy,hyU⟩,rfl⟩

 
def normalize (i : Fin (e.N+1)) (v : Fin (e.N+1) → ℂ) : Fin (e.N+1) → ℂ :=
  fun j => (v i)⁻¹ * v j

theorem normalize_analytic {i : Fin (e.N+1)} {v : Fin (e.N+1) → ℂ}
    (hv : v i ≠ 0) : AnalyticAt ℂ (e.normalize i) v := by
  apply analyticAt_pi_iff.mpr
  intro j
  exact ((ContinuousLinearMap.proj i : (Fin (e.N+1) → ℂ) →L[ℂ] ℂ).analyticAt v).inv hv |>.mul
    ((ContinuousLinearMap.proj j : (Fin (e.N+1) → ℂ) →L[ℂ] ℂ).analyticAt v)

theorem incidence_iff_normalize {x : X.Carrier} {v : Fin (e.N+1) → ℂ}
    {i : Fin (e.N+1)} (hi : (e.map x).rep i ≠ 0) (hv : v i ≠ 0) :
    e.Incidence x v ↔ e.normalize i v = projectiveCoordinates i (e.map x) := by
  rw [e.incidence_iff_coordinates hi]
  constructor
  · intro h
    ext j
    dsimp [normalize]
    rw [h j,← mul_assoc,inv_mul_cancel₀ hv,one_mul]
  · intro h j
    have hj := congrFun h j
    dsimp [normalize] at hj
    rw [← hj,← mul_assoc,mul_inv_cancel₀ hv,one_mul]

 

theorem cone_local_equations [CompactSpace X.Carrier] {v : Fin (e.N+1) → ℂ}
    (hv : v ≠ 0) (hvX : ∃ x, e.Incidence x v) :
    ∃ D : (Fin (e.N+1) → ℂ) → (Fin (e.N+1) → ℂ), AnalyticAt ℂ D v ∧
      ∀ᶠ w in 𝓝 v, (∃ x, e.Incidence x w) ↔ D w = 0 := by
  obtain ⟨x,hx⟩ := hvX
  obtain ⟨i,hi⟩ := Function.ne_iff.mp (e.map x).rep_nonzero
  change (e.map x).rep i ≠ 0 at hi
  have hvi : v i ≠ 0 := by
    intro hz
    apply hv
    ext j
    rw [(e.incidence_iff_coordinates hi).mp hx j,hz,zero_mul]
    rfl
  let c := chartAt (Model X) x
  let H := e.withinChart i x
  let n := e.normalize i
  have hcx : x ∈ c.source := mem_chart_source (Model X) x
  have hn : n v = H (c x) := by
    rw [e.incidence_iff_normalize hi hvi] at hx
    simpa [H,withinChart,c] using hx
  have hH : AnalyticAt ℂ H (c x) := e.withinChart_analytic i x hcx hi
  obtain ⟨r,hr,hr0,hri⟩ := AnalyticRetraction.exists_left_inverse hH
    (e.withinChart_immersion i x hcx hi)
  have hrn : AnalyticAt ℂ (r ∘ n) v := (hn ▸ hr).comp (e.normalize_analytic hvi)
  have hrn0 : r (n v) = c x := hn ▸ hr0
  have heq : ∀ᶠ y in 𝓝 x, y ∈ c.source ∧ (e.map y).rep i ≠ 0 ∧
      r (projectiveCoordinates i (e.map y)) = c y := by
    have hri' := (c.continuousAt hcx).eventually hri
    filter_upwards [c.open_source.mem_nhds hcx,(e.open_patch i).mem_nhds hi,hri'] with y hy hiy hry
    refine ⟨hy,hiy,?_⟩
    change r (projectiveCoordinates i (e.map (c.symm (c y)))) = c y at hry
    rwa [c.left_inv hy] at hry
  obtain ⟨U,hUsub,hU,hxU⟩ := mem_nhds_iff.mp heq
  have hloc := e.incidence_localizes hv hx hU hxU
  have hH' : AnalyticAt ℂ H ((r ∘ n) v) := by simpa only [Function.comp_apply,hrn0] using hH
  have hR : AnalyticAt ℂ (fun w => H (r (n w))) v := hH'.comp hrn
  let D := fun w => H (r (n w)) - n w
  refine ⟨D,hR.sub (e.normalize_analytic hvi),?_⟩
  have hc : ContinuousAt (fun w => c.symm (r (n w))) v := by
    apply (c.continuousAt_symm (c.map_source hcx)).comp_of_eq hrn.continuousAt
    exact hrn0
  have hx0 : c.symm (r (n v)) = x := by rw [hrn0,c.left_inv hcx]
  have hp : ∀ᶠ w in 𝓝 v, (e.map (c.symm (r (n w)))).rep i ≠ 0 :=
    hc.eventually (hx0 ▸ (e.open_patch i).mem_nhds hi)
  have hni : ∀ᶠ w in 𝓝 v, w i ≠ 0 := (continuous_apply i).continuousAt.eventually_ne hvi
  filter_upwards [hloc,hp,hni] with w hw hpw hiw
  change (∃ y, e.Incidence y w) ↔ H (r (n w)) - n w = 0
  rw [sub_eq_zero]
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨hcy,hiy,hry⟩ := hUsub (hw y hy)
    have hnw : n w = projectiveCoordinates i (e.map y) :=
      (e.incidence_iff_normalize hiy hiw).mp hy
    rw [hnw,hry]
    exact congrArg (projectiveCoordinates i ∘ e.map) (c.left_inv hcy)
  · intro h
    refine ⟨c.symm (r (n w)),(e.incidence_iff_normalize hpw hiw).mpr ?_⟩
    exact h.symm

theorem cone_local_equations_any [CompactSpace X.Carrier] {v : Fin (e.N+1) → ℂ}
    (hv : v ≠ 0) :
    ∃ D : (Fin (e.N+1) → ℂ) → (Fin (e.N+1) → ℂ), AnalyticAt ℂ D v ∧
      ∀ᶠ w in 𝓝 v, (∃ x, e.Incidence x w) ↔ D w = 0 := by
  by_cases h : ∃ x, e.Incidence x v
  · exact e.cone_local_equations hv h
  · refine ⟨fun _ => 1,analyticAt_const,?_⟩
    filter_upwards [e.isClosed_cone.isOpen_compl.mem_nhds h] with w hw
    constructor
    · exact fun hh => False.elim (hw hh)
    · intro hh
      exact False.elim (one_ne_zero (congrFun hh 0 : (1 : ℂ) = 0))

end

variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 

theorem cone_continuation [CompactSpace X.Carrier] {Q : E → Fin (e.N+1) → ℂ}
    {U : Set E} (hU : IsPreconnected U) (hQ : AnalyticOnNhd ℂ Q U)
    (hnz : ∀ z ∈ U, Q z ≠ 0)
    (hstart : (U ∩ interior {z | ∃ x, e.Incidence x (Q z)}).Nonempty) :
    ∀ z ∈ U, ∃ x, e.Incidence x (Q z) := by
  apply AnalyticContinuation.subset_of_local_analytic_equations (F := Fin (e.N+1) → ℂ) hU _ hstart
  intro z hz
  obtain ⟨D,hD,he⟩ := e.cone_local_equations_any (hnz z hz)
  exact ⟨D ∘ Q,hD.comp (hQ z hz),(hQ z hz).continuousAt.eventually he⟩

 

theorem exists_local_lift [CompactSpace X.Carrier] {x : X.Carrier}
    {v : Fin (e.N+1) → ℂ} (hv : v ≠ 0) (hx : e.Incidence x v) :
    ∃ L : (Fin (e.N+1) → ℂ) → X.Carrier,
      ContMDiffAt 𝓘(ℂ,Fin (e.N+1) → ℂ) (ModelWithCorners X) ω L v ∧
      ∀ᶠ w in 𝓝 v, ∀ y, e.Incidence y w → L w = y := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp (e.map x).rep_nonzero
  change (e.map x).rep i ≠ 0 at hi
  have hvi : v i ≠ 0 := by
    intro hz
    apply hv
    ext j
    rw [(e.incidence_iff_coordinates hi).mp hx j,hz,zero_mul]
    rfl
  let c := chartAt (Model X) x
  let H := e.withinChart i x
  let n := e.normalize i
  have hcx : x ∈ c.source := mem_chart_source (Model X) x
  have hn : n v = H (c x) := by
    rw [e.incidence_iff_normalize hi hvi] at hx
    simpa [H,withinChart,c] using hx
  have hH : AnalyticAt ℂ H (c x) := e.withinChart_analytic i x hcx hi
  obtain ⟨r,hr,hr0,hri⟩ := AnalyticRetraction.exists_left_inverse hH
    (e.withinChart_immersion i x hcx hi)
  have hrn : AnalyticAt ℂ (r ∘ n) v := (hn ▸ hr).comp (e.normalize_analytic hvi)
  have hrn0 : r (n v) = c x := hn ▸ hr0
  have heq : ∀ᶠ y in 𝓝 x, y ∈ c.source ∧ (e.map y).rep i ≠ 0 ∧
      r (projectiveCoordinates i (e.map y)) = c y := by
    have hri' := (c.continuousAt hcx).eventually hri
    filter_upwards [c.open_source.mem_nhds hcx,(e.open_patch i).mem_nhds hi,hri'] with y hy hiy hry
    refine ⟨hy,hiy,?_⟩
    change r (projectiveCoordinates i (e.map (c.symm (c y)))) = c y at hry
    rwa [c.left_inv hy] at hry
  obtain ⟨U,hUsub,hU,hxU⟩ := mem_nhds_iff.mp heq
  have hloc := e.incidence_localizes hv hx hU hxU
  refine ⟨c.symm ∘ (r ∘ n),?_,?_⟩
  · have hc := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x)
        (c.map_source hcx)
    exact hc.comp_of_eq hrn.contDiffAt.contMDiffAt hrn0
  · have hni : ∀ᶠ w in 𝓝 v, w i ≠ 0 := (continuous_apply i).continuousAt.eventually_ne hvi
    filter_upwards [hloc,hni] with w hw hiw y hy
    obtain ⟨hcy,hiy,hry⟩ := hUsub (hw y hy)
    have hnw : n w = projectiveCoordinates i (e.map y) :=
      (e.incidence_iff_normalize hiy hiw).mp hy
    dsimp only [Function.comp_apply]
    rw [hnw,hry,c.left_inv hcy]

 

theorem holomorphic_of_incidence [CompactSpace X.Carrier] {Q : E → Fin (e.N+1) → ℂ}
    {F : E → X.Carrier} {z : E} (hQ : AnalyticAt ℂ Q z) (hnz : Q z ≠ 0)
    (hF : ∀ᶠ w in 𝓝 z, e.Incidence (F w) (Q w)) :
    ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z := by
  obtain ⟨L,hL,hLinv⟩ := e.exists_local_lift hnz hF.self_of_nhds
  apply (hL.comp z hQ.contDiffAt.contMDiffAt).congr_of_eventuallyEq
  filter_upwards [hF,hQ.continuousAt.eventually hLinv] with w hw hLw
  exact (hLw (F w) hw).symm

 

theorem exists_global_regular_lift [CompactSpace X.Carrier]
    (Q : ℂ × ℂ → Fin (e.N+1) → ℂ) (hQ : AnalyticOnNhd ℂ Q univ)
    (hB : Set.Finite {z | Q z = 0})
    (F₀ : ℂ × ℂ → X.Carrier) (a : ℂ × ℂ)
    (hstart : ∀ᶠ z in 𝓝 a, Q z ≠ 0 ∧ e.Incidence (F₀ z) (Q z)) :
    ∃ F : ℂ × ℂ → X.Carrier,
      ContMDiffOn 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F {z | Q z ≠ 0} ∧
      (∀ z, Q z ≠ 0 → e.Incidence (F z) (Q z)) ∧ F =ᶠ[𝓝 a] F₀ := by
  let U := {z | Q z ≠ 0}
  have hrank : 1 < Module.rank ℝ (ℂ × ℂ) := by
    rw [rank_prod',Complex.rank_real_complex]
    norm_num
  have hUconn : IsPreconnected U :=
    (hB.countable.isPathConnected_compl_of_one_lt_rank hrank).isConnected.isPreconnected
  have hUopen : IsOpen U := hB.isClosed.isOpen_compl
  have hne : (U ∩ interior {z | ∃ x, e.Incidence x (Q z)}).Nonempty := by
    refine ⟨a,hstart.self_of_nhds.1,mem_interior_iff_mem_nhds.mpr ?_⟩
    filter_upwards [hstart] with z hz
    exact ⟨F₀ z,hz.2⟩
  have hcone : ∀ z ∈ U, ∃ x, e.Incidence x (Q z) :=
    e.cone_continuation hUconn (hQ.mono (subset_univ U)) (fun _ hz => hz) hne
  let F := fun z => if hz : z ∈ U then (hcone z hz).choose else F₀ a
  have hF (z : ℂ × ℂ) (hz : z ∈ U) : e.Incidence (F z) (Q z) := by
    dsimp only [F]
    rw [dite_eq_left hz]
    exact (hcone z hz).choose_spec
  refine ⟨F,?_,hF,?_⟩
  · intro z hz
    apply ContMDiffAt.contMDiffWithinAt
    apply e.holomorphic_of_incidence (hQ z (mem_univ z)) hz
    filter_upwards [hUopen.mem_nhds hz] with w hw
    exact hF w hw
  · filter_upwards [hstart] with z hz
    exact e.incidence_unique hz.1 (hF z hz.1) hz.2

end SplitTangent.ProjectiveEmbedding

namespace SplitTangent.TangentSplitting
section
open Filter Topology
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 

theorem chart_derivative {F : E → X.Carrier} {z : E} {x : X.Carrier}
    (hF : ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z)
    (hx : F z ∈ (chartAt (Model X) x).source) :
    fderiv ℂ ((chartAt (Model X) x) ∘ F) z =
      ((trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ (F z)).comp
        (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z) := by
  have hc := contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hx
  have ht : (trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ (F z) =
      mfderiv (ModelWithCorners X) 𝓘(ℂ,Model X) (chartAt (Model X) x) (F z) :=
    TangentBundle.continuousLinearMapAt_trivializationAt (I := ModelWithCorners X) hx
  rw [ht]
  exact mfderiv_eq_fderiv.symm.trans (mfderiv_comp z
    (hc.mdifferentiableAt (by simp)) (hF.mdifferentiableAt (by simp)))

theorem chart_pde_iff {F : E → X.Carrier} {z : E} {x : X.Carrier} (a b : E)
    (hF : ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z)
    (hx : F z ∈ (chartAt (Model X) x).source) :
    (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z b =
        S.projector (F z) (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z a)) ↔
      fderiv ℂ ((chartAt (Model X) x) ∘ F) z b =
        S.coordinateProjector x ((chartAt (Model X) x) (F z))
          (fderiv ℂ ((chartAt (Model X) x) ∘ F) z a) := by
  let t := trivializationAt (Model X) (Tangent X) x
  have ht : F z ∈ t.baseSet := hx
  have hd (v : E) : fderiv ℂ ((chartAt (Model X) x) ∘ F) z v =
      t.continuousLinearMapAt ℂ (F z) (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z v) :=
    congrArg (fun L : E →L[ℂ] Model X => L v) (chart_derivative hF hx)
  rw [hd a,hd b]
  change _ ↔ t.continuousLinearMapAt ℂ (F z) _ =
    t.continuousLinearMapAt ℂ ((chartAt (Model X) x).symm ((chartAt (Model X) x) (F z)))
      (S.projector _ (t.symmL ℂ _ (t.continuousLinearMapAt ℂ (F z) _)))
  rw [(chartAt (Model X) x).left_inv hx,t.symmL_continuousLinearMapAt ht]
  constructor
  · intro h
    exact congrArg (t.continuousLinearMapAt ℂ (F z)) h
  · intro h
    have hh := congrArg (t.symmL ℂ (F z)) h
    simpa only [t.symmL_continuousLinearMapAt ht] using hh

 
theorem pde_local_equations {F : E → X.Carrier} {z : E} (a b : E)
    (hF : ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z) :
    ∃ f : E → Model X, AnalyticAt ℂ f z ∧ ∀ᶠ w in 𝓝 z,
      (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F w b =
        S.projector (F w) (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F w a)) ↔ f w = 0 := by
  let x := F z
  let c := chartAt (Model X) x
  let G := c ∘ F
  have hx : F z ∈ c.source := mem_chart_source (Model X) x
  have hc := contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hx
  have hG : AnalyticAt ℂ G z := (hc.comp z hF).contDiffAt.analyticAt
  let f := fun w => fderiv ℂ G w b - S.coordinateProjector x (G w) (fderiv ℂ G w a)
  refine ⟨f,?_,?_⟩
  · have hd (v : E) : AnalyticAt ℂ (fun w => fderiv ℂ G w v) z :=
      (ContinuousLinearMap.apply ℂ (Model X) v).analyticAt _ |>.comp hG.fderiv
    apply (hd b).sub
    rw [← funext fun w => S.coordinateMatrix_mulVec x (G w) (fderiv ℂ G w a)]
    apply analyticAt_pi_iff.mpr
    intro i
    change AnalyticAt ℂ (fun w => ∑ j, S.coordinateMatrix x i j (G w) *
      (fderiv ℂ G w a) j) z
    apply Finset.analyticAt_fun_sum
    intro j _
    exact ((S.coordinateMatrix_analytic x i j (G z) (c.map_source hx)).comp (f := G) (x := z) hG).mul
      (analyticAt_pi_iff.mp (hd a) j)
  · have hFnear := (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hF
    have hxnear := hF.continuousAt.eventually (c.open_source.mem_nhds hx)
    filter_upwards [hFnear,hxnear] with w hw hxw
    exact (S.chart_pde_iff a b hw hxw).trans sub_eq_zero.symm

 

theorem pde_continuation {F : E → X.Carrier} {U : Set E} (a b : E)
    (hU : IsPreconnected U) (hF : ∀ z ∈ U, ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z)
    (hstart : (U ∩ interior {z | mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z b =
        S.projector (F z) (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z a)}).Nonempty) :
    ∀ z ∈ U, mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z b =
      S.projector (F z) (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z a) := by
  apply AnalyticContinuation.subset_of_local_analytic_equations (F := Model X) hU _ hstart
  exact fun z hz => S.pde_local_equations a b (hF z hz)

end

section
open Filter Topology
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

theorem exists_global_regular_tangent_box [CompactSpace X.Carrier]
    (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ (z : ℂ) (P : Fin (e.N+1) → Polynomial (Polynomial ℂ))
      (F : ℂ × ℂ → X.Carrier),
      Finset.univ.gcd P = 1 ∧
      Set.Finite {w : ℂ × ℂ | ∀ j, RationalSurface.eval (P j) w = 0} ∧
      (∃ j, RationalSurface.eval (P j) (z,0) ≠ 0) ∧
      (∀ᶠ u in 𝓝 z, F (u,0) = g.finite u) ∧
      (∀ w, (∃ j, RationalSurface.eval (P j) w ≠ 0) →
        ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F w ∧
        e.Incidence (F w) (fun j => RationalSurface.eval (P j) w) ∧
        mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (0,1) =
          S.projector (F w) (mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (1,0))) := by
  obtain ⟨z,k,P,F₀,hP,hB,hF₀,hdiag,hrep,hpde⟩ := S.exists_rational_tangent_germ e g
  let Q := fun w : ℂ × ℂ => fun j => RationalSurface.eval (P j) w
  have hQ : AnalyticOnNhd ℂ Q univ := fun w _ =>
    analyticAt_pi_iff.mpr (fun j => RationalSurface.eval_analytic (P j) w)
  have hQzero (w) : Q w = 0 ↔ ∀ j, RationalSurface.eval (P j) w = 0 :=
    funext_iff
  have hfinite : Set.Finite {w | Q w = 0} := by
    simpa only [hQzero] using hB
  have hstart : ∀ᶠ w in 𝓝 (z,0), Q w ≠ 0 ∧ e.Incidence (F₀ w) (Q w) := by
    filter_upwards [hrep] with w hw
    refine ⟨fun hz => hw.1 (congrFun hz k), (e.incidence_iff_coordinates hw.2.1).mpr ?_⟩
    intro j
    have hh := (div_eq_iff hw.1).mp (hw.2.2 j)
    exact hh.trans (mul_comm _ _)
  obtain ⟨F,hF,hinc,hagree⟩ := e.exists_global_regular_lift Q hQ hfinite F₀ (z,0) hstart
  let U := {w | Q w ≠ 0}
  have hUopen : IsOpen U := hfinite.isClosed.isOpen_compl
  have hFA (w) (hw : w ∈ U) : ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F w :=
    (hF w hw).contMDiffAt (hUopen.mem_nhds hw)
  have hrank : 1 < Module.rank ℝ (ℂ × ℂ) := by
    rw [rank_prod',Complex.rank_real_complex]
    norm_num
  have hUconn : IsPreconnected U :=
    (hfinite.countable.isPathConnected_compl_of_one_lt_rank hrank).isConnected.isPreconnected
  have hPDEnear : ∀ᶠ w in 𝓝 (z,0),
      mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (0,1) =
        S.projector (F w) (mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (1,0)) := by
    filter_upwards [hpde,hagree.eventuallyEq_nhds] with w hw he
    rw [he.mfderiv_eq,he.self_of_nhds]
    exact hw
  have hglobal := S.pde_continuation (F := F) (U := U) (1,0) (0,1) hUconn hFA
    ⟨(z,0),hstart.self_of_nhds.1,mem_interior_iff_mem_nhds.mpr hPDEnear⟩
  refine ⟨z,P,F,hP,hB,⟨k,hrep.self_of_nhds.1⟩,?_,?_⟩
  · have hline : Tendsto (fun u : ℂ => (u,(0 : ℂ))) (𝓝 z) (𝓝 (z,(0 : ℂ))) :=
      continuousAt_id.prodMk continuousAt_const
    filter_upwards [hdiag,hline.eventually hagree] with u hu he
    exact he.trans hu
  · intro w hw
    have hwU : w ∈ U := by
      obtain ⟨j,hj⟩ := hw
      exact fun he => hj (congrFun he j)
    exact ⟨hFA w hwU,hinc w hwU,hglobal w hwU⟩

end

open Filter Topology
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']

 
def WedgeAt (F : E → X.Carrier) (A : E → ℂ) (z : E) : Prop :=
  ∀ v w : E, fderiv ℂ A z v • S.projector (F z) (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z w) =
    fderiv ℂ A z w • S.projector (F z) (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z v)

def projectedInChart (x : X.Carrier) (F : E → X.Carrier) (v : E) (z : E) : Model X :=
  S.coordinateProjector x ((chartAt (Model X) x) (F z))
    (fderiv ℂ ((chartAt (Model X) x) ∘ F) z v)

lemma projectedInChart_eq {F : E → X.Carrier} {z : E} {x : X.Carrier} (v : E)
    (hF : ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z)
    (hx : F z ∈ (chartAt (Model X) x).source) :
    S.projectedInChart x F v z =
      (trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ (F z)
        (S.projector (F z) (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z v)) := by
  let t := trivializationAt (Model X) (Tangent X) x
  have ht : F z ∈ t.baseSet := hx
  have hd : fderiv ℂ ((chartAt (Model X) x) ∘ F) z v =
      t.continuousLinearMapAt ℂ (F z) (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z v) :=
    congrArg (fun L : E →L[ℂ] Model X => L v) (chart_derivative hF hx)
  simp only [projectedInChart,hd,coordinateProjector,ContinuousLinearMap.comp_apply]
  rw [(chartAt (Model X) x).left_inv hx,t.symmL_continuousLinearMapAt ht]

lemma projectedInChart_analytic {F : E → X.Carrier} {z : E} {x : X.Carrier} (v : E)
    (hF : ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z)
    (hx : F z ∈ (chartAt (Model X) x).source) :
    AnalyticAt ℂ (S.projectedInChart x F v) z := by
  let c := chartAt (Model X) x
  let G := c ∘ F
  have hc := contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hx
  have hG : AnalyticAt ℂ G z := (hc.comp z hF).contDiffAt.analyticAt
  have hd : AnalyticAt ℂ (fun w => fderiv ℂ G w v) z :=
    (ContinuousLinearMap.apply ℂ (Model X) v).analyticAt _ |>.comp hG.fderiv
  change AnalyticAt ℂ (fun w => S.coordinateProjector x (G w) (fderiv ℂ G w v)) z
  rw [← funext fun w => S.coordinateMatrix_mulVec x (G w) (fderiv ℂ G w v)]
  apply analyticAt_pi_iff.mpr
  intro i
  change AnalyticAt ℂ (fun w => ∑ j, S.coordinateMatrix x i j (G w) * (fderiv ℂ G w v) j) z
  apply Finset.analyticAt_fun_sum
  intro j _
  exact ((S.coordinateMatrix_analytic x i j (G z) (c.map_source hx)).comp hG).mul
    (analyticAt_pi_iff.mp hd j)

lemma chart_wedge_iff {F : E → X.Carrier} {A : E → ℂ} {z : E} {x : X.Carrier}
    (hF : ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z)
    (hx : F z ∈ (chartAt (Model X) x).source) :
    S.WedgeAt F A z ↔ ∀ v w : E,
      fderiv ℂ A z v • S.projectedInChart x F w z =
        fderiv ℂ A z w • S.projectedInChart x F v z := by
  let t := trivializationAt (Model X) (Tangent X) x
  have ht : F z ∈ t.baseSet := hx
  simp only [WedgeAt,projectedInChart_eq S _ hF hx,← map_smul]
  constructor
  · intro h v w
    exact congrArg (t.continuousLinearMapAt ℂ (F z)) (h v w)
  · intro h v w
    have H := congrArg (t.symmL ℂ (F z)) (h v w)
    dsimp only [t] at H ⊢
    simpa only [Bundle.Trivialization.symmL_continuousLinearMapAt (trivializationAt (Model X) (Tangent X) x) ht] using H

 
theorem WedgeAt.comp {F : E → X.Carrier} {A : E → ℂ} {f : E' → E} {z : E'}
    (hW : S.WedgeAt F A (f z))
    (hF : ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F (f z))
    (hA : DifferentiableAt ℂ A (f z)) (hf : DifferentiableAt ℂ f z) :
    S.WedgeAt (F ∘ f) (A ∘ f) z := by
  intro v w
  rw [fderiv_comp z hA hf,mfderiv_comp z (hF.mdifferentiableAt (by simp)) hf.mdifferentiableAt,
    mfderiv_eq_fderiv]
  exact hW (fderiv ℂ f z v) (fderiv ℂ f z w)

 

theorem wedgeAt_of_frequently {F : E → X.Carrier} {A : E → ℂ} {z : E}
    (hF : ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z)
    (hA : AnalyticAt ℂ A z) (hW : ∃ᶠ w in 𝓝 z, S.WedgeAt F A w) :
    S.WedgeAt F A z := by
  let x := F z
  let c := chartAt (Model X) x
  have hx : F z ∈ c.source := mem_chart_source (Model X) x
  have hnear := (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hF
  have hxnear := hF.continuousAt.eventually (c.open_source.mem_nhds hx)
  apply (S.chart_wedge_iff hF hx).mpr
  intro v w
  have hd (v : E) : ContinuousAt (fun q => fderiv ℂ A q v) z :=
    hA.fderiv.continuousAt.clm_apply continuousAt_const
  have hl := (hd v).smul (S.projectedInChart_analytic w hF hx).continuousAt
  have hr := (hd w).smul (S.projectedInChart_analytic v hF hx).continuousAt
  apply tendsto_nhds_unique_of_frequently_eq hl hr
  exact (hW.and_eventually (hnear.and hxnear)).mono (fun q hq =>
    (S.chart_wedge_iff hq.2.1 hq.2.2).mp hq.1 v w)

end SplitTangent.TangentSplitting

namespace SplitTangent.ExceptionalTangency
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 
theorem factor_fderiv (n : ℕ) {h : ℂ × ℂ → ℂ} {w : ℂ × ℂ}
    (hh : DifferentiableAt ℂ h w) (v : ℂ × ℂ) :
    fderiv ℂ (fun w : ℂ × ℂ => w.1 ^ (n+1) * h w) w v =
      w.1 ^ n * (((n+1 : ℕ) : ℂ) * h w * v.1 + w.1 * fderiv ℂ h w v) := by
  have H := ((hasFDerivAt_fst (𝕜 := ℂ) (p := w)).pow (n+1)).mul hh.hasFDerivAt
  change fderiv ℂ ((fun w : ℂ × ℂ => w.1 ^ (n+1)) * h) w v = _
  rw [H.fderiv]
  simp only [add_apply,smul_apply,
    smul_eq_mul,Nat.add_sub_cancel,nsmul_eq_mul]
  rw [pow_succ]
  change w.1 ^ n * w.1 * (fderiv ℂ h w v) + h w *
    (↑(n+1) * w.1 ^ n * v.1) = _
  ring

 

theorem kills_tangent_of_wedge (n : ℕ) {z : ℂ} {h : ℂ × ℂ → ℂ}
    (hh : AnalyticAt ℂ h (0,z)) (hu : h (0,z) ≠ 0)
    (A : ℂ × ℂ → (ℂ × ℂ →L[ℂ] E)) (hA : ContinuousAt A (0,z))
    (hwedge : ∀ᶠ w in 𝓝 (0,z),
      (fderiv ℂ (fun w : ℂ × ℂ => w.1 ^ (n+1) * h w) w (1,0)) • A w (0,1) =
      (fderiv ℂ (fun w : ℂ × ℂ => w.1 ^ (n+1) * h w) w (0,1)) • A w (1,0)) :
    A (0,z) (0,1) = 0 := by
  let L : ℂ × ℂ → E := fun w =>
    (((n+1 : ℕ) : ℂ) * h w + w.1 * fderiv ℂ h w (1,0)) • A w (0,1)
  let R : ℂ × ℂ → E := fun w => (w.1 * fderiv ℂ h w (0,1)) • A w (1,0)
  have hL : ContinuousAt L (0,z) :=
    ((continuousAt_const.mul hh.continuousAt).add
      (continuousAt_fst.mul (hh.fderiv.continuousAt.clm_apply continuousAt_const))).smul
        (hA.clm_apply continuousAt_const)
  have hR : ContinuousAt R (0,z) :=
    (continuousAt_fst.mul (hh.fderiv.continuousAt.clm_apply continuousAt_const)).smul
      (hA.clm_apply continuousAt_const)
  have hline : Tendsto (fun r : ℂ => (r,z)) (𝓝[≠] 0) (𝓝 (0,z)) :=
    (continuousAt_id.prodMk continuousAt_const).mono_left nhdsWithin_le_nhds
  have he : (fun r : ℂ => L (r,z)) =ᶠ[𝓝[≠] 0] (fun r => R (r,z)) := by
    filter_upwards [hline.eventually hwedge,hline.eventually hh.eventually_analyticAt,
      self_mem_nhdsWithin] with r hr har hr0
    have hn : r ^ n ≠ 0 := pow_ne_zero _ hr0
    rw [factor_fderiv n har.differentiableAt,factor_fderiv n har.differentiableAt] at hr
    simp only [mul_one,mul_zero,zero_add] at hr
    rw [mul_smul,mul_smul] at hr
    exact smul_right_injective E hn hr
  have h0 := tendsto_nhds_unique_of_eventuallyEq (hL.tendsto.comp hline) (hR.tendsto.comp hline) he
  have hn : (((n+1 : ℕ) : ℂ) * h (0,z)) ≠ 0 := mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero n) hu
  have hs : (((n+1 : ℕ) : ℂ) * h (0,z)) • A (0,z) (0,1) = 0 := by
    simpa only [L,R,zero_mul,add_zero,zero_smul] using h0
  exact (smul_eq_zero.mp hs).resolve_left hn

 

theorem complementary_kills_tangent (n m : ℕ) {z : ℂ} {h k : ℂ × ℂ → ℂ}
    (hh : AnalyticAt ℂ h (0,z)) (hu : h (0,z) ≠ 0)
    (hk : AnalyticAt ℂ k (0,z)) (ku : k (0,z) ≠ 0)
    (A B D : ℂ × ℂ → (ℂ × ℂ →L[ℂ] E))
    (hA : ContinuousAt A (0,z)) (hB : ContinuousAt B (0,z))
    (hcomp : D (0,z) = A (0,z) + B (0,z))
    (hWA : ∀ᶠ w in 𝓝 (0,z),
      (fderiv ℂ (fun w : ℂ × ℂ => w.1 ^ (n+1) * h w) w (1,0)) • A w (0,1) =
      (fderiv ℂ (fun w : ℂ × ℂ => w.1 ^ (n+1) * h w) w (0,1)) • A w (1,0))
    (hWB : ∀ᶠ w in 𝓝 (0,z),
      (fderiv ℂ (fun w : ℂ × ℂ => w.1 ^ (m+1) * k w) w (1,0)) • B w (0,1) =
      (fderiv ℂ (fun w : ℂ × ℂ => w.1 ^ (m+1) * k w) w (0,1)) • B w (1,0)) :
    D (0,z) (0,1) = 0 := by
  rw [hcomp,add_apply,
    kills_tangent_of_wedge n hh hu A hA hWA,kills_tangent_of_wedge m hk ku B hB hWB,add_zero]

end SplitTangent.ExceptionalTangency

namespace SplitTangent.ComplexManifold
open Filter Topology Metric Set
variable {X : ComplexManifold.{u}}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 

theorem chart_derivative {F : E → X.Carrier} {z : E} {x : X.Carrier}
    (hF : ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z)
    (hx : F z ∈ (chartAt (Model X) x).source) :
    fderiv ℂ ((chartAt (Model X) x) ∘ F) z =
      ((trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ (F z)).comp
        (mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z) := by
  have hc := contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hx
  have ht : (trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ (F z) =
      mfderiv (ModelWithCorners X) 𝓘(ℂ,Model X) (chartAt (Model X) x) (F z) :=
    TangentBundle.continuousLinearMapAt_trivializationAt (I := ModelWithCorners X) hx
  rw [ht]
  exact mfderiv_eq_fderiv.symm.trans (mfderiv_comp z
    (hc.mdifferentiableAt (by simp)) (hF.mdifferentiableAt (by simp)))

 
theorem locally_eq_of_mfderiv_zero {F : E → X.Carrier} {U : Set E}
    (hU : IsOpen U) (hF : ContMDiffOn 𝓘(ℂ,E) (ModelWithCorners X) ω F U)
    (hd : ∀ z ∈ U, mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z = 0)
    {z : E} (hz : z ∈ U) : ∀ᶠ w in 𝓝 z, F w = F z := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  let c := chartAt (Model X) (F z)
  have hzF := hF.contMDiffAt (hU.mem_nhds hz)
  have hp : ∀ᶠ w in 𝓝 z, F w ∈ c.source :=
    hzF.continuousAt.eventually (c.open_source.mem_nhds (mem_chart_source (Model X) (F z)))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (Filter.Eventually.and (hU.mem_nhds hz) hp)
  have ha (w : E) (hw : w ∈ ball z r) : AnalyticAt ℂ (c ∘ F) w := by
    have hc := contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) (F z)) (hball hw).2
    exact (hc.comp w (hF.contMDiffAt (hU.mem_nhds (hball hw).1))).contDiffAt.analyticAt
  have hd' (w : E) (hw : w ∈ ball z r) : fderiv ℂ (c ∘ F) w = 0 := by
    rw [chart_derivative (hF.contMDiffAt (hU.mem_nhds (hball hw).1)) (hball hw).2,
      hd w (hball hw).1,ContinuousLinearMap.comp_zero]
    rfl
  filter_upwards [Metric.ball_mem_nhds z hr] with w hw
  apply c.injOn (hball hw).2 (mem_chart_source (Model X) (F z))
  exact isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball z r).isPreconnected
    (fun w hw => (ha w hw).differentiableAt.differentiableWithinAt) hd' hw (mem_ball_self hr)

 

theorem eq_of_mfderiv_zero {F : E → X.Carrier} {U : Set E}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hF : ContMDiffOn 𝓘(ℂ,E) (ModelWithCorners X) ω F U)
    (hd : ∀ z ∈ U, mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z = 0)
    {z w : E} (hz : z ∈ U) (hw : w ∈ U) : F z = F w := by
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hconn
  have hl : IsLocallyConstant (fun q : U => F q) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro q
    exact continuous_subtype_val.continuousAt.eventually (locally_eq_of_mfderiv_zero hU hF hd q.2)
  exact hl.apply_eq_of_preconnectedSpace ⟨z,hz⟩ ⟨w,hw⟩

 

theorem curve_eq_of_mfderiv_zero_off_finite {F : ℂ → X.Carrier} {B : Set ℂ}
    (hB : B.Finite) (hF : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω F)
    (hd : ∀ z ∉ B, mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) F z = 0)
    (z w : ℂ) : F z = F w := by
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  have hconn := (hB.countable.isPathConnected_compl_of_one_lt_rank hrank).isConnected.isPreconnected
  have hden : Dense Bᶜ := hB.countable.dense_compl ℝ
  obtain ⟨a,ha⟩ := hden.nonempty
  have hc : F = fun _ => F a := Continuous.ext_on hden hF.continuous continuous_const
    (fun x hx => eq_of_mfderiv_zero hB.isClosed.isOpen_compl hconn hF.contMDiffOn hd hx ha)
  rw [congrFun hc z,congrFun hc w]

end SplitTangent.ComplexManifold

namespace SplitTangent.ExceptionalTangency
open Filter Topology
open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma kills_second_of_wedge (n : ℕ) {z : ℂ} {h : ℂ × ℂ → ℂ}
    (hh : AnalyticAt ℂ h (0,z)) (hu : h (0,z) ≠ 0)
    (A B : ℂ × ℂ → E) (hA : ContinuousAt A (0,z)) (hB : ContinuousAt B (0,z))
    (hwedge : ∀ᶠ w in 𝓝 (0,z),
      (fderiv ℂ (fun w : ℂ × ℂ => w.1 ^ (n+1) * h w) w (1,0)) • B w =
      (fderiv ℂ (fun w : ℂ × ℂ => w.1 ^ (n+1) * h w) w (0,1)) • A w) :
    B (0,z) = 0 := by
  let L := fun w : ℂ × ℂ =>
    (((n+1 : ℕ) : ℂ) * h w + w.1 * fderiv ℂ h w (1,0)) • B w
  let R := fun w : ℂ × ℂ => (w.1 * fderiv ℂ h w (0,1)) • A w
  have hL : ContinuousAt L (0,z) :=
    ((continuousAt_const.mul hh.continuousAt).add
      (continuousAt_fst.mul (hh.fderiv.continuousAt.clm_apply continuousAt_const))).smul hB
  have hR : ContinuousAt R (0,z) :=
    (continuousAt_fst.mul (hh.fderiv.continuousAt.clm_apply continuousAt_const)).smul hA
  have hline : Tendsto (fun r : ℂ => (r,z)) (𝓝[≠] 0) (𝓝 (0,z)) :=
    (continuousAt_id.prodMk continuousAt_const).mono_left nhdsWithin_le_nhds
  have he : (fun r : ℂ => L (r,z)) =ᶠ[𝓝[≠] 0] (fun r => R (r,z)) := by
    filter_upwards [hline.eventually hwedge,hline.eventually hh.eventually_analyticAt,
      self_mem_nhdsWithin] with r hr har hr0
    have hn : r ^ n ≠ 0 := pow_ne_zero _ hr0
    rw [factor_fderiv n har.differentiableAt,factor_fderiv n har.differentiableAt] at hr
    simp only [mul_one,mul_zero,zero_add] at hr
    rw [mul_smul,mul_smul] at hr
    exact smul_right_injective E hn hr
  have h0 := tendsto_nhds_unique_of_eventuallyEq (hL.tendsto.comp hline) (hR.tendsto.comp hline) he
  have hn : (((n+1 : ℕ) : ℂ) * h (0,z)) ≠ 0 := mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero n) hu
  have hs : (((n+1 : ℕ) : ℂ) * h (0,z)) • B (0,z) = 0 := by
    simpa only [L,R,zero_mul,add_zero,zero_smul] using h0
  exact (smul_eq_zero.mp hs).resolve_left hn
end SplitTangent.ExceptionalTangency

namespace SplitTangent.TangentSplitting
open Filter Topology
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

theorem kills_exceptional_of_wedge (n : ℕ) {z : ℂ} {h : ℂ × ℂ → ℂ}
    {F : ℂ × ℂ → X.Carrier} (hF : ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F (0,z))
    (hh : AnalyticAt ℂ h (0,z)) (hu : h (0,z) ≠ 0)
    (hW : ∀ᶠ w in 𝓝 (0,z), S.WedgeAt F (fun w : ℂ × ℂ => w.1^(n+1)*h w) w) :
    S.projector (F (0,z)) (mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F (0,z) (0,1)) = 0 := by
  let x := F (0,z)
  let c := chartAt (Model X) x
  let t := trivializationAt (Model X) (Tangent X) x
  have hx : F (0,z) ∈ c.source := mem_chart_source (Model X) x
  have hnear := (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hF
  have hxnear := hF.continuousAt.eventually (c.open_source.mem_nhds hx)
  have hk : S.projectedInChart x F (0,1) (0,z) = 0 := by
    apply ExceptionalTangency.kills_second_of_wedge n hh hu
      (S.projectedInChart x F (1,0)) (S.projectedInChart x F (0,1))
      (S.projectedInChart_analytic (1,0) hF hx).continuousAt
      (S.projectedInChart_analytic (0,1) hF hx).continuousAt
    filter_upwards [hW,hnear,hxnear] with w hw hFw hxw
    exact (S.chart_wedge_iff hFw hxw).mp hw (1,0) (0,1)
  rw [S.projectedInChart_eq (0,1) hF hx] at hk
  have H := congrArg (t.symmL ℂ (F (0,z))) hk
  change t.symmL ℂ (F (0,z)) (t.continuousLinearMapAt ℂ (F (0,z)) _) = _ at H
  simpa only [t.symmL_continuousLinearMapAt hx,map_zero] using H

 

theorem constant_exceptional {F : ℂ × ℂ → X.Carrier} {h k : ℂ × ℂ → ℂ}
    (n m : ℕ) (hF : ∀ z : ℂ, ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F (0,z))
    (hh : ∀ z : ℂ, AnalyticAt ℂ h (0,z)) (hk : ∀ z : ℂ, AnalyticAt ℂ k (0,z))
    (hB : Set.Finite {z : ℂ | h (0,z) = 0 ∨ k (0,z) = 0})
    (hW : ∀ z : ℂ, ∀ᶠ w in 𝓝 (0,z), S.WedgeAt F (fun w : ℂ × ℂ => w.1^(n+1)*h w) w)
    (hV : ∀ z : ℂ, ∀ᶠ w in 𝓝 (0,z), S.swap.WedgeAt F (fun w : ℂ × ℂ => w.1^(m+1)*k w) w)
    (z w : ℂ) : F (0,z) = F (0,w) := by
  let i : ℂ → ℂ × ℂ := fun z => (0,z)
  have hi : ContDiff ℂ ω i := contDiff_const.prodMk contDiff_id
  have hc : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω (F ∘ i) :=
    fun z => (hF z).comp z hi.contMDiff.contMDiffAt
  apply ComplexManifold.curve_eq_of_mfderiv_zero_off_finite hB hc _ z w
  intro a ha
  have hu : h (0,a) ≠ 0 := fun h => ha (Or.inl h)
  have ku : k (0,a) ≠ 0 := fun h => ha (Or.inr h)
  have hp := S.kills_exceptional_of_wedge n (hF a) (hh a) hu (hW a)
  have hq := S.swap.kills_exceptional_of_wedge m (hF a) (hk a) ku (hV a)
  have hd : mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F (0,a) (0,1) = 0 := by
    change _ - S.projector _ _ = 0 at hq
    rw [hp,sub_zero] at hq
    exact hq
  rw [mfderiv_comp a ((hF a).mdifferentiableAt (by simp)) (hi.contMDiff.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv]
  have hid : fderiv ℂ i a = (ContinuousLinearMap.inr ℂ ℂ ℂ) := by
    exact ((hasFDerivAt_const (0 : ℂ) a).prodMk (hasFDerivAt_id a)).fderiv
  rw [hid]
  apply ContinuousLinearMap.ext
  intro v
  change ℂ at v
  have hv : (0,v) = v • ((0,1) : ℂ × ℂ) := by simp
  let d : (ℂ × ℂ) →L[ℂ] Tangent X (F (0,a)) := mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F (0,a)
  have hd' : d (0,1) = 0 := hd
  change d (0,v) = 0
  rw [hv,map_smul,hd',smul_zero]

end SplitTangent.TangentSplitting

open Filter Topology Metric Set

 

open MvPowerSeries
namespace SplitTangent.FormalBlowup

abbrev D := MvPowerSeries (Fin 2) ℂ
abbrev x : D := X 0
abbrev y : D := X 1

lemma x_ne_zero : (x : D) ≠ 0 := by
  intro h
  have H := congrArg (coeff (Finsupp.single 0 1)) h
  simp [x] at H

 
def highOrder (k : ℕ) : Ideal D where
  carrier := {f | (k : ℕ∞) ≤ f.order}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    exact (le_min hf hg).trans min_order_le_add
  smul_mem' := by
    intro f g hg
    change (k : ℕ∞) ≤ (f * g).order
    exact (hg.trans (le_add_left le_rfl)).trans le_order_mul

lemma mem_highOrder {k : ℕ} {f : D} : f ∈ highOrder k ↔
    ∀ d : Fin 2 →₀ ℕ, d 0 + d 1 < k → coeff d f = 0 := by
  change ((k : ℕ∞) ≤ f.order) ↔ _
  constructor
  · intro hf d hd
    apply coeff_of_lt_order
    have hd' : (d.degree : ℕ∞) < k := by
      simpa [Finsupp.degree_eq_sum,Fin.sum_univ_two] using (show ((d 0 + d 1 : ℕ) : ℕ∞) < k by exact_mod_cast hd)
    exact hd'.trans_le hf
  · intro hf
    apply nat_le_order
    intro d hd
    apply hf d
    simpa [Finsupp.degree_eq_sum,Fin.sum_univ_two] using hd

lemma highOrder_one {order : ℕ} : (1 : D) ∉ highOrder (order+1) := by
  intro h
  have H := mem_highOrder.mp h 0 (by simp)
  simp at H

 

def coordinateSubstitution : Fin 2 → D := ![x,x*y]

lemma coordinateSubstitution_hasSubst : HasSubst coordinateSubstitution := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i <;> simp [coordinateSubstitution,x,y]

def blowup : D →ₐ[ℂ] D := substAlgHom coordinateSubstitution_hasSubst

lemma substituted_monomial (d : Fin 2 →₀ ℕ) :
    d.prod (fun i n => coordinateSubstitution i ^ n) = x ^ (d 0 + d 1) * y ^ d 1 := by
  rw [Finsupp.prod_fintype _ _ (by simp),Fin.prod_univ_two]
  simp only [coordinateSubstitution,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,mul_pow,pow_add]
  ring

lemma exceptional_pow_dvd {k : ℕ} {f : D} (hf : f ∈ highOrder k) : x ^ k ∣ blowup f := by
  apply X_pow_dvd_iff.mpr
  intro e he
  rw [blowup,substAlgHom_apply]
  rw [coeff_subst coordinateSubstitution_hasSubst]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  rw [substituted_monomial]
  by_cases hd : d 0 + d 1 < k
  · rw [(mem_highOrder.mp hf) d hd,zero_smul]
  · have hx : (x : D) ^ (d 0 + d 1) ∣ x ^ (d 0 + d 1) * y ^ d 1 := dvd_mul_right _ _
    have hc := X_pow_dvd_iff.mp hx e (he.trans_le (Nat.le_of_not_gt hd))
    rw [hc,smul_zero]

 
def transform (k : ℕ) : (highOrder k).restrictScalars ℂ →ₗ[ℂ] D where
  toFun f := (exceptional_pow_dvd f.property).choose
  map_add' f g := by
    apply mul_left_cancel₀ (pow_ne_zero _ x_ne_zero)
    rw [← (exceptional_pow_dvd (f+g).property).choose_spec,mul_add,
      ← (exceptional_pow_dvd f.property).choose_spec,
      ← (exceptional_pow_dvd g.property).choose_spec]
    exact map_add blowup (f : D) (g : D)
  map_smul' c f := by
    apply mul_left_cancel₀ (pow_ne_zero _ x_ne_zero)
    rw [mul_smul_comm,← (exceptional_pow_dvd (c • f).property).choose_spec,
      ← (exceptional_pow_dvd f.property).choose_spec]
    exact map_smul blowup c (f : D)

lemma exceptional_mul_transform (k : ℕ) (f : (highOrder k).restrictScalars ℂ) :
    x ^ k * transform k f = blowup f := (exceptional_pow_dvd f.property).choose_spec.symm

lemma transform_mul (k : ℕ) (q : D) (f : (highOrder k).restrictScalars ℂ) :
    transform k ⟨q*f, (highOrder k).mul_mem_left q f.property⟩ = blowup q * transform k f := by
  apply mul_left_cancel₀ (pow_ne_zero _ x_ne_zero)
  rw [exceptional_mul_transform]
  calc blowup (q * f) = blowup q * blowup f := map_mul blowup _ _
    _ = x^k * (blowup q * transform k f) := by rw [← exceptional_mul_transform]; ring

def exp (a b : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 b

@[simp] lemma exp_zero (a b : ℕ) : exp a b 0 = a := by simp [exp]
@[simp] lemma exp_one (a b : ℕ) : exp a b 1 = b := by simp [exp]

lemma exp_eta (d : Fin 2 →₀ ℕ) : exp (d 0) (d 1) = d := by
  ext i; fin_cases i <;> simp

lemma variable_monomial (a b : ℕ) : (x : D)^a * y^b = monomial (exp a b) 1 := by
  rw [X_pow_eq,X_pow_eq,monomial_mul_monomial]
  simp [exp]

lemma coeff_blowup (f : D) (a b : ℕ) :
    coeff (exp (a+b) b) (blowup f) = coeff (exp a b) f := by
  rw [blowup,substAlgHom_apply,coeff_subst coordinateSubstitution_hasSubst]
  rw [finsum_eq_single _ (exp a b)]
  · rw [substituted_monomial]
    simp only [exp_zero,exp_one]
    rw [variable_monomial,coeff_monomial,ite_eq_left rfl,smul_eq_mul,mul_one]
  · intro d hd
    rw [substituted_monomial,variable_monomial,coeff_monomial,ite_eq_right,smul_zero]
    intro H
    have H0 := congrArg (fun d : Fin 2 →₀ ℕ => d 0) H
    have H1 := congrArg (fun d : Fin 2 →₀ ℕ => d 1) H
    simp only [exp_zero,exp_one] at H0 H1
    have H2 : d 0 = a := by omega
    exact hd (by rw [← exp_eta d,H2,← H1])

lemma coeff_x_pow_mul (f : D) (a b k : ℕ) :
    coeff (exp (a+k) b) (x^k * f) = coeff (exp a b) f := by
  rw [X_pow_eq,coeff_monomial_mul,ite_eq_left,one_mul]
  · have H : exp (a+k) b - Finsupp.single 0 k = exp a b := by
      ext i
      fin_cases i <;> simp [exp]
    rw [H]
  · intro i
    fin_cases i <;> simp [exp]

 

lemma coeff_transform_initial (k a b : ℕ) (hab : a+b=k)
    (f : (highOrder k).restrictScalars ℂ) :
    coeff (exp 0 b) (transform k f) = coeff (exp a b) f := by
  have H := congrArg (coeff (exp k b)) (exceptional_mul_transform k f)
  have hx : exp k b = exp (0+k) b := by simp
  rw [hx,coeff_x_pow_mul] at H
  have Hb : coeff (exp (0+k) b) (blowup (f : D)) = coeff (exp a b) f := by
    simpa only [hab,zero_add] using coeff_blowup (f : D) a b
  exact H.trans Hb

 
lemma monomial_mem_highOrder (k a b : ℕ) (h : k ≤ a+b) :
    (x:D)^a*y^b ∈ highOrder k := by
  change (k : ℕ∞) ≤ _
  rw [variable_monomial,order_monomial_of_ne_zero one_ne_zero]
  exact_mod_cast (show k ≤ (exp a b).degree by simpa [Finsupp.degree_eq_sum,Fin.sum_univ_two] using h)

@[simp] lemma blowup_x : blowup x = x := by
  change substAlgHom coordinateSubstitution_hasSubst (X 0) = _
  rw [substAlgHom_X]
  rfl

@[simp] lemma blowup_y : blowup y = x*y := by
  change substAlgHom coordinateSubstitution_hasSubst (X 1) = _
  rw [substAlgHom_X]
  rfl

lemma transform_monomial (k a b : ℕ) (h : k ≤ a+b) :
    transform k ⟨x^a*y^b,monomial_mem_highOrder k a b h⟩ = x^(a+b-k)*y^b := by
  apply mul_left_cancel₀ (pow_ne_zero _ x_ne_zero)
  rw [exceptional_mul_transform,map_mul,map_pow,map_pow,blowup_x,blowup_y,mul_pow]
  change x^a * (x^b*y^b) = x^k*(x^(a+b-k)*y^b)
  rw [← mul_assoc,← pow_add,← mul_assoc,← pow_add,Nat.add_sub_of_le h]

 
def yEmbedding : Unit ↪ Fin 2 := ⟨fun _ => 1,Function.injective_of_subsingleton _⟩
def row : D →ₐ[ℂ] PowerSeries ℂ := killCompl yEmbedding
def insertRow : PowerSeries ℂ →ₐ[ℂ] D := rename yEmbedding

lemma row_coeff (f : D) (b : ℕ) : PowerSeries.coeff b (row f) = coeff (exp 0 b) f := by
  change coeff (Finsupp.single () b) (killCompl yEmbedding f) = _
  rw [coeff_killCompl,Finsupp.embDomain_single]
  simp [exp,yEmbedding]

lemma insertRow_coeff (g : PowerSeries ℂ) (b : ℕ) :
    coeff (exp 0 b) (insertRow g) = PowerSeries.coeff b g := by
  have H := coeff_embDomain_rename yEmbedding g (Finsupp.single () b)
  simpa [Finsupp.embDomain_single,exp,yEmbedding,insertRow,PowerSeries.coeff] using H

@[simp] lemma insertRow_X : insertRow PowerSeries.X = y := by
  exact rename_X yEmbedding ()

lemma self_sub_insertRow (f : D) : x ∣ f - insertRow (row f) := by
  rw [← pow_one (x : D)]
  apply X_pow_dvd_iff.mpr
  intro d hd
  have hd0 : d 0 = 0 := by omega
  have he : d = exp 0 (d 1) := by rw [← hd0,exp_eta]
  rw [map_sub,he,insertRow_coeff,row_coeff,sub_self]

lemma row_initial_order_le (k a b : ℕ) (hab : a+b=k)
    (f : (highOrder k).restrictScalars ℂ) (hf : coeff (exp a b) (f : D) ≠ 0) :
    (row (transform k f)).order.toNat ≤ k ∧ row (transform k f) ≠ 0 := by
  have hc : PowerSeries.coeff b (row (transform k f)) ≠ 0 := by
    rw [row_coeff,coeff_transform_initial k a b hab]
    exact hf
  have hne : row (transform k f) ≠ 0 := by intro h; simp [h] at hc
  refine ⟨?_,hne⟩
  have hle := PowerSeries.order_le b hc
  have hb := ENat.toNat_le_toNat hle (by simp)
  simp only [ENat.toNat_natCast] at hb
  omega

lemma initial_factor (f : D) (hf : row f ≠ 0) :
    ∃ v : D, IsUnit v ∧ x ∣ f - y^(row f).order.toNat * v := by
  refine ⟨insertRow (PowerSeries.divXPowOrder (row f)),?_,?_⟩
  · apply IsUnit.map insertRow
    rw [PowerSeries.isUnit_iff_constantCoeff,isUnit_iff_ne_zero]
    exact mt PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.mp hf
  · have H := congrArg insertRow (PowerSeries.X_pow_order_mul_divXPowOrder (f := row f))
    simp only [map_mul,map_pow,insertRow_X] at H
    rw [H]
    exact self_sub_insertRow f

 

lemma submodule_eq_top_of_nilpotent {A : Type*} [CommRing A] [Algebra ℂ A]
    (V : Submodule ℂ A) (t : A) (ht : IsNilpotent t)
    (hstable : ∀ v ∈ V, t*v ∈ V)
    (hmod : ∀ a : A, ∃ v ∈ V, ∃ w : A, a = v+t*w) : V = ⊤ := by
  have hp : ∀ n : ℕ, ∀ v ∈ V, t^n*v ∈ V := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro v hv
      simpa only [pow_succ',mul_assoc] using hstable (t^n*v) (ih v hv)
  have hl : ∀ n : ℕ, ∀ a : A, ∃ v ∈ V, ∃ w : A, a = v+t^n*w := by
    intro n
    induction n with
    | zero => intro a; exact ⟨0,V.zero_mem,a,by simp⟩
    | succ n ih =>
      intro a
      obtain ⟨v,hv,w,hw⟩ := ih a
      obtain ⟨v',hv',w',hw'⟩ := hmod w
      refine ⟨v+t^n*v',V.add_mem hv (hp n v' hv'),w',?_⟩
      rw [hw,hw',pow_succ]
      ring
  obtain ⟨n,hn⟩ := ht
  apply top_unique
  intro a ha
  obtain ⟨v,hv,w,hw⟩ := hl n a
  rw [hw]
  simpa [hn] using hv

lemma exceptional_power_in_sup (J : Ideal D) (f : D) (hf : f ∈ J) (hr : row f ≠ 0) :
    y^(row f).order.toNat ∈ J ⊔ Ideal.span {x} := by
  obtain ⟨v,hv,hd⟩ := initial_factor f hr
  let K : Ideal D := J ⊔ Ideal.span {x}
  have hF : f ∈ K := (show J ≤ K from le_sup_left) hf
  have hD : f-y^(row f).order.toNat*v ∈ K :=
    (show Ideal.span {x} ≤ K from le_sup_right) (Ideal.mem_span_singleton.mpr hd)
  have hM : y^(row f).order.toNat*v ∈ K := by
    convert K.sub_mem hF hD using 1; ring
  obtain ⟨u,rfl⟩ := hv
  have H := K.mul_mem_right (↑u⁻¹) hM
  simpa only [mul_assoc,Units.val_inv_eq_inv_val,Units.mul_inv, mul_one] using H

 

lemma low_remainder (J : Ideal D) (q : ℕ) (hyq : y^q ∈ J ⊔ Ideal.span {x})
    (f : D) : f - insertRow ((row f).trunc q : PowerSeries ℂ) ∈ J ⊔ Ideal.span {x} := by
  let K : Ideal D := J ⊔ Ideal.span {x}
  have h1 : f-insertRow (row f) ∈ K := (show Ideal.span {x} ≤ K from le_sup_right)
    (Ideal.mem_span_singleton.mpr (self_sub_insertRow f))
  have H := congrArg insertRow (PowerSeries.eq_X_pow_mul_shift_add_trunc q (row f))
  simp only [map_add,map_mul,map_pow,insertRow_X] at H
  have h2 : insertRow (row f)-insertRow ((row f).trunc q : PowerSeries ℂ) ∈ K := by
    rw [H,add_sub_cancel_right]
    exact K.mul_mem_right _ hyq
  convert K.add_mem h1 h2 using 1; ring

 

def transformIdeal (I : Ideal D) (k : ℕ) (hI : I ≤ highOrder k) : Ideal D :=
  Ideal.span (Set.range (fun f : I => transform k ⟨f,hI f.property⟩))

lemma transform_mem (I : Ideal D) (k : ℕ) (hI : I ≤ highOrder k) (f : I) :
    transform k ⟨f,hI f.property⟩ ∈ transformIdeal I k hI := Ideal.subset_span ⟨f,rfl⟩

 

lemma exists_x_pow_mem (I : Ideal D) [FiniteDimensional ℂ (D ⧸ I)] : ∃ n : ℕ, x^n ∈ I := by
  let : IsArtinianRing (D ⧸ I) := IsArtinianRing.of_finite ℂ (D ⧸ I)
  obtain ⟨n,hn⟩ := IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I
  refine ⟨n,hn (Ideal.pow_mem_pow ?_ n)⟩
  rw [IsLocalRing.mem_maximalIdeal,mem_nonunits_iff,MvPowerSeries.isUnit_iff_constantCoeff]
  simp [x]

lemma exists_x_pow_mem_transform (I : Ideal D) (k : ℕ) (hI : I ≤ highOrder k)
    [FiniteDimensional ℂ (D ⧸ I)] : ∃ n : ℕ, x^n ∈ transformIdeal I k hI := by
  obtain ⟨n,hn⟩ := exists_x_pow_mem I
  have hkn : k ≤ n := by
    by_contra h
    have H := mem_highOrder.mp (hI hn) (exp n 0) (by simpa using Nat.lt_of_not_ge h)
    simp [exp,X_pow_eq] at H
  have H := transform_mem I k hI ⟨x^n,hn⟩
  refine ⟨n-k,?_⟩
  have ht : transform k ⟨x^n,hI hn⟩ = x^(n-k) := by
    simpa only [pow_zero,mul_one,Nat.add_zero] using transform_monomial k n 0 (by simpa using hkn)
  rw [ht] at H
  exact H

lemma insertRow_trunc (g : PowerSeries ℂ) (q : ℕ) :
    insertRow (g.trunc q : PowerSeries ℂ) =
      ∑ b ∈ Finset.range q, (PowerSeries.coeff b g) • y^b := by
  rw [PowerSeries.trunc_apply,Nat.Ico_zero_eq_range]
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum, map_sum]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_monomial]
  apply Finset.sum_congr rfl
  intro b hb
  rw [PowerSeries.monomial_eq_C_mul_X_pow,map_mul,map_pow,insertRow_X]
  change (MvPowerSeries.rename yEmbedding (PowerSeries.C _)) * y^b = _
  rw [PowerSeries.C_apply,rename_C,smul_eq_C_mul]

 

lemma quotient_transform_surjective (J : Ideal D) (k : ℕ)
    (hnil : ∃ n : ℕ, x^n ∈ J)
    (q : ℕ) (hq : q ≤ k) (hyq : y^q ∈ J ⊔ Ideal.span {x}) :
    Function.Surjective ((Ideal.Quotient.mkₐ ℂ J).toLinearMap.comp (transform k)) := by
  let Q := Ideal.Quotient.mkₐ ℂ J
  let T := Q.toLinearMap.comp (transform k)
  let V := T.range
  have hY : ∀ b : ℕ, b ≤ k → Q (y^b) ∈ V := by
    intro b hb
    have hab : k ≤ k-b+b := by omega
    refine ⟨⟨x^(k-b)*y^b,monomial_mem_highOrder k (k-b) b hab⟩,?_⟩
    change Q (transform k _) = Q (y^b)
    rw [transform_monomial k (k-b) b hab]
    congr 1
    have he : k-b+b-k=0 := by omega
    simp [he]
  have hstable : ∀ v ∈ V, Q x * v ∈ V := by
    rintro v ⟨f,rfl⟩
    refine ⟨⟨x*f,(highOrder k).mul_mem_left x f.property⟩,?_⟩
    change Q (transform k _) = Q x * Q (transform k f)
    rw [transform_mul,blowup_x,map_mul]
  have hpoly (f : D) : Q (insertRow ((row f).trunc q : PowerSeries ℂ)) ∈ V := by
    rw [insertRow_trunc,map_sum]
    apply V.sum_mem
    intro b hb
    rw [map_smul]
    exact V.smul_mem _ (hY b ((Finset.mem_range.mp hb).le.trans hq))
  have hmod : ∀ a : D ⧸ J, ∃ v ∈ V, ∃ w : D ⧸ J, a = v+Q x*w := by
    intro a
    obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective a
    have H := low_remainder J q hyq f
    obtain ⟨j,hj,z,hz,he⟩ := Submodule.mem_sup.mp H
    obtain ⟨w,rfl⟩ := Ideal.mem_span_singleton.mp hz
    have heq := congrArg Q he
    have hjQ : Q j = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hj
    simp only [map_add,map_sub,map_mul,hjQ,zero_add] at heq
    refine ⟨Q (insertRow ((row f).trunc q : PowerSeries ℂ)),hpoly f,Q w,?_⟩
    change Q f = _
    linear_combination -heq
  have hnilQ : IsNilpotent (Q x) := by
    obtain ⟨n,hn⟩ := hnil
    refine ⟨n,?_⟩
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hn
  exact LinearMap.range_eq_top.mp (submodule_eq_top_of_nilpotent V (Q x) hnilQ hstable hmod)

lemma strict_transform_surjective (I : Ideal D) (k : ℕ) (hI : I ≤ highOrder k)
    [FiniteDimensional ℂ (D ⧸ I)]
    (f : I) (a b : ℕ) (hab : a+b=k) (hf : coeff (exp a b) (f : D) ≠ 0) :
    Function.Surjective ((Ideal.Quotient.mkₐ ℂ (transformIdeal I k hI)).toLinearMap.comp
      (transform k)) := by
  let f' : (highOrder k).restrictScalars ℂ := ⟨f,hI f.property⟩
  obtain ⟨hq,hr⟩ := row_initial_order_le k a b hab f' hf
  exact quotient_transform_surjective (transformIdeal I k hI) k
    (exists_x_pow_mem_transform I k hI) _ hq
    (exceptional_power_in_sup (transformIdeal I k hI) (transform k f')
      (transform_mem I k hI f) hr)

 

theorem finite_colength_strict_drop (I : Ideal D) (k : ℕ) (hk : 0 < k)
    (hI : I ≤ highOrder k) [FiniteDimensional ℂ (D ⧸ I)]
    (f : I) (a b : ℕ) (hab : a+b=k) (hf : coeff (exp a b) (f : D) ≠ 0) :
    FiniteDimensional ℂ (D ⧸ transformIdeal I k hI) ∧
      Module.finrank ℂ (D ⧸ transformIdeal I k hI) < Module.finrank ℂ (D ⧸ I) := by
  let M := (highOrder k).restrictScalars ℂ
  let L := (Ideal.Quotient.mkₐ ℂ I).toLinearMap.comp M.subtype
  let T := (Ideal.Quotient.mkₐ ℂ (transformIdeal I k hI)).toLinearMap.comp (transform k)
  have hker : L.ker ≤ T.ker := by
    intro g hg
    have hgI : (g : D) ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hg
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (transform_mem I k hI ⟨g,hgI⟩)
  let F := L.ker.liftQ T hker
  have hF : Function.Surjective F := by
    intro z
    obtain ⟨g,hg⟩ := strict_transform_surjective I k hI f a b hab hf z
    exact ⟨Submodule.Quotient.mk g,hg⟩
  let : FiniteDimensional ℂ (M ⧸ L.ker) := L.quotKerEquivRange.symm.finiteDimensional
  have : FiniteDimensional ℂ (D ⧸ transformIdeal I k hI) := Module.Finite.of_surjective F hF
  refine ⟨inferInstance,?_⟩
  have hproper : L.range < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    have hr : (Ideal.Quotient.mkₐ ℂ I) 1 ∈ L.range := by rw [htop]; trivial
    obtain ⟨g,hg⟩ := hr
    have hd : (g : D)-1 ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change (Ideal.Quotient.mkₐ ℂ I) ((g : D)-1) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hg
    have hone : (1 : D) ∈ highOrder k := by
      have hh := (highOrder k).sub_mem g.property (hI hd)
      simpa using hh
    have H := mem_highOrder.mp hone 0 (by simpa using hk)
    simp at H
  calc
    Module.finrank ℂ (D ⧸ transformIdeal I k hI) ≤ Module.finrank ℂ (M ⧸ L.ker) :=
      LinearMap.finrank_le_finrank_of_surjective hF
    _ = Module.finrank ℂ L.range := LinearEquiv.finrank_eq L.quotKerEquivRange
    _ < Module.finrank ℂ (D ⧸ I) := Submodule.finrank_lt hproper.ne

lemma transform_of_span_mem (k : ℕ) (S : Set D) (hI : Ideal.span S ≤ highOrder k)
    (J : Ideal D) (hS : ∀ f (hf : f ∈ S), transform k ⟨f,hI (Ideal.subset_span hf)⟩ ∈ J)
    (f : D) (hf : f ∈ Ideal.span S) : transform k ⟨f,hI hf⟩ ∈ J := by
  refine Submodule.span_induction (p := fun f hf => transform k ⟨f,hI hf⟩ ∈ J)
    hS ?_ ?_ ?_ hf
  · change transform k 0 ∈ J
    rw [map_zero]
    exact J.zero_mem
  · intro f g hf hg hft hgt
    have he := (transform k).map_add (⟨f,hI hf⟩ : (highOrder k).restrictScalars ℂ) ⟨g,hI hg⟩
    exact he.symm ▸ J.add_mem hft hgt
  · intro a f hf hft
    have he := transform_mul k a (⟨f,hI hf⟩ : (highOrder k).restrictScalars ℂ)
    exact he.symm ▸ J.mul_mem_left (blowup a) hft

 

lemma transformIdeal_span (k : ℕ) (S : Set D) (hS : S ⊆ highOrder k) :
    transformIdeal (Ideal.span S) k (Ideal.span_le.mpr hS) =
      Ideal.span (Set.range (fun f : S => transform k ⟨f,hS f.property⟩)) := by
  let hI : Ideal.span S ≤ highOrder k := Ideal.span_le.mpr hS
  let J := Ideal.span (Set.range (fun f : S => transform k ⟨f,hS f.property⟩))
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨f,rfl⟩
    apply transform_of_span_mem k S hI J ?_ f f.property
    intro g hg
    exact Ideal.subset_span ⟨⟨g,hg⟩,rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨f,rfl⟩
    exact transform_mem (Ideal.span S) k hI ⟨f,Ideal.subset_span f.property⟩

 

lemma exists_minimal_order (I : Ideal D) (hproper : I ≠ ⊤)
    [FiniteDimensional ℂ (D ⧸ I)] :
    ∃ k : ℕ, 0 < k ∧ I ≤ highOrder k ∧
      ∃ f : I, ∃ a b : ℕ, a+b=k ∧ coeff (exp a b) (f : D) ≠ 0 := by
  classical
  let P : ℕ → Prop := fun n => ∃ f : I, ∃ a b : ℕ, a+b=n ∧ coeff (exp a b) (f : D) ≠ 0
  have hex : ∃ n, P n := by
    obtain ⟨n,hn⟩ := exists_x_pow_mem I
    refine ⟨n,⟨x^n,hn⟩,n,0,by omega,?_⟩
    simp [exp,X_pow_eq]
  let k := Nat.find hex
  obtain ⟨f,a,b,hab,hf⟩ := Nat.find_spec hex
  have hI : I ≤ highOrder k := by
    intro g hg
    apply mem_highOrder.mpr
    intro d hd
    by_contra hc
    have hc' : coeff (exp (d 0) (d 1)) g ≠ 0 := by simpa only [exp_eta] using hc
    exact Nat.find_min hex hd ⟨⟨g,hg⟩,d 0,d 1,rfl,hc'⟩
  have hk : 0 < k := by
    by_contra hn
    have hk0 : k=0 := by omega
    have ha : a=0 := by omega
    have hb : b=0 := by omega
    have hunit : IsUnit (f : D) := by
      apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
      apply isUnit_iff_ne_zero.mpr
      simpa [ha,hb,exp] using hf
    exact hproper (I.eq_top_of_isUnit_mem f.property hunit)
  exact ⟨k,hk,hI,f,a,b,hab,hf⟩

lemma coeff_blowup_eq_zero (f : D) (a b : ℕ) (hab : a < b) :
    coeff (exp a b) (blowup f) = 0 := by
  rw [blowup,substAlgHom_apply,coeff_subst coordinateSubstitution_hasSubst]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  rw [substituted_monomial,variable_monomial,coeff_monomial,ite_eq_right,smul_zero]
  intro he
  have h0 := congrArg (fun e : Fin 2 →₀ ℕ => e 0) he
  have h1 := congrArg (fun e : Fin 2 →₀ ℕ => e 1) he
  simp only [exp_zero,exp_one] at h0 h1
  omega

lemma row_transform_coeff_eq_zero (k : ℕ) (f : (highOrder k).restrictScalars ℂ)
    (b : ℕ) (hb : k < b) : PowerSeries.coeff b (row (transform k f)) = 0 := by
  rw [row_coeff]
  have H := congrArg (coeff (exp k b)) (exceptional_mul_transform k f)
  have hx : exp k b = exp (0+k) b := by simp
  rw [hx,coeff_x_pow_mul] at H
  exact H.trans (coeff_blowup_eq_zero (f : D) (0+k) b (by simpa using hb))

 

def initialPolynomial (k : ℕ) (f : (highOrder k).restrictScalars ℂ) : Polynomial ℂ :=
  (row (transform k f)).trunc (k+1)

lemma initialPolynomial_coe (k : ℕ) (f : (highOrder k).restrictScalars ℂ) :
    (initialPolynomial k f : PowerSeries ℂ) = row (transform k f) := by
  ext b
  rw [Polynomial.coeff_coe,initialPolynomial,PowerSeries.coeff_trunc]
  split_ifs with hb
  · rfl
  · exact (row_transform_coeff_eq_zero k f b (by omega)).symm

lemma initialPolynomial_natDegree_le (k : ℕ) (f : (highOrder k).restrictScalars ℂ) :
    (initialPolynomial k f).natDegree ≤ k :=
  Nat.le_of_lt_succ (PowerSeries.natDegree_trunc_lt _ k)

lemma initialPolynomial_ne_zero (k a b : ℕ) (hab : a+b=k)
    (f : (highOrder k).restrictScalars ℂ) (hf : coeff (exp a b) (f : D) ≠ 0) :
    initialPolynomial k f ≠ 0 := by
  intro h
  have H := row_initial_order_le k a b hab f hf
  have hc := initialPolynomial_coe k f
  rw [h,Polynomial.coe_zero] at hc
  exact H.2 hc.symm

 

lemma finite_exceptional_base_set (k : ℕ) {ι : Type*}
    (f : ι → (highOrder k).restrictScalars ℂ) (i : ι)
    (a b : ℕ) (hab : a+b=k) (hf : coeff (exp a b) (f i : D) ≠ 0) :
    {z : ℂ | ∀ j, (initialPolynomial k (f j)).eval z = 0}.Finite := by
  apply (Polynomial.finite_setOfPred_isRoot (initialPolynomial_ne_zero k a b hab (f i) hf)).subset
  intro z hz
  exact hz i

 

abbrev B := MvPolynomial (Fin 2) ℂ

def polynomialTransform (k : ℕ) (p : B) : B :=
  ∑ d ∈ p.support, MvPolynomial.monomial (exp (d 0+d 1-k) (d 1)) (p.coeff d)

lemma blowup_monomial (d : Fin 2 →₀ ℕ) (c : ℂ) :
    blowup (monomial d c) = monomial (exp (d 0+d 1) (d 1)) c := by
  rw [blowup,substAlgHom_apply,subst_monomial coordinateSubstitution_hasSubst,
    substituted_monomial,← Algebra.smul_def,variable_monomial,← map_smul,smul_eq_mul,mul_one]

lemma polynomialTransform_factor (k : ℕ) (p : B) (hp : (p : D) ∈ highOrder k) :
    x^k * (polynomialTransform k p : D) = blowup (p : D) := by
  rw [polynomialTransform,← MvPolynomial.coeToMvPowerSeries.ringHom_apply,map_sum,Finset.mul_sum]
  conv_rhs => rw [MvPolynomial.as_sum p]
  rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply,MvPolynomial.coe_monomial]
  have hk : k ≤ d 0+d 1 := by
    by_contra h
    have hc := mem_highOrder.mp hp d (by omega)
    rw [MvPolynomial.coeff_coe] at hc
    exact MvPolynomial.mem_support_iff.mp hd hc
  rw [X_pow_eq,monomial_mul_monomial,one_mul,blowup_monomial]
  have he : Finsupp.single 0 k + exp (d 0+d 1-k) (d 1) = exp (d 0+d 1) (d 1) := by
    ext i
    fin_cases i <;> simp [exp]
    omega
  rw [he]

lemma transform_polynomial (k : ℕ) (p : B) (hp : (p : D) ∈ highOrder k) :
    transform k ⟨p,hp⟩ = (polynomialTransform k p : D) := by
  apply mul_left_cancel₀ (pow_ne_zero _ x_ne_zero)
  rw [exceptional_mul_transform,polynomialTransform_factor k p hp]

 

lemma mem_ideal_of_rectangle_zero (I : Ideal D) (A B : ℕ)
    (hx : x^A ∈ I) (hy : y^B ∈ I) (f : D)
    (hf : ∀ d : Fin 2 →₀ ℕ, d 0 < A → d 1 < B → coeff d f = 0) : f ∈ I := by
  let fX : D := fun d => if A ≤ d 0 then coeff d f else 0
  have hdX : x^A ∣ fX := by
    apply X_pow_dvd_iff.mpr
    intro d hd
    change (if A ≤ d 0 then coeff d f else 0) = 0
    rw [ite_eq_right (not_le.mpr hd)]
  have hdY : y^B ∣ f-fX := by
    apply X_pow_dvd_iff.mpr
    intro d hd
    rw [map_sub]
    change coeff d f - (if A ≤ d 0 then coeff d f else 0) = 0
    by_cases hA : A ≤ d 0
    · rw [ite_eq_left hA,sub_self]
    · rw [ite_eq_right hA,sub_zero]
      exact hf d (Nat.lt_of_not_ge hA) hd
  obtain ⟨g,hg⟩ := hdX
  obtain ⟨h,hh⟩ := hdY
  have hX : fX ∈ I := by rw [hg]; exact I.mul_mem_right g hx
  have hY : f-fX ∈ I := by rw [hh]; exact I.mul_mem_right h hy
  simpa using I.add_mem hY hX

 
def rectangleMap (A B : ℕ) : (Fin A × Fin B → ℂ) →ₗ[ℂ] D :=
  ∑ ab : Fin A × Fin B, (monomial (exp ab.1 ab.2)).comp (LinearMap.proj ab)

lemma rectangleMap_apply (A B : ℕ) (c : Fin A × Fin B → ℂ) :
    rectangleMap A B c = ∑ ab : Fin A × Fin B, monomial (exp ab.1 ab.2) (c ab) := by
  simp [rectangleMap]

lemma rectangleMap_coeff (A B : ℕ) (f : D) (d : Fin 2 →₀ ℕ)
    (hA : d 0 < A) (hB : d 1 < B) :
    coeff d (rectangleMap A B (fun ab => coeff (exp ab.1 ab.2) f)) = coeff d f := by
  classical
  rw [rectangleMap_apply,map_sum]
  let i : Fin A × Fin B := (⟨d 0,hA⟩,⟨d 1,hB⟩)
  rw [Finset.sum_eq_single i]
  · simp [i,exp_eta]
  · intro j hj hji
    rw [coeff_monomial,ite_eq_right]
    intro he
    apply hji
    apply Prod.ext <;> apply Fin.ext
    · have H := congrArg (fun d : Fin 2 →₀ ℕ => d 0) he
      simpa [i] using H.symm
    · have H := congrArg (fun d : Fin 2 →₀ ℕ => d 1) he
      simpa [i] using H.symm
  · simp

 
theorem finite_colength_of_coordinate_powers (I : Ideal D) (A B : ℕ)
    (hx : x^A ∈ I) (hy : y^B ∈ I) : FiniteDimensional ℂ (D ⧸ I) := by
  let T := (Ideal.Quotient.mkₐ ℂ I).toLinearMap.comp (rectangleMap A B)
  apply Module.Finite.of_surjective T
  intro z
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨fun ab => coeff (exp ab.1 ab.2) f,?_⟩
  apply Ideal.Quotient.eq.mpr
  apply mem_ideal_of_rectangle_zero I A B hx hy
  intro d hdA hdB
  rw [map_sub,rectangleMap_coeff A B f d hdA hdB,sub_self]


open MvPowerSeries

 

def shearCoordinates (c : ℂ) : Fin 2 → D := ![x,y + C c * x]

lemma shearCoordinates_hasSubst (c : ℂ) : HasSubst (shearCoordinates c) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i <;> simp [shearCoordinates,x,y]

def shear (c : ℂ) : D →ₐ[ℂ] D := substAlgHom (shearCoordinates_hasSubst c)

@[simp] lemma shear_x (c : ℂ) : shear c x = x := by
  simpa [shear,shearCoordinates,x] using substAlgHom_X (R := ℂ) (shearCoordinates_hasSubst c) 0

@[simp] lemma shear_y (c : ℂ) : shear c y = y + C c * x := by
  simpa [shear,shearCoordinates,y] using substAlgHom_X (R := ℂ) (shearCoordinates_hasSubst c) 1

@[simp] lemma shear_C (c a : ℂ) : shear c (C a) = C a := by
  simpa only [c_eq_algebraMap] using (shear c).commutes a

lemma shear_neg_shear (c : ℂ) (f : D) : shear (-c) (shear c f) = f := by
  simp only [shear,substAlgHom_apply]
  rw [subst_comp_subst_apply (shearCoordinates_hasSubst c) (shearCoordinates_hasSubst (-c))]
  have H : (fun i => subst (shearCoordinates (-c)) (shearCoordinates c i)) = X := by
    funext i
    rw [← substAlgHom_apply (R := ℂ) (shearCoordinates_hasSubst (-c))]
    change shear (-c) (shearCoordinates c i) = X i
    fin_cases i
    · simp [shearCoordinates,x]
    · change shear (-c) (y + C c * x) = y
      simp only [map_add,map_mul,shear_y,shear_C,shear_x,map_neg]
      change y + -(C c) * x + C c * x = y
      ring
  rw [H,← map_algebraMap_eq_subst_X]
  simp

 

def shearEquiv (c : ℂ) : D ≃ₐ[ℂ] D := AlgEquiv.ofAlgHom (shear c) (shear (-c))
  (by apply AlgHom.ext; intro f
      change shear c (shear (-c) f) = f
      simpa only [neg_neg] using shear_neg_shear (-c) f)
  (by apply AlgHom.ext; intro f; exact shear_neg_shear c f)

lemma order_le_shear (c : ℂ) (f : D) : f.order ≤ (shear c f).order := by
  have h1 : (1 : ℕ∞) ≤ ⨅ i, (shearCoordinates c i).order := by
    apply le_iInf
    intro i
    rw [one_le_order_iff_constCoeff_eq_zero]
    fin_cases i <;> simp [shearCoordinates,x,y]
  calc
    f.order = 1 * f.order := (one_mul _).symm
    _ ≤ (⨅ i, (shearCoordinates c i).order) * f.order := mul_le_mul h1 le_rfl bot_le bot_le
    _ ≤ (shear c f).order := by simpa only [shear,substAlgHom_apply] using le_order_subst (shearCoordinates_hasSubst c) f

lemma order_shear (c : ℂ) (f : D) : (shear c f).order = f.order := by
  apply le_antisymm
  · have H := order_le_shear (-c) (shear c f)
    rwa [shear_neg_shear] at H
  · exact order_le_shear c f

lemma shear_mem_highOrder_iff (c : ℂ) (f : D) (k : ℕ) :
    shear c f ∈ highOrder k ↔ f ∈ highOrder k := by
  change ((k : ℕ∞) ≤ (shear c f).order) ↔ (k : ℕ∞) ≤ f.order
  rw [order_shear]

def shearIdeal (I : Ideal D) (c : ℂ) : Ideal D := I.map (shear c).toRingHom

def shearQuotientEquiv (I : Ideal D) (c : ℂ) :
    (D ⧸ I) ≃ₐ[ℂ] D ⧸ shearIdeal I c :=
  Ideal.quotientEquivAlg I (shearIdeal I c) (shearEquiv c) rfl

lemma shearIdeal_ne_top (I : Ideal D) (hI : I ≠ ⊤) (c : ℂ) : shearIdeal I c ≠ ⊤ := by
  intro h
  apply hI
  exact (Ideal.map_eq_top_of_bijective (shear c).toRingHom (shearEquiv c).bijective).mp h

theorem colength_drop_at_direction (I : Ideal D) (hI : I ≠ ⊤)
    [FiniteDimensional ℂ (D ⧸ I)] (c : ℂ) :
    ∃ k : ℕ, ∃ _ : 0 < k, ∃ hJ : shearIdeal I c ≤ highOrder k,
    FiniteDimensional ℂ (D ⧸ transformIdeal (shearIdeal I c) k hJ) ∧
    Module.finrank ℂ (D ⧸ transformIdeal (shearIdeal I c) k hJ) <
      Module.finrank ℂ (D ⧸ I) := by
  let : FiniteDimensional ℂ (D ⧸ shearIdeal I c) :=
    Module.Finite.of_surjective (shearQuotientEquiv I c).toLinearMap (shearQuotientEquiv I c).surjective
  obtain ⟨k,hk,hJ,f,a,b,hab,hf⟩ := exists_minimal_order (shearIdeal I c) (shearIdeal_ne_top I hI c)
  obtain ⟨hfin,hlt⟩ := finite_colength_strict_drop (shearIdeal I c) k hk hJ f a b hab hf
  refine ⟨k,hk,hJ,hfin,?_⟩
  rw [(shearQuotientEquiv I c).toLinearEquiv.finrank_eq]
  exact hlt

end SplitTangent.FormalBlowup

namespace SplitTangent.PolynomialBlowup
open FormalBlowup

abbrev P := MvPolynomial (Fin 2) ℂ

def embed : P →ₐ[ℂ] D where
  toRingHom := MvPolynomial.coeToMvPowerSeries.ringHom
  commutes' a := by
    change ((MvPolynomial.C a : P) : D) = _
    rw [MvPolynomial.coe_C, ← MvPowerSeries.c_eq_algebraMap]

@[simp] lemma embed_apply (p : P) : embed p = (p : D) := rfl
@[simp] lemma embed_X (i : Fin 2) : embed (MvPolynomial.X i) = MvPowerSeries.X i := by simp
@[simp] lemma embed_C (a : ℂ) : embed (MvPolynomial.C a) = MvPowerSeries.C a := by
  change ((MvPolynomial.C a : P) : D) = _
  exact MvPolynomial.coe_C a

def shift (a : ℂ × ℂ) : P →ₐ[ℂ] P :=
  MvPolynomial.aeval ![MvPolynomial.X 0 + MvPolynomial.C a.1,
    MvPolynomial.X 1 + MvPolynomial.C a.2]

def shear (c : ℂ) : P →ₐ[ℂ] P :=
  MvPolynomial.aeval ![MvPolynomial.X 0,MvPolynomial.X 1 + MvPolynomial.C c * MvPolynomial.X 0]

def blowup : P →ₐ[ℂ] P :=
  MvPolynomial.aeval ![MvPolynomial.X 0,MvPolynomial.X 0 * MvPolynomial.X 1]

@[simp] lemma shift_X₀ (a : ℂ × ℂ) : shift a (MvPolynomial.X 0) = MvPolynomial.X 0 + MvPolynomial.C a.1 := by simp [shift]
@[simp] lemma shift_X₁ (a : ℂ × ℂ) : shift a (MvPolynomial.X 1) = MvPolynomial.X 1 + MvPolynomial.C a.2 := by simp [shift]
@[simp] lemma shear_X₀ (c : ℂ) : shear c (MvPolynomial.X 0) = MvPolynomial.X 0 := by simp [shear]
@[simp] lemma shear_X₁ (c : ℂ) : shear c (MvPolynomial.X 1) = MvPolynomial.X 1 + MvPolynomial.C c * MvPolynomial.X 0 := by simp [shear]
@[simp] lemma blowup_X₀ : blowup (MvPolynomial.X 0) = MvPolynomial.X 0 := by simp [blowup]
@[simp] lemma blowup_X₁ : blowup (MvPolynomial.X 1) = MvPolynomial.X 0 * MvPolynomial.X 1 := by simp [blowup]
@[simp] lemma shift_C (a : ℂ × ℂ) (b : ℂ) : shift a (MvPolynomial.C b) = MvPolynomial.C b := (shift a).commutes b
@[simp] lemma shear_C (c b : ℂ) : shear c (MvPolynomial.C b) = MvPolynomial.C b := (shear c).commutes b
@[simp] lemma blowup_C (c : ℂ) : blowup (MvPolynomial.C c) = MvPolynomial.C c := blowup.commutes c

lemma embed_shear (c : ℂ) (p : P) : embed (shear c p) = FormalBlowup.shear c (embed p) := by
  have h : embed.comp (shear c) = (FormalBlowup.shear c).comp embed := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [x,y]
  exact AlgHom.congr_fun h p

lemma embed_blowup (p : P) : embed (blowup p) = FormalBlowup.blowup (embed p) := by
  have h : embed.comp blowup = FormalBlowup.blowup.comp embed := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply,embed_X]
    rw [FormalBlowup.blowup,MvPowerSeries.substAlgHom_X]
    fin_cases i <;> simp [x,y,FormalBlowup.coordinateSubstitution]
  exact AlgHom.congr_fun h p

lemma polynomial_factor (k : ℕ) (p : P) (hp : embed p ∈ highOrder k) :
    MvPolynomial.X (R := ℂ) (0 : Fin 2)^k * polynomialTransform k p = blowup p := by
  apply MvPolynomial.coe_injective (Fin 2) ℂ
  change embed (_ * _) = embed (blowup p)
  rw [map_mul,map_pow,embed_X,embed_blowup]
  exact polynomialTransform_factor k p hp

lemma shift_blowup (c : ℂ) (p : P) : shift (0,c) (blowup p) = blowup (shear c p) := by
  have h : (shift (0,c)).comp blowup = blowup.comp (shear c) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp
    · simp [mul_add, mul_comm]
  exact AlgHom.congr_fun h p

 

lemma transform_at_direction (c : ℂ) (k : ℕ) (p : P) (hp : embed p ∈ highOrder k) :
    embed (shift (0,c) (polynomialTransform k p)) =
      transform k ⟨FormalBlowup.shear c (embed p),
        (shear_mem_highOrder_iff c (embed p) k).mpr hp⟩ := by
  apply mul_left_cancel₀ (pow_ne_zero k x_ne_zero)
  rw [exceptional_mul_transform]
  have h := congrArg (embed ∘ shift (0,c)) (polynomial_factor k p hp)
  simp only [Function.comp_apply,map_mul,map_pow,shift_X₀,MvPolynomial.C_0,
    add_zero,embed_X,shift_blowup,embed_blowup,embed_shear] at h
  exact h

def baseIdeal {ι : Type*} (p : ι → P) : Ideal D :=
  Ideal.span (Set.range (fun i => embed (p i)))

def transformPreimage (k : ℕ) (J : Ideal D) : Ideal D where
  carrier := {f | ∃ hf : f ∈ highOrder k, transform k ⟨f,hf⟩ ∈ J}
  zero_mem' := ⟨(highOrder k).zero_mem, by
    change transform k 0 ∈ J
    rw [map_zero]
    exact J.zero_mem⟩
  add_mem' := by
    rintro a b ⟨ha,hta⟩ ⟨hb,htb⟩
    refine ⟨(highOrder k).add_mem ha hb,?_⟩
    have h : transform k ⟨a+b,(highOrder k).add_mem ha hb⟩ =
        transform k ⟨a,ha⟩ + transform k ⟨b,hb⟩ := (transform k).map_add ⟨a,ha⟩ ⟨b,hb⟩
    rw [h]
    exact J.add_mem hta htb
  smul_mem' := by
    rintro a b ⟨hb,htb⟩
    refine ⟨(highOrder k).mul_mem_left a hb,?_⟩
    change transform k ⟨a*b,(highOrder k).mul_mem_left a hb⟩ ∈ J
    exact (transform_mul k a ⟨b,hb⟩).symm ▸ J.mul_mem_left _ htb

lemma transform_span {ι : Type*} (f : ι → D) (k : ℕ)
    (hI : Ideal.span (Set.range f) ≤ highOrder k) :
    transformIdeal (Ideal.span (Set.range f)) k hI =
      Ideal.span (Set.range (fun i => transform k ⟨f i,hI (Ideal.subset_span ⟨i,rfl⟩)⟩)) := by
  let J := Ideal.span (Set.range (fun i => transform k ⟨f i,hI (Ideal.subset_span ⟨i,rfl⟩)⟩))
  have hpre : Ideal.span (Set.range f) ≤ transformPreimage k J := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨hI (Ideal.subset_span ⟨i,rfl⟩),Ideal.subset_span ⟨i,rfl⟩⟩
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨g,rfl⟩
    obtain ⟨hg,htg⟩ := hpre g.property
    exact htg
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact transform_mem (Ideal.span (Set.range f)) k hI ⟨f i,Ideal.subset_span ⟨i,rfl⟩⟩

lemma shear_baseIdeal {ι : Type*} (p : ι → P) (c : ℂ) :
    shearIdeal (baseIdeal p) c = baseIdeal (fun i => shear c (p i)) := by
  simp only [shearIdeal,baseIdeal,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  exact (embed_shear c (p i)).symm

lemma baseIdeal_shift_transform {ι : Type*} (p : ι → P) (k : ℕ)
    (hI : baseIdeal p ≤ highOrder k) (c : ℂ)
    (hJ : shearIdeal (baseIdeal p) c ≤ highOrder k) :
    baseIdeal (fun i => shift (0,c) (polynomialTransform k (p i))) =
      transformIdeal (shearIdeal (baseIdeal p) c) k hJ := by
  simp only [shear_baseIdeal] at hJ ⊢
  simp only [baseIdeal]
  rw [transform_span]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  simpa only [embed_shear] using transform_at_direction c k (p i) (hI (Ideal.subset_span ⟨i,rfl⟩))

end SplitTangent.PolynomialBlowup

namespace SplitTangent.FormalBlowup

lemma shearIdeal_le_highOrder (I : Ideal D) (k : ℕ) (hI : I ≤ highOrder k) (c : ℂ) :
    shearIdeal I c ≤ highOrder k := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro f hf
  exact (shear_mem_highOrder_iff c f k).mpr (hI hf)

lemma order_eq_of_initial (k : ℕ) (f : D) (hf : f ∈ highOrder k)
    (a b : ℕ) (hab : a+b=k) (hc : coeff (exp a b) f ≠ 0) : f.order = k := by
  apply le_antisymm
  · have h := order_le hc
    simpa only [Finsupp.degree_eq_sum,Fin.sum_univ_two,exp_zero,exp_one,hab] using h
  · exact hf

lemma initial_of_order_eq (k : ℕ) (f : D) (h : f.order = k) :
    ∃ a b : ℕ, a+b=k ∧ coeff (exp a b) f ≠ 0 := by
  obtain ⟨d,hd,hdeg⟩ := (order_eq_nat.mp h).1
  refine ⟨d 0,d 1,?_,?_⟩
  · simpa [Finsupp.degree_eq_sum,Fin.sum_univ_two] using hdeg
  · simpa only [exp_eta] using hd

 
theorem uniform_colength_drop (I : Ideal D) (k : ℕ) (hk : 0 < k)
    (hI : I ≤ highOrder k) [FiniteDimensional ℂ (D ⧸ I)]
    (f : I) (a b : ℕ) (hab : a+b=k) (hf : coeff (exp a b) (f : D) ≠ 0) (c : ℂ) :
    FiniteDimensional ℂ (D ⧸ transformIdeal (shearIdeal I c) k (shearIdeal_le_highOrder I k hI c)) ∧
    Module.finrank ℂ (D ⧸ transformIdeal (shearIdeal I c) k (shearIdeal_le_highOrder I k hI c)) <
      Module.finrank ℂ (D ⧸ I) := by
  let : FiniteDimensional ℂ (D ⧸ shearIdeal I c) :=
    Module.Finite.of_surjective (shearQuotientEquiv I c).toLinearMap (shearQuotientEquiv I c).surjective
  have hm : shear c (f : D) ∈ shearIdeal I c := Ideal.mem_map_of_mem _ f.property
  have ho : (shear c (f : D)).order = k := by
    rw [order_shear]
    exact order_eq_of_initial k f (hI f.property) a b hab hf
  obtain ⟨a',b',hab',hf'⟩ := initial_of_order_eq k _ ho
  obtain ⟨hfin,hlt⟩ := finite_colength_strict_drop (shearIdeal I c) k hk
    (shearIdeal_le_highOrder I k hI c) ⟨shear c (f : D),hm⟩ a' b' hab' hf'
  refine ⟨hfin,?_⟩
  simpa only [(shearQuotientEquiv I c).toLinearEquiv.finrank_eq] using hlt

def swapCoordinates : Fin 2 → D := ![y,x]
lemma swapCoordinates_hasSubst : HasSubst swapCoordinates := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i <;> simp [swapCoordinates,x,y]
def swap : D →ₐ[ℂ] D := substAlgHom swapCoordinates_hasSubst
@[simp] lemma swap_x : swap x = y := by
  change substAlgHom swapCoordinates_hasSubst (X 0) = _
  rw [substAlgHom_X]
  rfl
@[simp] lemma swap_y : swap y = x := by
  change substAlgHom swapCoordinates_hasSubst (X 1) = _
  rw [substAlgHom_X]
  rfl
@[simp] lemma swap_C (a : ℂ) : swap (C a) = C a := by
  simpa only [c_eq_algebraMap] using swap.commutes a
lemma swap_swap (f : D) : swap (swap f) = f := by
  simp only [swap,substAlgHom_apply]
  rw [subst_comp_subst_apply swapCoordinates_hasSubst swapCoordinates_hasSubst]
  have H : (fun i => subst swapCoordinates (swapCoordinates i)) = X := by
    funext i
    rw [← substAlgHom_apply (R := ℂ) swapCoordinates_hasSubst]
    change swap (swapCoordinates i) = X i
    fin_cases i
    · exact swap_y
    · exact swap_x
  rw [H,← map_algebraMap_eq_subst_X]
  simp

def swapEquiv : D ≃ₐ[ℂ] D := AlgEquiv.ofAlgHom swap swap
  (by apply AlgHom.ext; intro f; exact swap_swap f)
  (by apply AlgHom.ext; intro f; exact swap_swap f)
lemma order_le_swap (f : D) : f.order ≤ (swap f).order := by
  have h1 : (1 : ℕ∞) ≤ ⨅ i, (swapCoordinates i).order := by
    apply le_iInf
    intro i
    rw [one_le_order_iff_constCoeff_eq_zero]
    fin_cases i <;> simp [swapCoordinates,x,y]
  calc
    f.order = 1 * f.order := (one_mul _).symm
    _ ≤ (⨅ i, (swapCoordinates i).order) * f.order := mul_le_mul h1 le_rfl bot_le bot_le
    _ ≤ (swap f).order := by simpa only [swap,substAlgHom_apply] using le_order_subst swapCoordinates_hasSubst f
lemma order_swap (f : D) : (swap f).order = f.order := by
  apply le_antisymm
  · have H := order_le_swap (swap f)
    rwa [swap_swap] at H
  · exact order_le_swap f
lemma swap_mem_highOrder_iff (f : D) (k : ℕ) : swap f ∈ highOrder k ↔ f ∈ highOrder k := by
  change ((k : ℕ∞) ≤ (swap f).order) ↔ (k : ℕ∞) ≤ f.order
  rw [order_swap]
def swapIdeal (I : Ideal D) : Ideal D := I.map swap.toRingHom
def swapQuotientEquiv (I : Ideal D) : (D ⧸ I) ≃ₐ[ℂ] D ⧸ swapIdeal I :=
  Ideal.quotientEquivAlg I (swapIdeal I) swapEquiv rfl
lemma swapIdeal_le_highOrder (I : Ideal D) (k : ℕ) (hI : I ≤ highOrder k) :
    swapIdeal I ≤ highOrder k := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro f hf
  exact (swap_mem_highOrder_iff f k).mpr (hI hf)

end SplitTangent.FormalBlowup

namespace SplitTangent.PolynomialBlowup
section
open FormalBlowup

def swap : P →ₐ[ℂ] P := MvPolynomial.aeval ![MvPolynomial.X 1,MvPolynomial.X 0]
@[simp] lemma swap_X₀ : swap (MvPolynomial.X 0) = MvPolynomial.X 1 := by simp [swap]
@[simp] lemma swap_X₁ : swap (MvPolynomial.X 1) = MvPolynomial.X 0 := by simp [swap]
lemma embed_swap (p : P) : embed (swap p) = FormalBlowup.swap (embed p) := by
  have h : embed.comp swap = FormalBlowup.swap.comp embed := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [x,y]
  exact AlgHom.congr_fun h p
lemma swap_baseIdeal {ι : Type*} (p : ι → P) :
    swapIdeal (baseIdeal p) = baseIdeal (fun i => swap (p i)) := by
  simp only [swapIdeal,baseIdeal,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  exact (embed_swap (p i)).symm

 

def child {ι : Type*} (p : ι → P) (k : ℕ) (c : ℂ) : ι → P :=
  fun i => shift (0,c) (polynomialTransform k (p i))

lemma child_finite_drop {ι : Type*} (p : ι → P) (k : ℕ) (hk : 0 < k)
    (hI : baseIdeal p ≤ highOrder k) [FiniteDimensional ℂ (D ⧸ baseIdeal p)]
    (f : baseIdeal p) (a b : ℕ) (hab : a+b=k) (hf : coeff (exp a b) (f : D) ≠ 0) (c : ℂ) :
    FiniteDimensional ℂ (D ⧸ baseIdeal (child p k c)) ∧
    Module.finrank ℂ (D ⧸ baseIdeal (child p k c)) < Module.finrank ℂ (D ⧸ baseIdeal p) := by
  have he : baseIdeal (child p k c) =
      transformIdeal (shearIdeal (baseIdeal p) c) k (shearIdeal_le_highOrder _ k hI c) :=
    baseIdeal_shift_transform p k hI c (shearIdeal_le_highOrder _ k hI c)
  rw [he]
  exact uniform_colength_drop (baseIdeal p) k hk hI f a b hab hf c

lemma swap_finite {ι : Type*} (p : ι → P) [FiniteDimensional ℂ (D ⧸ baseIdeal p)] :
    FiniteDimensional ℂ (D ⧸ baseIdeal (fun i => swap (p i))) := by
  rw [← swap_baseIdeal]
  exact Module.Finite.of_surjective (swapQuotientEquiv (baseIdeal p)).toLinearMap
    (swapQuotientEquiv (baseIdeal p)).surjective
lemma swap_finrank {ι : Type*} (p : ι → P) :
    Module.finrank ℂ (D ⧸ baseIdeal (fun i => swap (p i))) = Module.finrank ℂ (D ⧸ baseIdeal p) := by
  rw [← swap_baseIdeal]
  exact (swapQuotientEquiv (baseIdeal p)).toLinearEquiv.finrank_eq.symm

lemma swap_child_finite_drop {ι : Type*} (p : ι → P) (k : ℕ) (hk : 0 < k)
    (hI : baseIdeal p ≤ highOrder k) [FiniteDimensional ℂ (D ⧸ baseIdeal p)]
    (f : baseIdeal p) (a b : ℕ) (hab : a+b=k) (hf : coeff (exp a b) (f : D) ≠ 0) (c : ℂ) :
    FiniteDimensional ℂ (D ⧸ baseIdeal (child (fun i => swap (p i)) k c)) ∧
    Module.finrank ℂ (D ⧸ baseIdeal (child (fun i => swap (p i)) k c)) <
      Module.finrank ℂ (D ⧸ baseIdeal p) := by
  let := swap_finite p
  have hs : baseIdeal (fun i => swap (p i)) ≤ highOrder k := by
    rw [← swap_baseIdeal]
    exact swapIdeal_le_highOrder _ k hI
  have hm : FormalBlowup.swap (f : D) ∈ baseIdeal (fun i => swap (p i)) := by
    rw [← swap_baseIdeal]
    exact Ideal.mem_map_of_mem _ f.property
  have ho : (FormalBlowup.swap (f : D)).order = k := by
    rw [order_swap]
    exact order_eq_of_initial k f (hI f.property) a b hab hf
  obtain ⟨a',b',hab',hf'⟩ := initial_of_order_eq k _ ho
  obtain ⟨hfin,hlt⟩ := child_finite_drop (fun i => swap (p i)) k hk hs
    ⟨FormalBlowup.swap (f : D),hm⟩ a' b' hab' hf' c
  exact ⟨hfin,by simpa only [swap_finrank] using hlt⟩

 

def ResolvesWithin {ι : Type*} : ℕ → (ι → P) → Prop
  | 0, p => baseIdeal p = ⊤
  | n+1, p => baseIdeal p = ⊤ ∨ ∃ k : ℕ, 0 < k ∧ baseIdeal p ≤ highOrder k ∧
      (∀ c : ℂ, ResolvesWithin n (child p k c)) ∧
      (∀ c : ℂ, ResolvesWithin n (child (fun i => swap (p i)) k c))

lemma resolvesWithin_mono {ι : Type*} (p : ι → P) {n m : ℕ} (h : n ≤ m)
    (hp : ResolvesWithin n p) : ResolvesWithin m p := by
  induction m generalizing n p with
  | zero => simpa only [Nat.le_zero.mp h] using hp
  | succ m ih =>
    cases n with
    | zero => exact Or.inl hp
    | succ n =>
      rcases hp with hp | ⟨k,hk,hI,h₁,h₂⟩
      · exact Or.inl hp
      · exact Or.inr ⟨k,hk,hI,fun c => ih _ (Nat.le_of_succ_le_succ h) (h₁ c),
          fun c => ih _ (Nat.le_of_succ_le_succ h) (h₂ c)⟩

 

theorem resolvesWithin_colength {ι : Type*} (p : ι → P)
    [FiniteDimensional ℂ (D ⧸ baseIdeal p)] :
    ResolvesWithin (Module.finrank ℂ (D ⧸ baseIdeal p)) p := by
  generalize hn : Module.finrank ℂ (D ⧸ baseIdeal p) = n
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases hp : baseIdeal p = ⊤
    · cases n with
      | zero => exact hp
      | succ n => exact Or.inl hp
    · obtain ⟨k,hk,hI,f,a,b,hab,hf⟩ := exists_minimal_order (baseIdeal p) hp
      have hfirst := child_finite_drop p k hk hI f a b hab hf 0
      have hn0 : 0 < n := by have := hfirst.2; omega
      obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn0)
      refine Or.inr ⟨k,hk,hI,?_,?_⟩
      · intro c
        obtain ⟨hfin,hlt⟩ := child_finite_drop p k hk hI f a b hab hf c
        let := hfin
        have hl : Module.finrank ℂ (D ⧸ baseIdeal (child p k c)) < m+1 := by omega
        exact resolvesWithin_mono _ (by omega) (ih _ hl _ rfl)
      · intro c
        obtain ⟨hfin,hlt⟩ := swap_child_finite_drop p k hk hI f a b hab hf c
        let := hfin
        have hl : Module.finrank ℂ (D ⧸ baseIdeal (child (fun i => swap (p i)) k c)) < m+1 := by omega
        exact resolvesWithin_mono _ (by omega) (ih _ hl _ rfl)



def valueHom (w : ℂ × ℂ) : P →ₐ[ℂ] ℂ := MvPolynomial.aeval ![w.1,w.2]
def value (p : P) (w : ℂ × ℂ) : ℂ := valueHom w p
@[simp] lemma value_X₀ (w : ℂ × ℂ) : value (MvPolynomial.X 0) w = w.1 := by simp [value,valueHom]
@[simp] lemma value_X₁ (w : ℂ × ℂ) : value (MvPolynomial.X 1) w = w.2 := by simp [value,valueHom]
@[simp] lemma value_C (a : ℂ) (w : ℂ × ℂ) : value (MvPolynomial.C a) w = a := by simp [value,valueHom]
lemma value_add (p q : P) (w : ℂ × ℂ) : value (p+q) w = value p w + value q w := (valueHom w).map_add p q
lemma value_mul (p q : P) (w : ℂ × ℂ) : value (p*q) w = value p w * value q w := (valueHom w).map_mul p q
lemma value_pow (p : P) (n : ℕ) (w : ℂ × ℂ) : value (p^n) w = value p w ^ n := (valueHom w).map_pow p n

def constant : D →ₐ[ℂ] ℂ where
  toRingHom := MvPowerSeries.constantCoeff
  commutes' a := by simp [← MvPowerSeries.c_eq_algebraMap]
lemma constant_embed (p : P) : MvPowerSeries.constantCoeff (embed p) = value p 0 := by
  have H : constant.comp embed = valueHom 0 := by
    apply MvPolynomial.algHom_ext
    intro i
    change MvPowerSeries.constantCoeff (embed (MvPolynomial.X i)) = (valueHom 0) (MvPolynomial.X i)
    rw [embed_X]
    fin_cases i <;> simp [valueHom]
  exact AlgHom.congr_fun H p

lemma baseIdeal_ne_top_iff {ι : Type*} (p : ι → P) :
    baseIdeal p ≠ ⊤ ↔ ∀ i, value (p i) 0 = 0 := by
  constructor
  · intro hp i
    by_contra hi
    apply hp
    apply (baseIdeal p).eq_top_of_isUnit_mem (Ideal.subset_span ⟨i,rfl⟩)
    rw [MvPowerSeries.isUnit_iff_constantCoeff,isUnit_iff_ne_zero,constant_embed]
    exact hi
  · intro h
    have H : baseIdeal p ≤ RingHom.ker (MvPowerSeries.constantCoeff : D →+* ℂ) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change MvPowerSeries.constantCoeff (embed (p i)) = 0
      rw [constant_embed,h i]
    exact ne_top_of_le_ne_top (RingHom.ker_ne_top _) H
lemma baseIdeal_eq_top_iff {ι : Type*} (p : ι → P) :
    baseIdeal p = ⊤ ↔ ∃ i, value (p i) 0 ≠ 0 := by
  classical
  simpa only [not_not,not_forall] using not_congr (baseIdeal_ne_top_iff p)

lemma value_shift (p : P) (a w : ℂ × ℂ) : value (shift a p) w = value p (w+a) := by
  have H : (valueHom w).comp (shift a) = valueHom (w+a) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [valueHom,shift]
  exact AlgHom.congr_fun H p
lemma value_blowup (p : P) (w : ℂ × ℂ) : value (blowup p) w = value p (w.1,w.1*w.2) := by
  have H : (valueHom w).comp blowup = valueHom (w.1,w.1*w.2) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [valueHom,blowup]
  exact AlgHom.congr_fun H p
lemma value_swap (p : P) (w : ℂ × ℂ) : value (swap p) w = value p (w.2,w.1) := by
  have H : (valueHom w).comp swap = valueHom (w.2,w.1) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [valueHom,swap]
  exact AlgHom.congr_fun H p

 

lemma child_factor {ι : Type*} (p : ι → P) (k : ℕ) (hI : baseIdeal p ≤ highOrder k)
    (c : ℂ) (i : ι) (w : ℂ × ℂ) :
    w.1^k * value (child p k c i) w = value (p i) (w.1,w.1*(w.2+c)) := by
  have H := congrArg (fun q => value q (w+(0,c)))
    (polynomial_factor k (p i) (hI (Ideal.subset_span ⟨i,rfl⟩)))
  simpa only [value_mul,value_pow,value_X₀,value_blowup,value_shift,child,
    Prod.fst_add,Prod.snd_add,Prod.fst,Prod.snd,add_zero] using H



def linePolynomial : P →ₐ[ℂ] Polynomial ℂ := MvPolynomial.aeval ![0,Polynomial.X]
lemma linePolynomial_eval (p : P) (c : ℂ) : (linePolynomial p).eval c = value p (0,c) := by
  have H : (Polynomial.aeval c).comp linePolynomial = valueHom (0,c) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [linePolynomial,valueHom]
  simpa [Polynomial.aeval_def, Algebra.algebraMap_self, value] using AlgHom.congr_fun H p

lemma row_embed (p : P) : row (embed p) = (linePolynomial p : PowerSeries ℂ) := by
  have H : row.comp embed = (Polynomial.coeToPowerSeries.algHom ℂ).comp linePolynomial := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · change row (embed (MvPolynomial.X 0)) = _
      rw [embed_X]
      have h0 : row (X 0) = 0 := killCompl_X_eq_zero (by simp [yEmbedding])
      rw [h0]
      simp [linePolynomial]
    · change row (embed (MvPolynomial.X 1)) = _
      rw [embed_X]
      have h1 : row (X 1) = PowerSeries.X := killCompl_X ()
      rw [h1]
      simp [linePolynomial,Polynomial.coeToPowerSeries.algHom_apply]
  simpa only [AlgHom.comp_apply,Polynomial.coeToPowerSeries.algHom_apply,
    Algebra.algebraMap_self,PowerSeries.map_id,id_eq] using AlgHom.congr_fun H p

lemma exists_generator_initial {ι : Type*} (p : ι → P) (k : ℕ)
    (hI : baseIdeal p ≤ highOrder k) (f : baseIdeal p)
    (a b : ℕ) (hab : a+b=k) (hf : coeff (exp a b) (f : D) ≠ 0) :
    ∃ i : ι, ∃ a' b' : ℕ, a'+b'=k ∧ coeff (exp a' b') (embed (p i)) ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  have hJ : baseIdeal p ≤ highOrder (k+1) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    apply mem_highOrder.mpr
    intro d hd
    by_cases he : d 0+d 1=k
    · simpa only [exp_eta] using hn i (d 0) (d 1) he
    · exact mem_highOrder.mp (hI (Ideal.subset_span ⟨i,rfl⟩)) d (by omega)
  exact hf (mem_highOrder.mp (hJ f.property) (exp a b) (by simp [hab]))

 

theorem finite_bad_directions {ι : Type*} (p : ι → P) (k : ℕ)
    (hI : baseIdeal p ≤ highOrder k) (f : baseIdeal p)
    (a b : ℕ) (hab : a+b=k) (hf : coeff (exp a b) (f : D) ≠ 0) :
    {c : ℂ | baseIdeal (child p k c) ≠ ⊤}.Finite := by
  obtain ⟨i,a',b',hab',hc⟩ := exists_generator_initial p k hI f a b hab hf
  have hi := hI (Ideal.subset_span ⟨i,rfl⟩)
  have hrow : row (transform k ⟨embed (p i),hi⟩) ≠ 0 :=
    (row_initial_order_le k a' b' hab' ⟨embed (p i),hi⟩ hc).2
  have hpoly : linePolynomial (polynomialTransform k (p i)) ≠ 0 := by
    intro he
    have H : row (transform k ⟨embed (p i),hi⟩) = 0 := by
      have ht := transform_polynomial k (p i) hi
      change transform k ⟨embed (p i),hi⟩ = embed (polynomialTransform k (p i)) at ht
      exact (congrArg row ht).trans ((row_embed _).trans (by simp [he]))
    exact hrow H
  apply (Polynomial.finite_setOfPred_isRoot hpoly).subset
  intro c hc
  have H := (baseIdeal_ne_top_iff (child p k c)).mp hc i
  change value (shift (0,c) (polynomialTransform k (p i))) 0 = 0 at H
  rw [value_shift,zero_add] at H
  exact (linePolynomial_eval _ c).trans H

end

section
open FormalBlowup Filter Topology

lemma value_analytic (p : P) (w : ℂ × ℂ) : AnalyticAt ℂ (value p) w := by
  change AnalyticAt ℂ (fun z => value p z) w
  induction p using MvPolynomial.induction_on with
  | C a => simpa only [value_C] using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ × ℂ => a) w)
  | add p q hp hq => simpa only [value_add,Pi.add_apply] using hp.fun_add hq
  | mul_X p i hp =>
      have hi : AnalyticAt ℂ (fun z : ℂ × ℂ => ![z.1,z.2] i) w := by
        fin_cases i
        · simpa using ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt w)
        · simpa using ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt w)
      simpa only [value,valueHom,map_mul,MvPolynomial.aeval_X] using hp.fun_mul hi

def IsolatedAtOrigin {ι : Type*} (p : ι → P) : Prop :=
  ∀ᶠ w in 𝓝 (0 : ℂ × ℂ), (∀ i, value (p i) w = 0) → w = 0

lemma finite_isolated {T : Type*} [TopologicalSpace T] [T1Space T] {B : Set T}
    (hB : B.Finite) (a : T) : ∀ᶠ z in 𝓝 a, z ∈ B → z = a := by
  have hn : a ∈ (B \ {a})ᶜ := by simp
  filter_upwards [(hB.sdiff (t := {a})).isClosed.isOpen_compl.mem_nhds hn] with z hz hzb
  by_contra hza
  exact hz ⟨hzb,hza⟩

lemma child_isolated {ι : Type*} (p : ι → P) (k : ℕ)
    (hI : baseIdeal p ≤ highOrder k) (f : baseIdeal p)
    (a b : ℕ) (hab : a+b=k) (hf : coeff (exp a b) (f : D) ≠ 0)
    (hp : IsolatedAtOrigin p) (c : ℂ) : IsolatedAtOrigin (child p k c) := by
  have hbad := finite_bad_directions p k hI f a b hab hf
  have he := finite_isolated hbad c
  have hadd : Tendsto (fun z : ℂ => z+c) (𝓝 0) (𝓝 c) := by
    simpa only [id_eq,zero_add] using (continuousAt_id.add_const c).tendsto (x := (0 : ℂ))
  have hz := hadd.eventually he
  have hmap : Tendsto (fun w : ℂ × ℂ => (w.1,w.1*(w.2+c))) (𝓝 0) (𝓝 0) := by
    convert (continuous_fst.prodMk (continuous_fst.mul (continuous_snd.add_const c))).tendsto (0 : ℂ × ℂ) using 1; simp only [Pi.mul_apply,Prod.fst_zero,Prod.snd_zero,zero_mul,Prod.mk_zero_zero]
  have hp' := hmap.eventually hp
  have hz' := (continuous_snd.tendsto (0 : ℂ × ℂ)).eventually hz
  filter_upwards [hp',hz'] with w hw hwz hzero
  have H : (w.1,w.1*(w.2+c)) = (0 : ℂ × ℂ) := by
    apply hw
    intro i
    rw [← child_factor p k hI c i w,hzero i,mul_zero]
  have hx : w.1 = 0 := congrArg Prod.fst H
  have hchild : baseIdeal (child p k (w.2+c)) ≠ ⊤ := by
    apply (baseIdeal_ne_top_iff _).mpr
    intro i
    have hi := hzero i
    change value (shift (0,c) (polynomialTransform k (p i))) w = 0 at hi
    change value (shift (0,w.2+c) (polynomialTransform k (p i))) 0 = 0
    rw [value_shift,zero_add]
    have hw : w + (0,c) = (0,w.2+c) := Prod.ext (by simpa using hx) rfl
    simpa only [value_shift,hw] using hi
  have hy : w.2 = 0 := add_right_cancel ((hwz hchild).trans (zero_add c).symm)
  exact Prod.ext hx hy

end

open FormalBlowup

lemma X_dvd_of_linePolynomial_eq_zero {p : P} (hp : linePolynomial p = 0) :
    MvPolynomial.X 0 ∣ p := by
  apply MvPolynomial.X_dvd_iff_modMonomial_eq_zero.mpr
  ext d
  by_cases hd : 1 ≤ d 0
  · have hle : Finsupp.single 0 1 ≤ d := Finsupp.single_le_iff.mpr hd
    simp only [MvPolynomial.coeff_modMonomial_of_le _ hle,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]
  · have hd0 : d 0 = 0 := by omega
    have hrow : row (embed p) = 0 := by rw [row_embed,hp]; simp
    have H := congrArg (PowerSeries.coeff (d 1)) hrow
    rw [row_coeff] at H
    have he : exp 0 (d 1) = d := by rw [← hd0,exp_eta]
    have hnle : ¬Finsupp.single 0 1 ≤ d := by simpa [Finsupp.single_le_iff] using hd
    simpa only [MvPolynomial.coeff_modMonomial_of_not_le _ hnle,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply,
      he,embed_apply,MvPolynomial.coeff_coe,map_zero] using H

lemma linePolynomial_eq_zero_of_X_dvd {p : P} (hp : MvPolynomial.X 0 ∣ p) :
    linePolynomial p = 0 := by
  obtain ⟨q,rfl⟩ := hp
  simp [linePolynomial]

lemma blowup_injective : Function.Injective blowup := by
  apply (injective_iff_map_eq_zero blowup).mpr
  intro p hp
  apply MvPolynomial.ext
  intro d
  have H := congrArg (fun q : P => coeff (exp (d 0+d 1) (d 1)) (embed q)) hp
  rw [embed_blowup,coeff_blowup] at H
  simpa only [exp_eta,embed_apply,MvPolynomial.coeff_coe,map_zero,MvPowerSeries.coeff_zero,
    AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using H

 

theorem coordinate_exceptional_factor {p : P} (hp : p ≠ 0) (h0 : value p 0 = 0) :
    ∃ n : ℕ, ∃ q : P, blowup p = MvPolynomial.X 0 ^ (n+1) * q ∧
      linePolynomial q ≠ 0 := by
  have hb : blowup p ≠ 0 := fun h => hp (blowup_injective (h.trans (map_zero blowup).symm))
  obtain ⟨m,q,hn,hq⟩ := WfDvdMonoid.max_power_factor hb (MvPolynomial.X_prime (i := (0 : Fin 2))).irreducible
  have hl : linePolynomial q ≠ 0 := fun h => hn (X_dvd_of_linePolynomial_eq_zero h)
  have hb0 : linePolynomial (blowup p) = 0 := by
    apply Polynomial.funext
    intro z
    rw [linePolynomial_eval,value_blowup]
    simpa only [zero_mul,Prod.mk_zero_zero,Polynomial.eval_zero] using h0
  have hm : m ≠ 0 := by
    intro hm
    rw [hm,pow_zero,one_mul] at hq
    exact hl (hq ▸ hb0)
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  exact ⟨n,q,hq,hl⟩



lemma power_times_unit_product (i : Fin 2) (s : Finset (ℂ × ℂ)) :
    ∃ (n : ℕ) (u : D), IsUnit u ∧
      (∏ b ∈ s, (MvPowerSeries.X i - MvPowerSeries.C (![b.1,b.2] i))) =
        MvPowerSeries.X i ^ n * u := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0,1,isUnit_one,by simp⟩
  | @insert b s hb ih =>
    obtain ⟨n,u,hu,he⟩ := ih
    rw [Finset.prod_insert hb,he]
    by_cases hz : ![b.1,b.2] i = 0
    · refine ⟨n+1,u,hu,?_⟩
      simp only [hz,map_zero,sub_zero,pow_succ]; ring
    · refine ⟨n,(MvPowerSeries.X i - MvPowerSeries.C (![b.1,b.2] i))*u,?_,by ring⟩
      apply IsUnit.mul _ hu
      rw [MvPowerSeries.isUnit_iff_constantCoeff,isUnit_iff_ne_zero]
      simpa only [map_sub,MvPowerSeries.constantCoeff_X,MvPowerSeries.constantCoeff_C,zero_sub,neg_ne_zero] using hz

lemma coordinate_power_of_finite_zeros {ι : Type*} (p : ι → P)
    (hB : Set.Finite {w : ℂ × ℂ | ∀ j, value (p j) w = 0}) (i : Fin 2) :
    ∃ n : ℕ, MvPowerSeries.X i ^ n ∈ baseIdeal p := by
  classical
  let s := hB.toFinset
  let q : P := ∏ b ∈ s, (MvPolynomial.X i - MvPolynomial.C (![b.1,b.2] i))
  let J : Ideal P := Ideal.span (Set.range p)
  have hq : q ∈ J.radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
    intro z hz
    have he : ![z 0,z 1] = z := by ext j; fin_cases j <;> simp
    have hm : (z 0,z 1) ∈ s := by
      rw [Set.Finite.mem_toFinset]
      intro j
      change MvPolynomial.aeval ![z 0,z 1] (p j) = 0
      rw [he]
      exact hz (p j) (Ideal.subset_span ⟨j,rfl⟩)
    dsimp only [q]
    rw [map_prod]
    apply Finset.prod_eq_zero hm
    simp only [map_sub,MvPolynomial.aeval_X,MvPolynomial.aeval_C,he,Algebra.algebraMap_self,RingHom.id_apply,sub_self]
  obtain ⟨m,hm⟩ := hq
  have heJ : Ideal.map embed J = baseIdeal p := by
    simp only [J,baseIdeal,Ideal.map_span,← Set.range_comp]
    rfl
  have hmem : embed q ^ m ∈ baseIdeal p := by
    rw [← heJ,← map_pow]
    exact Ideal.mem_map_of_mem _ hm
  obtain ⟨n,u,hu,he⟩ := power_times_unit_product i s
  have hqe : embed q = MvPowerSeries.X i ^ n * u := by
    dsimp only [q]
    simpa only [map_prod,map_sub,embed_X,embed_C] using he
  rw [hqe,mul_pow,← pow_mul] at hmem
  exact ⟨n*m,(baseIdeal p).mul_unit_mem_iff_mem (hu.pow m) |>.mp hmem⟩

 

theorem finite_colength_of_finite_zeros {ι : Type*} (p : ι → P)
    (hB : Set.Finite {w : ℂ × ℂ | ∀ j, value (p j) w = 0}) :
    FiniteDimensional ℂ (D ⧸ baseIdeal p) := by
  obtain ⟨a,ha⟩ := coordinate_power_of_finite_zeros p hB 0
  obtain ⟨b,hb⟩ := coordinate_power_of_finite_zeros p hB 1
  exact finite_colength_of_coordinate_powers (baseIdeal p) a b ha hb

lemma finite_zeros_shift {ι : Type*} (p : ι → P)
    (hB : Set.Finite {w : ℂ × ℂ | ∀ j, value (p j) w = 0}) (a : ℂ × ℂ) :
    Set.Finite {w : ℂ × ℂ | ∀ j, value (shift a (p j)) w = 0} := by
  apply (hB.image (fun w => w-a)).subset
  intro w hw
  exact ⟨w+a,fun j => (value_shift _ _ _).symm.trans (hw j),add_sub_cancel_right w a⟩

end SplitTangent.PolynomialBlowup

namespace SplitTangent.IsolatedZero

 

theorem lower_bound_on_disc {f : ℂ → ℂ} {r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hf : ∀ z ∈ closedBall (0 : ℂ) r, DifferentiableAt ℂ f z)
    (hn : ∀ z ∈ closedBall (0 : ℂ) r, f z ≠ 0)
    (hb : ∀ z ∈ sphere (0 : ℂ) r, c ≤ ‖f z‖) : c ≤ ‖f 0‖ := by
  have hd : DiffContOnCl ℂ (fun z => (f z)⁻¹) (ball (0 : ℂ) r) := by
    refine ⟨?_,?_⟩
    · intro z hz
      exact ((hf z (ball_subset_closedBall hz)).inv (hn z (ball_subset_closedBall hz))).differentiableWithinAt
    · rw [closure_ball _ hr.ne']
      exact fun z hz => ((hf z hz).continuousAt.inv₀ (hn z hz)).continuousWithinAt
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x := (0 : ℂ)) (r := r))
    hd (C := c⁻¹) (fun z hz => ?_) (subset_closure (mem_ball_self hr))
  · rw [norm_inv] at h
    exact (inv_le_inv₀ (norm_pos_iff.mpr (hn 0 (mem_closedBall_self hr.le))) hc).mp h
  · rw [frontier_ball _ hr.ne'] at hz
    rw [norm_inv]
    exact (inv_le_inv₀ (norm_pos_iff.mpr (hn z (sphere_subset_closedBall hz))) hc).mpr (hb z hz)

 

theorem nonzero_of_punctured_nonzero {f : ℂ × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hn : ∀ᶠ w in 𝓝[≠] (0 : ℂ × ℂ), f w ≠ 0) : f 0 ≠ 0 := by
  intro hzero
  have hn' : ∀ᶠ w in 𝓝 (0 : ℂ × ℂ), w ≠ 0 → f w ≠ 0 := by
    simpa only [eventually_nhdsWithin_iff,mem_compl_iff,mem_singleton_iff] using hn
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hf.eventually_analyticAt.and hn')
  let R := r / 2
  have hR : 0 < R := half_pos hr
  have hxy {x y : ℂ} (hx : ‖x‖ < R) (hy : ‖y‖ ≤ R) :
      (x,y) ∈ ball (0 : ℂ × ℂ) r := by
    rw [mem_ball_zero_iff,Prod.norm_def,max_lt_iff]
    exact ⟨hx.trans (half_lt_self hr),hy.trans_lt (half_lt_self hr)⟩
  have h0y {y : ℂ} (hy : y ∈ sphere (0 : ℂ) R) :
      AnalyticAt ℂ f (0,y) ∧ f (0,y) ≠ 0 := by
    have hy' : ‖y‖ = R := by simpa using hy
    have ht := hball (hxy (x := 0) (by simpa using hR) hy'.le)
    refine ⟨ht.1,ht.2 ?_⟩
    intro he
    have he' : y = 0 := congrArg Prod.snd he
    rw [he',norm_zero] at hy'
    exact hR.ne' hy'.symm
  have hc : ContinuousOn (fun y : ℂ => ‖f (0,y)‖) (sphere 0 R) := by
    intro y hy
    exact ((h0y hy).1.continuousAt.comp (continuousAt_const.prodMk continuousAt_id)).norm.continuousWithinAt
  obtain ⟨y₀,hy₀,hmin⟩ := (isCompact_sphere (0 : ℂ) R).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hR.le) hc
  let c := ‖f (0,y₀)‖ / 2
  have hcpos : 0 < c := half_pos (norm_pos_iff.mpr (h0y hy₀).2)
  have hbound : ∀ᶠ x : ℂ in 𝓝 0, ∀ y ∈ sphere (0 : ℂ) R, c < ‖f (x,y)‖ := by
    apply (isCompact_sphere (0 : ℂ) R).eventually_forall_of_forall_eventually
    intro y hy
    exact (h0y hy).1.continuousAt.norm.eventually (lt_mem_nhds
      ((half_lt_self (norm_pos_iff.mpr (h0y hy₀).2)).trans_le (hmin hy)))
  have hsmall : ∀ᶠ x : ℂ in 𝓝 0, ‖f (x,0)‖ < c := by
    have hcont : ContinuousAt (fun x : ℂ => ‖f (x,(0 : ℂ))‖) 0 :=
      (hf.continuousAt.comp (f := fun x : ℂ => (x,(0 : ℂ)))
        (continuousAt_id.prodMk continuousAt_const)).norm
    apply Filter.Tendsto.eventually (p := fun q : ℝ => q < c) hcont
    change {q : ℝ | q < c} ∈ 𝓝 ‖f (0 : ℂ × ℂ)‖
    rw [hzero,norm_zero]
    exact gt_mem_nhds hcpos
  have hcontra : ∀ᶠ x : ℂ in 𝓝[≠] 0, False := by
    filter_upwards [hbound.filter_mono nhdsWithin_le_nhds,hsmall.filter_mono nhdsWithin_le_nhds,
      (show ∀ᶠ x : ℂ in 𝓝 0, x ∈ ball 0 R from ball_mem_nhds 0 hR).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with x hb hs hx hx0
    have hx' : ‖x‖ < R := by simpa using hx
    have hnz (y : ℂ) (hy : y ∈ closedBall (0 : ℂ) R) : f (x,y) ≠ 0 := by
      apply (hball (hxy hx' (by simpa using hy))).2
      intro he
      exact hx0 (congrArg Prod.fst he)
    have hdf (y : ℂ) (hy : y ∈ closedBall (0 : ℂ) R) :
        DifferentiableAt ℂ (fun y : ℂ => f (x,y)) y :=
      ((hball (hxy hx' (by simpa using hy))).1.differentiableAt).comp y
        ((differentiableAt_const x).prodMk differentiableAt_id)
    exact (not_le_of_gt hs) (lower_bound_on_disc hR hcpos hdf hnz (fun y hy => (hb y hy).le))
  exact hcontra.exists.elim (fun _ h => h)

 
theorem nonzero_of_punctured_nonzero_at {f : ℂ × ℂ → ℂ} {a : ℂ × ℂ}
    (hf : AnalyticAt ℂ f a) (hn : ∀ᶠ w in 𝓝[≠] a, f w ≠ 0) : f a ≠ 0 := by
  have hn' : ∀ᶠ w in 𝓝 a, w ≠ a → f w ≠ 0 := by
    simpa only [eventually_nhdsWithin_iff,mem_compl_iff,mem_singleton_iff] using hn
  have ht : ContinuousAt (fun w : ℂ × ℂ => w + a) 0 := continuousAt_id.add_const a
  have hft : AnalyticAt ℂ (fun w : ℂ × ℂ => f (w+a)) 0 := by
    simpa only [Function.comp_def,Pi.add_apply,id_eq,zero_add] using hf.comp_of_eq (analyticAt_id.add (analyticAt_const)) (zero_add a)
  have hnt : ∀ᶠ w in 𝓝[≠] (0 : ℂ × ℂ), f (w+a) ≠ 0 := by
    have he : ∀ᶠ w in 𝓝 (0 : ℂ × ℂ), w + a ≠ a → f (w+a) ≠ 0 := by
      have ht' : Tendsto (fun w : ℂ × ℂ => w+a) (𝓝 0) (𝓝 a) := by simpa only [ContinuousAt,zero_add] using ht
      exact ht'.eventually hn'
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with w hw hne
    apply hw
    simpa only [ne_eq,add_eq_right] using (show w ≠ 0 from hne)
  simpa only [zero_add] using nonzero_of_punctured_nonzero hft hnt

end SplitTangent.IsolatedZero

namespace SplitTangent.ProjectiveEmbedding
variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)

 

theorem nonzero_of_continuous_incidence {Q : ℂ × ℂ → Fin (e.N+1) → ℂ}
    {F : ℂ × ℂ → X.Carrier} {a : ℂ × ℂ} (hQ : AnalyticAt ℂ Q a)
    (hF : ContinuousAt F a) (hnz : ∀ᶠ w in 𝓝[≠] a, Q w ≠ 0)
    (hi : ∀ᶠ w in 𝓝[≠] a, e.Incidence (F w) (Q w)) : Q a ≠ 0 := by
  obtain ⟨i,hpi⟩ := Function.ne_iff.mp (e.map (F a)).rep_nonzero
  change (e.map (F a)).rep i ≠ 0 at hpi
  have hp : ∀ᶠ w in 𝓝 a, (e.map (F w)).rep i ≠ 0 :=
    hF.eventually ((e.open_patch i).mem_nhds hpi)
  have hni : ∀ᶠ w in 𝓝[≠] a, Q w i ≠ 0 := by
    filter_upwards [hp.filter_mono nhdsWithin_le_nhds,hnz,hi] with w hw hn hh
    intro hz
    apply hn
    ext j
    rw [(e.incidence_iff_coordinates hw).mp hh j,hz,zero_mul]
    rfl
  have hqa : Q a i ≠ 0 := IsolatedZero.nonzero_of_punctured_nonzero_at
    ((ContinuousLinearMap.proj i : (Fin (e.N+1) → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp hQ) hni
  intro hz
  exact hqa (congrFun hz i)

theorem holomorphic_of_continuous_punctured_incidence [CompactSpace X.Carrier]
    {Q : ℂ × ℂ → Fin (e.N+1) → ℂ} {F : ℂ × ℂ → X.Carrier} {a : ℂ × ℂ}
    (hQ : AnalyticAt ℂ Q a) (hF : ContinuousAt F a)
    (hnz : ∀ᶠ w in 𝓝[≠] a, Q w ≠ 0)
    (hi : ∀ᶠ w in 𝓝[≠] a, e.Incidence (F w) (Q w)) :
    ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F a := by
  have hqa := e.nonzero_of_continuous_incidence hQ hF hnz hi
  have hia : e.Incidence (F a) (Q a) :=
    e.isClosed_incidence.mem_of_tendsto
      ((hF.prodMk hQ.continuousAt).mono_left nhdsWithin_le_nhds) hi
  apply e.holomorphic_of_incidence hQ hqa
  have hi' : ∀ᶠ w in 𝓝 a, w ≠ a → e.Incidence (F w) (Q w) := by
    simpa only [eventually_nhdsWithin_iff,mem_compl_iff,mem_singleton_iff] using hi
  filter_upwards [hi'] with w hw
  by_cases hwa : w = a
  · simpa only [hwa] using hia
  · exact hw hwa

end SplitTangent.ProjectiveEmbedding

open Filter Topology Set Metric
namespace SplitTangent.AffineBlowup

 
def first (w : ℂ × ℂ) : ℂ × ℂ := (w.1,w.1*w.2)
def second (w : ℂ × ℂ) : ℂ × ℂ := (w.1*w.2,w.1)

variable {Y : Type*} [TopologicalSpace Y]

 

theorem tendsto_of_constant_exceptional {F H₁ H₂ : ℂ × ℂ → Y} {a : Y}
    (h₁ : ∀ z ∈ closedBall (0 : ℂ) 1, ContinuousAt H₁ (0,z))
    (h₂ : ∀ z ∈ closedBall (0 : ℂ) 1, ContinuousAt H₂ (0,z))
    (hc₁ : ∀ z ∈ closedBall (0 : ℂ) 1, H₁ (0,z) = a)
    (hc₂ : ∀ z ∈ closedBall (0 : ℂ) 1, H₂ (0,z) = a)
    (hf₁ : ∀ w : ℂ × ℂ, w.1 ≠ 0 → H₁ w = F (first w))
    (hf₂ : ∀ w : ℂ × ℂ, w.1 ≠ 0 → H₂ w = F (second w)) :
    Tendsto F (𝓝[≠] (0 : ℂ × ℂ)) (𝓝 a) := by
  apply tendsto_def.mpr
  intro V hV
  have he₁ : ∀ᶠ x : ℂ in 𝓝 0, ∀ z ∈ closedBall (0 : ℂ) 1, H₁ (x,z) ∈ V := by
    apply (isCompact_closedBall (0 : ℂ) 1).eventually_forall_of_forall_eventually
    intro z hz
    have ht := (h₁ z hz).tendsto
    rw [hc₁ z hz] at ht
    exact ht.eventually hV
  have he₂ : ∀ᶠ x : ℂ in 𝓝 0, ∀ z ∈ closedBall (0 : ℂ) 1, H₂ (x,z) ∈ V := by
    apply (isCompact_closedBall (0 : ℂ) 1).eventually_forall_of_forall_eventually
    intro z hz
    have ht := (h₂ z hz).tendsto
    rw [hc₂ z hz] at ht
    exact ht.eventually hV
  have hp₁ : ∀ᶠ w : ℂ × ℂ in 𝓝 0, ∀ z ∈ closedBall (0 : ℂ) 1, H₁ (w.1,z) ∈ V :=
    (continuous_fst.tendsto (0 : ℂ × ℂ)).eventually he₁
  have hp₂ : ∀ᶠ w : ℂ × ℂ in 𝓝 0, ∀ z ∈ closedBall (0 : ℂ) 1, H₂ (w.2,z) ∈ V :=
    (continuous_snd.tendsto (0 : ℂ × ℂ)).eventually he₂
  filter_upwards [hp₁.filter_mono nhdsWithin_le_nhds,hp₂.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with w hw₁ hw₂ hw0
  change F w ∈ V
  have hn : w ≠ 0 := hw0
  rcases le_total ‖w.2‖ ‖w.1‖ with hle | hle
  · have hx : w.1 ≠ 0 := by
      intro hx
      apply hn
      have hy : w.2 = 0 := norm_eq_zero.mp (le_antisymm (by simpa only [hx,norm_zero] using hle) (norm_nonneg _))
      exact Prod.ext hx hy
    have hz : w.2 / w.1 ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall_zero_iff,norm_div]
      exact (div_le_one (norm_pos_iff.mpr hx)).mpr hle
    have h := hw₁ (w.2/w.1) hz
    rw [hf₁ (w.1,w.2/w.1) hx] at h
    simpa [first,mul_div_cancel₀ _ hx] using h
  · have hy : w.2 ≠ 0 := by
      intro hy
      apply hn
      have hx : w.1 = 0 := norm_eq_zero.mp (le_antisymm (by simpa only [hy,norm_zero] using hle) (norm_nonneg _))
      exact Prod.ext hx hy
    have hz : w.1 / w.2 ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall_zero_iff,norm_div]
      exact (div_le_one (norm_pos_iff.mpr hy)).mpr hle
    have h := hw₂ (w.1/w.2) hz
    rw [hf₂ (w.2,w.1/w.2) hy] at h
    simpa [second,mul_div_cancel₀ _ hy] using h

end SplitTangent.AffineBlowup

namespace SplitTangent.ProjectiveEmbedding
open Filter Topology
variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)

lemma incidence_zero (x : X.Carrier) : e.Incidence x 0 := by
  intro i j
  simp

lemma incidence_smul_iff {x : X.Carrier} {v : Fin (e.N+1) → ℂ} {s : ℂ} (hs : s ≠ 0) :
    e.Incidence x (s • v) ↔ e.Incidence x v := by
  constructor <;> intro h i j
  · have H := h i j
    simp only [Pi.smul_apply,smul_eq_mul] at H
    apply mul_left_cancel₀ hs
    calc
      s * ((e.map x).rep i * v j) = (e.map x).rep i*(s*v j) := by ring
      _ = (e.map x).rep j*(s*v i) := H
      _ = s*((e.map x).rep j*v i) := by ring
  · simp only [Pi.smul_apply,smul_eq_mul]
    calc
      (e.map x).rep i*(s*v j) = s*((e.map x).rep i*v j) := by ring
      _ = s*((e.map x).rep j*v i) := by rw [h i j]
      _ = (e.map x).rep j*(s*v i) := by ring

 

def coneLift (x₀ : X.Carrier) (v : Fin (e.N+1) → ℂ) : X.Carrier := by
  classical
  exact if h : ∃ x, e.Incidence x v then Classical.choose h else x₀

lemma coneLift_incidence (x₀ : X.Carrier) {v : Fin (e.N+1) → ℂ}
    (h : ∃ x, e.Incidence x v) : e.Incidence (e.coneLift x₀ v) v := by
  simp only [coneLift,dite_eq_left h]
  exact Classical.choose_spec h

lemma coneLift_eq (x₀ : X.Carrier) {v : Fin (e.N+1) → ℂ}
    {x : X.Carrier} (hv : v ≠ 0) (hx : e.Incidence x v) : e.coneLift x₀ v = x :=
  e.incidence_unique hv (e.coneLift_incidence x₀ ⟨x,hx⟩) hx

lemma coneLift_smul (x₀ : X.Carrier) {v : Fin (e.N+1) → ℂ} {s : ℂ}
    (hs : s ≠ 0) (hv : ∃ x, e.Incidence x v) : e.coneLift x₀ (s • v) = e.coneLift x₀ v := by
  by_cases hv0 : v = 0
  · simp only [hv0,smul_zero]
  · apply e.coneLift_eq x₀ (smul_ne_zero hs hv0)
    exact (e.incidence_smul_iff hs).mpr (e.coneLift_incidence x₀ hv)

end SplitTangent.ProjectiveEmbedding

namespace SplitTangent.TangentSplitting
open Filter Topology
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
lemma WedgeAt.congr {F G : E → X.Carrier} {A B : E → ℂ} {z : E}
    (hW : S.WedgeAt F A z) (hF : F =ᶠ[𝓝 z] G) (hA : A =ᶠ[𝓝 z] B) :
    S.WedgeAt G B z := by
  intro v w
  have hder : mfderiv 𝓘(ℂ,E) (ModelWithCorners X) F z =
      mfderiv 𝓘(ℂ,E) (ModelWithCorners X) G z := hF.mfderiv_eq
  rw [← hA.fderiv_eq,← hder,← hF.self_of_nhds]
  exact hW v w
end SplitTangent.TangentSplitting

namespace SplitTangent.PolynomialBlowup
lemma value_sub (p q : P) (w : ℂ × ℂ) : value (p-q) w = value p w - value q w :=
  (valueHom w).map_sub p q

lemma shift_shift (a b : ℂ × ℂ) (p : P) : shift a (shift b p) = shift (a+b) p := by
  have H : (shift a).comp (shift b) = shift (a+b) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [shift] <;> ring
  exact AlgHom.congr_fun H p
lemma shift_zero (p : P) : shift 0 p = p := by
  have H : shift 0 = AlgHom.id ℂ P := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [shift]
  exact AlgHom.congr_fun H p
lemma shift_injective (a : ℂ × ℂ) : Function.Injective (shift a) := by
  intro p q h
  have H := congrArg (shift (-a)) h
  simpa only [shift_shift,neg_add_cancel,shift_zero] using H
lemma polynomial_swap_swap (p : P) : swap (swap p) = p := by
  have H : swap.comp swap = AlgHom.id ℂ P := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [swap]
  exact AlgHom.congr_fun H p
lemma polynomial_swap_injective : Function.Injective swap := by
  intro p q h
  have H := congrArg swap h
  simpa only [polynomial_swap_swap] using H
end SplitTangent.PolynomialBlowup

namespace SplitTangent.AffineBlowup
open Filter Topology Metric
variable {Y : Type*} [TopologicalSpace Y]
lemma tendsto_of_local_constant_exceptional {F G₁ G₂ : ℂ × ℂ → Y} {a : Y}
    (h₁ : ∀ z ∈ closedBall (0 : ℂ) 1, ContinuousAt G₁ (0,z))
    (h₂ : ∀ z ∈ closedBall (0 : ℂ) 1, ContinuousAt G₂ (0,z))
    (hc₁ : ∀ z ∈ closedBall (0 : ℂ) 1, G₁ (0,z) = a)
    (hc₂ : ∀ z ∈ closedBall (0 : ℂ) 1, G₂ (0,z) = a)
    (hf₁ : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ᶠ w in 𝓝 (0,z), w.1 ≠ 0 → G₁ w = F (first w))
    (hf₂ : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ᶠ w in 𝓝 (0,z), w.1 ≠ 0 → G₂ w = F (second w)) :
    Tendsto F (𝓝[≠] (0 : ℂ × ℂ)) (𝓝 a) := by
  classical
  let H₁ : ℂ × ℂ → Y := fun w => if w.1 = 0 then G₁ w else F (first w)
  let H₂ : ℂ × ℂ → Y := fun w => if w.1 = 0 then G₂ w else F (second w)
  have he₁ (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) : H₁ =ᶠ[𝓝 (0,z)] G₁ := by
    filter_upwards [hf₁ z hz] with w hw
    dsimp only [H₁]
    split_ifs with hx
    · rfl
    · exact (hw hx).symm
  have he₂ (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) : H₂ =ᶠ[𝓝 (0,z)] G₂ := by
    filter_upwards [hf₂ z hz] with w hw
    dsimp only [H₂]
    split_ifs with hx
    · rfl
    · exact (hw hx).symm
  apply tendsto_of_constant_exceptional (H₁ := H₁) (H₂ := H₂)
    (fun z hz => (h₁ z hz).congr_of_eventuallyEq (he₁ z hz))
    (fun z hz => (h₂ z hz).congr_of_eventuallyEq (he₂ z hz))
  · intro z hz; simpa only [H₁,ite_eq_left rfl] using hc₁ z hz
  · intro z hz; simpa only [H₂,ite_eq_left rfl] using hc₂ z hz
  · intro w hw; simp only [H₁,ite_eq_right hw]
  · intro w hw; simp only [H₂,ite_eq_right hw]
end SplitTangent.AffineBlowup

namespace SplitTangent.BasePointRemoval
open Filter Topology Set
open PolynomialBlowup
open FormalBlowup (D highOrder polynomialTransform)
variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X) (S : TangentSplitting X)

def tuple (p : Fin (e.N+1) → P) (w : ℂ × ℂ) : Fin (e.N+1) → ℂ := fun i => value (p i) w

def lift (x₀ : X.Carrier) (p : Fin (e.N+1) → P) : ℂ × ℂ → X.Carrier :=
  fun w => e.coneLift x₀ (tuple e p w)

lemma tuple_analytic (p : Fin (e.N+1) → P) (w : ℂ × ℂ) : AnalyticAt ℂ (tuple e p) w :=
  AnalyticAt.pi (fun i => value_analytic (p i) w)

lemma tuple_child (p : Fin (e.N+1) → P) (k : ℕ) (hI : baseIdeal p ≤ highOrder k)
    (c : ℂ) (w : ℂ × ℂ) :
    tuple e p (w.1,w.1*(w.2+c)) = w.1^k • tuple e (child p k c) w := by
  ext j; exact (child_factor p k hI c j w).symm

lemma lift_holomorphic [CompactSpace X.Carrier] (x₀ : X.Carrier)
    {p : Fin (e.N+1) → P} {z : ℂ × ℂ} (hp : tuple e p z ≠ 0)
    (hc : ∀ᶠ w in 𝓝 z, ∃ x, e.Incidence x (tuple e p w)) :
    ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω (lift e x₀ p) z := by
  apply e.holomorphic_of_incidence (tuple_analytic e p z) hp
  exact hc.mono (fun w hw => e.coneLift_incidence x₀ hw)

lemma frequently_first_ne (z : ℂ × ℂ) : ∃ᶠ w in 𝓝 z, w.1 ≠ 0 := by
  by_cases hz : z.1 = 0
  · have ht : Tendsto (fun r : ℂ => (r,z.2)) (𝓝[≠] 0) (𝓝 z) := by
      have H := (continuousAt_id.prodMk continuousAt_const : ContinuousAt (fun r : ℂ => (r,z.2)) 0)
      simpa only [id_eq,← hz,Prod.mk.eta] using H.mono_left nhdsWithin_le_nhds
    exact ht.frequently (show ∃ᶠ r : ℂ in 𝓝[≠] 0, (r,z.2).1 ≠ 0 from
      Filter.Eventually.frequently self_mem_nhdsWithin)
  · exact (continuous_fst.continuousAt.eventually_ne hz).frequently

lemma blowup_contDiff (c : ℂ) : ContDiff ℂ ω (fun w : ℂ × ℂ => (w.1,w.1*(w.2+c))) :=
  contDiff_fst.prodMk (contDiff_fst.mul (contDiff_snd.add contDiff_const))

lemma cone_child [CompactSpace X.Carrier] {p : Fin (e.N+1) → P} (k : ℕ)
    (hI : baseIdeal p ≤ highOrder k) (c : ℂ)
    (hc : ∀ᶠ w in 𝓝 (0 : ℂ × ℂ), ∃ x, e.Incidence x (tuple e p w)) :
    ∀ᶠ w in 𝓝 (0 : ℂ × ℂ), ∃ x, e.Incidence x (tuple e (child p k c) w) := by
  let β : ℂ × ℂ → ℂ × ℂ := fun w => (w.1,w.1*(w.2+c))
  have hβ : Continuous β := (blowup_contDiff c).continuous
  have h0 : β 0 = 0 := by simp [β]
  have hp := hβ.continuousAt.tendsto.eventually (h0 ▸ hc)
  obtain ⟨U,hUsub,hU,hU0⟩ := _root_.mem_nhds_iff.mp hp
  filter_upwards [hU.mem_nhds hU0] with z hz
  apply e.isClosed_cone.mem_of_frequently_of_tendsto _ (tuple_analytic e (child p k c) z).continuousAt.tendsto
  apply ((frequently_first_ne z).and_eventually (hU.mem_nhds hz)).mono
  intro w hw
  obtain ⟨x,hx⟩ := hUsub hw.2
  rw [tuple_child e p k hI c w] at hx
  exact ⟨x,(e.incidence_smul_iff (pow_ne_zero _ hw.1)).mp hx⟩

 

def Admissible (x₀ : X.Carrier) (p : Fin (e.N+1) → P) (A B : P) : Prop :=
  (∀ᶠ w in 𝓝 (0 : ℂ × ℂ), ∃ x, e.Incidence x (tuple e p w)) ∧
  (∀ᶠ w in 𝓝 (0 : ℂ × ℂ), tuple e p w ≠ 0 →
    S.WedgeAt (lift e x₀ p) (value A) w ∧ S.swap.WedgeAt (lift e x₀ p) (value B) w)

lemma value_child_coordinate (A : P) (c : ℂ) :
    value (shift (0,c) (blowup A)) = fun w : ℂ × ℂ => value A (w.1,w.1*(w.2+c)) := by
  funext w
  rw [value_shift,value_blowup]
  simp only [Prod.fst_add,Prod.snd_add,add_zero]

lemma lift_child_eq (x₀ : X.Carrier) {p : Fin (e.N+1) → P} (k : ℕ)
    (hI : baseIdeal p ≤ highOrder k) (c : ℂ) {w : ℂ × ℂ} (hw : w.1 ≠ 0)
    (hc : ∃ x, e.Incidence x (tuple e (child p k c) w)) :
    lift e x₀ (child p k c) w = lift e x₀ p (w.1,w.1*(w.2+c)) := by
  dsimp only [lift]
  rw [tuple_child e p k hI c w,e.coneLift_smul x₀ (pow_ne_zero _ hw) hc]

lemma admissible_child [CompactSpace X.Carrier] (x₀ : X.Carrier)
    {p : Fin (e.N+1) → P} {A B : P} (k : ℕ) (hI : baseIdeal p ≤ highOrder k)
    (c : ℂ) (hp : Admissible e S x₀ p A B) :
    Admissible e S x₀ (child p k c) (shift (0,c) (blowup A)) (shift (0,c) (blowup B)) := by
  have hc := cone_child e k hI c hp.1
  refine ⟨hc,?_⟩
  let β : ℂ × ℂ → ℂ × ℂ := fun w => (w.1,w.1*(w.2+c))
  have hβ : ContDiff ℂ ω β := blowup_contDiff c
  have hβ0 : β 0 = 0 := by simp [β]
  obtain ⟨V,hVsub,hV,hV0⟩ := _root_.mem_nhds_iff.mp (hp.1.and hp.2)
  obtain ⟨U₀,hU₀sub,hU₀,hU₀0⟩ := _root_.mem_nhds_iff.mp hc
  let U := U₀ ∩ β ⁻¹' V
  have hU : IsOpen U := hU₀.inter (hV.preimage hβ.continuous)
  have hU0 : (0 : ℂ × ℂ) ∈ U := ⟨hU₀0,by change β 0 ∈ V; rw [hβ0]; exact hV0⟩
  have hhol (z : ℂ × ℂ) (hz : z ∈ U) (hn : tuple e (child p k c) z ≠ 0) :
      ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω (lift e x₀ (child p k c)) z :=
    lift_holomorphic e x₀ hn (Filter.Eventually.mono (hU₀.mem_nhds hz.1) hU₀sub)
  have hoff (z : ℂ × ℂ) (hz : z ∈ U) (hx : z.1 ≠ 0)
      (hn : tuple e (child p k c) z ≠ 0) :
      S.WedgeAt (lift e x₀ (child p k c)) (value (shift (0,c) (blowup A))) z ∧
      S.swap.WedgeAt (lift e x₀ (child p k c)) (value (shift (0,c) (blowup B))) z := by
    have hnparent : tuple e p (β z) ≠ 0 := by
      rw [tuple_child e p k hI c z]
      exact smul_ne_zero (pow_ne_zero _ hx) hn
    have hFp := lift_holomorphic e x₀ hnparent (Filter.Eventually.mono (hV.mem_nhds hz.2) (fun w hw => (hVsub hw).1))
    have heq : lift e x₀ (child p k c) =ᶠ[𝓝 z] lift e x₀ p ∘ β := by
      filter_upwards [hU₀.mem_nhds hz.1,continuous_fst.continuousAt.eventually_ne hx] with w hw hxw
      exact lift_child_eq e x₀ k hI c hxw (hU₀sub hw)
    have hW := (hVsub hz.2).2 hnparent
    constructor
    · have h := hW.1.comp S hFp (value_analytic A (β z)).differentiableAt (hβ.differentiable (by simp) z)
      apply h.congr S heq.symm
      exact Filter.Eventually.of_forall (fun w => (congrFun (value_child_coordinate A c) w).symm)
    · have h := hW.2.comp S.swap hFp (value_analytic B (β z)).differentiableAt (hβ.differentiable (by simp) z)
      apply h.congr S.swap heq.symm
      exact Filter.Eventually.of_forall (fun w => (congrFun (value_child_coordinate B c) w).symm)
  filter_upwards [hU.mem_nhds hU0] with z hz hn
  have hfreq := (frequently_first_ne z).and_eventually
    (Filter.Eventually.and (hU.mem_nhds hz) ((tuple_analytic e (child p k c) z).continuousAt.eventually_ne hn))
  constructor
  · apply S.wedgeAt_of_frequently (hhol z hz hn) (value_analytic _ z)
    exact hfreq.mono (fun w hw => (hoff w hw.2.1 hw.1 hw.2.2).1)
  · apply S.swap.wedgeAt_of_frequently (hhol z hz hn) (value_analytic _ z)
    exact hfreq.mono (fun w hw => (hoff w hw.2.1 hw.1 hw.2.2).2)

lemma tuple_swap (p : Fin (e.N+1) → P) (w : ℂ × ℂ) :
    tuple e (fun i => swap (p i)) w = tuple e p w.swap := by
  ext i; exact value_swap (p i) w

lemma admissible_swap [CompactSpace X.Carrier] (x₀ : X.Carrier)
    {p : Fin (e.N+1) → P} {A B : P} (hp : Admissible e S x₀ p A B) :
    Admissible e S x₀ (fun i => swap (p i)) (swap A) (swap B) := by
  have hσ : ContDiff ℂ ω (Prod.swap : ℂ × ℂ → ℂ × ℂ) := contDiff_snd.prodMk contDiff_fst
  have h0 : Prod.swap (0 : ℂ × ℂ) = 0 := rfl
  have hq := hσ.continuous.continuousAt.tendsto.eventually (h0 ▸ hp.1)
  refine ⟨?_,?_⟩
  · simpa only [tuple_swap] using hq
  · obtain ⟨U,hUsub,hU,hU0⟩ := _root_.mem_nhds_iff.mp (hp.1.and hp.2)
    have hnear := hσ.continuous.continuousAt.tendsto.eventually (h0 ▸ hU.mem_nhds hU0)
    filter_upwards [hnear] with z hz hn
    rw [tuple_swap] at hn
    have hF := lift_holomorphic e x₀ hn (Filter.Eventually.mono (hU.mem_nhds hz) (fun w hw => (hUsub hw).1))
    have hW := (hUsub hz).2 hn
    have heq : lift e x₀ p ∘ Prod.swap = lift e x₀ (fun i => swap (p i)) := by
      funext w; dsimp only [lift,Function.comp_apply]; rw [tuple_swap]
    have hAe : value A ∘ Prod.swap = value (swap A) := by funext w; exact (value_swap A w).symm
    have hBe : value B ∘ Prod.swap = value (swap B) := by funext w; exact (value_swap B w).symm
    constructor
    · simpa only [heq,hAe] using hW.1.comp S hF (value_analytic A z.swap).differentiableAt (hσ.differentiable (by simp) z)
    · simpa only [heq,hBe] using hW.2.comp S.swap hF (value_analytic B z.swap).differentiableAt (hσ.differentiable (by simp) z)

lemma isolated_swap {p : Fin (e.N+1) → P} (hp : IsolatedAtOrigin p) :
    IsolatedAtOrigin (fun i => swap (p i)) := by
  have ht : Tendsto (Prod.swap : ℂ × ℂ → ℂ × ℂ) (𝓝 0) (𝓝 0) := continuous_swap.continuousAt
  filter_upwards [ht.eventually hp] with w hw hn
  have H := hw (fun i => (value_swap (p i) w).symm.trans (hn i))
  have := congrArg Prod.swap H
  simpa only [Prod.swap_swap,Prod.swap_zero] using this

lemma tuple_shift (p : Fin (e.N+1) → P) (a w : ℂ × ℂ) :
    tuple e (fun i => shift a (p i)) w = tuple e p (w+a) := by
  ext i; exact value_shift (p i) a w

lemma regular_shift_data [CompactSpace X.Carrier] (x₀ : X.Carrier)
    {p : Fin (e.N+1) → P} {A B : P} (a : ℂ × ℂ)
    (hp : Admissible e S x₀ (fun i => shift a (p i)) (shift a A) (shift a B))
    (hn : tuple e (fun i => shift a (p i)) 0 ≠ 0) :
    ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω (lift e x₀ p) a ∧
    ∀ᶠ w in 𝓝 a, S.WedgeAt (lift e x₀ p) (value A) w ∧ S.swap.WedgeAt (lift e x₀ p) (value B) w := by
  let f : ℂ × ℂ → ℂ × ℂ := fun w => w-a
  have hf : ContDiff ℂ ω f := contDiff_id.sub contDiff_const
  have hf0 : f a = 0 := sub_self a
  have hF := lift_holomorphic e x₀ hn hp.1
  have heq : lift e x₀ (fun i => shift a (p i)) ∘ f = lift e x₀ p := by
    funext w
    dsimp only [lift,Function.comp_apply]
    rw [tuple_shift]
    simp only [f,sub_add_cancel]
  have hAe : value (shift a A) ∘ f = value A := by funext w; simp only [Function.comp_apply,value_shift,f,sub_add_cancel]
  have hBe : value (shift a B) ∘ f = value B := by funext w; simp only [Function.comp_apply,value_shift,f,sub_add_cancel]
  constructor
  · rw [← heq]
    exact (hf0 ▸ hF).comp a hf.contMDiff.contMDiffAt
  · have hh := (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hF
    have hnear : ∀ᶠ z in 𝓝 (0 : ℂ × ℂ),
        ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω (lift e x₀ (fun i => shift a (p i))) z ∧
        S.WedgeAt (lift e x₀ (fun i => shift a (p i))) (value (shift a A)) z ∧
        S.swap.WedgeAt (lift e x₀ (fun i => shift a (p i))) (value (shift a B)) z := by
      filter_upwards [hh,hp.2,(tuple_analytic e (fun i => shift a (p i)) 0).continuousAt.eventually_ne hn] with z hz hw hnz
      exact ⟨hz,hw hnz⟩
    filter_upwards [hf.continuous.continuousAt.tendsto.eventually (hf0 ▸ hnear)] with w hw
    constructor
    · simpa only [heq,hAe] using hw.2.1.comp S hw.1 (value_analytic (shift a A) (f w)).differentiableAt (hf.differentiable (by simp) w)
    · simpa only [heq,hBe] using hw.2.2.comp S.swap hw.1 (value_analytic (shift a B) (f w)).differentiableAt (hf.differentiable (by simp) w)

lemma transformed_curve_data [CompactSpace X.Carrier] (x₀ : X.Carrier)
    {p : Fin (e.N+1) → P} {A B : P} (k : ℕ) (hI : baseIdeal p ≤ highOrder k)
    (hp : Admissible e S x₀ p A B)
    (hn : ∀ c : ℂ, tuple e (child p k c) 0 ≠ 0) :
    ∀ c : ℂ,
      ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω (lift e x₀ (fun i => polynomialTransform k (p i))) (0,c) ∧
      ∀ᶠ w in 𝓝 (0,c),
        S.WedgeAt (lift e x₀ (fun i => polynomialTransform k (p i))) (value (blowup A)) w ∧
        S.swap.WedgeAt (lift e x₀ (fun i => polynomialTransform k (p i))) (value (blowup B)) w := by
  intro c
  exact regular_shift_data e S x₀ (0,c) (admissible_child e S x₀ k hI c hp) (hn c)

lemma transformed_curve_constant [CompactSpace X.Carrier] (x₀ : X.Carrier)
    {p : Fin (e.N+1) → P} {A B : P} (k : ℕ) (hI : baseIdeal p ≤ highOrder k)
    (hp : Admissible e S x₀ p A B)
    (hA : A ≠ 0) (hA0 : value A 0 = 0) (hB : B ≠ 0) (hB0 : value B 0 = 0)
    (hn : ∀ c : ℂ, tuple e (child p k c) 0 ≠ 0) (z w : ℂ) :
    lift e x₀ (fun i => polynomialTransform k (p i)) (0,z) =
    lift e x₀ (fun i => polynomialTransform k (p i)) (0,w) := by
  obtain ⟨n,a,ha,hna⟩ := coordinate_exceptional_factor hA hA0
  obtain ⟨m,b,hb,hnb⟩ := coordinate_exceptional_factor hB hB0
  have hea : value (blowup A) = fun w : ℂ × ℂ => w.1^(n+1)*value a w := by
    funext w; rw [ha,value_mul,value_pow,value_X₀]
  have heb : value (blowup B) = fun w : ℂ × ℂ => w.1^(m+1)*value b w := by
    funext w; rw [hb,value_mul,value_pow,value_X₀]
  have hfinite : Set.Finite {z : ℂ | value a (0,z) = 0 ∨ value b (0,z) = 0} := by
    have H := (Polynomial.finite_setOfPred_isRoot hna).union (Polynomial.finite_setOfPred_isRoot hnb)
    simpa only [Set.ofPred_or, Polynomial.IsRoot,linePolynomial_eval] using H
  have hd := transformed_curve_data e S x₀ k hI hp hn
  apply S.constant_exceptional n m (fun c => (hd c).1) (fun c => value_analytic a (0,c))
    (fun c => value_analytic b (0,c)) hfinite _ _ z w
  · intro c
    simpa only [← hea] using (hd c).2.mono (fun w hw => hw.1)
  · intro c
    simpa only [← heb] using (hd c).2.mono (fun w hw => hw.2)

lemma tuple_transformed_factor (p : Fin (e.N+1) → P) (k : ℕ) (hI : baseIdeal p ≤ highOrder k)
    (w : ℂ × ℂ) : tuple e p (AffineBlowup.first w) =
      w.1^k • tuple e (fun i => polynomialTransform k (p i)) w := by
  have hc : child p k 0 = fun i => polynomialTransform k (p i) := by
    funext i; exact shift_zero _
  simpa only [hc,add_zero,AffineBlowup.first] using tuple_child e p k hI 0 w

lemma transformed_lift_near (x₀ : X.Carrier) {p : Fin (e.N+1) → P}
    (k : ℕ) (hI : baseIdeal p ≤ highOrder k)
    (hc : ∀ᶠ w in 𝓝 (0 : ℂ × ℂ), ∃ x, e.Incidence x (tuple e p w)) (c : ℂ) :
    ∀ᶠ w in 𝓝 (0,c), w.1 ≠ 0 →
      lift e x₀ (fun i => polynomialTransform k (p i)) w = lift e x₀ p (AffineBlowup.first w) := by
  have ht : Tendsto AffineBlowup.first (𝓝 (0,c)) (𝓝 (0 : ℂ × ℂ)) := by
    change Tendsto (fun w : ℂ × ℂ => (w.1,w.1*w.2)) _ _
    simpa only [AffineBlowup.first,Pi.mul_apply,Prod.fst,Prod.snd,zero_mul,Prod.mk_zero_zero] using
      (continuous_fst.prodMk (continuous_fst.mul continuous_snd)).tendsto ((0,c) : ℂ × ℂ)
  filter_upwards [ht.eventually hc] with w hw hx
  have hd := tuple_transformed_factor e p k hI w
  have hc' : ∃ x, e.Incidence x (tuple e (fun i => polynomialTransform k (p i)) w) := by
    obtain ⟨x,hh⟩ := hw
    rw [hd] at hh
    exact ⟨x,(e.incidence_smul_iff (pow_ne_zero _ hx)).mp hh⟩
  dsimp only [lift]
  rw [hd,e.coneLift_smul x₀ (pow_ne_zero _ hx) hc']

lemma lift_swap (x₀ : X.Carrier) (p : Fin (e.N+1) → P) (w : ℂ × ℂ) :
    lift e x₀ (fun i => swap (p i)) w = lift e x₀ p w.swap := by
  dsimp only [lift]; rw [tuple_swap]

 

theorem nonzero_of_regular_children [CompactSpace X.Carrier] (x₀ : X.Carrier)
    {p : Fin (e.N+1) → P} {A B : P} (k : ℕ) (hI : baseIdeal p ≤ highOrder k)
    (hIs : baseIdeal (fun i => swap (p i)) ≤ highOrder k)
    (hp : Admissible e S x₀ p A B) (hiso : IsolatedAtOrigin p)
    (hA : A ≠ 0) (hA0 : value A 0 = 0) (hB : B ≠ 0) (hB0 : value B 0 = 0)
    (hn₁ : ∀ c : ℂ, tuple e (child p k c) 0 ≠ 0)
    (hn₂ : ∀ c : ℂ, tuple e (child (fun i => swap (p i)) k c) 0 ≠ 0) : tuple e p 0 ≠ 0 := by
  classical
  let ps : Fin (e.N+1) → P := fun i => swap (p i)
  let G₁ := lift e x₀ (fun i => polynomialTransform k (p i))
  let G₂ := lift e x₀ (fun i => polynomialTransform k (ps i))
  have hs := admissible_swap e S x₀ hp
  have hA' : swap A ≠ 0 := fun h => hA (polynomial_swap_injective (h.trans (map_zero swap).symm))
  have hB' : swap B ≠ 0 := fun h => hB (polynomial_swap_injective (h.trans (map_zero swap).symm))
  have hA0' : value (swap A) 0 = 0 := by simpa only [value_swap,Prod.fst_zero,Prod.snd_zero,Prod.mk_zero_zero] using hA0
  have hB0' : value (swap B) 0 = 0 := by simpa only [value_swap,Prod.fst_zero,Prod.snd_zero,Prod.mk_zero_zero] using hB0
  have hg₁ (z : ℂ) : ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω G₁ (0,z) :=
    (transformed_curve_data e S x₀ k hI hp hn₁ z).1
  have hg₂ (z : ℂ) : ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω G₂ (0,z) :=
    (transformed_curve_data e S x₀ k hIs hs hn₂ z).1
  have hc₁ (z w : ℂ) : G₁ (0,z) = G₁ (0,w) :=
    transformed_curve_constant e S x₀ k hI hp hA hA0 hB hB0 hn₁ z w
  have hc₂ (z w : ℂ) : G₂ (0,z) = G₂ (0,w) :=
    transformed_curve_constant e S x₀ k hIs hs hA' hA0' hB' hB0' hn₂ z w
  have hf₁ (z : ℂ) : ∀ᶠ w in 𝓝 (0,z), w.1 ≠ 0 → G₁ w = lift e x₀ p (AffineBlowup.first w) :=
    transformed_lift_near e x₀ k hI hp.1 z
  have hf₂ (z : ℂ) : ∀ᶠ w in 𝓝 (0,z), w.1 ≠ 0 → G₂ w = lift e x₀ p (AffineBlowup.second w) := by
    filter_upwards [transformed_lift_near e x₀ k hIs hs.1 z] with w hw hx
    change lift e x₀ (fun i => polynomialTransform k (swap (p i))) w = _
    rw [hw hx,lift_swap]
    rfl
  have hcommon : G₁ (0,1) = G₂ (0,1) := by
    have ht : Tendsto (fun r : ℂ => (r,1)) (𝓝[≠] 0) (𝓝 ((0,1) : ℂ × ℂ)) :=
      (continuousAt_id.prodMk continuousAt_const).mono_left nhdsWithin_le_nhds
    apply tendsto_nhds_unique_of_eventuallyEq ((hg₁ 1).continuousAt.tendsto.comp ht)
      ((hg₂ 1).continuousAt.tendsto.comp ht)
    filter_upwards [ht.eventually (hf₁ 1),ht.eventually (hf₂ 1),self_mem_nhdsWithin] with r hr₁ hr₂ hr
    dsimp only [Function.comp_apply]
    rw [hr₁ hr,hr₂ hr]
    simp only [AffineBlowup.first,AffineBlowup.second,mul_one]
  have hlim : Tendsto (lift e x₀ p) (𝓝[≠] (0 : ℂ × ℂ)) (𝓝 (G₁ (0,0))) := by
    apply AffineBlowup.tendsto_of_local_constant_exceptional
      (fun z _ => (hg₁ z).continuousAt) (fun z _ => (hg₂ z).continuousAt)
      (fun z _ => hc₁ z 0) (fun z _ => (hc₂ z 1).trans (hcommon.symm.trans (hc₁ 1 0)))
      (fun z _ => hf₁ z) (fun z _ => hf₂ z)
  let F := Function.update (lift e x₀ p) 0 (G₁ (0,0))
  have hF : ContinuousAt F 0 := continuousAt_update_same.mpr hlim
  have heq : F =ᶠ[𝓝[≠] (0 : ℂ × ℂ)] lift e x₀ p := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact Function.update_of_ne hw _ _
  apply e.nonzero_of_continuous_incidence (tuple_analytic e p 0) hF
  · filter_upwards [hiso.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with w hw hn hz
    exact hn (hw (fun i => congrFun hz i))
  · filter_upwards [hp.1.filter_mono nhdsWithin_le_nhds,heq] with w hw he
    rw [he]
    exact e.coneLift_incidence x₀ hw

lemma child_coordinate_nonzero {A : P} (hA : A ≠ 0) (c : ℂ) :
    shift (0,c) (blowup A) ≠ 0 := by
  intro h
  apply hA
  apply blowup_injective
  apply shift_injective (0,c)
  simpa only [map_zero] using h

lemma child_coordinate_origin {A : P} (hA : value A 0 = 0) (c : ℂ) :
    value (shift (0,c) (blowup A)) 0 = 0 := by
  simpa only [value_shift,zero_add,value_blowup,Prod.fst,Prod.snd,zero_mul,Prod.mk_zero_zero] using hA

lemma swap_child_isolated {p : Fin (e.N+1) → P} (k : ℕ)
    (hI : baseIdeal p ≤ highOrder k) (f : baseIdeal p)
    (a b : ℕ) (hab : a+b=k) (hf : MvPowerSeries.coeff (FormalBlowup.exp a b) (f : D) ≠ 0)
    (hp : IsolatedAtOrigin p) (c : ℂ) : IsolatedAtOrigin (child (fun i => swap (p i)) k c) := by
  have hs : baseIdeal (fun i => swap (p i)) ≤ highOrder k := by
    rw [← swap_baseIdeal]
    exact FormalBlowup.swapIdeal_le_highOrder _ k hI
  have hm : FormalBlowup.swap (f : D) ∈ baseIdeal (fun i => swap (p i)) := by
    rw [← swap_baseIdeal]
    exact Ideal.mem_map_of_mem _ f.property
  have ho : (FormalBlowup.swap (f : D)).order = k := by
    rw [FormalBlowup.order_swap]
    exact FormalBlowup.order_eq_of_initial k f (hI f.property) a b hab hf
  obtain ⟨a',b',hab',hf'⟩ := FormalBlowup.initial_of_order_eq k _ ho
  exact child_isolated _ k hs ⟨_,hm⟩ a' b' hab' hf' (isolated_swap e hp) c

 

theorem no_basepoint [CompactSpace X.Carrier] (x₀ : X.Carrier)
    (p : Fin (e.N+1) → P) [FiniteDimensional ℂ (D ⧸ baseIdeal p)]
    (A B : P) (hp : Admissible e S x₀ p A B) (hiso : IsolatedAtOrigin p)
    (hA : A ≠ 0) (hA0 : value A 0 = 0) (hB : B ≠ 0) (hB0 : value B 0 = 0) :
    tuple e p 0 ≠ 0 := by
  classical
  generalize hn : Module.finrank ℂ (D ⧸ baseIdeal p) = n
  induction n using Nat.strong_induction_on generalizing p A B with
  | h n ih =>
    by_cases ht : baseIdeal p = ⊤
    · obtain ⟨i,hi⟩ := (baseIdeal_eq_top_iff p).mp ht
      exact fun h => hi (congrFun h i)
    · obtain ⟨k,hk,hI,f,a,b,hab,hf⟩ := FormalBlowup.exists_minimal_order (baseIdeal p) ht
      have hs : baseIdeal (fun i => swap (p i)) ≤ highOrder k := by
        rw [← swap_baseIdeal]
        exact FormalBlowup.swapIdeal_le_highOrder _ k hI
      apply nonzero_of_regular_children e S x₀ k hI hs hp hiso hA hA0 hB hB0
      · intro c
        obtain ⟨hfin,hlt⟩ := child_finite_drop p k hk hI f a b hab hf c
        let := hfin
        apply ih _ (by omega) (child p k c) (shift (0,c) (blowup A)) (shift (0,c) (blowup B))
          (admissible_child e S x₀ k hI c hp) (child_isolated p k hI f a b hab hf hiso c)
          (child_coordinate_nonzero hA c) (child_coordinate_origin hA0 c)
          (child_coordinate_nonzero hB c) (child_coordinate_origin hB0 c) rfl
      · intro c
        obtain ⟨hfin,hlt⟩ := swap_child_finite_drop p k hk hI f a b hab hf c
        let := hfin
        have hA' : swap A ≠ 0 := fun h => hA (polynomial_swap_injective (h.trans (map_zero swap).symm))
        have hB' : swap B ≠ 0 := fun h => hB (polynomial_swap_injective (h.trans (map_zero swap).symm))
        have hA0' : value (swap A) 0 = 0 := by simpa only [value_swap,Prod.fst_zero,Prod.snd_zero,Prod.mk_zero_zero] using hA0
        have hB0' : value (swap B) 0 = 0 := by simpa only [value_swap,Prod.fst_zero,Prod.snd_zero,Prod.mk_zero_zero] using hB0
        apply ih _ (by omega) (child (fun i => swap (p i)) k c)
          (shift (0,c) (blowup (swap A))) (shift (0,c) (blowup (swap B)))
          (admissible_child e S x₀ k hs c (admissible_swap e S x₀ hp))
          (swap_child_isolated e k hI f a b hab hf hiso c)
          (child_coordinate_nonzero hA' c) (child_coordinate_origin hA0' c)
          (child_coordinate_nonzero hB' c) (child_coordinate_origin hB0' c) rfl

 

theorem nonzero_everywhere [CompactSpace X.Carrier] (x₀ : X.Carrier)
    (p : Fin (e.N+1) → P) (A B : P)
    (hB : Set.Finite {w : ℂ × ℂ | ∀ j, value (p j) w = 0})
    (hcone : ∀ w, ∃ x, e.Incidence x (tuple e p w))
    (hreg : ∀ w, tuple e p w ≠ 0 →
      S.WedgeAt (lift e x₀ p) (value A) w ∧ S.swap.WedgeAt (lift e x₀ p) (value B) w)
    (hA : ∀ c : ℂ, A ≠ MvPolynomial.C c) (hB' : ∀ c : ℂ, B ≠ MvPolynomial.C c)
    (a : ℂ × ℂ) : tuple e p a ≠ 0 := by
  let p' := fun i => shift a (p i)
  let A' := shift a (A - MvPolynomial.C (value A a))
  let B' := shift a (B - MvPolynomial.C (value B a))
  have hfin := finite_zeros_shift p hB a
  let := finite_colength_of_finite_zeros p' hfin
  have hi : IsolatedAtOrigin p' := finite_isolated hfin 0
  let β : ℂ × ℂ → ℂ × ℂ := fun w => w+a
  have hβ : ContDiff ℂ ω β := contDiff_id.add contDiff_const
  have hF : lift e x₀ p' = lift e x₀ p ∘ β := by
    funext w; dsimp only [lift,Function.comp_apply,β,p']; rw [tuple_shift]
  have hAeq : value A' = (fun w => value A w - value A a) ∘ β := by
    funext w; simp only [A',Function.comp_apply,β,value_shift,value_sub,value_C]
  have hBeq : value B' = (fun w => value B w - value B a) ∘ β := by
    funext w; simp only [B',Function.comp_apply,β,value_shift,value_sub,value_C]
  have had : Admissible e S x₀ p' A' B' := by
    refine ⟨Filter.Eventually.of_forall ?_,Filter.Eventually.of_forall ?_⟩
    · intro w; simpa only [p',tuple_shift] using hcone (w+a)
    · intro w hw
      have hn : tuple e p (β w) ≠ 0 := by simpa only [p',tuple_shift,β] using hw
      have hh := hreg (β w) hn
      have hhol := lift_holomorphic e x₀ hn (Filter.Eventually.of_forall hcone)
      have hwa : S.WedgeAt (lift e x₀ p) (fun w => value A w - value A a) (β w) := by
        simpa only [TangentSplitting.WedgeAt,fderiv_sub_const] using hh.1
      have hwb : S.swap.WedgeAt (lift e x₀ p) (fun w => value B w - value B a) (β w) := by
        simpa only [TangentSplitting.WedgeAt,fderiv_sub_const] using hh.2
      rw [hF,hAeq,hBeq]
      exact ⟨hwa.comp S hhol ((value_analytic A _).differentiableAt.sub_const _) (hβ.differentiable (by simp) w),
        hwb.comp S.swap hhol ((value_analytic B _).differentiableAt.sub_const _) (hβ.differentiable (by simp) w)⟩
  have hAn : A' ≠ 0 := by
    intro hz
    exact hA _ (sub_eq_zero.mp (shift_injective a (hz.trans (map_zero (shift a)).symm)))
  have hBn : B' ≠ 0 := by
    intro hz
    exact hB' _ (sub_eq_zero.mp (shift_injective a (hz.trans (map_zero (shift a)).symm)))
  have hA0 : value A' 0 = 0 := by rw [hAeq]; simp only [Function.comp_apply,β,zero_add,sub_self]
  have hB0 : value B' 0 = 0 := by rw [hBeq]; simp only [Function.comp_apply,β,zero_add,sub_self]
  have hh := no_basepoint e S x₀ p' A' B' had hi hAn hA0 hBn hB0
  simpa only [p',tuple_shift,zero_add] using hh

end SplitTangent.BasePointRemoval

namespace SplitTangent.TangentSplitting
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

lemma wedges_of_pde {F : ℂ × ℂ → X.Carrier} {z : ℂ × ℂ}
    (hpde : mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F z (0,1) =
      S.projector (F z) (mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F z (1,0))) :
    S.WedgeAt F (fun w => w.1+w.2) z ∧ S.swap.WedgeAt F Prod.fst z := by
  let d : (ℂ × ℂ) →L[ℂ] TangentSpace (ModelWithCorners X) (F z) :=
    mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F z
  have hde : d (0,1) = S.projector (F z) (d (1,0)) := hpde
  have hd (w : ℂ × ℂ) : d w = w.1 • d (1,0) + w.2 • d (0,1) := by
    have hw : w = w.1 • (1,0) + w.2 • (0,1) := by ext <;> simp
    conv_lhs => rw [hw]
    rw [map_add,map_smul,map_smul]
  have hp (w : ℂ × ℂ) : S.projector (F z) (d w) =
      (w.1+w.2) • S.projector (F z) (d (1,0)) := by
    rw [hd,map_add,map_smul,map_smul,hde,S.idempotent,add_smul]
  have hq (w : ℂ × ℂ) : S.swap.projector (F z) (d w) =
      w.1 • S.swap.projector (F z) (d (1,0)) := by
    change d w - S.projector (F z) (d w) = w.1 • (d (1,0) - S.projector (F z) (d (1,0)))
    rw [hp,hd,hde,add_smul,smul_sub]
    abel
  have hda : fderiv ℂ (fun w : ℂ × ℂ => w.1+w.2) z =
      ContinuousLinearMap.fst ℂ ℂ ℂ + ContinuousLinearMap.snd ℂ ℂ ℂ :=
    (hasFDerivAt_fst.add hasFDerivAt_snd).fderiv
  have hdb : fderiv ℂ (Prod.fst : ℂ × ℂ → ℂ) z = ContinuousLinearMap.fst ℂ ℂ ℂ :=
    hasFDerivAt_fst.fderiv
  constructor
  · intro v w
    change fderiv ℂ (fun w : ℂ × ℂ => w.1+w.2) z v • S.projector (F z) (d w) =
      fderiv ℂ (fun w : ℂ × ℂ => w.1+w.2) z w • S.projector (F z) (d v)
    rw [hda,hp w,hp v]
    change (v.1+v.2) • ((w.1+w.2) • _) = (w.1+w.2) • ((v.1+v.2) • _)
    rw [smul_smul,smul_smul,mul_comm]
  · intro v w
    change fderiv ℂ (Prod.fst : ℂ × ℂ → ℂ) z v • S.swap.projector (F z) (d w) =
      fderiv ℂ (Prod.fst : ℂ × ℂ → ℂ) z w • S.swap.projector (F z) (d v)
    rw [hdb,hq w,hq v]
    change v.1 • (w.1 • _) = w.1 • (v.1 • _)
    rw [smul_smul,smul_smul,mul_comm]

end SplitTangent.TangentSplitting

namespace SplitTangent.ComplexManifold
open Filter Topology
variable {X : ComplexManifold.{u}}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma equality_local_equations {F G : E → X.Carrier} {z : E}
    (hF : ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z)
    (hG : ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω G z) :
    ∃ f : E → ℂ × Model X, AnalyticAt ℂ f z ∧
      ∀ᶠ w in 𝓝 z, F w = G w ↔ f w = 0 := by
  classical
  by_cases he : F z = G z
  · let c := chartAt (Model X) (F z)
    have hFc : F z ∈ c.source := mem_chart_source (Model X) (F z)
    have hGc : G z ∈ c.source := he ▸ hFc
    have hc := IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) (F z)
    have hFA := ((contMDiffAt_of_mem_maximalAtlas hc hFc).comp z hF).contDiffAt.analyticAt
    have hGA := ((contMDiffAt_of_mem_maximalAtlas hc hGc).comp z hG).contDiffAt.analyticAt
    refine ⟨fun w => (0,c (F w)-c (G w)), analyticAt_const.prod (hFA.sub hGA),?_⟩
    filter_upwards [hF.continuousAt.eventually (c.open_source.mem_nhds hFc),
      hG.continuousAt.eventually (c.open_source.mem_nhds hGc)] with w hwF hwG
    constructor
    · intro h; simp only [h,sub_self,Prod.zero_eq_mk]
    · intro h
      have hh := congrArg Prod.snd h
      exact c.injOn hwF hwG (sub_eq_zero.mp hh)
  · refine ⟨fun _ => (1,0),analyticAt_const,?_⟩
    have hn : ∀ᶠ w in 𝓝 z, F w ≠ G w :=
      (hF.continuousAt.prodMk hG.continuousAt).eventually
        (isClosed_diagonal.isOpen_compl.mem_nhds he)
    filter_upwards [hn] with w hw
    simp only [hw,Prod.zero_eq_mk,Prod.mk.injEq,one_ne_zero,false_and]

 
theorem eqOn_of_eventuallyEq {F G : E → X.Carrier} {U : Set E}
    (hU : IsPreconnected U)
    (hF : ∀ z ∈ U, ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z)
    (hG : ∀ z ∈ U, ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω G z)
    {a : E} (ha : a ∈ U) (he : F =ᶠ[𝓝 a] G) : Set.EqOn F G U := by
  exact AnalyticContinuation.subset_of_local_analytic_equations hU
    (fun z hz => equality_local_equations (hF z hz) (hG z hz))
    ⟨a,ha,mem_interior_iff_mem_nhds.mpr he⟩

end SplitTangent.ComplexManifold

namespace SplitTangent.RationalSurface
open PolynomialBlowup

def toMv : B →+* P :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)) (MvPolynomial.X 1)

lemma value_toMv (p : B) (w : ℂ × ℂ) : value (toMv p) w = eval p w := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa [toMv,value,valueHom,eval,map_add] using congrArg₂ (· + ·) hp hq
  | monomial n p =>
    simp only [toMv,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_monomial,eval,
      value,valueHom,map_mul,map_pow,MvPolynomial.aeval_X,Matrix.cons_val_one,Matrix.cons_val_zero]
    congr 1
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [Polynomial.eval₂_add,map_add] using congrArg₂ (· + ·) hp hq
    | monomial m c => simp

end SplitTangent.RationalSurface

namespace SplitTangent.TangentSplitting
section
open Filter Topology PolynomialBlowup BasePointRemoval
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

theorem exists_affine_polynomial_tangent_box [CompactSpace X.Carrier]
    (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ (z : ℂ) (P : Fin (e.N+1) → Polynomial (Polynomial ℂ)) (F : ℂ × ℂ → X.Carrier),
      (∀ w, (fun j => RationalSurface.eval (P j) w) ≠ 0) ∧
      (∀ w, e.Incidence (F w) (fun j => RationalSurface.eval (P j) w)) ∧
      ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F ∧
      (∀ᶠ u in 𝓝 z, F (u,0) = g.finite u) ∧
      (∀ w, mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (0,1) =
        S.projector (F w) (mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (1,0))) := by
  classical
  obtain ⟨z,P,F,hP,hB,hz,hdiag,hF⟩ := S.exists_global_regular_tangent_box e g
  let p := fun j => RationalSurface.toMv (P j)
  let x₀ := g.finite z
  let G := lift e x₀ p
  have htuple (w : ℂ × ℂ) : tuple e p w = fun j => RationalSurface.eval (P j) w := by
    funext j; exact RationalSurface.value_toMv (P j) w
  have hfinite : Set.Finite {w : ℂ × ℂ | ∀ j, value (p j) w = 0} := by
    simpa only [p,RationalSurface.value_toMv] using hB
  have hne (w : ℂ × ℂ) : tuple e p w ≠ 0 ↔ ∃ j, RationalSurface.eval (P j) w ≠ 0 := by
    simp only [htuple,ne_eq,funext_iff,Pi.zero_apply,not_forall]
  have hcone (w : ℂ × ℂ) : ∃ x, e.Incidence x (tuple e p w) := by
    by_cases hw : tuple e p w = 0
    · exact ⟨x₀,hw ▸ e.incidence_zero x₀⟩
    · exact ⟨F w,htuple w ▸ (hF w ((hne w).mp hw)).2.1⟩
  have hagree (w : ℂ × ℂ) (hw : tuple e p w ≠ 0) : G =ᶠ[𝓝 w] F := by
    filter_upwards [(tuple_analytic e p w).continuousAt.eventually_ne hw] with a ha
    exact e.coneLift_eq x₀ ha (htuple a ▸ (hF a ((hne a).mp ha)).2.1)
  have hreg (w : ℂ × ℂ) (hw : tuple e p w ≠ 0) :
      S.WedgeAt G (fun a => a.1+a.2) w ∧ S.swap.WedgeAt G Prod.fst w := by
    have he := hagree w hw
    apply S.wedges_of_pde
    rw [he.mfderiv_eq,he.self_of_nhds]
    exact (hF w ((hne w).mp hw)).2.2
  let A : PolynomialBlowup.P := MvPolynomial.X 0 + MvPolynomial.X 1
  let B : PolynomialBlowup.P := MvPolynomial.X 0
  have hA : value A = fun w : ℂ × ℂ => w.1+w.2 := by funext w; simp [A,value,valueHom]
  have hBB : value B = Prod.fst := by funext w; simp [B,value,valueHom]
  have hAnc (c : ℂ) : A ≠ MvPolynomial.C c := by
    intro he
    have h0 : (0 : ℂ) = c := by simpa [A,value,valueHom] using congrArg (fun q => value q (0,0)) he
    have h1 : (1 : ℂ) = c := by simpa [A,value,valueHom] using congrArg (fun q => value q (1,0)) he
    exact one_ne_zero (h1.trans h0.symm)
  have hBnc (c : ℂ) : B ≠ MvPolynomial.C c := by
    intro he
    have h0 : (0 : ℂ) = c := by simpa [B,value,valueHom] using congrArg (fun q => value q (0,0)) he
    have h1 : (1 : ℂ) = c := by simpa [B,value,valueHom] using congrArg (fun q => value q (1,0)) he
    exact one_ne_zero (h1.trans h0.symm)
  have hnonzero (w : ℂ × ℂ) : tuple e p w ≠ 0 :=
    nonzero_everywhere e S x₀ p A B hfinite hcone (by simpa only [hA,hBB] using hreg) hAnc hBnc w
  refine ⟨z,P,G,?_,?_,?_,?_,?_⟩
  · intro w; simpa only [htuple] using hnonzero w
  · intro w; exact htuple w ▸ e.coneLift_incidence x₀ (hcone w)
  · exact fun w => lift_holomorphic e x₀ (hnonzero w) (Filter.Eventually.of_forall hcone)
  · have he (u : ℂ) : G (u,0) = F (u,0) := (hagree (u,0) (hnonzero _)).self_of_nhds
    simpa only [he] using hdiag
  · intro w
    have he := hagree w (hnonzero w)
    rw [he.mfderiv_eq,he.self_of_nhds]
    exact (hF w ((hne w).mp (hnonzero w))).2.2

theorem exists_affine_tangent_box [CompactSpace X.Carrier]
    (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ (z : ℂ) (F : ℂ × ℂ → X.Carrier),
      ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F ∧
      (∀ᶠ u in 𝓝 z, F (u,0) = g.finite u) ∧
      (∀ w, mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (0,1) =
        S.projector (F w) (mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F w (1,0))) := by
  obtain ⟨z,P,F,hn,hi,hF,hd,hp⟩ := S.exists_affine_polynomial_tangent_box e g
  exact ⟨z,F,hF,hd,hp⟩

end

open Filter Topology
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

theorem exists_affine_box [CompactSpace X.Carrier]
    (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ H : ℂ × ℂ → X.Carrier,
      ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω H ∧
      (∀ u, H (u,u) = g.finite u) ∧
      (∀ w, mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) H w (1,0) ∈ S.first (H w) ∧
        mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) H w (0,1) ∈ S.second (H w)) := by
  obtain ⟨z,F,hF,hdiag,hpde⟩ := S.exists_affine_tangent_box e g
  have hline : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω (fun u : ℂ => F (u,0)) :=
    hF.comp ((contDiff_id.prodMk contDiff_const : ContDiff ℂ ω (fun u : ℂ => (u,(0 : ℂ)))).contMDiff)
  have hdiagall := ComplexManifold.eqOn_of_eventuallyEq isPreconnected_univ
    (fun u _ => hline u) (fun u _ => g.finite_holomorphic u) (mem_univ z) hdiag
  let L : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
    (ContinuousLinearMap.snd ℂ ℂ ℂ).prod
      (ContinuousLinearMap.fst ℂ ℂ ℂ - ContinuousLinearMap.snd ℂ ℂ ℂ)
  let H : ℂ × ℂ → X.Carrier := F ∘ L
  have hL : ContMDiff 𝓘(ℂ,ℂ × ℂ) 𝓘(ℂ,ℂ × ℂ) ω L := L.contDiff.contMDiff
  have hd (w : ℂ × ℂ) : mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) H w =
      (mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F (L w)).comp L := by
    change mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) (F ∘ L) w = _
    rw [mfderiv_comp w ((hF _).mdifferentiableAt (by simp)) ((hL _).mdifferentiableAt (by simp)),
      mfderiv_eq_fderiv,L.fderiv]
    rfl
  refine ⟨H,hF.comp hL,?_,?_⟩
  · intro u
    have he : L (u,u) = (u,0) := by simp [L]
    exact (congrArg F he).trans (hdiagall (mem_univ u))
  · intro w
    let d : (ℂ × ℂ) →L[ℂ] Tangent X (F (L w)) :=
      mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F (L w)
    have he : d (0,1) = S.projector (F (L w)) (d (1,0)) := hpde (L w)
    have hs : L (1,0) = (0,1) := by simp [L]
    have ht : L (0,1) = (1,0) - (0,1) := by simp [L]
    have hds : mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) H w (1,0) = d (0,1) := by
      rw [hd]
      change d (L (1,0)) = _
      rw [hs]
    have hdt : mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) H w (0,1) = d ((1,0)-(0,1)) := by
      rw [hd]
      change d (L (0,1)) = _
      rw [ht]
    constructor
    · change ∃ v, S.projector (H w) v = _
      refine ⟨d (1,0),?_⟩
      rw [hds]
      exact he.symm
    · change S.projector (H w) _ = 0
      rw [hdt]
      change S.projector (F (L w)) (d ((1,0)-(0,1))) = 0
      rw [map_sub,map_sub,he,S.idempotent,sub_self]

end SplitTangent.TangentSplitting

namespace SplitTangent.RationalSurface
open Polynomial

 
def RationalOn (U : Set (ℂ × ℂ)) (f : ℂ × ℂ → ℂ) : Prop :=
  ∃ A D : B, ∀ w ∈ U, eval D w ≠ 0 ∧ f w * eval D w = eval A w

lemma RationalOn.const (U : Set (ℂ × ℂ)) (c : ℂ) : RationalOn U (fun _ => c) := by
  refine ⟨C (C c),1,?_⟩
  intro w hw; simp [eval]

lemma RationalOn.fst (U : Set (ℂ × ℂ)) : RationalOn U Prod.fst := by
  refine ⟨C X,1,?_⟩
  intro w hw; simp [eval]

lemma RationalOn.snd (U : Set (ℂ × ℂ)) : RationalOn U Prod.snd := by
  refine ⟨X,1,?_⟩
  intro w hw; simp [eval]

lemma RationalOn.add {U : Set (ℂ × ℂ)} {f g : ℂ × ℂ → ℂ}
    (hf : RationalOn U f) (hg : RationalOn U g) : RationalOn U (fun w => f w + g w) := by
  obtain ⟨A,D,hf⟩ := hf
  obtain ⟨A',D',hg⟩ := hg
  refine ⟨A*D'+A'*D,D*D',?_⟩
  intro w hw
  obtain ⟨hn,he⟩ := hf w hw
  obtain ⟨hn',he'⟩ := hg w hw
  simp only [eval₂_mul,eval₂_add,eval]
  change eval D w * eval D' w ≠ 0 ∧
    (f w+g w)*(eval D w*eval D' w) = eval A w*eval D' w+eval A' w*eval D w
  exact ⟨mul_ne_zero hn hn',by rw [← he,← he']; ring⟩

lemma RationalOn.neg {U : Set (ℂ × ℂ)} {f : ℂ × ℂ → ℂ}
    (hf : RationalOn U f) : RationalOn U (fun w => -f w) := by
  obtain ⟨A,D,hf⟩ := hf
  refine ⟨-A,D,?_⟩
  intro w hw
  exact ⟨(hf w hw).1,by simpa only [eval,eval₂_neg,neg_mul] using congrArg Neg.neg (hf w hw).2⟩

lemma RationalOn.sub {U : Set (ℂ × ℂ)} {f g : ℂ × ℂ → ℂ}
    (hf : RationalOn U f) (hg : RationalOn U g) : RationalOn U (fun w => f w-g w) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma RationalOn.mul {U : Set (ℂ × ℂ)} {f g : ℂ × ℂ → ℂ}
    (hf : RationalOn U f) (hg : RationalOn U g) : RationalOn U (fun w => f w*g w) := by
  obtain ⟨A,D,hf⟩ := hf
  obtain ⟨A',D',hg⟩ := hg
  refine ⟨A*A',D*D',?_⟩
  intro w hw
  have he := (hf w hw).2
  have he' := (hg w hw).2
  refine ⟨by simpa only [eval,eval₂_mul] using mul_ne_zero (hf w hw).1 (hg w hw).1,?_⟩
  simp only [eval,eval₂_mul]
  change (f w*g w)*(eval D w*eval D' w) = eval A w*eval A' w
  rw [← he,← he']; ring

lemma RationalOn.inv {U : Set (ℂ × ℂ)} {f : ℂ × ℂ → ℂ}
    (hf : RationalOn U f) (hn : ∀ w ∈ U, f w ≠ 0) : RationalOn U (fun w => (f w)⁻¹) := by
  obtain ⟨A,D,hf⟩ := hf
  refine ⟨D,A,?_⟩
  intro w hw
  rw [← (hf w hw).2]
  exact ⟨mul_ne_zero (hn w hw) (hf w hw).1,by rw [← mul_assoc,inv_mul_cancel₀ (hn w hw),one_mul]⟩

lemma rational_polynomial_eval₂ {R' : Type*} [Semiring R'] {U : Set (ℂ × ℂ)}
    (H : (ℂ × ℂ) → R' →+* ℂ) (g : ℂ × ℂ → ℂ)
    (hH : ∀ a, RationalOn U (fun w => H w a)) (hg : RationalOn U g) (p : Polynomial R') :
    RationalOn U (fun w => p.eval₂ (H w) (g w)) := by
  induction p using Polynomial.induction_on with
  | C a => simpa only [Polynomial.eval₂_C] using hH a
  | add p q hp hq => simpa only [eval₂_add] using hp.add hq
  | monomial n a hp =>
      simpa only [pow_succ,← mul_assoc,eval₂_mul,Polynomial.eval₂_X] using hp.mul hg

lemma RationalOn.eval_comp {U : Set (ℂ × ℂ)} {f g : ℂ × ℂ → ℂ}
    (hf : RationalOn U f) (hg : RationalOn U g) (p : B) :
    RationalOn U (fun w => eval p (f w,g w)) := by
  apply rational_polynomial_eval₂ (fun w => Polynomial.evalRingHom (f w)) g _ hg p
  intro a
  exact rational_polynomial_eval₂ (fun _ => RingHom.id ℂ) f (RationalOn.const U) hf a

 

theorem primitive_tuple_of_rational {ι : Type*} [Fintype ι] [Nonempty ι]
    {U : Set (ℂ × ℂ)} (V : ℂ × ℂ → ι → ℂ)
    (hV : ∀ j, RationalOn U (fun w => V w j)) (hn : ∀ w ∈ U, V w ≠ 0) :
    ∃ p : ι → B, Finset.univ.gcd p = 1 ∧
      Set.Finite {w : ℂ × ℂ | ∀ j, eval (p j) w = 0} ∧
      ∀ w ∈ U, ∃ c : ℂ, c ≠ 0 ∧ (fun j => eval (p j) w) = c • V w := by
  classical
  choose A D hD using hV
  let q : ι → B := fun j => A j * ∏ i ∈ Finset.univ.erase j, D i
  obtain ⟨p,hp,hpg⟩ := Finset.extract_gcd q Finset.univ_nonempty
  let d := Finset.univ.gcd q
  have he (j : ι) (w : ℂ × ℂ) : eval (q j) w = eval d w * eval (p j) w := by
    rw [hp j (Finset.mem_univ j)]; exact eval₂_mul _ _
  refine ⟨p,hpg,finite_zero_set p hpg,?_⟩
  intro w hw
  let r := ∏ i, eval (D i) w
  have hr : r ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (hD i w hw).1)
  have hq (j : ι) : eval (q j) w = r * V w j := by
    have hprod := Finset.mul_prod_erase Finset.univ (fun i => eval (D i) w) (Finset.mem_univ j)
    dsimp only [q]
    simp only [eval,eval₂_mul,eval₂_finsetProd]
    change eval (A j) w * (∏ i ∈ Finset.univ.erase j, eval (D i) w) = r * V w j
    rw [← (hD j w hw).2]
    calc
      V w j * eval (D j) w * (∏ i ∈ Finset.univ.erase j, eval (D i) w) =
        V w j * r := by rw [mul_assoc,hprod]
      _ = r * V w j := mul_comm _ _
  have hd : eval d w ≠ 0 := by
    intro hz
    apply hn w hw
    funext j
    have hh := (he j w).symm.trans (hq j)
    change V w j = 0
    apply (mul_eq_zero.mp (by simpa only [hz,zero_mul] using hh.symm)).resolve_left hr
  refine ⟨r / eval d w,div_ne_zero hr hd,?_⟩
  funext j
  change eval (p j) w = (r / eval d w) * V w j
  apply mul_left_cancel₀ hd
  rw [← he,hq]
  field_simp

end SplitTangent.RationalSurface

namespace SplitTangent.TangentSplitting
open Filter Topology Set PolynomialBlowup BasePointRemoval
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

lemma wedges_iff_tangency {F : ℂ × ℂ → X.Carrier} {z : ℂ × ℂ} :
    (S.WedgeAt F Prod.fst z ∧ S.swap.WedgeAt F Prod.snd z) ↔
    (mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F z (1,0) ∈ S.first (F z) ∧
     mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F z (0,1) ∈ S.second (F z)) := by
  let d : (ℂ × ℂ) →L[ℂ] Tangent X (F z) := mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) F z
  have hdf : fderiv ℂ (Prod.fst : ℂ × ℂ → ℂ) z = ContinuousLinearMap.fst ℂ ℂ ℂ := hasFDerivAt_fst.fderiv
  have hds : fderiv ℂ (Prod.snd : ℂ × ℂ → ℂ) z = ContinuousLinearMap.snd ℂ ℂ ℂ := hasFDerivAt_snd.fderiv
  have hd (w : ℂ × ℂ) : d w = w.1 • d (1,0) + w.2 • d (0,1) := by
    have hw : w = w.1 • (1,0) + w.2 • (0,1) := by ext <;> simp
    conv_lhs => rw [hw]
    rw [map_add,map_smul,map_smul]
  constructor
  · intro h
    have ht := h.1 (1,0) (0,1)
    have hs := h.2 (0,1) (1,0)
    simp only [hdf,ContinuousLinearMap.coe_fst',one_smul,zero_smul] at ht
    simp only [hds,ContinuousLinearMap.coe_snd',one_smul,zero_smul] at hs
    refine ⟨?_,ht⟩
    change ∃ v, S.projector (F z) v = d (1,0)
    refine ⟨d (1,0),?_⟩
    change d (1,0) - S.projector (F z) (d (1,0)) = 0 at hs
    exact (sub_eq_zero.mp hs).symm
  · rintro ⟨⟨v,hv⟩,ht⟩
    change S.projector (F z) (d (0,1)) = 0 at ht
    have hs : S.projector (F z) (d (1,0)) = d (1,0) := by
      change S.projector (F z) v = d (1,0) at hv
      rw [← hv,S.idempotent]
    have hp (w : ℂ × ℂ) : S.projector (F z) (d w) = w.1 • d (1,0) := by
      rw [hd,map_add,map_smul,map_smul,hs,ht,smul_zero,add_zero]
    have hq (w : ℂ × ℂ) : S.swap.projector (F z) (d w) = w.2 • d (0,1) := by
      change d w - S.projector (F z) (d w) = _
      rw [hp,hd]; abel
    constructor
    · intro v w
      change fderiv ℂ (Prod.fst : ℂ × ℂ → ℂ) z v • S.projector (F z) (d w) =
        fderiv ℂ (Prod.fst : ℂ × ℂ → ℂ) z w • S.projector (F z) (d v)
      rw [hdf,hp w,hp v]
      change v.1 • (w.1 • _) = w.1 • (v.1 • _)
      rw [smul_smul,smul_smul,mul_comm]
    · intro v w
      change fderiv ℂ (Prod.snd : ℂ × ℂ → ℂ) z v • S.swap.projector (F z) (d w) =
        fderiv ℂ (Prod.snd : ℂ × ℂ → ℂ) z w • S.swap.projector (F z) (d v)
      rw [hds,hq w,hq v]
      change v.2 • (w.2 • _) = w.2 • (v.2 • _)
      rw [smul_smul,smul_smul,mul_comm]

 

theorem extend_rational_tangent_map [CompactSpace X.Carrier]
    (e : ProjectiveEmbedding X) (x₀ : X.Carrier) {U : Set (ℂ × ℂ)}
    (hU : IsOpen U) (hdense : Dense U) (F : ℂ × ℂ → X.Carrier)
    (V : ℂ × ℂ → Fin (e.N+1) → ℂ)
    (hV : ∀ j, RationalSurface.RationalOn U (fun w => V w j))
    (hn : ∀ w ∈ U, V w ≠ 0) (hi : ∀ w ∈ U, e.Incidence (F w) (V w))
    (hw : ∀ w ∈ U, S.WedgeAt F Prod.fst w ∧ S.swap.WedgeAt F Prod.snd w) :
    ∃ H : ℂ × ℂ → X.Carrier,
      ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω H ∧ EqOn H F U ∧
      (∀ w, S.WedgeAt H Prod.fst w ∧ S.swap.WedgeAt H Prod.snd w) := by
  obtain ⟨P,hprim,hfin,hprop⟩ := RationalSurface.primitive_tuple_of_rational V hV hn
  let p := fun j => RationalSurface.toMv (P j)
  let H := lift e x₀ p
  have htuple (w : ℂ × ℂ) : tuple e p w = fun j => RationalSurface.eval (P j) w := by
    funext j; exact RationalSurface.value_toMv (P j) w
  have hfinite : Set.Finite {w : ℂ × ℂ | ∀ j, value (p j) w = 0} := by
    simpa only [p,RationalSurface.value_toMv] using hfin
  have hprop' (w : ℂ × ℂ) (hw : w ∈ U) : tuple e p w ≠ 0 ∧ e.Incidence (F w) (tuple e p w) := by
    obtain ⟨c,hc,he⟩ := hprop w hw
    rw [htuple,he]
    exact ⟨smul_ne_zero hc (hn w hw),(e.incidence_smul_iff hc).mpr (hi w hw)⟩
  have hcone (w : ℂ × ℂ) : ∃ x, e.Incidence x (tuple e p w) := by
    apply e.isClosed_cone.mem_of_frequently_of_tendsto _ (tuple_analytic e p w).continuousAt
    exact (mem_closure_iff_frequently.mp (hdense w)).mono (fun a ha => ⟨F a,(hprop' a ha).2⟩)
  have hagree : EqOn H F U := by
    intro w hw
    exact e.coneLift_eq x₀ (hprop' w hw).1 (hprop' w hw).2
  have hnear (w : ℂ × ℂ) (hw : w ∈ U) : H =ᶠ[𝓝 w] F :=
    Filter.Eventually.mono (hU.mem_nhds hw) (fun a ha => hagree ha)
  have hreg (w : ℂ × ℂ) (hnw : tuple e p w ≠ 0) :
      S.WedgeAt H Prod.fst w ∧ S.swap.WedgeAt H Prod.snd w := by
    have hhol : ContMDiffAt 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω H w :=
      lift_holomorphic e x₀ hnw (Filter.Eventually.of_forall hcone)
    have hfreq := (mem_closure_iff_frequently.mp (hdense w)).mono (fun a ha =>
      And.intro ((hw a ha).1.congr S (hnear a ha).symm Filter.EventuallyEq.rfl)
        ((hw a ha).2.congr S.swap (hnear a ha).symm Filter.EventuallyEq.rfl))
    exact ⟨S.wedgeAt_of_frequently hhol (analyticAt_fst) (hfreq.mono (fun _ h => h.1)),
      S.swap.wedgeAt_of_frequently hhol (analyticAt_snd) (hfreq.mono (fun _ h => h.2))⟩
  let A : PolynomialBlowup.P := MvPolynomial.X 0
  let B : PolynomialBlowup.P := MvPolynomial.X 1
  have hA : value A = (Prod.fst : ℂ × ℂ → ℂ) := by funext w; simp [A,value,valueHom]
  have hB : value B = (Prod.snd : ℂ × ℂ → ℂ) := by funext w; simp [B,value,valueHom]
  have hAnc (c : ℂ) : A ≠ MvPolynomial.C c := by
    intro he
    have h0 : (0 : ℂ) = c := by simpa [A,value,valueHom] using congrArg (fun q => value q (0,0)) he
    have h1 : (1 : ℂ) = c := by simpa [A,value,valueHom] using congrArg (fun q => value q (1,0)) he
    exact one_ne_zero (h1.trans h0.symm)
  have hBnc (c : ℂ) : B ≠ MvPolynomial.C c := by
    intro he
    have h0 : (0 : ℂ) = c := by simpa [B,value,valueHom] using congrArg (fun q => value q (0,0)) he
    have h1 : (1 : ℂ) = c := by simpa [B,value,valueHom] using congrArg (fun q => value q (0,1)) he
    exact one_ne_zero (h1.trans h0.symm)
  have hall (w : ℂ × ℂ) : tuple e p w ≠ 0 :=
    nonzero_everywhere e S x₀ p A B hfinite hcone (by simpa only [hA,hB] using hreg) hAnc hBnc w
  exact ⟨H,(fun w => lift_holomorphic e x₀ (hall w) (Filter.Eventually.of_forall hcone)),
    hagree,fun w => hreg w (hall w)⟩

end SplitTangent.TangentSplitting

namespace SplitTangent
namespace TangentSplitting
open ReciprocalCharts
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

lemma tangency_comp_changeChart {H : ℂ × ℂ → X.Carrier}
    (hH : ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω H)
    (ht : ∀ w, mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) H w (1,0) ∈ S.first (H w) ∧
      mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) H w (0,1) ∈ S.second (H w))
    (b c : Bool) {w : ℂ × ℂ} (hw : w ∈ torus) :
    mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) (H ∘ changeChart b c) w (1,0) ∈
      S.first (H (changeChart b c w)) ∧
    mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) (H ∘ changeChart b c) w (0,1) ∈
      S.second (H (changeChart b c w)) := by
  let d : (ℂ × ℂ) →L[ℂ] Tangent X (H (changeChart b c w)) :=
    mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) H (changeChart b c w)
  have hd : mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) (H ∘ changeChart b c) w =
      d.comp (fderiv ℂ (changeChart b c) w) := by
    rw [mfderiv_comp w ((hH _).mdifferentiableAt (by simp))
      (changeChart_analytic b c hw).differentiableAt.mdifferentiableAt,mfderiv_eq_fderiv]
    rfl
  constructor
  · rw [hd]
    change d (fderiv ℂ (changeChart b c) w (1,0)) ∈ _
    rw [changeChart_fderiv_first b c hw,map_smul]
    exact (S.first _).smul_mem _ (ht _).1
  · rw [hd]
    change d (fderiv ℂ (changeChart b c) w (0,1)) ∈ _
    rw [changeChart_fderiv_second b c hw,map_smul]
    exact (S.second _).smul_mem _ (ht _).2

lemma rational_changeChart_fst (b : Bool) :
    RationalSurface.RationalOn torus (fun w => coord b w.1) := by
  cases b
  · exact RationalSurface.RationalOn.fst torus
  · exact (RationalSurface.RationalOn.fst torus).inv (fun _ h => h.1)

lemma rational_changeChart_snd (b : Bool) :
    RationalSurface.RationalOn torus (fun w => coord b w.2) := by
  cases b
  · exact RationalSurface.RationalOn.snd torus
  · exact (RationalSurface.RationalOn.snd torus).inv (fun _ h => h.2)

 

theorem exists_projective_tangent_box [CompactSpace X.Carrier]
    (e : ProjectiveEmbedding X) (g : RationalCurve X) : Nonempty (TangentBox S g) := by
  obtain ⟨z,P,F,hn,hi,hF,hdiag,hpde⟩ := S.exists_affine_polynomial_tangent_box e g
  let L : ℂ × ℂ → ℂ × ℂ := fun w => (w.2,w.1-w.2)
  let H₀ := F ∘ L
  have hL : ContDiff ℂ ω L := contDiff_snd.prodMk (contDiff_fst.sub contDiff_snd)
  have hH₀ : ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω H₀ := hF.comp hL.contMDiff
  have hA : (fun w : ℂ × ℂ => w.1+w.2) ∘ L = Prod.fst := by
    funext w; simp [L]
  have hB : Prod.fst ∘ L = Prod.snd := rfl
  have hW₀ (w : ℂ × ℂ) : S.WedgeAt H₀ Prod.fst w ∧ S.swap.WedgeAt H₀ Prod.snd w := by
    obtain ⟨ha,hb⟩ := S.wedges_of_pde (hpde (L w))
    rw [← hA,← hB]
    exact ⟨ha.comp S (hF _) (analyticAt_fst.add analyticAt_snd).differentiableAt
        (hL.differentiable (by simp) w),
      hb.comp S.swap (hF _) (analyticAt_fst.differentiableAt) (hL.differentiable (by simp) w)⟩
  have hT₀ (w : ℂ × ℂ) := (S.wedges_iff_tangency).mp (hW₀ w)
  have hline : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω (fun u : ℂ => F (u,0)) :=
    hF.comp ((contDiff_id.prodMk contDiff_const : ContDiff ℂ ω (fun u : ℂ => (u,(0 : ℂ)))).contMDiff)
  have hdiagall := ComplexManifold.eqOn_of_eventuallyEq isPreconnected_univ
    (fun u _ => hline u) (fun u _ => g.finite_holomorphic u) (mem_univ z) hdiag
  have hD₀ (u : ℂ) : H₀ (u,u) = g.finite u := by
    simpa only [H₀,Function.comp_apply,L,sub_self] using hdiagall (mem_univ u)
  have hcharts (a b : Bool) : ∃ H : ℂ × ℂ → X.Carrier,
      ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω H ∧
      EqOn H (H₀ ∘ changeChart a b) torus ∧
      (∀ w, S.WedgeAt H Prod.fst w ∧ S.swap.WedgeAt H Prod.snd w) := by
    let V : ℂ × ℂ → Fin (e.N+1) → ℂ := fun w j => RationalSurface.eval (P j) (L (changeChart a b w))
    apply S.extend_rational_tangent_map e (g.finite 0) torus_open torus_dense
      (H₀ ∘ changeChart a b) V
    · intro j
      exact (rational_changeChart_snd b).eval_comp
        ((rational_changeChart_fst a).sub (rational_changeChart_snd b)) (P j)
    · intro w _; exact hn (L (changeChart a b w))
    · intro w _; exact hi (L (changeChart a b w))
    · intro w hw
      exact (S.wedges_iff_tangency).mpr (S.tangency_comp_changeChart hH₀ hT₀ a b hw)
  choose H hH hEq hW using hcharts
  have heq (a b c d : Bool) (w : ℂ × ℂ) (hw : w ∈ overlap a b c d) :
      H a b w = H c d (changeChart (Bool.xor a c) (Bool.xor b d) w) := by
    apply tendsto_nhds_unique_of_frequently_eq (hH a b w).continuousAt
      ((hH c d _).continuousAt.comp (changeChart_analytic_on_overlap a b c d hw).continuousAt)
    apply (mem_closure_iff_frequently.mp (torus_dense w)).mono
    intro v hv
    change H a b v = H c d (changeChart (Bool.xor a c) (Bool.xor b d) v)
    rw [hEq a b hv,hEq c d (changeChart_torus _ _ hv)]
    simp only [Function.comp_apply]
    exact congrArg H₀ (changeChart_transition a b c d v).symm
  have hzero (w : ℂ × ℂ) : H false false w = H₀ w := by
    apply tendsto_nhds_unique_of_frequently_eq (hH false false w).continuousAt (hH₀ w).continuousAt
    apply (mem_closure_iff_frequently.mp (torus_dense w)).mono
    intro v hv
    exact hEq false false hv
  have hinfty (u : ℂ) : H true true (u,u) = g.infinity u := by
    have hc : Continuous (fun v : ℂ => H true true (v,v)) :=
      (hH true true).continuous.comp (continuous_id.prodMk continuous_id)
    apply tendsto_nhds_unique_of_frequently_eq hc.continuousAt (g.infinity_holomorphic u).continuousAt
    apply (mem_closure_iff_frequently.mp ((dense_compl_singleton (0 : ℂ)) u)).mono
    intro v hv
    have hv' : v ≠ 0 := hv
    rw [hEq true true (show (v,v) ∈ torus from ⟨hv',hv'⟩)]
    change H₀ (v⁻¹,v⁻¹) = _
    rw [hD₀,g.overlap v⁻¹ (inv_ne_zero hv'),inv_inv]
  exact ⟨⟨H,hH,heq,fun u => (hzero (u,u)).trans (hD₀ u),hinfty,
    fun a b w => (S.wedges_iff_tangency).mp (hW a b w)⟩⟩

end TangentSplitting
end SplitTangent

end

end OAI
