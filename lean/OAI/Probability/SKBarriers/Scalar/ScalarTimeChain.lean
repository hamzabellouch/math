import Mathlib
import OAI.Probability.SKBarriers.Dynamics.FiniteMarkovPath
import OAI.Probability.SKBarriers.Scalar.ScalarHierarchyMass
import OAI.Probability.SKBarriers.Scalar.ScalarSemigroup

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def scalarTimeStep (β m : ℝ) (t : ℝ≥0) (f : ℝ → ℝ) : ℝ → ℝ :=
  scalarStep m (β*Real.sqrt (t:ℝ)) f

theorem scalarTimeStep_regular {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (β m : ℝ) (t : ℝ≥0) : BoundedDerivs (scalarTimeStep β m t f) :=
  scalarStep_regular hf _ _

theorem scalarTimeStep_lipschitz {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) {m : ℝ} (hm : 0 ≤ m) (β : ℝ) (t : ℝ≥0) :
    LipschitzWith K (scalarTimeStep β m t f) := scalarStep_lipschitz hf hLip hm _

theorem scalarTimeStep_semigroup {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (β m : ℝ) (s t : ℝ≥0) :
    scalarTimeStep β m s (scalarTimeStep β m t f) = scalarTimeStep β m (s+t) f := by
  apply scalarStep_semigroup hf
  simp only [mul_pow, NNReal.coe_add]
  rw [Real.sq_sqrt s.coe_nonneg, Real.sq_sqrt t.coe_nonneg,
    Real.sq_sqrt (add_nonneg s.coe_nonneg t.coe_nonneg), mul_add]

@[simp] theorem scalarTimeStep_zero (β m : ℝ) (f : ℝ → ℝ) : scalarTimeStep β m 0 f=f := by
  simp only [scalarTimeStep,NNReal.coe_zero,Real.sqrt_zero,mul_zero,scalarStep_zero]

def scalarTimeChain (β : ℝ) : List (ℝ × ℝ≥0) → (ℝ → ℝ) → ℝ → ℝ
  | [],f => f
  | p::ps,f => scalarTimeStep β p.1 p.2 (scalarTimeChain β ps f)

theorem scalarTimeChain_regular {f : ℝ → ℝ} (hf : BoundedDerivs f) (β : ℝ)
    (l : List (ℝ × ℝ≥0)) : BoundedDerivs (scalarTimeChain β l f) := by
  induction l with
  | nil => exact hf
  | cons p l ih => exact scalarTimeStep_regular ih _ _ _

theorem scalarTimeChain_lipschitz {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β : ℝ) (l : List (ℝ × ℝ≥0))
    (hm : ∀ p ∈ l, 0 ≤ p.1) : LipschitzWith K (scalarTimeChain β l f) := by
  induction l with
  | nil => exact hLip
  | cons p l ih =>
    exact scalarTimeStep_lipschitz (scalarTimeChain_regular hf β l)
      (ih (fun q hq => hm q (List.mem_cons_of_mem p hq))) (hm p (List.mem_cons_self)) _ _

theorem scalarTimeChain_append (β : ℝ) (l₁ l₂ : List (ℝ × ℝ≥0)) (f : ℝ → ℝ) :
    scalarTimeChain β (l₁++l₂) f=scalarTimeChain β l₁ (scalarTimeChain β l₂ f) := by
  induction l₁ with
  | nil => rfl
  | cons p ps ih => simp only [List.cons_append,scalarTimeChain,ih]

theorem scalarTimeChain_ofFn (β : ℝ) (n : ℕ) (m : Fin n → ℝ) (t : Fin n → ℝ≥0)
    (f : ℝ → ℝ) :
    scalarTimeChain β (List.ofFn (fun i => (m i,t i))) f=
      scalarHierarchy n m (fun i => β*Real.sqrt (t i:ℝ)) f := by
  induction n generalizing f with
  | zero => simp [scalarTimeChain,scalarHierarchy]
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, scalarTimeChain_append]
    exact ih _ _ _

theorem scalarTimeChain_split {f : ℝ → ℝ} (hf : BoundedDerivs f) (β m : ℝ)
    (s t : ℝ≥0) (l r : List (ℝ × ℝ≥0)) :
    scalarTimeChain β (l++(m,s)::(m,t)::r) f =
      scalarTimeChain β (l++(m,s+t)::r) f := by
  simp only [scalarTimeChain_append,scalarTimeChain]
  rw [scalarTimeStep_semigroup (scalarTimeChain_regular hf β r)]

theorem scalarTimeChain_constant {f : ℝ → ℝ} (hf : BoundedDerivs f) (β m : ℝ)
    (l : List ℝ≥0) :
    scalarTimeChain β (l.map (fun t => (m,t))) f = scalarTimeStep β m l.sum f := by
  induction l with
  | nil => simp [scalarTimeChain]
  | cons t l ih =>
    simp only [List.map_cons,scalarTimeChain,List.sum_cons,ih]
    exact scalarTimeStep_semigroup hf β m t l.sum

theorem scalarTimeStep_mass_lipschitz {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hLip : LipschitzWith 1 f) (β : ℝ) {t : ℝ≥0} (ht : t ≤ 1)
    {m m' : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (hm' : m' ∈ Icc (0:ℝ) 1) (x : ℝ) :
    |scalarTimeStep β m' t f x-scalarTimeStep β m t f x| ≤
      gaussianMassBound |β| * β^2 * (t:ℝ) * |m'-m| := by
  have hst : Real.sqrt (t:ℝ) ≤ 1 := (Real.sqrt_le_one).mpr ht
  have hv : |β*Real.sqrt (t:ℝ)| ≤ |β| := by
    rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_of_le_one_right (abs_nonneg _) hst
  have H := scalarStep_mass_lipschitz hf hLip hv hm hm' x
  simpa only [scalarTimeStep,mul_pow,Real.sq_sqrt t.coe_nonneg,mul_assoc] using H

theorem scalarTimeChain_mass_lipschitz {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hLip : LipschitzWith 1 f) (β : ℝ) (l : List (ℝ × ℝ × ℝ≥0))
    (hm : ∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1 ∧ p.2.1 ∈ Icc (0:ℝ) 1 ∧ p.2.2 ≤ 1) (x : ℝ) :
    |scalarTimeChain β (l.map (fun p => (p.2.1,p.2.2))) f x-
      scalarTimeChain β (l.map (fun p => (p.1,p.2.2))) f x| ≤
      gaussianMassBound |β| * β^2 * (l.map (fun p => (p.2.2:ℝ)*|p.2.1-p.1|)).sum := by
  induction l generalizing x with
  | nil => simp [scalarTimeChain]
  | cons p l ih =>
    have htail q (hq : q ∈ l) := hm q (List.mem_cons_of_mem p hq)
    have hp := hm p (List.mem_cons_self)
    let f₁ := scalarTimeChain β (l.map (fun q => (q.2.1,q.2.2))) f
    let f₀ := scalarTimeChain β (l.map (fun q => (q.1,q.2.2))) f
    have hf₁ : BoundedDerivs f₁ := scalarTimeChain_regular hf β _
    have hf₀ : BoundedDerivs f₀ := scalarTimeChain_regular hf β _
    have hl₀ : LipschitzWith 1 f₀ := scalarTimeChain_lipschitz hf hLip β _ (by
      intro q hq
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
      exact (htail r hr).1.1)
    have H₁ := scalarStep_uniform_nonexpansive hf₁ hf₀ hp.2.1.1
      (fun z => ih htail z) (β*Real.sqrt (p.2.2:ℝ)) x
    have H₂ := scalarTimeStep_mass_lipschitz hf₀ hl₀ β hp.2.2 hp.1 hp.2.1 x
    calc
      _ ≤ |scalarTimeStep β p.2.1 p.2.2 f₁ x-scalarTimeStep β p.2.1 p.2.2 f₀ x|+
          |scalarTimeStep β p.2.1 p.2.2 f₀ x-scalarTimeStep β p.1 p.2.2 f₀ x| :=
        abs_sub_le _ _ _
      _ ≤ gaussianMassBound |β| * β^2 * (l.map (fun q => (q.2.2:ℝ)*|q.2.1-q.1|)).sum+
          gaussianMassBound |β| * β^2 * (p.2.2:ℝ)*|p.2.1-p.1| := add_le_add H₁ H₂
      _ = _ := by simp only [List.map_cons,List.sum_cons]; ring

end SK.Analytic

end
end

end OAI
