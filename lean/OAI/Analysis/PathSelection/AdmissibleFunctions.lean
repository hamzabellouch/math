import Mathlib

namespace OAI

/-! Real-holomorphic representatives, recursively extracted coefficients and admissibility. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

namespace PathSelection.Statement

abbrev RealPoint (m n : ℕ) := (Fin m → ℝ) × (Fin n → ℝ)
abbrev ComplexPoint (m n : ℕ) := (Fin m → ℂ) × (Fin n → ℂ)

 
def complexify {m n : ℕ} (x : RealPoint m n) : ComplexPoint m n :=
  (fun i => (x.1 i : ℂ), fun a => (x.2 a : ℂ))

def conjugate {m n : ℕ} (x : ComplexPoint m n) : ComplexPoint m n :=
  (fun i => star (x.1 i), fun a => star (x.2 a))

 

def realValue {m n : ℕ} (P : ComplexPoint m n → ℂ) (x : RealPoint m n) : ℝ :=
  (P (complexify x)).re

 
def quadraticRegion (A c : ℝ) : Set ℂ :=
  {L | A < L.re ∧ |L.im| < c * L.re ^ 2}

def tailBand (A c : ℝ) : Set ℂ :=
  {L | A < L.re ∧ |L.im| < c}

def ordinaryPolydisc {n : ℕ} (z₀ : Fin n → ℝ) (r : ℝ) : Set (Fin n → ℂ) :=
  {z | ∀ a, ‖z a - (z₀ a : ℂ)‖ < r}

def ordinaryClosedPolydisc {n : ℕ} (z₀ : Fin n → ℝ) (r : ℝ) :
    Set (Fin n → ℂ) :=
  {z | ∀ a, ‖z a - (z₀ a : ℂ)‖ ≤ r}

 
def quadraticDomain {m n : ℕ} (S : Finset (Fin m)) (A c : ℝ)
    (z₀ : Fin n → ℝ) (r : ℝ) : Set (ComplexPoint m n) :=
  {x | (∀ i, i ∉ S → x.1 i ∈ quadraticRegion A c) ∧ x.2 ∈ ordinaryPolydisc z₀ r}

 
def quadraticEstimateDomain {m n : ℕ} (S : Finset (Fin m)) (A c : ℝ)
    (z₀ : Fin n → ℝ) (r : ℝ) : Set (ComplexPoint m n) :=
  {x | (∀ i, i ∉ S → x.1 i ∈ quadraticRegion A c) ∧
    x.2 ∈ ordinaryClosedPolydisc z₀ r}

def commonBandDomain {m n : ℕ} (S : Finset (Fin m)) (A c : ℝ)
    (z₀ : Fin n → ℝ) (r : ℝ) : Set (ComplexPoint m n) :=
  {x | (∀ i, i ∉ S → x.1 i ∈ tailBand A c) ∧ x.2 ∈ ordinaryPolydisc z₀ r}

def RealHolomorphicOn {m n : ℕ} (f : ComplexPoint m n → ℂ)
    (U : Set (ComplexPoint m n)) : Prop :=
  AnalyticOnNhd ℂ f U ∧ ∀ x ∈ U, f (conjugate x) = star (f x)

 

structure Extraction (m : ℕ) where
  coordinate : Fin m
  exponent : ℝ
  power : ℕ

def expanded {m : ℕ} (h : List (Extraction m)) : Finset (Fin m) :=
  (h.map Extraction.coordinate).toFinset

 
structure CoefficientSystem (m n : ℕ) where
  coefficient : List (Extraction m) → ComplexPoint m n → ℂ
  exponents : List (Extraction m) → Fin m → Set ℝ
  degree : List (Extraction m) → Fin m → ℝ → ℕ

namespace CoefficientSystem

def Valid {m n : ℕ} (T : CoefficientSystem m n) : List (Extraction m) → Prop
  | [] => True
  | e :: h => T.Valid h ∧ e.coordinate ∉ expanded h ∧
      e.exponent ∈ T.exponents h e.coordinate ∧
      e.power ≤ T.degree h e.coordinate e.exponent

 

def IndependentOfExpanded {m n : ℕ} (T : CoefficientSystem m n)
    (h : List (Extraction m)) : Prop :=
  ∀ x y : ComplexPoint m n, x.2 = y.2 →
    (∀ i, i ∉ expanded h → x.1 i = y.1 i) → T.coefficient h x = T.coefficient h y

 
def QuadraticallyBounded {m n : ℕ} (T : CoefficientSystem m n)
    (h : List (Extraction m)) (z₀ : Fin n → ℝ) (R : ℝ) : Prop :=
  ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
    RealHolomorphicOn (T.coefficient h) (quadraticDomain (expanded h) A c z₀ R) ∧
    ∀ r : ℝ, 0 < r → r < R → ∃ C : ℝ, 0 < C ∧
      ∀ x ∈ quadraticEstimateDomain (expanded h) A c z₀ r, ‖T.coefficient h x‖ ≤ C

 

def finiteSum {ι : Type*} (s : Set ι) (f : ι → ℂ) : ℂ := by
  classical
  exact if hs : s.Finite then ∑ i ∈ hs.toFinset, f i else 0

 
def singlePartialSum {m n : ℕ} (T : CoefficientSystem m n)
    (h : List (Extraction m)) (i : Fin m) (B : ℝ) (x : ComplexPoint m n) : ℂ :=
  finiteSum (T.exponents h i ∩ Iic B) (fun d =>
    Complex.exp (-(d : ℂ) * x.1 i) *
      ∑ k ∈ Finset.range (T.degree h i d + 1),
        (x.1 i) ^ k * T.coefficient (⟨i, d, k⟩ :: h) x)

 

def SingleExpansion {m n : ℕ} (T : CoefficientSystem m n)
    (h : List (Extraction m)) (i : Fin m) (z₀ : Fin n → ℝ) (R : ℝ) : Prop :=
  (∀ d ∈ T.exponents h i, 0 ≤ d) ∧
  (∀ B : ℝ, (T.exponents h i ∩ Iic B).Finite) ∧
  (0 ∈ T.exponents h i → T.degree h i 0 = 0) ∧
  ∀ B r : ℝ, 0 < r → r < R →
    ∃ A c C ε : ℝ, 0 < A ∧ 0 < c ∧ 0 < C ∧ 0 < ε ∧
      ∀ x ∈ quadraticEstimateDomain (expanded h) A c z₀ r,
        ‖T.coefficient h x - T.singlePartialSum h i B x‖ ≤
          C * Real.exp (-(B + ε) * (x.1 i).re)

 

def iteratedHistories {m n : ℕ} (T : CoefficientSystem m n)
    (h : List (Extraction m)) (I : List (Fin m)) : Set (List (Extraction m)) :=
  {q | q.map Extraction.coordinate = I ∧ T.Valid (q ++ h)}

def weight {m : ℕ} (rates : Fin m → ℝ) (q : List (Extraction m)) : ℝ :=
  (q.map (fun e => rates e.coordinate * e.exponent)).sum

def iteratedTerm {m n : ℕ} (T : CoefficientSystem m n)
    (h q : List (Extraction m)) (x : ComplexPoint m n) : ℂ :=
  (q.map (fun e => Complex.exp (-(e.exponent : ℂ) * x.1 e.coordinate) *
    (x.1 e.coordinate) ^ e.power)).prod * T.coefficient (q ++ h) x

def groupedPartialSum {m n : ℕ} (T : CoefficientSystem m n)
    (h : List (Extraction m)) (I : List (Fin m)) (rates : Fin m → ℝ)
    (B : ℝ) (x : ComplexPoint m n) : ℂ :=
  finiteSum {q | q ∈ T.iteratedHistories h I ∧ weight rates q ≤ B}
    (fun q => T.iteratedTerm h q x)

 

def GroupedExpansion {m n : ℕ} (T : CoefficientSystem m n)
    (h : List (Extraction m)) (z₀ : Fin n → ℝ) (R : ℝ) : Prop :=
  ∀ (I : List (Fin m)) (rates : Fin m → ℝ),
    I.Nodup → (∀ i ∈ I, i ∉ expanded h) → (∀ i ∈ I, 0 < rates i) →
    (∀ B : ℝ,
      {q | q ∈ T.iteratedHistories h I ∧ weight rates q ≤ B}.Finite) ∧
    (∀ B : ℝ,
      ((weight rates '' T.iteratedHistories h I) ∩ Iic B).Finite) ∧
    ∀ B r : ℝ, 0 < r → r < R →
      ∃ A c C ε : ℝ, 0 < A ∧ 0 < c ∧ 0 < C ∧ 0 < ε ∧
        ∀ x : ℝ → ComplexPoint m n,
          (∀ᶠ U in atTop, x U ∈ quadraticEstimateDomain (expanded h) A c z₀ r) →
          (∀ i ∈ I, Tendsto (fun U => ((x U).1 i).re / U) atTop (𝓝 (rates i))) →
          ∀ᶠ U in atTop,
            ‖T.coefficient h (x U) - T.groupedPartialSum h I rates B (x U)‖ ≤
              C * Real.exp (-(B + ε) * U)

 

def CommonCoefficientDomains {m n : ℕ} (T : CoefficientSystem m n)
    (z₀ : Fin n → ℝ) (R : ℝ) : Prop :=
  ∀ S : Finset (Fin m), ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
    ∀ h : List (Extraction m), T.Valid h → expanded h = S →
      RealHolomorphicOn (T.coefficient h) (commonBandDomain S A c z₀ R)

end CoefficientSystem

 

def Admissible {m n : ℕ} (P : ComplexPoint m n → ℂ) (z₀ : Fin n → ℝ) : Prop :=
  ∃ T : CoefficientSystem m n, T.coefficient [] = P ∧
    ∃ R : ℝ, 0 < R ∧ T.CommonCoefficientDomains z₀ R ∧
      ∀ h : List (Extraction m), T.Valid h →
        T.IndependentOfExpanded h ∧ T.QuadraticallyBounded h z₀ R ∧
        (∀ i : Fin m, i ∉ expanded h → T.SingleExpansion h i z₀ R) ∧
        T.GroupedExpansion h z₀ R

 

inductive SignFormula (s : ℕ) where
  | truth : SignFormula s
  | falsity : SignFormula s
  | positive : Fin s → SignFormula s
  | zero : Fin s → SignFormula s
  | negative : Fin s → SignFormula s
  | not : SignFormula s → SignFormula s
  | and : SignFormula s → SignFormula s → SignFormula s
  | or : SignFormula s → SignFormula s → SignFormula s

def SignFormula.Holds {s : ℕ} : SignFormula s → (Fin s → ℝ) → Prop
  | .truth, _ => True
  | .falsity, _ => False
  | .positive j, v => 0 < v j
  | .zero j, v => v j = 0
  | .negative j, v => v j < 0
  | .not p, v => ¬ p.Holds v
  | .and p q, v => p.Holds v ∧ q.Holds v
  | .or p q, v => p.Holds v ∨ q.Holds v

 

def EventuallyMonotoneOrConstant (f : ℝ → ℝ) : Prop :=
  ∃ U : ℝ, MonotoneOn f (Ioi U) ∨ AntitoneOn f (Ioi U) ∨
    ∃ c : ℝ, EqOn f (fun _ => c) (Ioi U)

 

def PathConclusion {m n s a t : ℕ}
    (P : Fin s → ComplexPoint m n → ℂ) (φ : SignFormula s)
    (Q : Fin a → ComplexPoint m n → ℂ) (R : Fin t → ComplexPoint m n → ℂ)
    (z₀ : Fin n → ℝ) (ℓ : Fin t → ℝ) : Prop :=
  ∃ γ : ℝ → RealPoint m n, ∃ U : ℝ,
    AnalyticOnNhd ℝ γ (Ioi U) ∧
    (∀ i : Fin m, Tendsto (fun u => (γ u).1 i) atTop atTop) ∧
    Tendsto (fun u => (γ u).2) atTop (𝓝 z₀) ∧
    (∀ᶠ u in atTop, φ.Holds (fun j => realValue (P j) (γ u))) ∧
    (∀ i : Fin m, EventuallyMonotoneOrConstant (fun u => (γ u).1 i)) ∧
    (∀ b : Fin n, EventuallyMonotoneOrConstant (fun u => (γ u).2 b)) ∧
    (∀ j : Fin a, EventuallyMonotoneOrConstant (fun u => realValue (Q j) (γ u))) ∧
    (∀ j : Fin t, Tendsto (fun u => realValue (R j) (γ u)) atTop (𝓝 (ℓ j)))

 

lemma realValue_eq_of_realHolomorphicOn {m n : ℕ}
    {P : ComplexPoint m n → ℂ} {V : Set (ComplexPoint m n)}
    (hP : RealHolomorphicOn P V) {x : RealPoint m n} (hx : complexify x ∈ V) :
    (realValue P x : ℂ) = P (complexify x) := by
  have hc : conjugate (complexify x) = complexify x := by
    simp [conjugate, complexify]
  have hsym := hP.2 (complexify x) hx
  rw [hc] at hsym
  exact Complex.conj_eq_iff_re.mp hsym.symm

 

lemma eventually_mem_quadraticDomain {ι : Type*} {l : Filter ι} {m n : ℕ}
    {x : ι → RealPoint m n} {z₀ : Fin n → ℝ}
    (hL : ∀ i : Fin m, Tendsto (fun v => (x v).1 i) l atTop)
    (hz : Tendsto (fun v => (x v).2) l (𝓝 z₀))
    (S : Finset (Fin m)) {A c R : ℝ} (hA : 0 < A) (hc : 0 < c) (hR : 0 < R) :
    ∀ᶠ v in l, complexify (x v) ∈ quadraticDomain S A c z₀ R := by
  have hlen : ∀ᶠ v in l, ∀ i : Fin m, A < (x v).1 i :=
    Filter.eventually_all.mpr (fun i => (hL i).eventually (eventually_gt_atTop A))
  have hpar : ∀ᶠ v in l, ∀ a : Fin n, ‖((x v).2 a : ℂ) - (z₀ a : ℂ)‖ < R := by
    apply Filter.eventually_all.mpr
    intro a
    have ht : Tendsto (fun v => ((x v).2 a : ℂ)) l (𝓝 (z₀ a : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp ((tendsto_pi_nhds.mp hz) a)
    simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp ht R hR
  filter_upwards [hlen, hpar] with v hv hzv
  refine ⟨?_, hzv⟩
  intro i _
  refine ⟨hv i, ?_⟩
  change |(0 : ℝ)| < c * ((x v).1 i) ^ 2
  simpa only [abs_zero] using mul_pos hc (pow_pos (hA.trans (hv i)) 2)

 

lemma Admissible.eventually_realValue_eq {ι : Type*} {l : Filter ι} {m n : ℕ}
    {P : ComplexPoint m n → ℂ} {z₀ : Fin n → ℝ} (hP : Admissible P z₀)
    {x : ι → RealPoint m n}
    (hL : ∀ i : Fin m, Tendsto (fun v => (x v).1 i) l atTop)
    (hz : Tendsto (fun v => (x v).2) l (𝓝 z₀)) :
    ∀ᶠ v in l, (realValue P (x v) : ℂ) = P (complexify (x v)) := by
  obtain ⟨T, hT, R, hR, _, hrec⟩ := hP
  obtain ⟨A, c, hA, hc, han, _⟩ := (hrec [] trivial).2.1
  rw [hT] at han
  filter_upwards [eventually_mem_quadraticDomain hL hz (expanded []) hA hc hR] with v hv
  exact realValue_eq_of_realHolomorphicOn han hv

end PathSelection.Statement
end

end OAI
