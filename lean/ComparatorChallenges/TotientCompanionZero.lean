import Mathlib

namespace OAI

/-! The no-seed alternative of the weighted totient companion theorem. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def IsTotient (v : ℕ) : Prop := ∃ n : ℕ, 0 < n ∧ n.totient = v

def ell (v : ℕ) : ℕ := by
  classical
  exact if h : IsTotient v then Nat.find h else 0

def a (j : ℕ) : ℝ := (j + 1 : ℝ) * Real.log (j + 1) - j * Real.log j - 1

def RenewalRootSet : Set ℝ :=
  {z | 0 < z ∧ z < 1 ∧ (∑' j : ℕ, a (j+1) * z^(j+1)) = 1}

def rho : ℝ := sInf RenewalRootSet

def lam : ℝ := Real.log (1 / rho)

def gamma : ℝ := (∑' j : ℕ, (j+1 : ℝ) * a (j+1) * rho^(j+1))⁻¹

def P (H : ℕ) : ℕ := ⌊Real.log (Real.log (H : ℝ))⌋₊
def alpha (s : ℝ) : ℝ := lam * Real.exp (lam * s)

def largestPrimeFactor (n : ℕ) : ℕ := max 1 (n.primeFactors.sup id)

structure TailDatum (H : ℕ) where
  Q : Fin H → ℕ
  cofactor : ℕ

def tailPrime {H : ℕ} (η : TailDatum H) (h : ℕ) : ℕ :=
  if hH : h < H then η.Q ⟨h, hH⟩ else 1

def tailLog {H : ℕ} (η : TailDatum H) (h : ℕ) : ℝ :=
  Real.log (Real.log (tailPrime η h : ℝ))

def IsWitness (H : ℕ) (s : ℝ) (η : TailDatum H) : Prop :=
  (∀ h : Fin H, h.val < P H → η.Q h = 1) ∧
  0 < η.cofactor ∧
  (∀ h ∈ Finset.Ico (P H) H, (tailPrime η h).Prime ∧
    (9 / 10 : ℝ) * alpha s * h * (rho^h)⁻¹ ≤ tailLog η h ∧
    tailLog η h ≤ (11 / 10 : ℝ) * alpha s * h * (rho^h)⁻¹ ∧
    (∑ l ∈ Finset.Ico (P H) h, a (h-l) * tailLog η l) ≤
      (1 + (1 / 10000 : ℝ) * Real.exp (-(h : ℝ) / 40)) * tailLog η h) ∧
  largestPrimeFactor η.cofactor ≤ tailPrime η (P H) ∧
  Real.log (η.cofactor : ℝ) ≤
    Real.exp (2 * alpha s * (P H : ℝ) * (rho^(P H))⁻¹)

def w {H : ℕ} (η : TailDatum H) : ℕ :=
  η.cofactor * ∏ h ∈ Finset.Ico (P H) H, tailPrime η h

def witnesses (H : ℕ) (s : ℝ) (d : ℕ) : Set (TailDatum H) :=
  {η | IsWitness H s η ∧ (w η).totient = d}

def D {H : ℕ} (h : ℕ) (η : TailDatum H) : ℝ :=
  ∑ l ∈ Finset.Ico (P H) H, a (h-l) * tailLog η l

def maxD {H : ℕ} (h : ℕ) (T : Finset (TailDatum H)) : ℝ := by
  classical
  exact if ht : T.Nonempty then T.sup' ht (D h) else 0

def AH (H : ℕ) (f : ℝ → ℝ) (s : ℝ) : ℝ := by
  classical
  exact rho^(H*(H-1)/2) * (gamma / alpha s)^H *
    ∑ᶠ d : ℕ,
      if IsTotient d then
        f ((ell d : ℝ) / d) / d *
          ∑ᶠ T : Finset (TailDatum H),
            if T.Nonempty ∧ (↑T : Set (TailDatum H)) ⊆ witnesses H s d then
              (-1 : ℝ)^(T.card-1) *
               Real.exp (-(gamma / alpha s) *
                 ∑' n : ℕ, rho^(H+n) * maxD (H+n) T)
            else 0
      else 0

def A (f : ℝ → ℝ) (s : ℝ) : ℝ := limUnder atTop (fun H : ℕ => AH H f s)

def N (k : ℕ) (x : ℝ) : ℝ := by
  classical
  exact (((Finset.Icc 1 ⌊x⌋₊).filter fun v =>
    IsTotient v ∧ (k : ℝ) * x < ell v ∧ (ell v : ℝ) ≤ (k+1 : ℝ) * x).card : ℝ)

def fk (k : ℕ) (r : ℝ) : ℝ := min 1 ((k+1 : ℝ) / r) - min 1 ((k : ℝ) / r)

/-- Without a totient value whose least preimage exceeds its prescribed multiple,
both the weighted count and its limiting coefficient vanish. -/
theorem companion_zero_case (k : ℕ) (_hk : 0 < k)
    (hno : ¬ ∃ d : ℕ, IsTotient d ∧ k*d < ell d) :
    (∀ x : ℝ, 0 < x → N k x = 0) ∧
    (∀ s ∈ Set.Ico (0 : ℝ) 1, A (fk k) s = 0) := by
  sorry

end TotientAsymptotic
end

end OAI
