import Mathlib

namespace OAI

/-! Arithmetic data and renewal coefficients for counting totient values. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def IsTotient (v : ℕ) : Prop := ∃ n : ℕ, 0 < n ∧ n.totient = v

def V (x : ℝ) : ℝ := by
  classical
  exact (((Finset.Icc 1 ⌊x⌋₊).filter IsTotient).card : ℝ)

def ell (v : ℕ) : ℕ := by
  classical
  exact if h : IsTotient v then Nat.find h else 0

def a (j : ℕ) : ℝ := (j + 1 : ℝ) * Real.log (j + 1) - j * Real.log j - 1

def RenewalRootSet : Set ℝ :=
  {z | 0 < z ∧ z < 1 ∧ (∑' j : ℕ, a (j+1) * z^(j+1)) = 1}

def rho : ℝ := sInf RenewalRootSet

def lam : ℝ := Real.log (1 / rho)

def gamma : ℝ := (∑' j : ℕ, (j+1 : ℝ) * a (j+1) * rho^(j+1))⁻¹

def g : ℕ → ℝ
  | 0 => 1
  | n+1 => ∑ d ∈ Finset.range (n+1), a (d+1) * g (n-d)
termination_by n => n

def B (x : ℝ) : ℝ := Real.log (Real.log x)
def psi (b : ℝ) : ℝ := (Real.log b - Real.log (Real.log b)) / lam

def m (x : ℝ) : ℕ := ⌊psi (B x)⌋₊
def theta (x : ℝ) : ℝ := psi (B x) - m x

def G (x : ℝ) (j : ℕ) : ℝ :=
  (B x)^j / ((Nat.factorial j : ℝ) * ∏ i ∈ Finset.Icc 1 j, g i)

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

def mainTerm (x : ℝ) : ℝ := x / Real.log x * G x (m x) * A (fun _ => 1) (theta x)



def R (x : ℝ) (H : ℕ) : ℕ := m x - H
def L (x : ℝ) (H : ℕ) : ℕ := m x - P H

def bandScale (x : ℝ) (i : ℕ) : ℝ :=
  alpha (theta x) * (m x-i : ℕ) * (rho^(m x-i))⁻¹

def xi (x : ℝ) (i : ℕ) : ℝ :=
  1 + (1/10000 : ℝ) * Real.exp (-((m x-i : ℕ) : ℝ) / 40)

structure RemainderDatum (L : ℕ) where
  primes : Fin L → ℕ
  cofactor : ℕ

def remainderPrime {J : ℕ} (η : RemainderDatum J) (i : ℕ) : ℕ :=
  if hi : 1 ≤ i ∧ i ≤ J then η.primes ⟨i-1, by omega⟩ else 1

def remainderCoord {J : ℕ} (x : ℝ) (η : RemainderDatum J) (i : ℕ) : ℝ :=
  if i = 0 then B x else Real.log (Real.log (remainderPrime η i : ℝ))

def IsBasicRemainder (x : ℝ) (H : ℕ) (η : RemainderDatum (L x H)) : Prop :=
  0 < η.cofactor ∧
  (∀ i ∈ Finset.Icc 1 (L x H),
    (remainderPrime η i).Prime ∧
    (9/10 : ℝ) * bandScale x i ≤ remainderCoord x η i ∧
    remainderCoord x η i ≤ (11/10 : ℝ) * bandScale x i) ∧
  (∀ i ∈ Finset.Icc 0 (L x H),
    (∑ r ∈ Finset.Icc (i+1) (L x H), a (r-i) * remainderCoord x η r) ≤
      (if i = L x H then 1 else xi x i) * remainderCoord x η i) ∧
  largestPrimeFactor η.cofactor ≤ remainderPrime η (L x H) ∧
  Real.log (η.cofactor : ℝ) ≤ Real.exp (2 * bandScale x (L x H))

def remainderTail (x : ℝ) (H : ℕ) (η : RemainderDatum (L x H)) : ℕ :=
  η.cofactor * ∏ i ∈ Finset.Icc (R x H+1) (L x H), remainderPrime η i

structure PrefixDatum (R : ℕ) where
  primes : Fin R → ℕ
  d : ℕ

def IsPrefixDatum (x : ℝ) (H : ℕ) (ζ : PrefixDatum (R x H)) : Prop :=
  ∃ η : RemainderDatum (L x H), IsBasicRemainder x H η ∧
    (remainderTail x H η).totient = ζ.d ∧
    ∀ i : Fin (R x H), ζ.primes i = remainderPrime η (i.val+1)

def M (x : ℝ) (H : ℕ) (f : ℝ → ℝ) : ℝ := by
  classical
  exact ∑ᶠ ζ : PrefixDatum (R x H),
    if IsPrefixDatum x H ζ then
      f ((ell ζ.d : ℝ) / ζ.d) / ((ζ.d : ℝ) * ∏ i : Fin (R x H), (ζ.primes i - 1 : ℕ))
    else 0

def massError (x : ℝ) (H : ℕ) (t : ℝ) : ℝ :=
  V t * Real.log x / (t * G x (m x)) - M x H (fun _ => 1) / G x (m x)



def N (k : ℕ) (x : ℝ) : ℝ := by
  classical
  exact (((Finset.Icc 1 ⌊x⌋₊).filter fun v =>
    IsTotient v ∧ (k : ℝ) * x < ell v ∧ (ell v : ℝ) ≤ (k+1 : ℝ) * x).card : ℝ)

def fk (k : ℕ) (r : ℝ) : ℝ := min 1 ((k+1 : ℝ) / r) - min 1 ((k : ℝ) / r)



lemma isTotient_pos {d : ℕ} (hd : IsTotient d) : 0 < d := by
  obtain ⟨n, hn, rfl⟩ := hd
  exact Nat.totient_pos.mpr hn

lemma ell_spec {d : ℕ} (hd : IsTotient d) : 0 < ell d ∧ (ell d).totient = d := by
  classical
  simpa only [ell, dite_eq_left hd] using Nat.find_spec hd

lemma ell_le {d n : ℕ} (hn : 0 < n) (hφ : n.totient = d) : ell d ≤ n := by
  classical
  have hd : IsTotient d := ⟨n, hn, hφ⟩
  simpa only [ell, dite_eq_left hd] using Nat.find_min' hd ⟨hn, hφ⟩

lemma le_ell {d : ℕ} (hd : IsTotient d) : d ≤ ell d := by
  calc d = (ell d).totient := (ell_spec hd).2.symm
       _ ≤ ell d := Nat.totient_le _

lemma one_le_ell_ratio {d : ℕ} (hd : IsTotient d) : 1 ≤ (ell d : ℝ) / d := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (isTotient_pos hd)
  rw [le_div_iff₀ hdpos, one_mul]
  exact_mod_cast le_ell hd

end TotientAsymptotic

end

end OAI
