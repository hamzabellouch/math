import Mathlib
import OAI.Combinatorics.Chromatic.Walls.QuantumTorusChartCompletion
import OAI.Combinatorics.Chromatic.Walls.TruncatedFactorization
import OAI.Combinatorics.Chromatic.GradedAlgebra.KernelTraceLog

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit
noncomputable section
variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)

lemma strict_mul_through (V : M→Prop) (hV : ∀a b,V a→V b→V (a+b))
    (a b : PowerSeries (Torus v Ω)) (N : ℕ)
    (ha : constantCoeff a=1) (hb : constantCoeff b=1)
    (hsA : ∀n,n+1≤N→SupportedOn v Ω V (coeff (n+1) a))
    (hsB : ∀n,n+1≤N→SupportedOn v Ω V (coeff (n+1) b)) :
    ∀n,n+1≤N→SupportedOn v Ω V (coeff (n+1) (a*b)) :=by
  intro n hn
  rw [coeff_mul_succ a b n ha hb]
  apply SupportedOn.add v Ω ((hsA n hn).add v Ω (hsB n hn))
  apply SupportedOn.sum v Ω _ _ V
  intro i hi
  apply (hsA i.val (by omega)).mul v Ω hV
  have he : n-i.val=(n-i.val-1)+1:=by omega
  rw [he]
  exact hsB (n-i.val-1) (by omega)

lemma chart_three_truncated_unique (h : M→+ℝ) (f : CompletedPositive v Ω C)
    (a b c : PowerSeries (Torus v Ω)) (N : ℕ)
    (ha0 : constantCoeff a=1) (hb0 : constantCoeff b=1) (hc0 : constantCoeff c=1)
    (he : a*b*c=f.val)
    (ha : ∀n,n+1≤N→∀m,coeff (n+1) a m≠0→0<h m)
    (hb : ∀n,n+1≤N→∀m,coeff (n+1) b m≠0→h m=0)
    (hc : ∀n,n+1≤N→∀m,coeff (n+1) c m≠0→h m<0) :
    ∀n≤N,coeff n a=coeff n (chartPositive v Ω C h f).val ∧
      coeff n b=coeff n (chartZero v Ω C h f).val ∧
      coeff n c=coeff n (chartNegative v Ω C h f).val :=by
  classical
  have haP : ∀n,n+1≤N→positiveProject v Ω h (coeff (n+1) a)=coeff (n+1) a:=by
    intro n hn
    exact (Finsupp.filter_eq_self_iff _ _).mpr (ha n hn)
  have hbP : ∀n≤N,positiveProject v Ω h (coeff n b)=0:=by
    intro n hn
    cases n with
    | zero=>rw [coeff_zero_eq_constantCoeff,hb0]; exact positiveProject_one v Ω h
    | succ n=>
      apply (Finsupp.filter_eq_zero_iff _ _).mpr
      intro m hm
      by_contra hh
      have H:=hb n hn m hh
      linarith
  have hcP : ∀n≤N,positiveProject v Ω h (coeff n c)=0:=by
    intro n hn
    cases n with
    | zero=>rw [coeff_zero_eq_constantCoeff,hc0]; exact positiveProject_one v Ω h
    | succ n=>
      apply (Finsupp.filter_eq_zero_iff _ _).mpr
      intro m hm
      by_contra hh
      have H:=hc n hn m hh
      linarith
  have hbQ : ∀n,n+1≤N→zeroProject v Ω h (coeff (n+1) b)=coeff (n+1) b:=by
    intro n hn
    exact (Finsupp.filter_eq_self_iff _ _).mpr (hb n hn)
  have hcQ : ∀n,n+1≤N→zeroProject v Ω h (coeff (n+1) c)=0:=by
    intro n hn
    apply (Finsupp.filter_eq_zero_iff _ _).mpr
    intro m hm
    by_contra hh
    have H:=hc n hn m hh
    linarith
  exact three_truncated_unique (positiveProject v Ω h) (zeroProject v Ω h)
    (supportedSubring v Ω (nonpositiveCone h)) (nonpositive_iff v Ω h)
    f.val a b c N ha0 hb0 hc0 (fun n hn=>congrArg (coeff n) he) haP hbP hcP hbQ hcQ
end
end ElementaryPositivity.QuantumTorus

end

end OAI
