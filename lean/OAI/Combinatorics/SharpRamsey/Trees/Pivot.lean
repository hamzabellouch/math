import Mathlib
import OAI.Combinatorics.SharpRamsey.Trees.PivotLosses

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence GeometricCover PivotGeometry TreeDecoder SourceScales Filter
open scoped Classical BigOperators Topology
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

def Header (q b : ℝ) (r : ℕ)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)))
    (s t : ℕ) : Prop :=
  0<s ∧ 0<t ∧ s≤U.1.card ∧ t≤U.2.card ∧
    q^r*exp (-(b+log 4))≤(s:ℝ)*t ∧ (s:ℝ)*t≤2*q^r

structure Book (q b τ P H : ℝ) (r : ℕ) where
  library : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)) →
    ℕ → ℕ → Finset (Finset (Projectivization K V))
  valid : ∀ U s t,Header q b r U s t →
    (∀ W∈library U s t,W⊆U.1 ∧ (W.card:ℝ)≤100000*q^r/t) ∧
    (∀ S T,S⊆U.1 → S.card=s → T⊆U.2 → T.card=t →
      (incidenceCount S T:ℝ)≤(4*τ)*(s:ℝ)*t/q →
      ∃ W∈library U s t,(99/100:ℝ)*s≤(S∩W).card) ∧
    log (((library U s t).card:ℝ)+1)≤
      H*q*P*(log ((U.1.card:ℝ)/s)+log ((U.2.card:ℝ)/t)+P)
  invalid : ∀ U s t,¬Header q b r U s t → library U s t=∅

def Book.ofValidated (q b τ P H : ℝ) (r : ℕ)
    (hv : ∀ U s t,Header (K:=K) (V:=V) q b r U s t →
      Validated q P H r U.1 U.2 s t (4*τ)) : Book (K:=K) (V:=V) q b τ P H r where
  library U s t := if hh : Header q b r U s t then (hv U s t hh).choose else ∅
  valid U s t hh := by
    simp only [dite_eq_left hh]
    exact (hv U s t hh).choose_spec
  invalid U s t hh := dite_eq_right hh

variable [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma trimmed_header {n : ℕ} (hdim : Module.finrank K V=n+3)
    (A : Finset (Projectivization K V)) (B : Finset (Projectivization K (Module.Dual K V)))
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) (b τ : ℝ)
    (hA : A.Nonempty) (hB : B.Nonempty) (hτ : 0≤τ)
    (htrimA : (9/10:ℝ)*A.card≤(A∩U.1).card)
    (htrimB : (9/10:ℝ)*B.card≤(B∩U.2).card)
    (hprod : (Nat.card K:ℝ)^(n+3)*exp (-b)≤(A.card:ℝ)*B.card)
    (hsp : (incidenceCount A B:ℝ)≤τ*(A.card:ℝ)*B.card/Nat.card K)
    (hsparse : (incidenceCount A B:ℝ)≤(A.card:ℝ)*B.card/(40000*Nat.card K)) :
    Header (Nat.card K) b (n+3) U (A∩U.1).card (B∩U.2).card := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.zero_lt_one.trans (Finite.one_lt_card (α:=K))
  have ha : (0:ℝ)<A.card := by exact_mod_cast card_pos.mpr hA
  have hb : (0:ℝ)<B.card := by exact_mod_cast card_pos.mpr hB
  refine ⟨by exact_mod_cast (by linarith : (0:ℝ)<(A∩U.1).card),
    by exact_mod_cast (by linarith : (0:ℝ)<(B∩U.2).card),
    card_le_card inter_subset_right,card_le_card inter_subset_right,?_,?_⟩
  · exact (trimmed_inputs A U.1 B U.2 (Nat.card K) ((Nat.card K:ℝ)^(n+3)) τ b
      hq hτ (by linarith) (by linarith) hprod hsp).1
  · apply le_trans _ (sparse_product_bound_two hdim A B (hsparse.trans ?_))
    · exact mul_le_mul (by exact_mod_cast card_le_card (inter_subset_left (s₁:=A) (s₂:=U.1)))
        (by exact_mod_cast card_le_card (inter_subset_left (s₁:=B) (s₂:=U.2)))
        (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
theorem Book.input {n : ℕ} (hdim : Module.finrank K V=n+3) {b τ P H : ℝ}
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3))
    (A : Finset (Projectivization K V)) (B : Finset (Projectivization K (Module.Dual K V)))
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)))
    (hA : A.Nonempty) (hB : B.Nonempty) (hτ : 0≤τ)
    (htrimA : (9/10:ℝ)*A.card≤(A∩U.1).card)
    (htrimB : (9/10:ℝ)*B.card≤(B∩U.2).card)
    (hprod : (Nat.card K:ℝ)^(n+3)*exp (-b)≤(A.card:ℝ)*B.card)
    (hsp : (incidenceCount A B:ℝ)≤τ*(A.card:ℝ)*B.card/Nat.card K)
    (hsparse : (incidenceCount A B:ℝ)≤(A.card:ℝ)*B.card/(40000*Nat.card K)) :
    ∃ d : Input n A B b,(d.U,d.UT)=U ∧ d.W∈book.library U (A∩U.1).card (B∩U.2).card ∧ d.W⊆U.1 := by
  have hh := trimmed_header hdim A B U b τ hA hB hτ htrimA htrimB hprod hsp hsparse
  obtain ⟨hF,hc,_⟩ := book.valid U _ _ hh
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.zero_lt_one.trans (Finite.one_lt_card (α:=K))
  obtain ⟨W,hW,hWU,hn,hfrac,hratio⟩ := first_source A U.1 B U.2 (Nat.card K) τ b (n+3)
    hA hB hq hτ htrimA htrimB hprod hsp (book.library U _ _) hF hc
  exact ⟨⟨U.1,U.2,W,hA,hB,htrimA,htrimB,hn,hfrac,hratio,hprod,hsparse⟩,rfl,hW,hWU⟩

end
end SharpLogRamsey.ActualPivot

end

end OAI
