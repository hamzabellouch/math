import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.OriginalAmbientDomination
import OAI.Combinatorics.RamseyFive.Geometry.FiniteNode
import OAI.Combinatorics.RamseyFive.Geometry.ProducedPairOriginal

namespace OAI

section
namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
lemma eventMass_pure_filter_of_not {Ω : Type*} [Fintype Ω] (x : Ω) (P : Ω→Prop) (h : ¬P x) :
    eventMass (pureLaw x) (Finset.univ.filter P)=0 := by
  unfold eventMass
  apply Finset.sum_eq_zero
  intro y hy
  have hp := (Finset.mem_filter.mp hy).2
  have hne : y≠x := fun he=>h (he ▸ hp)
  simp [pureLaw,hne]
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem guardedNode_original (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ M : ℝ)
    (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ≤c*δ^2) :
    (∀b,eventMass (guardedNodeLaw pred σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀ c δ τ M hδ)
      (Finset.univ.filter fun out=>Excludes b (out.map Prod.fst))≤
        (50*(Nat.card K:ℝ)/(9*(c*δ)))*(((A₀.filter fun a=>Incident a b).card:ℝ)/A₀.card)) ∧
    (∀a,eventMass (guardedNodeLaw pred σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀ c δ τ M hδ)
      (Finset.univ.filter fun out=>Excludes a (out.map Prod.snd))≤
        (50*(Nat.card K:ℝ)/(9*((9:ℝ)/10*δ)))*(((B₀.filter (Incident a)).card:ℝ)/B₀.card)) := by
  unfold guardedNodeLaw
  split_ifs with hr
  · have hA := nonempty_of_positive_trim (A₀∩UA) A₀ hA₀ δ hδ hr.1
    have hB := nonempty_of_positive_trim (B₀∩UB) B₀ hB₀ δ hδ hr.2.1
    exact finiteNode_original pred hd hq3 (A₀∩UA) A₀ UA hA Finset.inter_subset_left Finset.inter_subset_right
      (B₀∩UB) B₀ UB hB Finset.inter_subset_left Finset.inter_subset_right c δ M hc hc9 hδ hr.1 hr.2.1
      (original_ready_sparse A₀ UA B₀ UB c δ τ hc.le hδ.le hτ hr) _ _ _
  · constructor <;> intro z <;>
      rw [eventMass_pure_filter_of_not _ _ (by simp [Excludes])] <;> positivity
end SharpRamseyFive.ProjectiveIncidence
end

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem nextAmbientCapLaw_original {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : 3≤Nat.card K) (A UA : Finset (ℙ K V)) (hA : A.Nonempty) (hAU : A⊆UA)
    (B B₀ UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty) (hBB₀ : B⊆B₀)
    (γ : ℝ) (hγ : 0<γ) (htrim : γ*B₀.card≤B.card)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences A B≤(9:ℝ)/10*A.card*B.card)
    (n : ℕ) (hn : 0<n) (hlen : 20*(Nat.card K:ℝ)*Real.log ((UA.card:ℝ)/A.card)≤n)
    (MB : ℝ) (Y : Option (Finset (ℙ K (Dual K V)))) (a : ℙ K V) :
    eventMass (nextAmbientCapLaw A UA B UB hB n (Nat.card K)
      ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^(d+1)/B.card) MB Y)
      (Finset.univ.filter (Excludes a))≤
    (50*(Nat.card K:ℝ)/(9*(((9:ℝ)/10)*γ)))*(((B₀.filter (Incident a)).card:ℝ)/B₀.card) := by
  cases Y with
  | none =>
    change eventMass (pureLaw (none : Option (Finset (ℙ K V))))
      (Finset.univ.filter (Excludes a))≤_
    rw [excludes_pure_none]
    positivity
  | some Y =>
    dsimp only [nextAmbientCapLaw]
    split_ifs with hY
    · have hC := hY.source_nonempty hB
      exact geometric_ambient_original hdim hd hq A UA hA hAU B B₀ (B∩(UB∩Y)) (UB∩Y)
        hC (hC.mono Finset.inter_subset_right) Finset.inter_subset_left
        Finset.inter_subset_right hBB₀ (9/10) γ (by norm_num) (by norm_num) hγ
        hY.2.2 htrim hsparse n hn hlen a
    · rw [excludes_pure_none]
      positivity

theorem second_ambient_unconditioned {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : 3≤Nat.card K) (A UA : Finset (ℙ K V)) (hA : A.Nonempty) (hAU : A⊆UA)
    (B B₀ UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty) (hBB₀ : B⊆B₀)
    (γ : ℝ) (hγ : 0<γ) (htrim : γ*B₀.card≤B.card)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences A B≤(9:ℝ)/10*A.card*B.card)
    (n : ℕ) (hn : 0<n) (hlen : 20*(Nat.card K:ℝ)*Real.log ((UA.card:ℝ)/A.card)≤n)
    (MB : ℝ) (p : Law (Option (Finset (ℙ K (Dual K V))))) (a : ℙ K V) :
    eventMass (adaptiveLaw p (nextAmbientCapLaw A UA B UB hB n (Nat.card K)
      ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^(d+1)/B.card) MB))
      (Finset.univ.filter fun pair=>Excludes a pair.2)≤
    (50*(Nat.card K:ℝ)/(9*(((9:ℝ)/10)*γ)))*(((B₀.filter (Incident a)).card:ℝ)/B₀.card) := by
  apply adaptive_event_second_le
  intro Y
  exact nextAmbientCapLaw_original hdim hd hq A UA hA hAU B B₀ UB hB hBB₀ γ hγ htrim
    hsparse n hn hlen MB Y a

theorem first_ambient_chronology {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : 3≤Nat.card K) (S U : Finset (ℙ K (Dual K V))) (hS : S.Nonempty) (hSU : S⊆U)
    (X X₀ C W : Finset (ℙ K V)) (hC : C.Nonempty) (hW : W.Nonempty)
    (hCX : C⊆X) (hCW : C⊆W) (hXX₀ : X⊆X₀)
    (c γ : ℝ) (hc : 0<c) (hc1 : c≤1) (hγ : 0<γ)
    (hcapture : c*X.card≤C.card) (htrim : γ*X₀.card≤X.card)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences X S≤c*S.card*X.card)
    (n : ℕ) (hn : 0<n) (hlen : 20*(Nat.card K:ℝ)*Real.log ((U.card:ℝ)/S.card)≤n)
    {Z : Type*} [Fintype Z] (next : Option (Finset (ℙ K (Dual K V)))→Law Z)
    (a : ℙ K (Dual K V)) :
    eventMass (adaptiveLaw (ambientCapLaw (fun a b=>Incident b a) S U C W hW n (Nat.card K)
      ((320/c+320)*(Nat.card K:ℝ)^(d+1)/X.card)) next)
      (Finset.univ.filter fun pair=>Excludes a pair.1)≤
      (50*(Nat.card K:ℝ)/(9*(c*γ)))*(((X₀.filter (fun b=>Incident b a)).card:ℝ)/X₀.card) := by
  rw [adaptive_event_first]
  exact geometric_dual_ambient_original hdim hd hq S U hS hSU X X₀ C W hC hW hCX hCW
    hXX₀ c γ hc hc1 hγ hcapture htrim hsparse n hn hlen a
end SharpRamseyFive.ProjectiveIncidence

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α Ω J : Type*} [Fintype Ω] [Fintype J]

noncomputable def inheritedSupport (X : Finset α) (C : J→Finset α) : Finset α :=
  X.filter (fun x=>∀j,x∈C j)

noncomputable def evictionFraction (X C : Finset α) : ℝ := (X\C).card/(X.card:ℝ)

lemma evictionFraction_nonneg (X C : Finset α) : 0≤evictionFraction X C := by
  unfold evictionFraction;positivity

lemma inherited_eviction (X : Finset α) (C : J→Finset α) :
    evictionFraction X (inheritedSupport X C)≤∑j,evictionFraction X (C j) := by
  have he : X\inheritedSupport X C=Finset.univ.biUnion (fun j=>X\C j) := by
    ext x
    simp only [Finset.mem_sdiff,inheritedSupport,Finset.mem_filter,not_and,
      not_forall,Finset.mem_biUnion,Finset.mem_univ,true_and]
    aesop
  unfold evictionFraction
  rw [he,←Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_biUnion_le

lemma trim_failure_eviction (X : Finset α) (C : J→Finset α)
    (h : ((inheritedSupport X C).card:ℝ)<(9/10:ℝ)*X.card) :
    (1:ℝ)/10≤evictionFraction X (inheritedSupport X C) := by
  have hX : (0:ℝ)<X.card := by
    have hn := Nat.cast_nonneg (α:=ℝ) (inheritedSupport X C).card
    linarith
  apply (le_div_iff₀ hX).mpr
  have he : (X\inheritedSupport X C).card+(inheritedSupport X C).card=X.card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  have he' : ((X\inheritedSupport X C).card:ℝ)+(inheritedSupport X C).card=X.card := by exact_mod_cast he
  linarith

theorem trim_failure_mass (p : Law Ω) (X : Ω→Finset α) (C : Ω→J→Finset α)
    (ready : Ω→Prop) (ρ : J→ℝ)
    (hρ : ∀j,(∑ω,p ω*evictionFraction (X ω) (C ω j))≤ρ j) :
    eventMass p (Finset.univ.filter (fun ω=>ready ω ∧
      ((inheritedSupport (X ω) (C ω)).card:ℝ)<(9/10:ℝ)*(X ω).card))≤10*∑j,ρ j := by
  let E := Finset.univ.filter (fun ω=>ready ω ∧
    ((inheritedSupport (X ω) (C ω)).card:ℝ)<(9/10:ℝ)*(X ω).card)
  have hm := event_markov p (fun ω=>evictionFraction (X ω) (inheritedSupport (X ω) (C ω)))
    (fun ω=>evictionFraction_nonneg _ _) (1/10) E (by
      intro ω hω
      exact trim_failure_eviction _ _ (Finset.mem_filter.mp hω).2.2)
  have hs : (∑ω,p ω*evictionFraction (X ω) (inheritedSupport (X ω) (C ω)))≤∑j,ρ j := by
    calc
      _ ≤ ∑ω,p ω*(∑j,evictionFraction (X ω) (C ω j)) :=
        Finset.sum_le_sum (fun ω _=>mul_le_mul_of_nonneg_left (inherited_eviction _ _) (p.nonneg ω))
      _ = ∑j,∑ω,p ω*evictionFraction (X ω) (C ω j) := by
        simp_rw [Finset.mul_sum];exact Finset.sum_comm
      _ ≤ _ := Finset.sum_le_sum (fun j _=>hρ j)
  change eventMass p E≤_
  linarith

end SharpRamseyFive.FiniteEntropy

end OAI
