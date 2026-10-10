import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentReferenceTermActual

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIndependentReferenceTerm
open Construction Conclusion Filter Construction.CanonicalOccurrenceTransport
open HistoryPairBulkTransport HistoryBulkSupportConverse HistoryGiantReferenceMean

def SelectedReferenceEquality {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource) : Prop :=
  let m := 2*(bulkSize k L/2)
  let seed := Template.initial m k
  let V := frequencyBound Bs BD Bz k L
  ∀ (outside : List ℕ) (l K : ℕ), l≤K → l≤k →
  ∀ (x₀ y₀ x y : SourceAssignment C.sources (Template.current seed l))
    (s t : ℤ) (gp gm : ℕ) (c e : HistoryChoices C.sources seed V l),
  let H := assignedHistory C.sources seed V l s gp gm x₀ c
  let J := assignedHistory C.sources seed V l t gp gm y₀ e
  ∀ (hs : H.Supported V outside) (ks : J.Supported V outside)
    (b sw : ℕ) (X tb td G : ℝ) (Jmul : ℤ→ℤ→ℂ) (P Q : ℤ),
  ∀π : Equiv.Perm (Fin (Template.current seed l).length),
  (∀i, (y₀ i).val=(x₀ (π i)).val) →
  (∀i, (y i).val=(x (π i)).val) →
  (∀i : Fin (Template.current seed l).length,
    ((Template.current seed l).get i).role≠.bulk → (x i).val=(x₀ i).val) →
  (∀i : Fin (Template.current seed l).length,
    ((Template.current seed l).get i).role≠.bulk → (y i).val=(y₀ i).val) →
  (assignmentPrior C.sources (Template.current seed l)).mass y₀≠0 →
  (assignmentPrior C.sources (Template.current seed l)).mass y≠0 →
  (assignmentPrior C.sources (Template.current seed l)).mass x₀≠0 →
  (assignmentPrior C.sources (Template.current seed l)).mass x≠0 →
  choicesMass C.sources seed V l c≠0 → choicesMass C.sources seed V l e≠0 →
  0<P → 0<Q → (∀q∈outside,∃p : spectator.Sample,(p:ℕ)=q) →
  sourceIntegrand d C.sources seed V outside l
    (sourceState C.sources (Template.current seed l) x s)
    (sourceState C.sources (Template.current seed l) y t)
    c e Jmul b sw X tb td G P Q =
  referenceTerm C V outside l K x₀ y₀ x y s t gp gm c e hs ks b sw X tb td G Jmul P Q

theorem selected_reference_equality_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase → C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 → |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀spectator : PrimeSource,
      (∀p : spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) → SelectedReferenceEquality C spectator := by
  filter_upwards [selected_source_inputs_eventually d Bs BD Bz hk] with L hL
  intro E C hG hcl hcu hb hd spectator hspec
  obtain ⟨hsep,hfreq,houtfreq⟩ := hL E C hG hcl hcu hb hd spectator hspec
  dsimp only [SelectedReferenceEquality]
  intro outside l K hle hl x₀ y₀ x y s t gp gm c e hs ks b sw X tb td G Jmul P Q
    π hold hmatch hfixed hfixedy hy₀ hy hx₀ hx hc he hp hq houtside
  have hprime : ∀q∈outside,q.Prime := by
    intro q hq
    obtain ⟨p,rfl⟩ := houtside q hq
    exact spectator.prime p.val p.property
  apply sourceIntegrand_eq_referenceTerm_of_source_masses C (frequencyBound Bs BD Bz k L)
    outside l K x₀ y₀ x y s t gp gm c e hs ks b sw X tb td G Jmul P Q
    hsep hle π hold hmatch hfixed hy₀ hx₀ hfixedy hy hx hc he (fun j hj => hfreq j (hj.trans hl)) hp hq hprime
  intro q hq j hj
  obtain ⟨p,rfl⟩ := houtside q hq
  exact houtfreq p j (hj.trans hl)

end Ostmann.Arithmetic.HistoryBulkIndependentReferenceTerm

end

end OAI
