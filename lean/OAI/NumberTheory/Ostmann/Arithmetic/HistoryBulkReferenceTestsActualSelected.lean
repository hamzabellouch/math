import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTestsActualFinite

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceTestsActual
open Construction Conclusion Filter Construction.CanonicalOccurrenceTransport
open HistoryPairBulkTransport HistoryBulkSupportConverse HistoryPairSmoothXi
open HistoryBulkReferenceTests HistoryBulkReferenceScalarCoordinates HistorySignedSpectatorCRT
open HistoryBulkResidueNormSum HistoryBulkSpectatorReferenceRaw HistoryFrequencyResidues

def SelectedInsertedSupport {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource) : Prop :=
  let m := 2*(bulkSize k L/2)
  let seed := Template.initial m k
  let V := frequencyBound Bs BD Bz k L
  ∀ (outside : List ℕ) (l K : ℕ), l≤K → l≤k →
  ∀ (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (x₀ x : SourceAssignment C.sources (Template.current seed l))
    (s t : ℤ) (gp gm gp' gm' : ℕ) (c e : HistoryChoices C.sources seed V l),
  let perm := leafBulkAssignmentPermutation (bulkSize k L/2) k l C.bulk
    (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ
  let H := assignedHistory C.sources seed V l s gp gm x₀ c
  let J := assignedHistory C.sources seed V l t gp gm (perm x₀) e
  let Hn := assignedHistory C.sources seed V l s gp' gm' x c
  let Jn := assignedHistory C.sources seed V l t gp' gm' (perm x) e
  ∀ (hs : H.Supported V outside) (ks : J.Supported V outside)
    (b sw : ℕ) (X tb td G : ℝ),
  (∀i : Fin (Template.current seed l).length,
    ((Template.current seed l).get i).role≠.bulk → (x i).val=(x₀ i).val) →
  (assignmentPrior C.sources (Template.current seed l)).mass x≠0 →
  choicesMass C.sources seed V l c≠0 → choicesMass C.sources seed V l e≠0 →
  0<gp' → 0<gm' →
  (assignedRoot C.sources (Template.current seed l) s gp' gm' x).Coprime outside →
  (assignedRoot C.sources (Template.current seed l) t gp' gm' (perm x)).Coprime outside →
  orderedSourceIndicatorB C.sources m k H J hs ks
    (root_matches (assignedLabels C.sources seed V l s gp gm x₀ c)) x gp' gm'≠0 →
  pairedRealXi b sw X tb td G H J hs ks
    (insertOrderedGiants m k H J hs
      (root_matches (assignedLabels C.sources seed V l s gp gm x₀ c))
      (orderedSourceValues C.sources m k l x)
      (fun a => if a then (gm':ℝ) else (gp':ℝ)))≠0 →
  independentRTest K H J σ (gp',gm')
    (sourceBulkUnits ((pairedFrequencyProduct H J)^(K+2)) C.sources m k l x)≠0 →
  ∀g : (q:ℕ)→ZMod q→ℂ,
  (∀q∈outside,∃p : spectator.Sample,(p:ℕ)=q) →
  (∀q∈outside,g q 0=0) →
  residuePairSpectator g outside outside.prod Hn Jn (gp',gm')≠0 →
  Hn.Supported V outside ∧ Jn.Supported V outside

theorem selected_inserted_support_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase → C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 → |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀spectator : PrimeSource,
      (∀p : spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) → SelectedInsertedSupport C spectator := by
  filter_upwards [selected_source_inputs_eventually d Bs BD Bz hk] with L hL
  intro E C hG hcl hcu hb hd spectator hspec
  obtain ⟨hsep,hfreq,houtfreq⟩ := hL E C hG hcl hcu hb hd spectator hspec
  dsimp only [SelectedInsertedSupport]
  intro outside l K hle hl σ x₀ x s t gp gm gp' gm' c e hs ks b sw X tb td G
    hfixed hx hc he hp hm hroot hroot' hB hXi hR g houtside hg hD
  have hprime : ∀q∈outside,q.Prime := by
    intro q hq
    obtain ⟨p,rfl⟩ := houtside q hq
    exact spectator.prime p.val p.property
  apply inserted_pair_supported_of_actual_finite_tests C (frequencyBound Bs BD Bz k L)
    outside l K σ x₀ x s t gp gm gp' gm' c e hs ks b sw X tb td G
    hsep hle hfixed hx hc he (fun j hj=>hfreq j (hj.trans hl)) hp hm hroot hroot'
    hB hXi hR g hprime hg ?_ hD
  intro q hq j hj
  obtain ⟨p,rfl⟩ := houtside q hq
  exact houtfreq p j (hj.trans hl)

end Ostmann.Arithmetic.HistoryBulkReferenceTestsActual

end

end OAI
