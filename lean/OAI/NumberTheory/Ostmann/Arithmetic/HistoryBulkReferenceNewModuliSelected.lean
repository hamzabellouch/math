import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceNewModuli
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseSelectedInputs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepresentativeIntegerAdmissible

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceNewModuli
open Construction Conclusion Filter HistoryPairBulkTransport
open HistoryGiantReferenceMean HistorySignedXiTransport
open HistoryBulkSupportConverse HistoryRepresentativeIntegerAdmissible

theorem selected_newCRTCompatible_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase → C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ spectator : PrimeSource,
      (∀ p : spectator.Sample, Real.exp ((1/2000:ℝ)*L) ≤ Real.log (p:ℕ) ∧
        Real.log (p:ℕ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      ∀ ds : Fin (2*(bulkSize k L/2)) → spectator.Sample,
      (∀ i, spectator.law.mass (ds i) ≠ 0) →
      let outside := spectatorList spectator ds
      ∀ l ≤ k,
      let seed := Template.initial (2*(bulkSize k L/2)) k
      let V := frequencyBound Bs BD Bz k L
      let T := Template.current seed l
      ∀ (x x₀ y₀ : SourceAssignment C.sources T) (snew s t : ℤ) (gp gm : ℕ) (P Q : ℤ)
        (cnew c e : HistoryChoices C.sources seed V l),
      (assignmentPrior C.sources T).mass x ≠ 0 →
      (assignmentPrior C.sources T).mass x₀ ≠ 0 →
      (assignmentPrior C.sources T).mass y₀ ≠ 0 →
      choicesMass C.sources seed V l c ≠ 0 → choicesMass C.sources seed V l e ≠ 0 →
      (∀ i : Fin T.length, (T.get i).role ≠ .bulk → (x i).val = (x₀ i).val) →
      let newh := assignedHistory C.sources seed V l snew gp gm x cnew
      let oldh := decodeHistory C.sources seed V l (giantState (sourceState C.sources T x₀ s) P Q) c
      let oldk := decodeHistory C.sources seed V l (giantState (sourceState C.sources T y₀ t) P Q) e
      oldh.Supported V outside → oldk.Supported V outside →
      NewCRTCompatible newh oldh oldk outside k := by
  filter_upwards [selected_source_inputs_eventually d Bs BD Bz hk] with L hL
  intro E C hG hcl hcu hb hd spectator hspec ds hds
  dsimp only
  intro l hl x x₀ y₀ snew s t gp gm P Q cnew c e hx hx₀ hy₀ hc he hfixed hs ks
  obtain ⟨hsep,hfreq,houtfreq⟩ := hL E C hG hcl hcu hb hd spectator hspec
  have hf : ∀ j ≤ l, ∀ origin, (C.sources origin).AboveFrequency
      (frequencyBound Bs BD Bz k L j) := fun j hj => hfreq j (hj.trans hl)
  have hout : ∀ q ∈ spectatorList spectator ds,
      ∃ p : spectator.Sample, p.val = q ∧ spectator.law.mass p ≠ 0 := by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact ⟨ds i,rfl,hds i⟩
  have hprimefreq : ∀ q ∈ spectatorList spectator ds, q.Prime ∧
      ∀ j ≤ l, frequencyBound Bs BD Bz k L j < q := by
    intro q hq
    obtain ⟨p,rfl,_⟩ := hout q hq
    exact ⟨spectator.prime p.val p.property, fun j hj => houtfreq p j (hj.trans hl)⟩
  have had := decoded_integer_pair_admissible C hsep (frequencyBound Bs BD Bz k L)
    (spectatorList spectator ds) l x₀ y₀ s t P Q c e hx₀ hy₀ hc he hf hprimefreq hs ks
  exact assigned_newCRTCompatible C spectator hsep (frequencyBound Bs BD Bz k L)
    (spectatorList spectator ds) l k s t snew P.toNat Q.toNat gp gm
    x₀ y₀ x c e cnew hs ks had hx hc he hfixed hout hf

end Ostmann.Arithmetic.HistoryBulkReferenceNewModuli

end

end OAI
