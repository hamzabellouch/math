import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationRootTestMixed
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationRootTestUnit
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseSelectedInputs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation
open Construction Conclusion CanonicalHistoryLeafBulk Filter
open HistoryBulkReferencePeriodicMeanSource HistoryBulkSupportConverse

theorem selected_masked_rootValue_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {depth : ℕ} (hdepth : 0<depth) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz depth L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase → C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
    ∀spectator : PrimeSource,
      (∀p : spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
    ∀ds : Fin (2*(bulkSize depth L/2))→spectator.Sample,∀l≤depth,
    ∃hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz depth L j<q,
    ∀r : Frame (l:=l) C (spectatorList spectator ds),
    ∀(σ : Equiv.Perm (Frame.Slots (depth:=depth) (L:=L) (l:=l)))
      (x y : Frame.Source (C:=C) (l:=l)),
      (assignmentPrior C.sources _).mass x≠0 →
      (∀u : Frame.Slots (depth:=depth) (L:=L) (l:=l),
        bulkSamples C.sources (2*(bulkSize depth L/2)) depth l y u.1 u.2 =
          bulkSamples C.sources (2*(bulkSize depth L/2)) depth l x (σ u).1 (σ u).2) →
      (∀i:Fin (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).length,
        ((Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).get i).role≠.bulk →
        (x i).val=(r.leftSource i).val) →
      (∀i:Fin (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).length,
        ((Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).get i).role≠.bulk →
        (y i).val=(r.rightSource i).val) →
      (staticPairMask (r.newLeft x) (r.newRight y) (spectatorList spectator ds)*r.principal σ x y =
        staticPairMask (r.newLeft x) (r.newRight y) (spectatorList spectator ds)*
          (r.giantIntegral x*r.rootValue false hV σ x*r.unitBMean x)) ∧
      (staticPairMask (r.newLeft x) (r.newRight y) (spectatorList spectator ds)*r.mixedBlockAverage σ x y =
        staticPairMask (r.newLeft x) (r.newRight y) (spectatorList spectator ds)*
          (Frame.extractedDensity (C:=C) x*r.rootValue true hV σ x*r.mixedBMean x)) := by
  filter_upwards [selected_source_inputs_eventually d Bs BD Bz hdepth] with L hL
  intro E C hG hcl hcu hb hd spectator hspec ds l hl
  obtain ⟨_,hfreq,hout⟩ := hL E C hG hcl hcu hb hd spectator hspec
  have hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz depth L j<q := by
    intro q hq j hj
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact hout (ds i) j (hj.trans hl)
  refine ⟨hV,?_⟩
  intro r σ x y hx hbulk hfixed hfixed'
  have hf := fun j (hj : j≤l)=>hfreq j (hj.trans hl)
  exact ⟨r.masked_principal_eq_rootValue hV σ x y hx hf hbulk hfixed hfixed',
    r.masked_mixedBlockAverage_eq_rootValue hV σ x y hx hf hbulk hfixed hfixed'⟩

end Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation

end

end OAI
