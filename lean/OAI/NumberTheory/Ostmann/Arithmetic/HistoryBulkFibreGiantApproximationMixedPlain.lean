import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationMixedPlainPeriodic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationMixedSource
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceSmallMultiplierSelected

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation
open Construction Conclusion Filter HistoryPairBulkTransport HistorySymbolicEncoding
open HistoryBulkReferencePeriodicMeanSource HistoryBulkReferenceSmallMultiplier
open HistorySignedResidueFactorization ScaleBudget

theorem frame_mixed_source_error_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    (hBs : 0≤Bs) {depth : ℕ} (hdepth : 0<depth) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz depth L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
    ∀ spectator : PrimeSource,
      (∀p:spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
    ∀ ds : Fin (2*(bulkSize depth L/2))→spectator.Sample,
      (∀i,spectator.law.mass (ds i)≠0) →
    ∀ l≤depth, ∀r : Frame (l:=l) C (spectatorList spectator ds),
    ∀(σ : Equiv.Perm (Frame.Slots (depth:=depth) (L:=L) (l:=l)))
      (x y : Frame.Source (C:=C) (l:=l))
      (π : Equiv.Perm (Fin (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).length)),
      (∀i,(y i).val=(x (π i)).val) →
      (assignmentPrior C.sources _).mass x≠0 →
      (∀i:Fin (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).length,
        ((Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).get i).role≠.bulk →
        (x i).val=(r.leftSource i).val) →
      ‖r.sourceMeanMixed σ x y - oldCompensation r.left r.right *
        (staticPairMask (r.newLeft x) (r.newRight y) (spectatorList spectator ds) *
          r.principalMixed σ x y)‖ ≤
        ((r.left.compensationProduct:ℝ)*(r.right.compensationProduct:ℝ)) *
          (9*Real.exp (-Real.exp (giant.target*L))) := by
  classical
  filter_upwards [frame_mixed_periodic_error_eventually d Bs BD Bz hBs hdepth,
    selected_smallMultiplier_test_eventually d Bs BD Bz hdepth] with L hAP hU
  intro E C hG hGu hcl hcu hb hd spectator hspec ds hds l hl r σ x y π hnew hx hfixed
  by_cases hg : ((r.newLeft x).root.small.map SmallSlot.value++spectatorList spectator ds).Pairwise Nat.Coprime ∧
      ((r.newRight y).root.small.map SmallSlot.value++spectatorList spectator ds).Pairwise Nat.Coprime
  · have hmask : staticPairMask (r.newLeft x) (r.newRight y) (spectatorList spectator ds)=1 := by
      simp only [staticPairMask,guardIndicator,ite_eq_left hg]
    have hfreq : r.left.root.frequency=r.s := by
      simp only [Frame.left,assignedHistory,decodeHistory_root,assignedRoot]
    have hu' := hU E C hG hcl hcu hb hd l hl
      (spectatorList spectator ds) r.left r.left_supported
    rw [hfreq] at hu'
    obtain ⟨hu,_⟩ := hu' x r.leftChoices hx hg.1
    have hpoint := hAP E C hG hGu hcl hcu hb hd spectator hspec ds hds l hl r σ x y hx hfixed hu
    rw [r.sourceMeanMixed_eq σ x y hu π hnew ,hmask,one_mul,one_mul,
      ←mul_sub,norm_mul,norm_oldCompensation]
    exact mul_le_mul_of_nonneg_left hpoint (by positivity)
  · have hmask : staticPairMask (r.newLeft x) (r.newRight y) (spectatorList spectator ds)=0 := by
      simp only [staticPairMask,guardIndicator,ite_eq_right hg]
    rw [r.sourceMeanMixed_eq_zero σ x y π hnew hmask,hmask,zero_mul,mul_zero,sub_self,norm_zero]
    positivity

end Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation

end

end OAI
