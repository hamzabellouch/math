import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationPrime

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation
open Construction Conclusion Filter HistoryBulkReferencePeriodicMeanSource
open HistorySignedResidueFactorization ScaleBudget

theorem frame_prime_mean_error_eventually (d : Decomposition) (Bs BD Bz : ℝ)
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
      (α : Type*) [Fintype α] (μ : FinitePrior α)
      (x y : α→Frame.Source (C:=C) (l:=l))
      (π : α→Equiv.Perm (Fin (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).length)),
      (∀u i,(y u i).val=(x u (π u i)).val) →
      (∀u,μ.mass u≠0 → (assignmentPrior C.sources _).mass (x u)≠0) →
      (∀u,μ.mass u≠0 → ∀i:Fin (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).length,
        ((Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).get i).role≠.bulk →
        (x u i).val=(r.leftSource i).val) →
      ‖μ.cmean (fun u=>r.sourceMean σ (x u) (y u))-
        oldCompensation r.left r.right * μ.cmean (fun u=>
          staticPairMask (r.newLeft (x u)) (r.newRight (y u)) (spectatorList spectator ds)*
            r.principal σ (x u) (y u))‖ ≤
        ((r.left.compensationProduct:ℝ)*(r.right.compensationProduct:ℝ))*
          (30*Real.exp (-Real.exp (giant.target*L))) := by
  filter_upwards [frame_prime_error_eventually d Bs BD Bz hBs hdepth] with L hL
  intro E C hG hGu hcl hcu hb hd spectator hspec ds hds l hl r σ α _ μ x y π hnew hx hfixed
  apply cmean_approximation_of_source_identity μ r.left r.right
    (fun u=>((r.newLeft (x u)).root.small.map SmallSlot.value++spectatorList spectator ds).Pairwise Nat.Coprime ∧
      ((r.newRight (y u)).root.small.map SmallSlot.value++spectatorList spectator ds).Pairwise Nat.Coprime)
    (fun u=>r.sourceMean σ (x u) (y u)) (fun u=>r.periodic σ (x u) (y u))
    (fun u=>r.principal σ (x u) (y u)) (30*Real.exp (-Real.exp (giant.target*L))) (by positivity)
  · intro u _
    exact r.sourceMean_eq σ (x u) (y u) (π u) (hnew u)
  · intro u hu _
    exact hL E C hG hGu hcl hcu hb hd spectator hspec ds hds l hl r σ
      (x u) (y u) (hx u hu) (hfixed u hu)

end Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation

end

end OAI
