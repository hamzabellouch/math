import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusBoundPositive
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesXiSelectedBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction Conclusion Filter HistorySignedXiTransport HistorySignedDecode HistorySymbolicEncoding

theorem selected_supportedHistoryPairXi_eq_residueTest_eventually (d : Decomposition)
    (Bs BD Bz : ℝ) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase → C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 → |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀l≤k,
      let seed := Template.initial (2*(bulkSize k L/2)) k
      let V := frequencyBound Bs BD Bz k L
      ∀(x y : OuterSample C.sources (Template.current seed l) C.giant)
        (s t Xp Xm : ℤ) (c e : HistoryChoices C.sources seed V l),
      (outerPrior C.sources (Template.current seed l) C.giant).mass x≠0 →
      (outerPrior C.sources (Template.current seed l) C.giant).mass y≠0 →
      choicesMass C.sources seed V l c≠0 → choicesMass C.sources seed V l e≠0 →
      0<Xp → 0<Xm →
      ∀outside : List ℕ, (∀q∈outside,Nat.Prime q) →
      let a := outerState C.sources (Template.current seed l) C.giant x s
      let b := outerState C.sources (Template.current seed l) C.giant y t
      let h := decodeHistory C.sources seed V l a c
      let g := decodeHistory C.sources seed V l b e
      ∀(hs : h.Supported V outside)(gs : g.Supported V outside)
        (M : ℕ)(hd : pairModulus h g outside ∣ M) (bcount scount : ℕ) (X tb td G : ℝ),
      supportedHistoryPairXi d V outside bcount scount X tb td G
        (decodeHistory C.sources seed V l (giantState a Xp Xm) c)
        (decodeHistory C.sources seed V l (giantState b Xp Xm) e) =
      (by classical exact if Nat.Coprime Xp.natAbs Xm.natAbs then
        (((h.compensationProduct:ℂ)*(g.compensationProduct:ℂ))*
          actualRealXi bcount scount X tb td G outside h g hs gs
            (signedGiantSample h Xp Xm) (signedGiantSample g Xp Xm)*
          liftedResidueTest (residueTransform d) V outside h g M hd
            ((Xp:ZMod M),(Xm:ZMod M))) else 0) := by
  filter_upwards [selected_changed_decoded_largePrimes_eventually d Bs BD Bz hk] with L hL
  intro E C hG hcl hcu hb hd l hl
  dsimp only
  intro x y s t Xp Xm c e hx hy hc he hp hm outside hout hs gs M hdiv bcount scount X tb td G
  let : NeZero (pairModulus
      (decodeHistory C.sources (Template.initial (2*(bulkSize k L/2)) k)
        (frequencyBound Bs BD Bz k L) l
        (outerState C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) C.giant x s) c)
      (decodeHistory C.sources (Template.initial (2*(bulkSize k L/2)) k)
        (frequencyBound Bs BD Bz k L) l
        (outerState C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) C.giant y t) e)
      outside) := ⟨ne_of_gt (pairModulus_pos _ _ hs gs (fun q hq=>(hout q hq).pos))⟩
  exact supportedHistoryPairXi_eq_residueTest d C.sources _ _ outside l _ _ c e
    (Template.assignedSlots_matches _ _ _) (Template.assignedSlots_matches _ _ _)
    Xp Xm hp hm hs gs
    (hL E C hG hcl hcu hb hd l hl x s Xp Xm c hx hc)
    (hL E C hG hcl hcu hb hd l hl y t Xp Xm e hy he)
    M hdiv bcount scount X tb td G

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
