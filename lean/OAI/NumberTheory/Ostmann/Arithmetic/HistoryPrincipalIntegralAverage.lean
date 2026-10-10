import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralAverageMixed
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesLift

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPrincipalIntegralAverage
open Construction PrimeCellReplacement LogCellPartition ResidueHaar HistoryCRTIntegration
  HistorySignedResidues
open scoped BigOperators

theorem principalIntegral_pair (M : ℕ) [NeZero M] (lo hi Z : Bool→ℝ)
    (f : (Bool→ℝ)→ℂ) (F : UnitPair M→ℂ) :
    principalIntegral M lo hi Z f*(∑u:Bool→(ZMod M)ˣ,F (u false,u true))=
      primeIntegral lo hi Z f*average F := by
  rw [principalIntegral_mul_sum]
  congr 1
  exact average_equiv (Equiv.boolArrowEquivProd ((ZMod M)ˣ)) F

theorem mixedPrincipalIntegral_pair (M : ℕ) [NeZero M]
    (loI hiI G : ℝ) (φ : ℝ→ℝ) (lo hi Z : Unit→ℝ)
    (f : (Option Unit→ℝ)→ℂ) (F : MixedPair M→ℂ) :
    mixedPrincipalIntegral M loI hiI G φ lo hi Z f*
        (∑r:ZMod M,∑u:Unit→(ZMod M)ˣ,F (r,u ()))=
      mixedIntegral loI hiI G φ lo hi Z f*average F := by
  rw [mixedPrincipalIntegral_mul_sum]
  congr 1
  exact average_equiv
    (Equiv.prodCongr (Equiv.refl (ZMod M)) (Equiv.funUnique Unit ((ZMod M)ˣ))) F

theorem primeResidueTest_main {l : ℕ} (g : (q:ℕ)→ZMod q→ℂ)
    (V : ℕ→ℕ) (outside : List ℕ) (h k : History l) (M : ℕ) [NeZero M]
    (hd : pairModulus h k outside∣M) (lo hi Z : Bool→ℝ) (f : (Bool→ℝ)→ℂ) :
    principalIntegral M lo hi Z f*
        (∑u:Bool→(ZMod M)ˣ,primeResidueTest g V outside h k M hd u)=
      primeIntegral lo hi Z f*
        average (fun z : UnitPair M =>
          liftedResidueTest g V outside h k M hd ((z.1:ZMod M),(z.2:ZMod M))) := by
  exact principalIntegral_pair M lo hi Z f
    (fun z => liftedResidueTest g V outside h k M hd ((z.1:ZMod M),(z.2:ZMod M)))

theorem mixedResidueTest_main {l : ℕ} (g : (q:ℕ)→ZMod q→ℂ)
    (V : ℕ→ℕ) (outside : List ℕ) (h k : History l) (M : ℕ) [NeZero M]
    (hd : pairModulus h k outside∣M) (loI hiI G : ℝ) (φ : ℝ→ℝ)
    (lo hi Z : Unit→ℝ) (f : (Option Unit→ℝ)→ℂ) :
    mixedPrincipalIntegral M loI hiI G φ lo hi Z f*
        (∑r:ZMod M,∑u:Unit→(ZMod M)ˣ,mixedResidueTest g V outside h k M hd r u)=
      mixedIntegral loI hiI G φ lo hi Z f*
        average (fun z : MixedPair M =>
          liftedResidueTest g V outside h k M hd (z.1,(z.2:ZMod M))) := by
  exact mixedPrincipalIntegral_pair M loI hiI G φ lo hi Z f
    (fun z => liftedResidueTest g V outside h k M hd (z.1,(z.2:ZMod M)))

end Ostmann.Arithmetic.HistoryPrincipalIntegralAverage

end

end OAI
