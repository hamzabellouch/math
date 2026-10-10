import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTIntegrationModuli
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesTest

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction HistorySignedDecode HistorySignedSupportReduction HistorySignedSpectator
open HistoryCRTIntegration

def crtModulus {l : ℕ} (h k : History l) (outside : List ℕ) (n : ℕ) : ℕ :=
  rootModulus h * outsideModulus outside * frequencyModulus h k n * representativeModulus h k

def comparisonModulus {l : ℕ} (h k : History l) (outside : List ℕ) (n : ℕ) : ℕ :=
  pairModulus h k outside * crtModulus h k outside n

theorem pairModulus_dvd_comparisonModulus {l : ℕ} (h k : History l) (outside : List ℕ) (n : ℕ) :
    pairModulus h k outside ∣ comparisonModulus h k outside n := dvd_mul_right _ _

theorem crtModulus_dvd_comparisonModulus {l : ℕ} (h k : History l) (outside : List ℕ) (n : ℕ) :
    crtModulus h k outside n ∣ comparisonModulus h k outside n := dvd_mul_left _ _

def liftedResidueTest {l : ℕ} (g : (q : ℕ) → ZMod q → ℂ)
    (V : ℕ → ℕ) (outside : List ℕ) (h k : History l) (M : ℕ)
    (hd : pairModulus h k outside ∣ M) (z : ZMod M × ZMod M) : ℂ :=
  residueTest g V outside h k
    (ZMod.castHom hd (ZMod (pairModulus h k outside)) z.1,
      ZMod.castHom hd (ZMod (pairModulus h k outside)) z.2)

theorem liftedResidueTest_intCast {l : ℕ} (g : (q : ℕ) → ZMod q → ℂ)
    {V : ℕ → ℕ} {outside : List ℕ} (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    [NeZero (pairModulus h k outside)] (M : ℕ) (hd : pairModulus h k outside ∣ M)
    (Xp Xm : ℤ) :
    liftedResidueTest g V outside h k M hd ((Xp : ZMod M), (Xm : ZMod M)) =
      (by classical exact if ResidueGuarded V outside (rebuild h Xp Xm) ∧
        ResidueGuarded V outside (rebuild k Xp Xm) then
        pairSpectator g outside (rebuild h Xp Xm) (rebuild k Xp Xm) else 0) := by
  simpa only [liftedResidueTest, map_intCast] using residueTest_intCast g h k hs ks Xp Xm

theorem norm_liftedResidueTest_le {l : ℕ} (g : (q : ℕ) → ZMod q → ℂ)
    (V : ℕ → ℕ) (outside : List ℕ) (h k : History l) (M : ℕ)
    (hd : pairModulus h k outside ∣ M) (hg : ∀ q ∈ outside, ∀ x, ‖g q x‖ ≤ 1)
    (z : ZMod M × ZMod M) : ‖liftedResidueTest g V outside h k M hd z‖ ≤ 1 :=
  norm_residueTest_le g V outside h k hg _

def primeResidueTest {l : ℕ} (g : (q : ℕ) → ZMod q → ℂ)
    (V : ℕ → ℕ) (outside : List ℕ) (h k : History l) (M : ℕ)
    (hd : pairModulus h k outside ∣ M) (u : Bool → (ZMod M)ˣ) : ℂ :=
  liftedResidueTest g V outside h k M hd ((u false : ZMod M), (u true : ZMod M))

def mixedResidueTest {l : ℕ} (g : (q : ℕ) → ZMod q → ℂ)
    (V : ℕ → ℕ) (outside : List ℕ) (h k : History l) (M : ℕ)
    (hd : pairModulus h k outside ∣ M) (r : ZMod M) (u : Unit → (ZMod M)ˣ) : ℂ :=
  liftedResidueTest g V outside h k M hd (r, (u () : ZMod M))

theorem norm_primeResidueTest_le {l : ℕ} (g : (q : ℕ) → ZMod q → ℂ)
    (V : ℕ → ℕ) (outside : List ℕ) (h k : History l) (M : ℕ)
    (hd : pairModulus h k outside ∣ M) (hg : ∀ q ∈ outside, ∀ x, ‖g q x‖ ≤ 1)
    (u : Bool → (ZMod M)ˣ) : ‖primeResidueTest g V outside h k M hd u‖ ≤ 1 :=
  norm_liftedResidueTest_le g V outside h k M hd hg _

theorem norm_mixedResidueTest_le {l : ℕ} (g : (q : ℕ) → ZMod q → ℂ)
    (V : ℕ → ℕ) (outside : List ℕ) (h k : History l) (M : ℕ)
    (hd : pairModulus h k outside ∣ M) (hg : ∀ q ∈ outside, ∀ x, ‖g q x‖ ≤ 1)
    (r : ZMod M) (u : Unit → (ZMod M)ˣ) : ‖mixedResidueTest g V outside h k M hd r u‖ ≤ 1 :=
  norm_liftedResidueTest_le g V outside h k M hd hg _

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
