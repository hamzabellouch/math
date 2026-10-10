import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationRootTestDensity
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreIntegralReplacementFrame

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreIntegralReplacementFrame
open Construction Conclusion Filter ScaleBudget HistoryBulkSourceDisintegration
open HistoryBulkFibreGiantApproximation HistoryBulkGoodPatternPrincipalFrame
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}

def rootDensity (r : Frame (l:=l) C outside) (mixed : Bool) : ℂ :=
  if mixed then Frame.extractedDensity (C:=C) r.leftSource else 1

theorem norm_rootDensity_le (r : Frame (l:=l) C outside) (mixed : Bool) :
    ‖rootDensity r mixed‖≤1 := by
  cases mixed
  · simp only [rootDensity,Bool.false_eq_true,ite_false,norm_one,le_refl]
  · exact Frame.norm_extractedDensity_le r.leftSource

theorem selected_weighted_bulkMean_error_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hBs : 0≤Bs) (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀spectator : PrimeSource,
      (∀p:spectator.Sample,Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
    ∀ds : Fin (2*(bulkSize k L/2))→spectator.Sample,
    ∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase → C.blockBase-2<(C.giantCenter:ℝ) →
    ∀l≤k,∀r : Frame (l:=l) C (spectatorList spectator ds),
    ∀(corrected mixed : Bool)(a : SelectedNonbulkSample C l)
      (σ : Equiv.Perm (Frame.Slots (depth:=k) (L:=L) (l:=l)))
      (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q),
      (corrected=true → l<k) →
      ‖rootDensity r mixed*bulkMean r corrected mixed a σ hV-
        rootDensity r mixed*principalOperator r corrected mixed σ hV‖≤
        192*Real.exp (-Real.exp (bulk.target*L)) := by
  filter_upwards [selected_bulkMean_error_eventually d Bs BD Bz hBs hk] with L hL
  intro spectator hspec ds E C hblock hcenter l hl r corrected mixed a σ hV hstage
  have hb := hL spectator hspec ds E C hblock hcenter l hl r corrected mixed a σ hV hstage
  rw [←mul_sub,norm_mul]
  exact (mul_le_mul_of_nonneg_right (norm_rootDensity_le r mixed) (norm_nonneg _)).trans
    (by simpa only [one_mul] using hb)

end Ostmann.Arithmetic.HistoryBulkFibreIntegralReplacementFrame

end

end OAI
