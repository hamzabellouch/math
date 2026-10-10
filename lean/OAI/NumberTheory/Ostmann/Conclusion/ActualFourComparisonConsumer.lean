import OAI.NumberTheory.Ostmann.Conclusion.ActualComparisonObstructionInterface
import OAI.NumberTheory.Ostmann.Conclusion.ActualComparisonProviders

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open Construction Filter

theorem false_of_actual_four_comparison_providers (d : Decomposition) (Cs Ccov : ℝ)
    (hsingle : ActualSingleComparisonProvider d Cs)
    (hdiagonal : ActualDiagonalGoodComparisonProvider d)
    (hbad : ActualBadCovarianceComparisonProvider d Ccov)
    (hgood : ActualGoodCovarianceComparisonProvider d) : False := by
  obtain ⟨δ,_hδ,hobstruction⟩ := exists_actual_comparison_obstruction_interface
  obtain ⟨BD,Bz,hBD,hBz,_hgap,k,hk,_hrate,hconfig⟩ := hobstruction d Cs Ccov 2
  have hk2 : 2≤k := (le_max_left 2 2).trans hk
  obtain ⟨εs,hεs,hs⟩ := hsingle BD Bz hBD hBz k hk2
  obtain ⟨εd,hεd,hd⟩ := hdiagonal BD Bz hBD hBz k hk2
  obtain ⟨εb,hεb,hb⟩ := hbad BD Bz hBD hBz k hk2
  obtain ⟨εg,hεg,hg⟩ := hgood BD Bz hBD hBz k hk2
  let ε := min εs (min εd (min εb εg))
  have hε : 0<ε := lt_min hεs (lt_min hεd (lt_min hεb hεg))
  have hεs' : ε≤εs := min_le_left _ _
  have hεd' : ε≤εd := (min_le_right _ _).trans (min_le_left _ _)
  have hεb' : ε≤εb := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hεg' : ε≤εg := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hfalse : ∀ᶠ L : ℝ in atTop,False := by
    filter_upwards [hconfig ε hε,hs,hd,hb,hg] with L hsource hsingleL hdiagonalL hbadL hgoodL
    obtain ⟨P,hP,hZ,_hPeq,hmass,hcard,hband,hbalanced,hflat,hchoices⟩ := hsource
    obtain ⟨C,_hfavorable,hG,hGu,hcl,hcu,hbulk,hspectator,hsep,hnot⟩ :=
      hchoices ∅ (by simp)
    have hdata : ActualComparisonSource C P hP hZ ε :=
      ⟨hG,hGu,hcl,hcu,hbulk,hspectator,hsep,hmass,hcard,hband,hbalanced,hflat⟩
    exact hnot ⟨hsingleL P hP hZ ∅ C (hdata.mono hεs'),
      hdiagonalL P hP hZ ∅ C (hdata.mono hεd'),
      hbadL P hP hZ ∅ C (hdata.mono hεb'),
      hgoodL P hP hZ ∅ C (hdata.mono hεg')⟩
  obtain ⟨L,hL⟩ := hfalse.exists
  exact hL

theorem no_decomposition_of_actual_four_comparison_providers (Cs Ccov : ℝ)
    (hsingle : ∀d : Decomposition,ActualSingleComparisonProvider d Cs)
    (hdiagonal : ∀d : Decomposition,ActualDiagonalGoodComparisonProvider d)
    (hbad : ∀d : Decomposition,ActualBadCovarianceComparisonProvider d Ccov)
    (hgood : ∀d : Decomposition,ActualGoodCovarianceComparisonProvider d) :
    ∀_d : Decomposition,False :=
  fun d=>false_of_actual_four_comparison_providers d Cs Ccov
    (hsingle d) (hdiagonal d) (hbad d) (hgood d)

end Ostmann.Conclusion

end

end OAI
