import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneXAllPrecision
import OAI.NumberTheory.Catalan.Polynomial.ManuscriptRationalFieldSubstitutes

namespace OAI

section

noncomputable section

namespace InternalCatalan

def manuscriptCase1X4SubstituteRat : ℚ :=
  barrierCase1XApproxRat Case1PointData.X4 (-1) (-2) (0) (634829897 / 500000000) (365170103 / 250000000) (1403008998125030609 / 1000000000000000000)

theorem manuscript_case1X4_substitute_interval :
    manuscriptCase1X4SubstituteRat ∈ Set.Icc manuscriptCase1X4Interval.1 manuscriptCase1X4Interval.2 := by
  have hf := manuscript_x_substitute_interval (41 / 48) (barrierCase1XRat Case1PointData.X4) (-1) (-2) (0) (634829897 / 500000000) (365170103 / 250000000) (1403008998125030609 / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num)
  change (barrierCase1XApproxRat Case1PointData.X4 (-1) (-2) (0) (634829897 / 500000000) (365170103 / 250000000) (1403008998125030609 / 1000000000000000000)) ∈ Set.Icc manuscriptCase1X4Interval.1 manuscriptCase1X4Interval.2 at hf
  exact hf

theorem manuscript_case1X4_substitute_cutoff :
    manuscriptCase1X4SubstituteRat < ((-66221 / 50000) : ℚ) := by
  have hp : Case1PointData.X4PrintedUpper < ((-66221 / 50000) : ℚ) := by norm_num [Case1PointData.X4PrintedUpper]
  exact manuscript_case1X4_substitute_interval.2.trans_lt (manuscript_case1X4_endpoint_lt_printed.trans hp)

end InternalCatalan

end

end

end OAI
