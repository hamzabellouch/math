import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound3

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval128 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm128 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm128 (originalVector B) := by
  rw [reducedTermArithmetic128, ← sound181 B hB hF]
  change (4056502804902051840000 : ℝ) * mixedMoment B node181 node181Labels =
    (37623398400 : ℝ) * ((107818617600 : ℝ) * mixedMoment B node181 node181Labels + 0)
  ring

theorem reducedTermEval129 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm129 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm129 (originalVector B) := by
  rw [reducedTermArithmetic129, ← sound182 B hB hF]
  change (9045659437026508800000 : ℝ) * mixedMoment B node182 node182Labels =
    (37623398400 : ℝ) * ((240426432000 : ℝ) * mixedMoment B node182 node182Labels + 0)
  ring

theorem reducedTermEval130 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm130 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm130 (originalVector B) := by
  rw [reducedTermArithmetic130, ← sound183 B hB hF]
  change (428320719706521600000 : ℝ) * mixedMoment B node183 node183Labels =
    (37623398400 : ℝ) * ((11384424000 : ℝ) * mixedMoment B node183 node183Labels + 0)
  ring

theorem reducedTermEval131 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm131 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm131 (originalVector B) := by
  rw [reducedTermArithmetic131, ← sound184 B hB hF]
  change (-1468359973011456000000 : ℝ) * mixedMoment B node184 node184Labels =
    (37623398400 : ℝ) * (((-39027840000 : ℤ) : ℝ) * mixedMoment B node184 node184Labels + 0)
  ring

theorem reducedTermEval132 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm132 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm132 (originalVector B) := by
  rw [reducedTermArithmetic132, ← sound185 B hB hF]
  change (-1793923125230960640000 : ℝ) * mixedMoment B node185 node185Labels =
    (37623398400 : ℝ) * (((-47681049600 : ℤ) : ℝ) * mixedMoment B node185 node185Labels + 0)
  ring

theorem reducedTermEval133 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm133 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm133 (originalVector B) := by
  rw [reducedTermArithmetic133, ← sound186 B hB hF]
  change (-1856208691380879360000 : ℝ) * mixedMoment B node186 node186Labels =
    (37623398400 : ℝ) * (((-49336550400 : ℤ) : ℝ) * mixedMoment B node186 node186Labels + 0)
  ring

theorem reducedTermEval134 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm134 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm134 (originalVector B) := by
  rw [reducedTermArithmetic134, ← sound187 B hB hF]
  change (-5695025342420090880000 : ℝ) * mixedMoment B node187 node187Labels =
    (37623398400 : ℝ) * (((-151369243200 : ℤ) : ℝ) * mixedMoment B node187 node187Labels + 0)
  ring

theorem reducedTermEval135 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm135 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm135 (originalVector B) := by
  rw [reducedTermArithmetic135, ← sound188 B hB hF]
  change (-682296537545441280000 : ℝ) * mixedMoment B node188 node188Labels =
    (37623398400 : ℝ) * (((-18134899200 : ℤ) : ℝ) * mixedMoment B node188 node188Labels + 0)
  ring

theorem reducedTermEval136 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm136 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm136 (originalVector B) := by
  rw [reducedTermArithmetic136, ← sound189 B hB hF]
  change (-317279744038010880000 : ℝ) * mixedMoment B node189 node189Labels =
    (37623398400 : ℝ) * (((-8433043200 : ℤ) : ℝ) * mixedMoment B node189 node189Labels + 0)
  ring

theorem reducedTermEval137 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm137 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm137 (originalVector B) := by
  rw [reducedTermArithmetic137, ← sound190 B hB hF]
  change (317279744038010880000 : ℝ) * mixedMoment B node190 node190Labels =
    (37623398400 : ℝ) * ((8433043200 : ℝ) * mixedMoment B node190 node190Labels + 0)
  ring

theorem reducedTermEval138 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm138 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm138 (originalVector B) := by
  rw [reducedTermArithmetic138, ← sound191 B hB hF]
  change (6220853449909862400000 : ℝ) * mixedMoment B node191 node191Labels =
    (37623398400 : ℝ) * ((165345336000 : ℝ) * mixedMoment B node191 node191Labels + 0)
  ring

theorem reducedTermEval139 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm139 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm139 (originalVector B) := by
  rw [reducedTermArithmetic139, ← sound192 B hB hF]
  change (7465024139891834880000 : ℝ) * mixedMoment B node192 node192Labels =
    (37623398400 : ℝ) * ((198414403200 : ℝ) * mixedMoment B node192 node192Labels + 0)
  ring

theorem reducedTermEval140 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm140 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm140 (originalVector B) := by
  rw [reducedTermArithmetic140, ← sound193 B hB hF]
  change (2823024443955609600000 : ℝ) * mixedMoment B node193 node193Labels =
    (37623398400 : ℝ) * ((75033744000 : ℝ) * mixedMoment B node193 node193Labels + 0)
  ring

theorem reducedTermEval141 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm141 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm141 (originalVector B) := by
  rw [reducedTermArithmetic141, ← sound194 B hB hF]
  change (-102561083051212800000 : ℝ) * mixedMoment B node194 node194Labels =
    (37623398400 : ℝ) * (((-2725992000 : ℤ) : ℝ) * mixedMoment B node194 node194Labels + 0)
  ring

theorem reducedTermEval142 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm142 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm142 (originalVector B) := by
  rw [reducedTermArithmetic142, ← sound195 B hB hF]
  change (-7465024139891834880000 : ℝ) * mixedMoment B node195 node195Labels =
    (37623398400 : ℝ) * (((-198414403200 : ℤ) : ℝ) * mixedMoment B node195 node195Labels + 0)
  ring

theorem reducedTermEval143 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm143 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm143 (originalVector B) := by
  rw [reducedTermArithmetic143, ← sound196 B hB hF]
  change (-3283736923169095680000 : ℝ) * mixedMoment B node196 node196Labels =
    (37623398400 : ℝ) * (((-87279115200 : ℤ) : ℝ) * mixedMoment B node196 node196Labels + 0)
  ring

theorem reducedTermEval144 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm144 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm144 (originalVector B) := by
  rw [reducedTermArithmetic144, ← sound197 B hB hF]
  change (-6220853449909862400000 : ℝ) * mixedMoment B node197 node197Labels =
    (37623398400 : ℝ) * (((-165345336000 : ℤ) : ℝ) * mixedMoment B node197 node197Labels + 0)
  ring

theorem reducedTermEval145 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm145 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm145 (originalVector B) := by
  rw [reducedTermArithmetic145, ← sound207 B hB hF]
  change (-2132092704404275200000 : ℝ) * mixedMoment B node207 node207Labels =
    (37623398400 : ℝ) * (((-56669328000 : ℤ) : ℝ) * mixedMoment B node207 node207Labels + 0)
  ring

theorem reducedTermEval146 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm146 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm146 (originalVector B) := by
  rw [reducedTermArithmetic146, ← sound208 B hB hF]
  change (-2328725225904537600000 : ℝ) * mixedMoment B node208 node208Labels =
    (37623398400 : ℝ) * (((-61895664000 : ℤ) : ℝ) * mixedMoment B node208 node208Labels + 0)
  ring

theorem reducedTermEval147 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm147 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm147 (originalVector B) := by
  rw [reducedTermArithmetic147, ← sound209 B hB hF]
  change (1192795066603929600000 : ℝ) * mixedMoment B node209 node209Labels =
    (37623398400 : ℝ) * ((31703544000 : ℝ) * mixedMoment B node209 node209Labels + 0)
  ring

theorem reducedTermEval148 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm148 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm148 (originalVector B) := by
  rw [reducedTermArithmetic148, ← sound210 B hB hF]
  change (2127030701889945600000 : ℝ) * mixedMoment B node210 node210Labels =
    (37623398400 : ℝ) * ((56534784000 : ℝ) * mixedMoment B node210 node210Labels + 0)
  ring

theorem reducedTermEval149 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm149 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm149 (originalVector B) := by
  rw [reducedTermArithmetic149, ← sound211 B hB hF]
  change (-15907654423019520000 : ℝ) * mixedMoment B node211 node211Labels =
    (37623398400 : ℝ) * (((-422812800 : ℤ) : ℝ) * mixedMoment B node211 node211Labels + 0)
  ring

theorem reducedTermEval150 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm150 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm150 (originalVector B) := by
  rw [reducedTermArithmetic150, ← sound212 B hB hF]
  change (-2504396397713817600000 : ℝ) * mixedMoment B node212 node212Labels =
    (37623398400 : ℝ) * (((-66564864000 : ℤ) : ℝ) * mixedMoment B node212 node212Labels + 0)
  ring

theorem reducedTermEval151 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm151 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm151 (originalVector B) := by
  rw [reducedTermArithmetic151, ← sound213 B hB hF]
  change (2504396397713817600000 : ℝ) * mixedMoment B node213 node213Labels =
    (37623398400 : ℝ) * ((66564864000 : ℝ) * mixedMoment B node213 node213Labels + 0)
  ring

theorem reducedTermEval152 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm152 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm152 (originalVector B) := by
  rw [reducedTermArithmetic152, ← sound214 B hB hF]
  change (289949987045376000000 : ℝ) * mixedMoment B node214 node214Labels =
    (37623398400 : ℝ) * ((7706640000 : ℝ) * mixedMoment B node214 node214Labels + 0)
  ring

theorem reducedTermEval153 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm153 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm153 (originalVector B) := by
  rw [reducedTermArithmetic153, ← sound218 B hB hF]
  change (-2203761666510028800000 : ℝ) * mixedMoment B node218 node218Labels =
    (37623398400 : ℝ) * (((-58574232000 : ℤ) : ℝ) * mixedMoment B node218 node218Labels + 0)
  ring

theorem reducedTermEval154 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm154 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm154 (originalVector B) := by
  rw [reducedTermArithmetic154, ← sound220 B hB hF]
  change (255912670388551680000 : ℝ) * mixedMoment B node220 node220Labels =
    (37623398400 : ℝ) * ((6801955200 : ℝ) * mixedMoment B node220 node220Labels + 0)
  ring

theorem reducedTermEval155 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm155 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm155 (originalVector B) := by
  rw [reducedTermArithmetic155, ← sound221 B hB hF]
  change (-185757071860039680000 : ℝ) * mixedMoment B node221 node221Labels =
    (37623398400 : ℝ) * (((-4937275200 : ℤ) : ℝ) * mixedMoment B node221 node221Labels + 0)
  ring

theorem reducedTermEval156 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm156 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm156 (originalVector B) := by
  rw [reducedTermArithmetic156, ← sound222 B hB hF]
  change (-255912670388551680000 : ℝ) * mixedMoment B node222 node222Labels =
    (37623398400 : ℝ) * (((-6801955200 : ℤ) : ℝ) * mixedMoment B node222 node222Labels + 0)
  ring

theorem reducedTermEval157 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm157 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm157 (originalVector B) := by
  rw [reducedTermArithmetic157, ← sound223 B hB hF]
  change (-1138648254193336320000 : ℝ) * mixedMoment B node223 node223Labels =
    (37623398400 : ℝ) * (((-30264364800 : ℤ) : ℝ) * mixedMoment B node223 node223Labels + 0)
  ring

theorem reducedTermEval158 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm158 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm158 (originalVector B) := by
  rw [reducedTermArithmetic158, ← sound224 B hB hF]
  change (1986888900421877760000 : ℝ) * mixedMoment B node224 node224Labels =
    (37623398400 : ℝ) * ((52809926400 : ℝ) * mixedMoment B node224 node224Labels + 0)
  ring

theorem reducedTermEval159 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm159 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm159 (originalVector B) := by
  rw [reducedTermArithmetic159, ← sound225 B hB hF]
  change (4917838199696916480000 : ℝ) * mixedMoment B node225 node225Labels =
    (37623398400 : ℝ) * ((130712227200 : ℝ) * mixedMoment B node225 node225Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
