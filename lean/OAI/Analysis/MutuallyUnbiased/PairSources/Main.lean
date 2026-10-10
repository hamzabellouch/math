import OAI.Analysis.MutuallyUnbiased.PairSources.Rows0
import OAI.Analysis.MutuallyUnbiased.PairSources.Rows1
import OAI.Analysis.MutuallyUnbiased.PairSources.Rows2
import OAI.Analysis.MutuallyUnbiased.PairSources.Rows3
import OAI.Analysis.MutuallyUnbiased.PairSources.Rows4
import OAI.Analysis.MutuallyUnbiased.PairSources.Rows5
import OAI.Analysis.MutuallyUnbiased.PairSources.Rows6
import OAI.Analysis.MutuallyUnbiased.PairSources.Rows7
import OAI.Analysis.MutuallyUnbiased.PairSources.Rows8
import OAI.Analysis.MutuallyUnbiased.PairSources.Rows9
import OAI.Analysis.MutuallyUnbiased.PairSources.Rows10
import OAI.Analysis.MutuallyUnbiased.PairSources.Rows11
import OAI.Analysis.MutuallyUnbiased.PairSources.Rows12
import OAI.Analysis.MutuallyUnbiased.PairSources.Rows13
import OAI.Analysis.MutuallyUnbiased.PairSources.Rows14
import OAI.Analysis.MutuallyUnbiased.PairSources.Rows15
import OAI.Analysis.MutuallyUnbiased.PairMerge.Main

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem allRowsSound {H : CMatrix} (hH : IsHadamard H) (k : Fin 255) :
    Integer.Sparse.eval (PairData.rows k) (momentVector H) = 0 := by
  fin_cases k
  · exact rowSound0 hH
  · exact rowSound1 hH
  · exact rowSound2 hH
  · exact rowSound3 hH
  · exact rowSound4 hH
  · exact rowSound5 hH
  · exact rowSound6 hH
  · exact rowSound7 hH
  · exact rowSound8 hH
  · exact rowSound9 hH
  · exact rowSound10 hH
  · exact rowSound11 hH
  · exact rowSound12 hH
  · exact rowSound13 hH
  · exact rowSound14 hH
  · exact rowSound15 hH
  · exact rowSound16 hH
  · exact rowSound17 hH
  · exact rowSound18 hH
  · exact rowSound19 hH
  · exact rowSound20 hH
  · exact rowSound21 hH
  · exact rowSound22 hH
  · exact rowSound23 hH
  · exact rowSound24 hH
  · exact rowSound25 hH
  · exact rowSound26 hH
  · exact rowSound27 hH
  · exact rowSound28 hH
  · exact rowSound29 hH
  · exact rowSound30 hH
  · exact rowSound31 hH
  · exact rowSound32 hH
  · exact rowSound33 hH
  · exact rowSound34 hH
  · exact rowSound35 hH
  · exact rowSound36 hH
  · exact rowSound37 hH
  · exact rowSound38 hH
  · exact rowSound39 hH
  · exact rowSound40 hH
  · exact rowSound41 hH
  · exact rowSound42 hH
  · exact rowSound43 hH
  · exact rowSound44 hH
  · exact rowSound45 hH
  · exact rowSound46 hH
  · exact rowSound47 hH
  · exact rowSound48 hH
  · exact rowSound49 hH
  · exact rowSound50 hH
  · exact rowSound51 hH
  · exact rowSound52 hH
  · exact rowSound53 hH
  · exact rowSound54 hH
  · exact rowSound55 hH
  · exact rowSound56 hH
  · exact rowSound57 hH
  · exact rowSound58 hH
  · exact rowSound59 hH
  · exact rowSound60 hH
  · exact rowSound61 hH
  · exact rowSound62 hH
  · exact rowSound63 hH
  · exact rowSound64 hH
  · exact rowSound65 hH
  · exact rowSound66 hH
  · exact rowSound67 hH
  · exact rowSound68 hH
  · exact rowSound69 hH
  · exact rowSound70 hH
  · exact rowSound71 hH
  · exact rowSound72 hH
  · exact rowSound73 hH
  · exact rowSound74 hH
  · exact rowSound75 hH
  · exact rowSound76 hH
  · exact rowSound77 hH
  · exact rowSound78 hH
  · exact rowSound79 hH
  · exact rowSound80 hH
  · exact rowSound81 hH
  · exact rowSound82 hH
  · exact rowSound83 hH
  · exact rowSound84 hH
  · exact rowSound85 hH
  · exact rowSound86 hH
  · exact rowSound87 hH
  · exact rowSound88 hH
  · exact rowSound89 hH
  · exact rowSound90 hH
  · exact rowSound91 hH
  · exact rowSound92 hH
  · exact rowSound93 hH
  · exact rowSound94 hH
  · exact rowSound95 hH
  · exact rowSound96 hH
  · exact rowSound97 hH
  · exact rowSound98 hH
  · exact rowSound99 hH
  · exact rowSound100 hH
  · exact rowSound101 hH
  · exact rowSound102 hH
  · exact rowSound103 hH
  · exact rowSound104 hH
  · exact rowSound105 hH
  · exact rowSound106 hH
  · exact rowSound107 hH
  · exact rowSound108 hH
  · exact rowSound109 hH
  · exact rowSound110 hH
  · exact rowSound111 hH
  · exact rowSound112 hH
  · exact rowSound113 hH
  · exact rowSound114 hH
  · exact rowSound115 hH
  · exact rowSound116 hH
  · exact rowSound117 hH
  · exact rowSound118 hH
  · exact rowSound119 hH
  · exact rowSound120 hH
  · exact rowSound121 hH
  · exact rowSound122 hH
  · exact rowSound123 hH
  · exact rowSound124 hH
  · exact rowSound125 hH
  · exact rowSound126 hH
  · exact rowSound127 hH
  · exact rowSound128 hH
  · exact rowSound129 hH
  · exact rowSound130 hH
  · exact rowSound131 hH
  · exact rowSound132 hH
  · exact rowSound133 hH
  · exact rowSound134 hH
  · exact rowSound135 hH
  · exact rowSound136 hH
  · exact rowSound137 hH
  · exact rowSound138 hH
  · exact rowSound139 hH
  · exact rowSound140 hH
  · exact rowSound141 hH
  · exact rowSound142 hH
  · exact rowSound143 hH
  · exact rowSound144 hH
  · exact rowSound145 hH
  · exact rowSound146 hH
  · exact rowSound147 hH
  · exact rowSound148 hH
  · exact rowSound149 hH
  · exact rowSound150 hH
  · exact rowSound151 hH
  · exact rowSound152 hH
  · exact rowSound153 hH
  · exact rowSound154 hH
  · exact rowSound155 hH
  · exact rowSound156 hH
  · exact rowSound157 hH
  · exact rowSound158 hH
  · exact rowSound159 hH
  · exact rowSound160 hH
  · exact rowSound161 hH
  · exact rowSound162 hH
  · exact rowSound163 hH
  · exact rowSound164 hH
  · exact rowSound165 hH
  · exact rowSound166 hH
  · exact rowSound167 hH
  · exact rowSound168 hH
  · exact rowSound169 hH
  · exact rowSound170 hH
  · exact rowSound171 hH
  · exact rowSound172 hH
  · exact rowSound173 hH
  · exact rowSound174 hH
  · exact rowSound175 hH
  · exact rowSound176 hH
  · exact rowSound177 hH
  · exact rowSound178 hH
  · exact rowSound179 hH
  · exact rowSound180 hH
  · exact rowSound181 hH
  · exact rowSound182 hH
  · exact rowSound183 hH
  · exact rowSound184 hH
  · exact rowSound185 hH
  · exact rowSound186 hH
  · exact rowSound187 hH
  · exact rowSound188 hH
  · exact rowSound189 hH
  · exact rowSound190 hH
  · exact rowSound191 hH
  · exact rowSound192 hH
  · exact rowSound193 hH
  · exact rowSound194 hH
  · exact rowSound195 hH
  · exact rowSound196 hH
  · exact rowSound197 hH
  · exact rowSound198 hH
  · exact rowSound199 hH
  · exact rowSound200 hH
  · exact rowSound201 hH
  · exact rowSound202 hH
  · exact rowSound203 hH
  · exact rowSound204 hH
  · exact rowSound205 hH
  · exact rowSound206 hH
  · exact rowSound207 hH
  · exact rowSound208 hH
  · exact rowSound209 hH
  · exact rowSound210 hH
  · exact rowSound211 hH
  · exact rowSound212 hH
  · exact rowSound213 hH
  · exact rowSound214 hH
  · exact rowSound215 hH
  · exact rowSound216 hH
  · exact rowSound217 hH
  · exact rowSound218 hH
  · exact rowSound219 hH
  · exact rowSound220 hH
  · exact rowSound221 hH
  · exact rowSound222 hH
  · exact rowSound223 hH
  · exact rowSound224 hH
  · exact rowSound225 hH
  · exact rowSound226 hH
  · exact rowSound227 hH
  · exact rowSound228 hH
  · exact rowSound229 hH
  · exact rowSound230 hH
  · exact rowSound231 hH
  · exact rowSound232 hH
  · exact rowSound233 hH
  · exact rowSound234 hH
  · exact rowSound235 hH
  · exact rowSound236 hH
  · exact rowSound237 hH
  · exact rowSound238 hH
  · exact rowSound239 hH
  · exact rowSound240 hH
  · exact rowSound241 hH
  · exact rowSound242 hH
  · exact rowSound243 hH
  · exact rowSound244 hH
  · exact rowSound245 hH
  · exact rowSound246 hH
  · exact rowSound247 hH
  · exact rowSound248 hH
  · exact rowSound249 hH
  · exact rowSound250 hH
  · exact rowSound251 hH
  · exact rowSound252 hH
  · exact rowSound253 hH
  · exact rowSound254 hH

theorem targetZero0 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval PairData.target0 (momentVector H) = 0 :=
  PairData.mergeConsequence0 _ (allRowsSound hH)

theorem targetZero1 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval PairData.target1 (momentVector H) = 0 :=
  PairData.mergeConsequence1 _ (allRowsSound hH)

end MUB6.Certificate.PairSourceBridge

end OAI
