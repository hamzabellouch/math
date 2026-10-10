import OAI.Analysis.MutuallyUnbiased.Certificate.MixedTargetBasic
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values3

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm128 : Integer.Sparse Master := [(Sum.inl 0, 112680633469501440000), (Sum.inl 1, -352126979592192000000), (Sum.inl 2, -305176715646566400000), (Sum.inl 5, 187801055782502400000), (Sum.inl 6, -46950263945625600000), (Sum.inl 9, 93900527891251200000), (Sum.inl 54, -1126806334695014400000), (Sum.inl 62, -1126806334695014400000), (Sum.inl 68, -281701583673753600000), (Sum.inl 260, -1126806334695014400000), (Sum.inl 264, -1126806334695014400000)]

def originalTerm128 : Integer.Sparse OriginalKey := [(Sum.inl 181, 107818617600)]

theorem reducedTermArithmetic128 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm128 x = (4056502804902051840000 : ℝ) * Sparse.eval nodeValue181 x := by
  norm_num [reducedTerm128, nodeValue181, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm129 : Integer.Sparse Master := [(Sum.inl 0, 251268317695180800000), (Sum.inl 1, 837561058983936000000), (Sum.inl 2, -418780529491968000000), (Sum.inl 5, 209390264745984000000), (Sum.inl 23, -2512683176951808000000), (Sum.inl 27, -628170794237952000000), (Sum.inl 54, -2512683176951808000000), (Sum.inl 68, -1256341588475904000000), (Sum.inl 125, -2512683176951808000000), (Sum.inl 196, -2512683176951808000000)]

def originalTerm129 : Integer.Sparse OriginalKey := [(Sum.inl 182, 240426432000)]

theorem reducedTermArithmetic129 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm129 x = (9045659437026508800000 : ℝ) * Sparse.eval nodeValue182 x := by
  norm_num [reducedTerm129, nodeValue182, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm130 : Integer.Sparse Master := [(Sum.inl 0, 13880764064563200000), (Sum.inl 1, -4957415737344000000), (Sum.inl 2, 4957415737344000000), (Sum.inl 5, 9914831474688000000), (Sum.inl 24, -118977977696256000000), (Sum.inl 27, -29744494424064000000), (Sum.inl 56, -118977977696256000000), (Sum.inl 68, -59488988848128000000), (Sum.inl 197, -237955955392512000000)]

def originalTerm130 : Integer.Sparse OriginalKey := [(Sum.inl 183, 11384424000)]

theorem reducedTermArithmetic130 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm130 x = (428320719706521600000 : ℝ) * Sparse.eval nodeValue183 x := by
  norm_num [reducedTerm130, nodeValue183, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm131 : Integer.Sparse Master := [(Sum.inl 0, -37388795609088000000), (Sum.inl 1, 101969442570240000000), (Sum.inl 2, 50984721285120000000), (Sum.inl 5, -33989814190080000000), (Sum.inl 27, 101969442570240000000), (Sum.inl 68, 203938885140480000000), (Sum.inl 263, -815755540561920000000)]

def originalTerm131 : Integer.Sparse OriginalKey := [(Sum.inl 184, -39027840000)]

theorem reducedTermArithmetic131 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm131 x = (-1468359973011456000000 : ℝ) * Sparse.eval nodeValue184 x := by
  norm_num [reducedTerm131, nodeValue184, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm132 : Integer.Sparse Master := [(Sum.inl 0, -49831197923082240000), (Sum.inl 1, -249155989615411200000), (Sum.inl 2, -249155989615411200000), (Sum.inl 68, -249155989615411200000), (Sum.inl 196, -996623958461644800000)]

def originalTerm132 : Integer.Sparse OriginalKey := [(Sum.inl 185, -47681049600)]

theorem reducedTermArithmetic132 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm132 x = (-1793923125230960640000 : ℝ) * Sparse.eval nodeValue185 x := by
  norm_num [reducedTerm132, nodeValue185, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm133 : Integer.Sparse Master := [(Sum.inl 0, -64451690672947200000), (Sum.inl 1, 128903381345894400000), (Sum.inl 2, 64451690672947200000), (Sum.inl 68, -257806762691788800000), (Sum.inl 197, -1031227050767155200000)]

def originalTerm133 : Integer.Sparse OriginalKey := [(Sum.inl 186, -49336550400)]

theorem reducedTermArithmetic133 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm133 x = (-1856208691380879360000 : ℝ) * Sparse.eval nodeValue186 x := by
  norm_num [reducedTerm133, nodeValue186, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm134 : Integer.Sparse Master := [(Sum.inl 0, -158195148400558080000), (Sum.inl 1, -593231806502092800000), (Sum.inl 2, 197743935500697600000), (Sum.inl 68, -790975742002790400000), (Sum.inl 125, -3163902968011161600000)]

def originalTerm134 : Integer.Sparse OriginalKey := [(Sum.inl 187, -151369243200)]

theorem reducedTermArithmetic134 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm134 x = (-5695025342420090880000 : ℝ) * Sparse.eval nodeValue187 x := by
  norm_num [reducedTerm134, nodeValue187, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm135 : Integer.Sparse Master := [(Sum.inl 0, -18952681598484480000), (Sum.inl 1, 23690851998105600000), (Sum.inl 2, -71072555994316800000), (Sum.inl 68, -94763407992422400000), (Sum.inl 264, -379053631969689600000)]

def originalTerm135 : Integer.Sparse OriginalKey := [(Sum.inl 188, -18134899200)]

theorem reducedTermArithmetic135 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm135 x = (-682296537545441280000 : ℝ) * Sparse.eval nodeValue188 x := by
  norm_num [reducedTerm135, nodeValue188, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm136 : Integer.Sparse Master := [(Sum.inl 0, -6977216593428480000), (Sum.inl 1, -23869425188044800000), (Sum.inl 2, -27541644447744000000), (Sum.inl 3, 88133262232780800000), (Sum.inl 5, 44066631116390400000), (Sum.inl 6, -5508328889548800000), (Sum.inl 9, 7344438519398400000), (Sum.inl 13, 29377754077593600000), (Sum.inl 26, 176266524465561600000), (Sum.inl 27, -66099946674585600000), (Sum.inl 34, 88133262232780800000), (Sum.inl 35, 88133262232780800000), (Sum.inl 54, -264399786698342400000), (Sum.inl 65, -264399786698342400000), (Sum.inl 67, 88133262232780800000), (Sum.inl 68, -110166577790976000000), (Sum.inl 257, 29377754077593600000), (Sum.inl 264, -176266524465561600000), (Sum.inl 266, -264399786698342400000)]

def originalTerm136 : Integer.Sparse OriginalKey := [(Sum.inl 189, -8433043200)]

theorem reducedTermArithmetic136 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm136 x = (-317279744038010880000 : ℝ) * Sparse.eval nodeValue189 x := by
  norm_num [reducedTerm136, nodeValue189, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm137 : Integer.Sparse Master := [(Sum.inl 0, 8078882371338240000), (Sum.inl 1, -3672219259699200000), (Sum.inl 2, -11016657779097600000), (Sum.inl 5, 14688877038796800000), (Sum.inl 6, -3672219259699200000), (Sum.inl 9, 7344438519398400000), (Sum.inl 26, 58755508155187200000), (Sum.inl 34, 29377754077593600000), (Sum.inl 35, 58755508155187200000), (Sum.inl 67, 58755508155187200000), (Sum.inl 68, -22033315558195200000), (Sum.inl 257, 29377754077593600000), (Sum.inl 266, -88133262232780800000)]

def originalTerm137 : Integer.Sparse OriginalKey := [(Sum.inl 190, 8433043200)]

theorem reducedTermArithmetic137 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm137 x = (317279744038010880000 : ℝ) * Sparse.eval nodeValue190 x := by
  norm_num [reducedTerm137, nodeValue190, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm138 : Integer.Sparse Master := [(Sum.inl 0, 144001237266432000000), (Sum.inl 1, 288002474532864000000), (Sum.inl 2, 252002165216256000000), (Sum.inl 3, -2304019796262912000000), (Sum.inl 5, -864007423598592000000), (Sum.inl 6, 108000927949824000000), (Sum.inl 9, -144001237266432000000), (Sum.inl 12, -1152009898131456000000), (Sum.inl 13, -3456029694394368000000), (Sum.inl 26, -1152009898131456000000), (Sum.inl 27, 1296011135397888000000), (Sum.inl 32, -576004949065728000000), (Sum.inl 34, -1152009898131456000000), (Sum.inl 35, -1728014847197184000000), (Sum.inl 54, 1728014847197184000000), (Sum.inl 55, 3456029694394368000000), (Sum.inl 60, -1152009898131456000000), (Sum.inl 61, 3456029694394368000000), (Sum.inl 65, 1728014847197184000000), (Sum.inl 67, -576004949065728000000), (Sum.inl 68, 2160018558996480000000), (Sum.inl 257, -576004949065728000000), (Sum.inl 264, 1728014847197184000000), (Sum.inl 266, 3456029694394368000000), (Sum.inl 268, 3456029694394368000000)]

def originalTerm138 : Integer.Sparse OriginalKey := [(Sum.inl 191, 165345336000)]

theorem reducedTermArithmetic138 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm138 x = (6220853449909862400000 : ℝ) * Sparse.eval nodeValue191 x := by
  norm_num [reducedTerm138, nodeValue191, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm139 : Integer.Sparse Master := [(Sum.inl 0, 190081633191690240000), (Sum.inl 1, -129601113539788800000), (Sum.inl 2, -129601113539788800000), (Sum.inl 3, 691205938878873600000), (Sum.inl 5, 345602969439436800000), (Sum.inl 6, -86400742359859200000), (Sum.inl 9, 172801484719718400000), (Sum.inl 13, 691205938878873600000), (Sum.inl 26, 691205938878873600000), (Sum.inl 34, 691205938878873600000), (Sum.inl 35, 1382411877757747200000), (Sum.inl 60, 691205938878873600000), (Sum.inl 67, 691205938878873600000), (Sum.inl 68, -518404454159155200000), (Sum.inl 257, 691205938878873600000), (Sum.inl 268, -2073617816636620800000)]

def originalTerm139 : Integer.Sparse OriginalKey := [(Sum.inl 192, 198414403200)]

theorem reducedTermArithmetic139 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm139 x = (7465024139891834880000 : ℝ) * Sparse.eval nodeValue192 x := by
  norm_num [reducedTerm139, nodeValue192, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm140 : Integer.Sparse Master := [(Sum.inl 0, 78417345665433600000), (Sum.inl 1, -228717258190848000000), (Sum.inl 2, -228717258190848000000), (Sum.inl 5, 65347788054528000000), (Sum.inl 27, -196043364163584000000), (Sum.inl 54, -784173456654336000000), (Sum.inl 65, -784173456654336000000), (Sum.inl 68, -392086728327168000000), (Sum.inl 264, -784173456654336000000), (Sum.inl 266, -784173456654336000000)]

def originalTerm140 : Integer.Sparse OriginalKey := [(Sum.inl 193, 75033744000)]

theorem reducedTermArithmetic140 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm140 x = (2823024443955609600000 : ℝ) * Sparse.eval nodeValue193 x := by
  norm_num [reducedTerm140, nodeValue193, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm141 : Integer.Sparse Master := [(Sum.inl 0, -2611509059174400000), (Sum.inl 1, -2374099144704000000), (Sum.inl 2, -14244594868224000000), (Sum.inl 5, -4748198289408000000), (Sum.inl 6, 1187049572352000000), (Sum.inl 9, -2374099144704000000), (Sum.inl 13, -18992793157632000000), (Sum.inl 32, -9496396578816000000), (Sum.inl 35, -18992793157632000000), (Sum.inl 60, -18992793157632000000), (Sum.inl 68, 7122297434112000000), (Sum.inl 257, -9496396578816000000), (Sum.inl 264, 28489189736448000000)]

def originalTerm141 : Integer.Sparse OriginalKey := [(Sum.inl 194, -2725992000)]

theorem reducedTermArithmetic141 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm141 x = (-102561083051212800000 : ℝ) * Sparse.eval nodeValue194 x := by
  norm_num [reducedTerm141, nodeValue194, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm142 : Integer.Sparse Master := [(Sum.inl 0, -190081633191690240000), (Sum.inl 1, 86400742359859200000), (Sum.inl 2, 172801484719718400000), (Sum.inl 5, -172801484719718400000), (Sum.inl 27, 518404454159155200000), (Sum.inl 55, 2073617816636620800000), (Sum.inl 61, 2073617816636620800000), (Sum.inl 68, 1036808908318310400000), (Sum.inl 266, 2073617816636620800000), (Sum.inl 268, 2073617816636620800000)]

def originalTerm142 : Integer.Sparse OriginalKey := [(Sum.inl 195, -198414403200)]

theorem reducedTermArithmetic142 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm142 x = (-7465024139891834880000 : ℝ) * Sparse.eval nodeValue195 x := by
  norm_num [reducedTerm142, nodeValue195, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm143 : Integer.Sparse Master := [(Sum.inl 0, -91214914532474880000), (Sum.inl 1, 228037286331187200000), (Sum.inl 2, 228037286331187200000), (Sum.inl 68, -456074572662374400000), (Sum.inl 266, -1824298290649497600000)]

def originalTerm143 : Integer.Sparse OriginalKey := [(Sum.inl 196, -87279115200)]

theorem reducedTermArithmetic143 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm143 x = (-3283736923169095680000 : ℝ) * Sparse.eval nodeValue196 x := by
  norm_num [reducedTerm143, nodeValue196, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm144 : Integer.Sparse Master := [(Sum.inl 0, -158401360993075200000), (Sum.inl 2, 72000618633216000000), (Sum.inl 68, -864007423598592000000), (Sum.inl 268, -3456029694394368000000)]

def originalTerm144 : Integer.Sparse OriginalKey := [(Sum.inl 197, -165345336000)]

theorem reducedTermArithmetic144 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm144 x = (-6220853449909862400000 : ℝ) * Sparse.eval nodeValue197 x := by
  norm_num [reducedTerm144, nodeValue197, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm145 : Integer.Sparse Master := [(Sum.inl 0, -71563296791347200000), (Sum.inl 1, 123384994467840000000), (Sum.inl 3, 789663964594176000000), (Sum.inl 5, -197415991148544000000), (Sum.inl 6, 123384994467840000000), (Sum.inl 7, 394831982297088000000), (Sum.inl 9, 49353997787136000000), (Sum.inl 13, 987079955742720000000), (Sum.inl 35, 789663964594176000000), (Sum.inl 52, 789663964594176000000), (Sum.inl 58, -12338499446784000000), (Sum.inl 68, -148061993361408000000), (Sum.inl 69, 197415991148544000000), (Sum.inl 70, 197415991148544000000), (Sum.inl 125, -592247973445632000000)]

def originalTerm145 : Integer.Sparse OriginalKey := [(Sum.inl 207, -56669328000)]

theorem reducedTermArithmetic145 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm145 x = (-2132092704404275200000 : ℝ) * Sparse.eval nodeValue207 x := by
  norm_num [reducedTerm145, nodeValue207, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm146 : Integer.Sparse Master := [(Sum.inl 0, -59296244178124800000), (Sum.inl 1, 80858514788352000000), (Sum.inl 2, 13476419131392000000), (Sum.inl 3, 862490824409088000000), (Sum.inl 5, 215622706102272000000), (Sum.inl 6, 53905676525568000000), (Sum.inl 9, 107811353051136000000), (Sum.inl 12, 431245412204544000000), (Sum.inl 13, 2803095179329536000000), (Sum.inl 32, 646868118306816000000), (Sum.inl 35, 1078113530511360000000), (Sum.inl 52, 862490824409088000000), (Sum.inl 54, -646868118306816000000), (Sum.inl 58, -13476419131392000000), (Sum.inl 60, 1078113530511360000000), (Sum.inl 62, -1293736236613632000000), (Sum.inl 68, -161717029576704000000), (Sum.inl 128, 431245412204544000000), (Sum.inl 257, 215622706102272000000), (Sum.inl 260, -646868118306816000000), (Sum.inl 264, -646868118306816000000), (Sum.inl 495, 215622706102272000000)]

def originalTerm146 : Integer.Sparse OriginalKey := [(Sum.inl 208, -61895664000)]

theorem reducedTermArithmetic146 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm146 x = (-2328725225904537600000 : ℝ) * Sparse.eval nodeValue208 x := by
  norm_num [reducedTerm146, nodeValue208, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm147 : Integer.Sparse Master := [(Sum.inl 0, 41416495368192000000), (Sum.inl 1, -124249486104576000000), (Sum.inl 2, -69027492280320000000), (Sum.inl 3, -441775950594048000000), (Sum.inl 5, 82832990736384000000), (Sum.inl 6, 13805498456064000000), (Sum.inl 7, -331331962945536000000), (Sum.inl 9, -55221993824256000000), (Sum.inl 12, -110443987648512000000), (Sum.inl 13, -441775950594048000000), (Sum.inl 23, 331331962945536000000), (Sum.inl 27, 82832990736384000000), (Sum.inl 35, -441775950594048000000), (Sum.inl 52, -220887975297024000000), (Sum.inl 54, 662663925891072000000), (Sum.inl 68, 165665981472768000000), (Sum.inl 69, -110443987648512000000), (Sum.inl 70, -110443987648512000000), (Sum.inl 125, 331331962945536000000), (Sum.inl 196, 331331962945536000000)]

def originalTerm147 : Integer.Sparse OriginalKey := [(Sum.inl 209, 31703544000)]

theorem reducedTermArithmetic147 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm147 x = (1192795066603929600000 : ℝ) * Sparse.eval nodeValue209 x := by
  norm_num [reducedTerm147, nodeValue209, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm148 : Integer.Sparse Master := [(Sum.inl 0, 88626279245414400000), (Sum.inl 1, 98473643606016000000), (Sum.inl 2, 49236821803008000000), (Sum.inl 5, 344657752621056000000), (Sum.inl 8, -590841861636096000000), (Sum.inl 9, -98473643606016000000), (Sum.inl 24, 590841861636096000000), (Sum.inl 27, 147710465409024000000), (Sum.inl 56, 1181683723272192000000), (Sum.inl 68, 295420930818048000000), (Sum.inl 71, -393894574424064000000), (Sum.inl 197, 1181683723272192000000)]

def originalTerm148 : Integer.Sparse OriginalKey := [(Sum.inl 210, 56534784000)]

theorem reducedTermArithmetic148 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm148 x = (2127030701889945600000 : ℝ) * Sparse.eval nodeValue210 x := by
  norm_num [reducedTerm148, nodeValue210, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm149 : Integer.Sparse Master := [(Sum.inl 0, -552349111910400000), (Sum.inl 1, 1196756409139200000), (Sum.inl 2, 460290926592000000), (Sum.inl 6, 184116370636800000), (Sum.inl 9, -368232741273600000), (Sum.inl 13, -1472930965094400000), (Sum.inl 52, -2945861930188800000), (Sum.inl 68, 1104698223820800000), (Sum.inl 69, -1472930965094400000), (Sum.inl 125, 4418792895283200000)]

def originalTerm149 : Integer.Sparse OriginalKey := [(Sum.inl 211, -422812800)]

theorem reducedTermArithmetic149 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm149 x = (-15907654423019520000 : ℝ) * Sparse.eval nodeValue211 x := by
  norm_num [reducedTerm149, nodeValue211, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm150 : Integer.Sparse Master := [(Sum.inl 0, -57972138835968000000), (Sum.inl 1, 72465173544960000000), (Sum.inl 2, -130437312380928000000), (Sum.inl 3, 927554221375488000000), (Sum.inl 4, 231888555343872000000), (Sum.inl 5, 173916416507904000000), (Sum.inl 6, 72465173544960000000), (Sum.inl 9, 115944277671936000000), (Sum.inl 13, 695665666031616000000), (Sum.inl 26, 695665666031616000000), (Sum.inl 34, 463777110687744000000), (Sum.inl 35, 927554221375488000000), (Sum.inl 52, 695665666031616000000), (Sum.inl 56, -695665666031616000000), (Sum.inl 58, -14493034708992000000), (Sum.inl 60, 463777110687744000000), (Sum.inl 67, 231888555343872000000), (Sum.inl 68, -173916416507904000000), (Sum.inl 128, 231888555343872000000), (Sum.inl 257, 231888555343872000000), (Sum.inl 262, -695665666031616000000), (Sum.inl 268, -695665666031616000000), (Sum.inl 495, 231888555343872000000)]

def originalTerm150 : Integer.Sparse OriginalKey := [(Sum.inl 212, -66564864000)]

theorem reducedTermArithmetic150 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm150 x = (-2504396397713817600000 : ℝ) * Sparse.eval nodeValue212 x := by
  norm_num [reducedTerm150, nodeValue212, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm151 : Integer.Sparse Master := [(Sum.inl 0, 57972138835968000000), (Sum.inl 1, 14493034708992000000), (Sum.inl 2, 72465173544960000000), (Sum.inl 3, -927554221375488000000), (Sum.inl 4, -231888555343872000000), (Sum.inl 5, -57972138835968000000), (Sum.inl 6, 57972138835968000000), (Sum.inl 9, -115944277671936000000), (Sum.inl 12, -463777110687744000000), (Sum.inl 13, -927554221375488000000), (Sum.inl 26, -231888555343872000000), (Sum.inl 27, 173916416507904000000), (Sum.inl 35, -463777110687744000000), (Sum.inl 51, 1391331332063232000000), (Sum.inl 54, 1391331332063232000000), (Sum.inl 55, 695665666031616000000), (Sum.inl 56, 1391331332063232000000), (Sum.inl 59, 695665666031616000000), (Sum.inl 61, 1391331332063232000000), (Sum.inl 68, 347832833015808000000), (Sum.inl 259, 695665666031616000000), (Sum.inl 262, 695665666031616000000), (Sum.inl 266, 695665666031616000000), (Sum.inl 268, 695665666031616000000)]

def originalTerm151 : Integer.Sparse OriginalKey := [(Sum.inl 213, 66564864000)]

theorem reducedTermArithmetic151 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm151 x = (2504396397713817600000 : ℝ) * Sparse.eval nodeValue213 x := by
  norm_num [reducedTerm151, nodeValue213, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm152 : Integer.Sparse Master := [(Sum.inl 0, 7382985781248000000), (Sum.inl 1, -20135415767040000000), (Sum.inl 2, -13423610511360000000), (Sum.inl 5, 13423610511360000000), (Sum.inl 6, -3355902627840000000), (Sum.inl 9, 6711805255680000000), (Sum.inl 26, 26847221022720000000), (Sum.inl 35, 26847221022720000000), (Sum.inl 54, -80541663068160000000), (Sum.inl 68, -20135415767040000000), (Sum.inl 259, -80541663068160000000), (Sum.inl 266, -80541663068160000000)]

def originalTerm152 : Integer.Sparse OriginalKey := [(Sum.inl 214, 7706640000)]

theorem reducedTermArithmetic152 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm152 x = (289949987045376000000 : ℝ) * Sparse.eval nodeValue214 x := by
  norm_num [reducedTerm152, nodeValue214, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm153 : Integer.Sparse Master := [(Sum.inl 0, -56114301693542400000), (Sum.inl 2, 25506500769792000000), (Sum.inl 3, 816208024633344000000), (Sum.inl 5, -102026003079168000000), (Sum.inl 12, 204052006158336000000), (Sum.inl 13, 3264832098533376000000), (Sum.inl 32, 816208024633344000000), (Sum.inl 35, 816208024633344000000), (Sum.inl 52, 816208024633344000000), (Sum.inl 60, 816208024633344000000), (Sum.inl 62, -1224312036950016000000), (Sum.inl 128, 204052006158336000000)]

def originalTerm153 : Integer.Sparse OriginalKey := [(Sum.inl 218, -58574232000)]

theorem reducedTermArithmetic153 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm153 x = (-2203761666510028800000 : ℝ) * Sparse.eval nodeValue218 x := by
  norm_num [reducedTerm153, nodeValue218, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm154 : Integer.Sparse Master := [(Sum.inl 0, 12440199254999040000), (Sum.inl 1, -14809761017856000000), (Sum.inl 2, -17771713221427200000), (Sum.inl 3, -47391235257139200000), (Sum.inl 5, 23695617628569600000), (Sum.inl 6, -5923904407142400000), (Sum.inl 7, -23695617628569600000), (Sum.inl 13, -23695617628569600000), (Sum.inl 26, -47391235257139200000), (Sum.inl 35, -47391235257139200000), (Sum.inl 54, 71086852885708800000)]

def originalTerm154 : Integer.Sparse OriginalKey := [(Sum.inl 220, 6801955200)]

theorem reducedTermArithmetic154 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm154 x = (255912670388551680000 : ℝ) * Sparse.eval nodeValue220 x := by
  norm_num [reducedTerm154, nodeValue220, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm155 : Integer.Sparse Master := [(Sum.inl 0, -7954874605117440000), (Sum.inl 1, -18274711930675200000), (Sum.inl 2, -7524881383219200000), (Sum.inl 3, 51599186627788800000), (Sum.inl 4, 17199728875929600000), (Sum.inl 5, -21499661094912000000), (Sum.inl 6, 3224949164236800000), (Sum.inl 8, 17199728875929600000), (Sum.inl 13, 34399457751859200000), (Sum.inl 26, 17199728875929600000), (Sum.inl 35, 17199728875929600000), (Sum.inl 52, 17199728875929600000), (Sum.inl 56, -51599186627788800000)]

def originalTerm155 : Integer.Sparse OriginalKey := [(Sum.inl 221, -4937275200)]

theorem reducedTermArithmetic155 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm155 x = (-185757071860039680000 : ℝ) * Sparse.eval nodeValue221 x := by
  norm_num [reducedTerm155, nodeValue221, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm156 : Integer.Sparse Master := [(Sum.inl 0, -11255418373570560000), (Sum.inl 1, 11847808814284800000), (Sum.inl 2, 14809761017856000000), (Sum.inl 5, 5923904407142400000), (Sum.inl 6, -5923904407142400000), (Sum.inl 26, -23695617628569600000), (Sum.inl 35, -23695617628569600000)]

def originalTerm156 : Integer.Sparse OriginalKey := [(Sum.inl 222, -6801955200)]

theorem reducedTermArithmetic156 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm156 x = (-255912670388551680000 : ℝ) * Sparse.eval nodeValue222 x := by
  norm_num [reducedTerm156, nodeValue222, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm157 : Integer.Sparse Master := [(Sum.inl 0, -40854277638881280000), (Sum.inl 1, -85662195049267200000), (Sum.inl 2, -13178799238348800000), (Sum.inl 3, 843443151254323200000), (Sum.inl 5, -79072795430092800000), (Sum.inl 6, 13178799238348800000), (Sum.inl 7, 105430393906790400000), (Sum.inl 12, 421721575627161600000), (Sum.inl 13, 948873545161113600000), (Sum.inl 35, 316291181720371200000), (Sum.inl 52, 210860787813580800000), (Sum.inl 54, -316291181720371200000)]

def originalTerm157 : Integer.Sparse OriginalKey := [(Sum.inl 223, -30264364800)]

theorem reducedTermArithmetic157 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm157 x = (-1138648254193336320000 : ℝ) * Sparse.eval nodeValue223 x := by
  norm_num [reducedTerm157, nodeValue223, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm158 : Integer.Sparse Master := [(Sum.inl 0, 62090278138183680000), (Sum.inl 1, 80487397586534400000), (Sum.inl 2, 11498199655219200000), (Sum.inl 3, 183971194483507200000), (Sum.inl 5, -45992798620876800000), (Sum.inl 6, 34494598965657600000), (Sum.inl 13, 367942388967014400000), (Sum.inl 35, 183971194483507200000), (Sum.inl 52, 183971194483507200000)]

def originalTerm158 : Integer.Sparse OriginalKey := [(Sum.inl 224, 52809926400)]

theorem reducedTermArithmetic158 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm158 x = (1986888900421877760000 : ℝ) * Sparse.eval nodeValue224 x := by
  norm_num [reducedTerm158, nodeValue224, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm159 : Integer.Sparse Master := [(Sum.inl 0, 125222731936727040000), (Sum.inl 1, 113838847215206400000), (Sum.inl 2, -113838847215206400000), (Sum.inl 3, 455355388860825600000), (Sum.inl 6, 56919423607603200000), (Sum.inl 13, 1366066166582476800000), (Sum.inl 32, 455355388860825600000), (Sum.inl 35, 455355388860825600000), (Sum.inl 52, 455355388860825600000), (Sum.inl 60, 455355388860825600000), (Sum.inl 62, -1366066166582476800000)]

def originalTerm159 : Integer.Sparse OriginalKey := [(Sum.inl 225, 130712227200)]

theorem reducedTermArithmetic159 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm159 x = (4917838199696916480000 : ℝ) * Sparse.eval nodeValue225 x := by
  norm_num [reducedTerm159, nodeValue225, Integer.Sparse.eval, Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
