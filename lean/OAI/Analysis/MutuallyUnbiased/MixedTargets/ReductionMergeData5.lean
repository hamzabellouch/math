import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData5
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData6
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData4

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge160 : Integer.Sparse Master := [(Sum.inl 0, -210793192152883200000), (Sum.inl 1, 126655862989824000000), (Sum.inl 2, -268214223449088000000), (Sum.inl 3, 3827095745111654400000), (Sum.inl 4, 17199728875929600000), (Sum.inl 5, 432603997301145600000), (Sum.inl 6, 222996805445836800000), (Sum.inl 7, 81734776278220800000), (Sum.inl 8, -359495116672204800000), (Sum.inl 9, 6343572514406400000), (Sum.inl 12, 877358805545779200000), (Sum.inl 13, 9478691642946355200000), (Sum.inl 26, 436737207700684800000), (Sum.inl 27, 173916416507904000000), (Sum.inl 32, 2074382725408358400000), (Sum.inl 34, 463777110687744000000), (Sum.inl 35, 2611882116071424000000), (Sum.inl 51, 1391331332063232000000), (Sum.inl 52, 3182953166113996800000), (Sum.inl 54, 1065585340160409600000), (Sum.inl 55, 695665666031616000000), (Sum.inl 56, 1774151016048230400000), (Sum.inl 58, -14493034708992000000), (Sum.inl 59, 963764986576896000000), (Sum.inl 60, 2538159836096102400000), (Sum.inl 61, 1659430652608512000000), (Sum.inl 62, -2590378203532492800000), (Sum.inl 67, 231888555343872000000), (Sum.inl 68, 154885698964684800000), (Sum.inl 69, -1472930965094400000), (Sum.inl 125, 4418792895283200000), (Sum.inl 128, 837350217459302400000), (Sum.inl 257, 231888555343872000000), (Sum.inl 259, 615124002963456000000), (Sum.inl 266, 615124002963456000000), (Sum.inl 495, 231888555343872000000)]

def originalMerge160 : Integer.Sparse OriginalKey := originalMerge152 ++ originalMerge159

theorem reducedMerge160Check : reducedMerge160 = Integer.Sparse.mergeBy masterLess reducedMerge152 reducedMerge159 := by decide +kernel

def reducedMerge161 : Integer.Sparse Master := [(Sum.inl 0, -15464765572300800000), (Sum.inl 1, -46903094654976000000), (Sum.inl 2, -116059384369152000000), (Sum.inl 3, -442600254170726400000), (Sum.inl 5, -55325031771340800000), (Sum.inl 6, 36338851971072000000), (Sum.inl 12, -221300127085363200000), (Sum.inl 13, -1024021885707878400000), (Sum.inl 35, -221300127085363200000), (Sum.inl 52, -581421631537152000000)]

def originalMerge161 : Integer.Sparse OriginalKey := originalTerm165 ++ originalTerm166

theorem reducedMerge161Check : reducedMerge161 = Integer.Sparse.mergeBy masterLess reducedTerm165 reducedTerm166 := by decide +kernel

def reducedMerge162 : Integer.Sparse Master := [(Sum.inl 0, 176111815797227520000), (Sum.inl 1, -122525429406105600000), (Sum.inl 2, -267304053871411200000), (Sum.inl 3, -39281135498035200000), (Sum.inl 5, -55325031771340800000), (Sum.inl 6, 11131407054028800000), (Sum.inl 12, -221300127085363200000), (Sum.inl 13, -620702767035187200000), (Sum.inl 35, -221300127085363200000), (Sum.inl 52, -178102512864460800000)]

def originalMerge162 : Integer.Sparse OriginalKey := originalTerm164 ++ originalMerge161

theorem reducedMerge162Check : reducedMerge162 = Integer.Sparse.mergeBy masterLess reducedTerm164 reducedMerge161 := by decide +kernel

def reducedMerge163 : Integer.Sparse Master := [(Sum.inl 0, 261166714015334400000), (Sum.inl 1, 405763535949004800000), (Sum.inl 2, 116569892081664000000), (Sum.inl 3, -2833374791349043200000), (Sum.inl 4, -468829381283020800000), (Sum.inl 5, 117207345320755200000), (Sum.inl 6, 28026929852006400000), (Sum.inl 12, -1875317525132083200000), (Sum.inl 13, -3771033553915084800000), (Sum.inl 26, -10199251825459200000), (Sum.inl 32, -468829381283020800000), (Sum.inl 33, 1406488143849062400000), (Sum.inl 34, -10199251825459200000), (Sum.inl 35, -20398503650918400000), (Sum.inl 51, 1406488143849062400000), (Sum.inl 52, -10199251825459200000), (Sum.inl 54, 2812976287698124800000), (Sum.inl 56, 1406488143849062400000), (Sum.inl 60, -10199251825459200000), (Sum.inl 61, 1406488143849062400000), (Sum.inl 62, 1406488143849062400000)]

def originalMerge163 : Integer.Sparse OriginalKey := originalTerm167 ++ originalTerm168

theorem reducedMerge163Check : reducedMerge163 = Integer.Sparse.mergeBy masterLess reducedTerm167 reducedTerm168 := by decide +kernel

def reducedMerge164 : Integer.Sparse Master := [(Sum.inl 0, -255477261696491520000), (Sum.inl 1, -148700628602265600000), (Sum.inl 2, -298267771098931200000), (Sum.inl 3, 1037486881957478400000), (Sum.inl 5, 515277385401139200000), (Sum.inl 6, -32421465061171200000), (Sum.inl 13, 518743440978739200000), (Sum.inl 26, 518743440978739200000), (Sum.inl 33, -1556230322936217600000), (Sum.inl 35, 172914480326246400000), (Sum.inl 51, 2313549150938726400000), (Sum.inl 54, 757318828002508800000), (Sum.inl 56, 2313549150938726400000), (Sum.inl 61, 2313549150938726400000), (Sum.inl 62, -1037486881957478400000)]

def originalMerge164 : Integer.Sparse OriginalKey := originalTerm169 ++ originalTerm170

theorem reducedMerge164Check : reducedMerge164 = Integer.Sparse.mergeBy masterLess reducedTerm169 reducedTerm170 := by decide +kernel

def reducedMerge165 : Integer.Sparse Master := [(Sum.inl 0, 5689452318842880000), (Sum.inl 1, 257062907346739200000), (Sum.inl 2, -181697879017267200000), (Sum.inl 3, -1795887909391564800000), (Sum.inl 4, -468829381283020800000), (Sum.inl 5, 632484730721894400000), (Sum.inl 6, -4394535209164800000), (Sum.inl 12, -1875317525132083200000), (Sum.inl 13, -3252290112936345600000), (Sum.inl 26, 508544189153280000000), (Sum.inl 32, -468829381283020800000), (Sum.inl 33, -149742179087155200000), (Sum.inl 34, -10199251825459200000), (Sum.inl 35, 152515976675328000000), (Sum.inl 51, 3720037294787788800000), (Sum.inl 52, -10199251825459200000), (Sum.inl 54, 3570295115700633600000), (Sum.inl 56, 3720037294787788800000), (Sum.inl 60, -10199251825459200000), (Sum.inl 61, 3720037294787788800000), (Sum.inl 62, 369001261891584000000)]

def originalMerge165 : Integer.Sparse OriginalKey := originalMerge163 ++ originalMerge164

theorem reducedMerge165Check : reducedMerge165 = Integer.Sparse.mergeBy masterLess reducedMerge163 reducedMerge164 := by decide +kernel

def reducedMerge166 : Integer.Sparse Master := [(Sum.inl 0, 181801268116070400000), (Sum.inl 1, 134537477940633600000), (Sum.inl 2, -449001932888678400000), (Sum.inl 3, -1835169044889600000000), (Sum.inl 4, -468829381283020800000), (Sum.inl 5, 577159698950553600000), (Sum.inl 6, 6736871844864000000), (Sum.inl 12, -2096617652217446400000), (Sum.inl 13, -3872992879971532800000), (Sum.inl 26, 508544189153280000000), (Sum.inl 32, -468829381283020800000), (Sum.inl 33, -149742179087155200000), (Sum.inl 34, -10199251825459200000), (Sum.inl 35, -68784150410035200000), (Sum.inl 51, 3720037294787788800000), (Sum.inl 52, -188301764689920000000), (Sum.inl 54, 3570295115700633600000), (Sum.inl 56, 3720037294787788800000), (Sum.inl 60, -10199251825459200000), (Sum.inl 61, 3720037294787788800000), (Sum.inl 62, 369001261891584000000)]

def originalMerge166 : Integer.Sparse OriginalKey := originalMerge162 ++ originalMerge165

theorem reducedMerge166Check : reducedMerge166 = Integer.Sparse.mergeBy masterLess reducedMerge162 reducedMerge165 := by decide +kernel

def reducedMerge167 : Integer.Sparse Master := [(Sum.inl 0, -18588586594959360000), (Sum.inl 1, -46427772135628800000), (Sum.inl 2, -35482028191948800000), (Sum.inl 3, 681534585136742400000), (Sum.inl 4, 289931526497894400000), (Sum.inl 5, 61659323847475200000), (Sum.inl 6, -15414830961868800000), (Sum.inl 12, 144965763248947200000), (Sum.inl 13, 362414408122368000000), (Sum.inl 26, 348308827530854400000), (Sum.inl 35, 246637295389900800000), (Sum.inl 54, -305014596422860800000), (Sum.inl 56, -434897289746841600000)]

def originalMerge167 : Integer.Sparse OriginalKey := originalTerm171 ++ originalTerm172

theorem reducedMerge167Check : reducedMerge167 = Integer.Sparse.mergeBy masterLess reducedTerm171 reducedTerm172 := by decide +kernel

def reducedMerge168 : Integer.Sparse Master := [(Sum.inl 0, -6466017864499200000), (Sum.inl 1, -14628823824384000000), (Sum.inl 2, -12393539343360000000), (Sum.inl 3, -53528230232064000000), (Sum.inl 4, -39659325898752000000), (Sum.inl 5, -3467226083328000000), (Sum.inl 6, 866806520832000000), (Sum.inl 13, -13868904333312000000), (Sum.inl 26, -39659325898752000000), (Sum.inl 33, -77371264696320000000), (Sum.inl 35, -39659325898752000000), (Sum.inl 54, -77371264696320000000), (Sum.inl 56, 118977977696256000000), (Sum.inl 62, -77371264696320000000)]

def originalMerge168 : Integer.Sparse OriginalKey := originalTerm173 ++ originalTerm174

theorem reducedMerge168Check : reducedMerge168 = Integer.Sparse.mergeBy masterLess reducedTerm173 reducedTerm174 := by decide +kernel

def reducedMerge169 : Integer.Sparse Master := [(Sum.inl 0, -25054604459458560000), (Sum.inl 1, -61056595960012800000), (Sum.inl 2, -47875567535308800000), (Sum.inl 3, 628006354904678400000), (Sum.inl 4, 250272200599142400000), (Sum.inl 5, 58192097764147200000), (Sum.inl 6, -14548024441036800000), (Sum.inl 12, 144965763248947200000), (Sum.inl 13, 348545503789056000000), (Sum.inl 26, 308649501632102400000), (Sum.inl 33, -77371264696320000000), (Sum.inl 35, 206977969491148800000), (Sum.inl 54, -382385861119180800000), (Sum.inl 56, -315919312050585600000), (Sum.inl 62, -77371264696320000000)]

def originalMerge169 : Integer.Sparse OriginalKey := originalMerge167 ++ originalMerge168

theorem reducedMerge169Check : reducedMerge169 = Integer.Sparse.mergeBy masterLess reducedMerge167 reducedMerge168 := by decide +kernel

def reducedMerge170 : Integer.Sparse Master := [(Sum.inl 0, 236848895673384960000), (Sum.inl 1, 1891025362940313600000), (Sum.inl 2, 400959471093350400000), (Sum.inl 3, 2001882035375308800000), (Sum.inl 5, 250235254421913600000), (Sum.inl 6, -75362108335718400000), (Sum.inl 12, 2001882035375308800000), (Sum.inl 13, 3002823053062963200000), (Sum.inl 26, 204852715683840000000), (Sum.inl 35, 1205793733371494400000), (Sum.inl 54, -3002823053062963200000)]

def originalMerge170 : Integer.Sparse OriginalKey := originalTerm175 ++ originalTerm176

theorem reducedMerge170Check : reducedMerge170 = Integer.Sparse.mergeBy masterLess reducedTerm175 reducedTerm176 := by decide +kernel

def reducedMerge171 : Integer.Sparse Master := [(Sum.inl 0, -299074803654574080000), (Sum.inl 1, -1443520516283596800000), (Sum.inl 2, 260639955084902400000), (Sum.inl 3, 1606420488211660800000), (Sum.inl 6, -132981274898841600000), (Sum.inl 13, 1606420488211660800000), (Sum.inl 35, 1606420488211660800000), (Sum.inl 62, -1563839730509414400000)]

def originalMerge171 : Integer.Sparse OriginalKey := originalTerm177 ++ originalTerm178

theorem reducedMerge171Check : reducedMerge171 = Integer.Sparse.mergeBy masterLess reducedTerm177 reducedTerm178 := by decide +kernel

def reducedMerge172 : Integer.Sparse Master := [(Sum.inl 0, -62225907981189120000), (Sum.inl 1, 447504846656716800000), (Sum.inl 2, 661599426178252800000), (Sum.inl 3, 3608302523586969600000), (Sum.inl 5, 250235254421913600000), (Sum.inl 6, -208343383234560000000), (Sum.inl 12, 2001882035375308800000), (Sum.inl 13, 4609243541274624000000), (Sum.inl 26, 204852715683840000000), (Sum.inl 35, 2812214221583155200000), (Sum.inl 54, -3002823053062963200000), (Sum.inl 62, -1563839730509414400000)]

def originalMerge172 : Integer.Sparse OriginalKey := originalMerge170 ++ originalMerge171

theorem reducedMerge172Check : reducedMerge172 = Integer.Sparse.mergeBy masterLess reducedMerge170 reducedMerge171 := by decide +kernel

def reducedMerge173 : Integer.Sparse Master := [(Sum.inl 0, -87280512440647680000), (Sum.inl 1, 386448250696704000000), (Sum.inl 2, 613723858642944000000), (Sum.inl 3, 4236308878491648000000), (Sum.inl 4, 250272200599142400000), (Sum.inl 5, 308427352186060800000), (Sum.inl 6, -222891407675596800000), (Sum.inl 12, 2146847798624256000000), (Sum.inl 13, 4957789045063680000000), (Sum.inl 26, 513502217315942400000), (Sum.inl 33, -77371264696320000000), (Sum.inl 35, 3019192191074304000000), (Sum.inl 54, -3385208914182144000000), (Sum.inl 56, -315919312050585600000), (Sum.inl 62, -1641210995205734400000)]

def originalMerge173 : Integer.Sparse OriginalKey := originalMerge169 ++ originalMerge172

theorem reducedMerge173Check : reducedMerge173 = Integer.Sparse.mergeBy masterLess reducedMerge169 reducedMerge172 := by decide +kernel

def reducedMerge174 : Integer.Sparse Master := [(Sum.inl 0, 94520755675422720000), (Sum.inl 1, 520985728637337600000), (Sum.inl 2, 164721925754265600000), (Sum.inl 3, 2401139833602048000000), (Sum.inl 4, -218557180683878400000), (Sum.inl 5, 885587051136614400000), (Sum.inl 6, -216154535830732800000), (Sum.inl 12, 50230146406809600000), (Sum.inl 13, 1084796165092147200000), (Sum.inl 26, 1022046406469222400000), (Sum.inl 32, -468829381283020800000), (Sum.inl 33, -227113443783475200000), (Sum.inl 34, -10199251825459200000), (Sum.inl 35, 2950408040664268800000), (Sum.inl 51, 3720037294787788800000), (Sum.inl 52, -188301764689920000000), (Sum.inl 54, 185086201518489600000), (Sum.inl 56, 3404117982737203200000), (Sum.inl 60, -10199251825459200000), (Sum.inl 61, 3720037294787788800000), (Sum.inl 62, -1272209733314150400000)]

def originalMerge174 : Integer.Sparse OriginalKey := originalMerge166 ++ originalMerge173

theorem reducedMerge174Check : reducedMerge174 = Integer.Sparse.mergeBy masterLess reducedMerge166 reducedMerge173 := by decide +kernel

def reducedMerge175 : Integer.Sparse Master := [(Sum.inl 0, -116272436477460480000), (Sum.inl 1, 647641591627161600000), (Sum.inl 2, -103492297694822400000), (Sum.inl 3, 6228235578713702400000), (Sum.inl 4, -201357451807948800000), (Sum.inl 5, 1318191048437760000000), (Sum.inl 6, 6842269615104000000), (Sum.inl 7, 81734776278220800000), (Sum.inl 8, -359495116672204800000), (Sum.inl 9, 6343572514406400000), (Sum.inl 12, 927588951952588800000), (Sum.inl 13, 10563487808038502400000), (Sum.inl 26, 1458783614169907200000), (Sum.inl 27, 173916416507904000000), (Sum.inl 32, 1605553344125337600000), (Sum.inl 33, -227113443783475200000), (Sum.inl 34, 453577858862284800000), (Sum.inl 35, 5562290156735692800000), (Sum.inl 51, 5111368626851020800000), (Sum.inl 52, 2994651401424076800000), (Sum.inl 54, 1250671541678899200000), (Sum.inl 55, 695665666031616000000), (Sum.inl 56, 5178268998785433600000), (Sum.inl 58, -14493034708992000000), (Sum.inl 59, 963764986576896000000), (Sum.inl 60, 2527960584270643200000), (Sum.inl 61, 5379467947396300800000), (Sum.inl 62, -3862587936846643200000), (Sum.inl 67, 231888555343872000000), (Sum.inl 68, 154885698964684800000), (Sum.inl 69, -1472930965094400000), (Sum.inl 125, 4418792895283200000), (Sum.inl 128, 837350217459302400000), (Sum.inl 257, 231888555343872000000), (Sum.inl 259, 615124002963456000000), (Sum.inl 266, 615124002963456000000), (Sum.inl 495, 231888555343872000000)]

def originalMerge175 : Integer.Sparse OriginalKey := originalMerge160 ++ originalMerge174

theorem reducedMerge175Check : reducedMerge175 = Integer.Sparse.mergeBy masterLess reducedMerge160 reducedMerge174 := by decide +kernel

def reducedMerge176 : Integer.Sparse Master := [(Sum.inl 0, -250052467829391360000), (Sum.inl 1, 816545070712627200000), (Sum.inl 2, -469073371111833600000), (Sum.inl 3, 6378265066792550400000), (Sum.inl 4, -159419535851520000000), (Sum.inl 5, 1629724617658368000000), (Sum.inl 6, 165306867180134400000), (Sum.inl 7, 485942927494348800000), (Sum.inl 8, -950336978308300800000), (Sum.inl 9, 137230208601292800000), (Sum.inl 12, 502925678051328000000), (Sum.inl 13, 11403961285931827200000), (Sum.inl 23, -3400986813028761600000), (Sum.inl 24, 346050136070553600000), (Sum.inl 26, 1291596033776025600000), (Sum.inl 27, 1694809840376217600000), (Sum.inl 32, 1666920116787609600000), (Sum.inl 33, 291629997195264000000), (Sum.inl 34, 110284915920076800000), (Sum.inl 35, 7105398742587801600000), (Sum.inl 51, 5111368626851020800000), (Sum.inl 52, 4163410868649984000000), (Sum.inl 54, -2913216157561651200000), (Sum.inl 55, 8407913186908569600000), (Sum.inl 56, 6115160996492083200000), (Sum.inl 58, -40307953287168000000), (Sum.inl 59, 963764986576896000000), (Sum.inl 60, 3126277362371788800000), (Sum.inl 61, 10909115458427289600000), (Sum.inl 62, -6283130508155289600000), (Sum.inl 63, -179799963549696000000), (Sum.inl 64, 787522039440998400000), (Sum.inl 65, 679441603844505600000), (Sum.inl 67, 493978315544985600000), (Sum.inl 68, -1052727619004006400000), (Sum.inl 69, 85499072534937600000), (Sum.inl 70, 146170347415142400000), (Sum.inl 71, -393894574424064000000), (Sum.inl 125, -5033436673189478400000), (Sum.inl 128, 1268595629663846400000), (Sum.inl 196, -4015686323729203200000), (Sum.inl 197, 1337667373331251200000), (Sum.inl 257, 611971362835660800000), (Sum.inl 259, 615124002963456000000), (Sum.inl 260, -1504895854539571200000), (Sum.inl 263, -1853242422519398400000), (Sum.inl 264, -1536463992707481600000), (Sum.inl 266, 3183766717759488000000), (Sum.inl 495, 447511261446144000000)]

def originalMerge176 : Integer.Sparse OriginalKey := originalMerge146 ++ originalMerge175

theorem reducedMerge176Check : reducedMerge176 = Integer.Sparse.mergeBy masterLess reducedMerge146 reducedMerge175 := by decide +kernel

def reducedMerge177 : Integer.Sparse Master := [(Sum.inl 0, 5277977542656000000), (Sum.inl 1, 100510302670848000000), (Sum.inl 2, 111015372109824000000), (Sum.inl 3, 617178742161408000000), (Sum.inl 5, 4705642045440000000), (Sum.inl 6, -12857890461696000000), (Sum.inl 12, 205726247387136000000), (Sum.inl 13, 960055821139968000000), (Sum.inl 26, 205726247387136000000), (Sum.inl 32, 137150831591424000000), (Sum.inl 34, 411452494774272000000), (Sum.inl 56, 560711037616128000000), (Sum.inl 60, 205726247387136000000), (Sum.inl 61, -617178742161408000000)]

def originalMerge177 : Integer.Sparse OriginalKey := originalTerm180 ++ originalTerm181

theorem reducedMerge177Check : reducedMerge177 = Integer.Sparse.mergeBy masterLess reducedTerm180 reducedTerm181 := by decide +kernel

def reducedMerge178 : Integer.Sparse Master := [(Sum.inl 0, -37749991938785280000), (Sum.inl 1, -96701224119091200000), (Sum.inl 2, 128943692727091200000), (Sum.inl 3, 617178742161408000000), (Sum.inl 5, 76418924514508800000), (Sum.inl 6, -12857890461696000000), (Sum.inl 12, 205726247387136000000), (Sum.inl 13, 960055821139968000000), (Sum.inl 26, 205726247387136000000), (Sum.inl 32, 137150831591424000000), (Sum.inl 34, 411452494774272000000), (Sum.inl 54, -860559389628825600000), (Sum.inl 56, 560711037616128000000), (Sum.inl 60, 205726247387136000000), (Sum.inl 61, -617178742161408000000)]

def originalMerge178 : Integer.Sparse OriginalKey := originalTerm179 ++ originalMerge177

theorem reducedMerge178Check : reducedMerge178 = Integer.Sparse.mergeBy masterLess reducedTerm179 reducedMerge177 := by decide +kernel

def reducedMerge179 : Integer.Sparse Master := [(Sum.inl 0, 80627212405555200000), (Sum.inl 1, -109755688476672000000), (Sum.inl 2, -194467340906496000000), (Sum.inl 3, 137150831591424000000), (Sum.inl 5, 17143853948928000000), (Sum.inl 6, 21093944997888000000), (Sum.inl 13, -268927704170496000000), (Sum.inl 26, 68575415795712000000), (Sum.inl 34, -268927704170496000000), (Sum.inl 60, -337503119966208000000), (Sum.inl 61, -205726247387136000000)]

def originalMerge179 : Integer.Sparse OriginalKey := originalTerm182 ++ originalTerm183

theorem reducedMerge179Check : reducedMerge179 = Integer.Sparse.mergeBy masterLess reducedTerm182 reducedTerm183 := by decide +kernel

def reducedMerge180 : Integer.Sparse Master := [(Sum.inl 0, -72520421624340480000), (Sum.inl 1, 78807074953420800000), (Sum.inl 2, 131803045923225600000), (Sum.inl 3, 363400943792947200000), (Sum.inl 5, 101519633940480000000), (Sum.inl 12, 242267295861964800000), (Sum.inl 13, 686424004942233600000), (Sum.inl 32, 80755765287321600000), (Sum.inl 61, -1218235607285760000000)]

def originalMerge180 : Integer.Sparse OriginalKey := originalTerm184 ++ originalTerm185

theorem reducedMerge180Check : reducedMerge180 = Integer.Sparse.mergeBy masterLess reducedTerm184 reducedTerm185 := by decide +kernel

def reducedMerge181 : Integer.Sparse Master := [(Sum.inl 0, 8106790781214720000), (Sum.inl 1, -30948613523251200000), (Sum.inl 2, -62664294983270400000), (Sum.inl 3, 500551775384371200000), (Sum.inl 5, 118663487889408000000), (Sum.inl 6, 21093944997888000000), (Sum.inl 12, 242267295861964800000), (Sum.inl 13, 417496300771737600000), (Sum.inl 26, 68575415795712000000), (Sum.inl 32, 80755765287321600000), (Sum.inl 34, -268927704170496000000), (Sum.inl 60, -337503119966208000000), (Sum.inl 61, -1423961854672896000000)]

def originalMerge181 : Integer.Sparse OriginalKey := originalMerge179 ++ originalMerge180

theorem reducedMerge181Check : reducedMerge181 = Integer.Sparse.mergeBy masterLess reducedMerge179 reducedMerge180 := by decide +kernel

def reducedMerge182 : Integer.Sparse Master := [(Sum.inl 0, -29643201157570560000), (Sum.inl 1, -127649837642342400000), (Sum.inl 2, 66279397743820800000), (Sum.inl 3, 1117730517545779200000), (Sum.inl 5, 195082412403916800000), (Sum.inl 6, 8236054536192000000), (Sum.inl 12, 447993543249100800000), (Sum.inl 13, 1377552121911705600000), (Sum.inl 26, 274301663182848000000), (Sum.inl 32, 217906596878745600000), (Sum.inl 34, 142524790603776000000), (Sum.inl 54, -860559389628825600000), (Sum.inl 56, 560711037616128000000), (Sum.inl 60, -131776872579072000000), (Sum.inl 61, -2041140596834304000000)]

def originalMerge182 : Integer.Sparse OriginalKey := originalMerge178 ++ originalMerge181

theorem reducedMerge182Check : reducedMerge182 = Integer.Sparse.mergeBy masterLess reducedMerge178 reducedMerge181 := by decide +kernel

def reducedMerge183 : Integer.Sparse Master := [(Sum.inl 0, 49144455105822720000), (Sum.inl 1, 68037456588595200000), (Sum.inl 2, 524405962050969600000), (Sum.inl 3, 433593179150745600000), (Sum.inl 12, 108398294787686400000), (Sum.inl 13, 2458566801034444800000), (Sum.inl 32, 674991207294566400000)]

def originalMerge183 : Integer.Sparse OriginalKey := originalTerm186 ++ originalTerm187

theorem reducedMerge183Check : reducedMerge183 = Integer.Sparse.mergeBy masterLess reducedTerm186 reducedTerm187 := by decide +kernel

def reducedMerge184 : Integer.Sparse Master := [(Sum.inl 0, 179350288483000320000), (Sum.inl 1, -46585413129830400000), (Sum.inl 2, -89565314330419200000), (Sum.inl 3, 524163551359795200000), (Sum.inl 12, 73734352905830400000), (Sum.inl 13, 597897904265625600000)]

def originalMerge184 : Integer.Sparse OriginalKey := originalTerm188 ++ originalTerm189

theorem reducedMerge184Check : reducedMerge184 = Integer.Sparse.mergeBy masterLess reducedTerm188 reducedTerm189 := by decide +kernel

def reducedMerge185 : Integer.Sparse Master := [(Sum.inl 0, 228494743588823040000), (Sum.inl 1, 21452043458764800000), (Sum.inl 2, 434840647720550400000), (Sum.inl 3, 957756730510540800000), (Sum.inl 12, 182132647693516800000), (Sum.inl 13, 3056464705300070400000), (Sum.inl 32, 674991207294566400000)]

def originalMerge185 : Integer.Sparse OriginalKey := originalMerge183 ++ originalMerge184

theorem reducedMerge185Check : reducedMerge185 = Integer.Sparse.mergeBy masterLess reducedMerge183 reducedMerge184 := by decide +kernel

def reducedMerge186 : Integer.Sparse Master := [(Sum.inl 0, -157658725691228160000), (Sum.inl 1, 472634854259097600000), (Sum.inl 2, 188029973259878400000), (Sum.inl 3, -1046647895202201600000), (Sum.inl 12, -1046647895202201600000), (Sum.inl 13, -3061402885029888000000), (Sum.inl 32, -523323947601100800000)]

def originalMerge186 : Integer.Sparse OriginalKey := originalTerm190 ++ originalTerm191

theorem reducedMerge186Check : reducedMerge186 = Integer.Sparse.mergeBy masterLess reducedTerm190 reducedTerm191 := by decide +kernel

def reducedMerge187 : Integer.Sparse Master := [(Sum.inl 0, -44788382087823360000), (Sum.inl 1, 111970955219558400000), (Sum.inl 2, -111970955219558400000), (Sum.inl 13, 597178427837644800000), (Sum.inl 32, 298589213918822400000)]

def originalMerge187 : Integer.Sparse OriginalKey := originalTerm192 ++ originalTerm193

theorem reducedMerge187Check : reducedMerge187 = Integer.Sparse.mergeBy masterLess reducedTerm192 reducedTerm193 := by decide +kernel

def reducedMerge188 : Integer.Sparse Master := [(Sum.inl 0, -202447107779051520000), (Sum.inl 1, 584605809478656000000), (Sum.inl 2, 76059018040320000000), (Sum.inl 3, -1046647895202201600000), (Sum.inl 12, -1046647895202201600000), (Sum.inl 13, -2464224457192243200000), (Sum.inl 32, -224734733682278400000)]

def originalMerge188 : Integer.Sparse OriginalKey := originalMerge186 ++ originalMerge187

theorem reducedMerge188Check : reducedMerge188 = Integer.Sparse.mergeBy masterLess reducedMerge186 reducedMerge187 := by decide +kernel

def reducedMerge189 : Integer.Sparse Master := [(Sum.inl 0, 26047635809771520000), (Sum.inl 1, 606057852937420800000), (Sum.inl 2, 510899665760870400000), (Sum.inl 3, -88891164691660800000), (Sum.inl 12, -864515247508684800000), (Sum.inl 13, 592240248107827200000), (Sum.inl 32, 450256473612288000000)]

def originalMerge189 : Integer.Sparse OriginalKey := originalMerge185 ++ originalMerge188

theorem reducedMerge189Check : reducedMerge189 = Integer.Sparse.mergeBy masterLess reducedMerge185 reducedMerge188 := by decide +kernel

def reducedMerge190 : Integer.Sparse Master := [(Sum.inl 0, -3595565347799040000), (Sum.inl 1, 478408015295078400000), (Sum.inl 2, 577179063504691200000), (Sum.inl 3, 1028839352854118400000), (Sum.inl 5, 195082412403916800000), (Sum.inl 6, 8236054536192000000), (Sum.inl 12, -416521704259584000000), (Sum.inl 13, 1969792370019532800000), (Sum.inl 26, 274301663182848000000), (Sum.inl 32, 668163070491033600000), (Sum.inl 34, 142524790603776000000), (Sum.inl 54, -860559389628825600000), (Sum.inl 56, 560711037616128000000), (Sum.inl 60, -131776872579072000000), (Sum.inl 61, -2041140596834304000000)]

def originalMerge190 : Integer.Sparse OriginalKey := originalMerge182 ++ originalMerge189

theorem reducedMerge190Check : reducedMerge190 = Integer.Sparse.mergeBy masterLess reducedMerge182 reducedMerge189 := by decide +kernel

def reducedMerge191 : Integer.Sparse Master := [(Sum.inl 0, -209343304474214400000), (Sum.inl 1, 767592116405452800000), (Sum.inl 2, 558248811931238400000), (Sum.inl 3, 1116497623862476800000), (Sum.inl 13, 1116497623862476800000)]

def originalMerge191 : Integer.Sparse OriginalKey := originalTerm195 ++ originalTerm196

theorem reducedMerge191Check : reducedMerge191 = Integer.Sparse.mergeBy masterLess reducedTerm195 reducedTerm196 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
