import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData07

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C07
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨107606939102091950273220527302786340890551562458571085572,399114476078032809568999731848101574276182045499492857⟩
def polyval0 : Box := ⟨3745874724990597878915306157922050007333443252084671935631,16197721037743392959780607200849185437213832540066234485⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨51889461676872498565624458356461035881388416001267,1732640784855811454359175081733861404785329443056⟩
def resval0Tail8 : Box := ⟨5893072682755933924460281270014716741926483329,347894793950410976620835020573381017242993229⟩
def resval0Tail12 : Box := ⟨5034333349979787067718056382124503823774040,447469922146103225755389239093915159441358⟩
def resval0Tail16 : Box := ⟨18939602734669199786594723842519460409800,25043108875664529446585999576827899040306⟩
def resval0Tail20 : Box := ⟨242466712992260905472923722291218467715,362770526914032708682052633323646832611605⟩
def resval0Tail24 : Box := ⟨9066016820137613639999759759114125054,5803661540488294283129713328216520266585530⟩
def resval0Tail28 : Box := ⟨901006703993289422958368383965618852,92858550717639094178352829830448813437245894⟩
def resval0Tail32 : Box := ⟨222883006422154944218477390769585832,1485736806871286354810800156852092373164483429⟩
def resval0Tail36 : Box := ⟨-394387748041087144814812286847878030,23771788908107327269145846111538220719153039836⟩
def resval0Tail40 : Box := ⟨-135855900462808664778845351505098901686,380348622401549748592422201805149876907784024343⟩
def resval0Tail44 : Box := ⟨-34830265733879073389520259727601349671595,6085577925769665539913860552844665030935833458554⟩
def resval0Tail48 : Box := ⟨-8916730314243529660904012619401506060876866,97369238452869239082450313627012740925629923553998⟩
def resval0Tail52 : Box := ⟨-2282684553034449819075801928553400855217399664,1557905675228940122769962701699256420380560050963106⟩
def resval0Tail56 : Box := ⟨-584367276995380894705728833392695784721535016005,24925942959328322358959173003316205371561441242466767⟩
def resval0Tail60 : Box := ⟨-149598022232287024248513328830904807428709965344752,398674839200237122877588084734460314373567023354170159⟩
def resval0Tail64 : Box := ⟨-38297087666872969492513821667507063970145064529569055,6342893903080476598249911390658794483775539158056695397⟩
def resval0Tail68 : Box := ⟨-9803914527685960041521426263005141415108257080262571322,92295056080502620451015017669354330831034398281741554780⟩
def resval0Tail72 : Box := ⟨738378480329011304009395104176463016324496729155119146062,2603290551079186021186761601013046824647505072123787481⟩
def resval0Tail76 : Box := ⟨-23694570105614703352877811393426095977367679769783,591102421875756032214212565394948511845787760787⟩
def resval0Tail80 : Box := ⟨-1202083033090911472770879122481945950176490686,60770220677781489068977094408768894450539332⟩
def resval0Tail84 : Box := ⟨-638432330881407701477663329630222007992758,50408145048848361480341383022633994240176⟩
def resval0Tail88 : Box := ⟨-1659248998868441241938838967341488416583,338142145518591765281714924313008248306⟩
def resval0Tail92 : Box := ⟨-15528963651869757143023011783828339649,2399447291166190157674105105465928658104⟩
def resval0Tail96 : Box := ⟨-439376931094572846674838875469576648,38352124970620995958163483167274518776021⟩
def resval0Tail100 : Box := ⟨-33762944632641793053544663671222769,613632492438984206986379978396582330244092⟩
def resval0Tail104 : Box := ⟨-6609189437607721271040798283962105,9818119720855051749247866717941772502739111⟩
def resval0Tail108 : Box := ⟨-4921287373379474019683639297871032,157089915490253054516136638666351246933414944⟩
def resval0Tail112 : Box := ⟨-451680801024453620068132173479989536,2513438647425438900355193115562016336127423026⟩
def resval0Tail116 : Box := ⟨-114694026376664282019090576403415639637,40215018251290050637643843288356138256635846253⟩
def resval0Tail120 : Box := ⟨-29359038556804062418115080704509419277599,643440264496588737960787777982197369144247670189⟩
def resval0Tail124 : Box := ⟨-7515895707838684072849806029640666098326387,10295037185793975654149661577163723580306416269980⟩
def resval0Tail128 : Box := ⟨-1924069003951453918070401467752831554803938654,164718791158055426604268857550669139140967182077753⟩
def resval0Tail132 : Box := ⟨-492561660934667531809683990664926840327811850969,2635038881980493176206421045633744654576930867837046⟩
def resval0Tail136 : Box := ⟨-126095799429836455888278113561796494482691692468103,42042407308549936881511597075257056367010106548823044⟩
def resval0Tail140 : Box := ⟨-32280698125871722500471709597384522072999777797838400,642415442300130689078099675329710019993172759001618574⟩
def resval0Tail144 : Box := ⟨-8391271023124259418054406631912806284045070339590746464,2465670639082417373668321458924141945410003259378915822⟩
def resval0Tail148 : Box := ⟨50173271997163987103470797974996710543038874,1049431012728690132486834258171870478584633⟩
def resval0Tail152 : Box := ⟨839377823415687040806229502000403587336,37806678930184102967158760979771520803⟩
def resval0Tail156 : Box := ⟨250343204444779375105541940043558403,18001580773473313137506623263972204⟩
def resval0Tail160 : Box := ⟨411754994051605988763205132965509,44271166619922631762496308293128⟩
def resval0Tail164 : Box := ⟨2582169039183093304118734079693,24556321198473559958931036428600⟩
def resval0Tail168 : Box := ⟨50528564248933883251195836479,386966330781738431570527662702498⟩
def resval0Tail172 : Box := ⟨2730452065165291001340057311,6191303568853307705545555582709831⟩
def resval0Tail176 : Box := ⟨377878673397189971153170561,99060845564073293043670178442243182⟩
def resval0Tail180 : Box := ⟨133880118245116723294932957,1584973526839951654134051835977384170⟩
def resval0Tail184 : Box := ⟨1562390591960268212806772420,25359576427419872077954835916744187197⟩
def resval0Tail188 : Box := ⟨373410280326339920083375899291,405753222488834923246987047975708982120⟩
def resval0Tail192 : Box := ⟨95541425286523062081458711699343,6492051470251913855181200210266590019796⟩
def resval0Tail196 : Box := ⟨24458362373026447830504349798026786,103872800594322506491693271815553289718314⟩
def resval0Tail200 : Box := ⟨6261338007033044460124280544527993498,1661958939504992644177959982500199997169485⟩
def resval0Tail204 : Box := ⟨1602902466949692993447275314283320497607,26589840311040625597217204737602366508207904⟩
def resval0Tail208 : Box := ⟨410343041852571026436857539478639346886270,425052748385619385014663051434991172709988115⟩
def resval0Tail212 : Box := ⟨105047879592181128359543145096658811813697349,6702361617383531452927113494267430941110219494⟩
def resval0Tail216 : Box := ⟨26895719853258700197677846121572490888026386668,82024547258334812890095454838563801299559723029⟩
theorem resval0H216 : resval0Tail216=hornerBox Q residualBox cell0 216 4 :=
  hornerChunk_step Q residualBox cell0 resval0Tail216 zero 216 4 0 (by decide +kernel) rfl
theorem resval0H212 : resval0Tail212=hornerBox Q residualBox cell0 212 8 :=
  hornerChunk_step Q residualBox cell0 resval0Tail212 resval0Tail216 212 4 4 (by decide +kernel) resval0H216
theorem resval0H208 : resval0Tail208=hornerBox Q residualBox cell0 208 12 :=
  hornerChunk_step Q residualBox cell0 resval0Tail208 resval0Tail212 208 4 8 (by decide +kernel) resval0H212
theorem resval0H204 : resval0Tail204=hornerBox Q residualBox cell0 204 16 :=
  hornerChunk_step Q residualBox cell0 resval0Tail204 resval0Tail208 204 4 12 (by decide +kernel) resval0H208
theorem resval0H200 : resval0Tail200=hornerBox Q residualBox cell0 200 20 :=
  hornerChunk_step Q residualBox cell0 resval0Tail200 resval0Tail204 200 4 16 (by decide +kernel) resval0H204
theorem resval0H196 : resval0Tail196=hornerBox Q residualBox cell0 196 24 :=
  hornerChunk_step Q residualBox cell0 resval0Tail196 resval0Tail200 196 4 20 (by decide +kernel) resval0H200
theorem resval0H192 : resval0Tail192=hornerBox Q residualBox cell0 192 28 :=
  hornerChunk_step Q residualBox cell0 resval0Tail192 resval0Tail196 192 4 24 (by decide +kernel) resval0H196
theorem resval0H188 : resval0Tail188=hornerBox Q residualBox cell0 188 32 :=
  hornerChunk_step Q residualBox cell0 resval0Tail188 resval0Tail192 188 4 28 (by decide +kernel) resval0H192
theorem resval0H184 : resval0Tail184=hornerBox Q residualBox cell0 184 36 :=
  hornerChunk_step Q residualBox cell0 resval0Tail184 resval0Tail188 184 4 32 (by decide +kernel) resval0H188
theorem resval0H180 : resval0Tail180=hornerBox Q residualBox cell0 180 40 :=
  hornerChunk_step Q residualBox cell0 resval0Tail180 resval0Tail184 180 4 36 (by decide +kernel) resval0H184
theorem resval0H176 : resval0Tail176=hornerBox Q residualBox cell0 176 44 :=
  hornerChunk_step Q residualBox cell0 resval0Tail176 resval0Tail180 176 4 40 (by decide +kernel) resval0H180
theorem resval0H172 : resval0Tail172=hornerBox Q residualBox cell0 172 48 :=
  hornerChunk_step Q residualBox cell0 resval0Tail172 resval0Tail176 172 4 44 (by decide +kernel) resval0H176
theorem resval0H168 : resval0Tail168=hornerBox Q residualBox cell0 168 52 :=
  hornerChunk_step Q residualBox cell0 resval0Tail168 resval0Tail172 168 4 48 (by decide +kernel) resval0H172
theorem resval0H164 : resval0Tail164=hornerBox Q residualBox cell0 164 56 :=
  hornerChunk_step Q residualBox cell0 resval0Tail164 resval0Tail168 164 4 52 (by decide +kernel) resval0H168
theorem resval0H160 : resval0Tail160=hornerBox Q residualBox cell0 160 60 :=
  hornerChunk_step Q residualBox cell0 resval0Tail160 resval0Tail164 160 4 56 (by decide +kernel) resval0H164
theorem resval0H156 : resval0Tail156=hornerBox Q residualBox cell0 156 64 :=
  hornerChunk_step Q residualBox cell0 resval0Tail156 resval0Tail160 156 4 60 (by decide +kernel) resval0H160
theorem resval0H152 : resval0Tail152=hornerBox Q residualBox cell0 152 68 :=
  hornerChunk_step Q residualBox cell0 resval0Tail152 resval0Tail156 152 4 64 (by decide +kernel) resval0H156
theorem resval0H148 : resval0Tail148=hornerBox Q residualBox cell0 148 72 :=
  hornerChunk_step Q residualBox cell0 resval0Tail148 resval0Tail152 148 4 68 (by decide +kernel) resval0H152
theorem resval0H144 : resval0Tail144=hornerBox Q residualBox cell0 144 76 :=
  hornerChunk_step Q residualBox cell0 resval0Tail144 resval0Tail148 144 4 72 (by decide +kernel) resval0H148
theorem resval0H140 : resval0Tail140=hornerBox Q residualBox cell0 140 80 :=
  hornerChunk_step Q residualBox cell0 resval0Tail140 resval0Tail144 140 4 76 (by decide +kernel) resval0H144
theorem resval0H136 : resval0Tail136=hornerBox Q residualBox cell0 136 84 :=
  hornerChunk_step Q residualBox cell0 resval0Tail136 resval0Tail140 136 4 80 (by decide +kernel) resval0H140
theorem resval0H132 : resval0Tail132=hornerBox Q residualBox cell0 132 88 :=
  hornerChunk_step Q residualBox cell0 resval0Tail132 resval0Tail136 132 4 84 (by decide +kernel) resval0H136
theorem resval0H128 : resval0Tail128=hornerBox Q residualBox cell0 128 92 :=
  hornerChunk_step Q residualBox cell0 resval0Tail128 resval0Tail132 128 4 88 (by decide +kernel) resval0H132
theorem resval0H124 : resval0Tail124=hornerBox Q residualBox cell0 124 96 :=
  hornerChunk_step Q residualBox cell0 resval0Tail124 resval0Tail128 124 4 92 (by decide +kernel) resval0H128
theorem resval0H120 : resval0Tail120=hornerBox Q residualBox cell0 120 100 :=
  hornerChunk_step Q residualBox cell0 resval0Tail120 resval0Tail124 120 4 96 (by decide +kernel) resval0H124
theorem resval0H116 : resval0Tail116=hornerBox Q residualBox cell0 116 104 :=
  hornerChunk_step Q residualBox cell0 resval0Tail116 resval0Tail120 116 4 100 (by decide +kernel) resval0H120
theorem resval0H112 : resval0Tail112=hornerBox Q residualBox cell0 112 108 :=
  hornerChunk_step Q residualBox cell0 resval0Tail112 resval0Tail116 112 4 104 (by decide +kernel) resval0H116
theorem resval0H108 : resval0Tail108=hornerBox Q residualBox cell0 108 112 :=
  hornerChunk_step Q residualBox cell0 resval0Tail108 resval0Tail112 108 4 108 (by decide +kernel) resval0H112
theorem resval0H104 : resval0Tail104=hornerBox Q residualBox cell0 104 116 :=
  hornerChunk_step Q residualBox cell0 resval0Tail104 resval0Tail108 104 4 112 (by decide +kernel) resval0H108
theorem resval0H100 : resval0Tail100=hornerBox Q residualBox cell0 100 120 :=
  hornerChunk_step Q residualBox cell0 resval0Tail100 resval0Tail104 100 4 116 (by decide +kernel) resval0H104
theorem resval0H96 : resval0Tail96=hornerBox Q residualBox cell0 96 124 :=
  hornerChunk_step Q residualBox cell0 resval0Tail96 resval0Tail100 96 4 120 (by decide +kernel) resval0H100
theorem resval0H92 : resval0Tail92=hornerBox Q residualBox cell0 92 128 :=
  hornerChunk_step Q residualBox cell0 resval0Tail92 resval0Tail96 92 4 124 (by decide +kernel) resval0H96
theorem resval0H88 : resval0Tail88=hornerBox Q residualBox cell0 88 132 :=
  hornerChunk_step Q residualBox cell0 resval0Tail88 resval0Tail92 88 4 128 (by decide +kernel) resval0H92
theorem resval0H84 : resval0Tail84=hornerBox Q residualBox cell0 84 136 :=
  hornerChunk_step Q residualBox cell0 resval0Tail84 resval0Tail88 84 4 132 (by decide +kernel) resval0H88
theorem resval0H80 : resval0Tail80=hornerBox Q residualBox cell0 80 140 :=
  hornerChunk_step Q residualBox cell0 resval0Tail80 resval0Tail84 80 4 136 (by decide +kernel) resval0H84
theorem resval0H76 : resval0Tail76=hornerBox Q residualBox cell0 76 144 :=
  hornerChunk_step Q residualBox cell0 resval0Tail76 resval0Tail80 76 4 140 (by decide +kernel) resval0H80
theorem resval0H72 : resval0Tail72=hornerBox Q residualBox cell0 72 148 :=
  hornerChunk_step Q residualBox cell0 resval0Tail72 resval0Tail76 72 4 144 (by decide +kernel) resval0H76
theorem resval0H68 : resval0Tail68=hornerBox Q residualBox cell0 68 152 :=
  hornerChunk_step Q residualBox cell0 resval0Tail68 resval0Tail72 68 4 148 (by decide +kernel) resval0H72
theorem resval0H64 : resval0Tail64=hornerBox Q residualBox cell0 64 156 :=
  hornerChunk_step Q residualBox cell0 resval0Tail64 resval0Tail68 64 4 152 (by decide +kernel) resval0H68
theorem resval0H60 : resval0Tail60=hornerBox Q residualBox cell0 60 160 :=
  hornerChunk_step Q residualBox cell0 resval0Tail60 resval0Tail64 60 4 156 (by decide +kernel) resval0H64
theorem resval0H56 : resval0Tail56=hornerBox Q residualBox cell0 56 164 :=
  hornerChunk_step Q residualBox cell0 resval0Tail56 resval0Tail60 56 4 160 (by decide +kernel) resval0H60
theorem resval0H52 : resval0Tail52=hornerBox Q residualBox cell0 52 168 :=
  hornerChunk_step Q residualBox cell0 resval0Tail52 resval0Tail56 52 4 164 (by decide +kernel) resval0H56
theorem resval0H48 : resval0Tail48=hornerBox Q residualBox cell0 48 172 :=
  hornerChunk_step Q residualBox cell0 resval0Tail48 resval0Tail52 48 4 168 (by decide +kernel) resval0H52
theorem resval0H44 : resval0Tail44=hornerBox Q residualBox cell0 44 176 :=
  hornerChunk_step Q residualBox cell0 resval0Tail44 resval0Tail48 44 4 172 (by decide +kernel) resval0H48
theorem resval0H40 : resval0Tail40=hornerBox Q residualBox cell0 40 180 :=
  hornerChunk_step Q residualBox cell0 resval0Tail40 resval0Tail44 40 4 176 (by decide +kernel) resval0H44
theorem resval0H36 : resval0Tail36=hornerBox Q residualBox cell0 36 184 :=
  hornerChunk_step Q residualBox cell0 resval0Tail36 resval0Tail40 36 4 180 (by decide +kernel) resval0H40
theorem resval0H32 : resval0Tail32=hornerBox Q residualBox cell0 32 188 :=
  hornerChunk_step Q residualBox cell0 resval0Tail32 resval0Tail36 32 4 184 (by decide +kernel) resval0H36
theorem resval0H28 : resval0Tail28=hornerBox Q residualBox cell0 28 192 :=
  hornerChunk_step Q residualBox cell0 resval0Tail28 resval0Tail32 28 4 188 (by decide +kernel) resval0H32
theorem resval0H24 : resval0Tail24=hornerBox Q residualBox cell0 24 196 :=
  hornerChunk_step Q residualBox cell0 resval0Tail24 resval0Tail28 24 4 192 (by decide +kernel) resval0H28
theorem resval0H20 : resval0Tail20=hornerBox Q residualBox cell0 20 200 :=
  hornerChunk_step Q residualBox cell0 resval0Tail20 resval0Tail24 20 4 196 (by decide +kernel) resval0H24
theorem resval0H16 : resval0Tail16=hornerBox Q residualBox cell0 16 204 :=
  hornerChunk_step Q residualBox cell0 resval0Tail16 resval0Tail20 16 4 200 (by decide +kernel) resval0H20
theorem resval0H12 : resval0Tail12=hornerBox Q residualBox cell0 12 208 :=
  hornerChunk_step Q residualBox cell0 resval0Tail12 resval0Tail16 12 4 204 (by decide +kernel) resval0H16
theorem resval0H8 : resval0Tail8=hornerBox Q residualBox cell0 8 212 :=
  hornerChunk_step Q residualBox cell0 resval0Tail8 resval0Tail12 8 4 208 (by decide +kernel) resval0H12
theorem resval0H4 : resval0Tail4=hornerBox Q residualBox cell0 4 216 :=
  hornerChunk_step Q residualBox cell0 resval0Tail4 resval0Tail8 4 4 212 (by decide +kernel) resval0H8
theorem resval0H0 : resval0=hornerBox Q residualBox cell0 0 220 :=
  hornerChunk_step Q residualBox cell0 resval0 resval0Tail4 0 4 216 (by decide +kernel) resval0H4
theorem resval0_eq : resval0=hornerBox Q residualBox cell0 0 220 := resval0H0
def polyval0Tail5 : Box := ⟨1937567883339673157907792646890252162324742056977925,52077122094543700738065933360687198248068554832676⟩
def polyval0Tail9 : Box := ⟨176376391465336128175018872338460975131666226814,9331652880397423806149474976676701583917132795⟩
def polyval0Tail13 : Box := ⟨130370834724935417771921518548212143422056979,10684080047650719707865977384345221862611211⟩
def polyval0Tail17 : Box := ⟨429784572255754667939110913579449027180143,416974084283878081864883127493031745870761⟩
def polyval0Tail21 : Box := ⟨4834659100447083578220713990486489009348,5866916200693732527621390389654825269280293⟩
def polyval0Tail25 : Box := ⟨158663987916723259178217184084669424846,93858149447551014931988561422367535982418624⟩
def polyval0Tail29 : Box := ⟨13790959557149764524095111339019279009,1501729831569583559990120778517870909481531394⟩
def polyval0Tail33 : Box := ⟨3016069301227929918081721167396190224,24027677238702692676349659776691439843886830387⟩
def polyval0Tail37 : Box := ⟨7157327873878684630062357280637052040,384442835797504153180658965818841797152289445280⟩
def polyval0Tail41 : Box := ⟨1431258528104075765591740004881426965568,6151085371420836246486225941834521908143662337636⟩
def polyval0Tail45 : Box := ⟨365899632981298636574289750315365078221979,98417365599707469844365639853680385511349769481258⟩
def polyval0Tail49 : Box := ⟨93668792652748641686963663030395901005959202,1574677761780855098309427795585899129528064828114417⟩
def polyval0Tail53 : Box := ⟨23979199839533786390712655024635217014265057290,25194821707994341848636778624515278566401197212276738⟩
def polyval0Tail57 : Box := ⟨6138674969259755359327619186492363002902050947375,403111392320155224836816578991871361219138063454293094⟩
def polyval0Tail61 : Box := ⟨1571500789915764141421002782678114069453156040139536,6448308995138167177020643878171720475793491579498086602⟩
def polyval0Tail65 : Box := ⟨402304212806300729039085743713952942817206068739298253,102795783729223439753778196048570031810314388619293402082⟩
def polyval0Tail69 : Box := ⟨102990007954816263237463297540198857264169840763562155044,1548179467074613874672737696102451458088377681927168000828⟩
def polyval0Tail73 : Box := ⟨26468750000000000000000000000000000000000000000000000000000,2⟩
theorem polyval0H73 : polyval0Tail73=hornerBox Q polyBox cell0 73 1 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail73 zero 73 1 0 (by decide +kernel) rfl
theorem polyval0H69 : polyval0Tail69=hornerBox Q polyBox cell0 69 5 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail69 polyval0Tail73 69 4 1 (by decide +kernel) polyval0H73
theorem polyval0H65 : polyval0Tail65=hornerBox Q polyBox cell0 65 9 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail65 polyval0Tail69 65 4 5 (by decide +kernel) polyval0H69
theorem polyval0H61 : polyval0Tail61=hornerBox Q polyBox cell0 61 13 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail61 polyval0Tail65 61 4 9 (by decide +kernel) polyval0H65
theorem polyval0H57 : polyval0Tail57=hornerBox Q polyBox cell0 57 17 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail57 polyval0Tail61 57 4 13 (by decide +kernel) polyval0H61
theorem polyval0H53 : polyval0Tail53=hornerBox Q polyBox cell0 53 21 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail53 polyval0Tail57 53 4 17 (by decide +kernel) polyval0H57
theorem polyval0H49 : polyval0Tail49=hornerBox Q polyBox cell0 49 25 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail49 polyval0Tail53 49 4 21 (by decide +kernel) polyval0H53
theorem polyval0H45 : polyval0Tail45=hornerBox Q polyBox cell0 45 29 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail45 polyval0Tail49 45 4 25 (by decide +kernel) polyval0H49
theorem polyval0H41 : polyval0Tail41=hornerBox Q polyBox cell0 41 33 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail41 polyval0Tail45 41 4 29 (by decide +kernel) polyval0H45
theorem polyval0H37 : polyval0Tail37=hornerBox Q polyBox cell0 37 37 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail37 polyval0Tail41 37 4 33 (by decide +kernel) polyval0H41
theorem polyval0H33 : polyval0Tail33=hornerBox Q polyBox cell0 33 41 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail33 polyval0Tail37 33 4 37 (by decide +kernel) polyval0H37
theorem polyval0H29 : polyval0Tail29=hornerBox Q polyBox cell0 29 45 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail29 polyval0Tail33 29 4 41 (by decide +kernel) polyval0H33
theorem polyval0H25 : polyval0Tail25=hornerBox Q polyBox cell0 25 49 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail25 polyval0Tail29 25 4 45 (by decide +kernel) polyval0H29
theorem polyval0H21 : polyval0Tail21=hornerBox Q polyBox cell0 21 53 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail21 polyval0Tail25 21 4 49 (by decide +kernel) polyval0H25
theorem polyval0H17 : polyval0Tail17=hornerBox Q polyBox cell0 17 57 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail17 polyval0Tail21 17 4 53 (by decide +kernel) polyval0H21
theorem polyval0H13 : polyval0Tail13=hornerBox Q polyBox cell0 13 61 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail13 polyval0Tail17 13 4 57 (by decide +kernel) polyval0H17
theorem polyval0H9 : polyval0Tail9=hornerBox Q polyBox cell0 9 65 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail9 polyval0Tail13 9 4 61 (by decide +kernel) polyval0H13
theorem polyval0H5 : polyval0Tail5=hornerBox Q polyBox cell0 5 69 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail5 polyval0Tail9 5 4 65 (by decide +kernel) polyval0H9
theorem polyval0H1 : polyval0=hornerBox Q polyBox cell0 1 73 :=
  hornerChunk_step Q polyBox cell0 polyval0 polyval0Tail5 1 4 69 (by decide +kernel) polyval0H5
theorem polyval0_eq : polyval0=hornerBox Q polyBox cell0 1 73 := polyval0H1
theorem polyval0_upper : 5*(polyval0.center+polyval0.radius)<Q := by decide +kernel
theorem resval0_pos : 0<(resval0).center-(resval0).radius := by decide +kernel
theorem polyval0_pos : 0<(polyval0).center-(polyval0).radius := by decide +kernel
def cell1 : Box := ⟨625000000000000000000000000000000000000000000000000000000000,125000000000000000000000000000000000000000000000000000000002⟩
def resval1 : Box := ⟨107396498561720362790426782110110419013678327474400984606,328236715597363689600458298102428848465848915370483207⟩
def polyval1 : Box := ⟨3728259624878296126647036097033899062694020472017048081574,10210082762793572039530035100678982817911964837831944474⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨50406361429022260744706077936508216146865333332276,3097121028954551775090292369828137821444488227714⟩
def resval1Tail8 : Box := ⟨5551844138612079625694243862146769252777540260,6018196732460517502874454434618945885887652489646⟩
def resval1Tail12 : Box := ⟨-314701511726857753733631205979427742728680684,19019641525541739881502664062120643354133340400055⟩
def resval1Tail16 : Box := ⟨-2093049734588158490082251517479819849770783083,60110375164267876898433510461207543044180307015257⟩
def resval1Tail20 : Box := ⟨-13717122939398664066899246156294393713056252340,189971367652859272015035918238888679892882201971878⟩
def resval1Tail24 : Box := ⟨-89896538288420823736789113769597566759509076339,600356791148789493520575149430441728097556606890712⟩
def resval1Tail28 : Box := ⟨-589145953377094430153605213120693913207829423314,1897118904020618266803884523765738059322325697753875⟩
def resval1Tail32 : Box := ⟨-3861026920056839968367424181409460701292205338234,5993833550775535232950638610309177516303882723583917⟩
def resval1Tail36 : Box := ⟨-25303626023285580715992652717825259452102201464766,18930373063977598348237515400619902181164812070844598⟩
def resval1Tail40 : Box := ⟨-165829843506204924089578543089235184658697455286074,59743469324891650542549579650078930271210929001109572⟩
def resval1Tail44 : Box := ⟨-1086782462402265050647998632228140145038377494744575,188256187748830463096463277860138275098259648004803030⟩
def resval1Tail48 : Box := ⟨-7122337545599483021275580466086706111283485264803042,591294951023234814333706854379954942467428600354905679⟩
def resval1Tail52 : Box := ⟨-46676951338840689517086387281858316939815381490567985,1844617195249079942161821086271961630598194681553185810⟩
def resval1Tail56 : Box := ⟨-305902068294218617820373359221614490057105866837244089,5671521407341670180399768253210560230403123243745928868⟩
def resval1Tail60 : Box := ⟨-2004759794770666838193789372310986231680537752377963502,16886850202298431007050188909278399714473962720538489200⟩
def resval1Tail64 : Box := ⟨-13138393787446334817953084973381782245692217864031195476,46568422990016331210613631371517777580886615584297246456⟩
def resval1Tail68 : Box := ⟨-86103713416541082072622241466264985330887867590351204445,102599253841792181630841386037329548866850508120420547993⟩
def resval1Tail72 : Box := ⟨741005812215970748952732848830242691470528240625677990700,1729143462977563758642658764241208659320402077481598874⟩
def resval1Tail76 : Box := ⟨-23174024078667336417819557793065013101737829717566,423211423295601428045994217966836375776858705991⟩
def resval1Tail80 : Box := ⟨-1149750860409970554726586297692275569355224881,59616661300101127270484602392814230021849832107⟩
def resval1Tail84 : Box := ⟨-3227982760874377550062752542992043384124048,188289391241651522590389067737271292615516895486⟩
def resval1Tail88 : Box := ⟨-17245752745439300333583142356406895187473834,595078520088617047959967909242965892430668694014⟩
def resval1Tail92 : Box := ⟨-113011861727462176980729727427615171247324036,1880683477834586313847262165112143669824181346221⟩
def resval1Tail96 : Box := ⟨-740634447016015168542249435536353254163901779,5943505061339359742226902780163426635502120630095⟩
def resval1Tail100 : Box := ⟨-4853821909507844476702287409519343643932500383,18781898006747460976319184008566544052327110835801⟩
def resval1Tail104 : Box := ⟨-31810007265970915594645742210874847883733465253,59343603179600409679341673686040403598136809884427⟩
def resval1Tail108 : Box := ⟨-208470063618234494316178158954655843383334532364,187447156798576730083927720711814471558852230482714⟩
def resval1Tail112 : Box := ⟨-1366229408928448166145573741805271379710926010753,591718220920971680306096386569626607424240451448328⟩
def resval1Tail116 : Box := ⟨-8953721054353467347532494659099794724374135026382,1865486023198170391095079369813149729548025001408405⟩
def resval1Tail120 : Box := ⟨-58679106301810886239363960441798140939367633736369,5865476134792585515552288500158952659950708226983076⟩
def resval1Tail124 : Box := ⟨-384559391059548449026507697649423539258031749172641,18338696679559778951208314998088841707311580342988285⟩
def resval1Tail128 : Box := ⟨-2520248425247903779039747916162892708419666204755213,56654486810289758815093269964768010865304491237479021⟩
def resval1Tail132 : Box := ⟨-16516700079714739604558059082103010763156375588683822,170504685356066111105312996711468131643730457562236689⟩
def resval1Tail136 : Box := ⟨-108243845652105563505170538165200230864749956858823322,482836088572060601633857913286197223191543427335377714⟩
def resval1Tail140 : Box := ⟨-709386949693048749919132598445620238817039352945785585,1158717597933031452094811835326406047883888798778172873⟩
def resval1Tail144 : Box := ⟨-4701950038080228719390431996243924968621401059079660103,1243898169565698983156726569377445825483055812237094835⟩
def resval1Tail148 : Box := ⟨49440688641786869368887567535530327682962884,793605277083687343781775035513581927934304⟩
def resval1Tail152 : Box := ⟨807755540165024218840537247991697873006,2507234434367406924315131100448082722137⟩
def resval1Tail156 : Box := ⟨331813059071263578360726875074914028,7841845672825386967429515202343779802125⟩
def resval1Tail160 : Box := ⟨630429450659403876488917262056924157,24783773209737575192532391655578094625901⟩
def resval1Tail164 : Box := ⟨4129103483086249765278742996895057876,78326824400724952721915723634488952470159⟩
def resval1Tail168 : Box := ⟨27060477461996806610328670792951069702,247537434540784881779151243532714317714105⟩
def resval1Tail172 : Box := ⟨177343544808506725460056701219740899446,782248714784324619657885150799608627899901⟩
def resval1Tail176 : Box := ⟨1162238655242196376989736063811581859136,2471690488903492184700667815935041044019320⟩
def resval1Tail180 : Box := ⟨7616847250993331168315122042364907385655,7807818933675376098000827829328471964096831⟩
def resval1Tail184 : Box := ⟨49917770144109310609375400579119302239827,24650718772042934521292916745992089273501522⟩
def resval1Tail188 : Box := ⟨327141098416434406748408096447099060836635,77739068220100642221045759575176807359559304⟩
def resval1Tail192 : Box := ⟨2143951902581944239007081940634856255263579,244583820758410297885870294086007264897861316⟩
def resval1Tail196 : Box := ⟨14050603188761033464109797081407806924518037,765730999295362599212538340877485837679959282⟩
def resval1Tail200 : Box := ⟨92082033057864528894406109457301624495008745,2372412908126526376518212748890130313097457920⟩
def resval1Tail204 : Box := ⟨603468811848048315217686911966862268545898627,7185552236833503589509018247155054214457092150⟩
def resval1Tail208 : Box := ⟨3954893205339593658956681196207285964658516655,20662259738650745400832208378269231521374857454⟩
def resval1Tail212 : Box := ⟨25918788143066836784775504982968581393707825069,51883571803565524450478340256468172588495808199⟩
def resval1Tail216 : Box := ⟨169862898499772614208948541686467377455316960256,76032163049432213264280191753952769427536149490⟩
theorem resval1H216 : resval1Tail216=hornerBox Q residualBox cell1 216 4 :=
  hornerChunk_step Q residualBox cell1 resval1Tail216 zero 216 4 0 (by decide +kernel) rfl
theorem resval1H212 : resval1Tail212=hornerBox Q residualBox cell1 212 8 :=
  hornerChunk_step Q residualBox cell1 resval1Tail212 resval1Tail216 212 4 4 (by decide +kernel) resval1H216
theorem resval1H208 : resval1Tail208=hornerBox Q residualBox cell1 208 12 :=
  hornerChunk_step Q residualBox cell1 resval1Tail208 resval1Tail212 208 4 8 (by decide +kernel) resval1H212
theorem resval1H204 : resval1Tail204=hornerBox Q residualBox cell1 204 16 :=
  hornerChunk_step Q residualBox cell1 resval1Tail204 resval1Tail208 204 4 12 (by decide +kernel) resval1H208
theorem resval1H200 : resval1Tail200=hornerBox Q residualBox cell1 200 20 :=
  hornerChunk_step Q residualBox cell1 resval1Tail200 resval1Tail204 200 4 16 (by decide +kernel) resval1H204
theorem resval1H196 : resval1Tail196=hornerBox Q residualBox cell1 196 24 :=
  hornerChunk_step Q residualBox cell1 resval1Tail196 resval1Tail200 196 4 20 (by decide +kernel) resval1H200
theorem resval1H192 : resval1Tail192=hornerBox Q residualBox cell1 192 28 :=
  hornerChunk_step Q residualBox cell1 resval1Tail192 resval1Tail196 192 4 24 (by decide +kernel) resval1H196
theorem resval1H188 : resval1Tail188=hornerBox Q residualBox cell1 188 32 :=
  hornerChunk_step Q residualBox cell1 resval1Tail188 resval1Tail192 188 4 28 (by decide +kernel) resval1H192
theorem resval1H184 : resval1Tail184=hornerBox Q residualBox cell1 184 36 :=
  hornerChunk_step Q residualBox cell1 resval1Tail184 resval1Tail188 184 4 32 (by decide +kernel) resval1H188
theorem resval1H180 : resval1Tail180=hornerBox Q residualBox cell1 180 40 :=
  hornerChunk_step Q residualBox cell1 resval1Tail180 resval1Tail184 180 4 36 (by decide +kernel) resval1H184
theorem resval1H176 : resval1Tail176=hornerBox Q residualBox cell1 176 44 :=
  hornerChunk_step Q residualBox cell1 resval1Tail176 resval1Tail180 176 4 40 (by decide +kernel) resval1H180
theorem resval1H172 : resval1Tail172=hornerBox Q residualBox cell1 172 48 :=
  hornerChunk_step Q residualBox cell1 resval1Tail172 resval1Tail176 172 4 44 (by decide +kernel) resval1H176
theorem resval1H168 : resval1Tail168=hornerBox Q residualBox cell1 168 52 :=
  hornerChunk_step Q residualBox cell1 resval1Tail168 resval1Tail172 168 4 48 (by decide +kernel) resval1H172
theorem resval1H164 : resval1Tail164=hornerBox Q residualBox cell1 164 56 :=
  hornerChunk_step Q residualBox cell1 resval1Tail164 resval1Tail168 164 4 52 (by decide +kernel) resval1H168
theorem resval1H160 : resval1Tail160=hornerBox Q residualBox cell1 160 60 :=
  hornerChunk_step Q residualBox cell1 resval1Tail160 resval1Tail164 160 4 56 (by decide +kernel) resval1H164
theorem resval1H156 : resval1Tail156=hornerBox Q residualBox cell1 156 64 :=
  hornerChunk_step Q residualBox cell1 resval1Tail156 resval1Tail160 156 4 60 (by decide +kernel) resval1H160
theorem resval1H152 : resval1Tail152=hornerBox Q residualBox cell1 152 68 :=
  hornerChunk_step Q residualBox cell1 resval1Tail152 resval1Tail156 152 4 64 (by decide +kernel) resval1H156
theorem resval1H148 : resval1Tail148=hornerBox Q residualBox cell1 148 72 :=
  hornerChunk_step Q residualBox cell1 resval1Tail148 resval1Tail152 148 4 68 (by decide +kernel) resval1H152
theorem resval1H144 : resval1Tail144=hornerBox Q residualBox cell1 144 76 :=
  hornerChunk_step Q residualBox cell1 resval1Tail144 resval1Tail148 144 4 72 (by decide +kernel) resval1H148
theorem resval1H140 : resval1Tail140=hornerBox Q residualBox cell1 140 80 :=
  hornerChunk_step Q residualBox cell1 resval1Tail140 resval1Tail144 140 4 76 (by decide +kernel) resval1H144
theorem resval1H136 : resval1Tail136=hornerBox Q residualBox cell1 136 84 :=
  hornerChunk_step Q residualBox cell1 resval1Tail136 resval1Tail140 136 4 80 (by decide +kernel) resval1H140
theorem resval1H132 : resval1Tail132=hornerBox Q residualBox cell1 132 88 :=
  hornerChunk_step Q residualBox cell1 resval1Tail132 resval1Tail136 132 4 84 (by decide +kernel) resval1H136
theorem resval1H128 : resval1Tail128=hornerBox Q residualBox cell1 128 92 :=
  hornerChunk_step Q residualBox cell1 resval1Tail128 resval1Tail132 128 4 88 (by decide +kernel) resval1H132
theorem resval1H124 : resval1Tail124=hornerBox Q residualBox cell1 124 96 :=
  hornerChunk_step Q residualBox cell1 resval1Tail124 resval1Tail128 124 4 92 (by decide +kernel) resval1H128
theorem resval1H120 : resval1Tail120=hornerBox Q residualBox cell1 120 100 :=
  hornerChunk_step Q residualBox cell1 resval1Tail120 resval1Tail124 120 4 96 (by decide +kernel) resval1H124
theorem resval1H116 : resval1Tail116=hornerBox Q residualBox cell1 116 104 :=
  hornerChunk_step Q residualBox cell1 resval1Tail116 resval1Tail120 116 4 100 (by decide +kernel) resval1H120
theorem resval1H112 : resval1Tail112=hornerBox Q residualBox cell1 112 108 :=
  hornerChunk_step Q residualBox cell1 resval1Tail112 resval1Tail116 112 4 104 (by decide +kernel) resval1H116
theorem resval1H108 : resval1Tail108=hornerBox Q residualBox cell1 108 112 :=
  hornerChunk_step Q residualBox cell1 resval1Tail108 resval1Tail112 108 4 108 (by decide +kernel) resval1H112
theorem resval1H104 : resval1Tail104=hornerBox Q residualBox cell1 104 116 :=
  hornerChunk_step Q residualBox cell1 resval1Tail104 resval1Tail108 104 4 112 (by decide +kernel) resval1H108
theorem resval1H100 : resval1Tail100=hornerBox Q residualBox cell1 100 120 :=
  hornerChunk_step Q residualBox cell1 resval1Tail100 resval1Tail104 100 4 116 (by decide +kernel) resval1H104
theorem resval1H96 : resval1Tail96=hornerBox Q residualBox cell1 96 124 :=
  hornerChunk_step Q residualBox cell1 resval1Tail96 resval1Tail100 96 4 120 (by decide +kernel) resval1H100
theorem resval1H92 : resval1Tail92=hornerBox Q residualBox cell1 92 128 :=
  hornerChunk_step Q residualBox cell1 resval1Tail92 resval1Tail96 92 4 124 (by decide +kernel) resval1H96
theorem resval1H88 : resval1Tail88=hornerBox Q residualBox cell1 88 132 :=
  hornerChunk_step Q residualBox cell1 resval1Tail88 resval1Tail92 88 4 128 (by decide +kernel) resval1H92
theorem resval1H84 : resval1Tail84=hornerBox Q residualBox cell1 84 136 :=
  hornerChunk_step Q residualBox cell1 resval1Tail84 resval1Tail88 84 4 132 (by decide +kernel) resval1H88
theorem resval1H80 : resval1Tail80=hornerBox Q residualBox cell1 80 140 :=
  hornerChunk_step Q residualBox cell1 resval1Tail80 resval1Tail84 80 4 136 (by decide +kernel) resval1H84
theorem resval1H76 : resval1Tail76=hornerBox Q residualBox cell1 76 144 :=
  hornerChunk_step Q residualBox cell1 resval1Tail76 resval1Tail80 76 4 140 (by decide +kernel) resval1H80
theorem resval1H72 : resval1Tail72=hornerBox Q residualBox cell1 72 148 :=
  hornerChunk_step Q residualBox cell1 resval1Tail72 resval1Tail76 72 4 144 (by decide +kernel) resval1H76
theorem resval1H68 : resval1Tail68=hornerBox Q residualBox cell1 68 152 :=
  hornerChunk_step Q residualBox cell1 resval1Tail68 resval1Tail72 68 4 148 (by decide +kernel) resval1H72
theorem resval1H64 : resval1Tail64=hornerBox Q residualBox cell1 64 156 :=
  hornerChunk_step Q residualBox cell1 resval1Tail64 resval1Tail68 64 4 152 (by decide +kernel) resval1H68
theorem resval1H60 : resval1Tail60=hornerBox Q residualBox cell1 60 160 :=
  hornerChunk_step Q residualBox cell1 resval1Tail60 resval1Tail64 60 4 156 (by decide +kernel) resval1H64
theorem resval1H56 : resval1Tail56=hornerBox Q residualBox cell1 56 164 :=
  hornerChunk_step Q residualBox cell1 resval1Tail56 resval1Tail60 56 4 160 (by decide +kernel) resval1H60
theorem resval1H52 : resval1Tail52=hornerBox Q residualBox cell1 52 168 :=
  hornerChunk_step Q residualBox cell1 resval1Tail52 resval1Tail56 52 4 164 (by decide +kernel) resval1H56
theorem resval1H48 : resval1Tail48=hornerBox Q residualBox cell1 48 172 :=
  hornerChunk_step Q residualBox cell1 resval1Tail48 resval1Tail52 48 4 168 (by decide +kernel) resval1H52
theorem resval1H44 : resval1Tail44=hornerBox Q residualBox cell1 44 176 :=
  hornerChunk_step Q residualBox cell1 resval1Tail44 resval1Tail48 44 4 172 (by decide +kernel) resval1H48
theorem resval1H40 : resval1Tail40=hornerBox Q residualBox cell1 40 180 :=
  hornerChunk_step Q residualBox cell1 resval1Tail40 resval1Tail44 40 4 176 (by decide +kernel) resval1H44
theorem resval1H36 : resval1Tail36=hornerBox Q residualBox cell1 36 184 :=
  hornerChunk_step Q residualBox cell1 resval1Tail36 resval1Tail40 36 4 180 (by decide +kernel) resval1H40
theorem resval1H32 : resval1Tail32=hornerBox Q residualBox cell1 32 188 :=
  hornerChunk_step Q residualBox cell1 resval1Tail32 resval1Tail36 32 4 184 (by decide +kernel) resval1H36
theorem resval1H28 : resval1Tail28=hornerBox Q residualBox cell1 28 192 :=
  hornerChunk_step Q residualBox cell1 resval1Tail28 resval1Tail32 28 4 188 (by decide +kernel) resval1H32
theorem resval1H24 : resval1Tail24=hornerBox Q residualBox cell1 24 196 :=
  hornerChunk_step Q residualBox cell1 resval1Tail24 resval1Tail28 24 4 192 (by decide +kernel) resval1H28
theorem resval1H20 : resval1Tail20=hornerBox Q residualBox cell1 20 200 :=
  hornerChunk_step Q residualBox cell1 resval1Tail20 resval1Tail24 20 4 196 (by decide +kernel) resval1H24
theorem resval1H16 : resval1Tail16=hornerBox Q residualBox cell1 16 204 :=
  hornerChunk_step Q residualBox cell1 resval1Tail16 resval1Tail20 16 4 200 (by decide +kernel) resval1H20
theorem resval1H12 : resval1Tail12=hornerBox Q residualBox cell1 12 208 :=
  hornerChunk_step Q residualBox cell1 resval1Tail12 resval1Tail16 12 4 204 (by decide +kernel) resval1H16
theorem resval1H8 : resval1Tail8=hornerBox Q residualBox cell1 8 212 :=
  hornerChunk_step Q residualBox cell1 resval1Tail8 resval1Tail12 8 4 208 (by decide +kernel) resval1H12
theorem resval1H4 : resval1Tail4=hornerBox Q residualBox cell1 4 216 :=
  hornerChunk_step Q residualBox cell1 resval1Tail4 resval1Tail8 4 4 212 (by decide +kernel) resval1H8
theorem resval1H0 : resval1=hornerBox Q residualBox cell1 0 220 :=
  hornerChunk_step Q residualBox cell1 resval1 resval1Tail4 0 4 216 (by decide +kernel) resval1H4
theorem resval1_eq : resval1=hornerBox Q residualBox cell1 0 220 := resval1H0
def polyval1Tail5 : Box := ⟨1886114792927742792783738009132269649445334941372061,117688383178041803708822115307442937118552169601576⟩
def polyval1Tail9 : Box := ⟨170208188511273526211454971629315951539862209507,266750217991159496866149965355355887927676190845846⟩
def polyval1Tail13 : Box := ⟨15077901968650233752315535932615776443757711597,843038701874863420016387779897738014975007700068040⟩
def polyval1Tail17 : Box := ⟨98019719477047630012341430416452559112400044435,2664367862996868842213997799929420810061143237974889⟩
def polyval1Tail21 : Box := ⟨642379479824793702373200626557512310776663367698,8420385594286765424605208439590231776990427214724149⟩
def polyval1Tail25 : Box := ⟨4209898131094456160794190232032663906650328096022,26610397031290476329034967517954178693594489345057055⟩
def polyval1Tail29 : Box := ⟨27589988391058562373140937394335795994164144199938,84087710924348288867059406885430844442777910840096418⟩
def polyval1Tail33 : Box := ⟨180813747919568527130207736132128643336464807131958,265665075556540555403870848788711455010544930224307611⟩
def polyval1Tail37 : Box := ⟨1184980978365669723495460162579113379892896566152596,839019311144372492577412787287917286523388641781329165⟩
def polyval1Tail41 : Box := ⟨7765891339817246577794665668608344636648291798845013,2647694587467849041037040968540975321667299729407921186⟩
def polyval1Tail45 : Box := ⟨50894545484626301815796102631788853593153811360970093,8341671906055652333477593503621438981556289527214364147⟩
def polyval1Tail49 : Box := ⟨333542493288046935013489679445408487484416908554356113,26191111970839253450294831665596863243221097802057644970⟩
def polyval1Tail53 : Box := ⟨2185904084012544808962876733538358301944630141285402337,81645102617426824642838811279488445643045916835730702775⟩
def polyval1Tail57 : Box := ⟨14325541004984645819733663180504309360548223141931842298,250621838199564496612239719628390843912527724168405448412⟩
def polyval1Tail61 : Box := ⟨93883865530274532140744960256339656471513033151590386137,743480690968058961900862313702028234509910294643680616592⟩
def polyval1Tail65 : Box := ⟨615277301146326002165703636802360351981210617599205412260,2031208210755079929345350807422384983500590993727646751637⟩
def polyval1Tail69 : Box := ⟨4032281382589279899795901665023848600301961022579249468774,4331919789487077734608192887826931608905484072783546776998⟩
def polyval1Tail73 : Box := ⟨26468750000000000000000000000000000000000000000000000000000,2⟩
theorem polyval1H73 : polyval1Tail73=hornerBox Q polyBox cell1 73 1 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail73 zero 73 1 0 (by decide +kernel) rfl
theorem polyval1H69 : polyval1Tail69=hornerBox Q polyBox cell1 69 5 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail69 polyval1Tail73 69 4 1 (by decide +kernel) polyval1H73
theorem polyval1H65 : polyval1Tail65=hornerBox Q polyBox cell1 65 9 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail65 polyval1Tail69 65 4 5 (by decide +kernel) polyval1H69
theorem polyval1H61 : polyval1Tail61=hornerBox Q polyBox cell1 61 13 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail61 polyval1Tail65 61 4 9 (by decide +kernel) polyval1H65
theorem polyval1H57 : polyval1Tail57=hornerBox Q polyBox cell1 57 17 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail57 polyval1Tail61 57 4 13 (by decide +kernel) polyval1H61
theorem polyval1H53 : polyval1Tail53=hornerBox Q polyBox cell1 53 21 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail53 polyval1Tail57 53 4 17 (by decide +kernel) polyval1H57
theorem polyval1H49 : polyval1Tail49=hornerBox Q polyBox cell1 49 25 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail49 polyval1Tail53 49 4 21 (by decide +kernel) polyval1H53
theorem polyval1H45 : polyval1Tail45=hornerBox Q polyBox cell1 45 29 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail45 polyval1Tail49 45 4 25 (by decide +kernel) polyval1H49
theorem polyval1H41 : polyval1Tail41=hornerBox Q polyBox cell1 41 33 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail41 polyval1Tail45 41 4 29 (by decide +kernel) polyval1H45
theorem polyval1H37 : polyval1Tail37=hornerBox Q polyBox cell1 37 37 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail37 polyval1Tail41 37 4 33 (by decide +kernel) polyval1H41
theorem polyval1H33 : polyval1Tail33=hornerBox Q polyBox cell1 33 41 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail33 polyval1Tail37 33 4 37 (by decide +kernel) polyval1H37
theorem polyval1H29 : polyval1Tail29=hornerBox Q polyBox cell1 29 45 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail29 polyval1Tail33 29 4 41 (by decide +kernel) polyval1H33
theorem polyval1H25 : polyval1Tail25=hornerBox Q polyBox cell1 25 49 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail25 polyval1Tail29 25 4 45 (by decide +kernel) polyval1H29
theorem polyval1H21 : polyval1Tail21=hornerBox Q polyBox cell1 21 53 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail21 polyval1Tail25 21 4 49 (by decide +kernel) polyval1H25
theorem polyval1H17 : polyval1Tail17=hornerBox Q polyBox cell1 17 57 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail17 polyval1Tail21 17 4 53 (by decide +kernel) polyval1H21
theorem polyval1H13 : polyval1Tail13=hornerBox Q polyBox cell1 13 61 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail13 polyval1Tail17 13 4 57 (by decide +kernel) polyval1H17
theorem polyval1H9 : polyval1Tail9=hornerBox Q polyBox cell1 9 65 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail9 polyval1Tail13 9 4 61 (by decide +kernel) polyval1H13
theorem polyval1H5 : polyval1Tail5=hornerBox Q polyBox cell1 5 69 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail5 polyval1Tail9 5 4 65 (by decide +kernel) polyval1H9
theorem polyval1H1 : polyval1=hornerBox Q polyBox cell1 1 73 :=
  hornerChunk_step Q polyBox cell1 polyval1 polyval1Tail5 1 4 69 (by decide +kernel) polyval1H5
theorem polyval1_eq : polyval1=hornerBox Q polyBox cell1 1 73 := polyval1H1
theorem polyval1_upper : 5*(polyval1.center+polyval1.radius)<Q := by decide +kernel
theorem resval1_pos : 0<(resval1).center-(resval1).radius := by decide +kernel
theorem polyval1_pos : 0<(polyval1).center-(polyval1).radius := by decide +kernel
def cell2 : Box := ⟨812500000000000000000000000000000000000000000000000000000000,62500000000000000000000000000000000000000000000000000000002⟩
def resval2 : Box := ⟨107292865080403209161295926372476293627683047684773927435,312816856043789105360643686006508807856053980424656950⟩
def polyval2 : Box := ⟨3719554461364794646782162988628815741496807400604421613786,8980712990729488349637733425044258935636237839530407723⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-143990812156154290288059301597304117205017946832721,33808271575714978616170145609809916502600350234411773⟩
def resval2Tail8 : Box := ⟨-444440420895525030673953312863265940275486954547061,57559893649773438119091874242305382989408700410041013⟩
def resval2Tail12 : Box := ⟨-1019824428776170826959334599426742928698073239576074,97933017742875025603553166286755048868733635172594312⟩
def resval2Tail16 : Box := ⟨-2340086623707916887728003330299268229153167257929494,166469093531528700779705183818203802282866307304123488⟩
def resval2Tail20 : Box := ⟨-5369556982332206199255599729878184664371671960239325,282611451729001279410420925366246556408307976267669336⟩
def resval2Tail24 : Box := ⟨-12320972178639980594563967005170335411705846958548506,478961914819120409566317037507940982884208383075294512⟩
def resval2Tail28 : Box := ⟨-28271672304868534824068950897493690722119078439249631,809835243623005926928188764086712858829291771166086932⟩
def resval2Tail32 : Box := ⟨-64872109385941120362066163436389797678060729382615305,1364901288215297445779131782850277218251050657338063352⟩
def resval2Tail36 : Box := ⟨-148855381839467710236928732707078731394131849842502181,2290274912444027986222752326057096570240080589993975710⟩
def resval2Tail40 : Box := ⟨-341563191212890160026452300757853114694544599036218259,3819485407448167054729947540075648667988827104845136082⟩
def resval2Tail44 : Box := ⟨-783750054246278825083271924219405156336812610634111961,6314815151966003703355127342851946907008284602810271241⟩
def resval2Tail48 : Box := ⟨-1798390937119993312450939309969053928044861647429375119,10311447915293796453029776716747181469529018415543798098⟩
def resval2Tail52 : Box := ⟨-4126583398868942938413728900888732163690789951418816556,16532267054894856576356189338592386644747261352477781897⟩
def resval2Tail56 : Box := ⟨-9468848066533904617762687458242288031746484522279344713,25774238755047313460416620441202232956124421362022634940⟩
def resval2Tail60 : Box := ⟨-21727195367399984299133410475269813681734189746786135205,38395954828848122058185115176204666050347976526169470243⟩
def resval2Tail64 : Box := ⟨-49855168779670637346559995171955864611482528379550323053,52712271119004570961544686375005531734975065087777605972⟩
def resval2Tail68 : Box := ⟨-114397496672586132291892560822820883995144333714001077916,60577976921681896718423482405195083252502049098167643878⟩
def resval2Tail72 : Box := ⟨742317945371645265764285537639315666836877812375724784259,1292476312528372688294368173711670783118563048035873488⟩
def resval2Tail76 : Box := ⟨-24998151500058740370131382166815244135215626992803,390507257309742180475972284333463396468412397215024⟩
def resval2Tail80 : Box := ⟨-4759714402619527380395638835880907895158870897954,664734194855690420177391595436134656648916422220543⟩
def resval2Tail84 : Box := ⟨-10919048381338789306222735455205361675779403016792,1131206063659606218640183118536236999168662115291982⟩
def resval2Tail88 : Box := ⟨-25054820100213086530756836071465996716925525293971,1923360197189551994637738028662461924154006342012238⟩
def resval2Tail92 : Box := ⟨-57490728265568907802933354885071441505730718200722,3266419272072958913804102384928836541941556657545264⟩
def resval2Tail96 : Box := ⟨-131918082966684563440298247214598094318582738282265,5538525632729506618864113368894567039918618487461644⟩
def resval2Tail100 : Box := ⟨-302698907086748259252619207185690150717623377673368,9370827731601963775877204522911578788430569422720867⟩
def resval2Tail104 : Box := ⟨-694572163959144719940790630677788021736625653928570,15808037212162872935002846986310289223286844369617904⟩
def resval2Tail108 : Box := ⟨-1593763570506162533184409654356844210867219758727635,26558959463477920888977131849097362176725186693730814⟩
def resval2Tail112 : Box := ⟨-3657045949255693697668744518291754187623849011582276,44370256652659677269109665842777279181566367069877253⟩
def resval2Tail116 : Box := ⟨-8391448595302025216148840586963899710848781895599243,73541009321168345246219963627054576540997100479676500⟩
def resval2Tail120 : Box := ⟨-19254997203939411274678050603631994118641021043586229,120518158825157897123510242861031978983642314838469392⟩
def resval2Tail124 : Box := ⟨-44182468987688571050816757187357797651420126753790100,194264364454703172602656245816962603458476231662332319⟩
def resval2Tail128 : Box := ⟨-101380984124405987589660288706416218810228827170717099,305398786712760469320576712287434317785959964784935417⟩
def resval2Tail132 : Box := ⟨-232628555567988239917874092232857757728824069403336572,461319774856439166710791231957589393712343274735351968⟩
def resval2Tail136 : Box := ⟨-533788908579091023608901542373208777493006012188020059,650056306512188786636977663418789000043261574604207947⟩
def resval2Tail140 : Box := ⟨-1224830775572245995990534243041639233126632993170300662,794756952575608221289028352020891932685833118524973767⟩
def resval2Tail144 : Box := ⟨-2851441479457533069964314439282069736255247148414688438,629770147550932231580368751245631528326618646611978477⟩
def resval2Tail148 : Box := ⟨49298029612737921744184498655538306399342803,38587863562464968607729301254575358981537466⟩
def resval2Tail152 : Box := ⟨487889183198954879287658946563131176320230,64625549514231635772940569661928788988845966⟩
def resval2Tail156 : Box := ⟨1117690138147361318166137460330932746224980,109961593058606963369561978213297115109984203⟩
def resval2Tail160 : Box := ⟨2564648503038733653864342741785003509817100,186931704274693436377856134172146276615487971⟩
def resval2Tail164 : Box := ⟨5884836114679089776671602916885428988477347,317387575787055289273677751839039908294613086⟩
def resval2Tail168 : Box := ⟨13503330401998030187804661913899648096115021,537985132384130555761916082709930126869337729⟩
def resval2Tail172 : Box := ⟨30984708561511860673007968358015264051799469,909830261689209719178959445139546664245265441⟩
def resval2Tail176 : Box := ⟨71097435674074478081322232335840515245444183,1533891368218868288324561900434236709953653539⟩
def resval2Tail180 : Box := ⟨163140000151820488762496168104077792930560315,2574900041807985246381996237709104023491394043⟩
def resval2Tail184 : Box := ⟨374340641082234779858988601343550480026274899,4296634790765896953107421909120698603595678442⟩
def resval2Tail188 : Box := ⟨858961109693825094777791090893955381142451887,7109516761547302592904854891237782264458980559⟩
def resval2Tail192 : Box := ⟨1970970039035556227718236977376853062768682152,11622901414776879844411743604085609404809405409⟩
def resval2Tail196 : Box := ⟨4522582979525724347934038485229028010250833052,18667961574749885048722574449721497928760548840⟩
def resval2Tail200 : Box := ⟨10377507725436710093673946762134647855999257460,29184537461699023552999331570846077831786943439⟩
def resval2Tail204 : Box := ⟨23812203574602461596448951395528079573743723697,43678898918736984451873367949042364614891929737⟩
def resval2Tail208 : Box := ⟨54639423460853378694953693441699360488016067492,60497417777271592054697567989379626620482740540⟩
def resval2Tail212 : Box := ⟨125375486035947251624139527766847992428877382904,71042882045624483969735844628013117151095850791⟩
def resval2Tail216 : Box := ⟨287687474848644247133342260345780041000579171467,47394613782543683027263151476776890198213513607⟩
theorem resval2H216 : resval2Tail216=hornerBox Q residualBox cell2 216 4 :=
  hornerChunk_step Q residualBox cell2 resval2Tail216 zero 216 4 0 (by decide +kernel) rfl
theorem resval2H212 : resval2Tail212=hornerBox Q residualBox cell2 212 8 :=
  hornerChunk_step Q residualBox cell2 resval2Tail212 resval2Tail216 212 4 4 (by decide +kernel) resval2H216
theorem resval2H208 : resval2Tail208=hornerBox Q residualBox cell2 208 12 :=
  hornerChunk_step Q residualBox cell2 resval2Tail208 resval2Tail212 208 4 8 (by decide +kernel) resval2H212
theorem resval2H204 : resval2Tail204=hornerBox Q residualBox cell2 204 16 :=
  hornerChunk_step Q residualBox cell2 resval2Tail204 resval2Tail208 204 4 12 (by decide +kernel) resval2H208
theorem resval2H200 : resval2Tail200=hornerBox Q residualBox cell2 200 20 :=
  hornerChunk_step Q residualBox cell2 resval2Tail200 resval2Tail204 200 4 16 (by decide +kernel) resval2H204
theorem resval2H196 : resval2Tail196=hornerBox Q residualBox cell2 196 24 :=
  hornerChunk_step Q residualBox cell2 resval2Tail196 resval2Tail200 196 4 20 (by decide +kernel) resval2H200
theorem resval2H192 : resval2Tail192=hornerBox Q residualBox cell2 192 28 :=
  hornerChunk_step Q residualBox cell2 resval2Tail192 resval2Tail196 192 4 24 (by decide +kernel) resval2H196
theorem resval2H188 : resval2Tail188=hornerBox Q residualBox cell2 188 32 :=
  hornerChunk_step Q residualBox cell2 resval2Tail188 resval2Tail192 188 4 28 (by decide +kernel) resval2H192
theorem resval2H184 : resval2Tail184=hornerBox Q residualBox cell2 184 36 :=
  hornerChunk_step Q residualBox cell2 resval2Tail184 resval2Tail188 184 4 32 (by decide +kernel) resval2H188
theorem resval2H180 : resval2Tail180=hornerBox Q residualBox cell2 180 40 :=
  hornerChunk_step Q residualBox cell2 resval2Tail180 resval2Tail184 180 4 36 (by decide +kernel) resval2H184
theorem resval2H176 : resval2Tail176=hornerBox Q residualBox cell2 176 44 :=
  hornerChunk_step Q residualBox cell2 resval2Tail176 resval2Tail180 176 4 40 (by decide +kernel) resval2H180
theorem resval2H172 : resval2Tail172=hornerBox Q residualBox cell2 172 48 :=
  hornerChunk_step Q residualBox cell2 resval2Tail172 resval2Tail176 172 4 44 (by decide +kernel) resval2H176
theorem resval2H168 : resval2Tail168=hornerBox Q residualBox cell2 168 52 :=
  hornerChunk_step Q residualBox cell2 resval2Tail168 resval2Tail172 168 4 48 (by decide +kernel) resval2H172
theorem resval2H164 : resval2Tail164=hornerBox Q residualBox cell2 164 56 :=
  hornerChunk_step Q residualBox cell2 resval2Tail164 resval2Tail168 164 4 52 (by decide +kernel) resval2H168
theorem resval2H160 : resval2Tail160=hornerBox Q residualBox cell2 160 60 :=
  hornerChunk_step Q residualBox cell2 resval2Tail160 resval2Tail164 160 4 56 (by decide +kernel) resval2H164
theorem resval2H156 : resval2Tail156=hornerBox Q residualBox cell2 156 64 :=
  hornerChunk_step Q residualBox cell2 resval2Tail156 resval2Tail160 156 4 60 (by decide +kernel) resval2H160
theorem resval2H152 : resval2Tail152=hornerBox Q residualBox cell2 152 68 :=
  hornerChunk_step Q residualBox cell2 resval2Tail152 resval2Tail156 152 4 64 (by decide +kernel) resval2H156
theorem resval2H148 : resval2Tail148=hornerBox Q residualBox cell2 148 72 :=
  hornerChunk_step Q residualBox cell2 resval2Tail148 resval2Tail152 148 4 68 (by decide +kernel) resval2H152
theorem resval2H144 : resval2Tail144=hornerBox Q residualBox cell2 144 76 :=
  hornerChunk_step Q residualBox cell2 resval2Tail144 resval2Tail148 144 4 72 (by decide +kernel) resval2H148
theorem resval2H140 : resval2Tail140=hornerBox Q residualBox cell2 140 80 :=
  hornerChunk_step Q residualBox cell2 resval2Tail140 resval2Tail144 140 4 76 (by decide +kernel) resval2H144
theorem resval2H136 : resval2Tail136=hornerBox Q residualBox cell2 136 84 :=
  hornerChunk_step Q residualBox cell2 resval2Tail136 resval2Tail140 136 4 80 (by decide +kernel) resval2H140
theorem resval2H132 : resval2Tail132=hornerBox Q residualBox cell2 132 88 :=
  hornerChunk_step Q residualBox cell2 resval2Tail132 resval2Tail136 132 4 84 (by decide +kernel) resval2H136
theorem resval2H128 : resval2Tail128=hornerBox Q residualBox cell2 128 92 :=
  hornerChunk_step Q residualBox cell2 resval2Tail128 resval2Tail132 128 4 88 (by decide +kernel) resval2H132
theorem resval2H124 : resval2Tail124=hornerBox Q residualBox cell2 124 96 :=
  hornerChunk_step Q residualBox cell2 resval2Tail124 resval2Tail128 124 4 92 (by decide +kernel) resval2H128
theorem resval2H120 : resval2Tail120=hornerBox Q residualBox cell2 120 100 :=
  hornerChunk_step Q residualBox cell2 resval2Tail120 resval2Tail124 120 4 96 (by decide +kernel) resval2H124
theorem resval2H116 : resval2Tail116=hornerBox Q residualBox cell2 116 104 :=
  hornerChunk_step Q residualBox cell2 resval2Tail116 resval2Tail120 116 4 100 (by decide +kernel) resval2H120
theorem resval2H112 : resval2Tail112=hornerBox Q residualBox cell2 112 108 :=
  hornerChunk_step Q residualBox cell2 resval2Tail112 resval2Tail116 112 4 104 (by decide +kernel) resval2H116
theorem resval2H108 : resval2Tail108=hornerBox Q residualBox cell2 108 112 :=
  hornerChunk_step Q residualBox cell2 resval2Tail108 resval2Tail112 108 4 108 (by decide +kernel) resval2H112
theorem resval2H104 : resval2Tail104=hornerBox Q residualBox cell2 104 116 :=
  hornerChunk_step Q residualBox cell2 resval2Tail104 resval2Tail108 104 4 112 (by decide +kernel) resval2H108
theorem resval2H100 : resval2Tail100=hornerBox Q residualBox cell2 100 120 :=
  hornerChunk_step Q residualBox cell2 resval2Tail100 resval2Tail104 100 4 116 (by decide +kernel) resval2H104
theorem resval2H96 : resval2Tail96=hornerBox Q residualBox cell2 96 124 :=
  hornerChunk_step Q residualBox cell2 resval2Tail96 resval2Tail100 96 4 120 (by decide +kernel) resval2H100
theorem resval2H92 : resval2Tail92=hornerBox Q residualBox cell2 92 128 :=
  hornerChunk_step Q residualBox cell2 resval2Tail92 resval2Tail96 92 4 124 (by decide +kernel) resval2H96
theorem resval2H88 : resval2Tail88=hornerBox Q residualBox cell2 88 132 :=
  hornerChunk_step Q residualBox cell2 resval2Tail88 resval2Tail92 88 4 128 (by decide +kernel) resval2H92
theorem resval2H84 : resval2Tail84=hornerBox Q residualBox cell2 84 136 :=
  hornerChunk_step Q residualBox cell2 resval2Tail84 resval2Tail88 84 4 132 (by decide +kernel) resval2H88
theorem resval2H80 : resval2Tail80=hornerBox Q residualBox cell2 80 140 :=
  hornerChunk_step Q residualBox cell2 resval2Tail80 resval2Tail84 80 4 136 (by decide +kernel) resval2H84
theorem resval2H76 : resval2Tail76=hornerBox Q residualBox cell2 76 144 :=
  hornerChunk_step Q residualBox cell2 resval2Tail76 resval2Tail80 76 4 140 (by decide +kernel) resval2H80
theorem resval2H72 : resval2Tail72=hornerBox Q residualBox cell2 72 148 :=
  hornerChunk_step Q residualBox cell2 resval2Tail72 resval2Tail76 72 4 144 (by decide +kernel) resval2H76
theorem resval2H68 : resval2Tail68=hornerBox Q residualBox cell2 68 152 :=
  hornerChunk_step Q residualBox cell2 resval2Tail68 resval2Tail72 68 4 148 (by decide +kernel) resval2H72
theorem resval2H64 : resval2Tail64=hornerBox Q residualBox cell2 64 156 :=
  hornerChunk_step Q residualBox cell2 resval2Tail64 resval2Tail68 64 4 152 (by decide +kernel) resval2H68
theorem resval2H60 : resval2Tail60=hornerBox Q residualBox cell2 60 160 :=
  hornerChunk_step Q residualBox cell2 resval2Tail60 resval2Tail64 60 4 156 (by decide +kernel) resval2H64
theorem resval2H56 : resval2Tail56=hornerBox Q residualBox cell2 56 164 :=
  hornerChunk_step Q residualBox cell2 resval2Tail56 resval2Tail60 56 4 160 (by decide +kernel) resval2H60
theorem resval2H52 : resval2Tail52=hornerBox Q residualBox cell2 52 168 :=
  hornerChunk_step Q residualBox cell2 resval2Tail52 resval2Tail56 52 4 164 (by decide +kernel) resval2H56
theorem resval2H48 : resval2Tail48=hornerBox Q residualBox cell2 48 172 :=
  hornerChunk_step Q residualBox cell2 resval2Tail48 resval2Tail52 48 4 168 (by decide +kernel) resval2H52
theorem resval2H44 : resval2Tail44=hornerBox Q residualBox cell2 44 176 :=
  hornerChunk_step Q residualBox cell2 resval2Tail44 resval2Tail48 44 4 172 (by decide +kernel) resval2H48
theorem resval2H40 : resval2Tail40=hornerBox Q residualBox cell2 40 180 :=
  hornerChunk_step Q residualBox cell2 resval2Tail40 resval2Tail44 40 4 176 (by decide +kernel) resval2H44
theorem resval2H36 : resval2Tail36=hornerBox Q residualBox cell2 36 184 :=
  hornerChunk_step Q residualBox cell2 resval2Tail36 resval2Tail40 36 4 180 (by decide +kernel) resval2H40
theorem resval2H32 : resval2Tail32=hornerBox Q residualBox cell2 32 188 :=
  hornerChunk_step Q residualBox cell2 resval2Tail32 resval2Tail36 32 4 184 (by decide +kernel) resval2H36
theorem resval2H28 : resval2Tail28=hornerBox Q residualBox cell2 28 192 :=
  hornerChunk_step Q residualBox cell2 resval2Tail28 resval2Tail32 28 4 188 (by decide +kernel) resval2H32
theorem resval2H24 : resval2Tail24=hornerBox Q residualBox cell2 24 196 :=
  hornerChunk_step Q residualBox cell2 resval2Tail24 resval2Tail28 24 4 192 (by decide +kernel) resval2H28
theorem resval2H20 : resval2Tail20=hornerBox Q residualBox cell2 20 200 :=
  hornerChunk_step Q residualBox cell2 resval2Tail20 resval2Tail24 20 4 196 (by decide +kernel) resval2H24
theorem resval2H16 : resval2Tail16=hornerBox Q residualBox cell2 16 204 :=
  hornerChunk_step Q residualBox cell2 resval2Tail16 resval2Tail20 16 4 200 (by decide +kernel) resval2H20
theorem resval2H12 : resval2Tail12=hornerBox Q residualBox cell2 12 208 :=
  hornerChunk_step Q residualBox cell2 resval2Tail12 resval2Tail16 12 4 204 (by decide +kernel) resval2H16
theorem resval2H8 : resval2Tail8=hornerBox Q residualBox cell2 8 212 :=
  hornerChunk_step Q residualBox cell2 resval2Tail8 resval2Tail12 8 4 208 (by decide +kernel) resval2H12
theorem resval2H4 : resval2Tail4=hornerBox Q residualBox cell2 4 216 :=
  hornerChunk_step Q residualBox cell2 resval2Tail4 resval2Tail8 4 4 212 (by decide +kernel) resval2H8
theorem resval2H0 : resval2=hornerBox Q residualBox cell2 0 220 :=
  hornerChunk_step Q residualBox cell2 resval2 resval2Tail4 0 4 216 (by decide +kernel) resval2H4
theorem resval2_eq : resval2=hornerBox Q residualBox cell2 0 220 := resval2H0
def polyval2Tail5 : Box := ⟨21368083684356480675747279897638675754173831765287406,2992151054908256508523973315406535761857725740826651679⟩
def polyval2Tail9 : Box := ⟨44759704883340591497575855154247626562184424283322745,5092983952962359528002117651476595040154318300774454490⟩
def polyval2Tail13 : Box := ⟨102705131928586166524987498692176452787184659302941464,8662058443519073267302050900346793118028722397120808304⟩
def polyval2Tail17 : Box := ⟨235666941577489858752013555967569285926087805916990573,14716632768770786618876415945070865466743907514063318449⟩
def polyval2Tail21 : Box := ⟨540760781597213868789463215859824561372658186744888911,24967202406068334342944652334449572612945470460096096244⟩
def polyval2Tail25 : Box := ⟨1240828352745168121810837179569423627624674562760020860,42274630712926663839606823990899158361147565216005484863⟩
def polyval2Tail29 : Box := ⟨2847201671002672524814981641335399796071918659294452739,71388250362729865244289665726893067764100620709318678054⟩
def polyval2Tail33 : Box := ⟨6533181916278531772482895162313736997614586510547100284,120109221886373894158192152427570691703575161492442942069⟩
def polyval2Tail37 : Box := ⟨14991023075705677606833684841515902725980047516298582333,201055326768386091074595946695595424438556813092977278462⟩
def polyval2Tail41 : Box := ⟨34398364493170662358003681842301593083706781946857255756,334167170267928831401434831956647041022389349798907045425⟩
def polyval2Tail45 : Box := ⟨78930402136635010269823745488342202845412522969625831137,549826128634486824981866978434846708952066032610223301169⟩
def polyval2Tail49 : Box := ⟨181113505634484508020669916782595401963168571252327167673,891517377346987810689500898491668650591034345033054456361⟩
def polyval2Tail53 : Box := ⟨415582602334007098174709497053707014754159441512906759149,1414278329232886120608065697257797205498466731121927459716⟩
def polyval2Tail57 : Box := ⟨953594812036045307058416869808051344242954579258470103243,2168067152019762556111853809757298604596222949903455194748⟩
def polyval2Tail61 : Box := ⟨2188116298504759510786952595767444025320307652781126982246,3137301196194366133056473556896808197592809262558532819107⟩
def polyval2Tail65 : Box := ⟨5020846249745186481994086862156214075885622810546639253450,4064080888238650386600858365308745192122828631442451327392⟩
def polyval2Tail69 : Box := ⟨11520821442433018847014668103009440463052288170716320043179,3977663213010592911489837266574691148333968715865582002395⟩
def polyval2Tail73 : Box := ⟨26468750000000000000000000000000000000000000000000000000000,2⟩
theorem polyval2H73 : polyval2Tail73=hornerBox Q polyBox cell2 73 1 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail73 zero 73 1 0 (by decide +kernel) rfl
theorem polyval2H69 : polyval2Tail69=hornerBox Q polyBox cell2 69 5 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail69 polyval2Tail73 69 4 1 (by decide +kernel) polyval2H73
theorem polyval2H65 : polyval2Tail65=hornerBox Q polyBox cell2 65 9 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail65 polyval2Tail69 65 4 5 (by decide +kernel) polyval2H69
theorem polyval2H61 : polyval2Tail61=hornerBox Q polyBox cell2 61 13 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail61 polyval2Tail65 61 4 9 (by decide +kernel) polyval2H65
theorem polyval2H57 : polyval2Tail57=hornerBox Q polyBox cell2 57 17 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail57 polyval2Tail61 57 4 13 (by decide +kernel) polyval2H61
theorem polyval2H53 : polyval2Tail53=hornerBox Q polyBox cell2 53 21 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail53 polyval2Tail57 53 4 17 (by decide +kernel) polyval2H57
theorem polyval2H49 : polyval2Tail49=hornerBox Q polyBox cell2 49 25 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail49 polyval2Tail53 49 4 21 (by decide +kernel) polyval2H53
theorem polyval2H45 : polyval2Tail45=hornerBox Q polyBox cell2 45 29 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail45 polyval2Tail49 45 4 25 (by decide +kernel) polyval2H49
theorem polyval2H41 : polyval2Tail41=hornerBox Q polyBox cell2 41 33 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail41 polyval2Tail45 41 4 29 (by decide +kernel) polyval2H45
theorem polyval2H37 : polyval2Tail37=hornerBox Q polyBox cell2 37 37 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail37 polyval2Tail41 37 4 33 (by decide +kernel) polyval2H41
theorem polyval2H33 : polyval2Tail33=hornerBox Q polyBox cell2 33 41 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail33 polyval2Tail37 33 4 37 (by decide +kernel) polyval2H37
theorem polyval2H29 : polyval2Tail29=hornerBox Q polyBox cell2 29 45 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail29 polyval2Tail33 29 4 41 (by decide +kernel) polyval2H33
theorem polyval2H25 : polyval2Tail25=hornerBox Q polyBox cell2 25 49 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail25 polyval2Tail29 25 4 45 (by decide +kernel) polyval2H29
theorem polyval2H21 : polyval2Tail21=hornerBox Q polyBox cell2 21 53 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail21 polyval2Tail25 21 4 49 (by decide +kernel) polyval2H25
theorem polyval2H17 : polyval2Tail17=hornerBox Q polyBox cell2 17 57 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail17 polyval2Tail21 17 4 53 (by decide +kernel) polyval2H21
theorem polyval2H13 : polyval2Tail13=hornerBox Q polyBox cell2 13 61 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail13 polyval2Tail17 13 4 57 (by decide +kernel) polyval2H17
theorem polyval2H9 : polyval2Tail9=hornerBox Q polyBox cell2 9 65 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail9 polyval2Tail13 9 4 61 (by decide +kernel) polyval2H13
theorem polyval2H5 : polyval2Tail5=hornerBox Q polyBox cell2 5 69 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail5 polyval2Tail9 5 4 65 (by decide +kernel) polyval2H9
theorem polyval2H1 : polyval2=hornerBox Q polyBox cell2 1 73 :=
  hornerChunk_step Q polyBox cell2 polyval2 polyval2Tail5 1 4 69 (by decide +kernel) polyval2H5
theorem polyval2_eq : polyval2=hornerBox Q polyBox cell2 1 73 := polyval2H1
theorem polyval2_upper : 5*(polyval2.center+polyval2.radius)<Q := by decide +kernel
theorem resval2_pos : 0<(resval2).center-(resval2).radius := by decide +kernel
theorem polyval2_pos : 0<(polyval2).center-(polyval2).radius := by decide +kernel
def cell3 : Box := ⟨906250000000000000000000000000000000000000000000000000000000,31250000000000000000000000000000000000000000000000000000002⟩
def resval3 : Box := ⟨107109492974055572668640919292317231725641315961390451269,1859674127235922865144088589263011987896889737542591571⟩
def polyval3 : Box := ⟨3737297346712383722764564540547539455239194064289159499169,235768619697228274795761398478842813855473859273655322858⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-195776734413572385009918691912932438414994161185528079,2027308021782444024459747448783318029000460588551832032⟩
def resval3Tail8 : Box := ⟨-290321013102638796766168596940838244065584513935990762,2587610174409712314070480957093328491420075046251218867⟩
def resval3Tail12 : Box := ⟨-430414011256585413083827615927795542595720991111956021,3295178060824063043296792234228976245071713440490357692⟩
def resval3Tail16 : Box := ⟨-638108195005986705734373463096830172374389651782954428,4184813326695860220513031722366443535617726661880193001⟩
def resval3Tail20 : Box := ⟨-946024195032263250925734119529584755564271406398323081,5297432295757923840229313364996944628145005232523599021⟩
def resval3Tail24 : Box := ⟨-1402523560409724948890702911534422472121329237079460180,6679869814018437277231819993060685638998564212441693504⟩
def resval3Tail28 : Box := ⟨-2079304470048237906698135374220580109423837919392812718,8383663079315199920949612787694407976433290313213278744⟩
def resval3Tail32 : Box := ⟨-3082662709708448426916139045518626207236957021526214217,10462049217503053034831318349740626601713413369235488366⟩
def resval3Tail36 : Box := ⟨-4570186578594994094005943462266245326366551905586498742,12963961389044175482293793777211727902935107293760589009⟩
def resval3Tail40 : Box := ⟨-6775507841772682324454238844118936506172638526197203569,15923117762320169376276976551185719357391249951750274331⟩
def resval3Tail44 : Box := ⟨-10044996134060765298200177235040544121214127687875255524,19339243423269192806291086899662027899576764886370746506⟩
def resval3Tail48 : Box := ⟨-14892160069716139739576171304891472616331645610757333302,23146862619255240687845325780397798826867036365236758531⟩
def resval3Tail52 : Box := ⟨-22078299342499898745910333892392826368802458253399521788,27164671342822143382689184822739582911498694122661295760⟩
def resval3Tail56 : Box := ⟨-32732075103616765236156715740107944599963809068894183024,31014835056052666650038780020507972789482569393075371515⟩
def resval3Tail60 : Box := ⟨-48526778442866133144900960402400015063084453974362372539,33996036455385662778412309902682304931173908606995324940⟩
def resval3Tail64 : Box := ⟨-71943138908954446777155994922058752324606869076608570828,34885803254618256087094376999195255426335881219364695616⟩
def resval3Tail68 : Box := ⟨-106658904515563049266363109033602326679796306428086129807,31635202135526837378402226964740440421243564397284682487⟩
def resval3Tail72 : Box := ⟨742972061917709361975415792041768673140551731689508160525,1093355353305298194976123269869702754549736525913765210⟩
def resval3Tail76 : Box := ⟨-2360844065358547196273643861978715624660043648465251,25143841979654130483448101793399723903005014468908377⟩
def resval3Tail80 : Box := ⟨-3466254016439060744445475077572802680083563259216005,32109865936645199813643668271724473149273711902568859⟩
def resval3Tail84 : Box := ⟨-5138876351599396415183789238326084029230328306044110,40915771020554868701138468973040328451055802830808457⟩
def resval3Tail88 : Box := ⟨-7618616092697206415878629987559796190189380174889899,52000887515073090208206400359326961307197538624253071⟩
def resval3Tail92 : Box := ⟨-11294942163036453084439168400471490497070045604618219,65884786991308995081497872456761022500362348617973631⟩
def resval3Tail96 : Box := ⟨-16745261464040598747254372432771747059846807423400506,83166851718363004777268329364924987756798978749283628⟩
def resval3Tail100 : Box := ⟨-24825605784571951641638872909379557681232299442818985,104514448526973777493123665140421472448303830700587484⟩
def resval3Tail104 : Box := ⟨-36805080881804146783942229563870037602929751116102647,130630569475953105620026946467266210209871801217077389⟩
def resval3Tail108 : Box := ⟨-54565193311737011194591252102359189143196959656967343,162186664107442826697442499263334245771443662057514740⟩
def resval3Tail112 : Box := ⟨-80895361450467279977550584471599469100649307417832095,199698213420117803598187991243789422653740849927622474⟩
def resval3Tail116 : Box := ⟨-119931023918760971341950439950358747163384381813133702,243308097517657083715492681667573290386715966208447220⟩
def resval3Tail120 : Box := ⟨-177803155092019585297895825027454820730942294519559734,292423789351577326453873974110757197714093102141386119⟩
def resval3Tail124 : Box := ⟨-263601201154519249306487470707177073270141383569150408,345125574767566029436867127728786880446119707517492833⟩
def resval3Tail128 : Box := ⟨-390800676254276878185747001833066564251079952797054233,397219432127545985723277378330396540839493376980593393⟩
def resval3Tail132 : Box := ⟨-579379638225839713507810791224895598531239843883214901,440742550868707908479177828029975474448487039480387144⟩
def resval3Tail136 : Box := ⟨-858956459366717792823450902471802180281742624928128741,461630756135772566119793150738075894626113295172473501⟩
def resval3Tail140 : Box := ⟨-1273441772374639839995152755677873283062691101024826399,436108971633359395489820077877041568978049584297792792⟩
def resval3Tail144 : Box := ⟨-1924724000578950570804852918359974600116036710177506126,321894861941013628860118457637312146090148316420518446⟩
def resval3Tail148 : Box := ⟨492525132518270537888881512010108778287162990,4335977715781801233238265089011286882844479570⟩
def resval3Tail152 : Box := ⟨657678770076072880770134488174685697626977277,5529065053180950901366836174289236509461342380⟩
def resval3Tail156 : Box := ⟨975037291098807545575944707658568780111292798,7033938332234977898069073525986355450058041777⟩
def resval3Tail160 : Box := ⟨1445536784269153242278936414861961780412490360,8922388676188423705909251634466068064434831634⟩
def resval3Tail164 : Box := ⟨2143073515478909460897328849031541658742444007,11278602790230199318457721045927062270031339765⟩
def resval3Tail168 : Box := ⟨3177203197267862054704564736251165333286039377,14197670449565757834466186794097446815117044681⟩
def resval3Tail172 : Box := ⟨4710347117734458696269041506639753964633983370,17782091782391726199021647973549490717721466054⟩
def resval3Tail176 : Box := ⟨6983302166077595411042590258589808355470540752,22134020811871434774834053911254475248194456221⟩
def resval3Tail180 : Box := ⟨10353060596986177609048355697533616483884490784,27340428364650714089616943356908381438509364021⟩
def resval3Tail184 : Box := ⟨15348879538041285108098860892784027826508987101,33446784513115956064438023151746990994921541593⟩
def resval3Tail188 : Box := ⟨22755406564690948256106345338038545255102731955,40412448037909366953433009661425178317768601237⟩
def resval3Tail192 : Box := ⟨33735917116361638102625109080241327848044816283,48037288201880618837316755783777401224900198751⟩
def resval3Tail196 : Box := ⟨50015019527183709217620173233769524201147123616,55843524349089368333661407237807691463313578661⟩
def resval3Tail200 : Box := ⟨74149523478979620858860841694316127721565219385,62888412945226451607830818787313268357585428867⟩
def resval3Tail204 : Box := ⟨109930014706311282759484513818883087638529219500,67470838656587879237083535591871274208320382494⟩
def resval3Tail208 : Box := ⟨162976207618600749876713068001822697180822432573,66675986475055620548970626365804588572450716302⟩
def resval3Tail212 : Box := ⟨241619582452482724757758643061920382656373211005,55673971980408539798821870882922632201536267364⟩
def resval3Tail216 : Box := ⟨358213011432861063856442313608054740523048237127,26645832407501503671552543447315594553060795131⟩
theorem resval3H216 : resval3Tail216=hornerBox Q residualBox cell3 216 4 :=
  hornerChunk_step Q residualBox cell3 resval3Tail216 zero 216 4 0 (by decide +kernel) rfl
theorem resval3H212 : resval3Tail212=hornerBox Q residualBox cell3 212 8 :=
  hornerChunk_step Q residualBox cell3 resval3Tail212 resval3Tail216 212 4 4 (by decide +kernel) resval3H216
theorem resval3H208 : resval3Tail208=hornerBox Q residualBox cell3 208 12 :=
  hornerChunk_step Q residualBox cell3 resval3Tail208 resval3Tail212 208 4 8 (by decide +kernel) resval3H212
theorem resval3H204 : resval3Tail204=hornerBox Q residualBox cell3 204 16 :=
  hornerChunk_step Q residualBox cell3 resval3Tail204 resval3Tail208 204 4 12 (by decide +kernel) resval3H208
theorem resval3H200 : resval3Tail200=hornerBox Q residualBox cell3 200 20 :=
  hornerChunk_step Q residualBox cell3 resval3Tail200 resval3Tail204 200 4 16 (by decide +kernel) resval3H204
theorem resval3H196 : resval3Tail196=hornerBox Q residualBox cell3 196 24 :=
  hornerChunk_step Q residualBox cell3 resval3Tail196 resval3Tail200 196 4 20 (by decide +kernel) resval3H200
theorem resval3H192 : resval3Tail192=hornerBox Q residualBox cell3 192 28 :=
  hornerChunk_step Q residualBox cell3 resval3Tail192 resval3Tail196 192 4 24 (by decide +kernel) resval3H196
theorem resval3H188 : resval3Tail188=hornerBox Q residualBox cell3 188 32 :=
  hornerChunk_step Q residualBox cell3 resval3Tail188 resval3Tail192 188 4 28 (by decide +kernel) resval3H192
theorem resval3H184 : resval3Tail184=hornerBox Q residualBox cell3 184 36 :=
  hornerChunk_step Q residualBox cell3 resval3Tail184 resval3Tail188 184 4 32 (by decide +kernel) resval3H188
theorem resval3H180 : resval3Tail180=hornerBox Q residualBox cell3 180 40 :=
  hornerChunk_step Q residualBox cell3 resval3Tail180 resval3Tail184 180 4 36 (by decide +kernel) resval3H184
theorem resval3H176 : resval3Tail176=hornerBox Q residualBox cell3 176 44 :=
  hornerChunk_step Q residualBox cell3 resval3Tail176 resval3Tail180 176 4 40 (by decide +kernel) resval3H180
theorem resval3H172 : resval3Tail172=hornerBox Q residualBox cell3 172 48 :=
  hornerChunk_step Q residualBox cell3 resval3Tail172 resval3Tail176 172 4 44 (by decide +kernel) resval3H176
theorem resval3H168 : resval3Tail168=hornerBox Q residualBox cell3 168 52 :=
  hornerChunk_step Q residualBox cell3 resval3Tail168 resval3Tail172 168 4 48 (by decide +kernel) resval3H172
theorem resval3H164 : resval3Tail164=hornerBox Q residualBox cell3 164 56 :=
  hornerChunk_step Q residualBox cell3 resval3Tail164 resval3Tail168 164 4 52 (by decide +kernel) resval3H168
theorem resval3H160 : resval3Tail160=hornerBox Q residualBox cell3 160 60 :=
  hornerChunk_step Q residualBox cell3 resval3Tail160 resval3Tail164 160 4 56 (by decide +kernel) resval3H164
theorem resval3H156 : resval3Tail156=hornerBox Q residualBox cell3 156 64 :=
  hornerChunk_step Q residualBox cell3 resval3Tail156 resval3Tail160 156 4 60 (by decide +kernel) resval3H160
theorem resval3H152 : resval3Tail152=hornerBox Q residualBox cell3 152 68 :=
  hornerChunk_step Q residualBox cell3 resval3Tail152 resval3Tail156 152 4 64 (by decide +kernel) resval3H156
theorem resval3H148 : resval3Tail148=hornerBox Q residualBox cell3 148 72 :=
  hornerChunk_step Q residualBox cell3 resval3Tail148 resval3Tail152 148 4 68 (by decide +kernel) resval3H152
theorem resval3H144 : resval3Tail144=hornerBox Q residualBox cell3 144 76 :=
  hornerChunk_step Q residualBox cell3 resval3Tail144 resval3Tail148 144 4 72 (by decide +kernel) resval3H148
theorem resval3H140 : resval3Tail140=hornerBox Q residualBox cell3 140 80 :=
  hornerChunk_step Q residualBox cell3 resval3Tail140 resval3Tail144 140 4 76 (by decide +kernel) resval3H144
theorem resval3H136 : resval3Tail136=hornerBox Q residualBox cell3 136 84 :=
  hornerChunk_step Q residualBox cell3 resval3Tail136 resval3Tail140 136 4 80 (by decide +kernel) resval3H140
theorem resval3H132 : resval3Tail132=hornerBox Q residualBox cell3 132 88 :=
  hornerChunk_step Q residualBox cell3 resval3Tail132 resval3Tail136 132 4 84 (by decide +kernel) resval3H136
theorem resval3H128 : resval3Tail128=hornerBox Q residualBox cell3 128 92 :=
  hornerChunk_step Q residualBox cell3 resval3Tail128 resval3Tail132 128 4 88 (by decide +kernel) resval3H132
theorem resval3H124 : resval3Tail124=hornerBox Q residualBox cell3 124 96 :=
  hornerChunk_step Q residualBox cell3 resval3Tail124 resval3Tail128 124 4 92 (by decide +kernel) resval3H128
theorem resval3H120 : resval3Tail120=hornerBox Q residualBox cell3 120 100 :=
  hornerChunk_step Q residualBox cell3 resval3Tail120 resval3Tail124 120 4 96 (by decide +kernel) resval3H124
theorem resval3H116 : resval3Tail116=hornerBox Q residualBox cell3 116 104 :=
  hornerChunk_step Q residualBox cell3 resval3Tail116 resval3Tail120 116 4 100 (by decide +kernel) resval3H120
theorem resval3H112 : resval3Tail112=hornerBox Q residualBox cell3 112 108 :=
  hornerChunk_step Q residualBox cell3 resval3Tail112 resval3Tail116 112 4 104 (by decide +kernel) resval3H116
theorem resval3H108 : resval3Tail108=hornerBox Q residualBox cell3 108 112 :=
  hornerChunk_step Q residualBox cell3 resval3Tail108 resval3Tail112 108 4 108 (by decide +kernel) resval3H112
theorem resval3H104 : resval3Tail104=hornerBox Q residualBox cell3 104 116 :=
  hornerChunk_step Q residualBox cell3 resval3Tail104 resval3Tail108 104 4 112 (by decide +kernel) resval3H108
theorem resval3H100 : resval3Tail100=hornerBox Q residualBox cell3 100 120 :=
  hornerChunk_step Q residualBox cell3 resval3Tail100 resval3Tail104 100 4 116 (by decide +kernel) resval3H104
theorem resval3H96 : resval3Tail96=hornerBox Q residualBox cell3 96 124 :=
  hornerChunk_step Q residualBox cell3 resval3Tail96 resval3Tail100 96 4 120 (by decide +kernel) resval3H100
theorem resval3H92 : resval3Tail92=hornerBox Q residualBox cell3 92 128 :=
  hornerChunk_step Q residualBox cell3 resval3Tail92 resval3Tail96 92 4 124 (by decide +kernel) resval3H96
theorem resval3H88 : resval3Tail88=hornerBox Q residualBox cell3 88 132 :=
  hornerChunk_step Q residualBox cell3 resval3Tail88 resval3Tail92 88 4 128 (by decide +kernel) resval3H92
theorem resval3H84 : resval3Tail84=hornerBox Q residualBox cell3 84 136 :=
  hornerChunk_step Q residualBox cell3 resval3Tail84 resval3Tail88 84 4 132 (by decide +kernel) resval3H88
theorem resval3H80 : resval3Tail80=hornerBox Q residualBox cell3 80 140 :=
  hornerChunk_step Q residualBox cell3 resval3Tail80 resval3Tail84 80 4 136 (by decide +kernel) resval3H84
theorem resval3H76 : resval3Tail76=hornerBox Q residualBox cell3 76 144 :=
  hornerChunk_step Q residualBox cell3 resval3Tail76 resval3Tail80 76 4 140 (by decide +kernel) resval3H80
theorem resval3H72 : resval3Tail72=hornerBox Q residualBox cell3 72 148 :=
  hornerChunk_step Q residualBox cell3 resval3Tail72 resval3Tail76 72 4 144 (by decide +kernel) resval3H76
theorem resval3H68 : resval3Tail68=hornerBox Q residualBox cell3 68 152 :=
  hornerChunk_step Q residualBox cell3 resval3Tail68 resval3Tail72 68 4 148 (by decide +kernel) resval3H72
theorem resval3H64 : resval3Tail64=hornerBox Q residualBox cell3 64 156 :=
  hornerChunk_step Q residualBox cell3 resval3Tail64 resval3Tail68 64 4 152 (by decide +kernel) resval3H68
theorem resval3H60 : resval3Tail60=hornerBox Q residualBox cell3 60 160 :=
  hornerChunk_step Q residualBox cell3 resval3Tail60 resval3Tail64 60 4 156 (by decide +kernel) resval3H64
theorem resval3H56 : resval3Tail56=hornerBox Q residualBox cell3 56 164 :=
  hornerChunk_step Q residualBox cell3 resval3Tail56 resval3Tail60 56 4 160 (by decide +kernel) resval3H60
theorem resval3H52 : resval3Tail52=hornerBox Q residualBox cell3 52 168 :=
  hornerChunk_step Q residualBox cell3 resval3Tail52 resval3Tail56 52 4 164 (by decide +kernel) resval3H56
theorem resval3H48 : resval3Tail48=hornerBox Q residualBox cell3 48 172 :=
  hornerChunk_step Q residualBox cell3 resval3Tail48 resval3Tail52 48 4 168 (by decide +kernel) resval3H52
theorem resval3H44 : resval3Tail44=hornerBox Q residualBox cell3 44 176 :=
  hornerChunk_step Q residualBox cell3 resval3Tail44 resval3Tail48 44 4 172 (by decide +kernel) resval3H48
theorem resval3H40 : resval3Tail40=hornerBox Q residualBox cell3 40 180 :=
  hornerChunk_step Q residualBox cell3 resval3Tail40 resval3Tail44 40 4 176 (by decide +kernel) resval3H44
theorem resval3H36 : resval3Tail36=hornerBox Q residualBox cell3 36 184 :=
  hornerChunk_step Q residualBox cell3 resval3Tail36 resval3Tail40 36 4 180 (by decide +kernel) resval3H40
theorem resval3H32 : resval3Tail32=hornerBox Q residualBox cell3 32 188 :=
  hornerChunk_step Q residualBox cell3 resval3Tail32 resval3Tail36 32 4 184 (by decide +kernel) resval3H36
theorem resval3H28 : resval3Tail28=hornerBox Q residualBox cell3 28 192 :=
  hornerChunk_step Q residualBox cell3 resval3Tail28 resval3Tail32 28 4 188 (by decide +kernel) resval3H32
theorem resval3H24 : resval3Tail24=hornerBox Q residualBox cell3 24 196 :=
  hornerChunk_step Q residualBox cell3 resval3Tail24 resval3Tail28 24 4 192 (by decide +kernel) resval3H28
theorem resval3H20 : resval3Tail20=hornerBox Q residualBox cell3 20 200 :=
  hornerChunk_step Q residualBox cell3 resval3Tail20 resval3Tail24 20 4 196 (by decide +kernel) resval3H24
theorem resval3H16 : resval3Tail16=hornerBox Q residualBox cell3 16 204 :=
  hornerChunk_step Q residualBox cell3 resval3Tail16 resval3Tail20 16 4 200 (by decide +kernel) resval3H20
theorem resval3H12 : resval3Tail12=hornerBox Q residualBox cell3 12 208 :=
  hornerChunk_step Q residualBox cell3 resval3Tail12 resval3Tail16 12 4 204 (by decide +kernel) resval3H16
theorem resval3H8 : resval3Tail8=hornerBox Q residualBox cell3 8 212 :=
  hornerChunk_step Q residualBox cell3 resval3Tail8 resval3Tail12 8 4 208 (by decide +kernel) resval3H12
theorem resval3H4 : resval3Tail4=hornerBox Q residualBox cell3 4 216 :=
  hornerChunk_step Q residualBox cell3 resval3Tail4 resval3Tail8 4 4 212 (by decide +kernel) resval3H8
theorem resval3H0 : resval3=hornerBox Q residualBox cell3 0 220 :=
  hornerChunk_step Q residualBox cell3 resval3 resval3Tail4 0 4 216 (by decide +kernel) resval3H4
theorem resval3_eq : resval3=hornerBox Q residualBox cell3 0 220 := resval3H0
def polyval3Tail5 : Box := ⟨32744255929843770855044908236608993192231790670244639749,295606079310614363734897963766431277324311546970840037239⟩
def polyval3Tail9 : Box := ⟨48542095087177094838624707561190419823812939903620932744,376517572176169165326968161605620942595280885529536170896⟩
def polyval3Tail13 : Box := ⟨71965846287668292303546440202529821969393451313903747929,478290160487732668337818069652578555098815727585745508772⟩
def polyval3Tail17 : Box := ⟨106692614727127301747956115847669432298973326781652786101,605634845223983047470220430730550796130687547518089289451⟩
def polyval3Tail21 : Box := ⟨158176616055163163174529918619606940027284499794231664175,763958542766682629555403946644295712119807821555021649353⟩
def polyval3Tail25 : Box := ⟨234503971344711316927111589445709246263300745319202859175,959235283342666176538819305404499539673933236869231169414⟩
def polyval3Tail29 : Box := ⟨347662719989299887507163934135031337402747716909204438318,1197678431520664979723356998041901664515011463846996979221⟩
def polyval3Tail33 : Box := ⟨515425671374602341690908023858969701322569912245780901962,1485077591941092622026026914919909603764393824150547254854⟩
def polyval3Tail37 : Box := ⟨764141817449210462375517003807564168563166298082034071137,1825586219383528009565992622909480768253278266717742650458⟩
def polyval3Tail41 : Box := ⟨1132874727829000510116420443235512502984596049082380142079,2219627328899302670073766184309532450305811960215958545416⟩
def polyval3Tail45 : Box := ⟨1679537907292889302691656204197972752456340628164000971890,2660404310776169012705652802237568155750173833939662081263⟩
def polyval3Tail49 : Box := ⟨2489990740140833266373079438151740335186022241440324903760,3128230557703587588118353908694443216768693506049577486190⟩
def polyval3Tail53 : Box := ⟨3691523638177632911730454626188246361558786892223675491749,3581478850227936770010209372350463530001403757316852465439⟩
def polyval3Tail57 : Box := ⟨5472850381143774012430052346992061421624955010854139366583,3942329689575187287189851617464980394763554270353135822488⟩
def polyval3Tail61 : Box := ⟨8113747663599358504958045973414538164547349922308742364788,4074563271998430778735930922540905978993204139059430065811⟩
def polyval3Tail65 : Box := ⟨12028997060729854889903416419539650948901783369014007739857,3749237911627034255326680791996911533375805155391343587463⟩
def polyval3Tail69 : Box := ⟨17833531019764281842313727864441661710520417893946038883019,2591998049672070235269954694115184983674350532652911455224⟩
def polyval3Tail73 : Box := ⟨26468750000000000000000000000000000000000000000000000000000,2⟩
theorem polyval3H73 : polyval3Tail73=hornerBox Q polyBox cell3 73 1 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail73 zero 73 1 0 (by decide +kernel) rfl
theorem polyval3H69 : polyval3Tail69=hornerBox Q polyBox cell3 69 5 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail69 polyval3Tail73 69 4 1 (by decide +kernel) polyval3H73
theorem polyval3H65 : polyval3Tail65=hornerBox Q polyBox cell3 65 9 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail65 polyval3Tail69 65 4 5 (by decide +kernel) polyval3H69
theorem polyval3H61 : polyval3Tail61=hornerBox Q polyBox cell3 61 13 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail61 polyval3Tail65 61 4 9 (by decide +kernel) polyval3H65
theorem polyval3H57 : polyval3Tail57=hornerBox Q polyBox cell3 57 17 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail57 polyval3Tail61 57 4 13 (by decide +kernel) polyval3H61
theorem polyval3H53 : polyval3Tail53=hornerBox Q polyBox cell3 53 21 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail53 polyval3Tail57 53 4 17 (by decide +kernel) polyval3H57
theorem polyval3H49 : polyval3Tail49=hornerBox Q polyBox cell3 49 25 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail49 polyval3Tail53 49 4 21 (by decide +kernel) polyval3H53
theorem polyval3H45 : polyval3Tail45=hornerBox Q polyBox cell3 45 29 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail45 polyval3Tail49 45 4 25 (by decide +kernel) polyval3H49
theorem polyval3H41 : polyval3Tail41=hornerBox Q polyBox cell3 41 33 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail41 polyval3Tail45 41 4 29 (by decide +kernel) polyval3H45
theorem polyval3H37 : polyval3Tail37=hornerBox Q polyBox cell3 37 37 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail37 polyval3Tail41 37 4 33 (by decide +kernel) polyval3H41
theorem polyval3H33 : polyval3Tail33=hornerBox Q polyBox cell3 33 41 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail33 polyval3Tail37 33 4 37 (by decide +kernel) polyval3H37
theorem polyval3H29 : polyval3Tail29=hornerBox Q polyBox cell3 29 45 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail29 polyval3Tail33 29 4 41 (by decide +kernel) polyval3H33
theorem polyval3H25 : polyval3Tail25=hornerBox Q polyBox cell3 25 49 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail25 polyval3Tail29 25 4 45 (by decide +kernel) polyval3H29
theorem polyval3H21 : polyval3Tail21=hornerBox Q polyBox cell3 21 53 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail21 polyval3Tail25 21 4 49 (by decide +kernel) polyval3H25
theorem polyval3H17 : polyval3Tail17=hornerBox Q polyBox cell3 17 57 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail17 polyval3Tail21 17 4 53 (by decide +kernel) polyval3H21
theorem polyval3H13 : polyval3Tail13=hornerBox Q polyBox cell3 13 61 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail13 polyval3Tail17 13 4 57 (by decide +kernel) polyval3H17
theorem polyval3H9 : polyval3Tail9=hornerBox Q polyBox cell3 9 65 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail9 polyval3Tail13 9 4 61 (by decide +kernel) polyval3H13
theorem polyval3H5 : polyval3Tail5=hornerBox Q polyBox cell3 5 69 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail5 polyval3Tail9 5 4 65 (by decide +kernel) polyval3H9
theorem polyval3H1 : polyval3=hornerBox Q polyBox cell3 1 73 :=
  hornerChunk_step Q polyBox cell3 polyval3 polyval3Tail5 1 4 69 (by decide +kernel) polyval3H5
theorem polyval3_eq : polyval3=hornerBox Q polyBox cell3 1 73 := polyval3H1
theorem polyval3_upper : 5*(polyval3.center+polyval3.radius)<Q := by decide +kernel
theorem resval3_pos : 0<(resval3).center-(resval3).radius := by decide +kernel
theorem polyval3_pos : 0<(polyval3).center-(polyval3).radius := by decide +kernel
def cell4 : Box := ⟨953125000000000000000000000000000000000000000000000000000000,15625000000000000000000000000000000000000000000000000000002⟩
def resval4 : Box := ⟨103633018993886276541132334408104308013153786071640481642,9405655338081255698763728591360617837228112803013448897⟩
def polyval4 : Box := ⟨4546845048066673074731834951597906480304264663849345946483,1858453900411795733989532621594331879560545992564283076011⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-4341498986901064623609218367806364841588408289200538472,10103720384223627387968335804999681138767526099525060782⟩
def resval4Tail8 : Box := ⟨-5260719910513027832182110360178821837919923571667275692,11140597619644443040937412702439623291429054875294887704⟩
def resval4Tail12 : Box := ⟨-6374494286349377556265655168183777040140373852111409373,12247743795932978632117451508763538918539867464293285467⟩
def resval4Tail16 : Box := ⟨-7724071620707113884420610605498212821330228741773136000,13419824316008708698303485235295597127802876916446100923⟩
def resval4Tail20 : Box := ⟨-9359374990661353522324664903894267526071956079024888601,14647639279439430250396347041297934140541439317042774001⟩
def resval4Tail24 : Box := ⟨-11340896941061472109353704026894150338945849521415053506,15916933682481684598861208061716612804472574254150897531⟩
def resval4Tail28 : Box := ⟨-13741937207998241996517588358947548485864391373277696577,17206906406724529975409388493962310640349169281391150668⟩
def resval4Tail32 : Box := ⟨-16651314195867440165218687715583557371045702447666687536,18488346561334123571458137827407121021239918151514972851⟩
def resval4Tail36 : Box := ⟨-20176650515337735787974552995645323866487183716086026336,19721310568539498077618449514800287337738831543547917181⟩
def resval4Tail40 : Box := ⟨-24448354119647373262885752017177036674225141094489575920,20852234000696023777123880334344983155774106899013385137⟩
def resval4Tail44 : Box := ⟨-29624442307969145757225275115783164014784812752207022489,21810348551012077078279965313071552278853785928473845857⟩
def resval4Tail48 : Box := ⟨-35896387043613810072037818955907655261514503707168408592,22503245731111501764294255169179497861899398554066082993⟩
def resval4Tail52 : Box := ⟨-43496197814947485749670108490921675343576242862188993773,22811393822265277680839740274170072833081252477129013411⟩
def resval4Tail56 : Box := ⟨-52705004045626546778541608913874320751170075258827327324,22581371909638145808966865192470034360377818795350228738⟩
def resval4Tail60 : Box := ⟨-63863454531532385179224111011121041044499753762994575097,21617532856589681853588311194617245635118516821804185461⟩
def resval4Tail64 : Box := ⟨-77384318594094730291635178221866547370985245361370588043,19671743833279437011185572900701947728392161356896302673⟩
def resval4Tail68 : Box := ⟨-93767711703191859004971108051180760036468507770483096506,16430773438281417900213173002244018885556499455344000381⟩
def resval4Tail72 : Box := ⟨743256424536085248000658290994408027783881485397394314218,1080502738462302778027272091018926590038032055267497421⟩
def resval4Tail76 : Box := ⟨-54511436037488497110471691790606608455315456961155762,129802538282281502322681966444146955769044443800200950⟩
def resval4Tail80 : Box := ⟨-66024780629168356614157339685932681009036104340520198,143221306004581936356090956030581469860197636369845921⟩
def resval4Tail84 : Box := ⟨-80003228940710708318410133991871870707549837710194905,157577100426541554790166357112586550086789856500923082⟩
def resval4Tail88 : Box := ⟨-96941128576176742410907421182535866587263887219668186,172810215947649823392280881526614876993362613152925197⟩
def resval4Tail92 : Box := ⟨-117465039025528766840774270867156913518960675314287208,188813633398178373509477537066445885153969163749614260⟩
def resval4Tail96 : Box := ⟨-142334173285662129825033455443825681678651322759230076,205418032907116512707057866971546221746076366391984368⟩
def resval4Tail100 : Box := ⟨-172468481285823176053534524943533851805253437904903604,222373235752337361180472149330521488368227607013156029⟩
def resval4Tail104 : Box := ⟨-208982680338753937886814945804691968877742319790260657,239324990288125389670807210596394247073958164032128721⟩
def resval4Tail108 : Box := ⟨-253227490356290238110462189297480306182655548863840950,255786017766698430007635370576511862055932414461002838⟩
def resval4Tail112 : Box := ⟨-306839599186889282021026028333555725279763889837899865,271099991026620714676060846880554212189356959772549750⟩
def resval4Tail116 : Box := ⟨-371802206374597675402847194719622836396494208283896329,284396822935749851397513518784784079875514519462679441⟩
def resval4Tail120 : Box := ⟨-450518384952073486456640319708754267682911609564798634,294537280656101063212179755013383314508542897407962073⟩
def resval4Tail124 : Box := ⟨-545899975040308966401993776176747049098767715421435865,300044502259890202972324633448457717992670050913231185⟩
def resval4Tail128 : Box := ⟨-661475297574619900143223528039744785655820069504681839,299019456989200168899095752494314122536522557851658910⟩
def resval4Tail132 : Box := ⟨-801519672663710197304189146467353904450791033609256929,289036738897605767160398385175521235557347873965903495⟩
def resval4Tail136 : Box := ⟨-971213570676069016639250350443020318068014642881949756,267016290707573493971904049726173507481177718240851143⟩
def resval4Tail140 : Box := ⟨-1176834302792294172238121988227319810691722184350178240,229065684579376112109825541571023679936746229877543830⟩
def resval4Tail144 : Box := ⟨-1460999301428659584828928343939331653425577034828172293,167754319971121121175740480513979001712441478219110318⟩
def resval4Tail148 : Box := ⟨15195035132019979812917234755808888549686385766,32309526938999575188710011229537794646073084725⟩
def resval4Tail152 : Box := ⟨18352894705950623988757227109427970115059041493,35528298820607080146313522444238170009121240400⟩
def resval4Tail156 : Box := ⟨22238480536308820523110622446064721902163062071,38938824093915917446041111533813270449685193357⟩
def resval4Tail160 : Box := ⟨26946704896126644278232629785279645144351061926,42514686214309818554034339524360447669131829820⟩
def resval4Tail164 : Box := ⟨32651731919395027437203999566208487596994034643,46215502983781663409956448500075340873099717363⟩
def resval4Tail168 : Box := ⟨39564599881349564071815893455317903210548873801,49982134525159220746328318650775355845803199063⟩
def resval4Tail172 : Box := ⟨47941027068198746995691575043207865199170688852,53731329680634636875683662613119751068683753297⟩
def resval4Tail176 : Box := ⟨58090871214324728215900083876751277994749854231,57349051808827657408411961761387183380363848001⟩
def resval4Tail180 : Box := ⟨70389591646394629218705373931696160111567947373,60682179026849439847555124579701107170189158443⟩
def resval4Tail184 : Box := ⟨85292138137608131975631073111021047696153816119,63528205964439978424852436936795692551273282402⟩
def resval4Tail188 : Box := ⟨103349780243503399577695668372414184036246500947,65622491244799735284750511379559177374804759752⟩
def resval4Tail192 : Box := ⟨125230499663963289153388529333094016954624284615,66622493985470722571050976804311377631611610313⟩
def resval4Tail196 : Box := ⟨151743699978227362157023005475152061385514299405,66088319725654756692440169491778417140707264729⟩
def resval4Tail200 : Box := ⟨183870147806400185785974093104394232169397871591,63458746602084187393527684557062229749135554902⟩
def resval4Tail204 : Box := ⟨222798252969964221833998162374463391950225873043,58021720569642269388747524665171846559533144195⟩
def resval4Tail208 : Box := ⟨269968029713749660062709955979203961892214120162,48878087022386748097488730419965104653596822528⟩
def resval4Tail212 : Box := ⟨327124365209337965673503457934496098943691611486,34897056849511256924835529729113718145847281969⟩
def resval4Tail216 : Box := ⟨396382592034086888693369838874021940057296476091,14661481603207359605499875496472137071966124727⟩
theorem resval4H216 : resval4Tail216=hornerBox Q residualBox cell4 216 4 :=
  hornerChunk_step Q residualBox cell4 resval4Tail216 zero 216 4 0 (by decide +kernel) rfl
theorem resval4H212 : resval4Tail212=hornerBox Q residualBox cell4 212 8 :=
  hornerChunk_step Q residualBox cell4 resval4Tail212 resval4Tail216 212 4 4 (by decide +kernel) resval4H216
theorem resval4H208 : resval4Tail208=hornerBox Q residualBox cell4 208 12 :=
  hornerChunk_step Q residualBox cell4 resval4Tail208 resval4Tail212 208 4 8 (by decide +kernel) resval4H212
theorem resval4H204 : resval4Tail204=hornerBox Q residualBox cell4 204 16 :=
  hornerChunk_step Q residualBox cell4 resval4Tail204 resval4Tail208 204 4 12 (by decide +kernel) resval4H208
theorem resval4H200 : resval4Tail200=hornerBox Q residualBox cell4 200 20 :=
  hornerChunk_step Q residualBox cell4 resval4Tail200 resval4Tail204 200 4 16 (by decide +kernel) resval4H204
theorem resval4H196 : resval4Tail196=hornerBox Q residualBox cell4 196 24 :=
  hornerChunk_step Q residualBox cell4 resval4Tail196 resval4Tail200 196 4 20 (by decide +kernel) resval4H200
theorem resval4H192 : resval4Tail192=hornerBox Q residualBox cell4 192 28 :=
  hornerChunk_step Q residualBox cell4 resval4Tail192 resval4Tail196 192 4 24 (by decide +kernel) resval4H196
theorem resval4H188 : resval4Tail188=hornerBox Q residualBox cell4 188 32 :=
  hornerChunk_step Q residualBox cell4 resval4Tail188 resval4Tail192 188 4 28 (by decide +kernel) resval4H192
theorem resval4H184 : resval4Tail184=hornerBox Q residualBox cell4 184 36 :=
  hornerChunk_step Q residualBox cell4 resval4Tail184 resval4Tail188 184 4 32 (by decide +kernel) resval4H188
theorem resval4H180 : resval4Tail180=hornerBox Q residualBox cell4 180 40 :=
  hornerChunk_step Q residualBox cell4 resval4Tail180 resval4Tail184 180 4 36 (by decide +kernel) resval4H184
theorem resval4H176 : resval4Tail176=hornerBox Q residualBox cell4 176 44 :=
  hornerChunk_step Q residualBox cell4 resval4Tail176 resval4Tail180 176 4 40 (by decide +kernel) resval4H180
theorem resval4H172 : resval4Tail172=hornerBox Q residualBox cell4 172 48 :=
  hornerChunk_step Q residualBox cell4 resval4Tail172 resval4Tail176 172 4 44 (by decide +kernel) resval4H176
theorem resval4H168 : resval4Tail168=hornerBox Q residualBox cell4 168 52 :=
  hornerChunk_step Q residualBox cell4 resval4Tail168 resval4Tail172 168 4 48 (by decide +kernel) resval4H172
theorem resval4H164 : resval4Tail164=hornerBox Q residualBox cell4 164 56 :=
  hornerChunk_step Q residualBox cell4 resval4Tail164 resval4Tail168 164 4 52 (by decide +kernel) resval4H168
theorem resval4H160 : resval4Tail160=hornerBox Q residualBox cell4 160 60 :=
  hornerChunk_step Q residualBox cell4 resval4Tail160 resval4Tail164 160 4 56 (by decide +kernel) resval4H164
theorem resval4H156 : resval4Tail156=hornerBox Q residualBox cell4 156 64 :=
  hornerChunk_step Q residualBox cell4 resval4Tail156 resval4Tail160 156 4 60 (by decide +kernel) resval4H160
theorem resval4H152 : resval4Tail152=hornerBox Q residualBox cell4 152 68 :=
  hornerChunk_step Q residualBox cell4 resval4Tail152 resval4Tail156 152 4 64 (by decide +kernel) resval4H156
theorem resval4H148 : resval4Tail148=hornerBox Q residualBox cell4 148 72 :=
  hornerChunk_step Q residualBox cell4 resval4Tail148 resval4Tail152 148 4 68 (by decide +kernel) resval4H152
theorem resval4H144 : resval4Tail144=hornerBox Q residualBox cell4 144 76 :=
  hornerChunk_step Q residualBox cell4 resval4Tail144 resval4Tail148 144 4 72 (by decide +kernel) resval4H148
theorem resval4H140 : resval4Tail140=hornerBox Q residualBox cell4 140 80 :=
  hornerChunk_step Q residualBox cell4 resval4Tail140 resval4Tail144 140 4 76 (by decide +kernel) resval4H144
theorem resval4H136 : resval4Tail136=hornerBox Q residualBox cell4 136 84 :=
  hornerChunk_step Q residualBox cell4 resval4Tail136 resval4Tail140 136 4 80 (by decide +kernel) resval4H140
theorem resval4H132 : resval4Tail132=hornerBox Q residualBox cell4 132 88 :=
  hornerChunk_step Q residualBox cell4 resval4Tail132 resval4Tail136 132 4 84 (by decide +kernel) resval4H136
theorem resval4H128 : resval4Tail128=hornerBox Q residualBox cell4 128 92 :=
  hornerChunk_step Q residualBox cell4 resval4Tail128 resval4Tail132 128 4 88 (by decide +kernel) resval4H132
theorem resval4H124 : resval4Tail124=hornerBox Q residualBox cell4 124 96 :=
  hornerChunk_step Q residualBox cell4 resval4Tail124 resval4Tail128 124 4 92 (by decide +kernel) resval4H128
theorem resval4H120 : resval4Tail120=hornerBox Q residualBox cell4 120 100 :=
  hornerChunk_step Q residualBox cell4 resval4Tail120 resval4Tail124 120 4 96 (by decide +kernel) resval4H124
theorem resval4H116 : resval4Tail116=hornerBox Q residualBox cell4 116 104 :=
  hornerChunk_step Q residualBox cell4 resval4Tail116 resval4Tail120 116 4 100 (by decide +kernel) resval4H120
theorem resval4H112 : resval4Tail112=hornerBox Q residualBox cell4 112 108 :=
  hornerChunk_step Q residualBox cell4 resval4Tail112 resval4Tail116 112 4 104 (by decide +kernel) resval4H116
theorem resval4H108 : resval4Tail108=hornerBox Q residualBox cell4 108 112 :=
  hornerChunk_step Q residualBox cell4 resval4Tail108 resval4Tail112 108 4 108 (by decide +kernel) resval4H112
theorem resval4H104 : resval4Tail104=hornerBox Q residualBox cell4 104 116 :=
  hornerChunk_step Q residualBox cell4 resval4Tail104 resval4Tail108 104 4 112 (by decide +kernel) resval4H108
theorem resval4H100 : resval4Tail100=hornerBox Q residualBox cell4 100 120 :=
  hornerChunk_step Q residualBox cell4 resval4Tail100 resval4Tail104 100 4 116 (by decide +kernel) resval4H104
theorem resval4H96 : resval4Tail96=hornerBox Q residualBox cell4 96 124 :=
  hornerChunk_step Q residualBox cell4 resval4Tail96 resval4Tail100 96 4 120 (by decide +kernel) resval4H100
theorem resval4H92 : resval4Tail92=hornerBox Q residualBox cell4 92 128 :=
  hornerChunk_step Q residualBox cell4 resval4Tail92 resval4Tail96 92 4 124 (by decide +kernel) resval4H96
theorem resval4H88 : resval4Tail88=hornerBox Q residualBox cell4 88 132 :=
  hornerChunk_step Q residualBox cell4 resval4Tail88 resval4Tail92 88 4 128 (by decide +kernel) resval4H92
theorem resval4H84 : resval4Tail84=hornerBox Q residualBox cell4 84 136 :=
  hornerChunk_step Q residualBox cell4 resval4Tail84 resval4Tail88 84 4 132 (by decide +kernel) resval4H88
theorem resval4H80 : resval4Tail80=hornerBox Q residualBox cell4 80 140 :=
  hornerChunk_step Q residualBox cell4 resval4Tail80 resval4Tail84 80 4 136 (by decide +kernel) resval4H84
theorem resval4H76 : resval4Tail76=hornerBox Q residualBox cell4 76 144 :=
  hornerChunk_step Q residualBox cell4 resval4Tail76 resval4Tail80 76 4 140 (by decide +kernel) resval4H80
theorem resval4H72 : resval4Tail72=hornerBox Q residualBox cell4 72 148 :=
  hornerChunk_step Q residualBox cell4 resval4Tail72 resval4Tail76 72 4 144 (by decide +kernel) resval4H76
theorem resval4H68 : resval4Tail68=hornerBox Q residualBox cell4 68 152 :=
  hornerChunk_step Q residualBox cell4 resval4Tail68 resval4Tail72 68 4 148 (by decide +kernel) resval4H72
theorem resval4H64 : resval4Tail64=hornerBox Q residualBox cell4 64 156 :=
  hornerChunk_step Q residualBox cell4 resval4Tail64 resval4Tail68 64 4 152 (by decide +kernel) resval4H68
theorem resval4H60 : resval4Tail60=hornerBox Q residualBox cell4 60 160 :=
  hornerChunk_step Q residualBox cell4 resval4Tail60 resval4Tail64 60 4 156 (by decide +kernel) resval4H64
theorem resval4H56 : resval4Tail56=hornerBox Q residualBox cell4 56 164 :=
  hornerChunk_step Q residualBox cell4 resval4Tail56 resval4Tail60 56 4 160 (by decide +kernel) resval4H60
theorem resval4H52 : resval4Tail52=hornerBox Q residualBox cell4 52 168 :=
  hornerChunk_step Q residualBox cell4 resval4Tail52 resval4Tail56 52 4 164 (by decide +kernel) resval4H56
theorem resval4H48 : resval4Tail48=hornerBox Q residualBox cell4 48 172 :=
  hornerChunk_step Q residualBox cell4 resval4Tail48 resval4Tail52 48 4 168 (by decide +kernel) resval4H52
theorem resval4H44 : resval4Tail44=hornerBox Q residualBox cell4 44 176 :=
  hornerChunk_step Q residualBox cell4 resval4Tail44 resval4Tail48 44 4 172 (by decide +kernel) resval4H48
theorem resval4H40 : resval4Tail40=hornerBox Q residualBox cell4 40 180 :=
  hornerChunk_step Q residualBox cell4 resval4Tail40 resval4Tail44 40 4 176 (by decide +kernel) resval4H44
theorem resval4H36 : resval4Tail36=hornerBox Q residualBox cell4 36 184 :=
  hornerChunk_step Q residualBox cell4 resval4Tail36 resval4Tail40 36 4 180 (by decide +kernel) resval4H40
theorem resval4H32 : resval4Tail32=hornerBox Q residualBox cell4 32 188 :=
  hornerChunk_step Q residualBox cell4 resval4Tail32 resval4Tail36 32 4 184 (by decide +kernel) resval4H36
theorem resval4H28 : resval4Tail28=hornerBox Q residualBox cell4 28 192 :=
  hornerChunk_step Q residualBox cell4 resval4Tail28 resval4Tail32 28 4 188 (by decide +kernel) resval4H32
theorem resval4H24 : resval4Tail24=hornerBox Q residualBox cell4 24 196 :=
  hornerChunk_step Q residualBox cell4 resval4Tail24 resval4Tail28 24 4 192 (by decide +kernel) resval4H28
theorem resval4H20 : resval4Tail20=hornerBox Q residualBox cell4 20 200 :=
  hornerChunk_step Q residualBox cell4 resval4Tail20 resval4Tail24 20 4 196 (by decide +kernel) resval4H24
theorem resval4H16 : resval4Tail16=hornerBox Q residualBox cell4 16 204 :=
  hornerChunk_step Q residualBox cell4 resval4Tail16 resval4Tail20 16 4 200 (by decide +kernel) resval4H20
theorem resval4H12 : resval4Tail12=hornerBox Q residualBox cell4 12 208 :=
  hornerChunk_step Q residualBox cell4 resval4Tail12 resval4Tail16 12 4 204 (by decide +kernel) resval4H16
theorem resval4H8 : resval4Tail8=hornerBox Q residualBox cell4 8 212 :=
  hornerChunk_step Q residualBox cell4 resval4Tail8 resval4Tail12 8 4 208 (by decide +kernel) resval4H12
theorem resval4H4 : resval4Tail4=hornerBox Q residualBox cell4 4 216 :=
  hornerChunk_step Q residualBox cell4 resval4Tail4 resval4Tail8 4 4 212 (by decide +kernel) resval4H8
theorem resval4H0 : resval4=hornerBox Q residualBox cell4 0 220 :=
  hornerChunk_step Q residualBox cell4 resval4 resval4Tail4 0 4 216 (by decide +kernel) resval4H4
theorem resval4_eq : resval4=hornerBox Q residualBox cell4 0 220 := resval4H0
def polyval4Tail5 : Box := ⟨1010322992201298454904720680060004594441590911294014200991,2042483218486407129826250379538573851235167472260020636799⟩
def polyval4Tail9 : Box := ⟨1224221492940318786898682402900105444203926387537297522975,2241966475308176627143798445751357471849440088679892542419⟩
def polyval4Tail13 : Box := ⟨1483407791278177877440902345922250779551815716186841365758,2452140523077980113853531014181090143747651621754273657269⟩
def polyval4Tail17 : Box := ⟨1797467768866838132358814673196359495710155267194263099659,2670997495349351775613488520918384258749776322326596194357⟩
def polyval4Tail21 : Box := ⟨2178019017502585258037109722182644761119747225537819805324,2895526070146482990935101201853057567776510372310964550063⟩
def polyval4Tail25 : Box := ⟨2639138749950158561620419742480022063518825970710211908973,3121420689225246636558322082030118182693299080232463353363⟩
def polyval4Tail29 : Box := ⟨3197884538893939300664734355657520219338119966606692172490,3342718624967835018441935024772088205268165816025108192190⟩
def polyval4Tail33 : Box := ⟨3874925304435030038117685209519886649921958193142871662204,3551348167580791874347205311264153550783053369097998629698⟩
def polyval4Tail37 : Box := ⟨4695305891232772131065797697030893402638389499950031606075,3736567484892364685187509871760548854574876311986554280293⟩
def polyval4Tail41 : Box := ⟨5689373518248889635643715222894822448835001521821311507491,3884269157168119249091179283852949935379552225649081000491⟩
def polyval4Tail45 : Box := ⟨6893900371984739906906601952224477251430092210854830367234,3976119846308147323942289533121444393893457375437521316173⟩
def polyval4Tail49 : Box := ⟨8353443869770592492162669496530229293376402299004200993734,3988497808238551339963221643247600172812914430510832598751⟩
def polyval4Tail53 : Box := ⟨10121994911469595866019071622267579673495123244012849210522,3891182739022505562368000184358613641139443740168320439494⟩
def polyval4Tail57 : Box := ⟨12264975091121318498554772873556433731216462693948005313204,3645742443230803183204447908109617785642789321105610339145⟩
def polyval4Tail61 : Box := ⟨14861656748648357015506579045165882092401113690459802046875,3203548643866609650666428638509076193859827080941169001268⟩
def polyval4Tail65 : Box := ⟨18008095383299633602776104654013594033807491216991127404511,2503339451063496659307389215746838531759161267591416410439⟩
def polyval4Tail69 : Box := ⟨21820682945729268367566060753127439109313362825332928794006,1468228002855151939549216566482739692703720894024760439270⟩
def polyval4Tail73 : Box := ⟨26468750000000000000000000000000000000000000000000000000000,2⟩
theorem polyval4H73 : polyval4Tail73=hornerBox Q polyBox cell4 73 1 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail73 zero 73 1 0 (by decide +kernel) rfl
theorem polyval4H69 : polyval4Tail69=hornerBox Q polyBox cell4 69 5 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail69 polyval4Tail73 69 4 1 (by decide +kernel) polyval4H73
theorem polyval4H65 : polyval4Tail65=hornerBox Q polyBox cell4 65 9 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail65 polyval4Tail69 65 4 5 (by decide +kernel) polyval4H69
theorem polyval4H61 : polyval4Tail61=hornerBox Q polyBox cell4 61 13 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail61 polyval4Tail65 61 4 9 (by decide +kernel) polyval4H65
theorem polyval4H57 : polyval4Tail57=hornerBox Q polyBox cell4 57 17 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail57 polyval4Tail61 57 4 13 (by decide +kernel) polyval4H61
theorem polyval4H53 : polyval4Tail53=hornerBox Q polyBox cell4 53 21 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail53 polyval4Tail57 53 4 17 (by decide +kernel) polyval4H57
theorem polyval4H49 : polyval4Tail49=hornerBox Q polyBox cell4 49 25 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail49 polyval4Tail53 49 4 21 (by decide +kernel) polyval4H53
theorem polyval4H45 : polyval4Tail45=hornerBox Q polyBox cell4 45 29 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail45 polyval4Tail49 45 4 25 (by decide +kernel) polyval4H49
theorem polyval4H41 : polyval4Tail41=hornerBox Q polyBox cell4 41 33 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail41 polyval4Tail45 41 4 29 (by decide +kernel) polyval4H45
theorem polyval4H37 : polyval4Tail37=hornerBox Q polyBox cell4 37 37 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail37 polyval4Tail41 37 4 33 (by decide +kernel) polyval4H41
theorem polyval4H33 : polyval4Tail33=hornerBox Q polyBox cell4 33 41 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail33 polyval4Tail37 33 4 37 (by decide +kernel) polyval4H37
theorem polyval4H29 : polyval4Tail29=hornerBox Q polyBox cell4 29 45 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail29 polyval4Tail33 29 4 41 (by decide +kernel) polyval4H33
theorem polyval4H25 : polyval4Tail25=hornerBox Q polyBox cell4 25 49 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail25 polyval4Tail29 25 4 45 (by decide +kernel) polyval4H29
theorem polyval4H21 : polyval4Tail21=hornerBox Q polyBox cell4 21 53 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail21 polyval4Tail25 21 4 49 (by decide +kernel) polyval4H25
theorem polyval4H17 : polyval4Tail17=hornerBox Q polyBox cell4 17 57 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail17 polyval4Tail21 17 4 53 (by decide +kernel) polyval4H21
theorem polyval4H13 : polyval4Tail13=hornerBox Q polyBox cell4 13 61 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail13 polyval4Tail17 13 4 57 (by decide +kernel) polyval4H17
theorem polyval4H9 : polyval4Tail9=hornerBox Q polyBox cell4 9 65 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail9 polyval4Tail13 9 4 61 (by decide +kernel) polyval4H13
theorem polyval4H5 : polyval4Tail5=hornerBox Q polyBox cell4 5 69 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail5 polyval4Tail9 5 4 65 (by decide +kernel) polyval4H9
theorem polyval4H1 : polyval4=hornerBox Q polyBox cell4 1 73 :=
  hornerChunk_step Q polyBox cell4 polyval4 polyval4Tail5 1 4 69 (by decide +kernel) polyval4H5
theorem polyval4_eq : polyval4=hornerBox Q polyBox cell4 1 73 := polyval4H1
theorem polyval4_upper : 5*(polyval4.center+polyval4.radius)<Q := by decide +kernel
theorem resval4_pos : 0<(resval4).center-(resval4).radius := by decide +kernel
theorem polyval4_pos : 0<(polyval4).center-(polyval4).radius := by decide +kernel
def cell5 : Box := ⟨976562500000000000000000000000000000000000000000000000000000,7812500000000000000000000000000000000000000000000000000002⟩
def resval5 : Box := ⟨90323062913149323977287403694963095110968375994509011508,15435675401672432315046166583363309467664175038841088559⟩
def polyval5 : Box := ⟨8505805622202859508838395270506353616722796079513107623798,3718896724475828677408269738740670013024868903513190189542⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-18559889828476775668657147886541817670790649019296681906,15578048654089063864727662487956127682499737825382260157⟩
def resval5Tail8 : Box := ⟨-20406868661001768084085418813194842061411511889924943012,15950764666651349704200024659015434422598472432936497978⟩
def resval5Tail12 : Box := ⟨-22437589385151255001349954397894036912931154379417154626,16284011441157585861383413915487328029849370426645397393⟩
def resval5Tail16 : Box := ⟨-24670390428241960603774522315199069568689404166806799045,16568882679133379506804821480413228933983182766691925597⟩
def resval5Tail20 : Box := ⟨-27125381137625784973717824658118143176122775066834300973,16795262899100232547555991255913558972041760932663679987⟩
def resval5Tail24 : Box := ⟨-29824671968675333721221909022409239048428826183375591157,16951685305570716379997576903814637976512958218251243964⟩
def resval5Tail28 : Box := ⟨-32792573624163454669159795275459504478971140678937485601,17025174904712940047151135820540228921037875344794623549⟩
def resval5Tail32 : Box := ⟨-36055816004468283690136065996713725988497508225305332179,17001074551068641175187097114552612544282389649867173075⟩
def resval5Tail36 : Box := ⟨-39643788945864875089586430820839378956116093832835349313,16862852131873017135359571786181478158340856441133936490⟩
def resval5Tail40 : Box := ⟨-43588806915076083953869356480356653698275187592642091164,16591886911035807597282738741626846230652476843166411179⟩
def resval5Tail44 : Box := ⟨-47926400044009070062730290637921449725669982109190200951,16167232851453925415779536773046979991396811090565935356⟩
def resval5Tail48 : Box := ⟨-52695634125832170658491375395430266555317431866336408824,15565356510270343344409187909223548564311611580947010717⟩
def resval5Tail52 : Box := ⟨-57939462454382264691267135187790793424418582654069539490,14759846854887863895056127128875700260148778871471038770⟩
def resval5Tail56 : Box := ⟨-63705112675684273959393904986549268552356088411728371950,13721094075696348438508789732800557100406445412469008126⟩
def resval5Tail60 : Box := ⟨-70044512135693439649697406147818156555700619997507844529,12415934172054135220637156037980517328116719680124312405⟩
def resval5Tail64 : Box := ⟨-77014755552651555380475604148261292331848505268578738528,10807255758079936673235693812004479655447756381504935130⟩
def resval5Tail68 : Box := ⟨-84678576820592641885181698863149191816715103817681969779,8853562246595496746632990319046278979702699153577461683⟩
def resval5Tail72 : Box := ⟨743248615896491507486529650110906293248533220708118546538,1104310075503845561713271779583641021886135485514428253⟩
def resval5Tail76 : Box := ⟨-238210766632744790451151249674900962712196980415779222,203113815022795452873854382173843800487880577233131935⟩
def resval5Tail80 : Box := ⟨-261890537566473618494161567246788312008829074539422603,208104486815729194766730656690210568004524322025721551⟩
def resval5Tail84 : Box := ⟨-287951690045155279506940054400418504750151622391682691,212602334314407108620034331941249213647456208601652557⟩
def resval5Tail88 : Box := ⟨-316606231441781723495535176819256860575535001204805252,216493735373342788356710622566430997750880728323144999⟩
def resval5Tail92 : Box := ⟨-348112232896576888493568823483097430761696851102653034,219649808338093324676466325682639261190257990288652373⟩
def resval5Tail96 : Box := ⟨-382753447840853256726167284629861565402539664394293352,221924390337948089728858595893151923473897097728504613⟩
def resval5Tail100 : Box := ⟨-420841866472372876550488977350733355846303564069946375,223152027852560499769853088128364779896513916857270781⟩
def resval5Tail104 : Box := ⟨-462720525641328740406842362136645735330833738826228215,223145748500439365267740293946184171101552345928487728⟩
def resval5Tail108 : Box := ⟨-508766598353263709701326979689814876043878542198400433,221694591031491202772063463316255531847855709059266835⟩
def resval5Tail112 : Box := ⟨-559394790713455382535880425019544435187360465922880804,218560868157593703005206255360603769151107718257868755⟩
def resval5Tail116 : Box := ⟨-615061076906766176041081075548162195221759387494905594,213477134246166066649968520221005921626706625100206477⟩
def resval5Tail120 : Box := ⟨-676266805851418001240724331696297744251387266880717580,206142827027527948627442492010791912453981187961185085⟩
def resval5Tail124 : Box := ⟨-743563216512568768822551986173836078314241140812422795,196220549300777564090951900124177098699107099387011819⟩
def resval5Tail128 : Box := ⟨-817556402542092847119530409810919139693443323653601504,183331953135543097862938089181934416596329688000985361⟩
def resval5Tail132 : Box := ⟨-898912770957754557898165485957280201425786179249931161,167053185225887611749497908801906395057995774232556329⟩
def resval5Tail136 : Box := ⟨-988365044031097315022010036931199889887618681334715442,146909847821499657818315785565393757151717117756533362⟩
def resval5Tail140 : Box := ⟨-1086718913656460567552592242497811682659527350984454119,122371420022221278862797808545345992797751146839465031⟩
def resval5Tail144 : Box := ⟨-1229045389601442115258827345135690016131793954861323214,90633324033024269585594953928018663582856126921908720⟩
def resval5Tail148 : Box := ⟨83014420123803804381204304020028967208783079319,62499051175258213729156838798872714419804125079⟩
def resval5Tail152 : Box := ⟨91221685616729894146906051013881788861571051441,63700537355861802428858746756171271549395054395⟩
def resval5Tail156 : Box := ⟨100299303183062583018577401607192825460326714600,64695937057061800572452722970948825351232890415⟩
def resval5Tail160 : Box := ⟨110280250107362278043492653223520471383323478182,65442954214454355077871897438139124864600064430⟩
def resval5Tail164 : Box := ⟨121254417307089911867312290981526600112915316894,65894281602229107275977046176029876855238410394⟩
def resval5Tail168 : Box := ⟨133320641748348813180677440983662909587745480605,65996435575756131924418470566743455464828763969⟩
def resval5Tail172 : Box := ⟨146587595824867946099249654517460635743568861747,65689045928717977842890703530645121972357893492⟩
def resval5Tail176 : Box := ⟨161174766097170936833873639386893054418649368987,64904068888488573178411816751014146149783248685⟩
def resval5Tail180 : Box := ⟨177213529427916475346524736230326000271394451206,63564915182132803765272354124721364631465818584⟩
def resval5Tail184 : Box := ⟨194848336205218521864397726866128150717091939255,61585484291565068617546027428520797829355979844⟩
def resval5Tail188 : Box := ⟨214238011310445131760956547003429627730168473967,58869095104645060030368704118094766859698503114⟩
def resval5Tail192 : Box := ⟨235557184547440625694031080707295598745063938184,55307302164673611570236497163292590845331003469⟩
def resval5Tail196 : Box := ⟨258997863416088076257208416520199742216038986065,50778585614558947837276178397733995318161628169⟩
def resval5Tail200 : Box := ⟨284771162395129120907205344950883234370416816555,45146901713590233219741505331377811296698850258⟩
def resval5Tail204 : Box := ⟨313109204308732079326632360949219588266223640706,38260079462987558821131661960005512029155563247⟩
def resval5Tail208 : Box := ⟨344267210901150800841275658785427942027470684254,29948047398768387221341185613858730120803807225⟩
def resval5Tail212 : Box := ⟨378525801469907869519113763323700370512381226938,20020872980993197548456056466100881388390566154⟩
def resval5Tail216 : Box := ⟨416194522937813176031946938684672409497118299120,8266508867945326996812095291597897085427279105⟩
theorem resval5H216 : resval5Tail216=hornerBox Q residualBox cell5 216 4 :=
  hornerChunk_step Q residualBox cell5 resval5Tail216 zero 216 4 0 (by decide +kernel) rfl
theorem resval5H212 : resval5Tail212=hornerBox Q residualBox cell5 212 8 :=
  hornerChunk_step Q residualBox cell5 resval5Tail212 resval5Tail216 212 4 4 (by decide +kernel) resval5H216
theorem resval5H208 : resval5Tail208=hornerBox Q residualBox cell5 208 12 :=
  hornerChunk_step Q residualBox cell5 resval5Tail208 resval5Tail212 208 4 8 (by decide +kernel) resval5H212
theorem resval5H204 : resval5Tail204=hornerBox Q residualBox cell5 204 16 :=
  hornerChunk_step Q residualBox cell5 resval5Tail204 resval5Tail208 204 4 12 (by decide +kernel) resval5H208
theorem resval5H200 : resval5Tail200=hornerBox Q residualBox cell5 200 20 :=
  hornerChunk_step Q residualBox cell5 resval5Tail200 resval5Tail204 200 4 16 (by decide +kernel) resval5H204
theorem resval5H196 : resval5Tail196=hornerBox Q residualBox cell5 196 24 :=
  hornerChunk_step Q residualBox cell5 resval5Tail196 resval5Tail200 196 4 20 (by decide +kernel) resval5H200
theorem resval5H192 : resval5Tail192=hornerBox Q residualBox cell5 192 28 :=
  hornerChunk_step Q residualBox cell5 resval5Tail192 resval5Tail196 192 4 24 (by decide +kernel) resval5H196
theorem resval5H188 : resval5Tail188=hornerBox Q residualBox cell5 188 32 :=
  hornerChunk_step Q residualBox cell5 resval5Tail188 resval5Tail192 188 4 28 (by decide +kernel) resval5H192
theorem resval5H184 : resval5Tail184=hornerBox Q residualBox cell5 184 36 :=
  hornerChunk_step Q residualBox cell5 resval5Tail184 resval5Tail188 184 4 32 (by decide +kernel) resval5H188
theorem resval5H180 : resval5Tail180=hornerBox Q residualBox cell5 180 40 :=
  hornerChunk_step Q residualBox cell5 resval5Tail180 resval5Tail184 180 4 36 (by decide +kernel) resval5H184
theorem resval5H176 : resval5Tail176=hornerBox Q residualBox cell5 176 44 :=
  hornerChunk_step Q residualBox cell5 resval5Tail176 resval5Tail180 176 4 40 (by decide +kernel) resval5H180
theorem resval5H172 : resval5Tail172=hornerBox Q residualBox cell5 172 48 :=
  hornerChunk_step Q residualBox cell5 resval5Tail172 resval5Tail176 172 4 44 (by decide +kernel) resval5H176
theorem resval5H168 : resval5Tail168=hornerBox Q residualBox cell5 168 52 :=
  hornerChunk_step Q residualBox cell5 resval5Tail168 resval5Tail172 168 4 48 (by decide +kernel) resval5H172
theorem resval5H164 : resval5Tail164=hornerBox Q residualBox cell5 164 56 :=
  hornerChunk_step Q residualBox cell5 resval5Tail164 resval5Tail168 164 4 52 (by decide +kernel) resval5H168
theorem resval5H160 : resval5Tail160=hornerBox Q residualBox cell5 160 60 :=
  hornerChunk_step Q residualBox cell5 resval5Tail160 resval5Tail164 160 4 56 (by decide +kernel) resval5H164
theorem resval5H156 : resval5Tail156=hornerBox Q residualBox cell5 156 64 :=
  hornerChunk_step Q residualBox cell5 resval5Tail156 resval5Tail160 156 4 60 (by decide +kernel) resval5H160
theorem resval5H152 : resval5Tail152=hornerBox Q residualBox cell5 152 68 :=
  hornerChunk_step Q residualBox cell5 resval5Tail152 resval5Tail156 152 4 64 (by decide +kernel) resval5H156
theorem resval5H148 : resval5Tail148=hornerBox Q residualBox cell5 148 72 :=
  hornerChunk_step Q residualBox cell5 resval5Tail148 resval5Tail152 148 4 68 (by decide +kernel) resval5H152
theorem resval5H144 : resval5Tail144=hornerBox Q residualBox cell5 144 76 :=
  hornerChunk_step Q residualBox cell5 resval5Tail144 resval5Tail148 144 4 72 (by decide +kernel) resval5H148
theorem resval5H140 : resval5Tail140=hornerBox Q residualBox cell5 140 80 :=
  hornerChunk_step Q residualBox cell5 resval5Tail140 resval5Tail144 140 4 76 (by decide +kernel) resval5H144
theorem resval5H136 : resval5Tail136=hornerBox Q residualBox cell5 136 84 :=
  hornerChunk_step Q residualBox cell5 resval5Tail136 resval5Tail140 136 4 80 (by decide +kernel) resval5H140
theorem resval5H132 : resval5Tail132=hornerBox Q residualBox cell5 132 88 :=
  hornerChunk_step Q residualBox cell5 resval5Tail132 resval5Tail136 132 4 84 (by decide +kernel) resval5H136
theorem resval5H128 : resval5Tail128=hornerBox Q residualBox cell5 128 92 :=
  hornerChunk_step Q residualBox cell5 resval5Tail128 resval5Tail132 128 4 88 (by decide +kernel) resval5H132
theorem resval5H124 : resval5Tail124=hornerBox Q residualBox cell5 124 96 :=
  hornerChunk_step Q residualBox cell5 resval5Tail124 resval5Tail128 124 4 92 (by decide +kernel) resval5H128
theorem resval5H120 : resval5Tail120=hornerBox Q residualBox cell5 120 100 :=
  hornerChunk_step Q residualBox cell5 resval5Tail120 resval5Tail124 120 4 96 (by decide +kernel) resval5H124
theorem resval5H116 : resval5Tail116=hornerBox Q residualBox cell5 116 104 :=
  hornerChunk_step Q residualBox cell5 resval5Tail116 resval5Tail120 116 4 100 (by decide +kernel) resval5H120
theorem resval5H112 : resval5Tail112=hornerBox Q residualBox cell5 112 108 :=
  hornerChunk_step Q residualBox cell5 resval5Tail112 resval5Tail116 112 4 104 (by decide +kernel) resval5H116
theorem resval5H108 : resval5Tail108=hornerBox Q residualBox cell5 108 112 :=
  hornerChunk_step Q residualBox cell5 resval5Tail108 resval5Tail112 108 4 108 (by decide +kernel) resval5H112
theorem resval5H104 : resval5Tail104=hornerBox Q residualBox cell5 104 116 :=
  hornerChunk_step Q residualBox cell5 resval5Tail104 resval5Tail108 104 4 112 (by decide +kernel) resval5H108
theorem resval5H100 : resval5Tail100=hornerBox Q residualBox cell5 100 120 :=
  hornerChunk_step Q residualBox cell5 resval5Tail100 resval5Tail104 100 4 116 (by decide +kernel) resval5H104
theorem resval5H96 : resval5Tail96=hornerBox Q residualBox cell5 96 124 :=
  hornerChunk_step Q residualBox cell5 resval5Tail96 resval5Tail100 96 4 120 (by decide +kernel) resval5H100
theorem resval5H92 : resval5Tail92=hornerBox Q residualBox cell5 92 128 :=
  hornerChunk_step Q residualBox cell5 resval5Tail92 resval5Tail96 92 4 124 (by decide +kernel) resval5H96
theorem resval5H88 : resval5Tail88=hornerBox Q residualBox cell5 88 132 :=
  hornerChunk_step Q residualBox cell5 resval5Tail88 resval5Tail92 88 4 128 (by decide +kernel) resval5H92
theorem resval5H84 : resval5Tail84=hornerBox Q residualBox cell5 84 136 :=
  hornerChunk_step Q residualBox cell5 resval5Tail84 resval5Tail88 84 4 132 (by decide +kernel) resval5H88
theorem resval5H80 : resval5Tail80=hornerBox Q residualBox cell5 80 140 :=
  hornerChunk_step Q residualBox cell5 resval5Tail80 resval5Tail84 80 4 136 (by decide +kernel) resval5H84
theorem resval5H76 : resval5Tail76=hornerBox Q residualBox cell5 76 144 :=
  hornerChunk_step Q residualBox cell5 resval5Tail76 resval5Tail80 76 4 140 (by decide +kernel) resval5H80
theorem resval5H72 : resval5Tail72=hornerBox Q residualBox cell5 72 148 :=
  hornerChunk_step Q residualBox cell5 resval5Tail72 resval5Tail76 72 4 144 (by decide +kernel) resval5H76
theorem resval5H68 : resval5Tail68=hornerBox Q residualBox cell5 68 152 :=
  hornerChunk_step Q residualBox cell5 resval5Tail68 resval5Tail72 68 4 148 (by decide +kernel) resval5H72
theorem resval5H64 : resval5Tail64=hornerBox Q residualBox cell5 64 156 :=
  hornerChunk_step Q residualBox cell5 resval5Tail64 resval5Tail68 64 4 152 (by decide +kernel) resval5H68
theorem resval5H60 : resval5Tail60=hornerBox Q residualBox cell5 60 160 :=
  hornerChunk_step Q residualBox cell5 resval5Tail60 resval5Tail64 60 4 156 (by decide +kernel) resval5H64
theorem resval5H56 : resval5Tail56=hornerBox Q residualBox cell5 56 164 :=
  hornerChunk_step Q residualBox cell5 resval5Tail56 resval5Tail60 56 4 160 (by decide +kernel) resval5H60
theorem resval5H52 : resval5Tail52=hornerBox Q residualBox cell5 52 168 :=
  hornerChunk_step Q residualBox cell5 resval5Tail52 resval5Tail56 52 4 164 (by decide +kernel) resval5H56
theorem resval5H48 : resval5Tail48=hornerBox Q residualBox cell5 48 172 :=
  hornerChunk_step Q residualBox cell5 resval5Tail48 resval5Tail52 48 4 168 (by decide +kernel) resval5H52
theorem resval5H44 : resval5Tail44=hornerBox Q residualBox cell5 44 176 :=
  hornerChunk_step Q residualBox cell5 resval5Tail44 resval5Tail48 44 4 172 (by decide +kernel) resval5H48
theorem resval5H40 : resval5Tail40=hornerBox Q residualBox cell5 40 180 :=
  hornerChunk_step Q residualBox cell5 resval5Tail40 resval5Tail44 40 4 176 (by decide +kernel) resval5H44
theorem resval5H36 : resval5Tail36=hornerBox Q residualBox cell5 36 184 :=
  hornerChunk_step Q residualBox cell5 resval5Tail36 resval5Tail40 36 4 180 (by decide +kernel) resval5H40
theorem resval5H32 : resval5Tail32=hornerBox Q residualBox cell5 32 188 :=
  hornerChunk_step Q residualBox cell5 resval5Tail32 resval5Tail36 32 4 184 (by decide +kernel) resval5H36
theorem resval5H28 : resval5Tail28=hornerBox Q residualBox cell5 28 192 :=
  hornerChunk_step Q residualBox cell5 resval5Tail28 resval5Tail32 28 4 188 (by decide +kernel) resval5H32
theorem resval5H24 : resval5Tail24=hornerBox Q residualBox cell5 24 196 :=
  hornerChunk_step Q residualBox cell5 resval5Tail24 resval5Tail28 24 4 192 (by decide +kernel) resval5H28
theorem resval5H20 : resval5Tail20=hornerBox Q residualBox cell5 20 200 :=
  hornerChunk_step Q residualBox cell5 resval5Tail20 resval5Tail24 20 4 196 (by decide +kernel) resval5H24
theorem resval5H16 : resval5Tail16=hornerBox Q residualBox cell5 16 204 :=
  hornerChunk_step Q residualBox cell5 resval5Tail16 resval5Tail20 16 4 200 (by decide +kernel) resval5H20
theorem resval5H12 : resval5Tail12=hornerBox Q residualBox cell5 12 208 :=
  hornerChunk_step Q residualBox cell5 resval5Tail12 resval5Tail16 12 4 204 (by decide +kernel) resval5H16
theorem resval5H8 : resval5Tail8=hornerBox Q residualBox cell5 8 212 :=
  hornerChunk_step Q residualBox cell5 resval5Tail8 resval5Tail12 8 4 208 (by decide +kernel) resval5H12
theorem resval5H4 : resval5Tail4=hornerBox Q residualBox cell5 4 216 :=
  hornerChunk_step Q residualBox cell5 resval5Tail4 resval5Tail8 4 4 212 (by decide +kernel) resval5H8
theorem resval5H0 : resval5=hornerBox Q residualBox cell5 0 220 :=
  hornerChunk_step Q residualBox cell5 resval5 resval5Tail4 0 4 216 (by decide +kernel) resval5H4
theorem resval5_eq : resval5=hornerBox Q residualBox cell5 0 220 := resval5H0
def polyval5Tail5 : Box := ⟨5270878099530575833855351339255201640597465267632539031568,3791209641301331413068580616067640202388752959204632838219⟩
def polyval5Tail9 : Box := ⟨5795389735252616257385723438106972436264413327760525750413,3855911523388715365300919697441709199857132366430022842486⟩
def polyval5Tail13 : Box := ⟨6372098401227269765417936109577861538559815686478352746475,3906728918573534987576287791379735836475604957935594484018⟩
def polyval5Tail17 : Box := ⟨7006196285482117546265796061786229631489786819879538739683,3940958739595213546139050137211934175712250563117874001328⟩
def polyval5Tail21 : Box := ⟨7703394282368607468647951500076921162940737036754836296041,3955543008291084649818492753407552964886712367810120941202⟩
def polyval5Tail25 : Box := ⟨8469971586807438970570537351221553382978978531522018896218,3947027938288346964406601092316493852273168403307197899917⟩
def polyval5Tail29 : Box := ⟨9312832246627116909475136921927885705145581543708888560160,3911518597917564012341016154350691819216017727780855120355⟩
def polyval5Tail33 : Box := ⟨10239567342693804398829969786569076163075276654234888602553,3844628674722129880206801323775295153763420309885088582855⟩
def polyval5Tail37 : Box := ⟨11258523356687235695306455472513216283109358926194202491765,3741424828960331847149701729244007457248322013158023094023⟩
def polyval5Tail41 : Box := ⟨12378877342265297974268256359997279916095755144963170134734,3596365070854200038478116397860362152372322997148030119881⟩
def polyval5Tail45 : Box := ⟨13610719576633562458927470791262784641439631576252464789096,3403230538349078072680244279340679623231974718338969631865⟩
def polyval5Tail49 : Box := ⟨14965144436907037833509833097468090759500300801776774485921,3155049988273637497901283963278135929821718495836897097050⟩
def polyval5Tail53 : Box := ⟨16454350319726608099553404282433902701451930882001596688353,2844016243439010673106113916589863521428646766714193228254⟩
def polyval5Tail57 : Box := ⟨18091749504039148940736513127108294634256215395169446485472,2461393760735469003516229920629178711301288517483803428479⟩
def polyval5Tail61 : Box := ⟨19892088946501730546378794905220696879169386071534642925199,1997416399957835192962343046616427630309809304332659615253⟩
def polyval5Tail65 : Box := ⟨21871583097438016662668433138053157983311649733255429144402,1441174379126292038016728234018328203240715789712418744517⟩
def polyval5Tail69 : Box := ⟨24048059974727619080787259380773345808229010125029598197630,780489295017102893549384919932175779427281510351056782903⟩
def polyval5Tail73 : Box := ⟨26468750000000000000000000000000000000000000000000000000000,2⟩
theorem polyval5H73 : polyval5Tail73=hornerBox Q polyBox cell5 73 1 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail73 zero 73 1 0 (by decide +kernel) rfl
theorem polyval5H69 : polyval5Tail69=hornerBox Q polyBox cell5 69 5 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail69 polyval5Tail73 69 4 1 (by decide +kernel) polyval5H73
theorem polyval5H65 : polyval5Tail65=hornerBox Q polyBox cell5 65 9 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail65 polyval5Tail69 65 4 5 (by decide +kernel) polyval5H69
theorem polyval5H61 : polyval5Tail61=hornerBox Q polyBox cell5 61 13 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail61 polyval5Tail65 61 4 9 (by decide +kernel) polyval5H65
theorem polyval5H57 : polyval5Tail57=hornerBox Q polyBox cell5 57 17 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail57 polyval5Tail61 57 4 13 (by decide +kernel) polyval5H61
theorem polyval5H53 : polyval5Tail53=hornerBox Q polyBox cell5 53 21 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail53 polyval5Tail57 53 4 17 (by decide +kernel) polyval5H57
theorem polyval5H49 : polyval5Tail49=hornerBox Q polyBox cell5 49 25 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail49 polyval5Tail53 49 4 21 (by decide +kernel) polyval5H53
theorem polyval5H45 : polyval5Tail45=hornerBox Q polyBox cell5 45 29 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail45 polyval5Tail49 45 4 25 (by decide +kernel) polyval5H49
theorem polyval5H41 : polyval5Tail41=hornerBox Q polyBox cell5 41 33 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail41 polyval5Tail45 41 4 29 (by decide +kernel) polyval5H45
theorem polyval5H37 : polyval5Tail37=hornerBox Q polyBox cell5 37 37 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail37 polyval5Tail41 37 4 33 (by decide +kernel) polyval5H41
theorem polyval5H33 : polyval5Tail33=hornerBox Q polyBox cell5 33 41 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail33 polyval5Tail37 33 4 37 (by decide +kernel) polyval5H37
theorem polyval5H29 : polyval5Tail29=hornerBox Q polyBox cell5 29 45 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail29 polyval5Tail33 29 4 41 (by decide +kernel) polyval5H33
theorem polyval5H25 : polyval5Tail25=hornerBox Q polyBox cell5 25 49 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail25 polyval5Tail29 25 4 45 (by decide +kernel) polyval5H29
theorem polyval5H21 : polyval5Tail21=hornerBox Q polyBox cell5 21 53 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail21 polyval5Tail25 21 4 49 (by decide +kernel) polyval5H25
theorem polyval5H17 : polyval5Tail17=hornerBox Q polyBox cell5 17 57 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail17 polyval5Tail21 17 4 53 (by decide +kernel) polyval5H21
theorem polyval5H13 : polyval5Tail13=hornerBox Q polyBox cell5 13 61 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail13 polyval5Tail17 13 4 57 (by decide +kernel) polyval5H17
theorem polyval5H9 : polyval5Tail9=hornerBox Q polyBox cell5 9 65 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail9 polyval5Tail13 9 4 61 (by decide +kernel) polyval5H13
theorem polyval5H5 : polyval5Tail5=hornerBox Q polyBox cell5 5 69 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail5 polyval5Tail9 5 4 65 (by decide +kernel) polyval5H9
theorem polyval5H1 : polyval5=hornerBox Q polyBox cell5 1 73 :=
  hornerChunk_step Q polyBox cell5 polyval5 polyval5Tail5 1 4 69 (by decide +kernel) polyval5H5
theorem polyval5_eq : polyval5=hornerBox Q polyBox cell5 1 73 := polyval5H1
theorem polyval5_upper : 5*(polyval5.center+polyval5.radius)<Q := by decide +kernel
theorem resval5_pos : 0<(resval5).center-(resval5).radius := by decide +kernel
theorem polyval5_pos : 0<(polyval5).center-(polyval5).radius := by decide +kernel
def cell6 : Box := ⟨988281250000000000000000000000000000000000000000000000000000,3906250000000000000000000000000000000000000000000000000002⟩
def resval6 : Box := ⟨71517447340384481669301923927654510518788338117557749288,14192967814698806140119485514176769652236422350133797644⟩
def polyval6 : Box := ⟨15027230458606614425068589191803713292824051415040397669288,3721851309925123839169300412713484644293570980031871229480⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-37401997815967692957875708264174155285810505916776385250,13791552136558483482577061939505479001683185461822208215⟩
def resval6Tail8 : Box := ⟨-39207860714818442905413537394569348570876433706452930127,13617278636763963148193221957136128475917676531385032076⟩
def resval6Tail12 : Box := ⟨-41100861332467388882545330589116525080531441530574904523,13407816290091437660536480413637912639729228943760373225⟩
def resval6Tail16 : Box := ⟨-43085258191663680887135639642968650973290221654575844490,13160612095434421928897397960638331383983131018514994858⟩
def resval6Tail20 : Box := ⟨-45165464013663415686102384910163619876309259504698012529,12872963303522926422255517222419196445918659790179095335⟩
def resval6Tail24 : Box := ⟨-47346104565394400432954956575817560149093706263246816452,12542008610889605458355084615276604491356603524776027670⟩
def resval6Tail28 : Box := ⟨-49632028951127734139804639819580588074955554759575109463,12164719610205902974774409339621794574743854610495575532⟩
def resval6Tail32 : Box := ⟨-52028320395466130721638565438065185033740643573535731280,11737891799460225063232793478714078751201407092572041850⟩
def resval6Tail36 : Box := ⟨-54540307546942829268483040927450994757507496761363629695,11258135127637644605422316086777945765015754481350032250⟩
def resval6Tail40 : Box := ⟨-57173576327371245678133682467729526606268568378762650164,10721864053585397257359365750463343602672575938659242415⟩
def resval6Tail44 : Box := ⟨-59933982353294854381856907710618635011646785198181697772,10125287093593002756499884421078464737582889057570243309⟩
def resval6Tail48 : Box := ⟨-62827663957158957459386280325385113816340328210758135619,9464395832003525079720769691549628680194023088060002926⟩
def resval6Tail52 : Box := ⟨-65861055837159603604089084187160531540006248804951949171,8734953367900649142378738487646152669557255659483394166⟩
def resval6Tail56 : Box := ⟨-69040903366122907286322943496007236463107983734381435245,7932482169581995692283671802255336214563230907617556069⟩
def resval6Tail60 : Box := ⟨-72374277591231897434054857482934659284720190886715077930,7052251307129175458675205909216841104858813008811844300⟩
def resval6Tail64 : Box := ⟨-75868590955550551008111796259675840328613611105422259058,6089263031687877568932174012769635770941592850613257621⟩
def resval6Tail68 : Box := ⟨-79531571843757823656879134723556301497705874986672546547,5038235609754135386972780499148986217873809814616153991⟩
def resval6Tail72 : Box := ⟨743085291707578225255353867579389713906753149135612088683,1061582279821310702123724975261946586957119659400959751⟩
def resval6Tail76 : Box := ⟨-484198787088318585493483444433793892941837208098100774,180714808820609543927151410192052717113983971663664899⟩
def resval6Tail80 : Box := ⟨-507552670508598408551828487388962107919215474778035874,178528094405456968545613563698992919685673320521153799⟩
def resval6Tail84 : Box := ⟨-532057896070364593116881866448074181717484873895984314,175888275617586298933463469612066560409025798011633850⟩
def resval6Tail88 : Box := ⟨-557746263263098249402620720536405032428817659001261320,172762167315544927850735029280006409903689900407317966⟩
def resval6Tail92 : Box := ⟨-584674894371148748765879606285317421943697961944765263,169114854748542082120581230087975510245256639192185542⟩
def resval6Tail96 : Box := ⟨-612903670762310253082418911365521805360980014784139922,164909372993873843340397094031492700027963440461679824⟩
def resval6Tail100 : Box := ⟨-642495364946272279966040424791251674994553998146697011,160106596335102840311184204407995130426763212098437724⟩
def resval6Tail104 : Box := ⟨-673515780161694280900959152812704935949040179398960920,154665121950605140682413773156569452785052423183652934⟩
def resval6Tail108 : Box := ⟨-706033896703284841627250449653750887430040251520589061,148541147604494915559058716212371404037125092459414361⟩
def resval6Tail112 : Box := ⟨-740122025313721961047690190274597595107426813964753747,141688343038163724991435076171497496043639574463969988⟩
def resval6Tail116 : Box := ⟨-775855967981511683298324242016906305321483581405099805,134057714745730822505561484795548773930868280231589420⟩
def resval6Tail120 : Box := ⟨-813315186502352293948436647068559407112213499818332518,125597463801009771751444477797497951458753212158275983⟩
def resval6Tail124 : Box := ⟨-852582979178835058808439075897141789605922762218531416,116252836387135160740898910783140356562565123690539057⟩
def resval6Tail128 : Box := ⟨-893746666051409788518771131569179348282441892234557343,105965966662723739398384886135542477628965994641279755⟩
def resval6Tail132 : Box := ⟨-936897783072521568405485439813363793210975516553920278,94675711580326507152610379005054581809558846981429341⟩
def resval6Tail136 : Box := ⟨-982132285662295489092114953632260164707386105813200206,82317477253204253974125713767896389663807232791955317⟩
def resval6Tail140 : Box := ⟨-1029550816709507272697786127791126941839552003203120139,68823031712389369379634605565505308188622184119500438⟩
def resval6Tail144 : Box := ⟨-1113045479534218305458475882562243423177192709377366317,52060124186888053325660046307862587058046039152963465⟩
def resval6Tail148 : Box := ⟨191286726332449490155032358911718251338176113158,61752881805868322495767140713853295174803652484⟩
def resval6Tail152 : Box := ⟨200471156589193152816275624202621664025530576640,60581967194925367996386917893768272013986863518⟩
def resval6Tail156 : Box := ⟨210150133793549278939808117492262093722940851475,59222757536546700466556141473890686510007904938⟩
def resval6Tail160 : Box := ⟨220296423966782617984108875158543842717347691674,57661386888799189182709675708551074042104038643⟩
def resval6Tail164 : Box := ⟨230932588700038648542743210798076719606052963946,55883743241159228231559290696109349185041996481⟩
def resval6Tail168 : Box := ⟨242082279700294371510252243685394964954913459146,53874894573700442968948409301576584812723019312⟩
def resval6Tail172 : Box := ⟨253770290606376201793990602743063389547680465836,51619044831486102490050683760097155571244392177⟩
def resval6Tail176 : Box := ⟨266022612122511006144494235905739639278933009614,49099487647360967943769896280846179531072160846⟩
def resval6Tail180 : Box := ⟨278866489814020139319761489374887954271840619548,46298557685086630386633178153383968981905246040⟩
def resval6Tail184 : Box := ⟨292330484693456420580362064676146173145344450740,43197579483288951309922084362151572543225597365⟩
def resval6Tail188 : Box := ⟨306444536731909491351410969310174912511905584684,39776813674774106252512773821718496358645688167⟩
def resval6Tail192 : Box := ⟨321240031436710046055033089433186698307313670950,36015400449560857256026237237032069197366278917⟩
def resval6Tail196 : Box := ⟨336749869643582200644239591539676693126738829243,31891300123463164210962520828177390327480318503⟩
def resval6Tail200 : Box := ⟨353008540678441252337276101372596411773353426101,27381230667224239688083305025147292419591576545⟩
def resval6Tail204 : Box := ⟨370052199051527205227977996555344114638453561992,22460602044035068899018897863202525897058370367⟩
def resval6Tail208 : Box := ⟨387918744854427729519797694103473696988847139103,17103447195749844400071007974737782051254880413⟩
def resval6Tail212 : Box := ⟨406647908060564686394012842558101751468146300017,11282349508004699343002552175984746711985856612⟩
def resval6Tail216 : Box := ⟨426282328231183916031422443199284287538884171149,4968284754045358426226330476119610676739737112⟩
theorem resval6H216 : resval6Tail216=hornerBox Q residualBox cell6 216 4 :=
  hornerChunk_step Q residualBox cell6 resval6Tail216 zero 216 4 0 (by decide +kernel) rfl
theorem resval6H212 : resval6Tail212=hornerBox Q residualBox cell6 212 8 :=
  hornerChunk_step Q residualBox cell6 resval6Tail212 resval6Tail216 212 4 4 (by decide +kernel) resval6H216
theorem resval6H208 : resval6Tail208=hornerBox Q residualBox cell6 208 12 :=
  hornerChunk_step Q residualBox cell6 resval6Tail208 resval6Tail212 208 4 8 (by decide +kernel) resval6H212
theorem resval6H204 : resval6Tail204=hornerBox Q residualBox cell6 204 16 :=
  hornerChunk_step Q residualBox cell6 resval6Tail204 resval6Tail208 204 4 12 (by decide +kernel) resval6H208
theorem resval6H200 : resval6Tail200=hornerBox Q residualBox cell6 200 20 :=
  hornerChunk_step Q residualBox cell6 resval6Tail200 resval6Tail204 200 4 16 (by decide +kernel) resval6H204
theorem resval6H196 : resval6Tail196=hornerBox Q residualBox cell6 196 24 :=
  hornerChunk_step Q residualBox cell6 resval6Tail196 resval6Tail200 196 4 20 (by decide +kernel) resval6H200
theorem resval6H192 : resval6Tail192=hornerBox Q residualBox cell6 192 28 :=
  hornerChunk_step Q residualBox cell6 resval6Tail192 resval6Tail196 192 4 24 (by decide +kernel) resval6H196
theorem resval6H188 : resval6Tail188=hornerBox Q residualBox cell6 188 32 :=
  hornerChunk_step Q residualBox cell6 resval6Tail188 resval6Tail192 188 4 28 (by decide +kernel) resval6H192
theorem resval6H184 : resval6Tail184=hornerBox Q residualBox cell6 184 36 :=
  hornerChunk_step Q residualBox cell6 resval6Tail184 resval6Tail188 184 4 32 (by decide +kernel) resval6H188
theorem resval6H180 : resval6Tail180=hornerBox Q residualBox cell6 180 40 :=
  hornerChunk_step Q residualBox cell6 resval6Tail180 resval6Tail184 180 4 36 (by decide +kernel) resval6H184
theorem resval6H176 : resval6Tail176=hornerBox Q residualBox cell6 176 44 :=
  hornerChunk_step Q residualBox cell6 resval6Tail176 resval6Tail180 176 4 40 (by decide +kernel) resval6H180
theorem resval6H172 : resval6Tail172=hornerBox Q residualBox cell6 172 48 :=
  hornerChunk_step Q residualBox cell6 resval6Tail172 resval6Tail176 172 4 44 (by decide +kernel) resval6H176
theorem resval6H168 : resval6Tail168=hornerBox Q residualBox cell6 168 52 :=
  hornerChunk_step Q residualBox cell6 resval6Tail168 resval6Tail172 168 4 48 (by decide +kernel) resval6H172
theorem resval6H164 : resval6Tail164=hornerBox Q residualBox cell6 164 56 :=
  hornerChunk_step Q residualBox cell6 resval6Tail164 resval6Tail168 164 4 52 (by decide +kernel) resval6H168
theorem resval6H160 : resval6Tail160=hornerBox Q residualBox cell6 160 60 :=
  hornerChunk_step Q residualBox cell6 resval6Tail160 resval6Tail164 160 4 56 (by decide +kernel) resval6H164
theorem resval6H156 : resval6Tail156=hornerBox Q residualBox cell6 156 64 :=
  hornerChunk_step Q residualBox cell6 resval6Tail156 resval6Tail160 156 4 60 (by decide +kernel) resval6H160
theorem resval6H152 : resval6Tail152=hornerBox Q residualBox cell6 152 68 :=
  hornerChunk_step Q residualBox cell6 resval6Tail152 resval6Tail156 152 4 64 (by decide +kernel) resval6H156
theorem resval6H148 : resval6Tail148=hornerBox Q residualBox cell6 148 72 :=
  hornerChunk_step Q residualBox cell6 resval6Tail148 resval6Tail152 148 4 68 (by decide +kernel) resval6H152
theorem resval6H144 : resval6Tail144=hornerBox Q residualBox cell6 144 76 :=
  hornerChunk_step Q residualBox cell6 resval6Tail144 resval6Tail148 144 4 72 (by decide +kernel) resval6H148
theorem resval6H140 : resval6Tail140=hornerBox Q residualBox cell6 140 80 :=
  hornerChunk_step Q residualBox cell6 resval6Tail140 resval6Tail144 140 4 76 (by decide +kernel) resval6H144
theorem resval6H136 : resval6Tail136=hornerBox Q residualBox cell6 136 84 :=
  hornerChunk_step Q residualBox cell6 resval6Tail136 resval6Tail140 136 4 80 (by decide +kernel) resval6H140
theorem resval6H132 : resval6Tail132=hornerBox Q residualBox cell6 132 88 :=
  hornerChunk_step Q residualBox cell6 resval6Tail132 resval6Tail136 132 4 84 (by decide +kernel) resval6H136
theorem resval6H128 : resval6Tail128=hornerBox Q residualBox cell6 128 92 :=
  hornerChunk_step Q residualBox cell6 resval6Tail128 resval6Tail132 128 4 88 (by decide +kernel) resval6H132
theorem resval6H124 : resval6Tail124=hornerBox Q residualBox cell6 124 96 :=
  hornerChunk_step Q residualBox cell6 resval6Tail124 resval6Tail128 124 4 92 (by decide +kernel) resval6H128
theorem resval6H120 : resval6Tail120=hornerBox Q residualBox cell6 120 100 :=
  hornerChunk_step Q residualBox cell6 resval6Tail120 resval6Tail124 120 4 96 (by decide +kernel) resval6H124
theorem resval6H116 : resval6Tail116=hornerBox Q residualBox cell6 116 104 :=
  hornerChunk_step Q residualBox cell6 resval6Tail116 resval6Tail120 116 4 100 (by decide +kernel) resval6H120
theorem resval6H112 : resval6Tail112=hornerBox Q residualBox cell6 112 108 :=
  hornerChunk_step Q residualBox cell6 resval6Tail112 resval6Tail116 112 4 104 (by decide +kernel) resval6H116
theorem resval6H108 : resval6Tail108=hornerBox Q residualBox cell6 108 112 :=
  hornerChunk_step Q residualBox cell6 resval6Tail108 resval6Tail112 108 4 108 (by decide +kernel) resval6H112
theorem resval6H104 : resval6Tail104=hornerBox Q residualBox cell6 104 116 :=
  hornerChunk_step Q residualBox cell6 resval6Tail104 resval6Tail108 104 4 112 (by decide +kernel) resval6H108
theorem resval6H100 : resval6Tail100=hornerBox Q residualBox cell6 100 120 :=
  hornerChunk_step Q residualBox cell6 resval6Tail100 resval6Tail104 100 4 116 (by decide +kernel) resval6H104
theorem resval6H96 : resval6Tail96=hornerBox Q residualBox cell6 96 124 :=
  hornerChunk_step Q residualBox cell6 resval6Tail96 resval6Tail100 96 4 120 (by decide +kernel) resval6H100
theorem resval6H92 : resval6Tail92=hornerBox Q residualBox cell6 92 128 :=
  hornerChunk_step Q residualBox cell6 resval6Tail92 resval6Tail96 92 4 124 (by decide +kernel) resval6H96
theorem resval6H88 : resval6Tail88=hornerBox Q residualBox cell6 88 132 :=
  hornerChunk_step Q residualBox cell6 resval6Tail88 resval6Tail92 88 4 128 (by decide +kernel) resval6H92
theorem resval6H84 : resval6Tail84=hornerBox Q residualBox cell6 84 136 :=
  hornerChunk_step Q residualBox cell6 resval6Tail84 resval6Tail88 84 4 132 (by decide +kernel) resval6H88
theorem resval6H80 : resval6Tail80=hornerBox Q residualBox cell6 80 140 :=
  hornerChunk_step Q residualBox cell6 resval6Tail80 resval6Tail84 80 4 136 (by decide +kernel) resval6H84
theorem resval6H76 : resval6Tail76=hornerBox Q residualBox cell6 76 144 :=
  hornerChunk_step Q residualBox cell6 resval6Tail76 resval6Tail80 76 4 140 (by decide +kernel) resval6H80
theorem resval6H72 : resval6Tail72=hornerBox Q residualBox cell6 72 148 :=
  hornerChunk_step Q residualBox cell6 resval6Tail72 resval6Tail76 72 4 144 (by decide +kernel) resval6H76
theorem resval6H68 : resval6Tail68=hornerBox Q residualBox cell6 68 152 :=
  hornerChunk_step Q residualBox cell6 resval6Tail68 resval6Tail72 68 4 148 (by decide +kernel) resval6H72
theorem resval6H64 : resval6Tail64=hornerBox Q residualBox cell6 64 156 :=
  hornerChunk_step Q residualBox cell6 resval6Tail64 resval6Tail68 64 4 152 (by decide +kernel) resval6H68
theorem resval6H60 : resval6Tail60=hornerBox Q residualBox cell6 60 160 :=
  hornerChunk_step Q residualBox cell6 resval6Tail60 resval6Tail64 60 4 156 (by decide +kernel) resval6H64
theorem resval6H56 : resval6Tail56=hornerBox Q residualBox cell6 56 164 :=
  hornerChunk_step Q residualBox cell6 resval6Tail56 resval6Tail60 56 4 160 (by decide +kernel) resval6H60
theorem resval6H52 : resval6Tail52=hornerBox Q residualBox cell6 52 168 :=
  hornerChunk_step Q residualBox cell6 resval6Tail52 resval6Tail56 52 4 164 (by decide +kernel) resval6H56
theorem resval6H48 : resval6Tail48=hornerBox Q residualBox cell6 48 172 :=
  hornerChunk_step Q residualBox cell6 resval6Tail48 resval6Tail52 48 4 168 (by decide +kernel) resval6H52
theorem resval6H44 : resval6Tail44=hornerBox Q residualBox cell6 44 176 :=
  hornerChunk_step Q residualBox cell6 resval6Tail44 resval6Tail48 44 4 172 (by decide +kernel) resval6H48
theorem resval6H40 : resval6Tail40=hornerBox Q residualBox cell6 40 180 :=
  hornerChunk_step Q residualBox cell6 resval6Tail40 resval6Tail44 40 4 176 (by decide +kernel) resval6H44
theorem resval6H36 : resval6Tail36=hornerBox Q residualBox cell6 36 184 :=
  hornerChunk_step Q residualBox cell6 resval6Tail36 resval6Tail40 36 4 180 (by decide +kernel) resval6H40
theorem resval6H32 : resval6Tail32=hornerBox Q residualBox cell6 32 188 :=
  hornerChunk_step Q residualBox cell6 resval6Tail32 resval6Tail36 32 4 184 (by decide +kernel) resval6H36
theorem resval6H28 : resval6Tail28=hornerBox Q residualBox cell6 28 192 :=
  hornerChunk_step Q residualBox cell6 resval6Tail28 resval6Tail32 28 4 188 (by decide +kernel) resval6H32
theorem resval6H24 : resval6Tail24=hornerBox Q residualBox cell6 24 196 :=
  hornerChunk_step Q residualBox cell6 resval6Tail24 resval6Tail28 24 4 192 (by decide +kernel) resval6H28
theorem resval6H20 : resval6Tail20=hornerBox Q residualBox cell6 20 200 :=
  hornerChunk_step Q residualBox cell6 resval6Tail20 resval6Tail24 20 4 196 (by decide +kernel) resval6H24
theorem resval6H16 : resval6Tail16=hornerBox Q residualBox cell6 16 204 :=
  hornerChunk_step Q residualBox cell6 resval6Tail16 resval6Tail20 16 4 200 (by decide +kernel) resval6H20
theorem resval6H12 : resval6Tail12=hornerBox Q residualBox cell6 12 208 :=
  hornerChunk_step Q residualBox cell6 resval6Tail12 resval6Tail16 12 4 204 (by decide +kernel) resval6H16
theorem resval6H8 : resval6Tail8=hornerBox Q residualBox cell6 8 212 :=
  hornerChunk_step Q residualBox cell6 resval6Tail8 resval6Tail12 8 4 208 (by decide +kernel) resval6H12
theorem resval6H4 : resval6Tail4=hornerBox Q residualBox cell6 4 216 :=
  hornerChunk_step Q residualBox cell6 resval6Tail4 resval6Tail8 4 4 212 (by decide +kernel) resval6H8
theorem resval6H0 : resval6=hornerBox Q residualBox cell6 0 220 :=
  hornerChunk_step Q residualBox cell6 resval6 resval6Tail4 0 4 216 (by decide +kernel) resval6H4
theorem resval6_eq : resval6=hornerBox Q residualBox cell6 0 220 := resval6H0
def polyval6Tail5 : Box := ⟨11862139714817011384989715591396785327236313880395045555071,3650562900941185045205514328217748051464170256712530389325⟩
def polyval6Tail9 : Box := ⟨12434855536107638927972410788479860108545148115684989069858,3572235315006715843351170330012602611247243730785127314473⟩
def polyval6Tail13 : Box := ⟨13035224663748035702129602245565819784262963659821871281376,3482012498206402327920545066031730515337117187771401686817⟩
def polyval6Tail17 : Box := ⟨13664580303581345856713738937721180698207452154959486360759,3379061542684301841917186879127526705906613359092988886680⟩
def polyval6Tail21 : Box := ⟨14324321957588479031448113819880947536450336381268805003636,3262501100984543572826310703897190044596052199059052416753⟩
def polyval6Tail25 : Box := ⟨15015916697483511462168887793471782079341655109767153457182,3131398769681403270816320939543246704617792030414994719286⟩
def polyval6Tail29 : Box := ⟨15740902426890413304328866175508929044216695311170871078486,2984768353328606904191153388402682261730821315460814508450⟩
def polyval6Tail33 : Box := ⟨16500891301189011469838474920055279182958529732555886752880,2821566987674868949457790241894525702085059304352818021703⟩
def polyval6Tail37 : Box := ⟨17297573312475166131750073709192807768502575021146197034118,2640692115072716595085909455017832453184494821806882055957⟩
def polyval6Tail41 : Box := ⟨18132720047606948312357250070109015712085569089475601763071,2440978304660284675204728761217322837285942954648395750523⟩
def polyval6Tail45 : Box := ⟨19008188627693609419607382968369759836599578697968870517436,2221193909528455903947626230280524552475022464930037366849⟩
def polyval6Tail49 : Box := ⟨19925925837787609418615627230650155214502299655347181785329,1980037552700384829147203190766374809889167718498715744527⟩
def polyval6Tail53 : Box := ⟨20887972455962926080305030193026508678415259005729937359166,1716134433346205598160775612966286327760880427354102238735⟩
def polyval6Tail57 : Box := ⟨21896467791406244314275175524165155731084847332604264189228,1428032444231661033603224159314859612014120039385435415772⟩
def polyval6Tail61 : Box := ⟨22953654441612412853207096699619675119837870525410958579414,1114198090954536055491277242049574668020239888689061978697⟩
def polyval6Tail65 : Box := ⟨24061883279267615255991434513901647324278216621389645955474,773012203055604404014371439442798610094644437101344963762⟩
def polyval6Tail69 : Box := ⟨25223618720653707565683207134789980383285934335448766114644,402765423201215045090879229986873416387415748973776141021⟩
def polyval6Tail73 : Box := ⟨26468750000000000000000000000000000000000000000000000000000,2⟩
theorem polyval6H73 : polyval6Tail73=hornerBox Q polyBox cell6 73 1 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail73 zero 73 1 0 (by decide +kernel) rfl
theorem polyval6H69 : polyval6Tail69=hornerBox Q polyBox cell6 69 5 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail69 polyval6Tail73 69 4 1 (by decide +kernel) polyval6H73
theorem polyval6H65 : polyval6Tail65=hornerBox Q polyBox cell6 65 9 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail65 polyval6Tail69 65 4 5 (by decide +kernel) polyval6H69
theorem polyval6H61 : polyval6Tail61=hornerBox Q polyBox cell6 61 13 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail61 polyval6Tail65 61 4 9 (by decide +kernel) polyval6H65
theorem polyval6H57 : polyval6Tail57=hornerBox Q polyBox cell6 57 17 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail57 polyval6Tail61 57 4 13 (by decide +kernel) polyval6H61
theorem polyval6H53 : polyval6Tail53=hornerBox Q polyBox cell6 53 21 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail53 polyval6Tail57 53 4 17 (by decide +kernel) polyval6H57
theorem polyval6H49 : polyval6Tail49=hornerBox Q polyBox cell6 49 25 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail49 polyval6Tail53 49 4 21 (by decide +kernel) polyval6H53
theorem polyval6H45 : polyval6Tail45=hornerBox Q polyBox cell6 45 29 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail45 polyval6Tail49 45 4 25 (by decide +kernel) polyval6H49
theorem polyval6H41 : polyval6Tail41=hornerBox Q polyBox cell6 41 33 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail41 polyval6Tail45 41 4 29 (by decide +kernel) polyval6H45
theorem polyval6H37 : polyval6Tail37=hornerBox Q polyBox cell6 37 37 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail37 polyval6Tail41 37 4 33 (by decide +kernel) polyval6H41
theorem polyval6H33 : polyval6Tail33=hornerBox Q polyBox cell6 33 41 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail33 polyval6Tail37 33 4 37 (by decide +kernel) polyval6H37
theorem polyval6H29 : polyval6Tail29=hornerBox Q polyBox cell6 29 45 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail29 polyval6Tail33 29 4 41 (by decide +kernel) polyval6H33
theorem polyval6H25 : polyval6Tail25=hornerBox Q polyBox cell6 25 49 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail25 polyval6Tail29 25 4 45 (by decide +kernel) polyval6H29
theorem polyval6H21 : polyval6Tail21=hornerBox Q polyBox cell6 21 53 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail21 polyval6Tail25 21 4 49 (by decide +kernel) polyval6H25
theorem polyval6H17 : polyval6Tail17=hornerBox Q polyBox cell6 17 57 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail17 polyval6Tail21 17 4 53 (by decide +kernel) polyval6H21
theorem polyval6H13 : polyval6Tail13=hornerBox Q polyBox cell6 13 61 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail13 polyval6Tail17 13 4 57 (by decide +kernel) polyval6H17
theorem polyval6H9 : polyval6Tail9=hornerBox Q polyBox cell6 9 65 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail9 polyval6Tail13 9 4 61 (by decide +kernel) polyval6H13
theorem polyval6H5 : polyval6Tail5=hornerBox Q polyBox cell6 5 69 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail5 polyval6Tail9 5 4 65 (by decide +kernel) polyval6H9
theorem polyval6H1 : polyval6=hornerBox Q polyBox cell6 1 73 :=
  hornerChunk_step Q polyBox cell6 polyval6 polyval6Tail5 1 4 69 (by decide +kernel) polyval6H5
theorem polyval6_eq : polyval6=hornerBox Q polyBox cell6 1 73 := polyval6H1
theorem polyval6_upper : 5*(polyval6.center+polyval6.radius)<Q := by decide +kernel
theorem resval6_pos : 0<(resval6).center-(resval6).radius := by decide +kernel
theorem polyval6_pos : 0<(polyval6).center-(polyval6).radius := by decide +kernel
def cell7 : Box := ⟨996093750000000000000000000000000000000000000000000000000000,3906250000000000000000000000000000000000000000000000000002⟩
def resval7 : Box := ⟨48994668079348779212763539907703407281577829160731649921,23213936411103474265361246658313986554999750846164079702⟩
def polyval7 : Box := ⟨23659291639619695418433489693059777507760672179039473335129,6499145853484594773195481725286196917503812043982591857866⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-59116177931185551599074606509714766484870649518063976977,22035661906137566681587186711340267566983155805501882571⟩
def resval7Tail8 : Box := ⟨-60049009382601429072527924056152444266215995420026157051,21102878804987499552375013021049612400012758866442321763⟩
def resval7Tail12 : Box := ⟨-60996509987718670448955356678264816377488083510418994184,20155378205079156196414388711676506286615099024896582392⟩
def resval7Tail16 : Box := ⟨-61958960998771862605872057843717022982071857308711824716,19192927194030160844926324137070945538462619989980827111⟩
def resval7Tail20 : Box := ⟨-62936598320461364014965328805066121641155776808383992214,18215289872340674120982524492671140221028667175745530722⟩
def resval7Tail24 : Box := ⟨-63929661574370390324101173197638291425063766154538124766,17222226618431647981812725031812625235956199907635512115⟩
def resval7Tail28 : Box := ⟨-64938394163015986844266827908537915434287946015598770260,16213494029786051467030391386869585579631734899155219527⟩
def resval7Tail32 : Box := ⟨-65963043329511943541284810822519993595713832899183952134,15188844863290094770389412501842192552305800389406844984⟩
def resval7Tail36 : Box := ⟨-67003860218168772611840862582391014836802608412405049313,14148027974633265699855423784605813976340750461326088102⟩
def resval7Tail40 : Box := ⟨-68061099936049865392305941108409005599622499230217454151,13090788256752172919316104113360958185723737727856795498⟩
def resval7Tail44 : Box := ⟨-69135021615498930668037307501971023257605018166527214069,12016866577303107643195289015844905471805267004079135809⟩
def resval7Tail48 : Box := ⟨-70225888477654040181016200183656845948758892158935059435,10925999715147998126413383277319180897693766467403776579⟩
def resval7Tail52 : Box := ⟨-71333967896963848741776560701098602266474769060593049791,9817920295838189472456435611333220498297996942256048294⟩
def resval7Tail56 : Box := ⟨-72459531466721796529031584514718265099977379397617608218,8692356726080234862444307881259245774678436274689907834⟩
def resval7Tail60 : Box := ⟨-73602855065632749988827935222903996093887342511278415842,7549033127167436849174660954842423165183623137194467755⟩
def resval7Tail64 : Box := ⟨-74764218923039725014247646391951133943615170373386499971,6387669267133852284014635583629562732361076391620749014⟩
def resval7Tail68 : Box := ⟨-75943866059748720805198748506723312396276893798583065857,5207977457300163195358391266885721591896324306141953151⟩
def resval7Tail72 : Box := ⟨742845713229178045110049602464507776935613040268736749230,1177255974660068652950382590935159493577212648017246951⟩
def resval7Tail76 : Box := ⟨-768019180285079308145904243519510734981591139195543184,288375841000959722625609843412192005552060038600906756⟩
def resval7Tail80 : Box := ⟨-780114549152649353978453672552869287446443350973115927,276257571371874622163089700176055975642865206983201290⟩
def resval7Tail84 : Box := ⟨-792423810264052122165721456842305633242737769325159517,263948309138435748212959136893803622169825526977884485⟩
def resval7Tail88 : Box := ⟨-804927297717459736850687609518402468759054795929564010,251444821684452037416554089219084006323952668786384619⟩
def resval7Tail92 : Box := ⟨-817628075051520647978752153042879275338473966351857357,238744044350389683669249588801030649597478912967162416⟩
def resval7Tail96 : Box := ⟨-830529255260907020186916559153257101470723662353394847,225842864141003298550232175197123889213258547429428272⟩
def resval7Tail100 : Box := ⟨-843634000460138664951323224012432985009346649189886093,212738118941771653443083510327253561687230455942875551⟩
def resval7Tail104 : Box := ⟨-856945522658071981602445783744008386881598240173427272,199426596743838336768443007068626897683210283915901334⟩
def resval7Tail108 : Box := ⟨-870467084545170770567959152249289854926837925457814206,185905034856739547799377607980198396275773653697444271⟩
def resval7Tail112 : Box := ⟨-884202000293200570229952630550267934470055776716351061,172170119108709748136736002186238063896815449781494710⟩
def resval7Tail116 : Box := ⟨-898153636367541212229259924812755188283025993612466155,158218483034369106139458013387407257897631575832916359⟩
def resval7Tail120 : Box := ⟨-912325412352316684775303850968598444334076686989920051,144046707049593633618412725853214333518583586266324732⟩
def resval7Tail124 : Box := ⟨-926720801788544545842091183113472120017952295509953027,129651317613365773097114386029284254931368055579969840⟩
def resval7Tail128 : Box := ⟨-941343333025510352995116214586907728255947690196841821,115028786376399997636185871681541832001445462809402524⟩
def resval7Tail132 : Box := ⟨-956196590085582801753630977107416507674907491365223459,100175529316333783898400645546121637529481988930845395⟩
def resval7Tail136 : Box := ⟨-971284213549227211667935564153009251762353357036616047,85087905858559384074496017825751596401089291566968886⟩
def resval7Tail140 : Box := ⟨-986609955674632526659117103981533031370407667611501425,69762213289315327374116026974166367973423092817270569⟩
def resval7Tail144 : Box := ⟨-1035703659154721047655905068545302933634431740583197497,52151892665550780443569660547018854490337526438579305⟩
def resval7Tail148 : Box := ⟨331925355490980670563973894193697028198576775258,106217287568742420601525983918417214860156563518⟩
def resval7Tail152 : Box := ⟨337113221841925955155748346333060165114729190518,100980144489579349901177399211424093022839872919⟩
def resval7Tail156 : Box := ⟨342432459172304347307509842950544732774049362695,95660906366232668282987822805998494504936930959⟩
def resval7Tail160 : Box := ⟨347835628412624345108934419606901383305228883494,90257737125683710369746386137658845540397556434⟩
def resval7Tail164 : Box := ⟨353324053116134395988822532314150260287781094779,84769312422173295755314170234072448582356238368⟩
def resval7Tail168 : Box := ⟨358899078510504355889178367088217129498554849389,79194287027803333663229317343740699087140710564⟩
def resval7Tail172 : Box := ⟨364562071049691525996030033064633040157851424716,73531294488616163515695961647254606930094390814⟩
def resval7Tail176 : Box := ⟨370314418748641110892940458471492267268883898185,67778946789666578616767587667399504199738808005⟩
def resval7Tail180 : Box := ⟨376157531523492133516923421708991378730574484416,61935834014815555992550129283190780404091243311⟩
def resval7Tail184 : Box := ⟨382092841537151731437008327800916982846790794668,56000524001155958072416350598209983713288412797⟩
def resval7Tail188 : Box := ⟨388121803550322198678075958008242278829606565784,49971561987985490831363492684588054940925147951⟩
def resval7Tail192 : Box := ⟨394245895278066808915067972858056872371562397020,43847470260240880594650030355704785728002788990⟩
def resval7Tail196 : Box := ⟨400466617752001815270131483928813745339246306455,37626747786305874243951856001299253054759628492⟩
def resval7Tail200 : Box := ⟨406785495688203401125172381145252790419748319910,31307869850104288547686692793950600947253810723⟩
def resval7Tail204 : Box := ⟨413204077860919776271321786242637366152978122069,24889287677387930692849360022570491158198950936⟩
def resval7Tail208 : Box := ⟨419723937482188395568870861158011610479909732438,18369428056126725040683554414805645610570311484⟩
def resval7Tail212 : Box := ⟨426346672609092482568750992899405783584942615808,11746692948709084927639302209872049333595183232⟩
def resval7Tail216 : Box := ⟨433074890459739388227469091187131160284531261349,5019377969496531026587897226500223615989935184⟩
theorem resval7H216 : resval7Tail216=hornerBox Q residualBox cell7 216 4 :=
  hornerChunk_step Q residualBox cell7 resval7Tail216 zero 216 4 0 (by decide +kernel) rfl
theorem resval7H212 : resval7Tail212=hornerBox Q residualBox cell7 212 8 :=
  hornerChunk_step Q residualBox cell7 resval7Tail212 resval7Tail216 212 4 4 (by decide +kernel) resval7H216
theorem resval7H208 : resval7Tail208=hornerBox Q residualBox cell7 208 12 :=
  hornerChunk_step Q residualBox cell7 resval7Tail208 resval7Tail212 208 4 8 (by decide +kernel) resval7H212
theorem resval7H204 : resval7Tail204=hornerBox Q residualBox cell7 204 16 :=
  hornerChunk_step Q residualBox cell7 resval7Tail204 resval7Tail208 204 4 12 (by decide +kernel) resval7H208
theorem resval7H200 : resval7Tail200=hornerBox Q residualBox cell7 200 20 :=
  hornerChunk_step Q residualBox cell7 resval7Tail200 resval7Tail204 200 4 16 (by decide +kernel) resval7H204
theorem resval7H196 : resval7Tail196=hornerBox Q residualBox cell7 196 24 :=
  hornerChunk_step Q residualBox cell7 resval7Tail196 resval7Tail200 196 4 20 (by decide +kernel) resval7H200
theorem resval7H192 : resval7Tail192=hornerBox Q residualBox cell7 192 28 :=
  hornerChunk_step Q residualBox cell7 resval7Tail192 resval7Tail196 192 4 24 (by decide +kernel) resval7H196
theorem resval7H188 : resval7Tail188=hornerBox Q residualBox cell7 188 32 :=
  hornerChunk_step Q residualBox cell7 resval7Tail188 resval7Tail192 188 4 28 (by decide +kernel) resval7H192
theorem resval7H184 : resval7Tail184=hornerBox Q residualBox cell7 184 36 :=
  hornerChunk_step Q residualBox cell7 resval7Tail184 resval7Tail188 184 4 32 (by decide +kernel) resval7H188
theorem resval7H180 : resval7Tail180=hornerBox Q residualBox cell7 180 40 :=
  hornerChunk_step Q residualBox cell7 resval7Tail180 resval7Tail184 180 4 36 (by decide +kernel) resval7H184
theorem resval7H176 : resval7Tail176=hornerBox Q residualBox cell7 176 44 :=
  hornerChunk_step Q residualBox cell7 resval7Tail176 resval7Tail180 176 4 40 (by decide +kernel) resval7H180
theorem resval7H172 : resval7Tail172=hornerBox Q residualBox cell7 172 48 :=
  hornerChunk_step Q residualBox cell7 resval7Tail172 resval7Tail176 172 4 44 (by decide +kernel) resval7H176
theorem resval7H168 : resval7Tail168=hornerBox Q residualBox cell7 168 52 :=
  hornerChunk_step Q residualBox cell7 resval7Tail168 resval7Tail172 168 4 48 (by decide +kernel) resval7H172
theorem resval7H164 : resval7Tail164=hornerBox Q residualBox cell7 164 56 :=
  hornerChunk_step Q residualBox cell7 resval7Tail164 resval7Tail168 164 4 52 (by decide +kernel) resval7H168
theorem resval7H160 : resval7Tail160=hornerBox Q residualBox cell7 160 60 :=
  hornerChunk_step Q residualBox cell7 resval7Tail160 resval7Tail164 160 4 56 (by decide +kernel) resval7H164
theorem resval7H156 : resval7Tail156=hornerBox Q residualBox cell7 156 64 :=
  hornerChunk_step Q residualBox cell7 resval7Tail156 resval7Tail160 156 4 60 (by decide +kernel) resval7H160
theorem resval7H152 : resval7Tail152=hornerBox Q residualBox cell7 152 68 :=
  hornerChunk_step Q residualBox cell7 resval7Tail152 resval7Tail156 152 4 64 (by decide +kernel) resval7H156
theorem resval7H148 : resval7Tail148=hornerBox Q residualBox cell7 148 72 :=
  hornerChunk_step Q residualBox cell7 resval7Tail148 resval7Tail152 148 4 68 (by decide +kernel) resval7H152
theorem resval7H144 : resval7Tail144=hornerBox Q residualBox cell7 144 76 :=
  hornerChunk_step Q residualBox cell7 resval7Tail144 resval7Tail148 144 4 72 (by decide +kernel) resval7H148
theorem resval7H140 : resval7Tail140=hornerBox Q residualBox cell7 140 80 :=
  hornerChunk_step Q residualBox cell7 resval7Tail140 resval7Tail144 140 4 76 (by decide +kernel) resval7H144
theorem resval7H136 : resval7Tail136=hornerBox Q residualBox cell7 136 84 :=
  hornerChunk_step Q residualBox cell7 resval7Tail136 resval7Tail140 136 4 80 (by decide +kernel) resval7H140
theorem resval7H132 : resval7Tail132=hornerBox Q residualBox cell7 132 88 :=
  hornerChunk_step Q residualBox cell7 resval7Tail132 resval7Tail136 132 4 84 (by decide +kernel) resval7H136
theorem resval7H128 : resval7Tail128=hornerBox Q residualBox cell7 128 92 :=
  hornerChunk_step Q residualBox cell7 resval7Tail128 resval7Tail132 128 4 88 (by decide +kernel) resval7H132
theorem resval7H124 : resval7Tail124=hornerBox Q residualBox cell7 124 96 :=
  hornerChunk_step Q residualBox cell7 resval7Tail124 resval7Tail128 124 4 92 (by decide +kernel) resval7H128
theorem resval7H120 : resval7Tail120=hornerBox Q residualBox cell7 120 100 :=
  hornerChunk_step Q residualBox cell7 resval7Tail120 resval7Tail124 120 4 96 (by decide +kernel) resval7H124
theorem resval7H116 : resval7Tail116=hornerBox Q residualBox cell7 116 104 :=
  hornerChunk_step Q residualBox cell7 resval7Tail116 resval7Tail120 116 4 100 (by decide +kernel) resval7H120
theorem resval7H112 : resval7Tail112=hornerBox Q residualBox cell7 112 108 :=
  hornerChunk_step Q residualBox cell7 resval7Tail112 resval7Tail116 112 4 104 (by decide +kernel) resval7H116
theorem resval7H108 : resval7Tail108=hornerBox Q residualBox cell7 108 112 :=
  hornerChunk_step Q residualBox cell7 resval7Tail108 resval7Tail112 108 4 108 (by decide +kernel) resval7H112
theorem resval7H104 : resval7Tail104=hornerBox Q residualBox cell7 104 116 :=
  hornerChunk_step Q residualBox cell7 resval7Tail104 resval7Tail108 104 4 112 (by decide +kernel) resval7H108
theorem resval7H100 : resval7Tail100=hornerBox Q residualBox cell7 100 120 :=
  hornerChunk_step Q residualBox cell7 resval7Tail100 resval7Tail104 100 4 116 (by decide +kernel) resval7H104
theorem resval7H96 : resval7Tail96=hornerBox Q residualBox cell7 96 124 :=
  hornerChunk_step Q residualBox cell7 resval7Tail96 resval7Tail100 96 4 120 (by decide +kernel) resval7H100
theorem resval7H92 : resval7Tail92=hornerBox Q residualBox cell7 92 128 :=
  hornerChunk_step Q residualBox cell7 resval7Tail92 resval7Tail96 92 4 124 (by decide +kernel) resval7H96
theorem resval7H88 : resval7Tail88=hornerBox Q residualBox cell7 88 132 :=
  hornerChunk_step Q residualBox cell7 resval7Tail88 resval7Tail92 88 4 128 (by decide +kernel) resval7H92
theorem resval7H84 : resval7Tail84=hornerBox Q residualBox cell7 84 136 :=
  hornerChunk_step Q residualBox cell7 resval7Tail84 resval7Tail88 84 4 132 (by decide +kernel) resval7H88
theorem resval7H80 : resval7Tail80=hornerBox Q residualBox cell7 80 140 :=
  hornerChunk_step Q residualBox cell7 resval7Tail80 resval7Tail84 80 4 136 (by decide +kernel) resval7H84
theorem resval7H76 : resval7Tail76=hornerBox Q residualBox cell7 76 144 :=
  hornerChunk_step Q residualBox cell7 resval7Tail76 resval7Tail80 76 4 140 (by decide +kernel) resval7H80
theorem resval7H72 : resval7Tail72=hornerBox Q residualBox cell7 72 148 :=
  hornerChunk_step Q residualBox cell7 resval7Tail72 resval7Tail76 72 4 144 (by decide +kernel) resval7H76
theorem resval7H68 : resval7Tail68=hornerBox Q residualBox cell7 68 152 :=
  hornerChunk_step Q residualBox cell7 resval7Tail68 resval7Tail72 68 4 148 (by decide +kernel) resval7H72
theorem resval7H64 : resval7Tail64=hornerBox Q residualBox cell7 64 156 :=
  hornerChunk_step Q residualBox cell7 resval7Tail64 resval7Tail68 64 4 152 (by decide +kernel) resval7H68
theorem resval7H60 : resval7Tail60=hornerBox Q residualBox cell7 60 160 :=
  hornerChunk_step Q residualBox cell7 resval7Tail60 resval7Tail64 60 4 156 (by decide +kernel) resval7H64
theorem resval7H56 : resval7Tail56=hornerBox Q residualBox cell7 56 164 :=
  hornerChunk_step Q residualBox cell7 resval7Tail56 resval7Tail60 56 4 160 (by decide +kernel) resval7H60
theorem resval7H52 : resval7Tail52=hornerBox Q residualBox cell7 52 168 :=
  hornerChunk_step Q residualBox cell7 resval7Tail52 resval7Tail56 52 4 164 (by decide +kernel) resval7H56
theorem resval7H48 : resval7Tail48=hornerBox Q residualBox cell7 48 172 :=
  hornerChunk_step Q residualBox cell7 resval7Tail48 resval7Tail52 48 4 168 (by decide +kernel) resval7H52
theorem resval7H44 : resval7Tail44=hornerBox Q residualBox cell7 44 176 :=
  hornerChunk_step Q residualBox cell7 resval7Tail44 resval7Tail48 44 4 172 (by decide +kernel) resval7H48
theorem resval7H40 : resval7Tail40=hornerBox Q residualBox cell7 40 180 :=
  hornerChunk_step Q residualBox cell7 resval7Tail40 resval7Tail44 40 4 176 (by decide +kernel) resval7H44
theorem resval7H36 : resval7Tail36=hornerBox Q residualBox cell7 36 184 :=
  hornerChunk_step Q residualBox cell7 resval7Tail36 resval7Tail40 36 4 180 (by decide +kernel) resval7H40
theorem resval7H32 : resval7Tail32=hornerBox Q residualBox cell7 32 188 :=
  hornerChunk_step Q residualBox cell7 resval7Tail32 resval7Tail36 32 4 184 (by decide +kernel) resval7H36
theorem resval7H28 : resval7Tail28=hornerBox Q residualBox cell7 28 192 :=
  hornerChunk_step Q residualBox cell7 resval7Tail28 resval7Tail32 28 4 188 (by decide +kernel) resval7H32
theorem resval7H24 : resval7Tail24=hornerBox Q residualBox cell7 24 196 :=
  hornerChunk_step Q residualBox cell7 resval7Tail24 resval7Tail28 24 4 192 (by decide +kernel) resval7H28
theorem resval7H20 : resval7Tail20=hornerBox Q residualBox cell7 20 200 :=
  hornerChunk_step Q residualBox cell7 resval7Tail20 resval7Tail24 20 4 196 (by decide +kernel) resval7H24
theorem resval7H16 : resval7Tail16=hornerBox Q residualBox cell7 16 204 :=
  hornerChunk_step Q residualBox cell7 resval7Tail16 resval7Tail20 16 4 200 (by decide +kernel) resval7H20
theorem resval7H12 : resval7Tail12=hornerBox Q residualBox cell7 12 208 :=
  hornerChunk_step Q residualBox cell7 resval7Tail12 resval7Tail16 12 4 204 (by decide +kernel) resval7H16
theorem resval7H8 : resval7Tail8=hornerBox Q residualBox cell7 8 212 :=
  hornerChunk_step Q residualBox cell7 resval7Tail8 resval7Tail12 8 4 208 (by decide +kernel) resval7H12
theorem resval7H4 : resval7Tail4=hornerBox Q residualBox cell7 4 216 :=
  hornerChunk_step Q residualBox cell7 resval7Tail4 resval7Tail8 4 4 212 (by decide +kernel) resval7H8
theorem resval7H0 : resval7=hornerBox Q residualBox cell7 0 220 :=
  hornerChunk_step Q residualBox cell7 resval7 resval7Tail4 0 4 216 (by decide +kernel) resval7H4
theorem resval7_eq : resval7=hornerBox Q residualBox cell7 0 220 := resval7H0
def polyval7Tail5 : Box := ⟨20262979239136083051442276531663814932549048367279178383815,6180316997142233253468614273563767179153104456676350919726⟩
def polyval7Tail9 : Box := ⟨20582702629366388792414389985850375636813867285547012636336,5860591754414607185539318994617975501170350353796199184399⟩
def polyval7Tail13 : Box := ⟨20907472734243005095631339719509630508765791127219415930858,5535821649374921753502321368990654384863989283169998105307⟩
def polyval7Tail17 : Box := ⟨21237367317975603611027159562186911953552145796899580816556,5205927065642206743787745662216081843774880010149457418678⟩
def polyval7Tail21 : Box := ⟨21572467238468024565934997507035582990158083047851081572566,4870827145149785419101216627870072557937053038559823078018⟩
def polyval7Tail25 : Box := ⟨21912854629626312332520817077260353407327739546945906213196,4530439753991497648544718174879980980948522563696328542208⟩
def polyval7Tail29 : Box := ⟨22258612921330131458038975155071270774504629789518671058971,4184681462287678522904812521215063540184180522224473079039⟩
def polyval7Tail33 : Box := ⟨22609826859881546267523902557112358579956556865704522506486,3833467523736263713410532115097907818343089906873722197935⟩
def polyval7Tail37 : Box := ⟨22966582528776570724901523036650679523039466679546891993151,3476711854841239256031389950886964676618814236061045436661⟩
def polyval7Tail41 : Box := ⟨23328967369804468521655751301449095739514958074520996416413,3114327013813341459276923222351257162668946873363846611445⟩
def polyval7Tail45 : Box := ⟨23697070204479974555714073661386884885381967330588655353655,2746224179137835425219890983752750109397206206413085735266⟩
def polyval7Tail49 : Box := ⟨24070981255813690893451183586470050180480274052976161915543,2372313127804119087498427029853564729776866608181662138642⟩
def polyval7Tail53 : Box := ⟨24450792170425993198610744071671304118520143036431498005706,1992502213191816782694319015216674356489702516410872280241⟩
def polyval7Tail57 : Box := ⟨24836596041009867830242177528041233826408716831720275795396,1606698342607942172661685246310837358601372719760356685806⟩
def polyval7Tail61 : Box := ⟨25228487429148190292519399847306826798051897943982931951066,1214806954469624142203314186863405892307741721975091667692⟩
def polyval7Tail65 : Box := ⟨25626562388495845757196673426364579696164963833648276092243,816731995126292137766305332090153589241664495789438596515⟩
def polyval7Tail69 : Box := ⟨26030918528780337638011542541036241639373151659939107259570,412375891945054087362291068354000779883347267019689139496⟩
def polyval7Tail73 : Box := ⟨26468750000000000000000000000000000000000000000000000000000,2⟩
theorem polyval7H73 : polyval7Tail73=hornerBox Q polyBox cell7 73 1 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail73 zero 73 1 0 (by decide +kernel) rfl
theorem polyval7H69 : polyval7Tail69=hornerBox Q polyBox cell7 69 5 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail69 polyval7Tail73 69 4 1 (by decide +kernel) polyval7H73
theorem polyval7H65 : polyval7Tail65=hornerBox Q polyBox cell7 65 9 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail65 polyval7Tail69 65 4 5 (by decide +kernel) polyval7H69
theorem polyval7H61 : polyval7Tail61=hornerBox Q polyBox cell7 61 13 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail61 polyval7Tail65 61 4 9 (by decide +kernel) polyval7H65
theorem polyval7H57 : polyval7Tail57=hornerBox Q polyBox cell7 57 17 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail57 polyval7Tail61 57 4 13 (by decide +kernel) polyval7H61
theorem polyval7H53 : polyval7Tail53=hornerBox Q polyBox cell7 53 21 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail53 polyval7Tail57 53 4 17 (by decide +kernel) polyval7H57
theorem polyval7H49 : polyval7Tail49=hornerBox Q polyBox cell7 49 25 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail49 polyval7Tail53 49 4 21 (by decide +kernel) polyval7H53
theorem polyval7H45 : polyval7Tail45=hornerBox Q polyBox cell7 45 29 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail45 polyval7Tail49 45 4 25 (by decide +kernel) polyval7H49
theorem polyval7H41 : polyval7Tail41=hornerBox Q polyBox cell7 41 33 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail41 polyval7Tail45 41 4 29 (by decide +kernel) polyval7H45
theorem polyval7H37 : polyval7Tail37=hornerBox Q polyBox cell7 37 37 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail37 polyval7Tail41 37 4 33 (by decide +kernel) polyval7H41
theorem polyval7H33 : polyval7Tail33=hornerBox Q polyBox cell7 33 41 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail33 polyval7Tail37 33 4 37 (by decide +kernel) polyval7H37
theorem polyval7H29 : polyval7Tail29=hornerBox Q polyBox cell7 29 45 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail29 polyval7Tail33 29 4 41 (by decide +kernel) polyval7H33
theorem polyval7H25 : polyval7Tail25=hornerBox Q polyBox cell7 25 49 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail25 polyval7Tail29 25 4 45 (by decide +kernel) polyval7H29
theorem polyval7H21 : polyval7Tail21=hornerBox Q polyBox cell7 21 53 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail21 polyval7Tail25 21 4 49 (by decide +kernel) polyval7H25
theorem polyval7H17 : polyval7Tail17=hornerBox Q polyBox cell7 17 57 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail17 polyval7Tail21 17 4 53 (by decide +kernel) polyval7H21
theorem polyval7H13 : polyval7Tail13=hornerBox Q polyBox cell7 13 61 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail13 polyval7Tail17 13 4 57 (by decide +kernel) polyval7H17
theorem polyval7H9 : polyval7Tail9=hornerBox Q polyBox cell7 9 65 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail9 polyval7Tail13 9 4 61 (by decide +kernel) polyval7H13
theorem polyval7H5 : polyval7Tail5=hornerBox Q polyBox cell7 5 69 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail5 polyval7Tail9 5 4 65 (by decide +kernel) polyval7H9
theorem polyval7H1 : polyval7=hornerBox Q polyBox cell7 1 73 :=
  hornerChunk_step Q polyBox cell7 polyval7 polyval7Tail5 1 4 69 (by decide +kernel) polyval7H5
theorem polyval7_eq : polyval7=hornerBox Q polyBox cell7 1 73 := polyval7H1
theorem polyval7_upper : 5*(polyval7.center+polyval7.radius)<Q := by decide +kernel
theorem resval7_pos : 0<(resval7).center-(resval7).radius := by decide +kernel
theorem polyval7_pos : 0<(polyval7).center-(polyval7).radius := by decide +kernel
def pend : Box := ⟨1030152652345666035708996878821868195939087477524772643511475,5785147438254482632092596477778486177006698249421681588⟩
def zend : Box := ⟨1003706039438305679259824218750000000000000000000000000000000,4078771048956351738281250000000000000000000000000000002⟩
def betaquot : Box := ⟨428742890898820879753225803405266415202089690775562838189408,394756427946271893549632090872501532659662664428256838⟩
def crit : Box := ⟨104070699704102230415341539206132496252808855562329859418,15124459601676735921764843863430447923111676379186438936⟩
def subsonic : Box := ⟨620391812874109915471182514504079962995616707053724248711,8531485887446050968455707453555554070843322373834071411⟩
def pendTail4 : Box := ⟨26441726241374885109551453981665812455951343602787387867825,1535536170610330343681015056753152363237383469860746520⟩
def pendTail8 : Box := ⟨26441759037290733721097859658512876232248650749073025838994,1535345037973246019951532635407293123804757357856428431⟩
def pendTail12 : Box := ⟨26441759038599392308365711828457397018001341442252585238347,1535345017836726156193251142566042667398597186904603747⟩
def pendTail16 : Box := ⟨26441759038599987489622261234957186897859462890794130373766,1535345017821209645363486223121686240798312930817688866⟩
def pendTail20 : Box := ⟨26441759038599988814568721239509994404314471703100714398501,1535345017821156297106825426409131509407207934739312987⟩
def pendTail24 : Box := ⟨26441759038599988825043928956678503838792814383368581365500,1535345017821155655073509796123654542497291257793425534⟩
def pendTail28 : Box := ⟨26441759038599988825286281189931847000696695729843928989700,1535345017821155631798946841413801104361499088646761354⟩
def pendTail32 : Box := ⟨26441759038599988825300379462094300221289958337945443389883,1535345017821155629477966301216343605377994296112956595⟩
def pendTail36 : Box := ⟨26441759038599988825302044112299116095213998515819308239102,1535345017821155628873376597215422172556165393120997461⟩
def pendTail40 : Box := ⟨26441759038599988825302099014597130984824005715612162750507,1535345017821155628471573471125857697074867480769486537⟩
def pendTail44 : Box := ⟨26441759038599988825300758079681604948685531244505766897184,1535345017821155627790542290603077792076451458187999305⟩
def pendTail48 : Box := ⟨26441759038599988825289651177812123585464134868690813301457,1535345017821155624780362956316138902357441162386867942⟩
def pendTail52 : Box := ⟨26441759038599988825103392087389143541743433897885184269203,1535345017821155588346233866550245785523405184330084202⟩
def pendTail56 : Box := ⟨26441759038599988816819168848275269704531760314047306897057,1535345017821154272701936231831223869587654579006796517⟩
def pendTail60 : Box := ⟨26441759038599987623795853124144831513685179528165567977838,1535345017820990488023730021156364466167305440608045519⟩
def pendTail64 : Box := ⟨26441759038599254057133873148866870952662568217554628563154,1535345017740124553737065486000411273315111155925560689⟩
def pendTail68 : Box := ⟨26441759035368613304763151003157807888824011896081322913829,1535344741781468129516791418248060870841283074673663574⟩
def pendTail72 : Box := ⟨26441328082162893330607671668236595353732676294341861983066,1507790365037903521911157570451186460704776745501246206⟩
theorem pendH72 : pendTail72=hornerBox Q polyBox (oneBox Q) 72 2 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail72 zero 72 2 0 (by decide +kernel) rfl
theorem pendH68 : pendTail68=hornerBox Q polyBox (oneBox Q) 68 6 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail68 pendTail72 68 4 2 (by decide +kernel) pendH72
theorem pendH64 : pendTail64=hornerBox Q polyBox (oneBox Q) 64 10 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail64 pendTail68 64 4 6 (by decide +kernel) pendH68
theorem pendH60 : pendTail60=hornerBox Q polyBox (oneBox Q) 60 14 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail60 pendTail64 60 4 10 (by decide +kernel) pendH64
theorem pendH56 : pendTail56=hornerBox Q polyBox (oneBox Q) 56 18 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail56 pendTail60 56 4 14 (by decide +kernel) pendH60
theorem pendH52 : pendTail52=hornerBox Q polyBox (oneBox Q) 52 22 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail52 pendTail56 52 4 18 (by decide +kernel) pendH56
theorem pendH48 : pendTail48=hornerBox Q polyBox (oneBox Q) 48 26 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail48 pendTail52 48 4 22 (by decide +kernel) pendH52
theorem pendH44 : pendTail44=hornerBox Q polyBox (oneBox Q) 44 30 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail44 pendTail48 44 4 26 (by decide +kernel) pendH48
theorem pendH40 : pendTail40=hornerBox Q polyBox (oneBox Q) 40 34 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail40 pendTail44 40 4 30 (by decide +kernel) pendH44
theorem pendH36 : pendTail36=hornerBox Q polyBox (oneBox Q) 36 38 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail36 pendTail40 36 4 34 (by decide +kernel) pendH40
theorem pendH32 : pendTail32=hornerBox Q polyBox (oneBox Q) 32 42 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail32 pendTail36 32 4 38 (by decide +kernel) pendH36
theorem pendH28 : pendTail28=hornerBox Q polyBox (oneBox Q) 28 46 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail28 pendTail32 28 4 42 (by decide +kernel) pendH32
theorem pendH24 : pendTail24=hornerBox Q polyBox (oneBox Q) 24 50 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail24 pendTail28 24 4 46 (by decide +kernel) pendH28
theorem pendH20 : pendTail20=hornerBox Q polyBox (oneBox Q) 20 54 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail20 pendTail24 20 4 50 (by decide +kernel) pendH24
theorem pendH16 : pendTail16=hornerBox Q polyBox (oneBox Q) 16 58 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail16 pendTail20 16 4 54 (by decide +kernel) pendH20
theorem pendH12 : pendTail12=hornerBox Q polyBox (oneBox Q) 12 62 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail12 pendTail16 12 4 58 (by decide +kernel) pendH16
theorem pendH8 : pendTail8=hornerBox Q polyBox (oneBox Q) 8 66 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail8 pendTail12 8 4 62 (by decide +kernel) pendH12
theorem pendH4 : pendTail4=hornerBox Q polyBox (oneBox Q) 4 70 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail4 pendTail8 4 4 66 (by decide +kernel) pendH8
theorem pendH0 : pend=hornerBox Q polyBox (oneBox Q) 0 74 :=
  hornerChunk_step Q polyBox (oneBox Q) pend pendTail4 0 4 70 (by decide +kernel) pendH4
theorem pend_eq : pend=hornerBox Q polyBox (oneBox Q) 0 74 := pendH0
theorem zend_eq : zend=add (oneBox Q) (scale 1 256 root) := by decide +kernel
theorem betaquot_eq : betaquot=scale 3 7 (sub (oneBox Q) kap) := by decide +kernel
theorem crit_eq : crit=add (sub pend zend) (mul Q (mul Q betaquot zend) (sub (oneBox Q) (mul Q pend pend))) := by decide +kernel
theorem subsonic_eq : subsonic=sub (oneBox Q) (mul Q sig (mul Q zend zend)) := by decide +kernel
theorem crit_pos : 0<crit.center-crit.radius := by decide +kernel
theorem subsonic_pos : 0<subsonic.center-subsonic.radius := by decide +kernel
end SepticProfile.ExteriorCertificates.C07

end
end

end OAI
