import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData32

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C32
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨120512117615163188554285220289633814435888505380719942390,306333368054477607750272104820707649084997905963203046⟩
def polyval0 : Box := ⟨3851758721385393959536923657406855687572031455045068124616,14805153033935029745050463602891435722622780281584092610⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨64923782986142861826744678823574641989807868237638,1870309220765613465138484118250958752867268147358⟩
def resval0Tail8 : Box := ⟨8233115251758328407286853484232175957669161939,433332799232134510842572017783201616134174606⟩
def resval0Tail12 : Box := ⟨7847645985538510853898256399525489793954764,628405116972336868212572274938741588663402⟩
def resval0Tail16 : Box := ⟨32912533884711746095932743288449890844772,28969918571221213362934330771895244868063⟩
def resval0Tail20 : Box := ⟨469242175336691251814228089893396902763,403589127994266755104457214433666734686747⟩
def resval0Tail24 : Box := ⟨19516819980578486585876429607192507755,6456242343232381580032642818962582078398216⟩
def resval0Tail28 : Box := ⟨2154652097294572295288013030858268880,103299809928160757253764946585248619227900179⟩
def resval0Tail32 : Box := ⟨594369047065537844807417224268103567,1652796948559431904883393276493458306574937157⟩
def resval0Tail36 : Box := ⟨-175052405398974992892510963064194266,26444751172945961784924502389080736111960118629⟩
def resval0Tail40 : Box := ⟨-147183158000615199592965814524125492321,423116018627088152213295854028442212583592043420⟩
def resval0Tail44 : Box := ⟨-37844473006878583637626752931726012237087,6769856262549149945216437950493649081395769290143⟩
def resval0Tail48 : Box := ⟨-9688833244447609253862209590113446176978330,108317691117470250939010432592517563641158094165135⟩
def resval0Tail52 : Box := ⟨-2480347480649541878290474731549862009994275226,1733080732553029125709142531859977303762654493314203⟩
def resval0Tail56 : Box := ⟨-634969084043556589656939326748273621844790840427,27728696437281511339470018590619853228520839078015512⟩
def resval0Tail60 : Box := ⟨-162552080932576063256485923983872351325369594065858,443506750406648765220502779207663050387772318979077719⟩
def resval0Tail64 : Box := ⟨-41613300917884464210703075032291822776410328956101536,7057095515564256411200272715212867844626020233813317756⟩
def resval0Tail68 : Box := ⟨-10652262145998974692051469972875872814452488655475482696,102926649471947430018707256928284641156900046516504994084⟩
def resval0Tail72 : Box := ⟨851663802793369355027685470657683177701577018989752317344,2560902787049280218752762275903075508017437426801739824⟩
def resval0Tail76 : Box := ⟨-30546492206327714497082598849177917462589138403556,651846842911992350690141841160278019405042740356⟩
def resval0Tail80 : Box := ⟨-1730950959750331854916475732558607562675742790,78265600907042884899356097861318430103225965⟩
def resval0Tail84 : Box := ⟨-1026150275729911944913590777815025048717198,73172235662094765969919288705263666251081⟩
def resval0Tail88 : Box := ⟨-2974397838333292943980311597044359861161,483315252760894487548002982720312286443⟩
def resval0Tail92 : Box := ⟨-31017998652289204081076816325395553127,2820803162959277756403184564509129587026⟩
def resval0Tail96 : Box := ⟨-976840718572016851680958768929124366,45061350693580250139629583436632094753055⟩
def resval0Tail100 : Box := ⟨-83444410960413703350218399683728131,720978513885335910920761284916019989056575⟩
def resval0Tail104 : Box := ⟨-18120600737438385136489001893910011,11535655857774933687494582272106807201544299⟩
def resval0Tail108 : Box := ⟨-11633963751467271425088818350236095,184570493613115954558062499247480136908020523⟩
def resval0Tail112 : Box := ⟨-522765186542888796936971240713764161,2953127897331668386798029010838790554383018804⟩
def resval0Tail116 : Box := ⟨-130684593873713028676361943857526027673,47250046234836172433006875045078507160257605431⟩
def resval0Tail120 : Box := ⟨-33445527386512229511513862101343466034928,756000708402456151432055479909371386203541893992⟩
def resval0Tail124 : Box := ⟨-8561981591034281348877573878283514080932022,12096003307585994393664793082828054766585203823171⟩
def resval0Tail128 : Box := ⟨-2191865997050357767519452989662533681633859743,193533998047256947616221129064854856865476758914521⟩
def resval0Tail132 : Box := ⟨-561117682765691497167208593942815675419538952161,3096017920982373665514298237787381023815224876068859⟩
def resval0Tail136 : Box := ⟨-143646208516075929748864552465767750519292365687463,49401618470508408645779277861080757589701958921264274⟩
def resval0Tail140 : Box := ⟨-36774467712359650811749746876000346194942920173198856,755950345428832111118236858247835774160464927168088303⟩
def resval0Tail144 : Box := ⟨-9948088204970146502658777559034495882988796198192818867,3008518532530844536957045688927297464715223328639838123⟩
def resval0Tail148 : Box := ⟨74313972255752358358870568248916241642730465,1297063613598661928763904444053119712594634⟩
def resval0Tail152 : Box := ⟨1389367105762017484392228051626688073892,55941136261327566112254842728546115351⟩
def resval0Tail156 : Box := ⟨462790188762416444448516684599466973,30034255131230174803393926356052329⟩
def resval0Tail160 : Box := ⟨849489367148211933719606252487762,82301648110881439916308654145740⟩
def resval0Tail164 : Box := ⟨5940304699653813945745240941846,34930605135044132968696602920801⟩
def resval0Tail168 : Box := ⟨129493533467230936910189075991,546397326944972306712049503644696⟩
def resval0Tail172 : Box := ⟨7786665830884794353182352312,8741984684947875756984729603314662⟩
def resval0Tail176 : Box := ⟨1197570461295873094236847927,139871724395916083298817427718617603⟩
def resval0Tail180 : Box := ⟨458696132129168902307644772,2237947583849191141450688148758644469⟩
def resval0Tail184 : Box := ⟨2427246933088750033077680458,35807161337264959342925125063173412204⟩
def resval0Tail188 : Box := ⟨517990591477933704832469997583,572914580911840909487103022426120712753⟩
def resval0Tail192 : Box := ⟨132383846100890518669518870824550,9166633170483961900794904326440025304580⟩
def resval0Tail196 : Box := ⟨33889119622837416067855082720592773,146666098956739685502192979746553427087223⟩
def resval0Tail200 : Box := ⟨8675600449507978061665939024582880107,2346649449933933578358324341615459253460862⟩
def resval0Tail204 : Box := ⟨2220953382181107114211629565198207635979,37544309055322356689671638874284773319964685⟩
def resval0Tail208 : Box := ⟨568564141975379457367136625640025306541099,600175916084669392128360598045003116300050937⟩
def resval0Tail212 : Box := ⟨145552870729133753341110448471606254577325212,9466359084327090693390299726964418664683752993⟩
def resval0Tail216 : Box := ⟨37288002221242449928788448659662005306610267084,116516486570433859709827061780259049741945618491⟩
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
def polyval0Tail5 : Box := ⟨2226160865312634594996501359506158047752907471652488,54423227717600344117824469984760113937868768915014⟩
def polyval0Tail9 : Box := ⟨226272069099913075143018678282105546848620679843,10940318122635579968751462751074461723914040855⟩
def polyval0Tail13 : Box := ⟨186615841825368583655487442539510884093124885,14000835233511138271433505930262663533639484⟩
def polyval0Tail17 : Box := ⟨685828384134720727492990794138081570565578,460138810754190136813753041405832874870453⟩
def polyval0Tail21 : Box := ⟨8591881569832821391257485329822260914543,6181597334779105061714035939114671638115903⟩
def polyval0Tail25 : Box := ⟨313654120818546783865864430722118646692,98885009765436860076068241831838968597179104⟩
def polyval0Tail29 : Box := ⟨30284569904187950875753718322346817280,1582159127474535849608002300151818157946824856⟩
def polyval0Tail33 : Box := ⟨7315216506115454424073169496574523937,25314545903006727392854144902026250854616424175⟩
def polyval0Tail37 : Box := ⟨10097174029627221706305433121415759081,405032734400301890519233999556153443791614378851⟩
def polyval0Tail41 : Box := ⟨1504401279972146271363352315596255916095,6480523749005395774392456323192264484961863042567⟩
def polyval0Tail45 : Box := ⟨383632647314255683070502068434400505050461,103688379624453836136150225654388915118982966498254⟩
def polyval0Tail49 : Box := ⟨98205013448646187433372647864688790145661185,1659013981924200155960036535324489203501520138197197⟩
def polyval0Tail53 : Box := ⟨25140443950627209630884932686810365945200903301,26544200141623518746365959683387161087450895956548189⟩
def polyval0Tail57 : Box := ⟨6435952927978039050804818073660851126073933023100,424701168560257278888503461128370941442539584223658335⟩
def polyval0Tail61 : Box := ⟨1647603944127902231593220251922855942822196579763618,6793674068299701913949363605266713198464153189830457639⟩
def polyval0Tail65 : Box := ⟨421786660814347437258496550302853994783466295491833795,108303360132825888351712935420244898221195741584496436998⟩
def polyval0Tail69 : Box := ⟨107978002189492369680622645798782936409025832255682838806,1631624692287728611061909588096127314037507453475796839296⟩
def polyval0Tail73 : Box := ⟨28031250000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨120269932195734886921537925100802032903822947009546096152,223603295766303188106499679185833019294433292066449383⟩
def polyval1 : Box := ⟨3833139577862322236620713618122659511641923623686419163749,8457158386035037779536087987254306157720783638162490698⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨63019129940468911963929663283527123103131061899721,3232745735521573567058622077889509381386848541094⟩
def resval1Tail8 : Box := ⟨7762294554875347452530306075973981792391812051,6529786911699106243636784115549795194134352136446⟩
def resval1Tail12 : Box := ⟨-332590633061768723463774806266015110562585392,20636410511470856199773828389713411547195051411866⟩
def resval1Tail16 : Box := ⟨-2227308963427117833194841532431933426978712755,65220093874031530095419488619746350671091993694352⟩
def resval1Tail20 : Box := ⟨-14597086493472079023012837732965170635506504585,206120146493756642771467092998731329438787849319734⟩
def resval1Tail24 : Box := ⟨-95663468729598735535600911414090640410324584618,651391921181154709370853343217202815908673188426046⟩
def resval1Tail28 : Box := ⟨-626940108773609903100102648170495277261447182093,2058395549648931440073668713585534663471322676944330⟩
def resval1Tail32 : Box := ⟨-4108714696869912875428487072348426763544571974587,6503419154166992518149583686428546399854175694670159⟩
def resval1Tail36 : Box := ⟨-26926872637409468462893902414430469625452004696294,20540074786981712275809292648497613848606008535903738⟩
def resval1Tail40 : Box := ⟨-176467952516528231785972490851411159987695158805968,64825413835909338335308807628765532970741038634686191⟩
def resval1Tail44 : Box := ⟨-1156500373612320734914353619836951617942537584669919,204281545772523750713576582502393990998646671780068358⟩
def resval1Tail48 : Box := ⟨-7579240848505699265826812135296113793745645734138169,641706435860270019120487874591907321771925408408184630⟩
def resval1Tail52 : Box := ⟨-49671312824766589966209789469897374476328996586193681,2002392060477042659254052912052957855770466765630500520⟩
def resval1Tail56 : Box := ⟨-325525915728354497535158559305283728346200404431587062,6160007708534117830863617133285406819288464565313850025⟩
def resval1Tail60 : Box := ⟨-2133366641305843800019902312925588724795093502972165575,18364122344006803627585456556459851343534437237914365989⟩
def resval1Tail64 : Box := ⟨-13981231601865670387645317899896940397246105171934941068,50800955791843634717909278089103655862872625422565804414⟩
def resval1Tail68 : Box := ⟨-91627058891283115755391948155503886969659154323765070537,113116347907638633184932528339548046441674816116293396129⟩
def resval1Tail72 : Box := ⟨854779909388662073390425351111066538111409767093892469538,1521638248627958599048782253025801547084469463919198053⟩
def resval1Tail76 : Box := ⟨-29857450836295321397901027493259688879732403144210,423324710433574897691455854609957166960520447765⟩
def resval1Tail80 : Box := ⟨-1653522130221743353438045387584430564309583769,68371194269997282032849335601611456474886852268⟩
def resval1Tail84 : Box := ⟨-3910277315329307015054286745048542707501752,215934869269199165353412507452271159618213030467⟩
def resval1Tail88 : Box := ⟨-19354224778243801154605920144043607213605705,682450819017279053628847715477373196181303747713⟩
def resval1Tail92 : Box := ⟨-126822136859747503281574813273938890594991760,2156815939143564201257113019566730755736983237576⟩
def resval1Tail96 : Box := ⟨-831141376932972730496738791461153064443011651,6816173141102829582785883735539731976787384134541⟩
def resval1Tail100 : Box := ⟨-5446968122431660074005959357236941330224372818,21539652986378924507945189784989323362737844103636⟩
def resval1Tail104 : Box := ⟨-35697250286727108500195851378116704986702639484,68057458161470437791707010341488663743248058437080⟩
def resval1Tail108 : Box := ⟨-233945499479006719125483447355766473591740926045,214974051851259646948488415296981934672388333397289⟩
def resval1Tail112 : Box := ⟨-1533185225385578717602262331788998798157313596421,678630361957195828616446497909234617997629690827937⟩
def resval1Tail116 : Box := ⟨-10047882693086895971862346956158137901138223734052,2139604809637046926744886864852058767536148187287668⟩
def resval1Tail120 : Box := ⟨-65849804017414310200594126746585683301766087891153,6728114260630909946488072322074129048871629350934197⟩
def resval1Tail124 : Box := ⟨-431553275608529327654006206849631480337120433951622,21040728212662720414520956199117973617904577123526099⟩
def resval1Tail128 : Box := ⟨-2828227547028287545673936957592246972310533766131002,65034785551705732419305833185080534254329162631310056⟩
def resval1Tail132 : Box := ⟨-18535072052257336940046913884925567622660240616680347,195945561938846872287236713593530901374046772150175795⟩
def resval1Tail136 : Box := ⟨-121471448255950803608002298236460487055849321131776864,556393271563072815249707270210461847811411011417671928⟩
def resval1Tail140 : Box := ⟨-796075777486519974567203295675656273857320039382549067,1346311890783293608784358108823264423682355024832802656⟩
def resval1Tail144 : Box := ⟨-5441227742146831097558359781647620883948461136191385375,1514436011254784271648181584921796223632105463694078314⟩
def resval1Tail148 : Box := ⟨73199374149809158295222597473322862814290213,903786255822673325593354679380551103843329⟩
def resval1Tail152 : Box := ⟨1335657924634308440907359016337480454345,3562699342273910704963588484054608840961⟩
def resval1Tail156 : Box := ⟨571388486509323927618545072930289050,11147438633004336272246837639991881578652⟩
def resval1Tail160 : Box := ⟨894619109998123431025062881577405821,35230951877164842447426385689764126133555⟩
def resval1Tail164 : Box := ⟨5857872602051557581683372735614046880,111344173048791287346503460043721498770345⟩
def resval1Tail168 : Box := ⟨38390119191689735218375017476726149519,351882695245375663291137733030269437339844⟩
def resval1Tail172 : Box := ⟨251593484403518451033886987870656250457,1111992824457583209350053589718447200762412⟩
def resval1Tail176 : Box := ⟨1648843059344845620539126213337395190319,3513592774140000618383305104255042215518668⟩
def resval1Tail180 : Box := ⟨10805857873716332444057833220728373640806,11099093574262483785769883481053620130432671⟩
def resval1Tail184 : Box := ⟨70817270161185339519147347535173785142036,35041951305479149939511016792441512195449201⟩
def resval1Tail188 : Box := ⟨464108061728342862589077229987935166807582,110509580276097901472008572473129189401981009⟩
def resval1Tail192 : Box := ⟨3041578593342866848451685606786300796722131,347690078375589461380375352318968038744995366⟩
def resval1Tail196 : Box := ⟨19933289469331833477664659428556419461500651,1088551947370750609353128967245420467589309486⟩
def resval1Tail200 : Box := ⟨130634805866214378455740436529630716323060057,3372725942665405297568031126064463444765873823⟩
def resval1Tail204 : Box := ⟨856128263724992372950698661644448946390615515,10216221756325698957164983192195318272407681292⟩
def resval1Tail208 : Box := ⟨5610722189230140771144516201899785015234938975,29383371701367700142229463646070785643120929617⟩
def resval1Tail212 : Box := ⟨36770429177431969010270933671916909307788285460,73828188745657739064133999704276953308915804112⟩
def resval1Tail216 : Box := ⟨240990386818831028554631981828164873231777138038,108565418141675783515568578448992996024323777424⟩
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
def polyval1Tail5 : Box := ⟨2165478386354529616467027067475654628947049112146576,121098282532088001946923720098301194032783765461446⟩
def polyval1Tail9 : Box := ⟨217563248073213275240776620682308188319871224304,281512451971501924693596101704653678615739393221073⟩
def polyval1Tail13 : Box := ⟨15946897312445158673749670863637955412771772329,889692934514078007450167637903636485458431057115123⟩
def polyval1Tail17 : Box := ⟨103373972219751572114150508229513789584438828618,2811815510520142357005616214264324681647435748687340⟩
def polyval1Tail21 : Box := ⟨677467599407551853690656612571174710547960853920,8886374807374536641291905421034633527744800079145584⟩
def polyval1Tail25 : Box := ⟨4439851610087783128751212119527062137419843688993,28083034005074171576917886209030198574073877991905833⟩
def polyval1Tail29 : Box := ⟨29097011510135841354682735763862218417646975663233,88741190733071392183631118012137464879167443982166811⟩
def polyval1Tail33 : Box := ⟨190690174632667407972788429511857116634951645636289,280367256277378013384100083300155649273908039044524767⟩
def polyval1Tail37 : Box := ⟨1249707128472614089037466365761815336256956948794057,885451950793931496948737966780823026157199170737929475⟩
def polyval1Tail41 : Box := ⟨8190080637158106603694968147587141171579413155420935,2794225035759575866972382709554763051463280456111943333⟩
def polyval1Tail45 : Box := ⟨53674512463679352863173621109246573936053051070689301,8803341164049455177985363678133202643796424142380567227⟩
def polyval1Tail49 : Box := ⟨351761284881969028147394146509647991413141765963293236,27640782087801517928506692983160442310386939487003437543⟩
def polyval1Tail53 : Box := ⟨2305302756602473912250397069406445927217670134786121192,86164957779286079021354170126360836516155595429190350705⟩
def polyval1Tail57 : Box := ⟨15108032145670110167349861727214309552963228142902829665,264501680165286419754015101965034802072930088157696555729⟩
def polyval1Tail61 : Box := ⟨99011999469896085264459149219969185422890336670213407548,784692770303030436851111716076750062672046852294150321925⟩
def polyval1Tail65 : Box := ⟨648885039759738422512125000778194472003984485749124280872,2144058430167779165274655422303664601315803056424395434572⟩
def polyval1Tail69 : Box := ⟨4252533291330273159313648965832933514201016112821094480478,4574547547683310909214705346053034101049342650317464481661⟩
def polyval1Tail73 : Box := ⟨28031250000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨120150728778619274270493047198167457752939211816183407834,203064337287774226871661292033652106515458484219724650⟩
def polyval2 : Box := ⟨3823940904521213759771182899138899529175140821729103132841,7146383287178677009037693699888610090428585568832135966⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-134202191509702489756217982926361756696132870323720,35137037457337261406981308172889342833013845319231452⟩
def resval2Tail8 : Box := ⟨-450461567227018279571715466625979081473843665976496,59825370228927147519171402306041391809184489036895991⟩
def resval2Tail12 : Box := ⟨-1033645480363603263058782644936100050091460172114341,101794275203175632953398159080169767847191604253109506⟩
def resval2Tail16 : Box := ⟨-2371800380251037265459908724786377601281774465321416,173048092642474504400114684609261630001303463950136178⟩
def resval2Tail20 : Box := ⟨-5442327289730075360817243652268396994222895227056702,293816265722012602068696031377714429499344922516884304⟩
def resval2Tail24 : Box := ⟨-12487950746114466228595036641548287631499399313480904,498033997182290145097748674799255529100114856342541578⟩
def resval2Tail28 : Box := ⟨-28654820913040811901735278440757836868346849766780002,842273083591226302940129177821046582640929381921542750⟩
def resval2Tail32 : Box := ⟨-65751281235147324805172711096852283429255964417769165,1420013273887500783217751980485564476097518592455740448⟩
def resval2Tail36 : Box := ⟨-150872727391429400190548782441946258660544840205956905,2383776009710764123887101171966985025599146494652142062⟩
def resval2Tail40 : Box := ⟨-346192187329740456455463887063309034365293430249428770,3977806657805863323008520220814394862605397662166372687⟩
def resval2Tail44 : Box := ⟨-794371737293577624601146059014401930751583949233748953,6582179395432550271281013339856577082519330099547470297⟩
def resval2Tail48 : Box := ⟨-1822763424784562965930877069506941293718899810890118683,10761307145663675196376770473194295587634214280632713359⟩
def resval2Tail52 : Box := ⟨-4182508448817657225018909028412797104237285756485984397,17285360379402243879859297015976136233312204222593370399⟩
def resval2Tail56 : Box := ⟨-9597173547904943335262719530475523567662764948538477467,27026062903735472068184023804200506027934771841634234020⟩
def resval2Tail60 : Box := ⟨-22021650699738335901747635778345160520614396583981464394,40455973834162697714577628294701580538499009028922975372⟩
def resval2Tail64 : Box := ⟨-50530825245319114746766180539067755451807188160222478570,56053243915812322111515589570446042538302668841825970047⟩
def resval2Tail68 : Box := ⟨-115947639109734701772669602803336406518347772259924720192,65879820521707754061057235691492111559144969027433594091⟩
def resval2Tail72 : Box := ⟨856336096265974601259266967356906235714510800964063178084,1002467558400344113815128296893777698660747700621038007⟩
def resval2Tail76 : Box := ⟨-31745931645972631662179066556488147857061995275871,428942243142616245564107431282967781522629021674969⟩
def resval2Tail80 : Box := ⟨-5092500307867787085056306723270968645652898984286,730372385384229679402409980700433540461414793780243⟩
def resval2Tail84 : Box := ⟨-11681529246457710422380162273846823076313767356285,1242986327706903238799624051372033559602162775080835⟩
def resval2Tail88 : Box := ⟨-26804406009518346604010448070135500439689763886747,2113603564946835418891899476446167477976927143054391⟩
def resval2Tail92 : Box := ⟨-61505323765650316374864286555923595482727207420318,3589936179369110700397188814734112310376093927441235⟩
def resval2Tail96 : Box := ⟨-141129963877454497415506091218176801536846119463554,6088068035639361261845585800617872997642570643813197⟩
def resval2Tail100 : Box := ⟨-323836466253730902008977209032462811949379396522473,10302900312597112158958289894794369185326440187069913⟩
def resval2Tail104 : Box := ⟨-743074354973723068727305205952360231785302440077492,17385669437684774612615421694692503664707799459894288⟩
def resval2Tail108 : Box := ⟨-1705056578115539174156303946140918388115332709039035,29221779979455975386186572654708323612678690133307816⟩
def resval2Tail112 : Box := ⟨-3912418609410734046820591876972918052262991404758195,48847399191427634810529218210951963927138610189340622⟩
def resval2Tail116 : Box := ⟨-8977426070037529030871722281360810820214372641667487,81028493843429342627977895603149223776477427190937295⟩
def resval2Tail120 : Box := ⟨-20599579668988463505077389802554417439477183168288594,132946546097592255602441149005002862757569520584227585⟩
def resval2Tail124 : Box := ⟨-47267744588313715772564910225068814853625008266150678,214675167173416659955108212282872127752074776917302932⟩
def resval2Tail128 : Box := ⟨-108460449891100927082462092562377560007157094818729655,338402593247611298263832849920462728533593686326067368⟩
def resval2Tail132 : Box := ⟨-248873080216534795956179461104501438101252046804664099,513455543147171746005487199474879433630829777515564876⟩
def resval2Tail136 : Box := ⟨-571063554718787731666579650518351365100201385231145824,729435421288003047677051224803506705118679020240250457⟩
def resval2Tail140 : Box := ⟨-1310361411250177325414838881266240046968315346721666654,908232779868980254756059838926183231414674673096819491⟩
def resval2Tail144 : Box := ⟨-3180451315516882696821445873635488000094651092384581556,763318860698576323492863975755056391495429947724544237⟩
def resval2Tail148 : Box := ⟨72962104415436757900260601626928656076146273,54720533678857313379766661560082083358096481⟩
def resval2Tail152 : Box := ⟨694971641831682697659435107949997982274399,92047645366125351411360035857659748681714812⟩
def resval2Tail156 : Box := ⟨1591673592041727918421877067823470622275266,156620889021115475458252767238528991459223044⟩
def resval2Tail160 : Box := ⟨3652249321321462792295787027971069914696459,266251396959696906588436692630925281767089831⟩
def resval2Tail164 : Box := ⟨8380442262987596584339026483901105332883371,452063262511672455422794617385866934457102359⟩
def resval2Tail168 : Box := ⟨19229742101005828662294976065954349094139652,766266890450842058798653257906120510161039412⟩
def resval2Tail172 : Box := ⟨44124518690925080823109718900205034311172214,1295898058123888961654518552473077887945880528⟩
def resval2Tail176 : Box := ⟨101248011516699895771803465536718570857291003,2184771344848763783521252755037920756047957860⟩
def resval2Tail180 : Box := ⟨232323436951032678120456448563781589759997248,3667524661205126933369199177693703919528415735⟩
def resval2Tail184 : Box := ⟨533088784147014375551523394670594940430388780,6119879899754539047111737059525880980773433762⟩
def resval2Tail188 : Box := ⟨1223224206360377231687568033019613760794192072,10126446651307578961208408437287527306193657923⟩
def resval2Tail192 : Box := ⟨2806807240223860589606066797592586978485914626,16555230174606605286812492061249427874569214736⟩
def resval2Tail196 : Box := ⟨6440492955264554058184557867285780256587764503,26590288073950601415002977707641584546737283624⟩
def resval2Tail200 : Box := ⟨14778339214881056323607586168454570133233641335,41570714969069497339484160464962114297306636533⟩
def resval2Tail204 : Box := ⟨33910340631856344959527713683351617559885731734,62218658092617530518132655672159281438564578471⟩
def resval2Tail208 : Box := ⟨77810583790877642022103945963023773157266658283,86181244103994733259459180760740915755359785109⟩
def resval2Tail212 : Box := ⟨178543973416295504963281642389883996867159535036,101218845187078466542126194758545469370312740179⟩
def resval2Tail216 : Box := ⟨409695707405490825938450402156032155111231239672,67575574560502672605496871420112070813332082934⟩
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
def polyval2Tail5 : Box := ⟨22728001714704749447371667328292165713201926991212164,3159282801608826135157043070338490150904576338522058308⟩
def polyval2Tail9 : Box := ⟨47249197147562169131611918841591315357338748011958987,5377475238551806593230660626303046993878298999207364437⟩
def polyval2Tail13 : Box := ⟨108417409198929524475275930733256606345424047784698786,9145922626787269943507659145031284336867453913577614557⟩
def polyval2Tail17 : Box := ⟨248774318766921474696866123996782737567766682443232617,15538721219221939586009726880297295133475241848761473263⟩
def polyval2Tail21 : Box := ⟨570836936895425867267455958868239441214121604397223832,26361933460272394575459846418106709191641923065195529553⟩
def polyval2Tail25 : Box := ⟨1309841024347122569170765130784750793668770583684416088,44636276237959984187504633796973630904093070890403545888⟩
def polyval2Tail29 : Box := ⟨3005557976667939109941951347384463991550382081585998991,75376489631166258421631213013852556921234457841867551668⟩
def polyval2Tail33 : Box := ⟨6896545903816745076940660841972008392276394859972738847,126819766883225684328390389268511588563778886258357015833⟩
def polyval2Tail37 : Box := ⟨15824797183310605549443024563165845820550180009303662591,212289329087295721325785300230009613987810681210596543790⟩
def polyval2Tail41 : Box := ⟨36311540499472842169611398358032927835284684914003560599,352841088073789762943269964954856245056716424992708782082⟩
def polyval2Tail45 : Box := ⟨83320371071511928312240931655480591867776299473323342013,580556832858552057756226412326776035704565758904804034276⟩
def polyval2Tail49 : Box := ⟨191186717500879021597988760810385355727892284616889202396,941358483372732843075881284606451875453833548255272318186⟩
def polyval2Tail53 : Box := ⟨438696569382640930357726769676303466160283342519678217289,1493375543394666109008397305969577466058409329859089412465⟩
def polyval2Tail57 : Box := ⟨1006632063690373569555215449118397602157593682457896264267,2289397663063416472936455511500520736448895532375651477915⟩
def polyval2Tail61 : Box := ⟨2309815445047900862511509107668302220847895319693851265312,3313065754778663894842733013601792780616925586395298011224⟩
def polyval2Tail65 : Box := ⟨5300096810596259804405558488073880771035861883903897901669,4292290275846330171981234563276223051961124887211184516697⟩
def polyval2Tail69 : Box := ⟨12161589273120291607890556730257932797618750645718618293852,4202599820189101489129087311432827880776316874988525264891⟩
def polyval2Tail73 : Box := ⟨28031250000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨119966360346857669660750236050875948839788075770426549818,1713729000518914486402633253849167592486883074934470298⟩
def polyval3 : Box := ⟨3842674269586797272476589560699972836715622850658200360520,246645765926247781564913425427676564111732721427265421822⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-185811255942388203242217459890911579258044290297910806,1986762004577094095464601847848464911700177581552524203⟩
def resval3Tail8 : Box := ⟨-275564999540316345924736265079367871891487497489425356,2536993266039984887994602585821060265935615576913464302⟩
def resval3Tail12 : Box := ⟨-408537558407676459191238172239931447859971206193585652,3232426767070036207715075013986659814046404491680469299⟩
def resval3Tail16 : Box := ⟨-605675366441489080240332957092675689131955413215234516,4107692298446339458839967321829463532741676850292052699⟩
def resval3Tail20 : Box := ⟨-897941063087768059618664598101002647094626083808406386,5203693767254759624335619699727080781112528403498192960⟩
def resval3Tail24 : Box := ⟨-1331238147452455059543588497248383517384888482480193980,6567561659783651944387162686099383010835736452168637069⟩
def resval3Tail28 : Box := ⟨-1973620628439199598372609643131028991534809861235809735,8251678021773649970881091103153208890098908772886990419⟩
def resval3Tail32 : Box := ⟨-2925981645323799394331725617261005148371417225521754408,10311058795967051162554667732203106861024469546634300992⟩
def resval3Tail36 : Box := ⟨-4337899830091644302558652738933294618119448528597705316,12797955623941682751381873925094819509024166723077604742⟩
def resval3Tail40 : Box := ⟨-6431132254702411087234353284161378991143035620338853226,15751888447233946874241616280595219882704641106741566066⟩
def resval3Tail44 : Box := ⟨-9534443785577211048452644395876444086475618955711762581,19182325492884046340237377975113297676774126638502860127⟩
def resval3Tail48 : Box := ⟨-14135243173371559032013664155513045793860479982468784295,23039713694445467407892937691111972666378119042341466506⟩
def resval3Tail52 : Box := ⟨-20956135886247835914492081322555804189021251413040033986,27168268524404146807768743085989460097688833799359602793⟩
def resval3Tail56 : Box := ⟨-31068417139804674658625171322006440993182091285272648694,31230466167977780370406699072283377038764848282635673034⟩
def resval3Tail60 : Box := ⟨-46060330435543507033315442282408848639131014808934169856,34587958284621975024548527390631329645335187385736587325⟩
def resval3Tail64 : Box := ⟨-68286518423610373486925137923820498055088343008794723884,36115777850379756185215755385609745976735378488062019112⟩
def resval3Tail68 : Box := ⟨-101237603425887130427941249348170897386549556946845771758,33914924003997831772658683158990876034153015182744411732⟩
def resval3Tail72 : Box := ⟨857112155081280118929724485119633086659418080378444692865,762760377579023277424052834178618817974521760315547494⟩
def resval3Tail76 : Box := ⟨-2372532691627594689864681738182531231051006117864783,26048688703429699340132527841869705799080784612191782⟩
def resval3Tail80 : Box := ⟨-3473852552936843707176324689698630907797579638451621,33280361872695947763359683345907952878402798825263631⟩
def resval3Tail84 : Box := ⟨-5150140803905103794528104470568047553349530005824029,42429594326795340891159533453224317810049862955592141⟩
def resval3Tail88 : Box := ⟨-7635316151064425094573038892993633077027743814348562,53958471927260258355564924391139823440343977471925024⟩
def resval3Tail92 : Box := ⟨-11319700753188461750176809074591225506374320692259905,68415815207323505163138733627790106129290403284875725⟩
def resval3Tail96 : Box := ⟨-16781967191222892256259693311249382850043603133735298,86438709825826205917437426371476945943219301805280439⟩
def resval3Tail100 : Box := ⟨-24880023681540624894933808205765047915751361068557195,108743093138001689158245639442686273693302885716563951⟩
def resval3Tail104 : Box := ⟨-36885757869778973610179383068740175072153325976661073,136094480824256089897773706861541284559749191359985280⟩
def resval3Tail108 : Box := ⟨-54684800587123585991205503420044047093837100934919037,169244738633662229741081390375578885232325337671602311⟩
def resval3Tail112 : Box := ⟨-81072684633750519670531509892158978014782686598541485,208812674030415785904101652706072727015839839999008208⟩
def resval3Tail116 : Box := ⟨-120193913540049266023147828438632131632031146736009774,255073777628638200694608769193012047992535469906568181⟩
def resval3Tail120 : Box := ⟨-178192900819010689196835072045843149882052149424852209,307605487495677741908022334037717831166413919982265827⟩
def resval3Tail124 : Box := ⟨-264179016782855689105888255113483747750658246122694488,364705589174505716514603297235913590985368610133820008⟩
def resval3Tail128 : Box := ⟨-391657313998396427880364916540770923570161150855959531,422457876836599046434073640909134873400544040031379636⟩
def resval3Tail132 : Box := ⟨-580649642339057976157102215819688486381998127111421967,473253629691838819068219312620111418488325310273478357⟩
def resval3Tail136 : Box := ⟨-860839297808933356856441949350783452067664183745773046,503478822441907594170286845754197896777919135309018385⟩
def resval3Tail140 : Box := ⟨-1276233459185458745346910325946221546396393390365848073,489928893389436292484449969264714593594780611149399427⟩
def resval3Tail144 : Box := ⟨-2048225025180629593553271908722712810897955168443136604,386740243339956985635997584917192734752709647446083070⟩
def resval3Tail148 : Box := ⟨704969396793834249774776965739031846952503056,6180207598286894660343107618827140537436960556⟩
def resval3Tail152 : Box := ⟨937822509886174800855123286384872882551129914,7881038025450000296280056092456414669089409488⟩
def resval3Tail156 : Box := ⟨1390362267680562624132322049870524576604819723,10025988512042209219356537107832132036779861237⟩
def resval3Tail160 : Box := ⟨2061274804157468791735093026505901527634891023,12717628201714864974092419034102956504801653626⟩
def resval3Tail164 : Box := ⟨3055932916398793820510856238999620433354255427,16075922637039239379864381957145465803916880506⟩
def resval3Tail168 : Box := ⟨4530558453776895660072373613349620525514511850,20236360766966109122282237640397857460504707375⟩
def resval3Tail172 : Box := ⟨6716757358429764181754486544878842905485812096,25344967442570009738289701001119325469799858410⟩
def resval3Tail176 : Box := ⟨9957895891269309370800173954994445337204567191,31547233917290121409578148044665471374154505810⟩
def resval3Tail180 : Box := ⟨14763030029201416893867802412734173787901536487,38966948975909711117511393487251042910510313191⟩
def resval3Tail184 : Box := ⟨21886858230179949582652047148355678033994489043,47668655924466230868572907191918427117281324909⟩
def resval3Tail188 : Box := ⟨32448255015431166415726620501801606784760650388,57594020058917319155744460278447196812778813673⟩
def resval3Tail192 : Box := ⟨48106002354171468987369609612447841696090763440,68457168791952034232168626891902691234358638628⟩
def resval3Tail196 : Box := ⟨71319319371689190415320415341852169364947271280,79576166736604141106689002262805358981449495256⟩
def resval3Tail200 : Box := ⟨105734109398511150940661948104312406469869648691,89605872381105872790717892313695423701990944415⟩
def resval3Tail204 : Box := ⟨156755588650979347814107933537174797338432043946,96119493737346330323574338105903156051788149331⟩
def resval3Tail208 : Box := ⟨232397234091305759885295451250212755386522873867,94959237995690350483274534347008545263632056812⟩
def resval3Tail212 : Box := ⟨344539387112725856909370731483590896202408598505,79236094621908363936909331945178221932794500820⟩
def resval3Tail216 : Box := ⟨510803436679187994765526981457924004303607047321,37797884422308421540746499705205832583758513426⟩
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
def polyval3Tail5 : Box := ⟨34576944729019125142983146182253936882838842865208103165,312182521946478921150741464136272398015100763923721234126⟩
def polyval3Tail9 : Box := ⟨51258734424996658900177936232785196798073877786540635382,397631911915437714679769551614649207731578236915565481082⟩
def polyval3Tail13 : Box := ⟨75993386632589191042516225322642730178759909974086959825,505112734550176739795191722260476713740478553608693546267⟩
def polyval3Tail17 : Box := ⟨112663625039385428933756336437246472110794344909113964753,639600488695387107981960887841248350165358749222313043867⟩
def polyval3Tail21 : Box := ⟨167028908297123790089163659731351882955118934423376370941,806805777287508596580074460808405560406843667664480572204⟩
def polyval3Tail25 : Box := ⟨247627894071189340847630037425255736708986276988679262528,1013038376634479155659157862891514430112747807185485659967⟩
def polyval3Tail29 : Box := ⟨367119527675126907169678601299155898383678859380135292733,1264861207474832412762782914163877870630378905875988093990⟩
def polyval3Tail33 : Box := ⟨544271266797035226158437151343931428399185827888228330074,1568390253376549642775572765605021864611526926430651753903⟩
def polyval3Tail37 : Box := ⟨806906714379388120564455279493875770722678086632787636662,1928014478432385864032611581521999760330333662541751043127⟩
def polyval3Tail41 : Box := ⟨1196275617381325495678032824187922586171009017349992735537,2344184536536944526139565290536084435241906252344735164393⟩
def polyval3Tail45 : Box := ⟨1773532587148871188340209965482783848769210931729582590085,2809728581190639807217043749530418154186416437092431942953⟩
def polyval3Tail49 : Box := ⟨2629342094729272743418289162510366672958839812729430367559,3303864896446987851308943609707865296590526258927948878585⟩
def polyval3Tail53 : Box := ⟨3898118309869545339776074443219418405847878272773508036022,3782645213562107290649562811736003503616772862607520122142⟩
def polyval3Tail57 : Box := ⟨5779136304933638052599163272787947007902632700333970574726,4163906031295829444384769944535411424180098797451705443546⟩
def polyval3Tail61 : Box := ⟨8567830367395861201650147227829785771314386579829424188114,4303818473041384102725899398441191047196882086903360231079⟩
def polyval3Tail65 : Box := ⟨12702195160537476130416933436983614921343821170393368849297,3960646882091075617193077329298726391650097505929296892542⟩
def polyval3Tail69 : Box := ⟨18831577748713891054710480867247537781188857730355772066300,2739109187433179499300187196726665829308485095806000987537⟩
def polyval3Tail73 : Box := ⟨28031250000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨116890494008052681862671890954568579516517728600826695045,8560771661516162609307377314924782875309695861022776104⟩
def polyval4 : Box := ⟨4697650386660168275179192553120781997370219312070616846275,1960513189424627497341044252786381159020008240300966153206⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-3843279489174170968460825009215819369608595629543656076,9306413163682321897069055680812135383098814531446114633⟩
def resval4Tail8 : Box := ⟨-4657034636404015114328123933289822584104467596811682317,10273341592174305632453312612897419845366251339313960870⟩
def resval4Tail12 : Box := ⟨-5642999666101722277280983429992354853133143553948707893,11309115328546678411650817993661675037680529495152389942⟩
def resval4Tail16 : Box := ⟨-6837708470451947731830180662880377859839348847196199109,12409911164223841524349726473168615810579470810279178722⟩
def resval4Tail20 : Box := ⟨-8285355288552165227866291105862488042441991215263359859,13568605808217510674022686475194042608955618119459527885⟩
def resval4Tail24 : Box := ⟨-10039490942643499181630145251866988063866346623090246341,14773739196147454177906193566887506937823792546121499353⟩
def resval4Tail28 : Box := ⟨-12165003778013455231237454637962421372494812446832687995,16008213296652808690124450136495306914485055784375768447⟩
def resval4Tail32 : Box := ⟨-14740519988966202149882448222317395114043664420208334298,17247663568619659307179926823359169977272411418405690682⟩
def resval4Tail36 : Box := ⟨-17861312130278225076502889395329977123689976836256125858,18458426740932231711507714661658993969365073561477159662⟩
def resval4Tail40 : Box := ⟨-21642823404739222572610484354670021837393761157635919792,19595011475700286585038685559779150199789059627730251647⟩
def resval4Tail44 : Box := ⟨-26224938095935476996956254413616607908046064839328379274,20596957613627964173689920264465812411171642165521272866⟩
def resval4Tail48 : Box := ⟨-31777156116565127352841694341059606313535729493300451849,21384944274818712187584543049130687986433202355071887141⟩
def resval4Tail52 : Box := ⟨-38504863087286233814813982555404646086924088708533154985,21855976113983364366740218758225628522126426350253832183⟩
def resval4Tail56 : Box := ⟨-46656927886563741943472799335867397679642031347834719090,21877439308454500771209780949709163229588174202962331468⟩
def resval4Tail60 : Box := ⟨-56534908717295483324232015858740099140729863147178428303,21279772936803772867577407023909311709716045109083829371⟩
def resval4Tail64 : Box := ⟨-68504208224716353451447535598627369620303042718273479639,19847445519845593003766585942031126267162393558696370061⟩
def resval4Tail68 : Box := ⟨-83007359832036435923787766348454670840977807730037812518,17307855641872625712327438913753509396311854111455504435⟩
def resval4Tail72 : Box := ⟨857460406032844187168220603981072612609316192639175620689,725478371621164404606990439184428431547197532443750445⟩
def resval4Tail76 : Box := ⟨-50965121997177813174449312755385109763489677627113446,126388615611555768194775193711989106394644277568101096⟩
def resval4Tail80 : Box := ⟨-61719728819452840158224326741985743239964902561870984,139616279018328838568812997973715193517267134675673131⟩
def resval4Tail84 : Box := ⟨-74786731639130728048154969192249425753767250099951340,153812405869102344565832364262972401302826939539447587⟩
def resval4Tail88 : Box := ⟨-90620219503357159539927457880542951361774209185377085,168933780038474272498098446869332533292483442812981236⟩
def resval4Tail92 : Box := ⟨-109805897422568554257759222415987765333818409220811409,184894596257134197980114086084643947681030671718525503⟩
def resval4Tail96 : Box := ⟨-133053474984457462760361462048066221489511311349515466,201552738475429174054267264956845881858174542221597626⟩
def resval4Tail100 : Box := ⟨-161222918085282034064473207727803006248781162776314192,218692692804902476427733892234048558340068288376782432⟩
def resval4Tail104 : Box := ⟨-195356260473241250247831368815214204441459117250584816,236004143464282761893255414618620162220459113965412914⟩
def resval4Tail108 : Box := ⟨-236716150280205490977059736204805453472756835708788470,253055243027789864348724081017971275463148036591711187⟩
def resval4Tail112 : Box := ⟨-286832557440134409062474971667982562447709040724758344,269259321910009808237421046480530702312211775930918999⟩
def resval4Tail116 : Box := ⟨-347559369777938519592626611366045042496884531028936599,283833525978039766562990395830536652783808834914115882⟩
def resval4Tail120 : Box := ⟨-421142971350627714115360287282682657534271095803832765,295747534723647464784472823363320781363928689032657722⟩
def resval4Tail124 : Box := ⟨-510305339865689121933398495218224327971840158157700685,303660102498197755025726636605673436448956754103558389⟩
def resval4Tail128 : Box := ⟨-618344737086037603616744400045422940420849961089609422,305840666052770505224117197245247877567700657634168365⟩
def resval4Tail132 : Box := ⟨-749257716924252148206702133033189897606214915453243455,300072653778430775444337590199712431343850716351690831⟩
def resval4Tail136 : Box := ⟨-907886964543015369155091740828316870562497917812510658,283534392224540215381822024390560955393549147517422047⟩
def resval4Tail140 : Box := ⟨-1100100772056830999721568852795137785404561810697235552,252652589752058883455396080218735215850319865371139265⟩
def resval4Tail144 : Box := ⟨-1481652152695585770182742189278084161837014979601344638,198195823172580628354814290705018032597774191498696287⟩
def resval4Tail148 : Box := ⟨21682348148683633963572322580065353531748231125,46059336735424485201864369214915403935392997188⟩
def resval4Tail152 : Box := ⟨26185270556679590935842548304238599451587220101,50646812170052931136890913620562566978832859112⟩
def resval4Tail156 : Box := ⟨31729088790792462081842472095674170541403331061,55506909749882872273334724250590406759235768922⟩
def resval4Tail160 : Box := ⟨38446619177511651041771874053876890265004636704,60602102405806150098729561286101018543172644830⟩
def resval4Tail164 : Box := ⟨46586352855766809210049637450966531464638845701,65874665662435018801249132173694162179308963618⟩
def resval4Tail168 : Box := ⟨56449391879728831462063369728831854691050550774,71240097534959080160554692196530909495412671223⟩
def resval4Tail172 : Box := ⟨68400586185761964567579622266804293819499439255,76579478211794551756001206534010575114834244542⟩
def resval4Tail176 : Box := ⟨82882029987571329473544849819948054288709424041,81729945274206390421052290258667980552941499206⟩
def resval4Tail180 : Box := ⟨100429415563847765547418912479005410651132028287,86472849324653778451565393026877835887518323368⟩
def resval4Tail184 : Box := ⟨121691849391339663203188885846368503326089130577,90519057894715981443915292748496404117733362055⟩
def resval4Tail188 : Box := ⟨147455863654506364685976438030576689408802481796,93490757286850771363555563384612006832946250394⟩
def resval4Tail192 : Box := ⟨178674511356746235475212175017459865703135802608,94898958006922268318144876572369285823905012446⟩
def resval4Tail196 : Box := ⟨216502621308924799162873990335729455448671227527,94115734106358735328959840833889015215741838675⟩
def resval4Tail200 : Box := ⟨262339517134859059764217340122896990140725680892,90340013322960901442105147031557308295293416781⟩
def resval4Tail204 : Box := ⟨317880780539602713703403698365522531645705193495,82555475191819889597263646412057864266427972794⟩
def resval4Tail208 : Box := ⟨385180973648500541342869377342142274924391163282,69478798343563656028384358889737656867262954737⟩
def resval4Tail212 : Box := ⟨466729640783354427574378380549496829592730137140,49496113931793663643874599861802798939513195131⟩
def resval4Tail216 : Box := ⟨565551260674678508352537514106116261747136026640,20584698390570724930132821565179544433448232010⟩
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
def polyval4Tail5 : Box := ⟨1067015115369895210674762205350905251818502124149691083991,2157233763534972702267246610090675716404246997245976128533⟩
def polyval4Tail9 : Box := ⟨1292915870979846116734688009442453700139036347561450265609,2367929704042509207304252775887792670888266945764851643942⟩
def polyval4Tail13 : Box := ⟨1566645813266020301066746167634586168810240886892374419100,2589918909633032987901546759974355846455053538946769792144⟩
def polyval4Tail17 : Box := ⟨1898328545348524208970267806644931013375633494643893564086,2821081203729649934555146701189972473530573453959902656270⟩
def polyval4Tail21 : Box := ⟨2300233553474864862994842117002564834796177541795106305597,3058236689269366097724406683700313187771977268327248576988⟩
def polyval4Tail25 : Box := ⟨2787227960879758641259973182153054884960135742371387128227,3296838663761992565953321011405111343383881711897898457584⟩
def polyval4Tail29 : Box := ⟨3377326486770956040054175392083006464764680196886429186359,3530590328331623017283561962693153940776080135639891919561⟩
def polyval4Tail33 : Box := ⟨4092357840240796641402658158612795083658540332334488847601,3750967630769610201112827391061512637659543302450455170227⟩
def polyval4Tail37 : Box := ⟨4958772199898390951105182065335794868417052616409102417921,3946626647653758231527492495278979593808390106058535734115⟩
def polyval4Tail41 : Box := ⟨6008619649213831289781582229737554555974294429723157647971,4102669105422871482898198564757282056973886480180219991911⟩
def polyval4Tail45 : Box := ⟨7280735761497237887992528796525215402031881997729171201076,4199733786224941950441579835425382823945535154051894959990⟩
def polyval4Tail49 : Box := ⟨8822178191239061856284028554041153335806647566330122651714,4212874435038340007155503469601266954517856809646576075763⟩
def polyval4Tail53 : Box := ⟨10689967413673683557710896620057146643418897614266005314053,4110176105154207673554333439156637739291879481961032215808⟩
def polyval4Tail57 : Box := ⟨12953196005368308368013700477291962784691259517678922424983,3851051315914559016229472319665220054134482295298706217219⟩
def polyval4Tail61 : Box := ⟨15695584491574155826317406892600875936942954512477382877993,3384144544540371753046360817349463826299333626889942276870⟩
def polyval4Tail65 : Box := ⟨19018578305335169364233595134326867687692262877796969672009,2644757941262014121751613554934952115076017549595538738919⟩
def polyval4Tail69 : Box := ⟨23045100620945965933070884293646007151343071848475782839918,1551692138267500093094551131400020813505916602325148755432⟩
def polyval4Tail73 : Box := ⟨28031250000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨105958083560855502327583161617079126219978383518451806055,13391063603886195746958094982688884799457880190556108278⟩
def polyval5 : Box := ⟨8879088465140029440498257647830137629021095864009136941866,3925670257484969546664589163672452676855352824530583049998⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-15491559998448209402183240156003252348451200129556735110,13619996989657654391665844308821196944111136373775629821⟩
def resval5Tail8 : Box := ⟨-17033217796673259701799634287989346304726960492017363878,13971232747383053588299544300622843630134258402757356916⟩
def resval5Tail12 : Box := ⟨-18728221034080620715992156695016809245638181042372876645,14292133924084233802388257190690088815376654894878864793⟩
def resval5Tail16 : Box := ⟨-20591896794538168042966766807230270934092947082437944713,14575436351904206848936576286829705475659708137601351850⟩
def resval5Tail20 : Box := ⟨-22641029963558087408430564195912076588519675273660915216,14812877548929488256133050371240587634901348726035206339⟩
def resval5Tail24 : Box := ⟨-24894075709756943040111205971420277937929796525691244721,14995078867660392021018254755103888444321670173017668504⟩
def resval5Tail28 : Box := ⟨-27371325705613838981922797652819123575823047249764822908,15111415310676327207781132530536669905308368771183235390⟩
def resval5Tail32 : Box := ⟨-30095090880966543881569725927615216657562384962750152016,15149871148861349227371307001898547250037937236743093118⟩
def resval5Tail36 : Box := ⟨-33089902362598178519607905724070934106075249789137601316,15096879848455413596518264151413907264816769719796209207⟩
def resval5Tail40 : Box := ⟨-36382732409649231444598150747118541174210903340886847692,14937146659422526081186139902146891492561373474484314741⟩
def resval5Tail44 : Box := ⟨-40003237334672057313816048170935365042147933777569801457,14653452048085622051364554138161686366254327024622869485⟩
def resval5Tail48 : Box := ⟨-43984024598154929408099708529356570321176540142891206558,14226433970201347367566672427946264604991954942721547179⟩
def resval5Tail52 : Box := ⟨-48360946482056950379077684043756998600936751963059496350,13634346774897346311557199921429106092343834282781861021⟩
def resval5Tail56 : Box := ⟨-53173422987274430514382548979376743034383341098378507874,12852794303256871616041386534243793312770381421406171194⟩
def resval5Tail60 : Box := ⟨-58464796863151657432402342646001923832130983944699940865,11854434495704809226998209273219505318999449215200523736⟩
def resval5Tail64 : Box := ⟨-64282723953868697269480559489461310095346980360871557175,10608652547013652924270745880188397066043524354471470225⟩
def resval5Tail68 : Box := ⟨-70679377095174451657957324962237693785154308472025676963,9081194782592280984554584571790915853978630486083987377⟩
def resval5Tail72 : Box := ⟨857505838750160943164645577776266359169041685035820015144,727239955779462099206102593186483663160691088978978694⟩
def resval5Tail76 : Box := ⟨-209957616879923443941413638525494319247263053083368199,187754446605584422816600602507470680077199995033668259⟩
def resval5Tail80 : Box := ⟨-230818686624726710711979961010701915503822270928651368,192721254458563760568986853303693806959724959854919145⟩
def resval5Tail84 : Box := ⟨-253787828108089415112251513775527816069934019907774278,197290610370149435102716698634641239304967087044500774⟩
def resval5Tail88 : Box := ⟨-279042667991872420619192310650201133366624043453574784,201364818275425773741543144940669983467207697557896208⟩
def resval5Tail92 : Box := ⟨-306810658102698856739821700346277045186498999008447082,204832845942251992691254114662801268261092905194089440⟩
def resval5Tail96 : Box := ⟨-337341886109524197190858012631568218775247526551185399,207568596583793820289984716553733767668471042173771601⟩
def resval5Tail100 : Box := ⟨-370911326313308953112867040487553353369047431223570890,209429148649465227801542377816295603634632027492918556⟩
def resval5Tail104 : Box := ⟨-407821316155301427956079645954636567659024511389490307,210252803497064523532165551865674000830793884622677824⟩
def resval5Tail108 : Box := ⟨-448404279167666199056537318782817152841410188124698264,209856920705652123703576084918510537097203830195110168⟩
def resval5Tail112 : Box := ⟨-493025718889364588952337767181365245244469457169254682,208035518721382631058776233694843283980109147444615903⟩
def resval5Tail116 : Box := ⟨-542087510711477850067059564389845417500657713473063245,204556616232201502131681934454380468923976999148453057⟩
def resval5Tail120 : Box := ⟨-596031521299416846951977012077249007710751553259753772,199159287137519442577723027158183665227077528163063908⟩
def resval5Tail124 : Box := ⟨-655343588189727435102039481156253865848005622129022941,191550399192143347807036577426028917619208381367501559⟩
def resval5Tail128 : Box := ⟨-720557895403052005472393885677827538029807609947289414,181401003333948820655797456494894819397248597250501266⟩
def resval5Tail132 : Box := ⟨-792261784481496779335535503757251942230324930062574873,168342337323499502149475139270025954412269232393994353⟩
def resval5Tail136 : Box := ⟨-871101044317468036648207995297495260123441021676640065,151961403597857425758277896571513678868447824485012162⟩
def resval5Tail140 : Box := ⟨-957786056715139699881124459184029200277479202219976345,131796064373482303367950549684587581309065376195939418⟩
def resval5Tail144 : Box := ⟨-1198250683901309658661006856875216259909428511937321696,103859836676772729693890132501989935395327617123969260⟩
def resval5Tail148 : Box := ⟨118475820966428968651003221610273837841481183313,89057334858610959003884306934356433435338467280⟩
def resval5Tail152 : Box := ⟨130186162746109071055492889445281115617037285665,90763352765621056429399560414275065913714787523⟩
def resval5Tail156 : Box := ⟨143141198297657232627621175815006333122245287725,92174417919820890189152420787568271216527479003⟩
def resval5Tail160 : Box := ⟨157385411941612004636136339719650096299811248535,93230387935421319312111765587787340414301678639⟩
def resval5Tail164 : Box := ⟨173047090472117332566149343358814493508627982796,93863708554792537648930085866197765732571826580⟩
def resval5Tail168 : Box := ⟨190267288126898463454995124369226843458629338405,93998008283538699606054077352953827930441294975⟩
def resval5Tail172 : Box := ⟨209201095680931327499035496645359657555485288136,93547084752063392504380675971132526365526863621⟩
def resval5Tail176 : Box := ⟨230019037244663527016669412244832386510886910522,92413781368378550867367964781118905407459037112⟩
def resval5Tail180 : Box := ⟨252908606060348364558894396139233694368306296801,90488742752984402388110316713566875619148053376⟩
def resval5Tail184 : Box := ⟨278075953127972768805695108545005199283234734215,87649036279963143112422071286914671659862320480⟩
def resval5Tail188 : Box := ⟨305747743869100017868785444114324408101678410895,83756625747167863985904279899126354609063388120⟩
def resval5Tail192 : Box := ⟨336173199550353684917032795296334045281974716661,78656681765036061033848100529909941534768031214⟩
def resval5Tail196 : Box := ⟨369626341852275451409172667261139753470448025107,72175711874808484900237324030986300827314313773⟩
def resval5Tail200 : Box := ⟨406408460798883617618452036233579975306707324322,64119491668140979555950015154423563163327906831⟩
def resval5Tail204 : Box := ⟨446850828274919339585518569526974604565004311328,54270776265141821364695227754509642898826610864⟩
def resval5Tail208 : Box := ⟨491317681569668245924900448423553726759373024857,42386769399012776085992156320663893923519920180⟩
def resval5Tail212 : Box := ⟨540209503979078286977442047707071290788160709597,28196325025613533149946552093092015122994667352⟩
def resval5Tail216 : Box := ⟨593974311526278011394370891268618571278758145959,11396564024574402958290126582966017458224208874⟩
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
def polyval5Tail5 : Box := ⟨5567004179392107561888799775167355800778935659543041552444,4004407246121608051283747281833114322123172096952505319850⟩
def polyval5Tail9 : Box := ⟨6120983505081744250948213480957606197913762116853510676784,4072757298997162703470252547598836650432149511814026650102⟩
def polyval5Tail13 : Box := ⟨6730092537036391788275188649737350825690830673965697855858,4126443660479824556699944605083889834386375603788162900721⟩
def polyval5Tail17 : Box := ⟨7399815000479814427440523927575458084108501276457852328604,4162611440971126832319688023428140960339390743901701502805⟩
def polyval5Tail21 : Box := ⟨8136182636418822360521976592693564424049556678591004156250,4178030919517346414510103665365239820913622335658371780653⟩
def polyval5Tail25 : Box := ⟨8945827414451686545631472013150275417100138033126718540128,4169054333688817683138916691785723915002794999406175053101⟩
def polyval5Tail29 : Box := ⟨9836041262266939260056826498821628234895607979387770165631,4131567995637707224571596981578224736495457175150953640342⟩
def polyval5Tail33 : Box := ⟨10814841739147024113635479619191701526246197979122806973233,4060939234567438930863519823801906183168958349288408525562⟩
def polyval5Tail37 : Box := ⟨11891044244749371264966945589344363699406259023950903722826,3951957624213414132744979982810303709312515558651682588266⟩
def polyval5Tail41 : Box := ⟨13074341413500817740696924752821806160325626927292595908213,3798769898333976148468304290147517360554294512569103012463⟩
def polyval5Tail45 : Box := ⟨14375390409657452816788011806423623867554105198098298783271,3594807895962404516325085751903666886259791431540976793590⟩
def polyval5Tail49 : Box := ⟨15805908909237965417231613481352741757017831040768578098467,3332708810708040947403252414344989088635137077244212689931⟩
def polyval5Tail53 : Box := ⟨17378780633275416001362629551359138964992940194056921491063,3004226944091255390836852718365644156002142929738260044948⟩
def polyval5Tail57 : Box := ⟨19108171382854676867526637547759886409974762029390092714669,2600136081063843513055099774186376277753347650528264203690⟩
def polyval5Tail61 : Box := ⟨21009656620985350200270945247717274872873028323840326238567,2110121515745488606055441979978933579134072970944301774856⟩
def polyval5Tail65 : Box := ⟨23100361750377787427613214867415948150044347337108826180559,1522660656162905063635097503739157123161255741759775153545⟩
def polyval5Tail69 : Box := ⟨25399116547060364185789715092081707373875450379142938688695,824891020388968903928496514805863651245491344486065562750⟩
def polyval5Tail73 : Box := ⟨28031250000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨91449703876386868743588172001052032231889856508530112920,11850955467667044678701225781052412505331127789184021781⟩
def polyval6 : Box := ⟨15767272411067590294437827045879236092116706109328640254845,3928888760602900756890890865489991675550091885476072880029⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-29970919162820634980467110735438413566552486085334858383,11611001184783290518744003613542369792926627043241401035⟩
def resval6Tail8 : Box := ⟨-31418013859014230359289679339703462657990246864893813767,11489185866988618495737099846237985757574726010801440698⟩
def resval6Tail12 : Box := ⟨-32934911712815257503220772255075225462973575120013171046,11339741348753659093906801016348062206028953257629818986⟩
def resval6Tail16 : Box := ⟨-34525047131931923058556587625671649137446411030274856466,11160640023260430191276168228283614997043354317408475819⟩
def resval6Tail20 : Box := ⟨-36191956118044406616947423144549203427892943927274436453,10949734816028723463489357123157891620610175767117076383⟩
def resval6Tail24 : Box := ⟨-37939345387278984780879208911971539334507392024922581169,10704752195722875716246387887943787078732524997699656542⟩
def resval6Tail28 : Box := ⟨-39771100620272946641047085923214513093285283023953337231,10423285342117884522185571095603139581450456486022184418⟩
def resval6Tail32 : Box := ⟨-41691295102794018160773663351682284700099814816733363322,10102786961169704289249822971827040580926918563347870773⟩
def resval6Tail36 : Box := ⟨-43704198783531869151924984547620497059895839237140750961,9740561729299617556860173296091127926293709931807123964⟩
def resval6Tail40 : Box := ⟨-45814287769210186020618679554440593518709310054625121327,9333758348229204113807857259302284516705079415785151526⟩
def resval6Tail44 : Box := ⟨-48026254278133676313588375816599709347060973069126636561,8879361190777221769349007286510275301866122363528051303⟩
def resval6Tail48 : Box := ⟨-50345017074303771159769022223076388479429240179531861071,8374181517058911366926806525850528244290128714708147690⟩
def resval6Tail52 : Box := ⟨-52775732405305434820140702528958333461699250807065365508,7814848239509767231139199315504132601400072621425113632⟩
def resval6Tail56 : Box := ⟨-55323805468287704162904700259462838636976180344808606133,7197798214087344838509986863805567523619417144373775783⟩
def resval6Tail60 : Box := ⟨-57994902429526942201876401197916605772029737509405207084,6519266033883390955622788340067296406174091988647829807⟩
def resval6Tail64 : Box := ⟨-60794963011753468582172436312843330264911703716174674770,5775273299765947027610558328504698517249415146783927750⟩
def resval6Tail68 : Box := ⟨-63729990906930463831972134360119606030356671102231216064,4961611976100743103988954424344125304498524011835909950⟩
def resval6Tail72 : Box := ⟨857403176700397232635337522419959938338625273378871038284,674486678760304204116713578172050302378092078925142480⟩
def resval6Tail76 : Box := ⟨-409641386700705673544218351744431771476786408643355101,160960498216842758433186758706638267800265619388083200⟩
def resval6Tail80 : Box := ⟨-429388708628964774291005407258878758698178799912541007,159367960663090310165294199820494959227060669998982871⟩
def resval6Tail84 : Box := ⟨-450120087702609849317500395274055141114195942505748509,157400266962480092565122244889326368189080675832863354⟩
def resval6Tail88 : Box := ⟨-471852403262427759497859236479071480400064013699651520,155029637461832326372078367879343180108737913150741227⟩
def resval6Tail92 : Box := ⟨-494633980014841517228907410449259097055891120851469080,152226804098049920874229437240139430303946885823425084⟩
def resval6Tail96 : Box := ⟨-518515477496150528622031935007417006680715349909446078,148960772963537249297840015677080592775043287296615585⟩
def resval6Tail100 : Box := ⟨-543550001144268113729564623443224512220404433231795668,145198730994006063092551363283744871591005041969929037⟩
def resval6Tail104 : Box := ⟨-569793220388734241402207187916457236705298141429474034,140905947851904179798111136877202322025580455161140365⟩
def resval6Tail108 : Box := ⟨-597303492443177867390051022273481316051914508549399404,136045672744878004665619452775155625915321611416464866⟩
def resval6Tail112 : Box := ⟨-626141992074624207427679244344998091975453127843821827,130579025924263202936559997421251426679036814427618684⟩
def resval6Tail116 : Box := ⟨-656372847638213447720259133702251163132174180864703204,124464884595969110345916221138480154775955231042860599⟩
def resval6Tail120 : Box := ⟨-688063283679832142016165936054245256900120194013584661,117659762962857275493923156217756366223629298002403110⟩
def resval6Tail124 : Box := ⟨-721283770423763676024226998728844454476585641209376093,110117686103797864465506777214735149114680206487204462⟩
def resval6Tail128 : Box := ⟨-756108180477774605278478062919443121018113871509757160,101790057379987770983518848382461821564500044970873348⟩
def resval6Tail132 : Box := ⟨-792613953104139879685155934050678385015442592103799566,92625519043795687873938828993239575697192140284763945⟩
def resval6Tail136 : Box := ⟨-830882266458788400880025194866408078790892948957225386,82569805707663636044294824235051762038085292017164591⟩
def resval6Tail140 : Box := ⟨-870998543861178588100599127348617002147316502184678938,71565578870216439856035885497216534224918279779883454⟩
def resval6Tail144 : Box := ⟨-1056521100897312527819894140229857162486957803835606845,56675870041331168467599482381612471476865830263231580⟩
def resval6Tail148 : Box := ⟨273030267102974584904546992307359037377430740829,87886283217689390730502155805618311217566857175⟩
def resval6Tail152 : Box := ⟨286136835426170612629316838127527859196485740421,86207151754778788045068609844077633163437244367⟩
def resval6Tail156 : Box := ⟨299951849604463783432789357569569907574113864897,84258746677270327415247641015627966425289857273⟩
def resval6Tail160 : Box := ⟨314433869906455864269689592668627280461398980584,82021525893171497279727254810522226020613151065⟩
def resval6Tail164 : Box := ⟨329615098806224526229294723504794740411683881410,79475338521420665156940024874893208944832467496⟩
def resval6Tail168 : Box := ⟨345529294898668654299309134686962130702863614237,76598862987489212160108098748538862096602166892⟩
def resval6Tail172 : Box := ⟨362211846682906058265415470203119419996116998455,73369544181150922036536399303385008334358432117⟩
def resval6Tail176 : Box := ⟨379699851255496415747794671885408227615200251091,69763527395103461556219372288341587563640138353⟩
def resval6Tail180 : Box := ⟨398032196803490254888500043938398343782397465526,65755588866768632887214710458677153405809655799⟩
def resval6Tail184 : Box := ⟨417249649080337953752556855442656301863424667989,61319062752654255293549543107818317546437064401⟩
def resval6Tail188 : Box := ⟨437394942056955094998289800533714721922726793727,56425764356220102717119978626112823380103823843⟩
def resval6Tail192 : Box := ⟨458512872949525522473853271946399498040616421542,51045909421327962096105399524821176513157916640⟩
def resval6Tail196 : Box := ⟨480650401835356030042136079268445886986874061766,45148029294058687543443951347975307943266699185⟩
def resval6Tail200 : Box := ⟨503856756078299093546023581439753672544835940874,38698881745925911292772591373837577894492129203⟩
def resval6Tail204 : Box := ⟨528183539795955243456445436554802159629018082088,31663357241284580364616186963949692628367600716⟩
def resval6Tail208 : Box := ⟨553684848612134519392131478006218986441808711132,24004380420996296584884473057598282936802209696⟩
def resval6Tail212 : Box := ⟨580417390108977161912400434788259006102494544619,15682806556196859925183986104466807236410584945⟩
def resval6Tail216 : Box := ⟨608448202792315544971739613820608095946786408131,6657054490360957193612786008614521915446475667⟩
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
def polyval6Tail5 : Box := ⟨12528966704065499638066016039687535202961202312853524974462,3855947801012839487478723218751589670812801266119507903436⟩
def polyval6Tail9 : Box := ⟨13133877415283703136918451961683074668398820534734850871822,3773222461205491851767495101105848766356667180853436007041⟩
def polyval6Tail13 : Box := ⟨13767996123216078217526209987695102140386625506698316015526,3677933370012368645461590741237155077884999999955267087230⟩
def polyval6Tail17 : Box := ⟨14432730811943504089261439375437933566149956422196217819350,3569200809083364894578922112170876091412925081081632738108⟩
def polyval6Tail21 : Box := ⟨15129559656018263834257462866380987836163666402286502588466,3446093891929189785533877159053045029328163252560188060617⟩
def polyval6Tail25 : Box := ⟨15860032198174938265995569980070158341708950551483793729549,3307627806173537144776841584525832463856514679993717480282⟩
def polyval6Tail29 : Box := ⟨16625772794853779980627528427675011127625956370425199255203,3152760923702601812123256047883900732738728603301951350985⟩
def polyval6Tail33 : Box := ⟨17428484228292306369650253305352926788130686069659059588101,2980391762168930955019906168986237816819965968854863731680⟩
def polyval6Tail37 : Box := ⟨18269951493012996064582803735088934752737210179925963272119,2789355790379837276816860154468870732010075673325022109699⟩
def polyval6Tail41 : Box := ⟨19152045765126967128648958456582370687956787818610766203580,2578422069732934694701061241756840766041405615992331457285⟩
def polyval6Tail45 : Box := ⟨20076728563280202316035158964293534944055450699631338452401,2346289723473398124527829188037380810405763490685594249931⟩
def polyval6Tail49 : Box := ⟨21046056110495043991983591901675449818448778108896192183759,2091584225140551491689061460428279243207943644089706481889⟩
def polyval6Tail53 : Box := ⟨22062183906606413403152592490694878033195836083170071562094,1812853497144425822826403079394567133834094238639914829179⟩
def polyval6Tail57 : Box := ⟨23127371521460509914311742834710209403756692168010647298285,1508563809965028327142481184414835487705912436266002638494⟩
def polyval6Tail61 : Box := ⟨24243987619534679356360862081367756555596741376057739605666,1177095471997201196750174273008280878506255028062373033538⟩
def polyval6Tail65 : Box := ⟨25414515227174722769808142017000137519579732887219271116995,816738299570059531402351970696553724149025465271094643739⟩
def polyval6Tail69 : Box := ⟨26641557448555343992064310232171515909238330178335403227340,425686849830196288560707726675497511920246230276077253092⟩
def polyval6Tail73 : Box := ⟨28031250000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨74940554880814748378636083372533818691395926654840125962,18992759816426872763629367309536614035351947310950074396⟩
def polyval7 : Box := ⟨24885015442482167368192495807503524144837830762104524570919,6862568833692737488579308604156334323567463042525003013178⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-45806337321686707953549650192018088600834841557545963129,18137328355065671955050160025854643615920375711984428313⟩
def resval7Tail8 : Box := ⟨-46529168033674597155142453320817279804760795080300569403,17414558400237067290958873391299843473164419636466957527⟩
def resval7Tail12 : Box := ⟨-47263341928001191079067069116007424690614269753207921449,16680384513236852919086019790552791282819009556295543931⟩
def resval7Tail16 : Box := ⟨-48009100189149677740693152146485225081344076721982063114,15934626252094978504982934899738365984940606218584658351⟩
def resval7Tail20 : Box := ⟨-48766625611930322856561106627389399909755811569166467297,15177100829314359329585952059429606254092845465516798314⟩
def resval7Tail24 : Box := ⟨-49536103867900859264084503802292731315760875788245647083,14407622573343823259256058666960881967771983032011207461⟩
def resval7Tail28 : Box := ⟨-50317723558284413371453369320533016482490566896677050877,13626002882960269163931238510855625525416525026696383516⟩
def resval7Tail32 : Box := ⟨-51111676260202836321176277373490112351846697951559547411,12832050181041846215173547433204402115301558410701120748⟩
def resval7Tail36 : Box := ⟨-51918156573632805488329922302888142833911422297745374400,12025569867611877048099291800547460331384490481314388751⟩
def resval7Tail40 : Box := ⟨-52737362169102810807144279403928146108235312092626207127,11206364272141871729081531215453819971982052755276533902⟩
def resval7Tail44 : Box := ⟨-53569493836142741437886932068079149929409781962928234099,10374232605101941097092109421251491978425823506880032361⟩
def resval7Tail48 : Box := ⟨-54414755532497948182121660064596690784273388089587885335,9528970908746734339218088828430675104383262239204700900⟩
def resval7Tail52 : Box := ⟨-55273354434119843878559310275480054764663545506152968621,8670372007124838273851842257482658050694856802585483239⟩
def resval7Tail56 : Box := ⟨-56145500985945269085059733067672238892646030738615797295,7798225455299383842863963034337460806925856206529446246⟩
def resval7Tail60 : Box := ⟨-57031408953469131368583407666267595519819853522357360837,6912317487767033457912084091763172569552492606979902197⟩
def resval7Tail64 : Box := ⟨-57931295462662668979730386606802781041948328869097285745,6012430965629381094269086714316558743901080211335272813⟩
def resval7Tail68 : Box := ⟨-58845159901606801257811015561168421670950367007745329328,5098339996669673833551520130385140790470527893618918398⟩
def resval7Tail72 : Box := ⟨857240323630017757548772965769151457800314132456109305208,771465068278509131337778451954333986168900266500863592⟩
def resval7Tail76 : Box := ⟨-628153717229959340338018595926794874464379233817391348,251112947356117307214099456177550567807886761270805722⟩
def resval7Tail80 : Box := ⟨-638035549627198827627535118750763436649532974562944698,241201754930963256795701806165835474939716843523676742⟩
def resval7Tail84 : Box := ⟨-648102975811164213195526389244908592746617792391510396,231134327146855559022198272728492296334680038780567816⟩
def resval7Tail88 : Box := ⟨-658329255386884893832300802313845891163916667814868372,220908047570222909645859216886650369712464261461539102⟩
def resval7Tail92 : Box := ⟨-668716893262847177638509066150112716202840968214299518,210520409694258098197400266177455648110283707880020510⟩
def resval7Tail96 : Box := ⟨-679268435476587023937104482058991504960732918251399490,199968867480518226983237734810564068950814047426414178⟩
def resval7Tail100 : Box := ⟨-689986468239930181193381647413987056188569238533386515,189250834717175069005335543045667964330182335038001195⟩
def resval7Tail104 : Box := ⟨-700873618571993425612996330444004408610973088887150049,178363684385111824532897730314342927196970900970151620⟩
def resval7Tail108 : Box := ⟨-711932554943071754292746807919222393797008693640210442,167304748014033495845278199582525973047877765559588338⟩
def resval7Tail112 : Box := ⟨-723165987928687724482659511944796930549926756493215750,156071315028417525655132305630759970128477507024036359⟩
def resval7Tail116 : Box := ⟨-734576670873960920164160404169120710085908269827396227,144660632083144329984628365231458998265639812903873636⟩
def resval7Tail120 : Box := ⟨-746167400568460364307646083581600068876299981896553784,133069902388644885960266796172554083355876442912246247⟩
def resval7Tail124 : Box := ⟨-757941017931705286856300381937929842309453558677360421,121296285025399966096567901259888125602740698118067701⟩
def resval7Tail128 : Box := ⟨-769900408709482432076564027192715351135904508965456607,109336894247622988220527786255271115311259632661101152⟩
def resval7Tail132 : Box := ⟨-782048504181187254306478309980380475037227809943907064,97188798775953665822338592256341304711308013146255925⟩
def resval7Tail136 : Box := ⟨-794388281915001411845877253489554456656241344137269349,84849021077335294489201589037380726431401543322915538⟩
def resval7Tail140 : Box := ⟨-806923089881455124784641610294671321826476402777933979,72314525291668081184081009930258156731927705722414709⟩
def resval7Tail144 : Box := ⟨-962023962705954712242929763031321782800513341296758185,56732994138815808741107481520080490021100928930756148⟩
def resval7Tail148 : Box := ⟨473806166187715812604413788571316529743499935250,151176794957705664900709058115737150294745890023⟩
def resval7Tail152 : Box := ⟨481208973968180419982618888212994098816880400567,143701343725121713523511032261104563046382769985⟩
def resval7Tail156 : Box := ⟨488801867133816424177491151965433763756919141341,136108449257847852516075150636105917620614841479⟩
def resval7Tail160 : Box := ⟨496514568258762423775534944006674673661016569260,128395748132484239177069978333557165267627423932⟩
def resval7Tail164 : Box := ⟨504348966461499949069208746663535848115625293322,120561349929745978461374658795356999753982998291⟩
def resval7Tail168 : Box := ⟨512306981974026930845621096537173191022967882471,112603334417218991791971632228426295801599222832⟩
def resval7Tail172 : Box := ⟨520390565327689672842108747495905861619952830599,104519751063556249695918044704872747269173855057⟩
def resval7Tail176 : Box := ⟨528601697830856151785669204685375714997879145535,96308618560389770747025970132452738638519536335⟩
def resval7Tail180 : Box := ⟨536942392054539414062653311401524008790033955211,87967924336706508469401631933298408355883044774⟩
def resval7Tail184 : Box := ⟨545414692325684225906521279220004260651883856535,79495624065561696625427035057045658071286512515⟩
def resval7Tail188 : Box := ⟨554020675228237193506628909961554667623817589439,70889641163008729025483033079411215263789331771⟩
def resval7Tail192 : Box := ⟨562762450112123162484062687003401934397136825777,62147866279122760049693639532204723168119901383⟩
def resval7Tail196 : Box := ⟨571642159610252648189983122045507342918803121881,53268156780993274369467056449654864867166870710⟩
def resval7Tail200 : Box := ⟨580661980163687017703808293573287280575173760040,44248336227558905846500845222408127574684968709⟩
def resval7Tail204 : Box := ⟨589824122555090262723297027360590608825490444797,35086193836155777722775811289051551784013149405⟩
def resval7Tail208 : Box := ⟨599130832450654266252280568043723474470687526475,25779483940645524254713579420930170418862727761⟩
def resval7Tail212 : Box := ⟨608584391108729819762699943609201966281730966772,16325925434094426918233327440141958645891903562⟩
def resval7Tail216 : Box := ⟨618194651908642328355303996443592485225363309525,6722945284479280429679232490527611134289392988⟩
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
def polyval7Tail5 : Box := ⟨21402496918918893885640443760309428962668001596289898501866,6528160410902023555250082568622486434665200929062995574104⟩
def polyval7Tail9 : Box := ⟨21740200242139903619212598676467411747885901785574235731392,6190454969243327198421815750203517901359901456569613441820⟩
def polyval7Tail13 : Box := ⟨22083234256626216180825250918363612593216981945908155739000,5847420954549735473734805340678411471451741804622075258164⟩
def polyval7Tail17 : Box := ⟨22431680932375141779033003478340394914957876114369297555707,5498974278800645587450560423148944235707252014023591029084⟩
def polyval7Tail21 : Box := ⟨22785625674414231093262369270017710237172223237231584372159,5145029536761555696410812909700399421964934243365780534373⟩
def polyval7Tail25 : Box := ⟨23145155235566734286091442697324346603238529067635429186430,4785499975609052496766652848585216929704398192064387529424⟩
def polyval7Tail29 : Box := ⟨23510357737510486333426399104405402732860525596276571733856,4420297473665300449204120445422666785900202052477622765138⟩
def polyval7Tail33 : Box := ⟨23881322692376611724393591123654886143496882437832979171880,4049332518799175058218353650060449532448681383744251610399⟩
def polyval7Tail37 : Box := ⟨24258141024689191850246800359735675970174498411997784849552,3672514186486594932362215093957497531065075748217292654848⟩
def polyval7Tail41 : Box := ⟨24640905093651114297767769415677237710457814968513512079291,3289750117524672484841392747245009512429123282281293145847⟩
def polyval7Tail45 : Box := ⟨25029708715781565843888934270422777224899408050744715043126,2900946495394220938726120118672775776035148129267332864179⟩
def polyval7Tail49 : Box := ⟨25424647187910717657492449381601114291807366896434280969745,2506008023265069125187743119475247148050071545203917206724⟩
def polyval7Tail53 : Box := ⟨25825817310537238769766215359647483348264361233187520775058,2104837900638548014446361665670472859614891152915123187296⟩
def polyval7Tail57 : Box := ⟨26233317411554362902119761349626781387620561968966106081391,1697337799621423981722298510873039082955846430994403372044⟩
def polyval7Tail61 : Box := ⟨26647247370350346526948157697746519433026202953177647589514,1283407840825462207832964550478756500423447987076092374980⟩
def polyval7Tail65 : Box := ⟨27067708642312060374193665378631594441131273849971604579974,862946568885723983653746356206753092634970895348463556393⟩
def polyval7Tail69 : Box := ⟨27494804476718477679269260174485877468626495203838751859555,435850921326288177980126391808173457314678563445142518912⟩
def polyval7Tail73 : Box := ⟨28031250000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1031743823211743129393932434011260290396715063089275609408264,3761064431775462839370400399568071690230715353918175900⟩
def zend : Box := ⟨1003811152536990166349179687500000000000000000000000000000000,2048027805117408476562500000000000000000000000000000002⟩
def betaquot : Box := ⟨428762629716017953225304190957193668306531600740916542172540,394796260959611110911084955784738177615271783945896678⟩
def crit : Box := ⟨174098573595319550292316623300662761177478625659756572469,9231572427617202285782311872035765948329536281064547132⟩
def subsonic : Box := ⟨390601070040373909662962497469682434169151705027034420232,4488134022922020620848063839481558217935574839111405335⟩
def pendTail4 : Box := ⟨27928996121823643040053675729111251527760918118226799814958,1622593747578123664377554835996823212603764284767200341⟩
def pendTail8 : Box := ⟨27929032735512279766076841343409377586125912692648414947534,1622474048528495863586191126339727368086768486410832437⟩
def pendTail12 : Box := ⟨27929032737141961461993932123593492635407350850834531802419,1622474033010231094278396380542866366459237235831971224⟩
def pendTail16 : Box := ⟨27929032737142787679289223256691938859723949665171472135635,1622474032997087345364281442924719424016650579883648345⟩
def pendTail20 : Box := ⟨27929032737142789727001607382710925428245239840453809061968,1622474032997037809566966571043014205907940592682253044⟩
def pendTail24 : Box := ⟨27929032737142789744987856145138805501093718775404727389745,1622474032997037152507380133283041104656529851292435347⟩
def pendTail28 : Box := ⟨27929032737142789745448253127685650182641917495530591241466,1622474032997037126152307934819927908505697317499130540⟩
def pendTail32 : Box := ⟨27929032737142789745477586249336035566300201407684434357947,1622474032997037123237566170788453391742892477726943809⟩
def pendTail36 : Box := ⟨27929032737142789745481233825214927386404362181120189474186,1622474032997037122394642515293524530762119069554316790⟩
def pendTail40 : Box := ⟨27929032737142789745481092382737389679731689662320219190156,1622474032997037121772817855396971218787766331145329405⟩
def pendTail44 : Box := ⟨27929032737142789745476528168757103096198012819376849516081,1622474032997037120604566961655966844442953100790868390⟩
def pendTail48 : Box := ⟨27929032737142789745437060636613616216184190390458406095698,1622474032997037114896563485932337556189445741188433402⟩
def pendTail52 : Box := ⟨27929032737142789744722963327653711864357694230480693254472,1622474032997037038850478647252169702838506481914576180⟩
def pendTail56 : Box := ⟨27929032737142789710402084598225136777956265604661479616735,1622474032997034287517950267241474053803833339698208091⟩
def pendTail60 : Box := ⟨27929032737142784403618842504561659380764836242700181202890,1622474032996724658963958519415348325923700424494972777⟩
def pendTail64 : Box := ⟨27929032737139335099346109966011465748191303550032108847620,1622474032847485232105894491826461468242790473758568652⟩
def pendTail68 : Box := ⟨27929032721631541567188655018954966942487509240344958328136,1622473542319511463414527487331881160108172324919414761⟩
def pendTail72 : Box := ⟨27927172427315187646395175854014946171052940490470256900167,1584784304785175334978871893593385610535334477129983743⟩
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
end SepticProfile.ExteriorCertificates.C32

end
end

end OAI
