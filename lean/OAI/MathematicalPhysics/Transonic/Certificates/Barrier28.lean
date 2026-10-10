import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData28

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C28
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨118658430666828997611423422884124426319514188885573892757,308364749572038515120385006711011592544398635172510137⟩
def polyval0 : Box := ⟨3839216988419438987026837581069704640334922513795062034251,14827154252776148930864688450629311843261625129970622099⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨63102901220812358995149790933311059949688666314042,1829834865298084415183840309596203156664443482231⟩
def resval0Tail8 : Box := ⟨7899993701002883981830678878303003395432868519,417704722148141967538093852426360945077194347⟩
def resval0Tail12 : Box := ⟨7434811680822685318498971463522515759067345,597685004377633120514695451186675201329387⟩
def resval0Tail16 : Box := ⟨30790733764536879371838997864677726852913,28322587726967180413208009644471145881283⟩
def resval0Tail20 : Box := ⟨433563735630531799239146222121686343601,396914019342374349070772034485661382156860⟩
def resval0Tail24 : Box := ⟨17813199776513650518254919859598910322,6349527718946733057187568041396007916216164⟩
def resval0Tail28 : Box := ⟨1943033024216535375404177871680731514,101592381712200403761110227057867142084633006⟩
def resval0Tail32 : Box := ⟨529496971184199918555455675202254481,1625478098102134347573701953820994122705456521⟩
def resval0Tail36 : Box := ⟨-215326399575155103184938240478440727,26007649566020445000563871193898367745821114074⟩
def resval0Tail40 : Box := ⟨-145322382213657290515842985909272849191,416122392918260683292936889221761016548344908359⟩
def resval0Tail44 : Box := ⟨-37346830829855765931027296093426701439461,6657958251675086490204286939251625245437295421687⟩
def resval0Tail48 : Box := ⟨-9561347701483059389977311643274911850852276,106527323063007708410033468042932450249425020418356⟩
def resval0Tail52 : Box := ⟨-2447710283379891972065134692991727230800622307,1704434874279107626413070615452461901048445931530204⟩
def resval0Tail56 : Box := ⟨-626613942107810602894878789582352831120794931332,27270370537852082591129780937456535399987212714798746⟩
def resval0Tail60 : Box := ⟨-160413165451352770886015189332495327525359990810899,436175541251293332427512359702938075549689007666631268⟩
def resval0Tail64 : Box := ⟨-41065743972702832833592813765670557101372318106333568,6940309507258733834606816595824537008821135082803418076⟩
def resval0Tail68 : Box := ⟨-10512212117351966366291648192755870051703465194631732976,101189433551561895118244450137849983823964188169447884013⟩
def resval0Tail72 : Box := ⟨833801740227203448573033173458027025597243793971886745603,2525426526206008297220863472450103105173264257686939309⟩
def resval0Tail76 : Box := ⟨-29519147870449073034255909039278408180836792609824,634393287227406500974593951772885015984377346005⟩
def resval0Tail80 : Box := ⟨-1651283609376248154737854036578676295294369351,74992242537274026179331001526163166131378283⟩
def resval0Tail84 : Box := ⟨-966470907138635505838383243917662291541046,69175426505676832473443325186413593289756⟩
def resval0Tail88 : Box := ⟨-2766136270820640487561574532711411260396,458331268357314361242563389524076147409⟩
def resval0Tail92 : Box := ⟨-28487157333282636929584903281658791061,2750335905118150702530172246610525631259⟩
def resval0Tail96 : Box := ⟨-886122259171070928654040022695408568,43939533399682547437160446516121880777979⟩
def resval0Tail100 : Box := ⟨-74780326407740889391550075613534560,703029718946858887937048169807245006811521⟩
def resval0Tail104 : Box := ⟨-16047352778745097174563733656290124,11248475176115413258996601407907816317642959⟩
def resval0Tail108 : Box := ⟨-10391016434265245331375510155405009,179975602719165570717083520189376522569845596⟩
def resval0Tail112 : Box := ⟨-510677611120320088719021151591192624,2879609643044687345986173860000043473351227626⟩
def resval0Tail116 : Box := ⟨-128012760676004187748095415578376631902,46073754168742186270099604004866565754026863772⟩
def resval0Tail120 : Box := ⟨-32762935672690810124118293512467472241734,737180035984840007919323054067291371293205124665⟩
def resval0Tail124 : Box := ⟨-8387249274580773375069783483821828803104424,11794872712714932777977726346284050931732457224359⟩
def resval0Tail128 : Box := ⟨-2147134728138726627482530898009336541338746641,188715950464839461724269127326302580900090868136657⟩
def resval0Tail132 : Box := ⟨-549666479403008011800188674434557528172604177617,3018939895157093077686462219674466550165583112054449⟩
def resval0Tail136 : Box := ⟨-140714685607267432526144983988854741779462868274819,48171118349849584742333410017352317821847985018640831⟩
def resval0Tail140 : Box := ⟨-36023806742250280026878407861696717429187468205174086,736965992214340173936939942682683113325727784550625260⟩
def resval0Tail144 : Box := ⟨-9683852971969490223319928305536339120906808866226385561,2919304368993118042857817081662355181403906300004233395⟩
def resval0Tail148 : Box := ⟨70223135972300240075634959465151001072046509,1238957079986056161647464823798865955396159⟩
def resval0Tail152 : Box := ⟨1295940591072922569704012259783409732231,52450290320926019191101102732493912453⟩
def resval0Tail156 : Box := ⟨426142252055521155708957394417436671,27774341407435885908392361443600314⟩
def resval0Tail160 : Box := ⟨772290813093251372907345025970243,75173837545165996256910142452128⟩
def resval0Tail164 : Box := ⟨5332632177166048695801577539972,33107450956902393768281754087618⟩
def resval0Tail168 : Box := ⟨114803912371166817878536355921,518470184654971684484106856209397⟩
def resval0Tail172 : Box := ⟨6818855459037730164312107749,8295191845204407541263550184441319⟩
def resval0Tail176 : Box := ⟨1036099404933743910825186980,132723042708665693912317678618204264⟩
def resval0Tail180 : Box := ⟨392927224703157334348985642,2123568677720751700152031352854705678⟩
def resval0Tail184 : Box := ⟨2266722234780003951152999646,33977098839670923298168444420864298458⟩
def resval0Tail188 : Box := ⟨492902263158653296982683393539,543633580973643311199743346429845011846⟩
def resval0Tail192 : Box := ⟨125997636308993929514335233142079,8698137177459069870893389940049116291556⟩
def resval0Tail196 : Box := ⟨32254447851492706802524316686397880,139170164600837426722361661801997539308754⟩
def resval0Tail200 : Box := ⟨8257127031250951188655981779260044338,2226714892558023194442209461330997684048465⟩
def resval0Tail204 : Box := ⟨2113824248022375694438823146966241304210,35625456570835190458119842034230164144816020⟩
def resval0Tail208 : Box := ⟨541139067609011535353251719135621685809893,569499987322868360962532988871046916516593086⟩
def resval0Tail212 : Box := ⟨138531956466198282977448991308221209812102810,8982126279182701422601106743497729977417441199⟩
def resval0Tail216 : Box := ⟨35485106299339112208239140435047381171541822631,110456376055102761418328304903288868091768035742⟩
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
def polyval0Tail5 : Box := ⟨2190331741581882779926722483068929760266881813190482,53731645698865194586065818181516553172214945622409⟩
def polyval0Tail9 : Box := ⟨219787183382457704866627048717804108934426827492,10660134524181948990305975284318636373999763081⟩
def polyval0Tail13 : Box := ⟨178973079265698590506004451573109350455437464,13467529018861902437490121022215378414855590⟩
def polyval0Tail17 : Box := ⟨649504963113876993558669324555820013108386,453276147161449505169032454430399113901447⟩
def polyval0Tail21 : Box := ⟨8036227835161659291214300622253526730645,6131395482771710522463980349506305282051864⟩
def polyval0Tail25 : Box := ⟨289795640950897201088402323470910172822,98083066341878914522449050433560951695070852⟩
def polyval0Tail29 : Box := ⟨27646036867465613335748766792992939557,1569328109291708819171868957437615109708221207⟩
def polyval0Tail33 : Box := ⟨6601707812237458381424373150113953740,25109249623830828358362848977696359552521003653⟩
def polyval0Tail37 : Box := ⟨9595345360896338190881234512847442597,401747993937974024226096911905799820222722643983⟩
def polyval0Tail41 : Box := ⟨1492690841796065376644258687797724189877,6427967901617734681531427211054014751835351333012⟩
def polyval0Tail45 : Box := ⟨380810827838284234681047769404610721573851,102847486068893542721568887078445730571654344432808⟩
def polyval0Tail49 : Box := ⟨97483255476014047509099169516468846561526019,1645559685711863368242155925043947810328164817552736⟩
def polyval0Tail53 : Box := ⟨24955679248769965338424281849022388953797663657,26328931575442655544147540504885646604646846025438454⟩
def polyval0Tail57 : Box := ⟨6388653266176225891346398772808006404300152354792,421256915844772172432449828893405873173205708024506147⟩
def polyval0Tail61 : Box := ⟨1635495231212094227459358593554549185975882280261173,6738577376764909135963147131100104548746928369633838139⟩
def polyval0Tail65 : Box := ⟨418686822175298376264835705382837735050610149173440711,107424719161372836679748613557979941404585834043717357114⟩
def polyval0Tail69 : Box := ⟨107184348034547203272626619774443709517597142229275103391,1618310438959179734399035863496466729196289045129873939471⟩
def polyval0Tail73 : Box := ⟨27781250000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨118420728381773490517403887029620764490870822232490704417,227229630428101725186856107273120124934326828613863341⟩
def polyval1 : Box := ⟨3820718192876165183748178533826965615326685234782366445631,8521443006973677697476729163920486678982370164759729496⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨61257284036197724168223205997994613774408933980494,3186697279509863509011168780980896700799287533958⟩
def resval1Tail8 : Box := ⟨7447856715486826245385779335531084719783684302,6441153425723375196774766494563946465953122183552⟩
def resval1Tail12 : Box := ⟨-329250317818155675493396381994947018673000495,20356311864062134658246704863529532172102424186818⟩
def resval1Tail16 : Box := ⟨-2202921694264546477118752142766121301201079496,64334856493846985817000763862839669358101484679268⟩
def resval1Tail20 : Box := ⟨-14437249604361105910886721627870817531940033316,203322441973451871405850472839455638459982215909325⟩
def resval1Tail24 : Box := ⟨-94615961489914176312132946099056382084554895075,642550335658159302463892684173448577809714206766865⟩
def resval1Tail28 : Box := ⟨-620075165318303572437674421526408599676435825112,2030455327484479191720914912034425472405532850997136⟩
def resval1Tail32 : Box := ⟨-4063724603440128423029411985114631805867549637783,6415137547968763411819590523118555715348490598698023⟩
def resval1Tail36 : Box := ⟨-26632025561107732019853507030528991971760722159612,20261213971704129015753178181220727540441683507998783⟩
def resval1Tail40 : Box := ⟨-174535642717276994123931228598627807116291495516774,63945076398022236954199792997480630984574933627155892⟩
def resval1Tail44 : Box := ⟨-1143836788111947672202499657165542012602850574829735,201505801266570960033588830545612160447576082620107248⟩
def resval1Tail48 : Box := ⟨-7496248774570455328462945691375788853989351372289143,632976681373563167234257584222929492534582767564839848⟩
def resval1Tail52 : Box := ⟨-49127415969024631603035483486691476176810517749594596,1975083326227545465160677198274615075632039804947127028⟩
def resval1Tail56 : Box := ⟨-321961433294569782299706248824153367979381754918039207,6075544122289621444121788229719618863019280704826571926⟩
def resval1Tail60 : Box := ⟨-2110006449229706032668258363569338903292810329397254892,18109270368410118604066979501281755488121171654414621879⟩
def resval1Tail64 : Box := ⟨-13828138250231838915225557018668200534419971310377941077,50074761307689361328696643519333339448060573558929107308⟩
def resval1Tail68 : Box := ⟨-90623803472101681218780473490073449774194795492383132123,111340668720592841623825903119361087666952723528713713083⟩
def resval1Tail72 : Box := ⟨836842552283080155734379487253869314241180023925351960604,1511402911680836632785707467817611280756415694590492154⟩
def resval1Tail76 : Box := ⟨-28855330541884685291375672889038813347356363006776,414737096260154141098345246859880256827655545625⟩
def resval1Tail80 : Box := ⟨-1577649031578297506517578229401726203430606734,66860716904360268217656070831641897551044064567⟩
def resval1Tail84 : Box := ⟨-3798319299352234126047607642588742394198779,211166575723440203575575284767706270112105394987⟩
def resval1Tail88 : Box := ⟨-18984059511884825811012766659970175947927769,667380845594192450062725696743720495811230463030⟩
def resval1Tail92 : Box := ⟨-124397457207448948313880041611129787295733665,2109188636523199910914244206680541335283871590630⟩
def resval1Tail96 : Box := ⟨-815251010922060836087492259331639452793170367,6665655572354652293690359017326755189124953111000⟩
def resval1Tail100 : Box := ⟨-5342829020244788872628801424847464297964040850,21063997057169837612382369082397741948006391912651⟩
def resval1Tail104 : Box := ⟨-35014764266680696468212330630426430830325403248,66554503888383269502225992089397138166938191793597⟩
def resval1Tail108 : Box := ⟨-229472759098040518448425426592798869099387281414,210226289896190655037454629677840517825806098511728⟩
def resval1Tail112 : Box := ⟨-1503872674024883469222029685795592719384836733875,663640266088369003815350602215723489560402093792861⟩
def resval1Tail116 : Box := ⟨-9855779956489447717143658977228228081838143032599,2092328164774039373993642257846160967338149738972173⟩
def resval1Tail120 : Box := ⟨-64590839522849267321943755478383886889398452314327,6579348541353883861494217146989191148861938381054045⟩
def resval1Tail124 : Box := ⟨-423302525896947385040554115156913541506261133290838,20574826875392483025817920878231314607069874692144307⟩
def resval1Tail128 : Box := ⟨-2774155433718425318995348575530947923870027672729962,63590302920974255218440778011040476956393284726388375⟩
def resval1Tail132 : Box := ⟨-18180705050460612039201136592267206546042365307310949,191563755922431070683761955160110371857465051001139208⟩
def resval1Tail136 : Box := ⟨-119149068663213433007552958053370342005487237406681599,543747005559213731616864402024982574845759988315280631⟩
def resval1Tail140 : Box := ⟨-780855739705904684207225947386813764402773816619053308,1314223541008157591838451670945208514002413305030692387⟩
def resval1Tail144 : Box := ⟨-5310901792180604898317354414238574831332519285328087595,1469680312019993421585644205573866967342742905321632812⟩
def resval1Tail148 : Box := ⟨69173197295277878857527344052767982323943446,868762357637801977766364219873990789918105⟩
def resval1Tail152 : Box := ⟨1245993376346404069812433921375036845301,3376845678395642653958455019823538009521⟩
def resval1Tail156 : Box := ⟨529955478382911097062992189828966776,10566503221711224221551315195679520444149⟩
def resval1Tail160 : Box := ⟨848287465994059245461984028001778578,33394932047832177170340829934040091766760⟩
def resval1Tail164 : Box := ⟨5554696111066449916591997963277637408,105541600677486011812136962906840716177556⟩
def resval1Tail168 : Box := ⟨36403225278670477473039774898475306139,333544729792376750927728864361263365014178⟩
def resval1Tail172 : Box := ⟨238572176537790647673400263191670097570,1054042539582655179513746303237401716492274⟩
def resval1Tail176 : Box := ⟨1563506616121213154702740341539715790136,3330485439190693325311787872435772944908383⟩
def resval1Tail180 : Box := ⟨10246596959406744133387070828043636540076,10520673528059658966632441202688981113383554⟩
def resval1Tail184 : Box := ⟨67152097833166310195737804322509511059390,33215755951609806026365251643635293349776107⟩
def resval1Tail188 : Box := ⟨440087988359437558865608812477900732223698,104750337451855388159630544314113807385160478⟩
def resval1Tail192 : Box := ⟨2884160640512409173957454729467047005004205,329569529639672719359581000876197309529020174⟩
def resval1Tail196 : Box := ⟨18901635173662142017071924902364607302066289,1031816200773589640570038530060157281397854898⟩
def resval1Tail200 : Box := ⟨123873756274113244647229846250045470373053366,3196913478324609313983407861766988729422354539⟩
def resval1Tail204 : Box := ⟨811819049118164936732149980286208587265564250,9683508507144576315223934077968010726348173176⟩
def resval1Tail208 : Box := ⟨5320337320366162135515398341254974093129360959,27850080635283012369929353670127384142906606779⟩
def resval1Tail212 : Box := ⟨34867362850726360932424428386301297357726252744,69967538495703941686060674820804511113150525576⟩
def resval1Tail216 : Box := ⟨228515996174178986490140407497759308983337988547,102821592075147748381349927334129719675495103856⟩
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
def polyval1Tail5 : Box := ⟨2130807577495030654710213814378258165576838346873397,120104531592244651148788064032563062390970063946783⟩
def polyval1Tail9 : Box := ⟨211408407402740458997615006629911173902630099072,279155139319713001123009925694279897811143088066259⟩
def polyval1Tail13 : Box := ⟨15809430078490451842945702175783895628051807046,882243121629044670138841194665921985913562463753584⟩
def polyval1Tail17 : Box := ⟨102519338379993921809106368805801621620872160506,2788270864885637034572575070445230042933645639132692⟩
def polyval1Tail21 : Box := ⟨671866885235999193079014945377816122148509133442,8811964999933860565273977524233186865982464799679067⟩
def polyval1Tail25 : Box := ⟨4403146772869009350099725810272992897111965867372,27847881271793850954642275785662716620420834707991517⟩
def polyval1Tail29 : Box := ⟨28856462689070004818073914649698915721087031627727,87998116514508690590594306025057117789289370663900818⟩
def polyval1Tail33 : Box := ⟨189113713878944055738252007076406527590344997716497,278019591004178107643196085378563452472161321082602664⟩
def polyval1Tail37 : Box := ⟨1239375635277016106378654509887552579200789807502703,878037518288458836547510836045088984522554575961423360⟩
def polyval1Tail41 : Box := ⟨8122372163351437461423473792303379479829144531026506,2770826823447468041151024417112857897689244472216091622⟩
def polyval1Tail45 : Box := ⟨53230778209739967553032847031761477304790828045414916,8729621000510874678110359324278129357435067612668018601⟩
def polyval1Tail49 : Box := ⟨348853228075351868896782763996343123127878046800108981,27409295603436714209035887132950570224928877662226698213⟩
def polyval1Tail53 : Box := ⟨2286244515514627449164989338639360092852724543216327665,85443213519881533334263141625770650533629385562986208164⟩
def polyval1Tail57 : Box := ⟨14983132056876778851231922566840792076786261226713244908,262285278524128468788077794820784534288295489655089022345⟩
def polyval1Tail61 : Box := ⟨98193454247975052955781683097919888613017612851996008297,778111645859915954290445166151555373485120445472747166054⟩
def polyval1Tail65 : Box := ⟨643520621788000881087353266797947800894089313302319479960,2126036237835640669392488904631943206438346585410741060123⟩
def polyval1Tail69 : Box := ⟨4217376996007409160545994681709987179248046529461803098218,4535790567286060195507580525279372283801881250140474627415⟩
def polyval1Tail73 : Box := ⟨27781250000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨118303724402869626056453376984928398519062772467353633528,207314590678083879981970195368486908886510460414760313⟩
def polyval2 : Box := ⟨3811578643560258196294310717052454779486368652400336444594,7216058223336053662745459212275233578676309865183384101⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-135006835706329293179047008058296497194908111501010,34848396608823162396574776820677171218165736464109182⟩
def resval2Tail8 : Box := ⟨-448329464582021612433458099342411640685298078623393,59333517297757786000376270431681044379404145476804379⟩
def resval2Tail12 : Box := ⟨-1028752459453126305437477092759830673790053179373213,100956451048256083998994786432441951276835551283236074⟩
def resval2Tail16 : Box := ⟨-2360572865724150606122014581501952580946710133982338,171621681858929916290446667847180227738670523820375334⟩
def resval2Tail20 : Box := ⟨-5416564662645855105395092687695432844500019792307285,291389480881829882521992669080755472230909134238388537⟩
def resval2Tail24 : Box := ⟨-12428835885689644006378851282720781722584148807979742,493909174339289104052343725539497980462654489780547339⟩
def resval2Tail28 : Box := ⟨-28519176100436168057567764764809071044798835368285848,835271115395404315895534160481677039949971692505518480⟩
def resval2Tail32 : Box := ⟨-65440030983445425427811229678944622553111951352541921,1408148071460104190045239533364567356874369795036556537⟩
def resval2Tail36 : Box := ⟨-150158533333254417531575612498062927139519985869453526,2363717713067736513636293099323261489894757891250278154⟩
def resval2Tail40 : Box := ⟨-344553399409270036507892489501378869932220185002933585,3944008493659642439107447218712448209781993921262465525⟩
def resval2Tail44 : Box := ⟨-790611378582189737659139142777128207130261739114016518,6525485878398345663343245013386194871548778951023843548⟩
def resval2Tail48 : Box := ⟨-1814134914980651460426603560661249223722006590406698049,10666804012379728786758147477307812403227884960242229306⟩
def resval2Tail52 : Box := ⟨-4162709491550434690786141239799448364307565349695237085,17129221306645365674131796760973786690590037234547876376⟩
def resval2Tail56 : Box := ⟨-9551742909500666468071286472041289400874078597851360681,26771351030278564221188903956751436163206576418624513925⟩
def resval2Tail60 : Box := ⟨-21917405669157561342129342414344348088706271063031070188,40048188990282954402792878809250285603074071154331958774⟩
def resval2Tail64 : Box := ⟨-50291624858366088171050360446799980183963884144807828592,55418943944604909484158400285231614267422501412138944813⟩
def resval2Tail68 : Box := ⟨-115398815426393228114871704964513477089182052448042544590,64938533761550065736580478420699985223153155017360491191⟩
def resval2Tail72 : Box := ⟨838361142589239225239433377503774149397899849012625472513,1004843057993178358954520934931944849994705409593546717⟩
def resval2Tail76 : Box := ⟨-30726796845032126270080995549648058319556921790177,421743265609410295392927148645813215773530594633192⟩
def resval2Tail80 : Box := ⟨-5025745961769234885260663077283543111154293005892,718099785744306348575905943433222154264520428454234⟩
def resval2Tail84 : Box := ⟨-11528524886256245191198988568830989145952153294853,1222089064799914261985296908041454625047035127514846⟩
def resval2Tail88 : Box := ⟨-26453322705718514848231929263212388802858322953821,2078043821716779577635154611073629271577538616476745⟩
def resval2Tail92 : Box := ⟨-60699728885006913884608467204928045699661868847365,3529479489584223421686915005327081502591415722797957⟩
def resval2Tail96 : Box := ⟨-139281447855686709097305002534750914257635768596702,5985405798645716651955580383260470980922849773204722⟩
def resval2Tail100 : Box := ⟨-319594865959533597712604342077293591867319373207761,10128851182216120417913983813835677386067129610354145⟩
def resval2Tail104 : Box := ⟨-733341589423479234724938042904549072127724668363397,17091246087930739269041980007656023651038491879959097⟩
def resval2Tail108 : Box := ⟨-1682723798342394682373320441977250295710511967982395,28725235854486792719804590890055627275231215359761115⟩
def resval2Tail112 : Box := ⟨-3861173868147725139912802145235377173687850842133946,48013462840718726999983948121761133138429674493222890⟩
def resval2Tail116 : Box := ⟨-8859840013407419729697476703594098183316188606497828,79636000036370584425078544859599257169823777199407938⟩
def resval2Tail120 : Box := ⟨-20329766994106251967527636105224082433740137710217402,130640229192437148797785147261150446452522960877937650⟩
def resval2Tail124 : Box := ⟨-46648633091479549245947877246930375986486708803007850,210899515338375417470317585569708828057629875020193867⟩
def resval2Tail128 : Box := ⟨-107039838180848312325414809068157011000618376131826602,332325932734889422941581728171567731554263817274396343⟩
def resval2Tail132 : Box := ⟨-245613348097794726516701960472538874526186367220340771,503925259845120355164659916335198629204230405795304461⟩
def resval2Tail136 : Box := ⟨-563583781448981571745149391143459296810226468780084286,715095992899817429513683936629607377742797629462732663⟩
def resval2Tail140 : Box := ⟨-1293198270242030466207079208474321257490982620013085530,888173260444900004902379275714347682706537533713986588⟩
def resval2Tail144 : Box := ⟨-3117321529964328795480318326631915633474619314449088174,740926573693767671541881901211870345467515133906734684⟩
def resval2Tail148 : Box := ⟨68951361654517281612698676867179527708290560,51866417887864282222877282346515902106149778⟩
def resval2Tail152 : Box := ⟨658590867100489422346159564701888543713133,87223772937073451631795604413084931328338455⟩
def resval2Tail156 : Box := ⟨1508396033372925253177327950811134874486569,148412939193160923270528674797611949933438463⟩
def resval2Tail160 : Box := ⟨3461160917505263758310806797594134984418481,252298017542214730278446192430957830844760683⟩
def resval2Tail164 : Box := ⟨7941971284097901345823319891612232253570066,428371895841349114659014077430456404056009673⟩
def resval2Tail168 : Box := ⟨18223627676704098719039936743437712826561896,726108567136212301722906622977784382123848258⟩
def resval2Tail172 : Box := ⟨41815891019938861421784757655511406328129892,1227981972351033730451156431374512800500376743⟩
def resval2Tail176 : Box := ⟨95950640169556839551918310223023267252909801,2070268455360432213011578190505062155515446892⟩
def resval2Tail180 : Box := ⟨220168101752462343542808420946446588437596466,3475306040392825101902187613498917306550277877⟩
def resval2Tail184 : Box := ⟨505197182047175243691483315468337518690092722,5799118555656738698751601404678256159831485778⟩
def resval2Tail188 : Box := ⟨1159224205127400187976352284966775421436742234,9595660118752329719626422682806238005590305206⟩
def resval2Tail192 : Box := ⟨2659952995596418149055379002232099429261965394,15687404851388743743536126464822192795579484369⟩
def resval2Tail196 : Box := ⟨6103521568551761510985613289224266326452083667,25196260914268406403128896707282806748996429453⟩
def resval2Tail200 : Box := ⟨14005125503890209399435539755868263801783900020,39390921580504380274968064431552081079132166345⟩
def resval2Tail204 : Box := ⟨32136126361925426504458289470683995185975159669,58955172620865279345847868481645456387205394600⟩
def resval2Tail208 : Box := ⟨73739476112764744136815013266759135603572201085,81658258428519999182065527308979856806618308989⟩
def resval2Tail212 : Box := ⟨169202419761516380291169410050496200529404569125,95899254958700010494539352823755860643545933949⟩
def resval2Tail216 : Box := ⟨388258681719169143018872332037974111734409259611,63999583806202476561254116026776857302622203340⟩
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
def polyval2Tail5 : Box := ⟨22520613248251847518550187794010434688189643436313958,3132586986581700473454651826944820544637942035343428467⟩
def polyval2Tail9 : Box := ⟨46851618297437351035229023015466775221859629518210233,5332034726554612414867517229794961342440238432663057239⟩
def polyval2Tail13 : Box := ⟨107505139455421698169782029760855537871315510306356625,9068637147309670979258507794616131471003063051125028028⟩
def polyval2Tail17 : Box := ⟨246681026884105433764936818173612309703070678682520777,15407412603240508879142115639415311487387900183273034437⟩
def polyval2Tail21 : Box := ⟨566033674515600282334059396821011185986109730167102548,26139158957299521875504166795190326048707856037721876571⟩
def polyval2Tail25 : Box := ⟨1298819470363570874867064094724243508171555381041952075,44259060171416817706641595756775266023198442645713311848⟩
def polyval2Tail29 : Box := ⟨2980267946141485461502661052794652324833067425590018887,74739463421094029199590355826162862097674468223557239640⟩
def polyval2Tail33 : Box := ⟨6838515462285227756559330570710296788289717666450936298,125747915058413092931446039395922849242793736408133057999⟩
def polyval2Tail37 : Box := ⟨15691640675617964567557526804254856497944078303064027091,210494956330954430902140564570629699246445612466098383039⟩
def polyval2Tail41 : Box := ⟨36005999906071178383990452593454631083595245362103344977,349858348839834915676546329661048943416440063380270266755⟩
def polyval2Tail45 : Box := ⟨82619278381158949149421976503546144280887152079457613341,575648265335305591158212797800333161100513789400017752338⟩
def polyval2Tail49 : Box := ⟨189577991946627670360608026676689927081630954437488370460,933397376259385972798213589045438533291100983787462436950⟩
def polyval2Tail53 : Box := ⟨435005191702468087590726461626376384171720473938592289012,1480741209035487716501044788525800309929907806939236976805⟩
def polyval2Tail57 : Box := ⟨998161837590173718300955889846351143804484406514217367381,2270016945176451517841854958806736691558840881161202700425⟩
def polyval2Tail61 : Box := ⟨2290379685175948971176069651901366030859983060744350403613,3284989033779546941713308868290375574453792376540291327287⟩
def polyval2Tail65 : Box := ⟨5255499564033051025406339045251018954606391599857784513599,4255833327633437387892659705066768195984846653674606791140⟩
def polyval2Tail69 : Box := ⟨12059256505282527520875661655041616228545042540722412432939,4166657676904311260679820314612773305640293944774207404524⟩
def polyval2Tail73 : Box := ⟨27781250000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨118119917899086247052662616169483817110173893727252751851,1717843772201185892636354619405656926748151095862103413⟩
def polyval3 : Box := ⟨3830144018608809236680829024820465591269656683559131969934,244681046594636376292112330860100862397358753153708760431⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-186594138446977890945594707489114337643573347837586990,1985724597807344912909175820513267779826531713902844744⟩
def resval3Tail8 : Box := ⟨-276723107917152299552744184430363861466060744545185153,2535503439986082643539375605616851552542563251354064834⟩
def resval3Tail12 : Box := ⟨-410254505889840622393753963311272453911908185553275116,3230280397970908050776483254870988496759963046805252583⟩
def resval3Tail16 : Box := ⟨-608220818564027204609523226551063810058690920917638712,4104590943605528495894115418912512958459533996656577190⟩
def resval3Tail20 : Box := ⟨-901714810728155250969447137893786915941375359202321610,5199200382270276804869115092884786539536803775564801828⟩
def resval3Tail24 : Box := ⟨-1336832898627400534555679719727693890917612322874607405,6561035310525098512260685444504450822514817075285883182⟩
def resval3Tail28 : Box := ⟨-1981915099530632317688327596793913815486653952445938885,8242177561309232932537610585927870799359797662469705084⟩
def resval3Tail32 : Box := ⟨-2938278573021800832175547109779855091763384212811509500,10297200668870572680979847725737800346969246753524872985⟩
def resval3Tail36 : Box := ⟨-4356130580327914689666012636063242546305556006387628275,12777703841334477222763767003300814149440650031353686645⟩
def resval3Tail40 : Box := ⟨-6458160164627529190838703599400176692692472610601720067,15722244233556500762082001943019415206473684482959612416⟩
def resval3Tail44 : Box := ⟨-9574513881730848203554719123296581169410577976514414650,19138868491392876970606332737501141432338355033481899462⟩
def resval3Tail48 : Box := ⟨-14194648899164272585494407205871687380030529845462653747,22975923490071015363332804896197336011299390962913699942⟩
def resval3Tail52 : Box := ⟨-21044207555540267699821036911111530966359617649878641720,27074520979786622462701860969326341742289150871810814828⟩
def resval3Tail56 : Box := ⟨-31198987363944704264738192736862452955472586196510904811,31092548306004565132416994978382622015179854301991151052⟩
def resval3Tail60 : Box := ⟨-46253906685080654148415244295929988289210607720111374624,34384870236705337282651566031797161030878940312083602518⟩
def resval3Tail64 : Box := ⟨-68573503951378768113993939269182535639278507000431076780,35816478937869353829018866288726850706972489937897578703⟩
def resval3Tail68 : Box := ⟨-101663113011228786827223031219320744632410980063533368684,33473514208383893215388678021365415582421885129413520401⟩
def resval3Tail72 : Box := ⟨839118422220086951802057158681674355276064604164160838118,771262369687119750250212975751081544405339824928417725⟩
def resval3Tail76 : Box := ⟨-2361504937123451469293044809750235289531763773138136,25809719734242094266121532774515123768757867849775928⟩
def resval3Tail80 : Box := ⟨-3458962435602590216768468182117118380103352877585577,32972891734620844471809711715687841472181222380838857⟩
def resval3Tail84 : Box := ⟨-5128065641575618748086364276172210795499379560042259,42034361896041650579504596139008405041188033181741093⟩
def resval3Tail88 : Box := ⟨-7602588726802209710505708342365723718441615989352067,53450978701313281697783205516217856233192640286999627⟩
def resval3Tail92 : Box := ⟨-11271180869828109906879924427834448600838551562837589,67764998783876981826653370158060351164155184176828815⟩
def resval3Tail96 : Box := ⟨-16710034274582317731381021231540209761009147500930013,85605325128582430045864686375189289082378681051117956⟩
def resval3Tail100 : Box := ⟨-24773379886501161083742766129120473976382242365474936,107677768633909799227622668934811412391023459349505052⟩
def resval3Tail104 : Box := ⟨-36727653631113859179545398840527610418660301386922767,134735427246587922383547885966781194525003526794141716⟩
def resval3Tail108 : Box := ⟨-54450403918525799498625137706488155381252946248046122,167515116444952007039087426675423671741998369682463393⟩
def resval3Tail112 : Box := ⟨-80725180994925791494394349062883193478233329083746420,206617680092301497970260012021202008662805090215012713⟩
def resval3Tail116 : Box := ⟨-119678723713680003773414250392684486805022024475820723,252297607036197085465636501690888459827343895679251448⟩
def resval3Tail120 : Box := ⟨-177429108652424883063706188869154577357852747461497356,304108487634467856201353636858148265779921211960580358⟩
def resval3Tail124 : Box := ⟨-263046660428210394508793271935384358961718338835557274,360322187181820275638083642703880718729949949013207031⟩
def resval3Tail128 : Box := ⟨-389978544602740998957822096127748195589312629952295435,416996285954710404137531117341023592783571705019236995⟩
def resval3Tail132 : Box := ⟨-578160790952093252140129482279997491947367939242513276,466499011426468445411537562698051433144123003907640197⟩
def resval3Tail136 : Box := ⟨-857149463306066948141421886219816914061619259246144227,495202631710618995247043377610839144617521237656351248⟩
def resval3Tail140 : Box := ⟨-1270763048104855841292318362174007691450479326728388589,479908765187550198039958293621170215907020042735000552⟩
def resval3Tail144 : Box := ⟨-2018753757629630199608116282416836496195634327608843077,375563245967605394071893106300407050204281728908418269⟩
def resval3Tail148 : Box := ⟨667768538004518505951910710980931007367558624,5855616383837653453570133722773587488513178538⟩
def resval3Tail152 : Box := ⟨888570344330464463660871008559793924552612103,7467097165521061990021728532396447869153030375⟩
def resval3Tail156 : Box := ⟨1317343838672469382105442135772470035573144106,9499385955525178085386937499306550690061887214⟩
def resval3Tail160 : Box := ⟨1953021688095842912135898332919050603827862263,12049649003599518869065117542650461576151457626⟩
def resval3Tail164 : Box := ⟨2895442786694523437804372922371951813616469241,15231550328385037570530026416315947874188863841⟩
def resval3Tail168 : Box := ⟨4292624594045354019357475059432842168518461324,19173461742544350996065875299401967915359050192⟩
def resval3Tail172 : Box := ⟨6364009674126268123158736508373348798239553701,24013737173374826235784684960302091847589067141⟩
def resval3Tail176 : Box := ⟨9434931530829508665766735486654961641599653818,29890224368386920363063158981071112576955977934⟩
def resval3Tail180 : Box := ⟨13987711765014305315879025136995450017677560944,36920207583352072813356293057167917260445871122⟩
def resval3Tail184 : Box := ⟨20737413915702019721701096565735141351768663670,45164836008535786837674058996299563263821531941⟩
def resval3Tail188 : Box := ⟨30744151948194792496597053216318789368480955228,54568832763604691763717187100023407158754160825⟩
def resval3Tail192 : Box := ⟨45579592655861394181375985431460115974265981883,64861331118410032989918991610783243432747249331⟩
def resval3Tail196 : Box := ⟨67573802984545770750941378801330765297363001909,75396199592652298427509330903025282736837988279⟩
def resval3Tail200 : Box := ⟨100181212330492501247807807380284309040011424174,84898927697147058324447332388232679158892389949⟩
def resval3Tail204 : Box := ⟨148523168161817695820992220735598042162277951177,91070156417962869551671237616053491551575260755⟩
def resval3Tail208 : Box := ⟨220192299211318873454341615095993291490627795007,89970429078316172364438646456813753439413309365⟩
def resval3Tail212 : Box := ⟨326445020344247315601553374948100480862967215153,75072501978374567521437445395111166805914072014⟩
def resval3Tail216 : Box := ⟨483975990354335554167301645214245047370185350122,35809909106769992167214530764208651428763251465⟩
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
def polyval3Tail5 : Box := ⟨34284213556850658950473453845907826063874736113184177588,309534532096074507030777547706395613700535855416041583874⟩
def polyval3Tail9 : Box := ⟨50824797441695477361527076912888989176267488644444132889,394259016457499336653335504022154411806866792123312336154⟩
def polyval3Tail13 : Box := ⟨75350055481290064920280863741038004906655001960645299219,500827975420295365991072768942062547164460895533023898797⟩
def polyval3Tail17 : Box := ⟨111709857575961924868627744080402013377233419802037358309,634174654683906727306152230821365289156277972668680208338⟩
def polyval3Tail21 : Box := ⟨165614904991893291164319583978329512229199172293260858212,799961142325888744739865437345505170890072381484212586085⟩
def polyval3Tail25 : Box := ⟨245531570361397369644114466232704570744219473871539765215,1004443577036492271374637090965696519688984879408609583532⟩
def polyval3Tail29 : Box := ⟨364011633174470412821828380373993035813128562436377833939,1254129033687121597043783673101210413246388770057874622778⟩
def polyval3Tail33 : Box := ⟨539663672949723642480071842303814261571979570962429437689,1555081349142943892479928967839670240057113344785897748338⟩
def polyval3Tail37 : Box := ⟨800075748573663675588810019108327283976171970543391677048,1911651851779226390009722677628442957059972979575108645976⟩
def polyval3Tail41 : Box := ⟨1186148402313052326153089731313641378750356975764507755768,2324286758511184776840076268912978853569172039998514162352⟩
def polyval3Tail45 : Box := ⟨1758518533798887791347536580481944170767026432550585619265,2785874131875723621629666002527003787649006967327101723902⟩
def polyval3Tail49 : Box := ⟨2607083083098093352918311822839730552922234111059594099782,3275807143818476198955979191552031720025897885711593617280⟩
def polyval3Tail53 : Box := ⟨3865118320642950025107460921060097177891421599610282473339,3750508225751209031073100625706731086996248994339067144195⟩
def polyval3Tail57 : Box := ⟨5730212331713282322842524108664116997720911064541618198819,4128507694844497673938074656737821245644898879133177327829⟩
def polyval3Tail61 : Box := ⟨8495298369302443625753565076473115678015749344676017169464,4267192014114675315520064368936450532889444521663795948318⟩
def polyval3Tail65 : Box := ⟨12594663200205453406198328453197865815491176337724697681397,3926869042137460810793127701898664539357158851614636426458⟩
def polyval3Tail69 : Box := ⟨18672156732238302516187651709456360801334271686556420231012,2715599228082342023998622451876101803196697077394092993272⟩
def polyval3Tail73 : Box := ⟨27781250000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨114999515680573972789516891203293064124509702649913641931,8634461325385231768383886249575063914051515048761022635⟩
def polyval4 : Box := ⟨4677858252711571619653391283861098973268085587059087418385,1943976461802100918744277905962174591675700287427318781329⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-3898541327273612349310333638324016532321462636623667019,9380895774550116284341843200244024527443613935608268321⟩
def resval4Tail8 : Box := ⟨-4723994169397788895543896141611973804023137799944055613,10353693399933345286346865457038233633655259795443296675⟩
def resval4Tail12 : Box := ⟨-5724135549668031610652712509761987079965988810275093119,11395238376967647543772107946851708190035720096147739077⟩
def resval4Tail16 : Box := ⟨-6936022053854851881699763456810176593779676592751219228,12501505229772204947993535668674597051057664157403289960⟩
def resval4Tail20 : Box := ⟨-8404483351952901150232429964267678017675283422808988062,13665100998545409580470636865360513108828783456940300265⟩
def resval4Tail24 : Box := ⟨-10183840227842992709933759419850943425722652258902841035,14874210947937652239469527319043141917570229049672944987⟩
def resval4Tail28 : Box := ⟨-12339914001035480834128906755791092823204326682237415895,16111275598004893526946560452547609425324993984632384484⟩
def resval4Tail32 : Box := ⟨-14952461364881807153241612354164220196019536090899349035,17351335284033983161233457932406872191313286666511645778⟩
def resval4Tail36 : Box := ⟨-18118124717037910018119969254363435156721895017726075308,18559964763259261074793124147257234658060786362262844227⟩
def resval4Tail40 : Box := ⟨-21954007119732481151677192844665530451445172325905206316,19690703022096547615161386545658626356692171979846945002⟩
def resval4Tail44 : Box := ⟨-26602004133464315998270960488860677367075057322629343708,20681862266626765490112832486583172668332103116415304435⟩
def resval4Tail48 : Box := ⟨-32234052765738365596665712720743286376829932135669132058,21452574278304927248697194095892421835345509478942874371⟩
def resval4Tail52 : Box := ⟨-39058491702034564390838651440986334735365228547649529838,21897900886043822070358110309398968242348773115252769992⟩
def resval4Tail56 : Box := ⟨-47327768094349862744258870399615890763391750664200985141,21882797030251374090193928344893835061781230984591444939⟩
def resval4Tail60 : Box := ⟨-57347775994012870411175939637161415492813898699689263492,21234668299172806763251631987840928127720742401477383251⟩
def resval4Tail64 : Box := ⟨-69489171861910303144528088260951164808155783110170243315,19734208112048639178301875090276979211214982710626115031⟩
def resval4Tail68 : Box := ⟨-84200893961220924355246998694170155330429485488415726214,17104127880674454655026886269055009224232381151874519461⟩
def resval4Tail72 : Box := ⟨839457033258654941920641822143673856806714425805250422396,737245683984840201402864118555244673671182211132412902⟩
def resval4Tail76 : Box := ⟨-51258844641489944902247263158652285324599303793111656,126297246197224507062158492384002401220286684175951903⟩
def resval4Tail80 : Box := ⟨-62076825962994667366590323019360970155375452917682254,139490047726371206077407318858503762603323290655899775⟩
def resval4Tail84 : Box := ⟨-75219431764149153879742644908260182367656246960525788,153641833478783876304506344457966425844102860910335997⟩
def resval4Tail88 : Box := ⟨-91144528822057026012399451337990784692443605427186685,168707093460996066266301399418934587873952166874061010⟩
def resval4Tail92 : Box := ⟨-110441210993672209324237902171181583304674682878214203,184597206851804171223677617624076217563994159717969367⟩
def resval4Tail96 : Box := ⟨-133823294095491412412542975282105471097681350828876459,201166602215191524844969986534066985023839510201794064⟩
def resval4Tail100 : Box := ⟨-162155719603567890280878674006982554157297119941752568,218195529056582415902279637298514844255254797044363808⟩
def resval4Tail104 : Box := ⟨-196486550251768228823787566729931373111524462879775426,235368481647956593248057610990607523685733813333107384⟩
def resval4Tail108 : Box := ⟨-238085739585538354571929557826604717193491405775195713,252247259804064973366140300539829624037342428875885155⟩
def resval4Tail112 : Box := ⟨-288492109619511552309220488126952826006883590175990462,268237423512872767262223609868724925941099849149233560⟩
def resval4Tail116 : Box := ⟨-349570274379304451621343301230384885528934643257397635,282546620562795425140192623868938124152457424374471266⟩
def resval4Tail120 : Box := ⟨-423579615022363518129967933837486696256615583754274612,294132927768550083690142170012574382519680329665159927⟩
def resval4Tail124 : Box := ⟨-513257858040334105366487110962380369069649376270153422,301640933941142247671910667658113266657803226264488521⟩
def resval4Tail128 : Box := ⟨-621922348237281083511877310714294798693292907133347901,303322790423094456071640528214145848303508104711217591⟩
def resval4Tail132 : Box := ⟨-753592762736805263457411716381213528368506960891238296,296940843446453750345964109614347080556614546717495153⟩
def resval4Tail136 : Box := ⟨-913139805440999866491915672698577698381334135962161729,279647718247702041834598650296864276441239444520623600⟩
def resval4Tail140 : Box := ⟨-1106465657249559969856534753597861856678359610499667471,247838805829811485019680855120144196336428612041324010⟩
def resval4Tail144 : Box := ⟨-1469025260873981482618041345933552515735754241173875478,192634869587106319547338798926464422221953762028235495⟩
def resval4Tail148 : Box := ⟨20541647601949237173181912422552425559846924649,43638283260897827635453040493263648431092118664⟩
def resval4Tail152 : Box := ⟨24807879133452710328111004660999402923896244959,47984669081663554019367669991614459339806016928⟩
def resval4Tail156 : Box := ⟨30060082771517849164469683324016469558747906607,52589383520590992321306809240350085490382177963⟩
def resval4Tail160 : Box := ⟨36424259214680647221682675603991893049345552339,57416862715745251302880950293999295218473578810⟩
def resval4Tail164 : Box := ⟨44135828548419453068910558053709428292202563481,62412423488423845940076837931490636558483359846⟩
def resval4Tail168 : Box := ⟨53480054327924143479837079823649719958936020776,67496014356799857862132317753386924635641437349⟩
def resval4Tail172 : Box := ⟨64802594739555234336545455171510093089272112449,72554977202125739173494602630560740073981837707⟩
def resval4Tail176 : Box := ⟨78522289061818773617287393348228844346209033404,77435023610356594862925498691292237201184013183⟩
def resval4Tail180 : Box := ⟨95146651214943961715553573959751111563159628532,81929013650867383320332159898739438882445530048⟩
def resval4Tail184 : Box := ⟨115290643530413015258246403904774346634717868980,85763032955918098958132632245122117783991583493⟩
def resval4Tail188 : Box := ⟨139699425212866573160942323624142344851138277455,88579151966570748156761056201362284461673623133⟩
def resval4Tail192 : Box := ⟨169275916997176876227536430350575971390238801436,89914114788246160865536952001431718057296012286⟩
def resval4Tail196 : Box := ⟨205114201662413127740762992232190357196808630573,89173038984450069265327248639637313791826168850⟩
def resval4Tail200 : Box := ⟨248539995942309617594158643655622635210332804794,85597005434513675446771181565020267277935493921⟩
def resval4Tail204 : Box := ⟨301159690954363367393253300631500572138213799886,78223171325654032920113246919861094883976481567⟩
def resval4Tail208 : Box := ⟨364919775233245240758789510152671227299934647596,65835740015646720140366432909319559269574449175⟩
def resval4Tail212 : Box := ⟨442178838653547456624802945677582640136645360679,46905757442177035221854979245880749989094392954⟩
def resval4Tail216 : Box := ⟨535801030601433940217171893048165001821751903867,19516964553911549454373065233426798239198351000⟩
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
def polyval4Tail5 : Box := ⟨1057958800517321033531455251106421606986945441495463652169,2138901942903669872178945748062451655535318679735699125217⟩
def polyval4Tail9 : Box := ⟨1281942237475562136495801317460561368808178786824517529724,2347806582371727280870439768856256477287290678039499021937⟩
def polyval4Tail13 : Box := ⟨1553348894753957732858679765642107241623759919575940933467,2567908226966207732345089856206769157829730825197883722927⟩
def polyval4Tail17 : Box := ⟨1882216467070927241207840521454742736949052741119169148720,2797104639503452679046115885384503378914361312555736489305⟩
def polyval4Tail21 : Box := ⟨2280710303318218416682777489106034869463917372774919798537,3032242849503792583676134864348876302070650332284658890589⟩
def polyval4Tail25 : Box := ⟨2763571341906588917711841687575214425458548386165297530855,3268814673325867084842118998806415449060177584985299801110⟩
def polyval4Tail29 : Box := ⟨3348661401974549187169547770588093993050513805234634492464,3500576675241223691961986126491294667417782873367417236129⟩
def polyval4Tail33 : Box := ⟨4057623921276420711135904703532485555136448811006247862867,3719077059052782698953995936413145604113246752573824554092⟩
def polyval4Tail37 : Box := ⟨4916684582324866071881002104462432607291561825247144252910,3913068078577998935991372826974833772842862004100225446251⟩
def polyval4Tail41 : Box := ⟨5957621443257513953758522520123024949637616826859509116171,4067777790933027006863403108525275575947564096795957518106⟩
def polyval4Tail45 : Box := ⟨7218940460154284252238934234249972097044276034014676594869,4164009172166562461944498028221936938108502872829902831869⟩
def polyval4Tail49 : Box := ⟨8747299885297528711048169745159035901733560460231633805081,4177027545979577239138920516762900165094990584419025670526⟩
def polyval4Tail53 : Box := ⟨10599236232195058680229528135023051469875663317654699749090,4075188670518385464563039931973668390493459662703684863019⟩
def polyval4Tail57 : Box := ⟨12843255653633654677863777201287172244088273274011684366313,3818249354685216779136180784498039192161653263916451405337⟩
def polyval4Tail61 : Box := ⟨15562368096256001346658679399983552436953136843788535736620,3355289732426818359975065913570796706591866445345646611911⟩
def polyval4Tail65 : Box := ⟨18857157974201338562088122854478425994049447418625966806909,2622160823515667485382416787505851739186515112454106867074⟩
def polyval4Tail69 : Box := ⟨22849505120878805639077858326370711314705667583373427012275,1538352152905516110204971784655190664322109419688654474184⟩
def polyval4Tail73 : Box := ⟨27781250000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨103781380216685797202890725747790045927297972788206674354,13603123505292511972431183334555134039135625164317379676⟩
def polyval5 : Box := ⟨8823752475764207444555927086298824382713924307542593672675,3892404619830915067716221631249947122228082624457732243323⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-15856160110785102064612817573465137695793662782607827606,13828957190113276817549808576535751360093053702355713337⟩
def resval5Tail8 : Box := ⟨-17434097979387355137990094966546410132992202966778316091,14181203852660811441319785867427265707534182675775137807⟩
def resval5Tail12 : Box := ⟨-19168993455990388512313936795569301254091757512209771841,14501930242712467397730483549567930693317812081400427311⟩
def resval5Tail16 : Box := ⟨-21076531197630557171982020876151348152240227746227656294,14783670564613515079208044304631888759145779451390385936⟩
def resval5Tail20 : Box := ⟨-23173891124978448414966140985398746397766392666843837865,15017935209686498310180042843282245194856842508062571158⟩
def resval5Tail24 : Box := ⟨-25479962752728854033094642724210040608106986470302617182,15195090010441327376037290835901017721718353187067453547⟩
def resval5Tail28 : Box := ⟨-28015515321924752097216828103467018699803670647261908340,15304222854225304926803431923715445968804356702064707020⟩
def resval5Tail32 : Box := ⟨-30803384854592952840958578215510278454446006999763908700,15332995756310327826048413002464965746661572846732610404⟩
def resval5Tail36 : Box := ⟨-33868679822484082648229457286281036089406121921440530330,15267480862947455896204218440995320154962513097360516088⟩
def resval5Tail40 : Box := ⟨-37239007282243640436312915501832927075084930471046366595,15091978697483788290874369846933890796673320185582674780⟩
def resval5Tail44 : Box := ⟨-40944721513662022956677095183708237462877178709811668881,14788816789064600492954104302492029298687841307416598871⟩
def resval5Tail48 : Box := ⟨-45019197400321537473438703366745611484894886414107033380,14338126632228149558723101613121696255424388508028222976⟩
def resval5Tail52 : Box := ⟨-49499131014796600884945517923320828688558269729751348821,13717596715061749242384719798975728717594651535202025781⟩
def resval5Tail56 : Box := ⟨-54424870115576474071896320576091484254227681333520209363,12902199121567120491645624990721201354932486106634892658⟩
def resval5Tail60 : Box := ⟨-59840777532268005767672342057713215559380035737478721008,11863886958325218168698162642589787016614409834674849588⟩
def resval5Tail64 : Box := ⟨-65795630701316955784483801984381043976304812247240997324,10571259573724083551325495682256934175774406975496673000⟩
def resval5Tail68 : Box := ⟨-72342873501649298834109877656180942680227385193790285557,8989187966499594138247104263792835902738820201479520978⟩
def resval5Tail72 : Box := ⟨839495175178304259545129266725835630030306112528854211832,741853328090849650720635506381162073589534445729414560⟩
def resval5Tail76 : Box := ⟨-213079034144097827804255142848924813793413585722940434,188980681457452506135070791710421983572827728979775148⟩
def resval5Tail80 : Box := ⟨-234251798458037510750498215914326172909532123795779690,193919520177465628847608077017835930943705644623953319⟩
def resval5Tail84 : Box := ⟨-257562574568091964685897309417421050608468204456011599,198448372966221776094826995309022177765353966921364666⟩
def resval5Tail88 : Box := ⟨-283193045616608648881074670979690826118046729317651437,202467660655271698959344220367800767482634058919572671⟩
def resval5Tail92 : Box := ⟨-311374046560757864657740536069604341753662550303549910,205864241011708776945697420171896974471308452891705757⟩
def resval5Tail96 : Box := ⟨-342359384781218869837438914373959223089281656236672311,208509653368078148805513214062055771280286500598618588⟩
def resval5Tail100 : Box := ⟨-376428124445187880520209269463971159755801564864841846,210258330294527168530402835761033996642777621589854581⟩
def resval5Tail104 : Box := ⟨-413887099849395223352504868838059083701918886346517942,210945614168142378344035181307372565321581609091658785⟩
def resval5Tail108 : Box := ⟨-455073678870896386470860140770715578961044677576994579,210385558090234675280665506188280306719141590967275590⟩
def resval5Tail112 : Box := ⟨-500358801413351983641324975076920421961346052555741676,208368488503259847448938566926770846745115097876562390⟩
def resval5Tail116 : Box := ⟨-550150320214042968965608172784152098779248227473345020,204658304528036864692075565962083923445674590789035769⟩
def resval5Tail120 : Box := ⟨-604896674100030021658329785552959024233239538380768465,198989486473897486959781381431904146367286502613278963⟩
def resval5Tail124 : Box := ⟨-665090926776012591506998634526409923444798629452278539,191063783145472379854178851236053466062126461789059850⟩
def resval5Tail128 : Box := ⟨-731275207518542181483698798876647300501561292944888294,180546544453680602982354447515429675586280739331189066⟩
def resval5Tail132 : Box := ⟨-804045593770976147939684061057255993468252893031033711,167062662406187808466782572730298388581910677792308564⟩
def resval5Tail136 : Box := ⟨-884057479644004723888607298328766356745110637916362787,150192079770695521421810078930151100044790741312511259⟩
def resval5Tail140 : Box := ⟨-972031747420391837860882257594696362888330767455292227,129464810416765272923736163258117181472817644771235321⟩
def resval5Tail144 : Box := ⟨-1194049764033356883691962282925156297305603102849815435,101109004374950198210919998964622047009535300153504211⟩
def resval5Tail148 : Box := ⟨112238979040226721234360675110999183501007053605,84377470561566732014702018897382549886737361736⟩
def resval5Tail152 : Box := ⟨123333045457599605789489839607144214056068981980,85994198959119158124879175333839928114257954574⟩
def resval5Tail156 : Box := ⟨135606116247428168851168627367712370614097847731,87331550763377390303045535638626698788805781337⟩
def resval5Tail160 : Box := ⟨149100501611174597749117617022434637429334019626,88332536785218738925687197169560344170669956213⟩
def resval5Tail164 : Box := ⟨163937735228719972826532028089105790198207216601,88933161278455621733079745056162385228357210274⟩
def resval5Tail168 : Box := ⟨180251446115240792301297158539109741057016594266,89061075563352230665472159604523769934373326576⟩
def resval5Tail172 : Box := ⟨198188560927146355132506670942872910485843640436,88634617756939622158370462800332655260854900037⟩
def resval5Tail176 : Box := ⟨217910627231589640673527611783972349547471289598,87561748570617081192943053006894840228720643284⟩
def resval5Tail180 : Box := ⟨239595268457094278344468466379261472505291519028,85738872271546860892531236283302838731652469092⟩
def resval5Tail184 : Box := ⟨263437783628687437997556472639626237463342185364,83049530799299134143606166858312523312404084267⟩
def resval5Tail188 : Box := ⟨289652906295279808923209406191728517849912763175,79362957796445369975773829382320160392984841998⟩
def resval5Tail192 : Box := ⟨318476738490772300416172207599018540471221004888,74532477953902268323490623383485306825318118734⟩
def resval5Tail196 : Box := ⟨350168877146780525610110749164314324857302445665,68393735576189923550649661102692516269206877821⟩
def resval5Tail200 : Box := ⟨385014752108150823091059656494249237265709313144,60762734624510001744122680154427129406147673075⟩
def resval5Tail204 : Box := ⟨423328196808206141800627700556079142259102663197,51433670681403360909892843037875740895598771117⟩
def resval5Tail208 : Box := ⟨465454274756115714051233612586065212587709364630,40176533282908640306828058193915465682474504522⟩
def resval5Tail212 : Box := ⟨511772387419744027904373171234846212527121720649,26734454857756149866725036892113919640165293572⟩
def resval5Tail216 : Box := ⟨562705759015342846767850883966476551089532107204,10820535531458998169643945118502083258659569747⟩
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
def polyval5Tail5 : Box := ⟨5519697561059928324516584800870096106434432079780214286561,3970346935577238190695630564362966447940639147158449851577⟩
def polyval5Tail9 : Box := ⟨6068969365159743839605887398893559166469867526051113802074,4038114080986170540079260065270884009283671040511893727116⟩
def polyval5Tail13 : Box := ⟨6672902385389801364079303203364707955161842581348567462464,4091342006672609371084592836280760128562281869110225384311⟩
def polyval5Tail17 : Box := ⟨7336933763750122732735800371548852274537897338388122215406,4127200073845050449972789117783081169116325744767944730095⟩
def polyval5Tail21 : Box := ⟨8067043985465591078928266063549168887597963143749365144764,4142485997262299368389188382562564188338100828868512824407⟩
def polyval5Tail25 : Box := ⟨8869808663799862525623044440826188759176224521509128018224,4133583001976627821249648224514988612442758351621926980197⟩
def polyval5Tail29 : Box := ⟨9752457761996254370811658160989373157335659990441664218742,4096412346253996884671200294153496328895484975557792179255⟩
def polyval5Tail33 : Box := ⟨10722940708709187634448741915786825912169954346930217126072,4026380714866852918639341875613961684273477223739587433049⟩
def polyval5Tail37 : Box := ⟨11789997993178373955756859684390055257780512389978859837965,3918321945959590315459873672054606106018500071004328677886⟩
def polyval5Tail41 : Box := ⟨12963239884955327292015532525882223589553926535594527878182,3766432499558573325048410113639194235669121385208478581859⟩
def polyval5Tail45 : Box := ⟨14253232987157998883893121462599181848191548814405863564428,3564200015070900537307230343356591717775508364494343030150⟩
def polyval5Tail49 : Box := ⟨15671595402780670256992959604711463102052385956727069311685,3304324238226676046513400790383857622523865176481777987219⟩
def polyval5Tail53 : Box := ⟨17231101371158253112450839808027842216617287870651146044564,2978629524247550694301398878335945215017456932482465529106⟩
def polyval5Tail57 : Box := ⟨18945796316975476511075107100832913049446522561048182470838,2577968042886557011287654969981418735635254709091566845070⟩
def polyval5Tail61 : Box := ⟨20831123347990271717243142231946695589060028504754249992311,2092112721629107110349504751787159172154649846288201948751⟩
def polyval5Tail65 : Box := ⟨22904062340771092392909360068207203946324105193874956310784,1509638864944435172352678573076744692173093343850327043379⟩
def polyval5Tail69 : Box := ⟨25183283033161566076714438187835224342503260680113065760906,817793272691277009153105974159499699932607232289447872085⟩
def polyval5Tail73 : Box := ⟨27781250000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨88740962374878165450492753152094032347666192829370810183,12099076798874610892476498212207050611328013767850790349⟩
def polyval6 : Box := ⟨15653343020091538497601872801096276959986163617552438715177,3895580372629482349631114835005766088723133870834107825594⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-30876398376953593759659237757612068186120200296571534167,11847526387779349838773897241726451248657565674955368613⟩
def resval6Tail8 : Box := ⟨-32367208860154759274513744364818442959715039808790616258,11718389220480232721930210541885771420548025570388390282⟩
def resval6Tail12 : Box := ⟨-33929934940057980088655781112740222814129829985111636214,11560672055366392380413898637767749605971972964997825236⟩
def resval6Tail16 : Box := ⟨-35568111225057626078670770284965986317873410888765427289,11372282340594242104413646723241361130037476668741591780⟩
def resval6Tail20 : Box := ⟨-37285380545314717045199261321810946711853491735907030624,11151004318039941490578884061388678968410779046274098957⟩
def resval6Tail24 : Box := ⟨-39085561603550677949327431828315717693810291004174349284,10894491830592928098230627727469008786519987582387273133⟩
def resval6Tail28 : Box := ⟨-40972657473839931723681139067414084467594888338749446135,10600261279841812817161002211661505223198805134810533824⟩
def resval6Tail32 : Box := ⟨-42950864503277510214670600206944283963963280507668512981,10265684220074860418765624373921762911363060652545095846⟩
def resval6Tail36 : Box := ⟨-45024581643422816158073135492518986191187984929866482858,9887979570164941199145461320686179826884610436206633780⟩
def resval6Tail40 : Box := ⟨-47198420232276198218750987551576450168846472169138170407,9464205424107563467723546906874465544113579949441726167⟩
def resval6Tail44 : Box := ⟨-49477214248540605975399844209623299241512016686956675295,8991250440027298750433325862916249900334982899660112673⟩
def resval6Tail48 : Box := ⟨-51866031060970792006573546331413921528167005752543460059,8465824786467647015480468707657614435292836263357018677⟩
def resval6Tail52 : Box := ⟨-54370182696713457072666387989411299569597718082453096469,7884450623730010101484489315123523721346838940261745194⟩
def resval6Tail56 : Box := ⟨-56995237653695796536815308801702694880705044274593035888,7243452096926549681541050723985464451146054151958478259⟩
def resval6Tail60 : Box := ⟨-59747033283323070735288718937889092402998881289823236308,6538944816256446262012243149768370772127255690210732246⟩
def resval6Tail64 : Box := ⟨-62631688760602632410318475347925672688446825523714674978,5766824798409033916769551276722369252817239531733094922⟩
def resval6Tail68 : Box := ⟨-65655433311836230601771330858150661157167620802056159030,4922751915905802981625978173174049770695205787090786834⟩
def resval6Tail72 : Box := ⟨839384597528274054797055977189400696849783213112596987896,690538578356483168928930678324023278186923989687809461⟩
def resval6Tail76 : Box := ⟨-418454868498203074475603689303798047492576977840814406,162798436282220638347573822466344781143896214997803933⟩
def resval6Tail80 : Box := ⟨-438628741767256503072157170485812532336312131654475012,161119817222370663795172994863342247184696618811272183⟩
def resval6Tail84 : Box := ⟨-459806240344663891483492806887399127201854467453475342,159056315841288717656822213928164196826147324335047379⟩
def resval6Tail88 : Box := ⟨-482006214495071820806561032018753559252651892552907917,156579503943274601752626128943556598017682038982227013⟩
def resval6Tail92 : Box := ⟨-505278028932674310575955897865583782773161253128142492,153659429341103840065256672007300718325923550437189903⟩
def resval6Tail96 : Box := ⟨-529673433338482378583392244974599087995413710412341849,150264375133238568906582754690929835297777820488696252⟩
def resval6Tail100 : Box := ⟨-555246675928507695445849632863182822358914567512835702,146360764329110663361950025617718035095156341655907528⟩
def resval6Tail104 : Box := ⟨-582054624085029414322589212388700286497497888573543271,141913059564262218049097898547673142028697877137287849⟩
def resval6Tail108 : Box := ⟨-610156890812951802090763763116505040065429295726058110,136883657639712050441685418224883456789876641413545071⟩
def resval6Tail112 : Box := ⟨-639615967301622564106938248588308276343826325081484328,131232778624997987223704272330096530112564445571141891⟩
def resval6Tail116 : Box := ⟨-670497361886888250127388805277020600884505482618878519,124918349251441638581574339777049997508898006526794472⟩
def resval6Tail120 : Box := ⟨-702869745722397529422620621604029429600388422434731466,117895880308629812708962413524803241206388564813721263⟩
def resval6Tail124 : Box := ⟨-736805105484082540684695343156412878986389685344387415,110118337742888624631189039217234392836151456692453033⟩
def resval6Tail128 : Box := ⟨-772378903447388382066137005970338641368694826849822408,101536007141610268283213045261612854844744657505659904⟩
def resval6Tail132 : Box := ⟨-809670245293245968673187683204358822690050870970136035,92096351271642402074292031777195477076012587057222268⟩
def resval6Tail136 : Box := ⟨-848762056046197854767690001655568334783340718334669544,81743860322068456436660821932650412030167169454532215⟩
def resval6Tail140 : Box := ⟨-889741530330165644230675744427299013515182977146975854,70419884445378639652532728109789948195228095532896281⟩
def resval6Tail144 : Box := ⟨-1056534117745541640181580707199206610094529316941775445,55330624739304138636096084341268736173764982089002669⟩
def resval6Tail148 : Box := ⟨258652383431027634750006914266480802266238503081,83274801771709481673733536176724620971745911024⟩
def resval6Tail152 : Box := ⟨271068928648198807479501813393802758458832360246,81684606380562526901688548114652758922411613614⟩
def resval6Tail156 : Box := ⟨284156447046664011260930797427826541293014252723,79839349063978376754570225784712821120990397240⟩
def resval6Tail160 : Box := ⟨297875847145385283097896911627935654350553457880,77720502390563361625434694896975066954341203514⟩
def resval6Tail164 : Box := ⟨312257635661272380291253359403142243414857089667,75308977173998682733406700351996707117282744243⟩
def resval6Tail168 : Box := ⟨327333793468587672097411921209164602562345889193,72584575200830505547846993017680190996820860114⟩
def resval6Tail172 : Box := ⟨343137845515381652391865315109273738583277577405,69525929697852056877733430525804478847893967150⟩
def resval6Tail176 : Box := ⟨359704935372757636711939557670865199960938737052,66110442750083986541363661510620289554635923763⟩
def resval6Tail180 : Box := ⟨377071903383853819657609747848131159496551761549,62314219500827918428350038976042894700788850386⟩
def resval6Tail184 : Box := ⟨395277368585948735710086247136169315807070475062,58111998972161284238200871138517247096019401289⟩
def resval6Tail188 : Box := ⟨414361814587860202255498603382773983338434057511,53477081336245609722461153004544488646474698594⟩
def resval6Tail192 : Box := ⟨434367679593603859518052543353319884391813637762,48381251459424770931040147653942050283144436991⟩
def resval6Tail196 : Box := ⟨455339450772497489703997881247810357420888947807,42794698532282156327992128283127737565041867675⟩
def resval6Tail200 : Box := ⟨477323763185562517609738730928807681457415276231,36685931589586079322186032809677973756911742319⟩
def resval6Tail204 : Box := ⟨500369503488206058018580472328283087209980886428,30021690714360104126862141000381208956284664000⟩
def resval6Tail208 : Box := ⟨524527918639832866577360063759188610558527922645,22766853710144446245587568554111376983061098073⟩
def resval6Tail212 : Box := ⟨549852729987848384010914205377245848346738642693,14884338008980292068167899901275426761582478416⟩
def resval6Tail216 : Box := ⟨576406251770884843225480092324708400031868602907,6334778090572167570283167083073859819126412003⟩
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
def polyval6Tail5 : Box := ⟨12422438102120248724409648823107940024187242885035252308118,3823134685814570490451006787081103484500910103762965540150⟩
def polyval6Tail9 : Box := ⟨13022205525154197830079193307846503474218718055449242561938,3741111845321606981280346721350432576613721505607624665113⟩
def polyval6Tail13 : Box := ⟨13650932585792629209783030732682097059236570781689199141732,3646632050037256255399276749171345520483246828014002469514⟩
def polyval6Tail17 : Box := ⟨14310015312287205775895976827049504230498135554064339769460,3538823060318082092963735790305737413057083304443068997798⟩
def polyval6Tail21 : Box := ⟨15000919310891641142614926600368059325430447618892208502952,3416761903693125990610886345822511111504758204807238753029⟩
def polyval6Tail25 : Box := ⟨15725180949223948341115009083541447494283212845248553928686,3279472140284421790334989859688065855679224134433427858178⟩
def polyval6Tail29 : Box := ⟨16484410772498023537297538325575280523410304460798830460742,3125920997526745690970456586877106629349796960066957151877⟩
def polyval6Tail33 : Box := ⟨17280297084903133552309202989812336011192512200679392992709,2955016357505568839835241567053886734909630571057690791554⟩
def polyval6Tail37 : Box := ⟨18114609703896684311308852719486381785689887790720364925159,2765603589506925586628049539408202503811287330089080858263⟩
def polyval6Tail41 : Box := ⟨18989203895758562856214901910899550391082217655886429980207,2556462220008395476010761790192268483527575345055618798123⟩
def polyval6Tail45 : Box := ⟨19906024501158569656577403805787558680755453456263986632960,2326302431955736740552209102518784775092940949659907351522⟩
def polyval6Tail49 : Box := ⟨20867110259910991765161065835714162436465233309513825974934,2073761384766172035617406944777221428354475719046503064866⟩
def polyval6Tail53 : Box := ⟨21874598344533301083559513443149527510501864394932000779099,1797399346075995142494252553726832236228526803533729719304⟩
def polyval6Tail57 : Box := ⟨22930729112690281148088240446539516119147254588542942525704,1495695625806074701439058000001854065883318094445184763735⟩
def polyval6Tail61 : Box := ⟨24037851089091641844489665341201190561673454559730974883003,1167044302652963976313978151600600600452471734298190049097⟩
def polyval6Tail65 : Box := ⟨25198426187940751611647230853435507333457409553508728659429,809749732623723337472339800450988882640561095628854223399⟩
def polyval6Tail69 : Box := ⟨26415035351786084902125462454367475388475993492735185804403,422021822954523484433206397083872987994927667385392483624⟩
def polyval6Tail73 : Box := ⟨27781250000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨71475865720593972937867025990794425525811864743563026805,19455726644244474029442985495170814453181684170426258695⟩
def polyval7 : Box := ⟨24693493286563163090575378213640655944569085101705486560184,6804275025487511311361243363236804620361220246307621193754⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-47451708849579153860612227033728284795863382775223240726,18569571737518518197809003453756815625870215533035423793⟩
def resval7Tail8 : Box := ⟨-48200499796116329777726851360584018321989176849552106033,17820839837310233565863926962844192389662052333954852055⟩
def resval7Tail12 : Box := ⟨-48961045280003957757376730380010685759750075579024440590,17060294360451426698340981903952845656709604668400109014⟩
def resval7Tail16 : Box := ⟨-49733591242742307103536496359931144101892556182191910611,16287748397719340083860836018345293192648902548657969323⟩
def resval7Tail20 : Box := ⟨-50518327044582489512290928549071013847692369952001903016,15503012595879181933298928980078960117639192939369851006⟩
def resval7Tail24 : Box := ⟨-51315445026420146946024586768064262607563835424361814494,14705894614041524810948959483843329992239672477759743245⟩
def resval7Tail28 : Box := ⟨-52125140564050738392539085587087281997228063006958096828,13896199076410933375421006562923078833122246061755629907⟩
def resval7Tail32 : Box := ⟨-52947612116062991106398907937866525969490545651346483292,13073727524398680662431671836939692922573122401484060838⟩
def resval7Tail36 : Box := ⟨-53783061272481666830831484045499039343025491859239394011,12238278367980004938070495345935460408039820093671870490⟩
def resval7Tail40 : Box := ⟨-54631692804177827987083244181382736308160550774581233829,11389646836283843781641026414038860035399202353136229994⟩
def resval7Tail44 : Box := ⟨-55493714713058737706460752644338232286982761382034846941,10527624927402934061183739416188361910928661266038611958⟩
def resval7Tail48 : Box := ⟨-56369338283049695648677407554474354686115374452641684935,9652001357411976107273575948397748037523323368286874991⟩
def resval7Tail52 : Box := ⟨-57258778131880305167112564513740645685520423291352107286,8762561508581366275239492959148709496204667320255166752⟩
def resval7Tail56 : Box := ⟨-58162252263687843364847180269125700698700561796687473524,7859087376773803434693818687032085939519477097894775370⟩
def resval7Tail60 : Box := ⟨-59079982122444009670819314786396216509212160987877459227,6941357518010533803865233153591067666577233752131105597⟩
def resval7Tail64 : Box := ⟨-60012192635872350128680882444852313088366396127994333836,6009146993802767730229068939800265563599440809386234161⟩
def resval7Tail68 : Box := ⟨-60958928258962455348973405902072944921911897317349914874,5062222426112799714510139451306769606409020882803512029⟩
def resval7Tail72 : Box := ⟨839211758968782394797295346852861271235841494669543965468,789529732651355224994438758825874417693048155550698260⟩
def resval7Tail76 : Box := ⟨-645247725293691547230694021953527974687205734992502263,254838568320964054947020102226146342887100605354780936⟩
def resval7Tail80 : Box := ⟨-655400274414369637908445346943364668335488174132673685,244657636397370878873206834299114557175799716262024476⟩
def resval7Tail84 : Box := ⟨-665741694986188760768604670392825944285247552886643760,234316214298076835288388183809042867794843376531130443⟩
def resval7Tail88 : Box := ⟨-676246292175658713380125808827369174883859598473126304,223811617107747095154972018831658147161500828293834016⟩
def resval7Tail92 : Box := ⟨-686916639179993030290143326840073935908905196186470210,213141270103410424081449046403281351840297010938472778⟩
def resval7Tail96 : Box := ⟨-697755351329558953933279984669458956700170649121804657,202302557953844477503811259965609548354326204827301596⟩
def resval7Tail100 : Box := ⟨-708765085222318348878288184292257787746930754793843323,191292824061085081901773284866394364837405713183688829⟩
def resval7Tail104 : Box := ⟨-719948539374131872220481786499412196043659198688675489,180109369909271558511914539091703981543352891639575934⟩
def resval7Tail108 : Box := ⟨-731308454880170377685290361382351066226857625853553353,168749454403233053040017550508997196972773502415983062⟩
def resval7Tail112 : Box := ⟨-742847616086764812119032969083420881618443796051764784,157210293196638618605955341879827558313055024898443647⟩
def resval7Tail116 : Box := ⟨-754568851273857108824041201641489924906636216112744865,145489058009546321910177939767439174593857621261477376⟩
def resval7Tail120 : Box := ⟨-766475033348219329517881559799001025877317054372735630,133582875935184101316466035016265886251104033605516437⟩
def resval7Tail124 : Box := ⟨-778569080547610966359433169770288743633319556801395810,121488828735792466717204398611257181277123298045273090⟩
def resval7Tail128 : Box := ⟨-790853957156047132543383067559300666266794869354672371,109203952127356438955821731452604271482134187277543949⟩
def resval7Tail132 : Box := ⟨-803332674230383234525402191881857566803586167384680331,96725235053049519773722648115996138100880510883329285⟩
def resval7Tail136 : Box := ⟨-816008290368446044135557212010164258483634749053234742,84049618943758114441335335241408388843729341033088905⟩
def resval7Tail140 : Box := ⟨-828884176379663156975239607988032943574871406515311982,71173987016568694461779671131245359377014349430826168⟩
def resval7Tail144 : Box := ⟨-964846626232968485333510846687505190443061152941892801,55388759595093486764766009507190622616699147336733966⟩
def resval7Tail148 : Box := ⟨448849613562214817117170976685966579347964238997,143242815157774912753526019521527925257763647864⟩
def resval7Tail152 : Box := ⟨455862664646694593108629410504503160837689340930,136161097013694541442685112554377551512953876207⟩
def resval7Tail156 : Box := ⟨463055623853893272146089472043468572559492035055,128968136591675577720774078086745685107667267173⟩
def resval7Tail160 : Box := ⟨470362080459628990627565104023875319278562921934,121661679985554963817138317138462869528685765921⟩
def resval7Tail164 : Box := ⟨477783824096903991771499340878765225965238860198,114239936348279293179325111938540897718296405712⟩
def resval7Tail168 : Box := ⟨485322673854986862639824634187647499034925412450,106701086590196417909731507838320819068514419570⟩
def resval7Tail172 : Box := ⟨492980477526552206490500335941343641967515325692,99043282918631073970507745554763942726227996404⟩
def resval7Tail176 : Box := ⟨500759112060204496154942501532620448095843979543,91264648384978784301371247886609257267072223550⟩
def resval7Tail180 : Box := ⟨508660484020522670426051193932085621758150858243,83363276424660610029702277450157539915376448148⟩
def resval7Tail184 : Box := ⟨516686530055364318028401489530829098441952488320,75337230389818962427256630118915865883912576864⟩
def resval7Tail188 : Box := ⟨524839217370543359240491582880920810376253712140,67184543074639921215297776817156539317438935255⟩
def resval7Tail192 : Box := ⟨533120544211997566179000439658371970844939167574,58903216233185714278132766049182442374250178994⟩
def resval7Tail196 : Box := ⟨541532540355564102275014624412777625736588746877,50491220089619178203015594035993180158099215132⟩
def resval7Tail200 : Box := ⟨550077267604483127028758494889732925158290948020,41946492840700154247145170075690559525153942020⟩
def resval7Tail204 : Box := ⟨558756820294751501740227088898688583519618420137,33266940150431872987548716976726801275263841308⟩
def resval7Tail208 : Box := ⟨567573325808495204371546067092368956978377135404,24450434636730837222800660493017102464307011889⟩
def resval7Tail212 : Box := ⟨576528945220321184134800246636455652598699915615,15494815344178138595361756875548077454083271342⟩
def resval7Tail216 : Box := ⟨585631827906965965548863853426258337329489636397,6397669675228162236671928159603215480953316534⟩
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
def polyval7Tail5 : Box := ⟨21220451724639384913216946529448620326122639530480254150582,6472586918526673155029991593960959931554557668774229598004⟩
def polyval7Tail9 : Box := ⟨21555282629431482307778783297998399623109391756894653752781,6137753928699463235489299651573157541240441244125036576970⟩
def polyval7Tail13 : Box := ⟨21895398868081322224802172729745689185952959784026187731875,5797637689848157425372990237545620532335175464142861981006⟩
def polyval7Tail17 : Box := ⟨22240881729020978154667376307671749678806605406196576014290,5452154828908343778817896007391458784321587379444975845201⟩
def polyval7Tail21 : Box := ⟨22591815890844699628789735622818869472273279075971666571357,5101220667084621757612563837418775646639691565498465884110⟩
def polyval7Tail25 : Box := ⟨22948287368474306249104508094896072106418341839350915782046,4744749189455015130908641384644967796570086628327765538709⟩
def polyval7Tail29 : Box := ⟨23310383534043005493634905500410593704500617575898145189276,4382653023886315886167167775474277142588725852118053933730⟩
def polyval7Tail33 : Box := ⟨23678193138310388413327423444141777914666599764477355675792,4014843419618932966457568575660690841627285067725512686956⟩
def polyval7Tail37 : Box := ⟨24051806332415482805560926406615170454060148858379709864605,3641230225513838574221371738011304779817177907684788649436⟩
def polyval7Tail41 : Box := ⟨24431314689973043718035819951680288876308524085019553892659,3261721867956277661746555276562762007977894784111920934429⟩
def polyval7Tail45 : Box := ⟨24816811229518496645541070243222930245018617977269940708663,2876225328410824734246358780877154621062396453227549712317⟩
def polyval7Tail49 : Box := ⟨25208390437307034731404699452601213734934404104113520298087,2484646120622286648438596128961845925908973214815870073041⟩
def polyval7Tail53 : Box := ⟨25606148290472458095669501762673624144624932793051179260996,2086888267456863285479888869893277293579296284708153549394⟩
def polyval7Tail57 : Box := ⟨26010182280551431668541346127086199676047069705241142133895,1682854277377889796777455051517768521248835067893211571657⟩
def polyval7Tail61 : Box := ⟨26420591437378946428736326022185861005467369759547601973459,1272445120550393408824661751200013494228348965830555164842⟩
def polyval7Tail65 : Box := ⟨26837476353380060896190790996393061124644186348114413339768,855560204567714160146733825223456543407457244786764181321⟩
def polyval7Tail69 : Box := ⟨27260939371308997349593735208379092613009989067960567406227,432097344080943024305928907773855711732309047853474240073⟩
def polyval7Tail73 : Box := ⟨27781250000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1031493916783461776249131134913538341101107454019992438187027,3851528588898152805486663339119463822851328020669566979⟩
def zend : Box := ⟨1003798700520032658766542968750000000000000000000000000000000,2150339076176447207031250000000000000000000000000000002⟩
def betaquot : Box := ⟨428759471371425155728945656436121555866261561715668758576861,394789887264355115209429243492732567529598232912596782⟩
def crit : Box := ⟨159108175708675052247305050424903122107516271512090857870,9505943810496801715330856550645862482649641003688820457⟩
def subsonic : Box := ⟨418674339326029306506752571906103194154829836929765209757,4691815985397375426534557119810960889873497497808464894⟩
def pendTail4 : Box := ⟨27691393775403750033902572613225042567423752691355688688969,1606758376672581748805454131038839846282137769277202397⟩
def pendTail8 : Box := ⟨27691429920830831921573641127051667767939561398638689256903,1606635524827031296756490727055956474098557576106938319⟩
def pendTail12 : Box := ⟨27691429922419303475188805775088017508252792340622234463021,1606635509233831417381858088730056637017925293610550643⟩
def pendTail16 : Box := ⟨27691429922420098687696245384322327855630998953933047510529,1606635509220777564044256556346369570026283784863854558⟩
def pendTail20 : Box := ⟨27691429922420100634171668484334786816843417037747297473984,1606635509220728924324549163418007003917868250086122565⟩
def pendTail24 : Box := ⟨27691429922420100651061975250950615189025939988251247359202,1606635509220728286705302517286446608022665838340403798⟩
def pendTail28 : Box := ⟨27691429922420100651489322068367235776021301149041055586098,1606635509220728261435910325243072445052863847307521590⟩
def pendTail32 : Box := ⟨27691429922420100651516268969967374773659869398390293208549,1606635509220728258674970376895785073291104711783032402⟩
def pendTail36 : Box := ⟨27691429922420100651519601637878773283580956068600776765087,1606635509220728257886140815282610122115596956930088412⟩
def pendTail40 : Box := ⟨27691429922420100651519504937416740883443825818933549954602,1606635509220728257311131219644706451402865234786017698⟩
def pendTail44 : Box := ⟨27691429922420100651515536351144910557902269219941081738522,1606635509220728256243308569112140948432857218042896031⟩
def pendTail48 : Box := ⟨27691429922420100651481391440727381984630863773179412680629,1606635509220728251083586717121440663091836755203258253⟩
def pendTail52 : Box := ⟨27691429922420100650868600038091282611971645993282905620674,1606635509220728183050858543074592278819311399248489119⟩
def pendTail56 : Box := ⟨27691429922420100621650280134314028793643965346543315796730,1606635509220725677255312011062865318230873130930934604⟩
def pendTail60 : Box := ⟨27691429922420096134427239957546005113464509669226294248595,1606635509220444463996331778677288922502997174488863149⟩
def pendTail64 : Box := ⟨27691429922417191723011235814351167385168006831232516165042,1606635509084939208697542415509787980195093324009617483⟩
def pendTail68 : Box := ⟨27691429909342315777289070421628030487830154826980214301976,1606635059903418001499290832033738599620191183446507584⟩
def pendTail72 : Box := ⟨27689828408687599294379382977340777244533346328134862758274,1570678746002154259024486957356949170823351303719644251⟩
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
end SepticProfile.ExteriorCertificates.C28

end
end

end OAI
