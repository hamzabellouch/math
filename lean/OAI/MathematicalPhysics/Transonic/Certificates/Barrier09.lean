import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData09

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C09
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨108874132032460015133620993569895927379832376805767317688,372808786210311751027815978340070219522679130687244833⟩
def polyval0 : Box := ⟨3758964768974162248368477769099885298727654024875125695979,15780601838499055603875063872885621596561695634118161342⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨53235015080517827560950506824477922670955484313320,1714950446933667959356064407153430152103720396350⟩
def resval0Tail8 : Box := ⟨6130226873311601608131730497012095510475073032,351564384941082031059802751102398562811439175⟩
def resval0Tail12 : Box := ⟨5309660568262445434839633426066793161916147,459469704969362846014284350934681343486675⟩
def resval0Tail16 : Box := ⟨20251356006415157213151434863964867380011,25343303252689072896717970126256415602562⟩
def resval0Tail20 : Box := ⟨262819495415073574623942319710545376228,365947555282849924509591399202886664718570⟩
def resval0Tail24 : Box := ⟨9960985195172651325301453406003720450,5854454683813910020405230522215983747407462⟩
def resval0Tail28 : Box := ⟨1003333826295791711092599277628134882,93671238460977296747804372143410473840468261⟩
def resval0Tail32 : Box := ⟨251770038127967668776952208912787915,1498739810342550389464785652980537367661963185⟩
def resval0Tail36 : Box := ⟨-378195141698812141171324034583269523,23979836963491262662002074370202703619810966533⟩
def resval0Tail40 : Box := ⟨-136710709989073548994349122613120428039,383677391286806900062071821027542231914089229640⟩
def resval0Tail44 : Box := ⟨-35057182391890009101586652832354552332375,6138838227720830431768290160078643444892137755814⟩
def resval0Tail48 : Box := ⟨-8974852423418252620685064579161560058269026,98221403229596874490978701779332896456124889373254⟩
def resval0Tail52 : Box := ⟨-2297564109281469254971421660255788959257410135,1571540297706965810126250528873838278962141424683171⟩
def resval0Tail56 : Box := ⟨-588176449541777493745378164033860302677605165200,25144093347875163313278988969563423540545009002771212⟩
def resval0Tail60 : Box := ⟨-150573170204903189191990592700747845920173043084192,402164331215137580867855856802980085194422716797439443⟩
def resval0Tail64 : Box := ⟨-38546724092828171769848224127359777121932595309868313,6398491740213413486391900783830809476076054761429219483⟩
def resval0Tail68 : Box := ⟨-9867786842365178934938144851440263922637530202121783608,93124723587856274108358605028913898115406913046190969916⟩
def resval0Tail72 : Box := ⟨747987827144984799106517605059546907252592141739112153160,2538123435347637092044341941211687387130893292515299468⟩
def resval0Tail76 : Box := ⟨-24339618960909505200468366634142958983515256076753,584745947672227548787661788740006978778466310193⟩
def resval0Tail80 : Box := ⟨-1252065167699331907159814979459870893477543082,61533388717134613953485677523442852745896171⟩
def resval0Tail84 : Box := ⟨-674234947839965801475828599828368915293956,51853221836927844646572543305395932767381⟩
def resval0Tail88 : Box := ⟨-1776570993181377815535061074130511957349,348515200372375158252210747015465996812⟩
def resval0Tail92 : Box := ⟨-16855993967972557636200168131153145705,2431441715540939492643865040139449166126⟩
def resval0Tail96 : Box := ⟨-483449665098985242801569077616598572,38861676103951587666095456326558947007041⟩
def resval0Tail100 : Box := ⟨-37654018755088973185755231852041545,621785195128064563035705473051520842272330⟩
def resval0Tail104 : Box := ⟨-7469226098827969217943817469590393,9948562949176210924445322970486927106052740⟩
def resval0Tail108 : Box := ⟨-5400319040983802847716909033439863,159177007138687429314194189328494509230380062⟩
def resval0Tail112 : Box := ⟨-456949214542354973404087917214534909,2546832113796925778272133234485933697660483423⟩
def resval0Tail116 : Box := ⟨-115892793149259320051616997559692121378,40749313712112703979930703697099500632167288426⟩
def resval0Tail120 : Box := ⟨-29665462566734229659763906622010728739246,651988991582492804741074054765536098710589154406⟩
def resval0Tail124 : Box := ⟨-7594336822924151868838929756808650040681926,10431816745630120745900599681630570684787109705093⟩
def resval0Tail128 : Box := ⟨-1944149869815179942362235565994522879491475958,166907245289633935944948392700082904319231585254514⟩
def resval0Tail132 : Box := ⟨-497702361959549560332929909507596102929164061555,2670049328680986935619143881988382008643887623889421⟩
def resval0Tail136 : Box := ⟨-127411822443165921393252525897619289797772698943781,42601340686655622362645083524183166524022434978480401⟩
def resval0Tail140 : Box := ⟨-32617644805375636508837375927132650884699035668159947,651042511267584104482015035659739961411576592595978547⟩
def resval0Tail144 : Box := ⟨-8506361691516335863158400401393387190203846343228167985,2508872455768967922270185538485549246239038870550025994⟩
def resval0Tail148 : Box := ⟨52079117265062947839371232540990959761661013,1046923978002712461331261241534081547340154⟩
def resval0Tail152 : Box := ⟨883474002317186052303484688623197279175,38723309252572523458002236224567066294⟩
def resval0Tail156 : Box := ⟨267174993451020336381187393827836065,18724335827355950078398961852531972⟩
def resval0Tail160 : Box := ⟨445549866475416385874210902134104,46703236534307399995587379082882⟩
def resval0Tail164 : Box := ⟨2832756568828941494777092589505,25311536695022297569633989483857⟩
def resval0Tail168 : Box := ⟨56194533390127452597111561389,398624196670862321665991054150154⟩
def resval0Tail172 : Box := ⟨3078111236944043137344868397,6377815562928106657682819957964650⟩
def resval0Tail176 : Box := ⟨431763375628367992030387260,102045036265790858833224079307041676⟩
def resval0Tail180 : Box := ⟨154289245958720019304010940,1632720577803145064575582040424464924⟩
def resval0Tail184 : Box := ⟨1622244627988182617051813426,26123529242688216693818984280063096811⟩
def resval0Tail188 : Box := ⟨384132580760569688286176803222,417976467523141454084402658429895927310⟩
def resval0Tail192 : Box := ⟨98276612826576447091488106901934,6687623388236797691866726648400851581640⟩
def resval0Tail196 : Box := ⟨25158521112458184026300403226679196,107001950625683961546881863547628850866434⟩
def resval0Tail200 : Box := ⟨6440578046082768489343180047986543023,1712025171969305069565676919496599128373826⟩
def resval0Tail204 : Box := ⟨1648787902970820244967517204180848432449,27390857012880392082557458887143682666873357⟩
def resval0Tail208 : Box := ⟨422089716370931879212927777625635730442254,437858003110987351715879447980591916337472256⟩
def resval0Tail212 : Box := ⟨108055045257208802868089304667002221771811569,6904426484479694820445443825532327729237167819⟩
def resval0Tail216 : Box := ⟨27666561776621473056986684750949357899678408253,84535387473458241837364391209525507393507229235⟩
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
def polyval0Tail5 : Box := ⟨1971570205457814055752417343275364315036079914552390,51705057289491099858866839031051457948131845245840⟩
def polyval0Tail9 : Box := ⟨181974978135880827948815893276335367696632793084,9403308362805173899358661358598937190961741580⟩
def polyval0Tail13 : Box := ⟨136377301235276707671953429481441229764165866,10918891607019844243704452753349159622293818⟩
def polyval0Tail17 : Box := ⟨455796988829637893561269845397519008198785,420406069751066006983910371016420015409470⟩
def polyval0Tail21 : Box := ⟨5197676650217922112066276320789993948320,5892166157175567196875652240976677499272773⟩
def polyval0Tail25 : Box := ⟨172903046728683431670922408651723037237,94261496823531542949862989311990776614202512⟩
def polyval0Tail29 : Box := ⟨15231767998764955250083993594637701724,1508183351706201213408818963922158657415918734⟩
def polyval0Tail33 : Box := ⟨3373238803317863628160479251179534208,24130933555339764014918435434660019210534176262⟩
def polyval0Tail37 : Box := ⟨7390108621754509633536809016450556222,386094936861696914558058623533985890518847789831⟩
def polyval0Tail41 : Box := ⟨1437122846921864079000571510645784013394,6177518988443148674881339241587666684976123641726⟩
def polyval0Tail45 : Box := ⟨367326202105742982925709956784991232208531,98840303470728510215212215269112083244701239392731⟩
def polyval0Tail49 : Box := ⟨94033747629358636259342270136285109490278905,1581444767375054594877287107556124566322362871202642⟩
def polyval0Tail53 : Box := ⟨24072626355849286003134535874427164448426922811,25303093709914312944361108494472319727248138378244728⟩
def polyval0Tail57 : Box := ⟨6162592121828697646222026488795431029378852536314,404843721928551927784404746232876357467853763136027886⟩
def polyval0Tail61 : Box := ⟨1577623580689074838661498175191993144503627914914391,6476020528757819596229508673023985670970749482552935104⟩
def polyval0Tail65 : Box := ⟨403871649699047528443158882785458187464379113142275869,103237698796760976895512223708526588598197660682784690118⟩
def polyval0Tail69 : Box := ⟨103391302181467493935759281754631275187009388245435795796,1554873910203399353347987379030992995790878960543893506697⟩
def polyval0Tail73 : Box := ⟨26593750000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨108660485636298636313523374897635482582524143110775237022,300613987628360830503769827046797293744753617638433337⟩
def polyval1 : Box := ⟨3741227018114704301623121105897888969213654892800430271479,9747386625407712978641272609326828733450134352817192265⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨51708466882847509763430410739474833338443310025668,3072579659571487430392954834774373412127552567129⟩
def resval1Tail8 : Box := ⟨5776092509232519808200795691165842622280788235,6052264156269684716881054950333291260544326998922⟩
def resval1Tail12 : Box := ⟨-315612540696125385196257018358592389434341054,19127316975817277220644251244475650324713531239229⟩
def resval1Tail16 : Box := ⟨-2100687258985563115651405891894101063021510015,60450678807230059824475428205580338079479297944079⟩
def resval1Tail20 : Box := ⟨-13767183951345690026343748252286888572225912186,191046869296824799299156769109271687070171234953038⟩
def resval1Tail24 : Box := ⟨-90224618252564873246106884423149702155998428180,603755737593253081793564093394907665509561881613967⟩
def resval1Tail28 : Box := ⟨-591296058235020014426355547781731198962915159528,1907860140067040353982159808747454842803185294365665⟩
def resval1Tail32 : Box := ⟨-3875117847254271200640856663097637217783287862810,6027773865462260047843281363519967060391180605740539⟩
def resval1Tail36 : Box := ⟨-25395972323766801828311957658466948376302073430956,19037593407024822056641018099012909619891510502125042⟩
def resval1Tail40 : Box := ⟨-166435044221038729944236778669673985892310696515000,60082025216436229867442897130314334815289970410211394⟩
def resval1Tail44 : Box := ⟨-1090748705806999945507116693333800287020852526740532,189324138043924614124231107097142961796806499226845633⟩
def resval1Tail48 : Box := ⟨-7148330718376753351516279869132148928662961707971724,594656743453614516204927012387667919652868713913492688⟩
def resval1Tail52 : Box := ⟨-46847300195953791345196137935340176391900654923375175,1855153921878487622027081434583009687058519266311208584⟩
def resval1Tail56 : Box := ⟨-307018466564193371779061414027815416654605260911917110,5704244655053784148079607594596285707951836601954952581⟩
def resval1Tail60 : Box := ⟨-2012076222472243917406463668204771907763346348661503296,16986483766836059360446245824428341530412537714068469671⟩
def resval1Tail64 : Box := ⟨-13186342727179738766973195292337936535415577192439668718,46858488839818931228646992590491179415460775437872622341⟩
def resval1Tail68 : Box := ⟨-86417935743209745702399935740438982309064963406331002175,103353311519230485612412809780466087680895029358870522416⟩
def resval1Tail72 : Box := ⟨750658649906417755152902321061284867901592267426895718656,1649000393513036456120420640850837264364677788954627947⟩
def resval1Tail76 : Box := ⟨-23803126770448290586981543930559108127291210987539,410833287252549469546202000597638164965041002731⟩
def resval1Tail80 : Box := ⟨-1197368600545069071454234881690026349081541224,60226653948587500994490748368118450118583445025⟩
def resval1Tail84 : Box := ⟨-3282461227999656042951259124583261926368057,190217988630011634099828545872048356970117591479⟩
def resval1Tail88 : Box := ⟨-17384462877167017782837304445363286612821927,601173773117798688280733625268704975690890146766⟩
def resval1Tail92 : Box := ⟨-113920215363512048657333184637229054639750371,1899947017127788975622308320405535670850158717118⟩
def resval1Tail96 : Box := ⟨-746587425753590499572510017657310198965723859,6004384276228630059779494038720571092968387399709⟩
def resval1Tail100 : Box := ⟨-4892835350717561984406289262988860118554669891,18974286190518610351427113362039563668046777084778⟩
def resval1Tail104 : Box := ⟨-32065685754262385480597873697423425141482706592,59951512470079565039501399488614368182788341819611⟩
def resval1Tail108 : Box := ⟨-210145678159097294883734977463567520569725982734,189367582814352734517352375453665328352767445546716⟩
def resval1Tail112 : Box := ⟨-1377210716383444717075470212536319848411994903505,597782029951308263453829762820551168550696762194690⟩
def resval1Tail116 : Box := ⟨-9025688150890531172030746205904355615994913629334,1884613393465517825850709798440538647309922213716216⟩
def resval1Tail120 : Box := ⟨-59150749865676188950907470790574969976926629467510,5925683878452849002693209806309232166027941484447907⟩
def resval1Tail124 : Box := ⟨-387650354319696229321170965688661507415983467511285,18527382545057371676363072541068831272079137963401726⟩
def resval1Tail128 : Box := ⟨-2540505362069618630609008498450881742669694735356727,57240339356949306849581583986247084200833313331527378⟩
def resval1Tail132 : Box := ⟨-16649455940871869192698356993834357250782034792414504,172287534776036917921531868283321861760476713873968617⟩
def resval1Tail136 : Box := ⟨-109113874466155606937053849868218608017939306306651827,488020318426276087987678218916934429953027817812493215⟩
def resval1Tail140 : Box := ⟨-715088791854326518622413255820625487763070594157587250,1172150220596381295614199373824935216389091748452981074⟩
def resval1Tail144 : Box := ⟨-4751345427776327078371150088358546268985111725954457612,1265012497020247621384792962818424233654701578302661902⟩
def resval1Tail148 : Box := ⟨51316145622796447914626171967983303331421442,779912276797486213064189927476187424089707⟩
def resval1Tail152 : Box := ⟨850082531805664751447845540114946980780,2583604339054793915394425490718992075858⟩
def resval1Tail156 : Box := ⟨350553681927438785561965833206598395,8082542595789923336591147802523264494784⟩
def resval1Tail160 : Box := ⟨649751246008921831844993647258822133,25544485828652622957652366903665964456293⟩
def resval1Tail164 : Box := ⟨4255528068243238031318071732653476114,80730986484522760207866791423195881386779⟩
def resval1Tail168 : Box := ⟨27889012161541456377556239132853003841,255135344994865981660213115324230116163221⟩
def resval1Tail172 : Box := ⟨182773429783482321733339328052753779256,806259052567579953793404148508928430538774⟩
def resval1Tail176 : Box := ⟨1197823949412320032454987355894308409566,2547556589079283669486099671038754268528193⟩
def resval1Tail180 : Box := ⟨7850059034866381428803878754769597462887,8047472530290393936898664959616904410011245⟩
def resval1Tail184 : Box := ⟨51446146890899642071713140111441181610370,25407351172458070913382517713092984559214593⟩
def resval1Tail188 : Box := ⟨337157468264199461231580372920922641373746,80125214306468349261504361725424058138149775⟩
def resval1Tail192 : Box := ⟨2209595184016257256297007098677606864694327,252091234128718711517319677321332022272468092⟩
def resval1Tail196 : Box := ⟨14480802997968948130256319000481155790897705,789235398286724290778122416658522457186325559⟩
def resval1Tail200 : Box := ⟨94901390527489570554886324027506484212252868,2445238702421664580825893322144728655842982928⟩
def resval1Tail204 : Box := ⟨621945752960989788814653841776430002467062406,7406151330927720705030990423749229189380603714⟩
def resval1Tail208 : Box := ⟨4075983686620570719716875949959136737492014074,21296767590866662456801902204318740840629112856⟩
def resval1Tail212 : Box := ⟨26712366730207576443735347493015633669304096498,53478057092685332928643386940663797498801286527⟩
def resval1Tail216 : Box := ⟨175064139677764538619920267575924604736638258824,78378746865447252293445920580085342798574540947⟩
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
def polyval1Tail5 : Box := ⟨1919041993659793720976953946221910362331819207030201,117255566109441266088006131932120429979573969440193⟩
def polyval1Tail9 : Box := ⟨175521021861885105464013907781604531182874987537,267933499014254596610358817393044809733481287035310⟩
def polyval1Tail13 : Box := ⟨15148980393420999893058626343250172181263876458,846778623242197710314712619691599781543739233253617⟩
def polyval1Tail17 : Box := ⟨98449112358146749527013244812003769794629970047,2676187640032138949701447276796182135567294660564722⟩
def polyval1Tail21 : Box := ⟨645193395295059684776346521446881115041850675720,8457740469753515899984286786984019444137715845040741⟩
def polyval1Tail25 : Box := ⟨4228339405439216106406105855655320841382346824563,26728447336704682404072246897395278765643727593318218⟩
def polyval1Tail29 : Box := ⟨27710845126525791892735553180072879017745992657910,84460745612702527590542733157326666105740229577755534⟩
def polyval1Tail33 : Box := ⟨181605794621119023625590078867538606845072508262038,266843639306665726620025808730761568815242805249252909⟩
def polyval1Tail37 : Box := ⟨1190171735628949345754187371734622062509715638894497,842741467103006011739142813930362903030893489374468666⟩
def polyval1Tail41 : Box := ⟨7799909486617875061996441711843854892243603792331198,2659440825608327183724761821420727035075752659913823901⟩
def polyval1Tail45 : Box := ⟨51117486811498899919981404840947190266437271169420505,8378680392007092888655693291337740797115038842766318714⟩
def polyval1Tail49 : Box := ⟨335003561567839194967800362140029205715436214074933866,26307320598648944739151719635158683879566274203164979665⟩
def polyval1Tail53 : Box := ⟨2195479341090991446261091655742637240751465014470742852,82007421708483042143536107027624273540589705151229279562⟩
def polyval1Tail57 : Box := ⟨14388293409773960346497952289067755873051888351327142614,251734455586410669577030144358807567756190990685415829535⟩
def polyval1Tail61 : Box := ⟨94295119690303342782208343122023779706109804556986283268,746784185779126352010379619731979226150902685436237309037⟩
def polyval1Tail65 : Box := ⟨617972496411114715281154583597252491846095643436697823333,2040253456684260422093462155186021302184930733232304968551⟩
def polyval1Tail69 : Box := ⟨4049944628762312725140824475498811051414718622033752353066,4351362147338956885650636821951849727887114446294075357704⟩
def polyval1Tail73 : Box := ⟨26593750000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨108555280483463567950087230235769859627132562692855991197,284549898961331560411629431480279192112993758369737808⟩
def polyval2 : Box := ⟨3732461538011151056949773523265727593886693251058847145392,8503167139038167938397564279965184583235410390431637998⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-142339367103908387707750031883690768311098809361306,33828788431879636441412252873356098182419346955274434⟩
def resval2Tail8 : Box := ⟨-443591499666952462052040208336164203346816220547433,57595189721944038348496769471176447292396321164246638⟩
def resval2Tail12 : Box := ⟨-1017876997585294233805544573443005089805852207252287,97993730874403449774965767679021292590992172579260789⟩
def resval2Tail16 : Box := ⟨-2335618053473055943663141549087458544575177007721648,166573813792559830786430757762246045831865592314292349⟩
def resval2Tail20 : Box := ⟨-5359303412119733272802128299228046796837540691792174,282792730257775243647668790479176896835246405234954715⟩
def resval2Tail24 : Box := ⟨-12297444361776301344985889886378394927504690414498833,479277203664833708032803028936022908288456896226936529⟩
def resval2Tail28 : Box := ⟨-28217685434451601278839022574930707386848799944888556,810386961927895181593315650314879693988629943051655912⟩
def resval2Tail32 : Box := ⟨-64748231246532690953849378216888350910058522111479670,1365874274207933125319750999903723316213765432129478213⟩
def resval2Tail36 : Box := ⟨-148571131366995778977086934797645735698954359213500406,2292007703427461523726662075003144682408322950401151876⟩
def resval2Tail40 : Box := ⟨-340910950781395447419921416836523988255693792746821868,3822608794040802433382771781596074571538999099912975061⟩
def resval2Tail44 : Box := ⟨-782253424964445643953487498130047025031970658876485255,6320527447501911090238245770560883320812795479176667655⟩
def resval2Tail48 : Box := ⟨-1794956775269420175145337382329833895337911597103397064,10322073817659441620842491418432203762995084388266194570⟩
def resval2Tail52 : Box := ⟨-4118703379575530185898115301643454247008165274107687399,16552415866004068992849198319050856434116795254639126052⟩
def resval2Tail56 : Box := ⟨-9450766593741875626395989827679649356015966869359592383,25813250245031142473182206288308858448747301962843234115⟩
def resval2Tail60 : Box := ⟨-21685705664626589530672925353142554217372257644131119990,38473150216926217874190079522810960028342531511196163047⟩
def resval2Tail64 : Box := ⟨-49759966609561406441759192055795403395961063646531652557,52868385611242155958789642760321203042612654354999549538⟩
def resval2Tail68 : Box := ⟨-114179033559972948833140755166817484724610312513509376626,60900341941053849679383543082309778856282597590924457394⟩
def resval2Tail72 : Box := ⟨751992497986671773370405071544115326901974549394275542099,1204848779220164889831631822577768423940976782965593210⟩
def resval2Tail76 : Box := ⟨-25624884857089500318968239334063942076608297438876,392507457765714042426563102021124549757094631710118⟩
def resval2Tail80 : Box := ⟨-4771795568295799410462902505188717345614234140817,668179240920961182954220837570997489178412150513678⟩
def resval2Tail84 : Box := ⟨-10946663079626446155951872822538927382173294639308,1137076078672801721979373653571525799727311022092696⟩
def resval2Tail88 : Box := ⟨-25118184644802584905306439583088659596493979754853,1933357928509598761833536441778511236545976088902961⟩
def resval2Tail92 : Box := ⟨-57636124392720297041388806379698268293431835165815,3283437661310717910572426944361394987416982476644618⟩
def resval2Tail96 : Box := ⟨-132251708560638617528708468510823146256443057003649,5567472667216630712456498816733698030756441145824180⟩
def resval2Tail100 : Box := ⟨-303464443549945299111747561098922089156294866320155,9420013708546553474611255470474088656686897274982337⟩
def resval2Tail104 : Box := ⟨-696328762035265339885589896068644569692169757657736,15891495690687458050489700544140712330702123748521522⟩
def resval2Tail108 : Box := ⟨-1597794256109490179854659898630095174007081467647521,26700301936457055004282887208130517442072034563914610⟩
def resval2Tail112 : Box := ⟨-3666294750477628526361956010033909150474998907491613,44609008042005740514803311958132584153160143260670911⟩
def resval2Tail116 : Box := ⟨-8412670871723744376560644224167945306744126468939945,73942864421075872280546932430416416873912621191391057⟩
def resval2Tail120 : Box := ⟨-19303693786957295349606016977924252894345715104994265,121191213568022808728327320675580409410659691853677531⟩
def resval2Tail124 : Box := ⟨-44294208046708215144189230185293324929860867658518431,195383901293566048886256002505058510934600464316660298⟩
def resval2Tail128 : Box := ⟨-101637380293024441489497944248120984278592061901926259,307242892867226906483054687127955322293922052809849965⟩
def resval2Tail132 : Box := ⟨-233216881582715836610273278759073179927237629282045072,464314813071349205230442255354981710887348133977952464⟩
def resval2Tail136 : Box := ⟨-535138880000116319610605611131431306593056641345681302,654819396269336276174772405796212909543353888383890352⟩
def resval2Tail140 : Box := ⟨-1227928433496625264198489377173788036721446535645382290,802087922510190974501468504638916572993096353272142145⟩
def resval2Tail144 : Box := ⟨-2867864273267374028147119001583715481319334016585884850,639770747633445194944628894907905147347762401089099264⟩
def resval2Tail148 : Box := ⟨51165369502472689099834142260551295414694989,39738812980082453571896816914600629696063811⟩
def resval2Tail152 : Box := ⟨503000667521100580464996848767478954546795,66619821023439358078098729863029607381655655⟩
def resval2Tail156 : Box := ⟨1152269702066847443673723060549060672493060,113354862650962317645963563334237013073133680⟩
def resval2Tail160 : Box := ⟨2643994649785992467878494890564934991922801,192700117429329985789609181940718039696858898⟩
def resval2Tail164 : Box := ⟨6066903586801414584611004253544380018938322,327181527514578642632811621239078144076823519⟩
def resval2Tail168 : Box := ⟨13921101973476440704583998294373915714703007,554586009143242672044505045534962081306969141⟩
def resval2Tail172 : Box := ⟨31943326176735725964720580289221645771339567,937904706782065312349440331345161662183674138⟩
def resval2Tail176 : Box := ⟨73297077284358124280438427066806296847466431,1581220849829031731191927505300088605307206641⟩
def resval2Tail180 : Box := ⟨168187292353478310094997093541322465325239426,2654347247195228414921628628072508284285382497⟩
def resval2Tail184 : Box := ⟨385922145291745895655064314943972678583848884,4429197169157026593030987434715255848803567688⟩
def resval2Tail188 : Box := ⟨885536000624623052997593839874482523814632663,7328844970629925932239713369173550850167820857⟩
def resval2Tail192 : Box := ⟨2031948718074832688337616664154818611075628505,11981422568163664872728302870018014664641323661⟩
def resval2Tail196 : Box := ⟨4662504505715914542919636883139202002572337403,19243688242486037153353767774800243206099809230⟩
def resval2Tail200 : Box := ⟨10698571313560385947150353714551400394610753849,30084338097782885461001018657171609650356070829⟩
def resval2Tail204 : Box := ⟨24548915290273249999675168654278474164822942130,45024927670518960302229390890536764006127992484⟩
def resval2Tail208 : Box := ⟨56329880342554851705292111935805615343520817043,62360024183655169183605656965482345985960620924⟩
def resval2Tail212 : Box := ⟨129254404225250149752870165739892623140373473009,73225332970694155515491402486961420294565454331⟩
def resval2Tail216 : Box := ⟨296588378320772503409964371663400779745502600973,48834453034513297385423234240836913771958661007⟩
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
def polyval2Tail5 : Box := ⟨21487460994326105725470298251719037739770994635357478,3005544122628918513511535715779005609921276600517745944⟩
def polyval2Tail9 : Box := ⟨44959244898986636117724431790606842308438844574563689,5115783114229068836118416169048043986040823719062863782⟩
def polyval2Tail13 : Box := ⟨103162984103652053508703483985546637798315729884823566,8700835351947637784490841279225610037572241684543612924⟩
def polyval2Tail17 : Box := ⟨236717528034342663368520454430600681630904332796713165,14782514951748131164861800690146776955082600158940518341⟩
def polyval2Tail21 : Box := ⟨543171454684110126287533269098054125456636104595438269,25078976082670061670034460976350082147987781397551525823⟩
def polyval2Tail25 : Box := ⟨1246359877251411380080701228568017653932323588569218283,42463892647947534720416189311998943889697012453676811059⟩
def polyval2Tail29 : Box := ⟨2859894293461310438792798264500540537718830627291017998,71707866782429935981548507995975659625165696130095496547⟩
def polyval2Tail33 : Box := ⟨6562306376397200385828523768592081738218270279720374987,120647001981308149589710358616259716490889062998648128032⟩
def polyval2Tail37 : Box := ⟨15057851989901156274644233678832619483072898962376970016,201955611997254659423468542189720163815641843956180706793⟩
def polyval2Tail41 : Box := ⟨34551709954489064723802775564309667307175252505546837063,335663678838259882005305096485278576911928992076623629002⟩
def polyval2Tail45 : Box := ⟨79282268253121226349439006785468464097926684368374681592,552288840657790762739954036220547304231987466142585250714⟩
def polyval2Tail49 : Box := ⟨181920896755595136398246010035873239913373617966562009505,895511532273599160707261731496133042519245423965675899833⟩
def polyval2Tail53 : Box := ⟨417435240004715621823198352888388189834698857942247165471,1420616917139632500626740446457067000972630630208833856560⟩
def polyval2Tail57 : Box := ⟨957845869855713875245078556582279281544448114197191356641,2177789963406780909319696597903804671474418184159337487319⟩
def polyval2Tail61 : Box := ⟨2197870765269572944608090409099236850192073975790788874301,3151385533373989386793754041415304866190831590442291882315⟩
def polyval2Tail65 : Box := ⟨5043228825072950976285496106569124253066550931779595647639,4082366259999309815518050791268876906965084371958172837703⟩
def polyval2Tail69 : Box := ⟨11572180455892767796868292637554131246186327045384538964733,3995681932387365648854994096201296925969427758158828377887⟩
def polyval2Tail73 : Box := ⟨26593750000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨108372307605860170226173659348199076669074553022912236571,1821534735099111141990581813705106116942542434084998689⟩
def polyval3 : Box := ⟨3750273492789473878673116876713428239667686505918168894133,236305484045824470147444773343644996400608720814478567040⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-194029328204906167548259864383545010962744669349189449,2015212048940188239618316221345547599944088720755834652⟩
def resval3Tail8 : Box := ⟨-287732289512379207886271031239614079417357824952792139,2572279823498089189089008964830256684659341323159191286⟩
def resval3Tail12 : Box := ⟨-426576112032297059842852246219909469690776601400415974,3275819032601177199556589857735245305731482884642927142⟩
def resval3Tail16 : Box := ⟨-632418336213292661151807105982055043620586523786018370,4160473875124862594856106735530814437790199264383217369⟩
def resval3Tail20 : Box := ⟨-937588722605594350331238747338911850870265383725137664,5266993676648892502363698476324178248020784154695893756⟩
def resval3Tail24 : Box := ⟨-1390017591869262597379541504127616895211813318920202625,6642051783292062102277944417959977907893273529935388887⟩
def resval3Tail28 : Box := ⟨-2060763807329624159077251331364860871800748926967322579,8337057399002673637102511362109487072332191101360001951⟩
def resval3Tail32 : Box := ⟨-3055175340542822418354973152710969892052102223295024773,10405202152359764611818000387919040273234885806310823372⟩
def resval3Tail36 : Box := ⟨-4529435313383267131820971691672457626948622167787738578,12895538501428860149425921097927246645316331553173011427⟩
def resval3Tail40 : Box := ⟨-6715092252112205355469441250376126815104902498700858142,15842203232875993627260714539180868908083013404259967025⟩
def resval3Tail44 : Box := ⟨-9955427296012204261976275749817104931851768990455658354,19245855013206296646869539213008245310127179537579448105⟩
def resval3Tail48 : Box := ⟨-14759370225332354599677885320929889896944623205445462137,23042807303891224172322048016264366595491846748041561813⟩
def resval3Tail52 : Box := ⟨-21881432405787938579172110461016222484354085004121438617,27054933155796188879226312246327004975142517301307885765⟩
def resval3Tail56 : Box := ⟨-32440210985918592501766993702357565427667676248466640969,30909787106801939681188695158638055028932516054351765883⟩
def resval3Tail60 : Box := ⟨-48094076717413641425016503831652441394131480638966080960,33914920319710578432938847832078778898856889587082523036⟩
def resval3Tail64 : Box := ⟨-71301639073799484774343391421347937107765568021844635546,34862146203290827851847183109072358895833261060875412349⟩
def resval3Tail68 : Box := ⟨-105707840817471366711097653829352215005234459308834503795,31725183703024462653620598225211086403651935697410387084⟩
def resval3Tail72 : Box := ⟨752657471643893079020062680612043611880141608715126025758,1001955353319430225027980715141987477062163137196189402⟩
def resval3Tail76 : Box := ⟨-2350977699109765334766622032102285731250337252193880,25107897059938605432595532877606109750694487108510208⟩
def resval3Tail80 : Box := ⟨-3450710863524088342862324482019597635423817034656096,32065330651730214840508237924930625036982620745729598⟩
def resval3Tail84 : Box := ⟨-5115832857829106954411679045163075500259957904650501,40861040619510343210396185513137469266269908403006468⟩
def resval3Tail88 : Box := ⟨-7584453073251122923702635008005039327605257873135996,51934369251109885710437338146293101914614444548157471⟩
def resval3Tail92 : Box := ⟨-11244293945031444806527834861099838463932650261652174,65805099434706252353716451136811918429324152327907449⟩
def resval3Tail96 : Box := ⟨-16670173195243867789436570853524809717380820883683101,83073215338770725617933821861271822415303783180685369⟩
def resval3Tail100 : Box := ⟨-24714284037569273788400445721965926102737372349643525,104407349759273795216101824381831039772077362744988489⟩
def resval3Tail104 : Box := ⟨-36640041368251428790343905560065434090471644206741824,130512855273919580957750298771964031394245888830565388⟩
def resval3Tail108 : Box := ⟨-54320514785149905329634702163415783376818013175535211,162065307127765043698788516773316381816796704799906207⟩
def resval3Tail112 : Box := ⟨-80532614493183539682658698894891975671809748339079901,199587113405775356109013282128432133440239849205408229⟩
def resval3Tail116 : Box := ⟨-119393235184890338222896349560366380727212751083235468,243232473211873517474728432696575145080474584747828702⟩
def resval3Tail120 : Box := ⟨-177005859025241129508812292587640728817385322366797734,292426998762221903547658061588929166681510343131027102⟩
def resval3Tail124 : Box := ⟨-262419173755906412320954696052631619241636638530835334,345279626598842770273805095159776024841589219571002281⟩
def resval3Tail128 : Box := ⟨-389048267294432278977826166686727730062766254834957951,397641087373199217181843264885594274694489016352861429⟩
def resval3Tail132 : Box := ⟨-576781612861837660977604218840990374505634007260551217,441617864619610497309077364160171075087878880075826913⟩
def resval3Tail136 : Box := ⟨-855104769525129672722722366065751169936721083295681516,463252329864914501599953649165822237774775046990037867⟩
def resval3Tail140 : Box := ⟨-1267731483604668696833767081951440683654045658355842800,438932304174487910959952321987745334468324797201627138⟩
def resval3Tail144 : Box := ⟨-1924629227803032436116675875256417370943778562562833540,326321081876650711158171064369352708204193139921084889⟩
def resval3Tail148 : Box := ⟨508152970022907234279873202035421233696718258,4469975714531002214649361412629090641686408036⟩
def resval3Tail152 : Box := ⟨678099812310342002695871964413228849345715075,5699976038102170274294294733786728234082162589⟩
def resval3Tail156 : Box := ⟨1005312346834539559196655019275723638771221376,7251349855831410733706259788634858285074832646⟩
def resval3Tail160 : Box := ⟨1490420920598746709960621018251980911678068718,9198144296147998499251757701337032944492482263⟩
def resval3Tail164 : Box := ⟨2209616273075832571188788342148394720800410723,11627140468547647717901247980527206818929459685⟩
def resval3Tail168 : Box := ⟨3275855838283174261707342075968851659219037240,14636355318636060206187856945569702288914266691⟩
def resval3Tail172 : Box := ⟨4856604109941618238592962105028179878088400288,18331438761759299234512518327966167837597265117⟩
def resval3Tail176 : Box := ⟨7200134757170265119410366174959195297446707563,22817674183862649989019820525964980212712907013⟩
def resval3Tail180 : Box := ⟨10674524698294691809331754593076681861519050162,28184677805597320527013435294635117442688132403⟩
def resval3Tail184 : Box := ⟨15825464574955434627271798466868062644361945142,34479260270379220591894204615907220077423541340⟩
def resval3Tail188 : Box := ⟨23461965388789561461070999041195600792145798669,41659426166051958824224608605464698168350892819⟩
def resval3Tail192 : Box := ⟨34783422457998169325809844868429612247676918783,49518711209914796075334055321165266778261484444⟩
def resval3Tail196 : Box := ⟨51567993466978313292625260975517062167432764680,57564344944090212155358131498303276287958467252⟩
def resval3Tail200 : Box := ⟨76451877425846660686335827509768033909644076685,64824111317023203889560445381134361743311724942⟩
def resval3Tail204 : Box := ⟨113343358330966910415645413725598642583687393942,69543815955506582988369807081279855865752837913⟩
def resval3Tail208 : Box := ⟨168036643576259162546014549425675670315573361151,68717802923273371906497293838579698618062375570⟩
def resval3Tail212 : Box := ⟨249121907128754873700181346515177837055099257194,57365784864260802312603999790251574349080614316⟩
def resval3Tail216 : Box := ⟨369335859488539470572189744470173489333102256766,27425441972991083251856785051441211026333924079⟩
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
def polyval3Tail5 : Box := ⟨32891132609337267299279040777165630303198212595019235358,296934357845213723255502353876067811258517787583026860350⟩
def polyval3Tail9 : Box := ⟨48759798702294603629346494589771364393412093140032647217,378209473496940205293909921766566158273076233583446758051⟩
def polyval3Tail13 : Box := ⟨72288601713841161715373322042540104315244038179023713624,480439461728374468620971176110957509595677012694592906757⟩
def polyval3Tail17 : Box := ⟨107171114211418736808056580719705449489409489554539003925,608356517704452802261967490594094034451558376313376104529⟩
def polyval3Tail21 : Box := ⟨158886013133891918818146461129524476510413144154656560341,767391890772054377020652348477028476438178363448779403937⟩
def polyval3Tail25 : Box := ⟨235555684526919072229531768741307338459251771168371495025,963546512221329740816822798098520452373445730835419852469⟩
def polyval3Tail29 : Box := ⟨349221932242628733062490071704736323401586339219512551756,1203061753013533917859442636149907745680443428718733392067⟩
def polyval3Tail33 : Box := ⟨517737273902800536688493588675552401076465561632176887205,1491753365049256263116241638356744178837580657548757929869⟩
def polyval3Tail37 : Box := ⟨767568872513050648267157658744130939731984411602206448396,1833793666042248007177378698622394887905967777624259390493⟩
def polyval3Tail41 : Box := ⟨1137955491614004330043008156397303844097880433291366468045,2229607872865206587155652963089168568730495263429714170695⟩
def polyval3Tail45 : Box := ⟨1687070368884002545495519258658760480807877492640415740202,2672369288489025931928507461104290837671443516620496171442⟩
def polyval3Tail49 : Box := ⟨2501157954367375700976732395938715736479560295782227050253,3142303524854328877737059822902059687510992369242868732431⟩
def polyval3Tail53 : Box := ⟨3708079537211837082305787200414255445996624101283267020007,3597597331968876622244173301925782557814047211499118640346⟩
def polyval3Tail57 : Box := ⟨5497395248580746978349182644108162331969539766429602410239,3960083058552630892904017148189571571359066019005397569660⟩
def polyval3Tail61 : Box := ⟨8150136537211956910351046852564411162850974351292501518218,4092931084245689393571343560518810129332190278955950267749⟩
def polyval3Tail65 : Box := ⟨12082945207983987236473788994906601280122780513653012289565,3766174389845872464934229254009456011469725083090506462010⟩
def polyval3Tail69 : Box := ⟨17913511592940625309169819771983297983065366690160651847751,2603780346917206365589566889192141660115286855125403547243⟩
def polyval3Tail73 : Box := ⟨26593750000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨104951098114651094158226207222497568820308959911243730733,9260629107475795725119668633278895517716165025427829699⟩
def polyval4 : Box := ⟨4563456258254916555701763369741465025122056127869809503650,1866291134938242439513577267422471018323039903406812797712⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-4272636381111412192030413799161168776234089566820586681,9976068752946575829116725130902645231624233527252637356⟩
def resval4Tail8 : Box := ⟨-5177279578965143411125025932079833811396831005721357952,11000914999732885696951667357696373332398456483454044064⟩
def resval4Tail12 : Box := ⟨-6273388368558182490294819538645197442607595230092223105,12095513436890411638291458062706129580980823738109763524⟩
def resval4Tail16 : Box := ⟨-7601560043284180215187870109937161339846512386860221424,13254695071168821577970800356606108894981749554886727851⟩
def resval4Tail20 : Box := ⟨-9210925850090891716010357118651375305052910214106434954,14469497835881259986150666370946538157537430784374767469⟩
def resval4Tail24 : Box := ⟨-11161018860967601272407234580180759276163739456902344815,15725997186249446462182256301127874437768503637586467992⟩
def resval4Tail28 : Box := ⟨-13523976204155992811564930249107988375426094236242901412,17003840422349157641759081233534835355632221482052860330⟩
def resval4Tail32 : Box := ⟨-16387207534449167017288112579028875145453952810897544644,18274414504415422572149679913738129349386721530582195162⟩
def resval4Tail36 : Box := ⟨-19856628459208878396814532602052019640845707722944966596,19498562154783089185275391222943111775062866636323092107⟩
def resval4Tail40 : Box := ⟨-24060578529819499009184343713056212387356929716610118548,20623741971021566217584217846660519834437390233717651776⟩
def resval4Tail44 : Box := ⟨-29154568731487251361944235977783390832769306112570433594,21580505028059007803594954461359300648662424884644624115⟩
def resval4Tail48 : Box := ⟨-35327034088792989699558723852504687994943098617967210967,22278132120194113188870093403387049094884195938833133120⟩
def resval4Tail52 : Box := ⟨-42806304185281570554456215596630600996825931899680665903,22599241289867191947354168877334281479772890928758340151⟩
def resval4Tail56 : Box := ⟨-51869049448001954286816592351214554368852494209220861670,22393133276754257049668147602908534060320562407263726253⟩
def resval4Tail60 : Box := ⟨-62850515638868066209258556905033993588472626317348318226,21467591380671126881253543964540684190861257035151849710⟩
def resval4Tail64 : Box := ⟨-76156925140329413679740766696961472009635122133833478279,19578790001035999459449769607273990202700373438119318922⟩
def resval4Tail68 : Box := ⟨-92280449674084057250163245601171500223923904365027058227,16418887747478633726732522572290952708181187088428318007⟩
def resval4Tail72 : Box := ⟨752947765299612020619465304280971868566667862401147179399,986313649220233916590529395813594272356755473382138436⟩
def resval4Tail76 : Box := ⟨-53888112336858529651096802603306180008958086301671397,128747773059205269612730834228243921826756420867430051⟩
def resval4Tail80 : Box := ⟨-65268743546634647803513439392973085111364246668147273,142071344889710322520506204222165310778126869583598922⟩
def resval4Tail84 : Box := ⟨-79087127260461078460825959822594491188393401783214036,156329110535048357722953808431818736646710368300611105⟩
def resval4Tail88 : Box := ⟨-95831074245202034394709485148054997784544334948488657,171463136673688859445134425285544495177734083084226033⟩
def resval4Tail92 : Box := ⟨-116119969319578813503322748954388758190341581829352372,187368846320222896376513459004353527567074423368712354⟩
def resval4Tail96 : Box := ⟨-140704331877561396200080682911552214797733437261419030,203880239938694761489976127607919949370228092547223146⟩
def resval4Tail100 : Box := ⟨-170493577677624139367277836299070515325937478260021598,220751572109768476944555658334773850599182994894840289⟩
def resval4Tail104 : Box := ⟨-206589659617662701210291594440159879189009107420818256,237634428609313187820968373581246023511202997891224255⟩
def resval4Tail108 : Box := ⟨-250327830774021206317092490548362626244112819975091472,254049132539958085775360888291065397184505262289526674⟩
def resval4Tail112 : Box := ⟨-303326037595491741307663258986342823372563256965574698,269349168148523987824883739792210273620677468580010820⟩
def resval4Tail116 : Box := ⟨-367544770387272652501866005020207020354136564277146430,282677018330295261160040976785581120088360339911183317⟩
def resval4Tail120 : Box := ⟨-445359585052123373543619054613685631608639862995510863,292909455203931976214407681706321119073004095100608325⟩
def resval4Tail124 : Box := ⟨-539648978786470616559766343551382691725601567509881666,298589888716849280934832419133555031005655957896156059⟩
def resval4Tail128 : Box := ⟨-653900870397113188397662274714250247693113763095513485,297844849225029894251829134317052337405068924005278328⟩
def resval4Tail132 : Box := ⟨-792341624119510069021113742919780185321028280264260578,288281036002474929811507619460169587479605472267688140⟩
def resval4Tail136 : Box := ⟨-960092389748065665088032403391402789605442010621078984,266858579928981566634960596709458893896601354636394001⟩
def resval4Tail140 : Box := ⟨-1163358613360316959725027075972360957840332133557157513,229735209104744785540633525285021126158097315979863580⟩
def resval4Tail144 : Box := ⟨-1452637924139392159222718774013071168361939936681561691,169388968830847520397688514863677277485603947846862965⟩
def resval4Tail148 : Box := ⟨15667902006567356996599502706739965488747835207,33307522974186651087908651766496570831136888131⟩
def resval4Tail152 : Box := ⟨18923633089517830743839631179058039184839626061,36625523551815777701311106961287903575349229729⟩
def resval4Tail156 : Box := ⟨22930052861497218280835382186167217207633574505,40141075567787995879779160676076646794241052703⟩
def resval4Tail160 : Box := ⟨27784693594614281845591015971790462376917849662,43826966090016097281767734002557648370505407971⟩
def resval4Tail164 : Box := ⟨33667135562993526595634026325379120083034140920,47641538160149283284614370807393287857223371801⟩
def resval4Tail168 : Box := ⟨40794979910691157282499133785945918163123957547,51523791246562649058718012012587641338826043803⟩
def resval4Tail172 : Box := ⟨49431897251840914127988670915773290351227769782,55387860809955804290384423344402641412070815254⟩
def resval4Tail176 : Box := ⟨59897381277449409821217301953660796580457443824,59116136151397964315227377016623319741127346979⟩
def resval4Tail180 : Box := ⟨72578567349294613280575224619519644428640525923,62550702100421272099628322599721201073493592622⟩
def resval4Tail184 : Box := ⟨87944553269798719676477774705513611294285175638,65482720005530465288855016050086415672291083885⟩
def resval4Tail188 : Box := ⟨106563751976562449080298844119089751202515320400,67639278059518566353263828319950876927630705652⟩
def resval4Tail192 : Box := ⟨129124918066097620629607195627596699662683920615,68667136931150613941748595651848739573863802701⟩
def resval4Tail196 : Box := ⟨156462625952242414056680672942325025694647210243,68112669965007507514072757884382324623887050264⟩
def resval4Tail200 : Box := ⟨189588142137987621580768971288220241909238439030,65397142973803289452484481695236048991440973139⟩
def resval4Tail204 : Box := ⟨229726833616514915684666294386105332449825359498,59786290959300130251253687976087508858289641043⟩
def resval4Tail208 : Box := ⟨278363496199363107484757818259334983029259190147,50352920769194043120072445511343981491316930279⟩
def resval4Tail212 : Box := ⟨337297279569424688305532353361045383718493240682,35930990998554869959002812678355527992051793058⟩
def resval4Tail216 : Box := ⟨408709565461882934940735635138604435170890378405,15059174060175776809492378543845562401688679749⟩
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
def polyval4Tail5 : Box := ⟨1014865775771038185720317124842806939479059168818990963900,2051677650616962903793701995424345010006980710176909701384⟩
def polyval4Tail9 : Box := ⟨1229726014013757375750095810819369812035172099307227651101,2252059306567682430279159576797652175101675829224996902070⟩
def polyval4Tail13 : Box := ⟨1490077703126843050958682494755385435194759933853055190727,2463180018286391972102694706057843483483918436295757591601⟩
def polyval4Tail17 : Box := ⟨1805549802438213648215410453190395098519396479251855872148,2683022919230786044946218544914339127153708043582117353383⟩
def polyval4Tail21 : Box := ⟨2187812140429984040584214409358922107303639441247606803145,2908563177723899422799563362718849636016216715631505932087⟩
def polyval4Tail25 : Box := ⟨2651005225859243584930011389580318273401336505092960388953,3135475910583269906382362085925305857741575187697682854500⟩
def polyval4Tail29 : Box := ⟨3212263328126425488991107095040488060185242952122645915275,3357771618698113451137503490727990366192839654987912247118⟩
def polyval4Tail33 : Box := ⟨3892348301909282053474077762129342110608904449753349641181,3567342343351072333349115115674848735020497689604840965459⟩
def polyval4Tail37 : Box := ⟨4716417602106310293180132581965671566851662500246460790995,3753398003650918141815573478072539279281153899159447825411⟩
def polyval4Tail41 : Box := ⟨5714954899217723412518331095382129041536113035385196887130,3901767805108969281479637233752897935283489868554861179250⟩
def polyval4Tail45 : Box := ⟨6924897720148164110804799960158192412554236940409201972743,3994036041414449103516190251028776800900161598395963317429⟩
def polyval4Tail49 : Box := ⟨8391003827707778912870486154035680254527242586328610632631,4006474830562340243962084155307018896694158319965727924316⟩
def polyval4Tail53 : Box := ⟨10167506883422985408313055982948382879650105072149599325682,3908728071249673324296915234496444516600808396535486070880⟩
def polyval4Tail57 : Box := ⟨12320122639330774201381306956185597691268517985665411455340,3662190858500718345233051192130812951856157911665769570388⟩
def polyval4Tail61 : Box := ⟨14928479871070495730690573768454215767289806824204991870326,3218016373521841998930264682452347503065073467662446411486⟩
def polyval4Tail65 : Box := ⟨18089065976468118268088267587969823425436707112498128095484,2514667394158835155762553299759949888175883221053962809105⟩
def polyval4Tail69 : Box := ⟨21918796254126755608453996029061470394231794993509708495300,1474911487181361889945761795612702614351411207465588688688⟩
def polyval4Tail73 : Box := ⟨26593750000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨91944533206491798868910609652914475476353643805925745065,15127961900954702973030953541770907451888372438877161753⟩
def polyval5 : Box := ⟨8540240707946050646537717911227725687974473066077186670051,3735124239355850780271530398787356480337543090664316802545⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-18163609143818786498309209919097526564307251463800198605,15293491831696796354384870364732176467186148751113087681⟩
def resval5Tail8 : Box := ⟨-19971154830160019891146667320784984558855261959983938460,15661374446219819983020606974736244066657425613770673657⟩
def resval5Tail12 : Box := ⟨-21958516961992733156879119012761725252373614859065500056,15990833664053033929631170560212806477849942223503765293⟩
def resval5Tail16 : Box := ⟨-24143644728432602030764386094380702355447639919193546361,16273166594402501121966539732613923882879620121803244749⟩
def resval5Tail20 : Box := ⟨-26546218115804390051467282539083268910219766253556987645,16498487802940062115136162972712341089503577586757855351⟩
def resval5Tail24 : Box := ⟨-29187875491804824798867850169221247159445807772058805090,16655590308386905882035465847186054388426941635116114950⟩
def resval5Tail28 : Box := ⟨-32092408493317539470236851029030259641247125178274256485,16731792107346012426402415567708338611404165773322685726⟩
def resval5Tail32 : Box := ⟨-35285976301739895441988300978901872044846681743037281359,16712765998495733498157840747887072207747545316534480078⟩
def resval5Tail36 : Box := ⟨-38797341241191392978469475967896608731992980902594009313,16582350951240874048998061528964039453136152269400855485⟩
def resval5Tail40 : Box := ⟨-42658127821483284715287831654165451847627493653259631101,16322343083380233279093069299924000876520435508393906330⟩
def resval5Tail44 : Box := ⟨-46903107558875759119755710335722877116434003439069408835,15912264113320388125492049039341846825569095080097315200⟩
def resval5Tail48 : Box := ⟨-51570512139812295662638407120927538468218502753640195229,15329104933112340958449257931313104233435372086186103527⟩
def resval5Tail52 : Box := ⟨-56702377748086986002962744226218701137863599541421642582,14547041707070960402175270491399341084608893372769572445⟩
def resval5Tail56 : Box := ⟨-62344923656568755917783336387331327147326665846969257666,13537121634712486421729684896100562171664212028098728780⟩
def resval5Tail60 : Box := ⟨-68548968493202316614298098852687572070609424847007164754,12266915223742881942488974684069858183966179888677090955⟩
def resval5Tail64 : Box := ⟨-75370387927303149889669356868322983645902919429034001133,10700131595900673988913569286666409803651976060547058688⟩
def resval5Tail68 : Box := ⟨-82870565013623207260316461916788893246997941794556723743,8796189963860860201942119125651999386068030035639614198⟩
def resval5Tail72 : Box := ⟨752945829031480630949517969377075590254667072877868838056,1007447535432536537308406892470956070539713162269660506⟩
def resval5Tail76 : Box := ⟨-234169405387800061934612563071072703381684746472701329,200318559962011518461198497257324251161138822939910726⟩
def resval5Tail80 : Box := ⟨-257446337721188448151452896944351071180845471587504392,205266919931178817408693479314211856946213204821514089⟩
def resval5Tail84 : Box := ⟨-283065240588988438749267962281110618661307146085910050,209733557687558853408052960624626541676280210186973483⟩
def resval5Tail88 : Box := ⟨-311233523446152231935799177976540248086499419849910680,213606973728687606047891257600488621795498765176180949⟩
def resval5Tail92 : Box := ⟨-342204877982737069052358163383641082989725420064972364,216760664219116401519021858263984922150692176147958026⟩
def resval5Tail96 : Box := ⟨-376258242423686683490487283139071814551330727045508856,219051149764715931202878688908210110555264780274856197⟩
def resval5Tail100 : Box := ⟨-413700312591404564444389313297149819651358580447233186,220316000886013640004331566921341386365087350430747248⟩
def resval5Tail104 : Box := ⟨-454868304108815261413493250762073889575095228563302376,220371648477517957968589758048024511434442655212640079⟩
def resval5Tail108 : Box := ⟨-500132989474392057104340511257025996667522427503087059,219010956630132106288279981853002123402000439034975920⟩
def resval5Tail112 : Box := ⟨-549902037361465885374816132489584589579623888280483973,216000532884722146604997895363930411114318725335987381⟩
def resval5Tail116 : Box := ⟨-604623684216644123730110821929199203672748402176143267,211077748420399146368682191025367513051735898369232924⟩
def resval5Tail120 : Box := ⟨-664790771224964579954617145861264752537679186880140067,203947437855926596267818037880881530119176073426607690⟩
def resval5Tail124 : Box := ⟨-730945183000023227613615971889873424061767626553658109,194278245230597843982328028581953493736452412767361555⟩
def resval5Tail128 : Box := ⟨-803682727975381788510075037158326405878268129817346360,181698579303016739740962201304159262032570479578091090⟩
def resval5Tail132 : Box := ⟨-883658504451677290650394277631613005373691343402375474,165792137530626168952191874628085636791922744009359307⟩
def resval5Tail136 : Box := ⟨-971592800636109738043851878141271206674027995287614896,146092953933737526993862329080755292838019739798233010⟩
def resval5Tail140 : Box := ⟨-1068277651239966763156902146595233934886753228044805678,122079916063475325170261164929764810838008380568303105⟩
def resval5Tail144 : Box := ⟨-1216548752613357896553109484831708126596207410759522405,90871092167574904696072564134796225356324224723011744⟩
def resval5Tail148 : Box := ⟨85598180127958388414801068414547412740263039177,64422242423178339417992680394887205297419985559⟩
def resval5Tail152 : Box := ⟨94060527722471188972605838158747100558882777224,65659746459197972268329727280255813788410983010⟩
def resval5Tail156 : Box := ⟨103420643042893612116180841165512330061520178176,66684616884193637569281241220960046341885804530⟩
def resval5Tail160 : Box := ⟨113712199577470802280130341843931661661390715648,67453277092520948732300010866897515911783503471⟩
def resval5Tail164 : Box := ⟨125027885655413884612958233132090130817604981180,67916941278100756185544318101144742890653019590⟩
def resval5Tail168 : Box := ⟨137469614074375718396190047638130356267104275534,68020454589299175966937971840148910298652077001⟩
def resval5Tail172 : Box := ⟨151149439140655365618962509796135154853552009302,67701560860252721168704110301946738691337534058⟩
def resval5Tail176 : Box := ⟨166190565866971427668932090255111606278365272604,66890091085790352681151514702283235235359812025⟩
def resval5Tail180 : Box := ⟨182728459597408299111315660913293596333389260058,65507064322087609338748924494493095872049995728⟩
def resval5Tail184 : Box := ⟨200912066052947448586742477351313515204712396607,63463691855076920113339561844371867496478741260⟩
def resval5Tail188 : Box := ⟨220905152785715480598253332154713614662990684641,60660274538495692586597058952819600059213231177⟩
def resval5Tail192 : Box := ⟨242887784123528008993879125938671265228736309295,56984982167875421900229056717156572311003875928⟩
def resval5Tail196 : Box := ⟨267057942888565970635681339935442021658272976672,52312502616148622597796861675440585293534919076⟩
def resval5Tail200 : Box := ⟨293633313495917213993070963058459898122763039568,46502547200292581245158437065804270978397488303⟩
def resval5Tail204 : Box := ⟨322853242491156470919298373522278008950761351301,39398197364894874964679378366934733758951573400⟩
def resval5Tail208 : Box := ⟨354980894184222000570998334747525290970625520560,30824076244901417966002471199061865558006103464⟩
def resval5Tail212 : Box := ⟨390305620822065513007213387065873313211301756316,20584326989431032052019503375742995318303407690⟩
def resval5Tail216 : Box := ⟨429146862911906441646320928298366797791181065480,8460281215062024968703329135828923127188629039⟩
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
def polyval5Tail5 : Box := ⟨5294605969895400938114306335601733325798926199713388078319,3808291425046029709352085356914832760150108924893351158934⟩
def polyval5Tail9 : Box := ⟨5821478769454324674999617409234726009229240613070163654911,3873285547740454264707624756207896333909128345580581866515⟩
def polyval5Tail13 : Box := ⟨6400783597683941344132183298856061610219881349095995529412,3924332741767851665692766474218261939761632313043810661818⟩
def polyval5Tail17 : Box := ⟨7037735992531261160885367139373623582713918817578024290540,3958717756837508900938119697633115028671242295795572047852⟩
def polyval5Tail21 : Box := ⟨7738072557005789522554010855267300333773860299995906485573,3973368853099251200243083598620348118173478040568562893032⟩
def polyval5Tail25 : Box := ⟨8508100753002230186169205045961639398396774622271353963878,3964816700972095708733300239741074327940373479183939550301⟩
def polyval5Tail29 : Box := ⟨9354755708215693430819727170349151552921351555739954944173,3929148839983043555258867178154559217171253360273718832361⟩
def polyval5Tail33 : Box := ⟨10285662676187064780619404583055464293639252800600910262568,3861959217151757129906302882039265457989365863912904433252⟩
def polyval5Tail37 : Box := ⟨11309205711849287990013037094007855134448526058315562478829,3758292290010449768392763231197308251046173783817476536418⟩
def polyval5Tail41 : Box := ⟨12434603181089047449085954772672726712891457091258538048307,3612581126468701349766864515680592570459459564255420027874⟩
def polyval5Tail45 : Box := ⟨13671990784387846261152264376671585239254084296917074066970,3418578875481608381192023437535222839178395009800800878120⟩
def polyval5Tail49 : Box := ⟨15032512842280751890334804428092942978285763547902175211383,3169282918317929991573711989235823927838509469227681507505⟩
def polyval5Tail53 : Box := ⟨16528422664779733867860310611991966029217128989789880340961,2856850939557150814005559378710225028481064186445706824732⟩
def polyval5Tail57 : Box := ⟨18173192908721696800749644370511890907546100550410712357898,2472508079115348659872129508048352080573703880300042081054⟩
def polyval5Tail61 : Box := ⟨19981636916955859375415133411488123233643842328145049904154,2006444240888406997477344845027927907342758920337624833044⟩
def polyval5Tail65 : Box := ⟨21970042132197194762124801131726534062322969217212956320750,1447700539213565770712163052710604212735551326324440327528⟩
def polyval5Tail69 : Box := ⟨24156316837967202669771379416583730408353436218260214409550,784043756614516780629448120720968776183649483799699135096⟩
def polyval5Tail73 : Box := ⟨26593750000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨73669432422783466658906305288992042112522545672325237929,13844272956783232599287423481657749958478250375473777242⟩
def polyval6 : Box := ⟨15091050846096318516119023668487957959189946419522666139622,3738099578245199591306103834676389684152947139536851271695⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-36467951507186848194109912233725117546878231560273539224,13476183116356128352245559336335496536431051090157638780⟩
def resval6Tail8 : Box := ⟨-38228718899671474583601351745523243158167218668342879116,13307187587944818481273990941061931657527546774743532306⟩
def resval6Tail12 : Box := ⟨-40074445424503296460256284909304030506923194620219582538,13103911456719247044955723973174737258266054258720092323⟩
def resval6Tail16 : Box := ⟨-42009285743083511161306274855057893281405433215679197834,12863866453593509925524116267278630437146333773765706071⟩
def resval6Tail20 : Box := ⟨-44037542377686226282978518994371796417116337872029522499,12584418295616292700563478851308620910163257186457878215⟩
def resval6Tail24 : Box := ⟨-46163725575500897033234859416079076236575030700801815055,12262778136147842097652744483381400473410832900443230938⟩
def resval6Tail28 : Box := ⟨-48392563343634188033847314907870837212361227966934312207,11895994229697187268415207249203837998983148991090420615⟩
def resval6Tail32 : Box := ⟨-50729011962813993331788181242496773489972360763514692753,11480943166645933419066503398484051125350778892612340381⟩
def resval6Tail36 : Box := ⟨-53178267008702445451528522970592874959381054177001934709,11014320656080987358455373855528371862256142793436851913⟩
def resval6Tail40 : Box := ⟨-55745774905330576770795788943935947729440988620936872693,10492631834003776565249482862249713720352537079288489367⟩
def resval6Tail44 : Box := ⟨-58437245036346094885910511765512123874244937117254363675,9912181073056982435644043699718402139209271695365570625⟩
def resval6Tail48 : Box := ⟨-61258662441006130877198659458221497878949722498811713830,9269061268727797285711185479590227257626184693560707312⟩
def resval6Tail52 : Box := ⟨-64216301123147120264664337449214297081717125260258279633,8559142575746675576719938157609408468397331372812142598⟩
def resval6Tail56 : Box := ⟨-67316738002727050918160034761678570732502086165092730459,7778060567099650386704027228393096836671673231925445745⟩
def resval6Tail60 : Box := ⟨-70566867540962226584608706395198402914449498531705896510,6921203786707348639132858986800270801196252068378506921⟩
def resval6Tail64 : Box := ⟨-73973917068600584077870475636346025740986878179812267105,5983700665151979512806933954678099017486452351741557740⟩
def resval6Tail68 : Box := ⟨-77545410556652912427064569208542223753711274279609577251,4960402565103912894704943401452199149708834929830169022⟩
def resval6Tail72 : Box := ⟨752789707897086155151848138575655936580468619176907155702,963654189677838915974256400879370397845794964327900706⟩
def resval6Tail76 : Box := ⟨-474215828978930824112336305279595937456175397146180063,177406045641729671988086403914943903193276421511724671⟩
def resval6Tail80 : Box := ⟨-497087079520573957219381469732490259218386184096335476,175277742032139929889004819275453156106306333853002852⟩
def resval6Tail84 : Box := ⟨-521087014264241635496211804502120917873797244351528753,172706086622756118262264515501093817083177783732905171⟩
def resval6Tail88 : Box := ⟨-546245694664674928146102332698530985881584168241667609,169658606458684588718326094657203124241243254983917974⟩
def resval6Tail92 : Box := ⟨-572619065092881560571416589955303554766170515777777217,166101120668738302434604207822209775152946591174915932⟩
def resval6Tail96 : Box := ⟨-600265772179917635949801801949327942171340567649284499,161997440927459546119461694225600903699962229338889628⟩
def resval6Tail100 : Box := ⟨-629247294084257077131244203356515498528877983638078000,157309263129250814166339818052428881790769747759678474⟩
def resval6Tail104 : Box := ⟨-659628077200578392354606189256994946306815773967207463,151996053489848092937122141582451836971740333193423531⟩
def resval6Tail108 : Box := ⟨-691475679469621188180390349869035285527887671571551497,146014928774306575116138140261454991986467150687879493⟩
def resval6Tail112 : Box := ⟨-724860920607208875716613148691097510543399012889298775,139320530355973211787472679793251355335640937310283193⟩
def resval6Tail116 : Box := ⟨-759858039586501398179662929010356791771724566199716770,131864891796288158768587711573986489059622598417381917⟩
def resval6Tail120 : Box := ⟨-796544859723672255944281805920153067341372916318959191,123597299619890102041983067372032660697952224430268739⟩
def resval6Tail124 : Box := ⟨-835002961734111899968792623902623259746811525756679140,114464146943378874888601236757900349623965281437419128⟩
def resval6Tail128 : Box := ⟨-875317865143983716050561137178524328943680857269636152,104408779599175930173647431291758456283017151590757390⟩
def resval6Tail132 : Box := ⟨-917579218460547331138071965791920751336860378805902003,93371334378179462339198077305513576499162404648164531⟩
def resval6Tail136 : Box := ⟨-961880998532334418896478046038355649758700604812320280,81288568995529883197009508157517775671583744815357981⟩
def resval6Tail140 : Box := ⟨-1008321788207927019518790902773080021965846301180080605,68093678261441199451727860105898861066747941477639254⟩
def resval6Tail144 : Box := ⟨-1098480721369790064321327766408481013957875169516871509,51599177522685789939452550396321284613186677635391603⟩
def resval6Tail148 : Box := ⟨197242002120284943311865297821581755786137410260,63636497241162821693937712911311732052141012790⟩
def resval6Tail152 : Box := ⟨206712023495787516212973314975133912549025379039,62427936889216235430297719704813810112700410556⟩
def resval6Tail156 : Box := ⟨216692316889906072073341700831446447323167311704,61025138646501262515487393104995764468332383383⟩
def resval6Tail160 : Box := ⟨227154471187810948679593306201128546007473776908,59413845305050214976274019624273147900457039224⟩
def resval6Tail164 : Box := ⟨238121750328998996995093845058376761719668851377,57579504239275587780221620880409892725241216178⟩
def resval6Tail168 : Box := ⟨249618542321648304657003963374017469923284135677,55506717244267068762681338675670962175627680603⟩
def resval6Tail172 : Box := ⟨261670412655270772492876275886552941661944420550,53179195139244030943939748834656334759633262714⟩
def resval6Tail176 : Box := ⟨274304161150617657502826670429601944611959449213,50579710048334834310016340655770566576463652652⟩
def resval6Tail180 : Box := ⟨287547881554611145315178328221995337134042052773,47690045227574918867654754301748640904458784461⟩
def resval6Tail184 : Box := ⟨301431024012588149550235268097847591258285794412,44490942314870153985410014397958229210876707107⟩
def resval6Tail188 : Box := ⟨315984460556775899341010933447573123049075126889,40962045873575341415790677920224969550587091319⟩
def resval6Tail192 : Box := ⟨331240553756626452859428996764802231558434954765,37081845093935560266218352163586561893065370285⟩
def resval6Tail196 : Box := ⟨347233228683668322525195171447014172248309447152,32827612509921707457731339067527864727901654698⟩
def resval6Tail200 : Box := ⟨363998048350903910598001364351606189463032652143,28175339581945815211998787855332965791991237264⟩
def resval6Tail204 : Box := ⟨381572292794507847550063532281844874448624063861,23099668988550444519852322691573023256234174824⟩
def resval6Tail208 : Box := ⟨399995041973691352604667878646639983314507121534,17573823462411644839136728347940642076004337326⟩
def resval6Tail212 : Box := ⟨419307262700905534380921179988255492455537024146,11569530995416921090954304678121224049071605494⟩
def resval6Tail216 : Box := ⟨439553179392254486044998417679545419269225509684,5056855283679555796443149058766604043241845351⟩
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
def polyval6Tail5 : Box := ⟨11915569968639419533822908486886701504755602780642259242004,3667017948418205859702451637378880902549504693570249153161⟩
def polyval6Tail9 : Box := ⟨12490865430543561177321994014696156909897727116006189536184,3588337936157618300667870916542737173126160899197251087023⟩
def polyval6Tail13 : Box := ⟨13093938780304414335775648499903283588076541441930582435810,3497709124570353933970198197584896373435307011947121097893⟩
def polyval6Tail17 : Box := ⟨13726129205217822883604852645294854910092392662530163623588,3394294855858531908332130638069951929470220114348352772741⟩
def polyval6Tail21 : Box := ⟨14388842510989286420205633582078500537241420315189163416700,3277209813142207199283700998803657198247511636945844601697⟩
def polyval6Tail25 : Box := ⟨15083552377413814081932037768690329082788545160256970134319,3145517393614439744631224163251675356181074516732941643748⟩
def polyval6Tail29 : Box := ⟨15811803635242062311917694728383963868548869756875269675233,2998226960167300377133049444472043279979521424964861312519⟩
def polyval6Tail33 : Box := ⟨16575215701430188300897252043213813332911114278062378445857,2834290951650025564057908756594971883830299672135651555509⟩
def polyval6Tail37 : Box := ⟨17375486180247639965373893410905302627149229362171754930431,2652601844654710467500540638339106819770519914586889925016⟩
def polyval6Tail41 : Box := ⟨18214394638250572381539122264357195930239824771060256324407,2451988959375802685400586405152992051769968991080785174251⟩
def polyval6Tail45 : Box := ⟨19093806561515322728876189442887102788421619447667416204085,2231215101720694148063450619353116882186413111953030420599⟩
def polyval6Tail49 : Box := ⟨20015677503931668999598676422948031910646041829132721113659,1988973033461636849780483605052018704450109104387617088402⟩
def polyval6Tail53 : Box := ⟨20982057435780458590722456353208803287318923469713911293833,1723881761813148986758703108308382530384628158086294963534⟩
def polyval6Tail57 : Box := ⟨21995095302265566551188408574902452933783057548392443542620,1434482639393105401537766331863941514773474843462397705173⟩
def polyval6Tail61 : Box := ⟨23057043802137026109383000042179565582584689692577869052770,1119235265078848012204440722196144224196755945603471494692⟩
def polyval6Tail65 : Box := ⟨24170264397037530954284457348559093759529642909701842901457,776513175800348782291756379704596829299883062532028778908⟩
def polyval6Tail69 : Box := ⟨25337232613005306151570634344230508748530951093008927706665,404599315240212055019523437929615595518734821907733013032⟩
def polyval6Tail73 : Box := ⟨26593750000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨51876125655115790913077552769488653036875813646630203285,22606876843678441271488433723905422400312601937382977230⟩
def polyval7 : Box := ⟨23762025891439572086524188309215382877882933197982515399996,6527923086138404092123817580234976335642008376568689192192⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-57470044062293100925102861234440001549623375216750782137,21483074346896758939414242472384114630768466659925663620⟩
def resval7Tail8 : Box := ⟨-58376902797953606794765945449709936509512393916630656435,20576265275777103093646797218932807929165322827891230655⟩
def resval7Tail12 : Box := ⟨-59298019587667249221524530490796354280258830937146209516,19655148491492483169613993124534596008263441930205616945⟩
def resval7Tail16 : Box := ⟨-60233670478466009759918563851637580729318378592729782028,18719497600698162494564774297250664228501205516282366847⟩
def resval7Tail20 : Box := ⟨-61184084806480045245281384006321376636256846523126608072,17769083272684142785290860802249111405322796772171845432⟩
def resval7Tail24 : Box := ⟨-62149495520862669786578170572044504103622049263829826865,16803672558301518429567902385312599792752017772502175989⟩
def resval7Tail28 : Box := ⟨-63130139246417932586398689834206435822059018530669673158,15823028832746255635732503568566999578293823329954421031⟩
def resval7Tail32 : Box := ⟨-64126256341602528731099819263124568956765494950717544684,14826911737561659491461004639345730540922962654136082625⟩
def resval7Tail36 : Box := ⟨-65138090957438329505665714910126029554127686338969967719,13815077121725858716923468012252496461033241031614176499⟩
def resval7Tail40 : Box := ⟨-66165891097354465161001680741830765582587485313938504519,12787276981809723061505645526179036556174752127960720052⟩
def resval7Tail44 : Box := ⟨-67209908677973643055906769808776418100486370015991878991,11743259401190545166156081568766689351308707356393957401⟩
def resval7Tail48 : Box := ⟨-68270399590857600230262237624489696262996943547562318825,10682768488306587987376669178808853611131555056451677461⟩
def resval7Tail52 : Box := ⟨-69347623765226824315706474711985317129683891812916728706,9605544313937363791828128243165900095697721119237423382⟩
def resval7Tail56 : Box := ⟨-70441845231669908849777372315181740281265646574365778475,8511322847494271086400232953392295409096814379117325837⟩
def resval7Tail60 : Box := ⟨-71553332186856186582406817543891166021759774961311352396,7399835892305765837245117920265786659206562053904057693⟩
def resval7Tail64 : Box := ⟨-72682357056308176480253750026431807629111759229717379799,6270811019642957855727255428206978858833330814430510702⟩
def resval7Tail68 : Box := ⟨-73829144646452084274989546042710960357028900631039221096,5123968325648914507879614144640956092132378020603964175⟩
def resval7Tail72 : Box := ⟨752559293865024687409340681976631877537278769453800249465,1076533073908601052352801378598156880109085466522851156⟩
def resval7Tail76 : Box := ⟨-749954569036407448063807485878510896133610208076720624,282453025643084255888350167144188830503236225401572071⟩
def resval7Tail80 : Box := ⟨-761764276333735019881854282558186178913192197383457501,270619822237939874196456186632216956049100479315041511⟩
def resval7Tail84 : Box := ⟨-773783992331023772165721842823335706869279856605470083,258600105074367285864661156201287333185372493212754961⟩
def resval7Tail88 : Box := ⟨-785993366045449462066868673754696282433460360984674422,246390731359335175394137807355243051311778399587282510⟩
def resval7Tail92 : Box := ⟨-798395388882170612314793410978283515129514568453541221,233988708522612488088244035654985888953851354616148304⟩
def resval7Tail96 : Box := ⟨-810993100610284831692999696531060422002291061937749772,221390996794498254798577123702313454394114276944696561⟩
def resval7Tail100 : Box := ⟨-823789588963357864318341010842329003121805218953883627,208594508441425221800391186728018819608674313327044405⟩
def resval7Tail104 : Box := ⟨-836787990395650818238022692564531248587522952416293273,195596107009132267854982247003321101307291525278199334⟩
def resval7Tail108 : Box := ⟨-849991490850872248131218070143130859131728405626252820,182392606553910837957929287021507510340488022224035548⟩
def resval7Tail112 : Box := ⟨-863403326543061651838214350560207136454738836885634586,168980770861721434250319400340931807296516057478128869⟩
def resval7Tail116 : Box := ⟨-877026784749794373973544956194460404090035725238992110,155357312654988712117618069640461319567239221892149095⟩
def resval7Tail120 : Box := ⟨-890865204617902321982311208555835855478657493502044858,141518892786880764139790461595749325095770391187447025⟩
def resval7Tail124 : Box := ⟨-904921977981907979371883340295277129920313696287431848,127462119422875107424101129901727719980858984539798447⟩
def resval7Tail128 : Box := ⟨-919200550195372358034313213405157405215950192866743960,113183547209410768138440970430692523003658797692407474⟩
def resval7Tail132 : Box := ⟨-933704420975369299694519363570854925829588513228550554,98679676429421662628701792523348114153394412525065028⟩
def resval7Tail136 : Box := ⟨-948437145268439428444213750391131360613264617689703589,83946952143782592242727153654575533334116149140540706⟩
def resval7Tail140 : Box := ⟨-963402402304544047439858904893732166658993873980585624,68981758259993564249604269678086463617204257716341746⟩
def resval7Tail144 : Box := ⟨-1019759970152543206339539622738146099774236872600402997,51681567491154182839152757323218580955886161221686469⟩
def resval7Tail148 : Box := ⟨342261183258379613559323709231227150858893026441,109457459672973511550262361288344823210789298593⟩
def resval7Tail152 : Box := ⟨347610260643714039394504157858654624144601648108,104057283989025225238295665676828051788938064816⟩
def resval7Tail156 : Box := ⟨353095128484550554565028265336125295157375551009,98572415315006348736200030795940177489958346531⟩
def resval7Tail160 : Box := ⟨358666541725407548726437792479281683840257853934,93001002073905689860843480222683550290727073708⟩
def resval7Tail164 : Box := ⟨364325865115917345514719293709048139393061835938,87341678683395501166521363204867313739273885147⟩
def resval7Tail168 : Box := ⟨370074485771470142764819507006023483633686737757,81593058027842701527261596505963729339753489785⟩
def resval7Tail172 : Box := ⟨375913812694696070159760169736151840503488841063,75753731104616774087512280821582434828763744206⟩
def resval7Tail176 : Box := ⟨381845277120579685123902805692448730751547529353,69822266678733159121129909473126186720134594965⟩
def resval7Tail180 : Box := ⟨387870332867259209869628383092642492103442462911,63797210932053634375144000285150703522095343356⟩
def resval7Tail184 : Box := ⟨393990456692361327456731727572558383403435940001,57677087106951516787988328840791978415935414846⟩
def resval7Tail188 : Box := ⟨400207148654958511226396057555955535278117810674,51460395144354333018347472566018049018926612118⟩
def resval7Tail192 : Box := ⟨406521932483237602301855430819609343094136729022,45145611316075241943242156736152004400377779673⟩
def resval7Tail196 : Box := ⟨412936355947969751701486856997781739836380438430,38731187851343092549097148827891811168926673468⟩
def resval7Tail200 : Box := ⟨419451991241873265769926398592963500952283368363,32215552557439578680918294661136693523635236382⟩
def resval7Tail204 : Box := ⟨426070435364962361919012412772548403052767985641,25597108434350504505018108333419898955740046593⟩
def resval7Tail208 : Box := ⟨432793310515986857990388546755384114602993493683,18874233283335548314978303332780448205251894031⟩
def resval7Tail212 : Box := ⟨439622264517690489228425363579216084733155096770,12045279306897323325766632820704199653988883772⟩
def resval7Tail216 : Box := ⟨446560241276799459798167996369665631448484953952,5108482532573681063262837771748386943223544261⟩
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
def polyval7Tail5 : Box := ⟨20354283262236138507967283385990469379976115624168941257389,6208185227028779849610764648481955574485655281186677557394⟩
def polyval7Tail9 : Box := ⟨20675447286870103061611716522547831278139788215830882380838,5887019319210857678962892485294374850991376438903380830484⟩
def polyval7Tail13 : Box := ⟨21001680790047535759594234261501579891368768046313252315848,5560785815865504447953759686631783969792929210602551458704⟩
def polyval7Tail17 : Box := ⟨21333061862737878668735625007962618254388796516693906782812,5229404743175040061645271179480231366133424397432397982023⟩
def polyval7Tail21 : Box := ⟨21669671727182451085151082051567710624648514680295699981649,4892794878730467254966324721092321836949346737037235241247⟩
def polyval7Tail25 : Box := ⟨22011592887378680779754437478492365864589080340803162193505,4550873718534237556125523084956596864806377499954853374371⟩
def polyval7Tail29 : Box := ⟨22358909149137214428048408728308916088990067133761378257197,4203557456775703907700412475895959842317001925858023149068⟩
def polyval7Tail33 : Box := ⟨22711705640622833842771570609383520060645383617339269393138,3850760965290084492967125852875572001360900798235614840059⟩
def polyval7Tail37 : Box := ⟨23070068833219601410344727607198074318204723290982963435515,3492397772693316925392337803513613985937109713129488633817⟩
def polyval7Tail41 : Box := ⟨23434086562725232599850192242193890133420755132827283170233,3128380043187685735886667758006874013863714818662641855431⟩
def polyval7Tail45 : Box := ⟨23803848050879889990050059743656068492576178711509635078403,2758618555033028345688432993351491446142429191579915001112⟩
def polyval7Tail49 : Box := ⟨24179443927234675577313060342257709609821810777318726228277,2383022678678242758444552639472943262055731863297454687626⟩
def polyval7Tail53 : Box := ⟨24560966251365181391992148300535861138670088530467905320017,2001500354547736944199575273872687224103762853421695265138⟩
def polyval7Tail57 : Box := ⟨24948508535435543053193448529274416804147281785765603311161,1613958070477375309529626752720485662197803341729962151961⟩
def polyval7Tail61 : Box := ⟨25342165767118532836391677929022688344297706793474542549285,1220300838794391033694183329387315480548714354414185477570⟩
def polyval7Tail65 : Box := ⟨25742034432883214289414649315929931011965005413320359138421,820432173035108669029045352047973008101144275959387145096⟩
def polyval7Tail69 : Box := ⟨26148212591583999641804572539401823744253413248396814040649,414254060745454497618922733381404168226935918635530375605⟩
def polyval7Tail73 : Box := ⟨26593750000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1030284666964464653321077760410275343705473194652647468211774,5282013113322857570245479175015508051746921903736380482⟩
def zend : Box := ⟨1003719032529364207999003906250000000000000000000000000000000,3590165151888315175781250000000000000000000000000000002⟩
def betaquot : Box := ⟨428744469930905484697039707385341824855517878573877411255123,394759614361117546671745062722706785181115547998500193⟩
def crit : Box := ⟨105598620275691715883470355914338868685317799305190609851,13675007810898206627780718122517335571640675543817228834⟩
def subsonic : Box := ⟨592881079186293145562538333423570279630398719173394513002,7558600691298985836731091716632387509235974065381146098⟩
def pendTail4 : Box := ⟨26560893094546438564586808750819966740295071311432432552593,1540431916860356052005344311313770434039454136277442223⟩
def pendTail8 : Box := ⟨26560926345983238708526000525806389494428844213474318914924,1540258602701362526891768160843648578693053081530044387⟩
def pendTail12 : Box := ⟨26560926347328403237962070178049254933789407112567848304556,1540258583908179049016133740404635729075048313808304253⟩
def pendTail16 : Box := ⟨26560926347329023441166161164936748279299704390093991979541,1540258583893535135527294651759701794689678977587113757⟩
def pendTail20 : Box := ⟨26560926347329024840646742360758110960188866382084501641574,1540258583893484240431889855428893621937316844273508711⟩
def pendTail24 : Box := ⟨26560926347329024851859683295289498623839338176642500744412,1540258583893483620680236145371872868527422003839328139⟩
def pendTail28 : Box := ⟨26560926347329024852122463035337789444467602282644863991373,1540258583893483597932181193775311864223916193667238688⟩
def pendTail32 : Box := ⟨26560926347329024852137929353365752379386831423267810814799,1540258583893483595634269648741474171642027264912813802⟩
def pendTail36 : Box := ⟨26560926347329024852139768598092105606289270447993255288408,1540258583893483595027753131988228950672493421524534130⟩
def pendTail40 : Box := ⟨26560926347329024852139815260193129452778530644706508750987,1540258583893483594619271846053264528164117237063964396⟩
def pendTail44 : Box := ⟨26560926347329024852138246301029240046860750439366661128141,1540258583893483593917656564815347658324565486331764464⟩
def pendTail48 : Box := ⟨26560926347329024852125181436873187369473758810647896318720,1540258583893483590775454057823714376878108240362738723⟩
def pendTail52 : Box := ⟨26560926347329024851903820615793843254061016240207219296555,1540258583893483552251033046788103308971760597203149677⟩
def pendTail56 : Box := ⟨26560926347329024841949850554213300496124152318065126909723,1540258583893482143739880817509862229394061507585376358⟩
def pendTail60 : Box := ⟨26560926347329023393980363238029704766567910242867454431436,1540258583893305693348749327413809737395204674813550072⟩
def pendTail64 : Box := ⟨26560926347328124448936692946465447590436076749237815547398,1540258583808726065815730287720088037199282746163977531⟩
def pendTail68 : Box := ⟨26560926343343152307298679207866506350854326246840183173171,1540258295021536410091185746547295256999206359099354547⟩
def pendTail72 : Box := ⟨26560396893234167878903228613544174410536189575576154851937,1511982793473080013316927247265910063685281548783173304⟩
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
end SepticProfile.ExteriorCertificates.C09

end
end

end OAI
