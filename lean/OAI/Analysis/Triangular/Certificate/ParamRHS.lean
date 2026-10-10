import OAI.Analysis.Triangular.Certificate.ParamInterval

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
def rhsPlusTableRow0 : Fin 8 → RI := ![⟨1874456087585338350570292911831758804106153791481581659431790,1874456087585338350570292911831758804106262149572695679595998⟩,⟨-791886840546457827717261766487251937317323882728293964008424,-791886840546457827717261766487251908072700273946820069026578⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩]
lemma rhsPlusTableRow0_calc (j : Fin 8) : rhsPlusBox 0 j = rhsPlusTableRow0 j := by
  revert j
  decide +kernel
def rhsPlusTableRow1 : Fin 8 → RI := ![⟨561973897773317740648608818680619254334178781616840649784489,561973897773317740648608818680619254334243741279123192255363⟩,⟨-250271701543505453454448791090305012853544068561128160160704,-250271701543505453454448791090304914713595166685245179068394⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩]
lemma rhsPlusTableRow1_calc (j : Fin 8) : rhsPlusBox 1 j = rhsPlusTableRow1 j := by
  revert j
  decide +kernel
def rhsPlusTableRow2 : Fin 8 → RI := ![⟨0,4⟩,⟨-18237250733434003640496825739255374539565914380627990004759,-18237250733434003640496825739255360847254951978029207854377⟩,⟨13579638705302215226590059801737535389302367201278493258175143,13579638705302215226590059801737535389303510602438686091632968⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩]
lemma rhsPlusTableRow2_calc (j : Fin 8) : rhsPlusBox 2 j = rhsPlusTableRow2 j := by
  revert j
  decide +kernel
def rhsPlusTableRow3 : Fin 8 → RI := ![⟨0,4⟩,⟨-169326312877590649891007097087058863936249646326846562533323,-169326312877590649891007097087058818576690066430882065576176⟩,⟨23119557865402894747844636724206319683690342698197126975826623,23119557865402894747844636724206319683693301089643897369978455⟩,⟨-13579638705302215226590059801737535389303510602438686091632964,-13579638705302215226590059801737535389302367201278493258175139⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩]
lemma rhsPlusTableRow3_calc (j : Fin 8) : rhsPlusBox 3 j = rhsPlusTableRow3 j := by
  revert j
  decide +kernel
def rhsPlusTableRow4 : Fin 8 → RI := ![⟨0,4⟩,⟨5156498132250989535156195502169660220036359023416553880220,5156498132250989535156195502169665526862152116117638474608⟩,⟨0,4⟩,⟨0,4⟩,⟨16694432693867460272613036027758482030952285631480513206525991,16694432693867460272613036027758482030953395543236286930261587⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩]
lemma rhsPlusTableRow4_calc (j : Fin 8) : rhsPlusBox 4 j = rhsPlusTableRow4 j := by
  revert j
  decide +kernel
def rhsPlusTableRow5 : Fin 8 → RI := ![⟨0,4⟩,⟨22756504449753060760971129249563838900133777152108942376915,22756504449753060760971129249563860119555443019686586040862⟩,⟨0,4⟩,⟨0,4⟩,⟨-22202865676981591280126265323976477328265401786512631278337981,-22202865676981591280126265323976477328262526089602442488170375⟩,⟨-16694432693867460272613036027758482030953395543236286930261583,-16694432693867460272613036027758482030952285631480513206525987⟩,⟨0,4⟩,⟨0,4⟩]
lemma rhsPlusTableRow5_calc (j : Fin 8) : rhsPlusBox 5 j = rhsPlusTableRow5 j := by
  revert j
  decide +kernel
def rhsPlusTableRow6 : Fin 8 → RI := ![⟨0,4⟩,⟨-117595715452103264028043496323669029766028321257604540047,-117595715452103264028043496323668923841770177450798209097⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨16555288516830855347972997338697702932368932792470320650261501,16555288516830855347972997338697702932369504183796023455900141⟩,⟨0,4⟩]
lemma rhsPlusTableRow6_calc (j : Fin 8) : rhsPlusBox 6 j = rhsPlusTableRow6 j := by
  revert j
  decide +kernel
def rhsPlusTableRow7 : Fin 8 → RI := ![⟨0,4⟩,⟨-29404890737555391624532723396911892982956483791454969802,-29404890737555391624532723396911490107036626586330906925⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨12793894392299767606603013637939229848621314311453231203851719,12793894392299767606603013637939229848621794570562709080136670⟩,⟨-16555288516830855347972997338697702932369504183796023455900137,-16555288516830855347972997338697702932368932792470320650261497⟩]
lemma rhsPlusTableRow7_calc (j : Fin 8) : rhsPlusBox 7 j = rhsPlusTableRow7 j := by
  revert j
  decide +kernel
def rhsPlusTableRow8 : Fin 8 → RI := ![⟨0,3⟩,⟨-14161368646876411825263828259605396135656776103879864677,-14161368646876411825263828259605370656949114883927935600⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsPlusTableRow8_calc (j : Fin 8) : rhsPlusBox 8 j = rhsPlusTableRow8 j := by
  revert j
  decide +kernel
def rhsPlusTableRow9 : Fin 8 → RI := ![⟨0,3⟩,⟨48658109850423137779720163102648641177497040217518896331,48658109850423137779720163102648726102948238732586202357⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsPlusTableRow9_calc (j : Fin 8) : rhsPlusBox 9 j = rhsPlusTableRow9 j := by
  revert j
  decide +kernel
def rhsPlusTableRow10 : Fin 8 → RI := ![⟨0,3⟩,⟨-866064556935212017717311504278910933528986846619607011,-866064556935212017717311504278902532506275274466502594⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsPlusTableRow10_calc (j : Fin 8) : rhsPlusBox 10 j = rhsPlusTableRow10 j := by
  revert j
  decide +kernel
def rhsPlusTableRow11 : Fin 8 → RI := ![⟨0,3⟩,⟨-10084402938649966990755679536537123179970132791391599231,-10084402938649966990755679536537094438721227603950472864⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsPlusTableRow11_calc (j : Fin 8) : rhsPlusBox 11 j = rhsPlusTableRow11 j := by
  revert j
  decide +kernel
def rhsPlusTableRow12 : Fin 8 → RI := ![⟨0,3⟩,⟨678489486441443849645465154620129865407085455173189260,678489486441443849645465154620133388074543266831996269⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsPlusTableRow12_calc (j : Fin 8) : rhsPlusBox 12 j = rhsPlusTableRow12 j := by
  revert j
  decide +kernel
def rhsPlusTableRow13 : Fin 8 → RI := ![⟨0,3⟩,⟨606398979550235099515397986722593475474322441158528681,606398979550235099515397986722605610437472930042105979⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsPlusTableRow13_calc (j : Fin 8) : rhsPlusBox 13 j = rhsPlusTableRow13 j := by
  revert j
  decide +kernel
def rhsPlusTableRow14 : Fin 8 → RI := ![⟨0,3⟩,⟨-5541246284173884064720658849882916513100465556579359,-5541246284173884064720658849882865872260329082319212⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsPlusTableRow14_calc (j : Fin 8) : rhsPlusBox 14 j = rhsPlusTableRow14 j := by
  revert j
  decide +kernel
def rhsPlusTableRow15 : Fin 8 → RI := ![⟨0,3⟩,⟨21780503350109283249490080573320501782310770033812801,21780503350109283249490080573320686807820666393657737⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsPlusTableRow15_calc (j : Fin 8) : rhsPlusBox 15 j = rhsPlusTableRow15 j := by
  revert j
  decide +kernel
def rhsPlusTableRow16 : Fin 8 → RI := ![⟨0,3⟩,⟨-242196331137455198322408323680282630504323497545100,-242196331137455198322408323680276724090703668020701⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsPlusTableRow16_calc (j : Fin 8) : rhsPlusBox 16 j = rhsPlusTableRow16 j := by
  revert j
  decide +kernel
def rhsPlusTableRow17 : Fin 8 → RI := ![⟨0,3⟩,⟨-1322670319984407916629287226643997731362671243382595,-1322670319984407916629287226643975757549641322032420⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsPlusTableRow17_calc (j : Fin 8) : rhsPlusBox 17 j = rhsPlusTableRow17 j := by
  revert j
  decide +kernel
def rhsPlusTableRow18 : Fin 8 → RI := ![⟨0,3⟩,⟨-61388454782416196798460909664239373375784406252275,-61388454782416196798460909664238058894167176055713⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsPlusTableRow18_calc (j : Fin 8) : rhsPlusBox 18 j = rhsPlusTableRow18 j := by
  revert j
  decide +kernel
def rhsPlusTableRow19 : Fin 8 → RI := ![⟨0,3⟩,⟨81191344668734640112990239726836010545630862295641,81191344668734640112990239726840147684908547515557⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsPlusTableRow19_calc (j : Fin 8) : rhsPlusBox 19 j = rhsPlusTableRow19 j := by
  revert j
  decide +kernel
def rhsPlusTable : Fin 20 → Fin 8 → RI := ![rhsPlusTableRow0,rhsPlusTableRow1,rhsPlusTableRow2,rhsPlusTableRow3,rhsPlusTableRow4,rhsPlusTableRow5,rhsPlusTableRow6,rhsPlusTableRow7,rhsPlusTableRow8,rhsPlusTableRow9,rhsPlusTableRow10,rhsPlusTableRow11,rhsPlusTableRow12,rhsPlusTableRow13,rhsPlusTableRow14,rhsPlusTableRow15,rhsPlusTableRow16,rhsPlusTableRow17,rhsPlusTableRow18,rhsPlusTableRow19]
lemma rhsPlusTable_calc (i : Fin 20) (j : Fin 8) : rhsPlusBox i j = rhsPlusTable i j := by
  fin_cases i
  · exact rhsPlusTableRow0_calc j
  · exact rhsPlusTableRow1_calc j
  · exact rhsPlusTableRow2_calc j
  · exact rhsPlusTableRow3_calc j
  · exact rhsPlusTableRow4_calc j
  · exact rhsPlusTableRow5_calc j
  · exact rhsPlusTableRow6_calc j
  · exact rhsPlusTableRow7_calc j
  · exact rhsPlusTableRow8_calc j
  · exact rhsPlusTableRow9_calc j
  · exact rhsPlusTableRow10_calc j
  · exact rhsPlusTableRow11_calc j
  · exact rhsPlusTableRow12_calc j
  · exact rhsPlusTableRow13_calc j
  · exact rhsPlusTableRow14_calc j
  · exact rhsPlusTableRow15_calc j
  · exact rhsPlusTableRow16_calc j
  · exact rhsPlusTableRow17_calc j
  · exact rhsPlusTableRow18_calc j
  · exact rhsPlusTableRow19_calc j
lemma rhsPlusTable_mem (i : Fin 20) (j : Fin 8) : (rhsPlusTable i j).Mem ((Yf+Construction.R0*(gamma 1+gamma 0)) i j) := by
  rw [← rhsPlusTable_calc]
  exact rhsPlusBox_mem i j
def rhsMinusTableRow0 : Fin 8 → RI := ![⟨1874456087585338350570292911831758804106153791481581659431790,1874456087585338350570292911831758804106262149572695679595998⟩,⟨3800510165282262322258459079662541176708724756910040726396,3800510165282262322258459079662541176730295556369595812238⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩]
lemma rhsMinusTableRow0_calc (j : Fin 8) : rhsMinusBox 0 j = rhsMinusTableRow0 j := by
  revert j
  decide +kernel
def rhsMinusTableRow1 : Fin 8 → RI := ![⟨561973897773317740648608818680619254334178781616840649784489,561973897773317740648608818680619254334243741279123192255363⟩,⟨-1871079386855962384913401297548939417519015300278098369966479,-1871079386855962384913401297548939417518755299779619568913209⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩]
lemma rhsMinusTableRow1_calc (j : Fin 8) : rhsMinusBox 1 j = rhsMinusTableRow1 j := by
  revert j
  decide +kernel
def rhsMinusTableRow2 : Fin 8 → RI := ![⟨0,4⟩,⟨32298687622280709990851182301646460640599555784330561537103,32298687622280709990851182301646460640624089521277919177400⟩,⟨13579638705302215226590059801737535389302367201278493258175143,13579638705302215226590059801737535389303510602438686091632968⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩]
lemma rhsMinusTableRow2_calc (j : Fin 8) : rhsMinusBox 2 j = rhsMinusTableRow2 j := by
  revert j
  decide +kernel
def rhsMinusTableRow3 : Fin 8 → RI := ![⟨0,4⟩,⟨88281906839232413390666577025539590651677053747313876301865,88281906839232413390666577025539590651848902814068400484909⟩,⟨23119557865402894747844636724206319683690342698197126975826623,23119557865402894747844636724206319683693301089643897369978455⟩,⟨-13579638705302215226590059801737535389303510602438686091632964,-13579638705302215226590059801737535389302367201278493258175139⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩]
lemma rhsMinusTableRow3_calc (j : Fin 8) : rhsMinusBox 3 j = rhsMinusTableRow3 j := by
  revert j
  decide +kernel
def rhsMinusTableRow4 : Fin 8 → RI := ![⟨0,4⟩,⟨-28267994688546660485407508871694824140623172721543163089282,-28267994688546660485407508871694824140613970884994270402676⟩,⟨0,4⟩,⟨0,4⟩,⟨16694432693867460272613036027758482030952285631480513206525991,16694432693867460272613036027758482030953395543236286930261587⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩]
lemma rhsMinusTableRow4_calc (j : Fin 8) : rhsMinusBox 4 j = rhsMinusTableRow4 j := by
  revert j
  decide +kernel
def rhsMinusTableRow5 : Fin 8 → RI := ![⟨0,4⟩,⟨106868635310709889166732321991480152333396950299700409162860,106868635310709889166732321991480152333467326256028532411470⟩,⟨0,4⟩,⟨0,4⟩,⟨-22202865676981591280126265323976477328265401786512631278337981,-22202865676981591280126265323976477328262526089602442488170375⟩,⟨-16694432693867460272613036027758482030953395543236286930261583,-16694432693867460272613036027758482030952285631480513206525987⟩,⟨0,4⟩,⟨0,4⟩]
lemma rhsMinusTableRow5_calc (j : Fin 8) : rhsMinusBox 5 j = rhsMinusTableRow5 j := by
  revert j
  decide +kernel
def rhsMinusTableRow6 : Fin 8 → RI := ![⟨0,4⟩,⟨-7234947148275458062642027223080526693864268565711158195726,-7234947148275458062642027223080526693864157168542168372771⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨16555288516830855347972997338697702932368932792470320650261501,16555288516830855347972997338697702932369504183796023455900141⟩,⟨0,4⟩]
lemma rhsMinusTableRow6_calc (j : Fin 8) : rhsMinusBox 6 j = rhsMinusTableRow6 j := by
  revert j
  decide +kernel
def rhsMinusTableRow7 : Fin 8 → RI := ![⟨0,4⟩,⟨12841934272106857530937290901480783425456784008202733457126,12841934272106857530937290901480783425457199118225049012963⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨0,4⟩,⟨12793894392299767606603013637939229848621314311453231203851719,12793894392299767606603013637939229848621794570562709080136670⟩,⟨-16555288516830855347972997338697702932369504183796023455900137,-16555288516830855347972997338697702932368932792470320650261497⟩]
lemma rhsMinusTableRow7_calc (j : Fin 8) : rhsMinusBox 7 j = rhsMinusTableRow7 j := by
  revert j
  decide +kernel
def rhsMinusTableRow8 : Fin 8 → RI := ![⟨0,3⟩,⟨6297752757445065626459474264305459413090904494770990068929,6297752757445065626459474264305459413090938991820012428757⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsMinusTableRow8_calc (j : Fin 8) : rhsMinusBox 8 j = rhsMinusTableRow8 j := by
  revert j
  decide +kernel
def rhsMinusTableRow9 : Fin 8 → RI := ![⟨0,3⟩,⟨7519050541546144040317772025475080705789468527006476842416,7519050541546144040317772025475080705789633905782515434443⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsMinusTableRow9_calc (j : Fin 8) : rhsMinusBox 9 j = rhsMinusTableRow9 j := by
  revert j
  decide +kernel
def rhsMinusTableRow10 : Fin 8 → RI := ![⟨0,3⟩,⟨13330763399432416902771460277347667500538198574829617287533,13330763399432416902771460277347667500538322462674276340395⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsMinusTableRow10_calc (j : Fin 8) : rhsMinusBox 10 j = rhsMinusTableRow10 j := by
  revert j
  decide +kernel
def rhsMinusTableRow11 : Fin 8 → RI := ![⟨0,3⟩,⟨12190911551380191881788561565169501321963919210555605989272,12190911551380191881788561565169501321964597492385241151826⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsMinusTableRow11_calc (j : Fin 8) : rhsMinusBox 11 j = rhsMinusTableRow11 j := by
  revert j
  decide +kernel
def rhsMinusTableRow12 : Fin 8 → RI := ![⟨0,3⟩,⟨-2614594628346643569837666170574498402485896795895652666701,-2614594628346643569837666170574498402485836711283028534835⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsMinusTableRow12_calc (j : Fin 8) : rhsMinusBox 12 j = rhsMinusTableRow12 j := by
  revert j
  decide +kernel
def rhsMinusTableRow13 : Fin 8 → RI := ![⟨0,3⟩,⟨47416265186631222392752187825280969532085989419846286270364,47416265186631222392752187825280969532086462649610979995513⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsMinusTableRow13_calc (j : Fin 8) : rhsMinusBox 13 j = rhsMinusTableRow13 j := by
  revert j
  decide +kernel
def rhsMinusTableRow14 : Fin 8 → RI := ![⟨0,3⟩,⟨127985850114211739748205125064025577081636368035293151673,127985850114211739748205125064025577081636592591373167215⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsMinusTableRow14_calc (j : Fin 8) : rhsMinusBox 14 j = rhsMinusTableRow14 j := by
  revert j
  decide +kernel
def rhsMinusTableRow15 : Fin 8 → RI := ![⟨0,3⟩,⟨3050603057555462399132639579408736584554558738439309507917,3050603057555462399132639579408736584554560584703907882762⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsMinusTableRow15_calc (j : Fin 8) : rhsMinusBox 15 j = rhsMinusTableRow15 j := by
  revert j
  decide +kernel
def rhsMinusTableRow16 : Fin 8 → RI := ![⟨0,3⟩,⟨258391711635444201049532658285191228798640070817137966727,258391711635444201049532658285191228798640192546992384573⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsMinusTableRow16_calc (j : Fin 8) : rhsMinusBox 16 j = rhsMinusTableRow16 j := by
  revert j
  decide +kernel
def rhsMinusTableRow17 : Fin 8 → RI := ![⟨0,3⟩,⟨1764409646795333172805051773694276725308271097823259265427,1764409646795333172805051773694276725308272097740979488536⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsMinusTableRow17_calc (j : Fin 8) : rhsMinusBox 17 j = rhsMinusTableRow17 j := by
  revert j
  decide +kernel
def rhsMinusTableRow18 : Fin 8 → RI := ![⟨0,3⟩,⟨61184842643293630433407730629952597930545038076115326901,61184842643293630433407730629952597930545106423504287423⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsMinusTableRow18_calc (j : Fin 8) : rhsMinusBox 18 j = rhsMinusTableRow18 j := by
  revert j
  decide +kernel
def rhsMinusTableRow19 : Fin 8 → RI := ![⟨0,3⟩,⟨-1230482993355089794580253355339900524326004622452759641840,-1230482993355089794580253355339900524326004213985555240154⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩,⟨0,3⟩]
lemma rhsMinusTableRow19_calc (j : Fin 8) : rhsMinusBox 19 j = rhsMinusTableRow19 j := by
  revert j
  decide +kernel
def rhsMinusTable : Fin 20 → Fin 8 → RI := ![rhsMinusTableRow0,rhsMinusTableRow1,rhsMinusTableRow2,rhsMinusTableRow3,rhsMinusTableRow4,rhsMinusTableRow5,rhsMinusTableRow6,rhsMinusTableRow7,rhsMinusTableRow8,rhsMinusTableRow9,rhsMinusTableRow10,rhsMinusTableRow11,rhsMinusTableRow12,rhsMinusTableRow13,rhsMinusTableRow14,rhsMinusTableRow15,rhsMinusTableRow16,rhsMinusTableRow17,rhsMinusTableRow18,rhsMinusTableRow19]
lemma rhsMinusTable_calc (i : Fin 20) (j : Fin 8) : rhsMinusBox i j = rhsMinusTable i j := by
  fin_cases i
  · exact rhsMinusTableRow0_calc j
  · exact rhsMinusTableRow1_calc j
  · exact rhsMinusTableRow2_calc j
  · exact rhsMinusTableRow3_calc j
  · exact rhsMinusTableRow4_calc j
  · exact rhsMinusTableRow5_calc j
  · exact rhsMinusTableRow6_calc j
  · exact rhsMinusTableRow7_calc j
  · exact rhsMinusTableRow8_calc j
  · exact rhsMinusTableRow9_calc j
  · exact rhsMinusTableRow10_calc j
  · exact rhsMinusTableRow11_calc j
  · exact rhsMinusTableRow12_calc j
  · exact rhsMinusTableRow13_calc j
  · exact rhsMinusTableRow14_calc j
  · exact rhsMinusTableRow15_calc j
  · exact rhsMinusTableRow16_calc j
  · exact rhsMinusTableRow17_calc j
  · exact rhsMinusTableRow18_calc j
  · exact rhsMinusTableRow19_calc j
lemma rhsMinusTable_mem (i : Fin 20) (j : Fin 8) : (rhsMinusTable i j).Mem ((Yf+Construction.R0*(gamma 1-gamma 0)) i j) := by
  rw [← rhsMinusTable_calc]
  exact rhsMinusBox_mem i j
end AtomicTriangular.FiniteCertificate
end

end OAI
