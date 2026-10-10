import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData12
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData13
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData11

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge384 : Integer.Sparse Master := [(Sum.inl 0, -423778416910571520000), (Sum.inl 1, 299742544391270400000), (Sum.inl 2, 388757867168563200000), (Sum.inl 3, 9584025461769830400000), (Sum.inl 4, 2731728907218124800000), (Sum.inl 5, 323974216194048000000), (Sum.inl 6, -40496777024256000000), (Sum.inl 12, 2311814850921676800000), (Sum.inl 13, 6804854299179417600000), (Sum.inl 25, -7834632063197184000000), (Sum.inl 26, 2158466553402163200000), (Sum.inl 27, -485961324291072000000), (Sum.inl 31, -2137080764399616000000), (Sum.inl 33, -8057746737524736000000), (Sum.inl 34, 1200611473934745600000), (Sum.inl 51, -255596124672000000000), (Sum.inl 55, -255596124672000000000), (Sum.inl 63, -1688249172492288000000), (Sum.inl 64, -3632094469656576000000), (Sum.inl 123, -1943845297164288000000)]

def originalMerge384 : Integer.Sparse OriginalKey := originalMerge376 ++ originalMerge383

theorem reducedMerge384Check : reducedMerge384 = Integer.Sparse.mergeBy masterLess reducedMerge376 reducedMerge383 := by decide +kernel

def reducedMerge385 : Integer.Sparse Master := [(Sum.inl 0, -741059302383267840000), (Sum.inl 1, -5957621298152294400000), (Sum.inl 2, 1417711871145830400000), (Sum.inl 3, 46116810641328537600000), (Sum.inl 4, 10057164815145369600000), (Sum.inl 5, 943605600524697600000), (Sum.inl 6, -126501902818099200000), (Sum.inl 7, 562832512362086400000), (Sum.inl 8, -92692816802611200000), (Sum.inl 12, 22067780563571097600000), (Sum.inl 13, 30825002453962752000000), (Sum.inl 23, -4150728363840307200000), (Sum.inl 24, 278078450407833600000), (Sum.inl 25, -14014152297131212800000), (Sum.inl 26, 2121716628180172800000), (Sum.inl 27, -1518022833817190400000), (Sum.inl 31, -5420227055394816000000), (Sum.inl 32, 1481351094197452800000), (Sum.inl 33, -21957120275521536000000), (Sum.inl 34, 1200611473934745600000), (Sum.inl 35, -77137280601292800000), (Sum.inl 51, -255596124672000000000), (Sum.inl 54, -6334880740186521600000), (Sum.inl 55, -255596124672000000000), (Sum.inl 62, -3283146290995200000000), (Sum.inl 63, -1688249172492288000000), (Sum.inl 64, -3632094469656576000000), (Sum.inl 81, -255596124672000000000), (Sum.inl 123, -1943845297164288000000), (Sum.inl 195, 511192249344000000000)]

def originalMerge385 : Integer.Sparse OriginalKey := originalMerge370 ++ originalMerge384

theorem reducedMerge385Check : reducedMerge385 = Integer.Sparse.mergeBy masterLess reducedMerge370 reducedMerge384 := by decide +kernel

def reducedMerge386 : Integer.Sparse Master := [(Sum.inl 0, 219449668466165760000), (Sum.inl 1, -828605081764454400000), (Sum.inl 2, 56218488983193600000), (Sum.inl 3, 2655804553423257600000), (Sum.inl 4, 1756308729692160000000), (Sum.inl 12, 878154364846080000000), (Sum.inl 13, 14227639256678400000), (Sum.inl 26, 878154364846080000000)]

def originalMerge386 : Integer.Sparse OriginalKey := originalTerm390 ++ originalTerm391

theorem reducedMerge386Check : reducedMerge386 = Integer.Sparse.mergeBy masterLess reducedTerm390 reducedTerm391 := by decide +kernel

def reducedMerge387 : Integer.Sparse Master := [(Sum.inl 0, 647827988480870400000), (Sum.inl 1, -3238233131847168000000), (Sum.inl 2, 859427839010764800000), (Sum.inl 3, 6939587753570304000000), (Sum.inl 4, 1756308729692160000000), (Sum.inl 12, 5161937564993126400000), (Sum.inl 13, 14227639256678400000), (Sum.inl 26, 878154364846080000000), (Sum.inl 33, -12851349600441139200000)]

def originalMerge387 : Integer.Sparse OriginalKey := originalTerm389 ++ originalMerge386

theorem reducedMerge387Check : reducedMerge387 = Integer.Sparse.mergeBy masterLess reducedTerm389 reducedMerge386 := by decide +kernel

def reducedMerge388 : Integer.Sparse Master := [(Sum.inl 0, 149201132044124160000), (Sum.inl 1, 859036820860108800000), (Sum.inl 2, -22606232127897600000), (Sum.inl 3, 361699714046361600000), (Sum.inl 12, 361699714046361600000)]

def originalMerge388 : Integer.Sparse OriginalKey := originalTerm392 ++ originalTerm393

theorem reducedMerge388Check : reducedMerge388 = Integer.Sparse.mergeBy masterLess reducedTerm392 reducedTerm393 := by decide +kernel

def reducedMerge389 : Integer.Sparse Master := [(Sum.inl 0, -559206427749580800000), (Sum.inl 1, -1619075139687936000000), (Sum.inl 2, -239651335223193600000), (Sum.inl 3, 2300844615539097600000), (Sum.inl 4, -340794832896000000000), (Sum.inl 12, 2641639448435097600000), (Sum.inl 13, -170397416448000000000), (Sum.inl 25, 511192249344000000000), (Sum.inl 31, 511192249344000000000), (Sum.inl 33, 511192249344000000000)]

def originalMerge389 : Integer.Sparse OriginalKey := originalTerm394 ++ originalTerm395

theorem reducedMerge389Check : reducedMerge389 = Integer.Sparse.mergeBy masterLess reducedTerm394 reducedTerm395 := by decide +kernel

def reducedMerge390 : Integer.Sparse Master := [(Sum.inl 0, -410005295705456640000), (Sum.inl 1, -760038318827827200000), (Sum.inl 2, -262257567351091200000), (Sum.inl 3, 2662544329585459200000), (Sum.inl 4, -340794832896000000000), (Sum.inl 12, 3003339162481459200000), (Sum.inl 13, -170397416448000000000), (Sum.inl 25, 511192249344000000000), (Sum.inl 31, 511192249344000000000), (Sum.inl 33, 511192249344000000000)]

def originalMerge390 : Integer.Sparse OriginalKey := originalMerge388 ++ originalMerge389

theorem reducedMerge390Check : reducedMerge390 = Integer.Sparse.mergeBy masterLess reducedMerge388 reducedMerge389 := by decide +kernel

def reducedMerge391 : Integer.Sparse Master := [(Sum.inl 0, 237822692775413760000), (Sum.inl 1, -3998271450674995200000), (Sum.inl 2, 597170271659673600000), (Sum.inl 3, 9602132083155763200000), (Sum.inl 4, 1415513896796160000000), (Sum.inl 12, 8165276727474585600000), (Sum.inl 13, -156169777191321600000), (Sum.inl 25, 511192249344000000000), (Sum.inl 26, 878154364846080000000), (Sum.inl 31, 511192249344000000000), (Sum.inl 33, -12340157351097139200000)]

def originalMerge391 : Integer.Sparse OriginalKey := originalMerge387 ++ originalMerge390

theorem reducedMerge391Check : reducedMerge391 = Integer.Sparse.mergeBy masterLess reducedMerge387 reducedMerge390 := by decide +kernel

def reducedMerge392 : Integer.Sparse Master := [(Sum.inl 0, 32695253144064000000), (Sum.inl 1, 568435841116416000000), (Sum.inl 2, -29369419188480000000), (Sum.inl 3, -954973234446336000000), (Sum.inl 4, -474961313820672000000), (Sum.inl 12, -960023841251328000000), (Sum.inl 13, -320007947083776000000), (Sum.inl 25, -1455187582291968000000), (Sum.inl 31, -1455187582291968000000), (Sum.inl 33, -1455187582291968000000)]

def originalMerge392 : Integer.Sparse OriginalKey := originalTerm396 ++ originalTerm397

theorem reducedMerge392Check : reducedMerge392 = Integer.Sparse.mergeBy masterLess reducedTerm396 reducedTerm397 := by decide +kernel

def reducedMerge393 : Integer.Sparse Master := [(Sum.inl 0, 55765907805081600000), (Sum.inl 1, 155061942465024000000), (Sum.inl 2, 83766603174912000000), (Sum.inl 3, -160003973541888000000), (Sum.inl 12, -160003973541888000000), (Sum.inl 25, 1770392515885056000000)]

def originalMerge393 : Integer.Sparse OriginalKey := originalTerm398 ++ originalTerm399

theorem reducedMerge393Check : reducedMerge393 = Integer.Sparse.mergeBy masterLess reducedTerm398 reducedTerm399 := by decide +kernel

def reducedMerge394 : Integer.Sparse Master := [(Sum.inl 0, 88461160949145600000), (Sum.inl 1, 723497783581440000000), (Sum.inl 2, 54397183986432000000), (Sum.inl 3, -1114977207988224000000), (Sum.inl 4, -474961313820672000000), (Sum.inl 12, -1120027814793216000000), (Sum.inl 13, -320007947083776000000), (Sum.inl 25, 315204933593088000000), (Sum.inl 31, -1455187582291968000000), (Sum.inl 33, -1455187582291968000000)]

def originalMerge394 : Integer.Sparse OriginalKey := originalMerge392 ++ originalMerge393

theorem reducedMerge394Check : reducedMerge394 = Integer.Sparse.mergeBy masterLess reducedMerge392 reducedMerge393 := by decide +kernel

def reducedMerge395 : Integer.Sparse Master := [(Sum.inl 0, -1137493015622369280000), (Sum.inl 1, 1598593763708928000000), (Sum.inl 2, -309065204651212800000), (Sum.inl 3, 4945043274419404800000), (Sum.inl 4, 4945043274419404800000), (Sum.inl 12, -28409461574860800000)]

def originalMerge395 : Integer.Sparse OriginalKey := originalTerm400 ++ originalTerm401

theorem reducedMerge395Check : reducedMerge395 = Integer.Sparse.mergeBy masterLess reducedTerm400 reducedTerm401 := by decide +kernel

def reducedMerge396 : Integer.Sparse Master := [(Sum.inl 0, -4678341044428800000), (Sum.inl 1, -317856945285734400000), (Sum.inl 12, 322535286330163200000)]

def originalMerge396 : Integer.Sparse OriginalKey := originalTerm402 ++ originalTerm403

theorem reducedMerge396Check : reducedMerge396 = Integer.Sparse.mergeBy masterLess reducedTerm402 reducedTerm403 := by decide +kernel

def reducedMerge397 : Integer.Sparse Master := [(Sum.inl 0, -1142171356666798080000), (Sum.inl 1, 1280736818423193600000), (Sum.inl 2, -309065204651212800000), (Sum.inl 3, 4945043274419404800000), (Sum.inl 4, 4945043274419404800000), (Sum.inl 12, 294125824755302400000)]

def originalMerge397 : Integer.Sparse OriginalKey := originalMerge395 ++ originalMerge396

theorem reducedMerge397Check : reducedMerge397 = Integer.Sparse.mergeBy masterLess reducedMerge395 reducedMerge396 := by decide +kernel

def reducedMerge398 : Integer.Sparse Master := [(Sum.inl 0, -1053710195717652480000), (Sum.inl 1, 2004234602004633600000), (Sum.inl 2, -254668020664780800000), (Sum.inl 3, 3830066066431180800000), (Sum.inl 4, 4470081960598732800000), (Sum.inl 12, -825901990037913600000), (Sum.inl 13, -320007947083776000000), (Sum.inl 25, 315204933593088000000), (Sum.inl 31, -1455187582291968000000), (Sum.inl 33, -1455187582291968000000)]

def originalMerge398 : Integer.Sparse OriginalKey := originalMerge394 ++ originalMerge397

theorem reducedMerge398Check : reducedMerge398 = Integer.Sparse.mergeBy masterLess reducedMerge394 reducedMerge397 := by decide +kernel

def reducedMerge399 : Integer.Sparse Master := [(Sum.inl 0, -815887502942238720000), (Sum.inl 1, -1994036848670361600000), (Sum.inl 2, 342502250994892800000), (Sum.inl 3, 13432198149586944000000), (Sum.inl 4, 5885595857394892800000), (Sum.inl 12, 7339374737436672000000), (Sum.inl 13, -476177724275097600000), (Sum.inl 25, 826397182937088000000), (Sum.inl 26, 878154364846080000000), (Sum.inl 31, -943995332947968000000), (Sum.inl 33, -13795344933389107200000)]

def originalMerge399 : Integer.Sparse OriginalKey := originalMerge391 ++ originalMerge398

theorem reducedMerge399Check : reducedMerge399 = Integer.Sparse.mergeBy masterLess reducedMerge391 reducedMerge398 := by decide +kernel

def reducedMerge400 : Integer.Sparse Master := [(Sum.inl 0, -224991278439137280000), (Sum.inl 1, -1332014959366963200000), (Sum.inl 5, 161277964517376000000), (Sum.inl 8, 645111858069504000000), (Sum.inl 12, -1704340850481561600000), (Sum.inl 24, -645111858069504000000), (Sum.inl 27, -483833893552128000000), (Sum.inl 30, -1290223716139008000000)]

def originalMerge400 : Integer.Sparse OriginalKey := originalTerm405 ++ originalTerm406

theorem reducedMerge400Check : reducedMerge400 = Integer.Sparse.mergeBy masterLess reducedTerm405 reducedTerm406 := by decide +kernel

def reducedMerge401 : Integer.Sparse Master := [(Sum.inl 0, -224991278439137280000), (Sum.inl 1, -1332014959366963200000), (Sum.inl 5, 161277964517376000000), (Sum.inl 8, 645111858069504000000), (Sum.inl 12, -1704340850481561600000), (Sum.inl 24, -645111858069504000000), (Sum.inl 27, -483833893552128000000), (Sum.inl 30, -1290223716139008000000)]

def originalMerge401 : Integer.Sparse OriginalKey := originalTerm404 ++ originalMerge400

theorem reducedMerge401Check : reducedMerge401 = Integer.Sparse.mergeBy masterLess reducedTerm404 reducedMerge400 := by decide +kernel

def reducedMerge402 : Integer.Sparse Master := [(Sum.inl 0, 376315250540544000000), (Sum.inl 1, 268796607528960000000), (Sum.inl 5, 161277964517376000000), (Sum.inl 8, 645111858069504000000), (Sum.inl 27, -806389822586880000000), (Sum.inl 30, -3225559290347520000000)]

def originalMerge402 : Integer.Sparse OriginalKey := originalTerm407 ++ originalTerm408

theorem reducedMerge402Check : reducedMerge402 = Integer.Sparse.mergeBy masterLess reducedTerm407 reducedTerm408 := by decide +kernel

def reducedMerge403 : Integer.Sparse Master := [(Sum.inl 1, 320007947083776000000), (Sum.inl 2, -80001986770944000000), (Sum.inl 3, -320007947083776000000), (Sum.inl 4, -320007947083776000000), (Sum.inl 12, -80001986770944000000), (Sum.inl 31, 480011920625664000000)]

def originalMerge403 : Integer.Sparse OriginalKey := originalTerm409 ++ originalTerm410

theorem reducedMerge403Check : reducedMerge403 = Integer.Sparse.mergeBy masterLess reducedTerm409 reducedTerm410 := by decide +kernel

def reducedMerge404 : Integer.Sparse Master := [(Sum.inl 0, 376315250540544000000), (Sum.inl 1, 588804554612736000000), (Sum.inl 2, -80001986770944000000), (Sum.inl 3, -320007947083776000000), (Sum.inl 4, -320007947083776000000), (Sum.inl 5, 161277964517376000000), (Sum.inl 8, 645111858069504000000), (Sum.inl 12, -80001986770944000000), (Sum.inl 27, -806389822586880000000), (Sum.inl 30, -3225559290347520000000), (Sum.inl 31, 480011920625664000000)]

def originalMerge404 : Integer.Sparse OriginalKey := originalMerge402 ++ originalMerge403

theorem reducedMerge404Check : reducedMerge404 = Integer.Sparse.mergeBy masterLess reducedMerge402 reducedMerge403 := by decide +kernel

def reducedMerge405 : Integer.Sparse Master := [(Sum.inl 0, 151323972101406720000), (Sum.inl 1, -743210404754227200000), (Sum.inl 2, -80001986770944000000), (Sum.inl 3, -320007947083776000000), (Sum.inl 4, -320007947083776000000), (Sum.inl 5, 322555929034752000000), (Sum.inl 8, 1290223716139008000000), (Sum.inl 12, -1784342837252505600000), (Sum.inl 24, -645111858069504000000), (Sum.inl 27, -1290223716139008000000), (Sum.inl 30, -4515783006486528000000), (Sum.inl 31, 480011920625664000000)]

def originalMerge405 : Integer.Sparse OriginalKey := originalMerge401 ++ originalMerge404

theorem reducedMerge405Check : reducedMerge405 = Integer.Sparse.mergeBy masterLess reducedMerge401 reducedMerge404 := by decide +kernel

def reducedMerge406 : Integer.Sparse Master := [(Sum.inl 0, -93814003219507200000), (Sum.inl 1, 60525163367424000000), (Sum.inl 2, -45393872525568000000), (Sum.inl 3, -242100653469696000000), (Sum.inl 4, -242100653469696000000), (Sum.inl 31, 726301960409088000000)]

def originalMerge406 : Integer.Sparse OriginalKey := originalTerm411 ++ originalTerm412

theorem reducedMerge406Check : reducedMerge406 = Integer.Sparse.mergeBy masterLess reducedTerm411 reducedTerm412 := by decide +kernel

def reducedMerge407 : Integer.Sparse Master := [(Sum.inl 0, -184588041596313600000), (Sum.inl 1, -226883279508480000000), (Sum.inl 2, 133335745837056000000), (Sum.inl 5, 53759321505792000000), (Sum.inl 6, -13439830376448000000), (Sum.inl 8, 430074572046336000000), (Sum.inl 27, -161277964517376000000), (Sum.inl 30, -645111858069504000000), (Sum.inl 31, -670613248327680000000)]

def originalMerge407 : Integer.Sparse OriginalKey := originalTerm413 ++ originalTerm414

theorem reducedMerge407Check : reducedMerge407 = Integer.Sparse.mergeBy masterLess reducedTerm413 reducedTerm414 := by decide +kernel

def reducedMerge408 : Integer.Sparse Master := [(Sum.inl 0, -278402044815820800000), (Sum.inl 1, -166358116141056000000), (Sum.inl 2, 87941873311488000000), (Sum.inl 3, -242100653469696000000), (Sum.inl 4, -242100653469696000000), (Sum.inl 5, 53759321505792000000), (Sum.inl 6, -13439830376448000000), (Sum.inl 8, 430074572046336000000), (Sum.inl 27, -161277964517376000000), (Sum.inl 30, -645111858069504000000), (Sum.inl 31, 55688712081408000000)]

def originalMerge408 : Integer.Sparse OriginalKey := originalMerge406 ++ originalMerge407

theorem reducedMerge408Check : reducedMerge408 = Integer.Sparse.mergeBy masterLess reducedMerge406 reducedMerge407 := by decide +kernel

def reducedMerge409 : Integer.Sparse Master := [(Sum.inl 0, 358405884591390720000), (Sum.inl 1, 1753901137362124800000), (Sum.inl 2, -419411141543116800000), (Sum.inl 3, -610052569517260800000), (Sum.inl 4, -1220105139034521600000)]

def originalMerge409 : Integer.Sparse OriginalKey := originalTerm415 ++ originalTerm416

theorem reducedMerge409Check : reducedMerge409 = Integer.Sparse.mergeBy masterLess reducedTerm415 reducedTerm416 := by decide +kernel

def reducedMerge410 : Integer.Sparse Master := [(Sum.inl 0, -429052445894983680000), (Sum.inl 1, 390047678086348800000), (Sum.inl 2, -195023839043174400000)]

def originalMerge410 : Integer.Sparse OriginalKey := originalTerm417 ++ originalTerm418

theorem reducedMerge410Check : reducedMerge410 = Integer.Sparse.mergeBy masterLess reducedTerm417 reducedTerm418 := by decide +kernel

def reducedMerge411 : Integer.Sparse Master := [(Sum.inl 0, -70646561303592960000), (Sum.inl 1, 2143948815448473600000), (Sum.inl 2, -614434980586291200000), (Sum.inl 3, -610052569517260800000), (Sum.inl 4, -1220105139034521600000)]

def originalMerge411 : Integer.Sparse OriginalKey := originalMerge409 ++ originalMerge410

theorem reducedMerge411Check : reducedMerge411 = Integer.Sparse.mergeBy masterLess reducedMerge409 reducedMerge410 := by decide +kernel

def reducedMerge412 : Integer.Sparse Master := [(Sum.inl 0, -349048606119413760000), (Sum.inl 1, 1977590699307417600000), (Sum.inl 2, -526493107274803200000), (Sum.inl 3, -852153222986956800000), (Sum.inl 4, -1462205792504217600000), (Sum.inl 5, 53759321505792000000), (Sum.inl 6, -13439830376448000000), (Sum.inl 8, 430074572046336000000), (Sum.inl 27, -161277964517376000000), (Sum.inl 30, -645111858069504000000), (Sum.inl 31, 55688712081408000000)]

def originalMerge412 : Integer.Sparse OriginalKey := originalMerge408 ++ originalMerge411

theorem reducedMerge412Check : reducedMerge412 = Integer.Sparse.mergeBy masterLess reducedMerge408 reducedMerge411 := by decide +kernel

def reducedMerge413 : Integer.Sparse Master := [(Sum.inl 0, -197724634018007040000), (Sum.inl 1, 1234380294553190400000), (Sum.inl 2, -606495094045747200000), (Sum.inl 3, -1172161170070732800000), (Sum.inl 4, -1782213739587993600000), (Sum.inl 5, 376315250540544000000), (Sum.inl 6, -13439830376448000000), (Sum.inl 8, 1720298288185344000000), (Sum.inl 12, -1784342837252505600000), (Sum.inl 24, -645111858069504000000), (Sum.inl 27, -1451501680656384000000), (Sum.inl 30, -5160894864556032000000), (Sum.inl 31, 535700632707072000000)]

def originalMerge413 : Integer.Sparse OriginalKey := originalMerge405 ++ originalMerge412

theorem reducedMerge413Check : reducedMerge413 = Integer.Sparse.mergeBy masterLess reducedMerge405 reducedMerge412 := by decide +kernel

def reducedMerge414 : Integer.Sparse Master := [(Sum.inl 0, -1013612136960245760000), (Sum.inl 1, -759656554117171200000), (Sum.inl 2, -263992843050854400000), (Sum.inl 3, 12260036979516211200000), (Sum.inl 4, 4103382117806899200000), (Sum.inl 5, 376315250540544000000), (Sum.inl 6, -13439830376448000000), (Sum.inl 8, 1720298288185344000000), (Sum.inl 12, 5555031900184166400000), (Sum.inl 13, -476177724275097600000), (Sum.inl 24, -645111858069504000000), (Sum.inl 25, 826397182937088000000), (Sum.inl 26, 878154364846080000000), (Sum.inl 27, -1451501680656384000000), (Sum.inl 30, -5160894864556032000000), (Sum.inl 31, -408294700240896000000), (Sum.inl 33, -13795344933389107200000)]

def originalMerge414 : Integer.Sparse OriginalKey := originalMerge399 ++ originalMerge413

theorem reducedMerge414Check : reducedMerge414 = Integer.Sparse.mergeBy masterLess reducedMerge399 reducedMerge413 := by decide +kernel

def reducedMerge415 : Integer.Sparse Master := [(Sum.inl 0, -1754671439343513600000), (Sum.inl 1, -6717277852269465600000), (Sum.inl 2, 1153719028094976000000), (Sum.inl 3, 58376847620844748800000), (Sum.inl 4, 14160546932952268800000), (Sum.inl 5, 1319920851065241600000), (Sum.inl 6, -139941733194547200000), (Sum.inl 7, 562832512362086400000), (Sum.inl 8, 1627605471382732800000), (Sum.inl 12, 27622812463755264000000), (Sum.inl 13, 30348824729687654400000), (Sum.inl 23, -4150728363840307200000), (Sum.inl 24, -367033407661670400000), (Sum.inl 25, -13187755114194124800000), (Sum.inl 26, 2999870993026252800000), (Sum.inl 27, -2969524514473574400000), (Sum.inl 30, -5160894864556032000000), (Sum.inl 31, -5828521755635712000000), (Sum.inl 32, 1481351094197452800000), (Sum.inl 33, -35752465208910643200000), (Sum.inl 34, 1200611473934745600000), (Sum.inl 35, -77137280601292800000), (Sum.inl 51, -255596124672000000000), (Sum.inl 54, -6334880740186521600000), (Sum.inl 55, -255596124672000000000), (Sum.inl 62, -3283146290995200000000), (Sum.inl 63, -1688249172492288000000), (Sum.inl 64, -3632094469656576000000), (Sum.inl 81, -255596124672000000000), (Sum.inl 123, -1943845297164288000000), (Sum.inl 195, 511192249344000000000)]

def originalMerge415 : Integer.Sparse OriginalKey := originalMerge385 ++ originalMerge414

theorem reducedMerge415Check : reducedMerge415 = Integer.Sparse.mergeBy masterLess reducedMerge385 reducedMerge414 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
