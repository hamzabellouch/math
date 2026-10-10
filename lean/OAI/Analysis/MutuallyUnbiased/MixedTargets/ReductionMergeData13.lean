import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData13
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData14

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge416 : Integer.Sparse Master := [(Sum.inl 0, 185349405198827520000), (Sum.inl 1, 913556918834380800000), (Sum.inl 4, -8116989021388800000)]

def originalMerge416 : Integer.Sparse OriginalKey := originalTerm420 ++ originalTerm421

theorem reducedMerge416Check : reducedMerge416 = Integer.Sparse.mergeBy masterLess reducedTerm420 reducedTerm421 := by decide +kernel

def reducedMerge417 : Integer.Sparse Master := [(Sum.inl 0, -300736362871848960000), (Sum.inl 1, 1457682778614988800000), (Sum.inl 4, -588517906120704000000)]

def originalMerge417 : Integer.Sparse OriginalKey := originalTerm419 ++ originalMerge416

theorem reducedMerge417Check : reducedMerge417 = Integer.Sparse.mergeBy masterLess reducedTerm419 reducedMerge416 := by decide +kernel

def reducedMerge418 : Integer.Sparse Master := [(Sum.inl 0, 196910301321216000000), (Sum.inl 1, -421950645688320000000), (Sum.inl 4, 2250403443671040000000)]

def originalMerge418 : Integer.Sparse OriginalKey := originalTerm422 ++ originalTerm423

theorem reducedMerge418Check : reducedMerge418 = Integer.Sparse.mergeBy masterLess reducedTerm422 reducedTerm423 := by decide +kernel

def reducedMerge419 : Integer.Sparse Master := [(Sum.inl 0, 1204186356864368640000), (Sum.inl 1, 1600500854060236800000), (Sum.inl 12, -609714611070566400000)]

def originalMerge419 : Integer.Sparse OriginalKey := originalTerm424 ++ originalTerm425

theorem reducedMerge419Check : reducedMerge419 = Integer.Sparse.mergeBy masterLess reducedTerm424 reducedTerm425 := by decide +kernel

def reducedMerge420 : Integer.Sparse Master := [(Sum.inl 0, 1401096658185584640000), (Sum.inl 1, 1178550208371916800000), (Sum.inl 4, 2250403443671040000000), (Sum.inl 12, -609714611070566400000)]

def originalMerge420 : Integer.Sparse OriginalKey := originalMerge418 ++ originalMerge419

theorem reducedMerge420Check : reducedMerge420 = Integer.Sparse.mergeBy masterLess reducedMerge418 reducedMerge419 := by decide +kernel

def reducedMerge421 : Integer.Sparse Master := [(Sum.inl 0, 1100360295313735680000), (Sum.inl 1, 2636232986986905600000), (Sum.inl 4, 1661885537550336000000), (Sum.inl 12, -609714611070566400000)]

def originalMerge421 : Integer.Sparse OriginalKey := originalMerge417 ++ originalMerge420

theorem reducedMerge421Check : reducedMerge421 = Integer.Sparse.mergeBy masterLess reducedMerge417 reducedMerge420 := by decide +kernel

def reducedMerge422 : Integer.Sparse Master := [(Sum.inl 0, -105737073514168320000), (Sum.inl 1, -236221121680588800000), (Sum.inl 4, 179977997470924800000), (Sum.inr 577, -654308882759024640000)]

def originalMerge422 : Integer.Sparse OriginalKey := originalTerm426 ++ originalTerm427

theorem reducedMerge422Check : reducedMerge422 = Integer.Sparse.mergeBy masterLess reducedTerm426 reducedTerm427 := by decide +kernel

def reducedMerge423 : Integer.Sparse Master := [(Sum.inr 578, -2282493232765992960000), (Sum.inr 579, 654308882759024640000)]

def originalMerge423 : Integer.Sparse OriginalKey := originalTerm428 ++ originalTerm429

theorem reducedMerge423Check : reducedMerge423 = Integer.Sparse.mergeBy masterLess reducedTerm428 reducedTerm429 := by decide +kernel

def reducedMerge424 : Integer.Sparse Master := [(Sum.inl 0, -105737073514168320000), (Sum.inl 1, -236221121680588800000), (Sum.inl 4, 179977997470924800000), (Sum.inr 577, -654308882759024640000), (Sum.inr 578, -2282493232765992960000), (Sum.inr 579, 654308882759024640000)]

def originalMerge424 : Integer.Sparse OriginalKey := originalMerge422 ++ originalMerge423

theorem reducedMerge424Check : reducedMerge424 = Integer.Sparse.mergeBy masterLess reducedMerge422 reducedMerge423 := by decide +kernel

def reducedMerge425 : Integer.Sparse Master := [(Sum.inr 580, 877592856526848000000), (Sum.inr 581, 877447660307742720000)]

def originalMerge425 : Integer.Sparse OriginalKey := originalTerm430 ++ originalTerm431

theorem reducedMerge425Check : reducedMerge425 = Integer.Sparse.mergeBy masterLess reducedTerm430 reducedTerm431 := by decide +kernel

def reducedMerge426 : Integer.Sparse Master := [(Sum.inr 582, 607591276892651520000), (Sum.inr 583, 2282493232765992960000)]

def originalMerge426 : Integer.Sparse OriginalKey := originalTerm432 ++ originalTerm433

theorem reducedMerge426Check : reducedMerge426 = Integer.Sparse.mergeBy masterLess reducedTerm432 reducedTerm433 := by decide +kernel

def reducedMerge427 : Integer.Sparse Master := [(Sum.inr 580, 877592856526848000000), (Sum.inr 581, 877447660307742720000), (Sum.inr 582, 607591276892651520000), (Sum.inr 583, 2282493232765992960000)]

def originalMerge427 : Integer.Sparse OriginalKey := originalMerge425 ++ originalMerge426

theorem reducedMerge427Check : reducedMerge427 = Integer.Sparse.mergeBy masterLess reducedMerge425 reducedMerge426 := by decide +kernel

def reducedMerge428 : Integer.Sparse Master := [(Sum.inl 0, -105737073514168320000), (Sum.inl 1, -236221121680588800000), (Sum.inl 4, 179977997470924800000), (Sum.inr 577, -654308882759024640000), (Sum.inr 578, -2282493232765992960000), (Sum.inr 579, 654308882759024640000), (Sum.inr 580, 877592856526848000000), (Sum.inr 581, 877447660307742720000), (Sum.inr 582, 607591276892651520000), (Sum.inr 583, 2282493232765992960000)]

def originalMerge428 : Integer.Sparse OriginalKey := originalMerge424 ++ originalMerge427

theorem reducedMerge428Check : reducedMerge428 = Integer.Sparse.mergeBy masterLess reducedMerge424 reducedMerge427 := by decide +kernel

def reducedMerge429 : Integer.Sparse Master := [(Sum.inl 0, 994623221799567360000), (Sum.inl 1, 2400011865306316800000), (Sum.inl 4, 1841863535021260800000), (Sum.inl 12, -609714611070566400000), (Sum.inr 577, -654308882759024640000), (Sum.inr 578, -2282493232765992960000), (Sum.inr 579, 654308882759024640000), (Sum.inr 580, 877592856526848000000), (Sum.inr 581, 877447660307742720000), (Sum.inr 582, 607591276892651520000), (Sum.inr 583, 2282493232765992960000)]

def originalMerge429 : Integer.Sparse OriginalKey := originalMerge421 ++ originalMerge428

theorem reducedMerge429Check : reducedMerge429 = Integer.Sparse.mergeBy masterLess reducedMerge421 reducedMerge428 := by decide +kernel

def reducedMerge430 : Integer.Sparse Master := [(Sum.inr 585, -2325444766551244800000), (Sum.inr 586, -878028445184163840000)]

def originalMerge430 : Integer.Sparse OriginalKey := originalTerm435 ++ originalTerm436

theorem reducedMerge430Check : reducedMerge430 = Integer.Sparse.mergeBy masterLess reducedTerm435 reducedTerm436 := by decide +kernel

def reducedMerge431 : Integer.Sparse Master := [(Sum.inr 584, -113253321790586880000), (Sum.inr 585, -2325444766551244800000), (Sum.inr 586, -878028445184163840000)]

def originalMerge431 : Integer.Sparse OriginalKey := originalTerm434 ++ originalMerge430

theorem reducedMerge431Check : reducedMerge431 = Integer.Sparse.mergeBy masterLess reducedTerm434 reducedMerge430 := by decide +kernel

def reducedMerge432 : Integer.Sparse Master := [(Sum.inr 587, 4950070676784414720000), (Sum.inr 588, -947351242264412160000)]

def originalMerge432 : Integer.Sparse OriginalKey := originalTerm437 ++ originalTerm438

theorem reducedMerge432Check : reducedMerge432 = Integer.Sparse.mergeBy masterLess reducedTerm437 reducedTerm438 := by decide +kernel

def reducedMerge433 : Integer.Sparse Master := [(Sum.inr 589, -877883248965058560000), (Sum.inr 590, -544816666760970240000)]

def originalMerge433 : Integer.Sparse OriginalKey := originalTerm439 ++ originalTerm440

theorem reducedMerge433Check : reducedMerge433 = Integer.Sparse.mergeBy masterLess reducedTerm439 reducedTerm440 := by decide +kernel

def reducedMerge434 : Integer.Sparse Master := [(Sum.inr 587, 4950070676784414720000), (Sum.inr 588, -947351242264412160000), (Sum.inr 589, -877883248965058560000), (Sum.inr 590, -544816666760970240000)]

def originalMerge434 : Integer.Sparse OriginalKey := originalMerge432 ++ originalMerge433

theorem reducedMerge434Check : reducedMerge434 = Integer.Sparse.mergeBy masterLess reducedMerge432 reducedMerge433 := by decide +kernel

def reducedMerge435 : Integer.Sparse Master := [(Sum.inr 584, -113253321790586880000), (Sum.inr 585, -2325444766551244800000), (Sum.inr 586, -878028445184163840000), (Sum.inr 587, 4950070676784414720000), (Sum.inr 588, -947351242264412160000), (Sum.inr 589, -877883248965058560000), (Sum.inr 590, -544816666760970240000)]

def originalMerge435 : Integer.Sparse OriginalKey := originalMerge431 ++ originalMerge434

theorem reducedMerge435Check : reducedMerge435 = Integer.Sparse.mergeBy masterLess reducedMerge431 reducedMerge434 := by decide +kernel

def reducedMerge436 : Integer.Sparse Master := [(Sum.inr 591, 2291676713032089600000), (Sum.inr 597, -28541892592926720000)]

def originalMerge436 : Integer.Sparse OriginalKey := originalTerm441 ++ originalTerm442

theorem reducedMerge436Check : reducedMerge436 = Integer.Sparse.mergeBy masterLess reducedTerm441 reducedTerm442 := by decide +kernel

def reducedMerge437 : Integer.Sparse Master := [(Sum.inr 599, -1211529171307069440000), (Sum.inr 600, 344588552322416640000)]

def originalMerge437 : Integer.Sparse OriginalKey := originalTerm443 ++ originalTerm444

theorem reducedMerge437Check : reducedMerge437 = Integer.Sparse.mergeBy masterLess reducedTerm443 reducedTerm444 := by decide +kernel

def reducedMerge438 : Integer.Sparse Master := [(Sum.inr 591, 2291676713032089600000), (Sum.inr 597, -28541892592926720000), (Sum.inr 599, -1211529171307069440000), (Sum.inr 600, 344588552322416640000)]

def originalMerge438 : Integer.Sparse OriginalKey := originalMerge436 ++ originalMerge437

theorem reducedMerge438Check : reducedMerge438 = Integer.Sparse.mergeBy masterLess reducedMerge436 reducedMerge437 := by decide +kernel

def reducedMerge439 : Integer.Sparse Master := [(Sum.inr 601, 28541892592926720000), (Sum.inr 603, 533546803510640640000)]

def originalMerge439 : Integer.Sparse OriginalKey := originalTerm445 ++ originalTerm446

theorem reducedMerge439Check : reducedMerge439 = Integer.Sparse.mergeBy masterLess reducedTerm445 reducedTerm446 := by decide +kernel

def reducedMerge440 : Integer.Sparse Master := [(Sum.inr 604, 6690208535414046720000), (Sum.inr 605, -2453660793490636800000)]

def originalMerge440 : Integer.Sparse OriginalKey := originalTerm447 ++ originalTerm448

theorem reducedMerge440Check : reducedMerge440 = Integer.Sparse.mergeBy masterLess reducedTerm447 reducedTerm448 := by decide +kernel

def reducedMerge441 : Integer.Sparse Master := [(Sum.inr 601, 28541892592926720000), (Sum.inr 603, 533546803510640640000), (Sum.inr 604, 6690208535414046720000), (Sum.inr 605, -2453660793490636800000)]

def originalMerge441 : Integer.Sparse OriginalKey := originalMerge439 ++ originalMerge440

theorem reducedMerge441Check : reducedMerge441 = Integer.Sparse.mergeBy masterLess reducedMerge439 reducedMerge440 := by decide +kernel

def reducedMerge442 : Integer.Sparse Master := [(Sum.inr 591, 2291676713032089600000), (Sum.inr 597, -28541892592926720000), (Sum.inr 599, -1211529171307069440000), (Sum.inr 600, 344588552322416640000), (Sum.inr 601, 28541892592926720000), (Sum.inr 603, 533546803510640640000), (Sum.inr 604, 6690208535414046720000), (Sum.inr 605, -2453660793490636800000)]

def originalMerge442 : Integer.Sparse OriginalKey := originalMerge438 ++ originalMerge441

theorem reducedMerge442Check : reducedMerge442 = Integer.Sparse.mergeBy masterLess reducedMerge438 reducedMerge441 := by decide +kernel

def reducedMerge443 : Integer.Sparse Master := [(Sum.inr 584, -113253321790586880000), (Sum.inr 585, -2325444766551244800000), (Sum.inr 586, -878028445184163840000), (Sum.inr 587, 4950070676784414720000), (Sum.inr 588, -947351242264412160000), (Sum.inr 589, -877883248965058560000), (Sum.inr 590, -544816666760970240000), (Sum.inr 591, 2291676713032089600000), (Sum.inr 597, -28541892592926720000), (Sum.inr 599, -1211529171307069440000), (Sum.inr 600, 344588552322416640000), (Sum.inr 601, 28541892592926720000), (Sum.inr 603, 533546803510640640000), (Sum.inr 604, 6690208535414046720000), (Sum.inr 605, -2453660793490636800000)]

def originalMerge443 : Integer.Sparse OriginalKey := originalMerge435 ++ originalMerge442

theorem reducedMerge443Check : reducedMerge443 = Integer.Sparse.mergeBy masterLess reducedMerge435 reducedMerge442 := by decide +kernel

def reducedMerge444 : Integer.Sparse Master := [(Sum.inl 0, 994623221799567360000), (Sum.inl 1, 2400011865306316800000), (Sum.inl 4, 1841863535021260800000), (Sum.inl 12, -609714611070566400000), (Sum.inr 577, -654308882759024640000), (Sum.inr 578, -2282493232765992960000), (Sum.inr 579, 654308882759024640000), (Sum.inr 580, 877592856526848000000), (Sum.inr 581, 877447660307742720000), (Sum.inr 582, 607591276892651520000), (Sum.inr 583, 2282493232765992960000), (Sum.inr 584, -113253321790586880000), (Sum.inr 585, -2325444766551244800000), (Sum.inr 586, -878028445184163840000), (Sum.inr 587, 4950070676784414720000), (Sum.inr 588, -947351242264412160000), (Sum.inr 589, -877883248965058560000), (Sum.inr 590, -544816666760970240000), (Sum.inr 591, 2291676713032089600000), (Sum.inr 597, -28541892592926720000), (Sum.inr 599, -1211529171307069440000), (Sum.inr 600, 344588552322416640000), (Sum.inr 601, 28541892592926720000), (Sum.inr 603, 533546803510640640000), (Sum.inr 604, 6690208535414046720000), (Sum.inr 605, -2453660793490636800000)]

def originalMerge444 : Integer.Sparse OriginalKey := originalMerge429 ++ originalMerge443

theorem reducedMerge444Check : reducedMerge444 = Integer.Sparse.mergeBy masterLess reducedMerge429 reducedMerge443 := by decide +kernel

def reducedMerge445 : Integer.Sparse Master := [(Sum.inr 607, 2300979745408942080000), (Sum.inr 608, -1054181617875025920000)]

def originalMerge445 : Integer.Sparse OriginalKey := originalTerm450 ++ originalTerm451

theorem reducedMerge445Check : reducedMerge445 = Integer.Sparse.mergeBy masterLess reducedTerm450 reducedTerm451 := by decide +kernel

def reducedMerge446 : Integer.Sparse Master := [(Sum.inr 606, 1441480432653434880000), (Sum.inr 607, 2300979745408942080000), (Sum.inr 608, -1054181617875025920000)]

def originalMerge446 : Integer.Sparse OriginalKey := originalTerm449 ++ originalMerge445

theorem reducedMerge446Check : reducedMerge446 = Integer.Sparse.mergeBy masterLess reducedTerm449 reducedMerge445 := by decide +kernel

def reducedMerge447 : Integer.Sparse Master := [(Sum.inr 610, -9473152863350292480000), (Sum.inr 611, 18388973290326589440000)]

def originalMerge447 : Integer.Sparse OriginalKey := originalTerm452 ++ originalTerm453

theorem reducedMerge447Check : reducedMerge447 = Integer.Sparse.mergeBy masterLess reducedTerm452 reducedTerm453 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
