import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData42
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData43
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData41

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1344 : Integer.Sparse Master := [(Sum.inr 3517, 3031883170345451520000), (Sum.inr 3519, -500927005576101888000), (Sum.inr 3523, -12294580299389337600000), (Sum.inr 3524, -1072771597873446912000), (Sum.inr 3526, -8846701964077694976000), (Sum.inr 3529, 2431584286271078400000), (Sum.inr 3530, 6558674437762449408000), (Sum.inr 3532, -1598770106249379840000), (Sum.inr 3533, -1975281871324446720000), (Sum.inr 3534, 26110149656309268480000), (Sum.inr 3535, 4491472530225364992000), (Sum.inr 3537, 7698731041103413248000), (Sum.inr 3538, 1252704393088598016000), (Sum.inr 3539, 6590198986965909504000), (Sum.inr 3540, 442881254805405696000), (Sum.inr 3541, -2683554743866687488000), (Sum.inr 3542, -1438088403369590784000), (Sum.inr 3543, -3946797413223727104000), (Sum.inr 3544, -2488508247260528640000), (Sum.inr 3548, -1028860950356951040000), (Sum.inr 3549, 1255758373127946240000), (Sum.inr 3553, -1133832859511095296000), (Sum.inr 3554, -5933039869919232000000), (Sum.inr 3555, -5743947411554107392000), (Sum.inr 3556, -1645301575619444736000), (Sum.inr 3557, 900394580334477312000), (Sum.inr 3558, 8704054146298871808000), (Sum.inr 3562, 2987270009704415232000)]

def originalMerge1344 : Integer.Sparse OriginalKey := originalMerge1329 ++ originalMerge1343

theorem reducedMerge1344Check : reducedMerge1344 = Integer.Sparse.mergeBy masterLess reducedMerge1329 reducedMerge1343 := by decide +kernel

def reducedMerge1345 : Integer.Sparse Master := [(Sum.inr 3569, 1962225745433985024000), (Sum.inr 3570, 2433073703307706368000)]

def originalMerge1345 : Integer.Sparse OriginalKey := originalTerm1350 ++ originalTerm1351

theorem reducedMerge1345Check : reducedMerge1345 = Integer.Sparse.mergeBy masterLess reducedTerm1350 reducedTerm1351 := by decide +kernel

def reducedMerge1346 : Integer.Sparse Master := [(Sum.inr 3565, 5653339486845861888000), (Sum.inr 3569, 1962225745433985024000), (Sum.inr 3570, 2433073703307706368000)]

def originalMerge1346 : Integer.Sparse OriginalKey := originalTerm1349 ++ originalMerge1345

theorem reducedMerge1346Check : reducedMerge1346 = Integer.Sparse.mergeBy masterLess reducedTerm1349 reducedMerge1345 := by decide +kernel

def reducedMerge1347 : Integer.Sparse Master := [(Sum.inr 3571, 12926463385317801984000), (Sum.inr 3572, -16798163909915049984000)]

def originalMerge1347 : Integer.Sparse OriginalKey := originalTerm1352 ++ originalTerm1353

theorem reducedMerge1347Check : reducedMerge1347 = Integer.Sparse.mergeBy masterLess reducedTerm1352 reducedTerm1353 := by decide +kernel

def reducedMerge1348 : Integer.Sparse Master := [(Sum.inr 3573, 19725678159807578112000), (Sum.inr 3577, 4629005356695552000000)]

def originalMerge1348 : Integer.Sparse OriginalKey := originalTerm1354 ++ originalTerm1355

theorem reducedMerge1348Check : reducedMerge1348 = Integer.Sparse.mergeBy masterLess reducedTerm1354 reducedTerm1355 := by decide +kernel

def reducedMerge1349 : Integer.Sparse Master := [(Sum.inr 3571, 12926463385317801984000), (Sum.inr 3572, -16798163909915049984000), (Sum.inr 3573, 19725678159807578112000), (Sum.inr 3577, 4629005356695552000000)]

def originalMerge1349 : Integer.Sparse OriginalKey := originalMerge1347 ++ originalMerge1348

theorem reducedMerge1349Check : reducedMerge1349 = Integer.Sparse.mergeBy masterLess reducedMerge1347 reducedMerge1348 := by decide +kernel

def reducedMerge1350 : Integer.Sparse Master := [(Sum.inr 3565, 5653339486845861888000), (Sum.inr 3569, 1962225745433985024000), (Sum.inr 3570, 2433073703307706368000), (Sum.inr 3571, 12926463385317801984000), (Sum.inr 3572, -16798163909915049984000), (Sum.inr 3573, 19725678159807578112000), (Sum.inr 3577, 4629005356695552000000)]

def originalMerge1350 : Integer.Sparse OriginalKey := originalMerge1346 ++ originalMerge1349

theorem reducedMerge1350Check : reducedMerge1350 = Integer.Sparse.mergeBy masterLess reducedMerge1346 reducedMerge1349 := by decide +kernel

def reducedMerge1351 : Integer.Sparse Master := [(Sum.inr 3578, 13978224602687471616000), (Sum.inr 3579, 4549640633792593920000)]

def originalMerge1351 : Integer.Sparse OriginalKey := originalTerm1356 ++ originalTerm1357

theorem reducedMerge1351Check : reducedMerge1351 = Integer.Sparse.mergeBy masterLess reducedTerm1356 reducedTerm1357 := by decide +kernel

def reducedMerge1352 : Integer.Sparse Master := [(Sum.inr 3580, 831414264535056384000), (Sum.inr 3581, -220499962681098240000)]

def originalMerge1352 : Integer.Sparse OriginalKey := originalTerm1358 ++ originalTerm1359

theorem reducedMerge1352Check : reducedMerge1352 = Integer.Sparse.mergeBy masterLess reducedTerm1358 reducedTerm1359 := by decide +kernel

def reducedMerge1353 : Integer.Sparse Master := [(Sum.inr 3578, 13978224602687471616000), (Sum.inr 3579, 4549640633792593920000), (Sum.inr 3580, 831414264535056384000), (Sum.inr 3581, -220499962681098240000)]

def originalMerge1353 : Integer.Sparse OriginalKey := originalMerge1351 ++ originalMerge1352

theorem reducedMerge1353Check : reducedMerge1353 = Integer.Sparse.mergeBy masterLess reducedMerge1351 reducedMerge1352 := by decide +kernel

def reducedMerge1354 : Integer.Sparse Master := [(Sum.inr 3582, 4158174109630464000000), (Sum.inr 3583, -11906431827880181760000)]

def originalMerge1354 : Integer.Sparse OriginalKey := originalTerm1360 ++ originalTerm1361

theorem reducedMerge1354Check : reducedMerge1354 = Integer.Sparse.mergeBy masterLess reducedTerm1360 reducedTerm1361 := by decide +kernel

def reducedMerge1355 : Integer.Sparse Master := [(Sum.inr 3584, 29008204646800490496000)]

def originalMerge1355 : Integer.Sparse OriginalKey := originalTerm1362 ++ originalTerm1363

theorem reducedMerge1355Check : reducedMerge1355 = Integer.Sparse.mergeBy masterLess reducedTerm1362 reducedTerm1363 := by decide +kernel

def reducedMerge1356 : Integer.Sparse Master := [(Sum.inr 3582, 4158174109630464000000), (Sum.inr 3583, -11906431827880181760000), (Sum.inr 3584, 29008204646800490496000)]

def originalMerge1356 : Integer.Sparse OriginalKey := originalMerge1354 ++ originalMerge1355

theorem reducedMerge1356Check : reducedMerge1356 = Integer.Sparse.mergeBy masterLess reducedMerge1354 reducedMerge1355 := by decide +kernel

def reducedMerge1357 : Integer.Sparse Master := [(Sum.inr 3578, 13978224602687471616000), (Sum.inr 3579, 4549640633792593920000), (Sum.inr 3580, 831414264535056384000), (Sum.inr 3581, -220499962681098240000), (Sum.inr 3582, 4158174109630464000000), (Sum.inr 3583, -11906431827880181760000), (Sum.inr 3584, 29008204646800490496000)]

def originalMerge1357 : Integer.Sparse OriginalKey := originalMerge1353 ++ originalMerge1356

theorem reducedMerge1357Check : reducedMerge1357 = Integer.Sparse.mergeBy masterLess reducedMerge1353 reducedMerge1356 := by decide +kernel

def reducedMerge1358 : Integer.Sparse Master := [(Sum.inr 3565, 5653339486845861888000), (Sum.inr 3569, 1962225745433985024000), (Sum.inr 3570, 2433073703307706368000), (Sum.inr 3571, 12926463385317801984000), (Sum.inr 3572, -16798163909915049984000), (Sum.inr 3573, 19725678159807578112000), (Sum.inr 3577, 4629005356695552000000), (Sum.inr 3578, 13978224602687471616000), (Sum.inr 3579, 4549640633792593920000), (Sum.inr 3580, 831414264535056384000), (Sum.inr 3581, -220499962681098240000), (Sum.inr 3582, 4158174109630464000000), (Sum.inr 3583, -11906431827880181760000), (Sum.inr 3584, 29008204646800490496000)]

def originalMerge1358 : Integer.Sparse OriginalKey := originalMerge1350 ++ originalMerge1357

theorem reducedMerge1358Check : reducedMerge1358 = Integer.Sparse.mergeBy masterLess reducedMerge1350 reducedMerge1357 := by decide +kernel

def reducedMerge1359 : Integer.Sparse Master := [(Sum.inr 3622, 13643436319594905600000), (Sum.inr 3623, -6320730118534594560000)]

def originalMerge1359 : Integer.Sparse OriginalKey := originalTerm1365 ++ originalTerm1366

theorem reducedMerge1359Check : reducedMerge1359 = Integer.Sparse.mergeBy masterLess reducedTerm1365 reducedTerm1366 := by decide +kernel

def reducedMerge1360 : Integer.Sparse Master := [(Sum.inr 3619, -9131775422933237760000), (Sum.inr 3622, 13643436319594905600000), (Sum.inr 3623, -6320730118534594560000)]

def originalMerge1360 : Integer.Sparse OriginalKey := originalTerm1364 ++ originalMerge1359

theorem reducedMerge1360Check : reducedMerge1360 = Integer.Sparse.mergeBy masterLess reducedTerm1364 reducedMerge1359 := by decide +kernel

def reducedMerge1361 : Integer.Sparse Master := [(Sum.inr 3625, 3684922744987975680000), (Sum.inr 3626, 5131131445562572800000)]

def originalMerge1361 : Integer.Sparse OriginalKey := originalTerm1367 ++ originalTerm1368

theorem reducedMerge1361Check : reducedMerge1361 = Integer.Sparse.mergeBy masterLess reducedTerm1367 reducedTerm1368 := by decide +kernel

def reducedMerge1362 : Integer.Sparse Master := [(Sum.inr 3627, 7417776676181114880000)]

def originalMerge1362 : Integer.Sparse OriginalKey := originalTerm1369 ++ originalTerm1370

theorem reducedMerge1362Check : reducedMerge1362 = Integer.Sparse.mergeBy masterLess reducedTerm1369 reducedTerm1370 := by decide +kernel

def reducedMerge1363 : Integer.Sparse Master := [(Sum.inr 3625, 3684922744987975680000), (Sum.inr 3626, 5131131445562572800000), (Sum.inr 3627, 7417776676181114880000)]

def originalMerge1363 : Integer.Sparse OriginalKey := originalMerge1361 ++ originalMerge1362

theorem reducedMerge1363Check : reducedMerge1363 = Integer.Sparse.mergeBy masterLess reducedMerge1361 reducedMerge1362 := by decide +kernel

def reducedMerge1364 : Integer.Sparse Master := [(Sum.inr 3619, -9131775422933237760000), (Sum.inr 3622, 13643436319594905600000), (Sum.inr 3623, -6320730118534594560000), (Sum.inr 3625, 3684922744987975680000), (Sum.inr 3626, 5131131445562572800000), (Sum.inr 3627, 7417776676181114880000)]

def originalMerge1364 : Integer.Sparse OriginalKey := originalMerge1360 ++ originalMerge1363

theorem reducedMerge1364Check : reducedMerge1364 = Integer.Sparse.mergeBy masterLess reducedMerge1360 reducedMerge1363 := by decide +kernel

def reducedMerge1365 : Integer.Sparse Master := [(Sum.inr 3632, -3609060248797839360000)]

def originalMerge1365 : Integer.Sparse OriginalKey := originalTerm1371 ++ originalTerm1372

theorem reducedMerge1365Check : reducedMerge1365 = Integer.Sparse.mergeBy masterLess reducedTerm1371 reducedTerm1372 := by decide +kernel

def reducedMerge1366 : Integer.Sparse Master := [(Sum.inr 3633, 17665403553650442240000)]

def originalMerge1366 : Integer.Sparse OriginalKey := originalTerm1373 ++ originalTerm1374

theorem reducedMerge1366Check : reducedMerge1366 = Integer.Sparse.mergeBy masterLess reducedTerm1373 reducedTerm1374 := by decide +kernel

def reducedMerge1367 : Integer.Sparse Master := [(Sum.inr 3632, -3609060248797839360000), (Sum.inr 3633, 17665403553650442240000)]

def originalMerge1367 : Integer.Sparse OriginalKey := originalMerge1365 ++ originalMerge1366

theorem reducedMerge1367Check : reducedMerge1367 = Integer.Sparse.mergeBy masterLess reducedMerge1365 reducedMerge1366 := by decide +kernel

def reducedMerge1368 : Integer.Sparse Master := [(Sum.inr 3670, -3558260895488409600000)]

def originalMerge1368 : Integer.Sparse OriginalKey := originalTerm1375 ++ originalTerm1376

theorem reducedMerge1368Check : reducedMerge1368 = Integer.Sparse.mergeBy masterLess reducedTerm1375 reducedTerm1376 := by decide +kernel

def reducedMerge1369 : Integer.Sparse Master := [(Sum.inr 3671, 2856821572837048320000), (Sum.inr 3672, 8029997437000089600000)]

def originalMerge1369 : Integer.Sparse OriginalKey := originalTerm1377 ++ originalTerm1378

theorem reducedMerge1369Check : reducedMerge1369 = Integer.Sparse.mergeBy masterLess reducedTerm1377 reducedTerm1378 := by decide +kernel

def reducedMerge1370 : Integer.Sparse Master := [(Sum.inr 3670, -3558260895488409600000), (Sum.inr 3671, 2856821572837048320000), (Sum.inr 3672, 8029997437000089600000)]

def originalMerge1370 : Integer.Sparse OriginalKey := originalMerge1368 ++ originalMerge1369

theorem reducedMerge1370Check : reducedMerge1370 = Integer.Sparse.mergeBy masterLess reducedMerge1368 reducedMerge1369 := by decide +kernel

def reducedMerge1371 : Integer.Sparse Master := [(Sum.inr 3632, -3609060248797839360000), (Sum.inr 3633, 17665403553650442240000), (Sum.inr 3670, -3558260895488409600000), (Sum.inr 3671, 2856821572837048320000), (Sum.inr 3672, 8029997437000089600000)]

def originalMerge1371 : Integer.Sparse OriginalKey := originalMerge1367 ++ originalMerge1370

theorem reducedMerge1371Check : reducedMerge1371 = Integer.Sparse.mergeBy masterLess reducedMerge1367 reducedMerge1370 := by decide +kernel

def reducedMerge1372 : Integer.Sparse Master := [(Sum.inr 3619, -9131775422933237760000), (Sum.inr 3622, 13643436319594905600000), (Sum.inr 3623, -6320730118534594560000), (Sum.inr 3625, 3684922744987975680000), (Sum.inr 3626, 5131131445562572800000), (Sum.inr 3627, 7417776676181114880000), (Sum.inr 3632, -3609060248797839360000), (Sum.inr 3633, 17665403553650442240000), (Sum.inr 3670, -3558260895488409600000), (Sum.inr 3671, 2856821572837048320000), (Sum.inr 3672, 8029997437000089600000)]

def originalMerge1372 : Integer.Sparse OriginalKey := originalMerge1364 ++ originalMerge1371

theorem reducedMerge1372Check : reducedMerge1372 = Integer.Sparse.mergeBy masterLess reducedMerge1364 reducedMerge1371 := by decide +kernel

def reducedMerge1373 : Integer.Sparse Master := [(Sum.inr 3565, 5653339486845861888000), (Sum.inr 3569, 1962225745433985024000), (Sum.inr 3570, 2433073703307706368000), (Sum.inr 3571, 12926463385317801984000), (Sum.inr 3572, -16798163909915049984000), (Sum.inr 3573, 19725678159807578112000), (Sum.inr 3577, 4629005356695552000000), (Sum.inr 3578, 13978224602687471616000), (Sum.inr 3579, 4549640633792593920000), (Sum.inr 3580, 831414264535056384000), (Sum.inr 3581, -220499962681098240000), (Sum.inr 3582, 4158174109630464000000), (Sum.inr 3583, -11906431827880181760000), (Sum.inr 3584, 29008204646800490496000), (Sum.inr 3619, -9131775422933237760000), (Sum.inr 3622, 13643436319594905600000), (Sum.inr 3623, -6320730118534594560000), (Sum.inr 3625, 3684922744987975680000), (Sum.inr 3626, 5131131445562572800000), (Sum.inr 3627, 7417776676181114880000), (Sum.inr 3632, -3609060248797839360000), (Sum.inr 3633, 17665403553650442240000), (Sum.inr 3670, -3558260895488409600000), (Sum.inr 3671, 2856821572837048320000), (Sum.inr 3672, 8029997437000089600000)]

def originalMerge1373 : Integer.Sparse OriginalKey := originalMerge1358 ++ originalMerge1372

theorem reducedMerge1373Check : reducedMerge1373 = Integer.Sparse.mergeBy masterLess reducedMerge1358 reducedMerge1372 := by decide +kernel

def reducedMerge1374 : Integer.Sparse Master := [(Sum.inr 3517, 3031883170345451520000), (Sum.inr 3519, -500927005576101888000), (Sum.inr 3523, -12294580299389337600000), (Sum.inr 3524, -1072771597873446912000), (Sum.inr 3526, -8846701964077694976000), (Sum.inr 3529, 2431584286271078400000), (Sum.inr 3530, 6558674437762449408000), (Sum.inr 3532, -1598770106249379840000), (Sum.inr 3533, -1975281871324446720000), (Sum.inr 3534, 26110149656309268480000), (Sum.inr 3535, 4491472530225364992000), (Sum.inr 3537, 7698731041103413248000), (Sum.inr 3538, 1252704393088598016000), (Sum.inr 3539, 6590198986965909504000), (Sum.inr 3540, 442881254805405696000), (Sum.inr 3541, -2683554743866687488000), (Sum.inr 3542, -1438088403369590784000), (Sum.inr 3543, -3946797413223727104000), (Sum.inr 3544, -2488508247260528640000), (Sum.inr 3548, -1028860950356951040000), (Sum.inr 3549, 1255758373127946240000), (Sum.inr 3553, -1133832859511095296000), (Sum.inr 3554, -5933039869919232000000), (Sum.inr 3555, -5743947411554107392000), (Sum.inr 3556, -1645301575619444736000), (Sum.inr 3557, 900394580334477312000), (Sum.inr 3558, 8704054146298871808000), (Sum.inr 3562, 2987270009704415232000), (Sum.inr 3565, 5653339486845861888000), (Sum.inr 3569, 1962225745433985024000), (Sum.inr 3570, 2433073703307706368000), (Sum.inr 3571, 12926463385317801984000), (Sum.inr 3572, -16798163909915049984000), (Sum.inr 3573, 19725678159807578112000), (Sum.inr 3577, 4629005356695552000000), (Sum.inr 3578, 13978224602687471616000), (Sum.inr 3579, 4549640633792593920000), (Sum.inr 3580, 831414264535056384000), (Sum.inr 3581, -220499962681098240000), (Sum.inr 3582, 4158174109630464000000), (Sum.inr 3583, -11906431827880181760000), (Sum.inr 3584, 29008204646800490496000), (Sum.inr 3619, -9131775422933237760000), (Sum.inr 3622, 13643436319594905600000), (Sum.inr 3623, -6320730118534594560000), (Sum.inr 3625, 3684922744987975680000), (Sum.inr 3626, 5131131445562572800000), (Sum.inr 3627, 7417776676181114880000), (Sum.inr 3632, -3609060248797839360000), (Sum.inr 3633, 17665403553650442240000), (Sum.inr 3670, -3558260895488409600000), (Sum.inr 3671, 2856821572837048320000), (Sum.inr 3672, 8029997437000089600000)]

def originalMerge1374 : Integer.Sparse OriginalKey := originalMerge1344 ++ originalMerge1373

theorem reducedMerge1374Check : reducedMerge1374 = Integer.Sparse.mergeBy masterLess reducedMerge1344 reducedMerge1373 := by decide +kernel

def reducedMerge1375 : Integer.Sparse Master := [(Sum.inr 3674, -3375760173907968000000), (Sum.inr 3676, 2139241300593868800000)]

def originalMerge1375 : Integer.Sparse OriginalKey := originalTerm1380 ++ originalTerm1381

theorem reducedMerge1375Check : reducedMerge1375 = Integer.Sparse.mergeBy masterLess reducedTerm1380 reducedTerm1381 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
