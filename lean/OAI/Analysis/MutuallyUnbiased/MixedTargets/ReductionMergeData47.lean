import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData47
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData48
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData46

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1504 : Integer.Sparse Master := [(Sum.inr 3963, -12658524359512227840000), (Sum.inr 3964, -11253260405800304640000), (Sum.inr 3972, 8806052365250789376000)]

def originalMerge1504 : Integer.Sparse OriginalKey := originalMerge1502 ++ originalMerge1503

theorem reducedMerge1504Check : reducedMerge1504 = Integer.Sparse.mergeBy masterLess reducedMerge1502 reducedMerge1503 := by decide +kernel

def reducedMerge1505 : Integer.Sparse Master := [(Sum.inr 3973, 3649006690387623936000), (Sum.inr 3974, 51911513818286653440000)]

def originalMerge1505 : Integer.Sparse OriginalKey := originalTerm1510 ++ originalTerm1511

theorem reducedMerge1505Check : reducedMerge1505 = Integer.Sparse.mergeBy masterLess reducedTerm1510 reducedTerm1511 := by decide +kernel

def reducedMerge1506 : Integer.Sparse Master := [(Sum.inl 0, -1769633697226752000), (Sum.inl 1, 42028800309135360000), (Sum.inl 2, -11060210607667200000), (Sum.inl 3, -141570695778140160000), (Sum.inl 4, -70785347889070080000), (Sum.inl 12, -70785347889070080000), (Sum.inl 13, -35392673944535040000)]

def originalMerge1506 : Integer.Sparse OriginalKey := originalTerm1512 ++ originalTerm1513

theorem reducedMerge1506Check : reducedMerge1506 = Integer.Sparse.mergeBy masterLess reducedTerm1512 reducedTerm1513 := by decide +kernel

def reducedMerge1507 : Integer.Sparse Master := [(Sum.inl 0, -1769633697226752000), (Sum.inl 1, 42028800309135360000), (Sum.inl 2, -11060210607667200000), (Sum.inl 3, -141570695778140160000), (Sum.inl 4, -70785347889070080000), (Sum.inl 12, -70785347889070080000), (Sum.inl 13, -35392673944535040000), (Sum.inr 3973, 3649006690387623936000), (Sum.inr 3974, 51911513818286653440000)]

def originalMerge1507 : Integer.Sparse OriginalKey := originalMerge1505 ++ originalMerge1506

theorem reducedMerge1507Check : reducedMerge1507 = Integer.Sparse.mergeBy masterLess reducedMerge1505 reducedMerge1506 := by decide +kernel

def reducedMerge1508 : Integer.Sparse Master := [(Sum.inl 0, -1769633697226752000), (Sum.inl 1, 42028800309135360000), (Sum.inl 2, -11060210607667200000), (Sum.inl 3, -141570695778140160000), (Sum.inl 4, -70785347889070080000), (Sum.inl 12, -70785347889070080000), (Sum.inl 13, -35392673944535040000), (Sum.inr 3963, -12658524359512227840000), (Sum.inr 3964, -11253260405800304640000), (Sum.inr 3972, 8806052365250789376000), (Sum.inr 3973, 3649006690387623936000), (Sum.inr 3974, 51911513818286653440000)]

def originalMerge1508 : Integer.Sparse OriginalKey := originalMerge1504 ++ originalMerge1507

theorem reducedMerge1508Check : reducedMerge1508 = Integer.Sparse.mergeBy masterLess reducedMerge1504 reducedMerge1507 := by decide +kernel

def reducedMerge1509 : Integer.Sparse Master := [(Sum.inl 0, -1769633697226752000), (Sum.inl 1, 42028800309135360000), (Sum.inl 2, -11060210607667200000), (Sum.inl 3, -141570695778140160000), (Sum.inl 4, -70785347889070080000), (Sum.inl 12, -70785347889070080000), (Sum.inl 13, -35392673944535040000), (Sum.inr 3955, -3649006690387623936000), (Sum.inr 3957, -10194471562001448960000), (Sum.inr 3958, -15869111358269030400000), (Sum.inr 3959, -22837858583598858240000), (Sum.inr 3960, 6539548315307212800000), (Sum.inr 3961, 9259209259419893760000), (Sum.inr 3963, -12658524359512227840000), (Sum.inr 3964, -11253260405800304640000), (Sum.inr 3972, 8806052365250789376000), (Sum.inr 3973, 3649006690387623936000), (Sum.inr 3974, 51911513818286653440000)]

def originalMerge1509 : Integer.Sparse OriginalKey := originalMerge1501 ++ originalMerge1508

theorem reducedMerge1509Check : reducedMerge1509 = Integer.Sparse.mergeBy masterLess reducedMerge1501 reducedMerge1508 := by decide +kernel

def reducedMerge1510 : Integer.Sparse Master := [(Sum.inl 0, -15242027862129868800), (Sum.inl 1, -92540883448645632000), (Sum.inl 2, 27217906896660480000), (Sum.inl 3, 435486510346567680000), (Sum.inl 4, 174194604138627072000), (Sum.inl 12, 174194604138627072000), (Sum.inl 26, 87097302069313536000), (Sum.inr 3983, -1485688708340121600000)]

def originalMerge1510 : Integer.Sparse OriginalKey := originalTerm1515 ++ originalTerm1516

theorem reducedMerge1510Check : reducedMerge1510 = Integer.Sparse.mergeBy masterLess reducedTerm1515 reducedTerm1516 := by decide +kernel

def reducedMerge1511 : Integer.Sparse Master := [(Sum.inl 0, -15242027862129868800), (Sum.inl 1, -92540883448645632000), (Sum.inl 2, 27217906896660480000), (Sum.inl 3, 435486510346567680000), (Sum.inl 4, 174194604138627072000), (Sum.inl 12, 174194604138627072000), (Sum.inl 26, 87097302069313536000), (Sum.inr 3978, -19036929296722821120000), (Sum.inr 3983, -1485688708340121600000)]

def originalMerge1511 : Integer.Sparse OriginalKey := originalTerm1514 ++ originalMerge1510

theorem reducedMerge1511Check : reducedMerge1511 = Integer.Sparse.mergeBy masterLess reducedTerm1514 reducedMerge1510 := by decide +kernel

def reducedMerge1512 : Integer.Sparse Master := [(Sum.inl 0, -27160729310350540800), (Sum.inl 1, -484814639546044416000), (Sum.inl 2, 111722523467821056000), (Sum.inl 3, 457080568157896704000), (Sum.inl 4, 367612693621899264000), (Sum.inl 12, -99209070013906944000), (Sum.inl 26, 89467874535997440000), (Sum.inl 31, -566030833649713152000)]

def originalMerge1512 : Integer.Sparse OriginalKey := originalTerm1517 ++ originalTerm1518

theorem reducedMerge1512Check : reducedMerge1512 = Integer.Sparse.mergeBy masterLess reducedTerm1517 reducedTerm1518 := by decide +kernel

def reducedMerge1513 : Integer.Sparse Master := [(Sum.inl 0, -90035296257831321600), (Sum.inl 1, 58087287908278272000), (Sum.inl 2, -43565465931208704000), (Sum.inl 3, -232349151633113088000), (Sum.inl 4, -232349151633113088000), (Sum.inl 31, 697047454899339264000)]

def originalMerge1513 : Integer.Sparse OriginalKey := originalTerm1519 ++ originalTerm1520

theorem reducedMerge1513Check : reducedMerge1513 = Integer.Sparse.mergeBy masterLess reducedTerm1519 reducedTerm1520 := by decide +kernel

def reducedMerge1514 : Integer.Sparse Master := [(Sum.inl 0, -117196025568181862400), (Sum.inl 1, -426727351637766144000), (Sum.inl 2, 68157057536612352000), (Sum.inl 3, 224731416524783616000), (Sum.inl 4, 135263541988786176000), (Sum.inl 12, -99209070013906944000), (Sum.inl 26, 89467874535997440000), (Sum.inl 31, 131016621249626112000)]

def originalMerge1514 : Integer.Sparse OriginalKey := originalMerge1512 ++ originalMerge1513

theorem reducedMerge1514Check : reducedMerge1514 = Integer.Sparse.mergeBy masterLess reducedMerge1512 reducedMerge1513 := by decide +kernel

def reducedMerge1515 : Integer.Sparse Master := [(Sum.inl 0, -132438053430311731200), (Sum.inl 1, -519268235086411776000), (Sum.inl 2, 95374964433272832000), (Sum.inl 3, 660217926871351296000), (Sum.inl 4, 309458146127413248000), (Sum.inl 12, 74985534124720128000), (Sum.inl 26, 176565176605310976000), (Sum.inl 31, 131016621249626112000), (Sum.inr 3978, -19036929296722821120000), (Sum.inr 3983, -1485688708340121600000)]

def originalMerge1515 : Integer.Sparse OriginalKey := originalMerge1511 ++ originalMerge1514

theorem reducedMerge1515Check : reducedMerge1515 = Integer.Sparse.mergeBy masterLess reducedMerge1511 reducedMerge1514 := by decide +kernel

def reducedMerge1516 : Integer.Sparse Master := [(Sum.inl 0, -1394517657673728000), (Sum.inl 1, 443818610883551232000), (Sum.inl 2, -109211505648795648000), (Sum.inl 3, -459158305117962240000), (Sum.inl 4, -444283450102775808000), (Sum.inl 12, -111070862525693952000), (Sum.inl 26, -7437427507593216000), (Sum.inl 31, 666425175154163712000)]

def originalMerge1516 : Integer.Sparse OriginalKey := originalTerm1521 ++ originalTerm1522

theorem reducedMerge1516Check : reducedMerge1516 = Integer.Sparse.mergeBy masterLess reducedTerm1521 reducedTerm1522 := by decide +kernel

def reducedMerge1517 : Integer.Sparse Master := [(Sum.inl 0, -112149081358523596800), (Sum.inl 1, 138105772703152128000), (Sum.inl 2, -95195218964428800000), (Sum.inl 3, -149985783791714304000), (Sum.inl 12, -74992891895857152000), (Sum.inl 31, -1159791876708433920000)]

def originalMerge1517 : Integer.Sparse OriginalKey := originalTerm1523 ++ originalTerm1524

theorem reducedMerge1517Check : reducedMerge1517 = Integer.Sparse.mergeBy masterLess reducedTerm1523 reducedTerm1524 := by decide +kernel

def reducedMerge1518 : Integer.Sparse Master := [(Sum.inl 0, -113543599016197324800), (Sum.inl 1, 581924383586703360000), (Sum.inl 2, -204406724613224448000), (Sum.inl 3, -609144088909676544000), (Sum.inl 4, -444283450102775808000), (Sum.inl 12, -186063754421551104000), (Sum.inl 26, -7437427507593216000), (Sum.inl 31, -493366701554270208000)]

def originalMerge1518 : Integer.Sparse OriginalKey := originalMerge1516 ++ originalMerge1517

theorem reducedMerge1518Check : reducedMerge1518 = Integer.Sparse.mergeBy masterLess reducedMerge1516 reducedMerge1517 := by decide +kernel

def reducedMerge1519 : Integer.Sparse Master := []

def originalMerge1519 : Integer.Sparse OriginalKey := originalTerm1525 ++ originalTerm1526

theorem reducedMerge1519Check : reducedMerge1519 = Integer.Sparse.mergeBy masterLess reducedTerm1525 reducedTerm1526 := by decide +kernel

def reducedMerge1520 : Integer.Sparse Master := [(Sum.inr 4010, -41423402361966428160000)]

def originalMerge1520 : Integer.Sparse OriginalKey := originalTerm1527 ++ originalTerm1528

theorem reducedMerge1520Check : reducedMerge1520 = Integer.Sparse.mergeBy masterLess reducedTerm1527 reducedTerm1528 := by decide +kernel

def reducedMerge1521 : Integer.Sparse Master := [(Sum.inr 4010, -41423402361966428160000)]

def originalMerge1521 : Integer.Sparse OriginalKey := originalMerge1519 ++ originalMerge1520

theorem reducedMerge1521Check : reducedMerge1521 = Integer.Sparse.mergeBy masterLess reducedMerge1519 reducedMerge1520 := by decide +kernel

def reducedMerge1522 : Integer.Sparse Master := [(Sum.inl 0, -113543599016197324800), (Sum.inl 1, 581924383586703360000), (Sum.inl 2, -204406724613224448000), (Sum.inl 3, -609144088909676544000), (Sum.inl 4, -444283450102775808000), (Sum.inl 12, -186063754421551104000), (Sum.inl 26, -7437427507593216000), (Sum.inl 31, -493366701554270208000), (Sum.inr 4010, -41423402361966428160000)]

def originalMerge1522 : Integer.Sparse OriginalKey := originalMerge1518 ++ originalMerge1521

theorem reducedMerge1522Check : reducedMerge1522 = Integer.Sparse.mergeBy masterLess reducedMerge1518 reducedMerge1521 := by decide +kernel

def reducedMerge1523 : Integer.Sparse Master := [(Sum.inl 0, -245981652446509056000), (Sum.inl 1, 62656148500291584000), (Sum.inl 2, -109031760179951616000), (Sum.inl 3, 51073837961674752000), (Sum.inl 4, -134825303975362560000), (Sum.inl 12, -111078220296830976000), (Sum.inl 26, 169127749097717760000), (Sum.inl 31, -362350080304644096000), (Sum.inr 3978, -19036929296722821120000), (Sum.inr 3983, -1485688708340121600000), (Sum.inr 4010, -41423402361966428160000)]

def originalMerge1523 : Integer.Sparse OriginalKey := originalMerge1515 ++ originalMerge1522

theorem reducedMerge1523Check : reducedMerge1523 = Integer.Sparse.mergeBy masterLess reducedMerge1515 reducedMerge1522 := by decide +kernel

def reducedMerge1524 : Integer.Sparse Master := [(Sum.inl 0, -247751286143735808000), (Sum.inl 1, 104684948809426944000), (Sum.inl 2, -120091970787618816000), (Sum.inl 3, -90496857816465408000), (Sum.inl 4, -205610651864432640000), (Sum.inl 12, -181863568185901056000), (Sum.inl 13, -35392673944535040000), (Sum.inl 26, 169127749097717760000), (Sum.inl 31, -362350080304644096000), (Sum.inr 3955, -3649006690387623936000), (Sum.inr 3957, -10194471562001448960000), (Sum.inr 3958, -15869111358269030400000), (Sum.inr 3959, -22837858583598858240000), (Sum.inr 3960, 6539548315307212800000), (Sum.inr 3961, 9259209259419893760000), (Sum.inr 3963, -12658524359512227840000), (Sum.inr 3964, -11253260405800304640000), (Sum.inr 3972, 8806052365250789376000), (Sum.inr 3973, 3649006690387623936000), (Sum.inr 3974, 51911513818286653440000), (Sum.inr 3978, -19036929296722821120000), (Sum.inr 3983, -1485688708340121600000), (Sum.inr 4010, -41423402361966428160000)]

def originalMerge1524 : Integer.Sparse OriginalKey := originalMerge1509 ++ originalMerge1523

theorem reducedMerge1524Check : reducedMerge1524 = Integer.Sparse.mergeBy masterLess reducedMerge1509 reducedMerge1523 := by decide +kernel

def reducedMerge1525 : Integer.Sparse Master := [(Sum.inr 4024, 7296061782863314944000), (Sum.inr 4025, -6738341217491681280000)]

def originalMerge1525 : Integer.Sparse OriginalKey := originalTerm1530 ++ originalTerm1531

theorem reducedMerge1525Check : reducedMerge1525 = Integer.Sparse.mergeBy masterLess reducedTerm1530 reducedTerm1531 := by decide +kernel

def reducedMerge1526 : Integer.Sparse Master := [(Sum.inr 4022, 12266190676214415360000), (Sum.inr 4024, 7296061782863314944000), (Sum.inr 4025, -6738341217491681280000)]

def originalMerge1526 : Integer.Sparse OriginalKey := originalTerm1529 ++ originalMerge1525

theorem reducedMerge1526Check : reducedMerge1526 = Integer.Sparse.mergeBy masterLess reducedTerm1529 reducedMerge1525 := by decide +kernel

def reducedMerge1527 : Integer.Sparse Master := [(Sum.inl 0, 18281431960823808000), (Sum.inl 1, 1508692626575253504000), (Sum.inl 2, -220644145628928000000), (Sum.inl 3, -3848267041336295424000), (Sum.inl 4, -2592008086830317568000), (Sum.inl 12, -1780998843099119616000), (Sum.inl 25, 1097278598869254144000), (Sum.inl 26, -811009243731197952000)]

def originalMerge1527 : Integer.Sparse OriginalKey := originalTerm1532 ++ originalTerm1533

theorem reducedMerge1527Check : reducedMerge1527 = Integer.Sparse.mergeBy masterLess reducedTerm1532 reducedTerm1533 := by decide +kernel

def reducedMerge1528 : Integer.Sparse Master := [(Sum.inl 0, -10685907930945945600), (Sum.inl 1, 10434180609183744000), (Sum.inl 2, -32582654185697280000), (Sum.inl 3, 125124264312864768000), (Sum.inl 12, 125124264312864768000), (Sum.inl 25, -594297303987437568000)]

def originalMerge1528 : Integer.Sparse OriginalKey := originalTerm1534 ++ originalTerm1535

theorem reducedMerge1528Check : reducedMerge1528 = Integer.Sparse.mergeBy masterLess reducedTerm1534 reducedTerm1535 := by decide +kernel

def reducedMerge1529 : Integer.Sparse Master := [(Sum.inl 0, 7595524029877862400), (Sum.inl 1, 1519126807184437248000), (Sum.inl 2, -253226799814625280000), (Sum.inl 3, -3723142777023430656000), (Sum.inl 4, -2592008086830317568000), (Sum.inl 12, -1655874578786254848000), (Sum.inl 25, 502981294881816576000), (Sum.inl 26, -811009243731197952000)]

def originalMerge1529 : Integer.Sparse OriginalKey := originalMerge1527 ++ originalMerge1528

theorem reducedMerge1529Check : reducedMerge1529 = Integer.Sparse.mergeBy masterLess reducedMerge1527 reducedMerge1528 := by decide +kernel

def reducedMerge1530 : Integer.Sparse Master := [(Sum.inl 0, 7595524029877862400), (Sum.inl 1, 1519126807184437248000), (Sum.inl 2, -253226799814625280000), (Sum.inl 3, -3723142777023430656000), (Sum.inl 4, -2592008086830317568000), (Sum.inl 12, -1655874578786254848000), (Sum.inl 25, 502981294881816576000), (Sum.inl 26, -811009243731197952000), (Sum.inr 4022, 12266190676214415360000), (Sum.inr 4024, 7296061782863314944000), (Sum.inr 4025, -6738341217491681280000)]

def originalMerge1530 : Integer.Sparse OriginalKey := originalMerge1526 ++ originalMerge1529

theorem reducedMerge1530Check : reducedMerge1530 = Integer.Sparse.mergeBy masterLess reducedMerge1526 reducedMerge1529 := by decide +kernel

def reducedMerge1531 : Integer.Sparse Master := [(Sum.inl 0, 45605150947735142400), (Sum.inl 2, 87702213361029120000), (Sum.inl 3, -561294165510586368000), (Sum.inl 4, -280647082755293184000), (Sum.inl 25, 420970624132939776000), (Sum.inl 26, -280647082755293184000)]

def originalMerge1531 : Integer.Sparse OriginalKey := originalTerm1536 ++ originalTerm1537

theorem reducedMerge1531Check : reducedMerge1531 = Integer.Sparse.mergeBy masterLess reducedTerm1536 reducedTerm1537 := by decide +kernel

def reducedMerge1532 : Integer.Sparse Master := []

def originalMerge1532 : Integer.Sparse OriginalKey := originalTerm1538 ++ originalTerm1539

theorem reducedMerge1532Check : reducedMerge1532 = Integer.Sparse.mergeBy masterLess reducedTerm1538 reducedTerm1539 := by decide +kernel

def reducedMerge1533 : Integer.Sparse Master := [(Sum.inl 0, 45605150947735142400), (Sum.inl 2, 87702213361029120000), (Sum.inl 3, -561294165510586368000), (Sum.inl 4, -280647082755293184000), (Sum.inl 25, 420970624132939776000), (Sum.inl 26, -280647082755293184000)]

def originalMerge1533 : Integer.Sparse OriginalKey := originalMerge1531 ++ originalMerge1532

theorem reducedMerge1533Check : reducedMerge1533 = Integer.Sparse.mergeBy masterLess reducedMerge1531 reducedMerge1532 := by decide +kernel

def reducedMerge1534 : Integer.Sparse Master := [(Sum.inr 4046, -8408006041455820800000)]

def originalMerge1534 : Integer.Sparse OriginalKey := originalTerm1540 ++ originalTerm1541

theorem reducedMerge1534Check : reducedMerge1534 = Integer.Sparse.mergeBy masterLess reducedTerm1540 reducedTerm1541 := by decide +kernel

def reducedMerge1535 : Integer.Sparse Master := [(Sum.inr 4047, -3803939670426255360000)]

def originalMerge1535 : Integer.Sparse OriginalKey := originalTerm1542 ++ originalTerm1543

theorem reducedMerge1535Check : reducedMerge1535 = Integer.Sparse.mergeBy masterLess reducedTerm1542 reducedTerm1543 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
