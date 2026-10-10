import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SupportedContraction

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA5_5_6I1PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 5 5 6)) (shape 5 5 6) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) a
def CA5_5_6I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 5 5 6) A5_5_6Law 1 a
lemma CA5_5_6I1PairRaw_sound (a : PairSlot × PairSlot) :
    (CA5_5_6I1PairRaw a).Encloses (CA5_5_6I1PairValue a) := by
  exact stageAPairBall_sound (shape 5 5 6) (by decide +kernel) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (fun u _ => A5_5_6Law_sound u) 1 a
def CA5_5_6I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(93537288070256079402972541309 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(652381924125339307024405155381 / 100000000000000000000000000000000), (237687503 / 100000000000000000000000000000000)⟩ ⟨(-697456530528588441793418937411939 / 100000000000000000000000000000000), (50821977053 / 20000000000000000000000000000000)⟩ ⟨-11, 93537288070256079402972541309, 48828125000000000000000000000⟩,
   .log ⟨(1613642536704346184787405822127 / 50000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩ ⟨(11080976686687357950484078695309 / 100000000000000000000000000000000), (2050212633 / 50000000000000000000000000000000)⟩ ⟨(-85838223418728811451671099437089 / 25000000000000000000000000000000), (63527471343 / 50000000000000000000000000000000)⟩ ⟨-5, 1613642536704346184787405822127, 1562500000000000000000000000000⟩,
   .log ⟨(105748458053799922176503947421 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1302549239761697377852668102557 / 100000000000000000000000000000000), (111965539 / 25000000000000000000000000000000)⟩ ⟨(-307935752382086885208266943192763 / 50000000000000000000000000000000), (8470329511 / 4000000000000000000000000000000)⟩ ⟨-9, 105748458053799922176503947421, 97656250000000000000000000000⟩,
   .log ⟨(839006469603486263195888899 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(32248122419825969306621328061 / 50000000000000000000000000000000), (4263999 / 20000000000000000000000000000000)⟩ ⟨(-960902078474627384583035355219307 / 100000000000000000000000000000000), (317637370143 / 100000000000000000000000000000000)⟩ ⟨-14, 839006469603486263195888899, 762939453125000000000000000⟩,
   .log ⟨(115894106530178325567094543839 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1406282588477668427903360339541 / 100000000000000000000000000000000), (61353831 / 12500000000000000000000000000000)⟩ ⟨(-606710138496765798101697242384949 / 100000000000000000000000000000000), (52939559423 / 25000000000000000000000000000000)⟩ ⟨-9, 115894106530178325567094543839, 97656250000000000000000000000⟩,
   .log ⟨(14720923342416175865597814517 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(129892358078622649085042416827 / 100000000000000000000000000000000), (8728377 / 20000000000000000000000000000000)⟩ ⟨(-220591390664261052584519050398637 / 25000000000000000000000000000000), (148230769177 / 50000000000000000000000000000000)⟩ ⟨-13, 14720923342416175865597814517, 12207031250000000000000000000⟩,
   .log ⟨(342478869926790246694714177923 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(972077555150069540765137454643 / 50000000000000000000000000000000), (725227237 / 100000000000000000000000000000000)⟩ ⟨(-283835775140774381653923397150353 / 50000000000000000000000000000000), (105879118853 / 50000000000000000000000000000000)⟩ ⟨-9, 342478869926790246694714177923, 195312500000000000000000000000⟩,
   .log ⟨(5908704031647045563643605658289 / 50000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩ ⟨(12618607543410798900927802926913 / 50000000000000000000000000000000), (6256083811 / 50000000000000000000000000000000)⟩ ⟨(-213559648204165917402503523662071 / 100000000000000000000000000000000), (26469779701 / 25000000000000000000000000000000)⟩ ⟨-4, 5908704031647045563643605658289, 3125000000000000000000000000000⟩,
   .log ⟨(77270193648899215581010397217 / 10000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(1878837154219123850744917697371 / 50000000000000000000000000000000), (1472634021 / 100000000000000000000000000000000)⟩ ⟨(-243151604195040036693364802809577 / 50000000000000000000000000000000), (38116482733 / 20000000000000000000000000000000)⟩ ⟨-8, 77270193648899215581010397217, 39062500000000000000000000000⟩,
   .log ⟨(1589189209993002088149044443 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(17560066412729960079394565853 / 100000000000000000000000000000000), (5720919 / 100000000000000000000000000000000)⟩ ⟨(-1104970150961903706641593068790249 / 100000000000000000000000000000000), (71997813107 / 20000000000000000000000000000000)⟩ ⟨-16, 1589189209993002088149044443, 1525878906250000000000000000⟩,
   .log ⟨(346874733494015276613142148599 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(982342611063375921042667996777 / 50000000000000000000000000000000), (734535847 / 100000000000000000000000000000000)⟩ ⟨(-283198087438768307756480081269003 / 50000000000000000000000000000000), (211758237983 / 100000000000000000000000000000000)⟩ ⟨-9, 346874733494015276613142148599, 195312500000000000000000000000⟩,
   .log ⟨(3326635926250490731224746288949 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩ ⟨(1132123607638928403432988160347 / 10000000000000000000000000000000), (4226655443 / 100000000000000000000000000000000)⟩ ⟨(-170160431249079401322918921789431 / 50000000000000000000000000000000), (15881867841 / 12500000000000000000000000000000)⟩ ⟨-5, 3326635926250490731224746288949, 3125000000000000000000000000000⟩,
   .log ⟨(10232154009125278381983263637 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1050195810943384143989541388881 / 100000000000000000000000000000000), (76269353 / 20000000000000000000000000000000)⟩ ⟨(-320740081342719521173649740126007 / 50000000000000000000000000000000), (116467030867 / 50000000000000000000000000000000)⟩ ⟨-10, 10232154009125278381983263637, 6103515625000000000000000000⟩,
   .log ⟨(8931430846063090726447876807 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(10408855692673650400315948783 / 12500000000000000000000000000000), (7092393 / 25000000000000000000000000000000)⟩ ⟨(-932334885379472895606571449505183 / 100000000000000000000000000000000), (317637366441 / 100000000000000000000000000000000)⟩ ⟨-14, 8931430846063090726447876807, 6103515625000000000000000000⟩,
   .log ⟨(1217655791446770390904187641 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(517399029813141660603578609 / 2000000000000000000000000000000), (4383433 / 50000000000000000000000000000000)⟩ ⟨(-531142537825066128646635079222143 / 50000000000000000000000000000000), (359989043673 / 100000000000000000000000000000000)⟩ ⟨-16, 1217655791446770390904187641, 762939453125000000000000000⟩,
   .log ⟨(63826366823931803670370729979 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(425314137905799802263071395953 / 50000000000000000000000000000000), (1858417 / 625000000000000000000000000000)⟩ ⟨(-666361190633096713230454251391847 / 100000000000000000000000000000000), (232934062863 / 100000000000000000000000000000000)⟩ ⟨-10, 63826366823931803670370729979, 48828125000000000000000000000⟩,
   .log ⟨(6318022770492013635887522281 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(61092242223303530802112754089 / 100000000000000000000000000000000), (5017103 / 25000000000000000000000000000000)⟩ ⟨(-966951915853035071028086549271659 / 100000000000000000000000000000000), (4963083923 / 1562500000000000000000000000000)⟩ ⟨-14, 6318022770492013635887522281, 6103515625000000000000000000⟩]
lemma CA5_5_6I1PairCertificates_valid :
    CA5_5_6I1PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I1PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 2, 0, 4, 0 => 1
  | 2, 0, 2, 1 => 2
  | 2, 0, 3, 1 => 3
  | 2, 0, 1, 2 => 2
  | 2, 0, 1, 3 => 3
  | 2, 0, 0, 4 => 1
  | 3, 0, 4, 0 => 4
  | 3, 0, 2, 1 => 5
  | 3, 0, 3, 1 => 6
  | 3, 0, 1, 2 => 5
  | 3, 0, 1, 3 => 6
  | 3, 0, 0, 4 => 4
  | 1, 1, 4, 0 => 7
  | 1, 1, 2, 1 => 8
  | 1, 1, 3, 1 => 9
  | 1, 1, 1, 2 => 8
  | 1, 1, 1, 3 => 9
  | 1, 1, 0, 4 => 7
  | 0, 2, 4, 0 => 1
  | 0, 2, 2, 1 => 2
  | 0, 2, 3, 1 => 3
  | 0, 2, 1, 2 => 2
  | 0, 2, 1, 3 => 3
  | 0, 2, 0, 4 => 1
  | 0, 3, 4, 0 => 4
  | 0, 3, 2, 1 => 5
  | 0, 3, 3, 1 => 6
  | 0, 3, 1, 2 => 5
  | 0, 3, 1, 3 => 6
  | 0, 3, 0, 4 => 4
  | 4, 0, 2, 0 => 1
  | 4, 0, 3, 0 => 4
  | 4, 0, 1, 1 => 7
  | 4, 0, 0, 2 => 1
  | 4, 0, 0, 3 => 4
  | 2, 1, 2, 0 => 2
  | 2, 1, 3, 0 => 5
  | 2, 1, 1, 1 => 8
  | 2, 1, 0, 2 => 2
  | 2, 1, 0, 3 => 5
  | 3, 1, 2, 0 => 3
  | 3, 1, 3, 0 => 6
  | 3, 1, 1, 1 => 9
  | 3, 1, 0, 2 => 3
  | 3, 1, 0, 3 => 6
  | 1, 2, 2, 0 => 2
  | 1, 2, 3, 0 => 5
  | 1, 2, 1, 1 => 8
  | 1, 2, 0, 2 => 2
  | 1, 2, 0, 3 => 5
  | 1, 3, 2, 0 => 3
  | 1, 3, 3, 0 => 6
  | 1, 3, 1, 1 => 9
  | 1, 3, 0, 2 => 3
  | 1, 3, 0, 3 => 6
  | 0, 4, 2, 0 => 1
  | 0, 4, 3, 0 => 4
  | 0, 4, 1, 1 => 7
  | 0, 4, 0, 2 => 1
  | 0, 4, 0, 3 => 4
  | 0, 5, 1, 0 => 10
  | 0, 5, 0, 1 => 10
  | 1, 4, 1, 0 => 11
  | 1, 4, 0, 1 => 11
  | 2, 2, 1, 0 => 12
  | 2, 2, 0, 1 => 12
  | 2, 3, 1, 0 => 13
  | 2, 3, 0, 1 => 13
  | 3, 2, 1, 0 => 13
  | 3, 2, 0, 1 => 13
  | 3, 3, 1, 0 => 14
  | 3, 3, 0, 1 => 14
  | 4, 1, 1, 0 => 11
  | 4, 1, 0, 1 => 11
  | 5, 0, 1, 0 => 10
  | 5, 0, 0, 1 => 10
  | 1, 5, 0, 0 => 15
  | 2, 4, 0, 0 => 16
  | 3, 4, 0, 0 => 17
  | 4, 2, 0, 0 => 16
  | 4, 3, 0, 0 => 17
  | 5, 1, 0, 0 => 15
  | 0, 1, 5, 0 => 10
  | 0, 1, 4, 1 => 11
  | 0, 1, 2, 2 => 12
  | 0, 1, 2, 3 => 13
  | 0, 1, 3, 2 => 13
  | 0, 1, 3, 3 => 14
  | 0, 1, 1, 4 => 11
  | 0, 1, 0, 5 => 10
  | 1, 0, 5, 0 => 10
  | 1, 0, 4, 1 => 11
  | 1, 0, 2, 2 => 12
  | 1, 0, 2, 3 => 13
  | 1, 0, 3, 2 => 13
  | 1, 0, 3, 3 => 14
  | 1, 0, 1, 4 => 11
  | 1, 0, 0, 5 => 10
  | 0, 0, 1, 5 => 15
  | 0, 0, 2, 4 => 16
  | 0, 0, 3, 4 => 17
  | 0, 0, 4, 2 => 16
  | 0, 0, 4, 3 => 17
  | 0, 0, 5, 1 => 15
  | _, _, _, _ => 0
def CA5_5_6I1PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1PairCertificates (CA5_5_6I1PairCertificateIndex a)).input
lemma CA5_5_6I1PairP_check_0_0 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((0,0),(k,l))) (CA5_5_6I1PairP ((0,0),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_0_1 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((0,1),(k,l))) (CA5_5_6I1PairP ((0,1),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_0_2 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((0,2),(k,l))) (CA5_5_6I1PairP ((0,2),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_0_3 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((0,3),(k,l))) (CA5_5_6I1PairP ((0,3),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_0_4 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((0,4),(k,l))) (CA5_5_6I1PairP ((0,4),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_0_5 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((0,5),(k,l))) (CA5_5_6I1PairP ((0,5),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_1_0 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((1,0),(k,l))) (CA5_5_6I1PairP ((1,0),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_1_1 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((1,1),(k,l))) (CA5_5_6I1PairP ((1,1),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_1_2 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((1,2),(k,l))) (CA5_5_6I1PairP ((1,2),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_1_3 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((1,3),(k,l))) (CA5_5_6I1PairP ((1,3),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_1_4 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((1,4),(k,l))) (CA5_5_6I1PairP ((1,4),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_1_5 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((1,5),(k,l))) (CA5_5_6I1PairP ((1,5),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_2_0 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((2,0),(k,l))) (CA5_5_6I1PairP ((2,0),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_2_1 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((2,1),(k,l))) (CA5_5_6I1PairP ((2,1),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_2_2 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((2,2),(k,l))) (CA5_5_6I1PairP ((2,2),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_2_3 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((2,3),(k,l))) (CA5_5_6I1PairP ((2,3),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_2_4 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((2,4),(k,l))) (CA5_5_6I1PairP ((2,4),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_2_5 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((2,5),(k,l))) (CA5_5_6I1PairP ((2,5),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_3_0 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((3,0),(k,l))) (CA5_5_6I1PairP ((3,0),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_3_1 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((3,1),(k,l))) (CA5_5_6I1PairP ((3,1),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_3_2 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((3,2),(k,l))) (CA5_5_6I1PairP ((3,2),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_3_3 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((3,3),(k,l))) (CA5_5_6I1PairP ((3,3),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_3_4 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((3,4),(k,l))) (CA5_5_6I1PairP ((3,4),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_3_5 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((3,5),(k,l))) (CA5_5_6I1PairP ((3,5),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_4_0 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((4,0),(k,l))) (CA5_5_6I1PairP ((4,0),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_4_1 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((4,1),(k,l))) (CA5_5_6I1PairP ((4,1),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_4_2 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((4,2),(k,l))) (CA5_5_6I1PairP ((4,2),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_4_3 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((4,3),(k,l))) (CA5_5_6I1PairP ((4,3),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_4_4 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((4,4),(k,l))) (CA5_5_6I1PairP ((4,4),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_4_5 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((4,5),(k,l))) (CA5_5_6I1PairP ((4,5),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_5_0 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((5,0),(k,l))) (CA5_5_6I1PairP ((5,0),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_5_1 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((5,1),(k,l))) (CA5_5_6I1PairP ((5,1),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_5_2 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((5,2),(k,l))) (CA5_5_6I1PairP ((5,2),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_5_3 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((5,3),(k,l))) (CA5_5_6I1PairP ((5,3),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_5_4 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((5,4),(k,l))) (CA5_5_6I1PairP ((5,4),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check_5_5 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((5,5),(k,l))) (CA5_5_6I1PairP ((5,5),(k,l))) = true := by
  decide +kernel
lemma CA5_5_6I1PairP_check (a : PairSlot × PairSlot) : contains (CA5_5_6I1PairRaw a) (CA5_5_6I1PairP a) = true := by
  rcases a with ⟨⟨i,j⟩,⟨k,l⟩⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (CA5_5_6I1PairP_check_0_0 k l) (CA5_5_6I1PairP_check_0_1 k l) (CA5_5_6I1PairP_check_0_2 k l) (CA5_5_6I1PairP_check_0_3 k l) (CA5_5_6I1PairP_check_0_4 k l) (CA5_5_6I1PairP_check_0_5 k l)
  · exact forall_fin6 (CA5_5_6I1PairP_check_1_0 k l) (CA5_5_6I1PairP_check_1_1 k l) (CA5_5_6I1PairP_check_1_2 k l) (CA5_5_6I1PairP_check_1_3 k l) (CA5_5_6I1PairP_check_1_4 k l) (CA5_5_6I1PairP_check_1_5 k l)
  · exact forall_fin6 (CA5_5_6I1PairP_check_2_0 k l) (CA5_5_6I1PairP_check_2_1 k l) (CA5_5_6I1PairP_check_2_2 k l) (CA5_5_6I1PairP_check_2_3 k l) (CA5_5_6I1PairP_check_2_4 k l) (CA5_5_6I1PairP_check_2_5 k l)
  · exact forall_fin6 (CA5_5_6I1PairP_check_3_0 k l) (CA5_5_6I1PairP_check_3_1 k l) (CA5_5_6I1PairP_check_3_2 k l) (CA5_5_6I1PairP_check_3_3 k l) (CA5_5_6I1PairP_check_3_4 k l) (CA5_5_6I1PairP_check_3_5 k l)
  · exact forall_fin6 (CA5_5_6I1PairP_check_4_0 k l) (CA5_5_6I1PairP_check_4_1 k l) (CA5_5_6I1PairP_check_4_2 k l) (CA5_5_6I1PairP_check_4_3 k l) (CA5_5_6I1PairP_check_4_4 k l) (CA5_5_6I1PairP_check_4_5 k l)
  · exact forall_fin6 (CA5_5_6I1PairP_check_5_0 k l) (CA5_5_6I1PairP_check_5_1 k l) (CA5_5_6I1PairP_check_5_2 k l) (CA5_5_6I1PairP_check_5_3 k l) (CA5_5_6I1PairP_check_5_4 k l) (CA5_5_6I1PairP_check_5_5 k l)
lemma CA5_5_6I1PairP_sound (a : PairSlot × PairSlot) :
    (CA5_5_6I1PairP a).Encloses (CA5_5_6I1PairValue a) :=
  contains_sound (CA5_5_6I1PairRaw_sound a) (CA5_5_6I1PairP_check a)
def CA5_5_6I1PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1PairCertificates (CA5_5_6I1PairCertificateIndex a)).output
lemma CA5_5_6I1PairTerms_sound (a : PairSlot × PairSlot) :
    (CA5_5_6I1PairTerms a).Encloses (Foundation.entropyTerm (CA5_5_6I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1PairCertificates_valid
    (CA5_5_6I1PairCertificateIndex a) (CA5_5_6I1PairP_sound a)
def CA5_5_6I1PairEntropy : Ball := ⟨(78619182179922625235000698456083 / 25000000000000000000000000000000), (32217977861 / 25000000000000000000000000000000)⟩
lemma CA5_5_6I1PairEntropy_sound : CA5_5_6I1PairEntropy.Encloses (Foundation.finiteEntropy CA5_5_6I1PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA5_5_6I1PairValue CA5_5_6I1PairTerms CA5_5_6I1PairTerms_sound) (by decide +kernel)
def CA5_5_6I1PairMass : Ball := ⟨1, (73 / 12500000000000000000000000000000)⟩
lemma CA5_5_6I1PairMass_sound : CA5_5_6I1PairMass.Encloses (∑ a, CA5_5_6I1PairValue a) := by
  exact contains_sound (doublePairSumBall_sound CA5_5_6I1PairP CA5_5_6I1PairValue CA5_5_6I1PairP_sound) (by decide +kernel)
def CA5_5_6I1PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA5_5_6I1PairMassTermLog : Ball := ⟨0, (10587912133 / 50000000000000000000000000000000)⟩
lemma CA5_5_6I1PairMassTermLog_sound : CA5_5_6I1PairMassTermLog.Encloses (Real.log ((∑ a, CA5_5_6I1PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA5_5_6I1PairMass_sound) (w := CA5_5_6I1PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA5_5_6I1PairMassTerm : Ball := ⟨0, (21175824267 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I1PairMassTerm_sound : CA5_5_6I1PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA5_5_6I1PairMass_sound) CA5_5_6I1PairMassTermLog_sound) (by decide +kernel)
def CA5_5_6I1PairH : Ball := ⟨(78619182179922625235000698456083 / 25000000000000000000000000000000), (150047735711 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I1PairH_sound : CA5_5_6I1PairH.Encloses (homogeneousEntropy CA5_5_6I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1PairValue CA5_5_6I1PairMassTerm_sound CA5_5_6I1PairEntropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA5_5_6I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA5_5_6I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
lemma CA5_5_6I1R0Raw_sound (a : PairSlot) :
    (CA5_5_6I1R0Raw a).Encloses (CA5_5_6I1R0Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 0 a
def CA5_5_6I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(272812136002498323516874715041 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(402680401197399720458807296919 / 25000000000000000000000000000000), (144425551 / 25000000000000000000000000000000)⟩ ⟨(-18450443916180478597926154971713 / 3125000000000000000000000000000), (105879119331 / 50000000000000000000000000000000)⟩ ⟨-9, 272812136002498323516874715041, 195312500000000000000000000000⟩]
lemma CA5_5_6I1R0Certificates_valid :
    CA5_5_6I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA5_5_6I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R0Certificates (CA5_5_6I1R0CertificateIndex a)).input
lemma CA5_5_6I1R0P_check : ∀ a : PairSlot, contains (CA5_5_6I1R0Raw a) (CA5_5_6I1R0P a) = true := by
  decide +kernel
lemma CA5_5_6I1R0P_sound (a : PairSlot) :
    (CA5_5_6I1R0P a).Encloses (CA5_5_6I1R0Value a) :=
  contains_sound (CA5_5_6I1R0Raw_sound a) (CA5_5_6I1R0P_check a)
def CA5_5_6I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R0Certificates (CA5_5_6I1R0CertificateIndex a)).output
lemma CA5_5_6I1R0Terms_sound (a : PairSlot) :
    (CA5_5_6I1R0Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R0Certificates_valid
    (CA5_5_6I1R0CertificateIndex a) (CA5_5_6I1R0P_sound a)
def CA5_5_6I1R0Entropy : Ball := ⟨(402680401197399720458807296919 / 25000000000000000000000000000000), (144425551 / 25000000000000000000000000000000)⟩
lemma CA5_5_6I1R0Entropy_sound : CA5_5_6I1R0Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R0Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R0Value CA5_5_6I1R0Terms CA5_5_6I1R0Terms_sound) (by decide +kernel)
def CA5_5_6I1R0Mass : Ball := ⟨(272812136002498323516874715041 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
lemma CA5_5_6I1R0Mass_sound : CA5_5_6I1R0Mass.Encloses (∑ a, CA5_5_6I1R0Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R0P CA5_5_6I1R0Value CA5_5_6I1R0P_sound) (by decide +kernel)
def CA5_5_6I1R0MassTermLogWitness : LogWitness := ⟨-9, 272812136002498323516874715041, 195312500000000000000000000000⟩
def CA5_5_6I1R0MassTermLog : Ball := ⟨(-18450443916180478597926154971713 / 3125000000000000000000000000000), (105879119331 / 50000000000000000000000000000000)⟩
lemma CA5_5_6I1R0MassTermLog_sound : CA5_5_6I1R0MassTermLog.Encloses (Real.log ((∑ a, CA5_5_6I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA5_5_6I1R0Mass_sound) (w := CA5_5_6I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA5_5_6I1R0MassTerm : Ball := ⟨(402680401197399720458807296919 / 25000000000000000000000000000000), (144425551 / 25000000000000000000000000000000)⟩
lemma CA5_5_6I1R0MassTerm_sound : CA5_5_6I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA5_5_6I1R0Mass_sound) CA5_5_6I1R0MassTermLog_sound) (by decide +kernel)
def CA5_5_6I1R0H : Ball := ⟨0, (144425551 / 12500000000000000000000000000000)⟩
lemma CA5_5_6I1R0H_sound : CA5_5_6I1R0H.Encloses (homogeneousEntropy CA5_5_6I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R0Value CA5_5_6I1R0MassTerm_sound CA5_5_6I1R0Entropy_sound) (by decide +kernel)
def CA5_5_6I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA5_5_6I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
lemma CA5_5_6I1R1Raw_sound (a : PairSlot) :
    (CA5_5_6I1R1Raw a).Encloses (CA5_5_6I1R1Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 1 a
def CA5_5_6I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(4359924130796579287577240988223 / 100000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩ ⟨(1365840203404610014013524827681 / 10000000000000000000000000000000), (692437397 / 12500000000000000000000000000000)⟩ ⟨(-313271552997199605743781525828231 / 100000000000000000000000000000000), (1016439541 / 800000000000000000000000000000)⟩ ⟨-5, 4359924130796579287577240988223, 3125000000000000000000000000000⟩]
lemma CA5_5_6I1R1Certificates_valid :
    CA5_5_6I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 1 => 1
  | 1, 0 => 1
  | _, _ => 0
def CA5_5_6I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R1Certificates (CA5_5_6I1R1CertificateIndex a)).input
lemma CA5_5_6I1R1P_check : ∀ a : PairSlot, contains (CA5_5_6I1R1Raw a) (CA5_5_6I1R1P a) = true := by
  decide +kernel
lemma CA5_5_6I1R1P_sound (a : PairSlot) :
    (CA5_5_6I1R1P a).Encloses (CA5_5_6I1R1Value a) :=
  contains_sound (CA5_5_6I1R1Raw_sound a) (CA5_5_6I1R1P_check a)
def CA5_5_6I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R1Certificates (CA5_5_6I1R1CertificateIndex a)).output
lemma CA5_5_6I1R1Terms_sound (a : PairSlot) :
    (CA5_5_6I1R1Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R1Certificates_valid
    (CA5_5_6I1R1CertificateIndex a) (CA5_5_6I1R1P_sound a)
def CA5_5_6I1R1Entropy : Ball := ⟨(1365840203404610014013524827681 / 5000000000000000000000000000000), (692437397 / 6250000000000000000000000000000)⟩
lemma CA5_5_6I1R1Entropy_sound : CA5_5_6I1R1Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R1Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R1Value CA5_5_6I1R1Terms CA5_5_6I1R1Terms_sound) (by decide +kernel)
def CA5_5_6I1R1Mass : Ball := ⟨(4359924130796579287577240988223 / 50000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
lemma CA5_5_6I1R1Mass_sound : CA5_5_6I1R1Mass.Encloses (∑ a, CA5_5_6I1R1Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R1P CA5_5_6I1R1Value CA5_5_6I1R1P_sound) (by decide +kernel)
def CA5_5_6I1R1MassTermLogWitness : LogWitness := ⟨-4, 4359924130796579287577240988223, 3125000000000000000000000000000⟩
def CA5_5_6I1R1MassTermLog : Ball := ⟨(-243956834941205074802058332777901 / 100000000000000000000000000000000), (52939559471 / 50000000000000000000000000000000)⟩
lemma CA5_5_6I1R1MassTermLog_sound : CA5_5_6I1R1MassTermLog.Encloses (Real.log ((∑ a, CA5_5_6I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA5_5_6I1R1Mass_sound) (w := CA5_5_6I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA5_5_6I1R1MassTerm : Ball := ⟨(4254533166131672394740051234551 / 20000000000000000000000000000000), (73859989 / 800000000000000000000000000000)⟩
lemma CA5_5_6I1R1MassTerm_sound : CA5_5_6I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA5_5_6I1R1Mass_sound) CA5_5_6I1R1MassTermLog_sound) (by decide +kernel)
def CA5_5_6I1R1H : Ball := ⟨(1208827647486767661314048076173 / 20000000000000000000000000000000), (20311496977 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I1R1H_sound : CA5_5_6I1R1H.Encloses (homogeneousEntropy CA5_5_6I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R1Value CA5_5_6I1R1MassTerm_sound CA5_5_6I1R1Entropy_sound) (by decide +kernel)
def CA5_5_6I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA5_5_6I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
lemma CA5_5_6I1R2Raw_sound (a : PairSlot) :
    (CA5_5_6I1R2Raw a).Encloses (CA5_5_6I1R2Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 2 a
def CA5_5_6I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(706463855517309658666158416081 / 10000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩ ⟨(18721774905585311917576443552047 / 100000000000000000000000000000000), (149599543 / 2000000000000000000000000000000)⟩ ⟨(-265006833107919618614468150433133 / 100000000000000000000000000000000), (10587911891 / 10000000000000000000000000000000)⟩ ⟨-4, 706463855517309658666158416081, 625000000000000000000000000000⟩,
   .log ⟨(20257695052768057368428321071 / 4000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(1338404367096807668078744925419 / 50000000000000000000000000000000), (60324383 / 6250000000000000000000000000000)⟩ ⟨(-528551491612635391787962770436149 / 100000000000000000000000000000000), (11911400871 / 6250000000000000000000000000000)⟩ ⟨-8, 20257695052768057368428321071, 15625000000000000000000000000⟩,
   .log ⟨(12932588869709873529792029466671 / 50000000000000000000000000000000), (39 / 50000000000000000000000000000000)⟩ ⟨(34976771429046153962921539625079 / 100000000000000000000000000000000), (4107873371 / 25000000000000000000000000000000)⟩ ⟨(-135227261074413224277923572694637 / 100000000000000000000000000000000), (1270549427 / 2000000000000000000000000000000)⟩ ⟨-2, 12932588869709873529792029466671, 12500000000000000000000000000000⟩]
lemma CA5_5_6I1R2Certificates_valid :
    CA5_5_6I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA5_5_6I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R2Certificates (CA5_5_6I1R2CertificateIndex a)).input
lemma CA5_5_6I1R2P_check : ∀ a : PairSlot, contains (CA5_5_6I1R2Raw a) (CA5_5_6I1R2P a) = true := by
  decide +kernel
lemma CA5_5_6I1R2P_sound (a : PairSlot) :
    (CA5_5_6I1R2P a).Encloses (CA5_5_6I1R2Value a) :=
  contains_sound (CA5_5_6I1R2Raw_sound a) (CA5_5_6I1R2P_check a)
def CA5_5_6I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R2Certificates (CA5_5_6I1R2CertificateIndex a)).output
lemma CA5_5_6I1R2Terms_sound (a : PairSlot) :
    (CA5_5_6I1R2Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R2Certificates_valid
    (CA5_5_6I1R2CertificateIndex a) (CA5_5_6I1R2P_sound a)
def CA5_5_6I1R2Entropy : Ball := ⟨(77773938708604008470389406430849 / 100000000000000000000000000000000), (833045701 / 2500000000000000000000000000000)⟩
lemma CA5_5_6I1R2Entropy_sound : CA5_5_6I1R2Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R2Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R2Value CA5_5_6I1R2Terms CA5_5_6I1R2Terms_sound) (by decide +kernel)
def CA5_5_6I1R2Mass : Ball := ⟨(1281479362575135721916520103391 / 3125000000000000000000000000000), (39 / 25000000000000000000000000000000)⟩
lemma CA5_5_6I1R2Mass_sound : CA5_5_6I1R2Mass.Encloses (∑ a, CA5_5_6I1R2Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R2P CA5_5_6I1R2Value CA5_5_6I1R2P_sound) (by decide +kernel)
def CA5_5_6I1R2MassTermLogWitness : LogWitness := ⟨-2, 1281479362575135721916520103391, 781250000000000000000000000000⟩
def CA5_5_6I1R2MassTermLog : Ball := ⟨(-17828382412244256628210000201737 / 20000000000000000000000000000000), (63527471429 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I1R2MassTermLog_sound : CA5_5_6I1R2MassTermLog.Encloses (Real.log ((∑ a, CA5_5_6I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA5_5_6I1R2Mass_sound) (w := CA5_5_6I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA5_5_6I1R2MassTerm : Ball := ⟨(36554726607021648898164340666049 / 100000000000000000000000000000000), (2605092609 / 10000000000000000000000000000000)⟩
lemma CA5_5_6I1R2MassTerm_sound : CA5_5_6I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA5_5_6I1R2Mass_sound) CA5_5_6I1R2MassTermLog_sound) (by decide +kernel)
def CA5_5_6I1R2H : Ball := ⟨(25762007563488974732640666103 / 62500000000000000000000000000), (5937275413 / 10000000000000000000000000000000)⟩
lemma CA5_5_6I1R2H_sound : CA5_5_6I1R2H.Encloses (homogeneousEntropy CA5_5_6I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R2Value CA5_5_6I1R2MassTerm_sound CA5_5_6I1R2Entropy_sound) (by decide +kernel)
def CA5_5_6I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA5_5_6I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
lemma CA5_5_6I1R3Raw_sound (a : PairSlot) :
    (CA5_5_6I1R3Raw a).Encloses (CA5_5_6I1R3Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 3 a
def CA5_5_6I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(271458879193725131923505208621 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(1415920722504171364818907810507 / 50000000000000000000000000000000), (1034705791 / 100000000000000000000000000000000)⟩ ⟨(-104319352287143818244296975851629 / 20000000000000000000000000000000), (190582413883 / 100000000000000000000000000000000)⟩ ⟨-8, 271458879193725131923505208621, 195312500000000000000000000000⟩,
   .log ⟨(3746874575659416762664980149143 / 20000000000000000000000000000000), (27 / 50000000000000000000000000000000)⟩ ⟨(15688259651860853458808066430393 / 50000000000000000000000000000000), (793431561 / 5000000000000000000000000000000)⟩ ⟨(-5233781961162877534054015531269 / 3125000000000000000000000000000), (4235164751 / 5000000000000000000000000000000)⟩ ⟨-3, 3746874575659416762664980149143, 2500000000000000000000000000000⟩,
   .log ⟨(1225028089781086675900339639741 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(134820662787370913389849792629 / 2500000000000000000000000000000), (415055667 / 20000000000000000000000000000000)⟩ ⟨(-110055160295518982233674994553211 / 25000000000000000000000000000000), (10587911867 / 6250000000000000000000000000000)⟩ ⟨-7, 1225028089781086675900339639741, 781250000000000000000000000000⟩]
lemma CA5_5_6I1R3Certificates_valid :
    CA5_5_6I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA5_5_6I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R3Certificates (CA5_5_6I1R3CertificateIndex a)).input
lemma CA5_5_6I1R3P_check : ∀ a : PairSlot, contains (CA5_5_6I1R3Raw a) (CA5_5_6I1R3P a) = true := by
  decide +kernel
lemma CA5_5_6I1R3P_sound (a : PairSlot) :
    (CA5_5_6I1R3P a).Encloses (CA5_5_6I1R3Value a) :=
  contains_sound (CA5_5_6I1R3Raw_sound a) (CA5_5_6I1R3P_check a)
def CA5_5_6I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R3Certificates (CA5_5_6I1R3CertificateIndex a)).output
lemma CA5_5_6I1R3Terms_sound (a : PairSlot) :
    (CA5_5_6I1R3Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R3Certificates_valid
    (CA5_5_6I1R3CertificateIndex a) (CA5_5_6I1R3P_sound a)
def CA5_5_6I1R3Entropy : Ball := ⟨(495014840752811077285599252337 / 625000000000000000000000000000), (9489307673 / 25000000000000000000000000000000)⟩
lemma CA5_5_6I1R3Entropy_sound : CA5_5_6I1R3Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R3Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R3Value CA5_5_6I1R3Terms CA5_5_6I1R3Terms_sound) (by decide +kernel)
def CA5_5_6I1R3Mass : Ball := ⟨(10251159363232810376536125401349 / 25000000000000000000000000000000), (63 / 50000000000000000000000000000000)⟩
lemma CA5_5_6I1R3Mass_sound : CA5_5_6I1R3Mass.Encloses (∑ a, CA5_5_6I1R3Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R3P CA5_5_6I1R3Value CA5_5_6I1R3P_sound) (by decide +kernel)
def CA5_5_6I1R3MassTermLogWitness : LogWitness := ⟨-2, 10251159363232810376536125401349, 6250000000000000000000000000000⟩
def CA5_5_6I1R3MassTermLog : Ball := ⟨(-44574250853600040046678633920341 / 50000000000000000000000000000000), (15881867839 / 25000000000000000000000000000000)⟩
lemma CA5_5_6I1R3MassTermLog_sound : CA5_5_6I1R3MassTermLog.Encloses (Real.log ((∑ a, CA5_5_6I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA5_5_6I1R3Mass_sound) (w := CA5_5_6I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA5_5_6I1R3MassTerm : Ball := ⟨(9138754979939402818134539391403 / 25000000000000000000000000000000), (13024604713 / 50000000000000000000000000000000)⟩
lemma CA5_5_6I1R3MassTerm_sound : CA5_5_6I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA5_5_6I1R3Mass_sound) CA5_5_6I1R3MassTermLog_sound) (by decide +kernel)
def CA5_5_6I1R3H : Ball := ⟨(10661838650173040273289430702077 / 25000000000000000000000000000000), (32003220059 / 50000000000000000000000000000000)⟩
lemma CA5_5_6I1R3H_sound : CA5_5_6I1R3H.Encloses (homogeneousEntropy CA5_5_6I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R3Value CA5_5_6I1R3MassTerm_sound CA5_5_6I1R3Entropy_sound) (by decide +kernel)
def CA5_5_6I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA5_5_6I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
lemma CA5_5_6I1R4Raw_sound (a : PairSlot) :
    (CA5_5_6I1R4Raw a).Encloses (CA5_5_6I1R4Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 4 a
def CA5_5_6I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(394592318926025536485814717 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(32714500344003059911566981341 / 100000000000000000000000000000000), (5347729 / 50000000000000000000000000000000)⟩ ⟨(-207267721486844674945926562184131 / 20000000000000000000000000000000), (67762642121 / 20000000000000000000000000000000)⟩ ⟨-15, 394592318926025536485814717, 381469726562500000000000000⟩,
   .log ⟨(346222247156512031659066700391 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(1721658462280752209912386633821 / 50000000000000000000000000000000), (164959683 / 12500000000000000000000000000000)⟩ ⟨(-497269738273769923200338345290949 / 100000000000000000000000000000000), (190582414013 / 100000000000000000000000000000000)⟩ ⟨-8, 346222247156512031659066700391, 195312500000000000000000000000⟩,
   .log ⟨(6647203530643439341023305867833 / 100000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩ ⟨(18020395555235912452468847350461 / 100000000000000000000000000000000), (7038000639 / 100000000000000000000000000000000)⟩ ⟨(-67774348536803284726700195379887 / 25000000000000000000000000000000), (52939559493 / 50000000000000000000000000000000)⟩ ⟨-4, 6647203530643439341023305867833, 6250000000000000000000000000000⟩,
   .log ⟨(326754586305341673734263853161 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(935125239342346232274455191849 / 50000000000000000000000000000000), (172982443 / 25000000000000000000000000000000)⟩ ⟨(-572371607643481832506121049572673 / 100000000000000000000000000000000), (52939559437 / 25000000000000000000000000000000)⟩ ⟨-9, 326754586305341673734263853161, 195312500000000000000000000000⟩,
   .log ⟨(8894723011787277341472726829 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(153599771432237162935399418387 / 100000000000000000000000000000000), (26369437 / 50000000000000000000000000000000)⟩ ⟨(-863432010354267982849928330105699 / 100000000000000000000000000000000), (296461537183 / 100000000000000000000000000000000)⟩ ⟨-13, 8894723011787277341472726829, 6103515625000000000000000000⟩]
lemma CA5_5_6I1R4Certificates_valid :
    CA5_5_6I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I1R4CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 5 => 1
  | 1, 4 => 2
  | 2, 2 => 3
  | 2, 3 => 4
  | 3, 2 => 4
  | 3, 3 => 5
  | 4, 1 => 2
  | 5, 0 => 1
  | _, _ => 0
def CA5_5_6I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R4Certificates (CA5_5_6I1R4CertificateIndex a)).input
lemma CA5_5_6I1R4P_check : ∀ a : PairSlot, contains (CA5_5_6I1R4Raw a) (CA5_5_6I1R4P a) = true := by
  decide +kernel
lemma CA5_5_6I1R4P_sound (a : PairSlot) :
    (CA5_5_6I1R4P a).Encloses (CA5_5_6I1R4Value a) :=
  contains_sound (CA5_5_6I1R4Raw_sound a) (CA5_5_6I1R4P_check a)
def CA5_5_6I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R4Certificates (CA5_5_6I1R4CertificateIndex a)).output
lemma CA5_5_6I1R4Terms_sound (a : PairSlot) :
    (CA5_5_6I1R4Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R4Certificates_valid
    (CA5_5_6I1R4CertificateIndex a) (CA5_5_6I1R4P_sound a)
def CA5_5_6I1R4Entropy : Ball := ⟨(2886655913384854950397474803421 / 10000000000000000000000000000000), (11135344901 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I1R4Entropy_sound : CA5_5_6I1R4Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R4Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R4Value CA5_5_6I1R4Terms CA5_5_6I1R4Terms_sound) (by decide +kernel)
def CA5_5_6I1R4Mass : Ball := ⟨(8709704615006561778394818864849 / 100000000000000000000000000000000), (59 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I1R4Mass_sound : CA5_5_6I1R4Mass.Encloses (∑ a, CA5_5_6I1R4Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R4P CA5_5_6I1R4Value CA5_5_6I1R4P_sound) (by decide +kernel)
def CA5_5_6I1R4MassTermLogWitness : LogWitness := ⟨-4, 8709704615006561778394818864849, 6250000000000000000000000000000⟩
def CA5_5_6I1R4MassTermLog : Ball := ⟨(-244073230901602138310941379700737 / 100000000000000000000000000000000), (26469779773 / 25000000000000000000000000000000)⟩
lemma CA5_5_6I1R4MassTermLog_sound : CA5_5_6I1R4MassTermLog.Encloses (Real.log ((∑ a, CA5_5_6I1R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA5_5_6I1R4Mass_sound) (w := CA5_5_6I1R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA5_5_6I1R4MassTerm : Ball := ⟨(4251611491166492618787916417629 / 20000000000000000000000000000000), (4610879333 / 50000000000000000000000000000000)⟩
lemma CA5_5_6I1R4MassTerm_sound : CA5_5_6I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA5_5_6I1R4Mass_sound) CA5_5_6I1R4MassTermLog_sound) (by decide +kernel)
def CA5_5_6I1R4H : Ball := ⟨(1521700335603217282007033189213 / 20000000000000000000000000000000), (20357103567 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I1R4H_sound : CA5_5_6I1R4H.Encloses (homogeneousEntropy CA5_5_6I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R4Value CA5_5_6I1R4MassTerm_sound CA5_5_6I1R4Entropy_sound) (by decide +kernel)
def CA5_5_6I1R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 5 a
def CA5_5_6I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
lemma CA5_5_6I1R5Raw_sound (a : PairSlot) :
    (CA5_5_6I1R5Raw a).Encloses (CA5_5_6I1R5Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 5 a
def CA5_5_6I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1182429246892354719670022127 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(6297740714917424058006949267 / 25000000000000000000000000000000), (8513243 / 100000000000000000000000000000000)⟩ ⟨(-213044145566225290681104832862459 / 20000000000000000000000000000000), (359989044897 / 100000000000000000000000000000000)⟩ ⟨-16, 1182429246892354719670022127, 762939453125000000000000000⟩,
   .log ⟨(3162039426222401142649858937 / 2500000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(168797982085904458943340093419 / 20000000000000000000000000000000), (294618697 / 100000000000000000000000000000000)⟩ ⟨(-333641440169285425875927063846407 / 50000000000000000000000000000000), (58233515721 / 25000000000000000000000000000000)⟩ ⟨-10, 3162039426222401142649858937, 2441406250000000000000000000⟩,
   .log ⟨(6194842723022241767055626031 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(60023121764133098394063297447 / 100000000000000000000000000000000), (9838573 / 50000000000000000000000000000000)⟩ ⟨(-968920833793984817510231564930619 / 100000000000000000000000000000000), (317637371387 / 100000000000000000000000000000000)⟩ ⟨-14, 6194842723022241767055626031, 6103515625000000000000000000⟩]
lemma CA5_5_6I1R5Certificates_valid :
    CA5_5_6I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 5 => 1
  | 2, 4 => 2
  | 3, 4 => 3
  | 4, 2 => 2
  | 4, 3 => 3
  | 5, 1 => 1
  | _, _ => 0
def CA5_5_6I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R5Certificates (CA5_5_6I1R5CertificateIndex a)).input
lemma CA5_5_6I1R5P_check : ∀ a : PairSlot, contains (CA5_5_6I1R5Raw a) (CA5_5_6I1R5P a) = true := by
  decide +kernel
lemma CA5_5_6I1R5P_sound (a : PairSlot) :
    (CA5_5_6I1R5P a).Encloses (CA5_5_6I1R5Value a) :=
  contains_sound (CA5_5_6I1R5Raw_sound a) (CA5_5_6I1R5P_check a)
def CA5_5_6I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R5Certificates (CA5_5_6I1R5CertificateIndex a)).output
lemma CA5_5_6I1R5Terms_sound (a : PairSlot) :
    (CA5_5_6I1R5Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R5Certificates_valid
    (CA5_5_6I1R5CertificateIndex a) (CA5_5_6I1R5P_sound a)
def CA5_5_6I1R5Entropy : Ball := ⟨(92920399505332508934279156161 / 5000000000000000000000000000000), (161404543 / 25000000000000000000000000000000)⟩
lemma CA5_5_6I1R5Entropy_sound : CA5_5_6I1R5Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R5Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R5Value CA5_5_6I1R5Terms CA5_5_6I1R5Terms_sound) (by decide +kernel)
def CA5_5_6I1R5Mass : Ball := ⟨(27008255653140599382478005553 / 10000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
lemma CA5_5_6I1R5Mass_sound : CA5_5_6I1R5Mass.Encloses (∑ a, CA5_5_6I1R5Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R5P CA5_5_6I1R5Value CA5_5_6I1R5P_sound) (by decide +kernel)
def CA5_5_6I1R5MassTermLogWitness : LogWitness := ⟨-9, 27008255653140599382478005553, 19531250000000000000000000000⟩
def CA5_5_6I1R5MassTermLog : Ball := ⟨(-591419778777729021357025396717877 / 100000000000000000000000000000000), (52939560133 / 25000000000000000000000000000000)⟩
lemma CA5_5_6I1R5MassTermLog_sound : CA5_5_6I1R5MassTermLog.Encloses (Real.log ((∑ a, CA5_5_6I1R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA5_5_6I1R5Mass_sound) (w := CA5_5_6I1R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA5_5_6I1R5MassTerm : Ball := ⟨(319464331671055250544989325127 / 20000000000000000000000000000000), (57192213 / 10000000000000000000000000000000)⟩
lemma CA5_5_6I1R5MassTerm_sound : CA5_5_6I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA5_5_6I1R5Mass_sound) CA5_5_6I1R5MassTermLog_sound) (by decide +kernel)
def CA5_5_6I1R5H : Ball := ⟨(52217266350274785192127299517 / 20000000000000000000000000000000), (608770151 / 50000000000000000000000000000000)⟩
lemma CA5_5_6I1R5H_sound : CA5_5_6I1R5H.Encloses (homogeneousEntropy CA5_5_6I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R5Value CA5_5_6I1R5MassTerm_sound CA5_5_6I1R5Entropy_sound) (by decide +kernel)
def CA5_5_6I1R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 6 a
def CA5_5_6I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
lemma CA5_5_6I1R6Raw_sound (a : PairSlot) :
    (CA5_5_6I1R6Raw a).Encloses (CA5_5_6I1R6Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 6 a
def CA5_5_6I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA5_5_6I1R6Certificates_valid :
    CA5_5_6I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I1R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA5_5_6I1R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R6Certificates (CA5_5_6I1R6CertificateIndex a)).input
lemma CA5_5_6I1R6P_check : ∀ a : PairSlot, contains (CA5_5_6I1R6Raw a) (CA5_5_6I1R6P a) = true := by
  decide +kernel
lemma CA5_5_6I1R6P_sound (a : PairSlot) :
    (CA5_5_6I1R6P a).Encloses (CA5_5_6I1R6Value a) :=
  contains_sound (CA5_5_6I1R6Raw_sound a) (CA5_5_6I1R6P_check a)
def CA5_5_6I1R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R6Certificates (CA5_5_6I1R6CertificateIndex a)).output
lemma CA5_5_6I1R6Terms_sound (a : PairSlot) :
    (CA5_5_6I1R6Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R6Certificates_valid
    (CA5_5_6I1R6CertificateIndex a) (CA5_5_6I1R6P_sound a)
def CA5_5_6I1R6Entropy : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R6Entropy_sound : CA5_5_6I1R6Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R6Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R6Value CA5_5_6I1R6Terms CA5_5_6I1R6Terms_sound) (by decide +kernel)
def CA5_5_6I1R6Mass : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R6Mass_sound : CA5_5_6I1R6Mass.Encloses (∑ a, CA5_5_6I1R6Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R6P CA5_5_6I1R6Value CA5_5_6I1R6P_sound) (by decide +kernel)
def CA5_5_6I1R6MassTerm : Ball := .exact 0
lemma CA5_5_6I1R6MassTerm_sound : CA5_5_6I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R6Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I1R6Mass_sound)
def CA5_5_6I1R6H : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R6H_sound : CA5_5_6I1R6H.Encloses (homogeneousEntropy CA5_5_6I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R6Value CA5_5_6I1R6MassTerm_sound CA5_5_6I1R6Entropy_sound) (by decide +kernel)
def CA5_5_6I1R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 7 a
def CA5_5_6I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
lemma CA5_5_6I1R7Raw_sound (a : PairSlot) :
    (CA5_5_6I1R7Raw a).Encloses (CA5_5_6I1R7Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 7 a
def CA5_5_6I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA5_5_6I1R7Certificates_valid :
    CA5_5_6I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I1R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA5_5_6I1R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R7Certificates (CA5_5_6I1R7CertificateIndex a)).input
lemma CA5_5_6I1R7P_check : ∀ a : PairSlot, contains (CA5_5_6I1R7Raw a) (CA5_5_6I1R7P a) = true := by
  decide +kernel
lemma CA5_5_6I1R7P_sound (a : PairSlot) :
    (CA5_5_6I1R7P a).Encloses (CA5_5_6I1R7Value a) :=
  contains_sound (CA5_5_6I1R7Raw_sound a) (CA5_5_6I1R7P_check a)
def CA5_5_6I1R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R7Certificates (CA5_5_6I1R7CertificateIndex a)).output
lemma CA5_5_6I1R7Terms_sound (a : PairSlot) :
    (CA5_5_6I1R7Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R7Certificates_valid
    (CA5_5_6I1R7CertificateIndex a) (CA5_5_6I1R7P_sound a)
def CA5_5_6I1R7Entropy : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R7Entropy_sound : CA5_5_6I1R7Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R7Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R7Value CA5_5_6I1R7Terms CA5_5_6I1R7Terms_sound) (by decide +kernel)
def CA5_5_6I1R7Mass : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R7Mass_sound : CA5_5_6I1R7Mass.Encloses (∑ a, CA5_5_6I1R7Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R7P CA5_5_6I1R7Value CA5_5_6I1R7P_sound) (by decide +kernel)
def CA5_5_6I1R7MassTerm : Ball := .exact 0
lemma CA5_5_6I1R7MassTerm_sound : CA5_5_6I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R7Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I1R7Mass_sound)
def CA5_5_6I1R7H : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R7H_sound : CA5_5_6I1R7H.Encloses (homogeneousEntropy CA5_5_6I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R7Value CA5_5_6I1R7MassTerm_sound CA5_5_6I1R7Entropy_sound) (by decide +kernel)
def CA5_5_6I1R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 8 a
def CA5_5_6I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
lemma CA5_5_6I1R8Raw_sound (a : PairSlot) :
    (CA5_5_6I1R8Raw a).Encloses (CA5_5_6I1R8Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 8 a
def CA5_5_6I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA5_5_6I1R8Certificates_valid :
    CA5_5_6I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA5_5_6I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R8Certificates (CA5_5_6I1R8CertificateIndex a)).input
lemma CA5_5_6I1R8P_check : ∀ a : PairSlot, contains (CA5_5_6I1R8Raw a) (CA5_5_6I1R8P a) = true := by
  decide +kernel
lemma CA5_5_6I1R8P_sound (a : PairSlot) :
    (CA5_5_6I1R8P a).Encloses (CA5_5_6I1R8Value a) :=
  contains_sound (CA5_5_6I1R8Raw_sound a) (CA5_5_6I1R8P_check a)
def CA5_5_6I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R8Certificates (CA5_5_6I1R8CertificateIndex a)).output
lemma CA5_5_6I1R8Terms_sound (a : PairSlot) :
    (CA5_5_6I1R8Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R8Certificates_valid
    (CA5_5_6I1R8CertificateIndex a) (CA5_5_6I1R8P_sound a)
def CA5_5_6I1R8Entropy : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R8Entropy_sound : CA5_5_6I1R8Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R8Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R8Value CA5_5_6I1R8Terms CA5_5_6I1R8Terms_sound) (by decide +kernel)
def CA5_5_6I1R8Mass : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R8Mass_sound : CA5_5_6I1R8Mass.Encloses (∑ a, CA5_5_6I1R8Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R8P CA5_5_6I1R8Value CA5_5_6I1R8P_sound) (by decide +kernel)
def CA5_5_6I1R8MassTerm : Ball := .exact 0
lemma CA5_5_6I1R8MassTerm_sound : CA5_5_6I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R8Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I1R8Mass_sound)
def CA5_5_6I1R8H : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R8H_sound : CA5_5_6I1R8H.Encloses (homogeneousEntropy CA5_5_6I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R8Value CA5_5_6I1R8MassTerm_sound CA5_5_6I1R8Entropy_sound) (by decide +kernel)
def CA5_5_6I1R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 9 a
def CA5_5_6I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
lemma CA5_5_6I1R9Raw_sound (a : PairSlot) :
    (CA5_5_6I1R9Raw a).Encloses (CA5_5_6I1R9Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 9 a
def CA5_5_6I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA5_5_6I1R9Certificates_valid :
    CA5_5_6I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA5_5_6I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R9Certificates (CA5_5_6I1R9CertificateIndex a)).input
lemma CA5_5_6I1R9P_check : ∀ a : PairSlot, contains (CA5_5_6I1R9Raw a) (CA5_5_6I1R9P a) = true := by
  decide +kernel
lemma CA5_5_6I1R9P_sound (a : PairSlot) :
    (CA5_5_6I1R9P a).Encloses (CA5_5_6I1R9Value a) :=
  contains_sound (CA5_5_6I1R9Raw_sound a) (CA5_5_6I1R9P_check a)
def CA5_5_6I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R9Certificates (CA5_5_6I1R9CertificateIndex a)).output
lemma CA5_5_6I1R9Terms_sound (a : PairSlot) :
    (CA5_5_6I1R9Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R9Certificates_valid
    (CA5_5_6I1R9CertificateIndex a) (CA5_5_6I1R9P_sound a)
def CA5_5_6I1R9Entropy : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R9Entropy_sound : CA5_5_6I1R9Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R9Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R9Value CA5_5_6I1R9Terms CA5_5_6I1R9Terms_sound) (by decide +kernel)
def CA5_5_6I1R9Mass : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R9Mass_sound : CA5_5_6I1R9Mass.Encloses (∑ a, CA5_5_6I1R9Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R9P CA5_5_6I1R9Value CA5_5_6I1R9P_sound) (by decide +kernel)
def CA5_5_6I1R9MassTerm : Ball := .exact 0
lemma CA5_5_6I1R9MassTerm_sound : CA5_5_6I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R9Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I1R9Mass_sound)
def CA5_5_6I1R9H : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R9H_sound : CA5_5_6I1R9H.Encloses (homogeneousEntropy CA5_5_6I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R9Value CA5_5_6I1R9MassTerm_sound CA5_5_6I1R9Entropy_sound) (by decide +kernel)
def CA5_5_6I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA5_5_6I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
lemma CA5_5_6I1R10Raw_sound (a : PairSlot) :
    (CA5_5_6I1R10Raw a).Encloses (CA5_5_6I1R10Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 10 a
def CA5_5_6I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA5_5_6I1R10Certificates_valid :
    CA5_5_6I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA5_5_6I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R10Certificates (CA5_5_6I1R10CertificateIndex a)).input
lemma CA5_5_6I1R10P_check : ∀ a : PairSlot, contains (CA5_5_6I1R10Raw a) (CA5_5_6I1R10P a) = true := by
  decide +kernel
lemma CA5_5_6I1R10P_sound (a : PairSlot) :
    (CA5_5_6I1R10P a).Encloses (CA5_5_6I1R10Value a) :=
  contains_sound (CA5_5_6I1R10Raw_sound a) (CA5_5_6I1R10P_check a)
def CA5_5_6I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R10Certificates (CA5_5_6I1R10CertificateIndex a)).output
lemma CA5_5_6I1R10Terms_sound (a : PairSlot) :
    (CA5_5_6I1R10Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R10Certificates_valid
    (CA5_5_6I1R10CertificateIndex a) (CA5_5_6I1R10P_sound a)
def CA5_5_6I1R10Entropy : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R10Entropy_sound : CA5_5_6I1R10Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R10Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R10Value CA5_5_6I1R10Terms CA5_5_6I1R10Terms_sound) (by decide +kernel)
def CA5_5_6I1R10Mass : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R10Mass_sound : CA5_5_6I1R10Mass.Encloses (∑ a, CA5_5_6I1R10Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R10P CA5_5_6I1R10Value CA5_5_6I1R10P_sound) (by decide +kernel)
def CA5_5_6I1R10MassTerm : Ball := .exact 0
lemma CA5_5_6I1R10MassTerm_sound : CA5_5_6I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R10Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I1R10Mass_sound)
def CA5_5_6I1R10H : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R10H_sound : CA5_5_6I1R10H.Encloses (homogeneousEntropy CA5_5_6I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R10Value CA5_5_6I1R10MassTerm_sound CA5_5_6I1R10Entropy_sound) (by decide +kernel)
def CA5_5_6I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA5_5_6I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
lemma CA5_5_6I1R11Raw_sound (a : PairSlot) :
    (CA5_5_6I1R11Raw a).Encloses (CA5_5_6I1R11Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 11 a
def CA5_5_6I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA5_5_6I1R11Certificates_valid :
    CA5_5_6I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA5_5_6I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R11Certificates (CA5_5_6I1R11CertificateIndex a)).input
lemma CA5_5_6I1R11P_check : ∀ a : PairSlot, contains (CA5_5_6I1R11Raw a) (CA5_5_6I1R11P a) = true := by
  decide +kernel
lemma CA5_5_6I1R11P_sound (a : PairSlot) :
    (CA5_5_6I1R11P a).Encloses (CA5_5_6I1R11Value a) :=
  contains_sound (CA5_5_6I1R11Raw_sound a) (CA5_5_6I1R11P_check a)
def CA5_5_6I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R11Certificates (CA5_5_6I1R11CertificateIndex a)).output
lemma CA5_5_6I1R11Terms_sound (a : PairSlot) :
    (CA5_5_6I1R11Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R11Certificates_valid
    (CA5_5_6I1R11CertificateIndex a) (CA5_5_6I1R11P_sound a)
def CA5_5_6I1R11Entropy : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R11Entropy_sound : CA5_5_6I1R11Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R11Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R11Value CA5_5_6I1R11Terms CA5_5_6I1R11Terms_sound) (by decide +kernel)
def CA5_5_6I1R11Mass : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R11Mass_sound : CA5_5_6I1R11Mass.Encloses (∑ a, CA5_5_6I1R11Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R11P CA5_5_6I1R11Value CA5_5_6I1R11P_sound) (by decide +kernel)
def CA5_5_6I1R11MassTerm : Ball := .exact 0
lemma CA5_5_6I1R11MassTerm_sound : CA5_5_6I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R11Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I1R11Mass_sound)
def CA5_5_6I1R11H : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R11H_sound : CA5_5_6I1R11H.Encloses (homogeneousEntropy CA5_5_6I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R11Value CA5_5_6I1R11MassTerm_sound CA5_5_6I1R11Entropy_sound) (by decide +kernel)
def CA5_5_6I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA5_5_6I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
lemma CA5_5_6I1R12Raw_sound (a : PairSlot) :
    (CA5_5_6I1R12Raw a).Encloses (CA5_5_6I1R12Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 12 a
def CA5_5_6I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA5_5_6I1R12Certificates_valid :
    CA5_5_6I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA5_5_6I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R12Certificates (CA5_5_6I1R12CertificateIndex a)).input
lemma CA5_5_6I1R12P_check : ∀ a : PairSlot, contains (CA5_5_6I1R12Raw a) (CA5_5_6I1R12P a) = true := by
  decide +kernel
lemma CA5_5_6I1R12P_sound (a : PairSlot) :
    (CA5_5_6I1R12P a).Encloses (CA5_5_6I1R12Value a) :=
  contains_sound (CA5_5_6I1R12Raw_sound a) (CA5_5_6I1R12P_check a)
def CA5_5_6I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R12Certificates (CA5_5_6I1R12CertificateIndex a)).output
lemma CA5_5_6I1R12Terms_sound (a : PairSlot) :
    (CA5_5_6I1R12Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R12Certificates_valid
    (CA5_5_6I1R12CertificateIndex a) (CA5_5_6I1R12P_sound a)
def CA5_5_6I1R12Entropy : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R12Entropy_sound : CA5_5_6I1R12Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R12Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R12Value CA5_5_6I1R12Terms CA5_5_6I1R12Terms_sound) (by decide +kernel)
def CA5_5_6I1R12Mass : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R12Mass_sound : CA5_5_6I1R12Mass.Encloses (∑ a, CA5_5_6I1R12Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R12P CA5_5_6I1R12Value CA5_5_6I1R12P_sound) (by decide +kernel)
def CA5_5_6I1R12MassTerm : Ball := .exact 0
lemma CA5_5_6I1R12MassTerm_sound : CA5_5_6I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R12Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I1R12Mass_sound)
def CA5_5_6I1R12H : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R12H_sound : CA5_5_6I1R12H.Encloses (homogeneousEntropy CA5_5_6I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R12Value CA5_5_6I1R12MassTerm_sound CA5_5_6I1R12Entropy_sound) (by decide +kernel)
def CA5_5_6I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA5_5_6I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
lemma CA5_5_6I1R13Raw_sound (a : PairSlot) :
    (CA5_5_6I1R13Raw a).Encloses (CA5_5_6I1R13Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 13 a
def CA5_5_6I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA5_5_6I1R13Certificates_valid :
    CA5_5_6I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA5_5_6I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R13Certificates (CA5_5_6I1R13CertificateIndex a)).input
lemma CA5_5_6I1R13P_check : ∀ a : PairSlot, contains (CA5_5_6I1R13Raw a) (CA5_5_6I1R13P a) = true := by
  decide +kernel
lemma CA5_5_6I1R13P_sound (a : PairSlot) :
    (CA5_5_6I1R13P a).Encloses (CA5_5_6I1R13Value a) :=
  contains_sound (CA5_5_6I1R13Raw_sound a) (CA5_5_6I1R13P_check a)
def CA5_5_6I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R13Certificates (CA5_5_6I1R13CertificateIndex a)).output
lemma CA5_5_6I1R13Terms_sound (a : PairSlot) :
    (CA5_5_6I1R13Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R13Certificates_valid
    (CA5_5_6I1R13CertificateIndex a) (CA5_5_6I1R13P_sound a)
def CA5_5_6I1R13Entropy : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R13Entropy_sound : CA5_5_6I1R13Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R13Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R13Value CA5_5_6I1R13Terms CA5_5_6I1R13Terms_sound) (by decide +kernel)
def CA5_5_6I1R13Mass : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R13Mass_sound : CA5_5_6I1R13Mass.Encloses (∑ a, CA5_5_6I1R13Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R13P CA5_5_6I1R13Value CA5_5_6I1R13P_sound) (by decide +kernel)
def CA5_5_6I1R13MassTerm : Ball := .exact 0
lemma CA5_5_6I1R13MassTerm_sound : CA5_5_6I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R13Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I1R13Mass_sound)
def CA5_5_6I1R13H : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R13H_sound : CA5_5_6I1R13H.Encloses (homogeneousEntropy CA5_5_6I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R13Value CA5_5_6I1R13MassTerm_sound CA5_5_6I1R13Entropy_sound) (by decide +kernel)
def CA5_5_6I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA5_5_6I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
lemma CA5_5_6I1R14Raw_sound (a : PairSlot) :
    (CA5_5_6I1R14Raw a).Encloses (CA5_5_6I1R14Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 14 a
def CA5_5_6I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA5_5_6I1R14Certificates_valid :
    CA5_5_6I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA5_5_6I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R14Certificates (CA5_5_6I1R14CertificateIndex a)).input
lemma CA5_5_6I1R14P_check : ∀ a : PairSlot, contains (CA5_5_6I1R14Raw a) (CA5_5_6I1R14P a) = true := by
  decide +kernel
lemma CA5_5_6I1R14P_sound (a : PairSlot) :
    (CA5_5_6I1R14P a).Encloses (CA5_5_6I1R14Value a) :=
  contains_sound (CA5_5_6I1R14Raw_sound a) (CA5_5_6I1R14P_check a)
def CA5_5_6I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R14Certificates (CA5_5_6I1R14CertificateIndex a)).output
lemma CA5_5_6I1R14Terms_sound (a : PairSlot) :
    (CA5_5_6I1R14Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R14Certificates_valid
    (CA5_5_6I1R14CertificateIndex a) (CA5_5_6I1R14P_sound a)
def CA5_5_6I1R14Entropy : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R14Entropy_sound : CA5_5_6I1R14Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R14Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R14Value CA5_5_6I1R14Terms CA5_5_6I1R14Terms_sound) (by decide +kernel)
def CA5_5_6I1R14Mass : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R14Mass_sound : CA5_5_6I1R14Mass.Encloses (∑ a, CA5_5_6I1R14Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R14P CA5_5_6I1R14Value CA5_5_6I1R14P_sound) (by decide +kernel)
def CA5_5_6I1R14MassTerm : Ball := .exact 0
lemma CA5_5_6I1R14MassTerm_sound : CA5_5_6I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R14Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I1R14Mass_sound)
def CA5_5_6I1R14H : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R14H_sound : CA5_5_6I1R14H.Encloses (homogeneousEntropy CA5_5_6I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R14Value CA5_5_6I1R14MassTerm_sound CA5_5_6I1R14Entropy_sound) (by decide +kernel)
def CA5_5_6I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA5_5_6I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
lemma CA5_5_6I1R15Raw_sound (a : PairSlot) :
    (CA5_5_6I1R15Raw a).Encloses (CA5_5_6I1R15Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 15 a
def CA5_5_6I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA5_5_6I1R15Certificates_valid :
    CA5_5_6I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA5_5_6I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R15Certificates (CA5_5_6I1R15CertificateIndex a)).input
lemma CA5_5_6I1R15P_check : ∀ a : PairSlot, contains (CA5_5_6I1R15Raw a) (CA5_5_6I1R15P a) = true := by
  decide +kernel
lemma CA5_5_6I1R15P_sound (a : PairSlot) :
    (CA5_5_6I1R15P a).Encloses (CA5_5_6I1R15Value a) :=
  contains_sound (CA5_5_6I1R15Raw_sound a) (CA5_5_6I1R15P_check a)
def CA5_5_6I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R15Certificates (CA5_5_6I1R15CertificateIndex a)).output
lemma CA5_5_6I1R15Terms_sound (a : PairSlot) :
    (CA5_5_6I1R15Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R15Certificates_valid
    (CA5_5_6I1R15CertificateIndex a) (CA5_5_6I1R15P_sound a)
def CA5_5_6I1R15Entropy : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R15Entropy_sound : CA5_5_6I1R15Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R15Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R15Value CA5_5_6I1R15Terms CA5_5_6I1R15Terms_sound) (by decide +kernel)
def CA5_5_6I1R15Mass : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R15Mass_sound : CA5_5_6I1R15Mass.Encloses (∑ a, CA5_5_6I1R15Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R15P CA5_5_6I1R15Value CA5_5_6I1R15P_sound) (by decide +kernel)
def CA5_5_6I1R15MassTerm : Ball := .exact 0
lemma CA5_5_6I1R15MassTerm_sound : CA5_5_6I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R15Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I1R15Mass_sound)
def CA5_5_6I1R15H : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R15H_sound : CA5_5_6I1R15H.Encloses (homogeneousEntropy CA5_5_6I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R15Value CA5_5_6I1R15MassTerm_sound CA5_5_6I1R15Entropy_sound) (by decide +kernel)
def CA5_5_6I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA5_5_6I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
lemma CA5_5_6I1R16Raw_sound (a : PairSlot) :
    (CA5_5_6I1R16Raw a).Encloses (CA5_5_6I1R16Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 16 a
def CA5_5_6I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA5_5_6I1R16Certificates_valid :
    CA5_5_6I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA5_5_6I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R16Certificates (CA5_5_6I1R16CertificateIndex a)).input
lemma CA5_5_6I1R16P_check : ∀ a : PairSlot, contains (CA5_5_6I1R16Raw a) (CA5_5_6I1R16P a) = true := by
  decide +kernel
lemma CA5_5_6I1R16P_sound (a : PairSlot) :
    (CA5_5_6I1R16P a).Encloses (CA5_5_6I1R16Value a) :=
  contains_sound (CA5_5_6I1R16Raw_sound a) (CA5_5_6I1R16P_check a)
def CA5_5_6I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I1R16Certificates (CA5_5_6I1R16CertificateIndex a)).output
lemma CA5_5_6I1R16Terms_sound (a : PairSlot) :
    (CA5_5_6I1R16Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R16Certificates_valid
    (CA5_5_6I1R16CertificateIndex a) (CA5_5_6I1R16P_sound a)
def CA5_5_6I1R16Entropy : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R16Entropy_sound : CA5_5_6I1R16Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R16Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R16Value CA5_5_6I1R16Terms CA5_5_6I1R16Terms_sound) (by decide +kernel)
def CA5_5_6I1R16Mass : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R16Mass_sound : CA5_5_6I1R16Mass.Encloses (∑ a, CA5_5_6I1R16Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R16P CA5_5_6I1R16Value CA5_5_6I1R16P_sound) (by decide +kernel)
def CA5_5_6I1R16MassTerm : Ball := .exact 0
lemma CA5_5_6I1R16MassTerm_sound : CA5_5_6I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R16Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I1R16Mass_sound)
def CA5_5_6I1R16H : Ball := ⟨0, 0⟩
lemma CA5_5_6I1R16H_sound : CA5_5_6I1R16H.Encloses (homogeneousEntropy CA5_5_6I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R16Value CA5_5_6I1R16MassTerm_sound CA5_5_6I1R16Entropy_sound) (by decide +kernel)
def CA5_5_6I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA5_5_6I1R0H
  | 1 => CA5_5_6I1R1H
  | 2 => CA5_5_6I1R2H
  | 3 => CA5_5_6I1R3H
  | 4 => CA5_5_6I1R4H
  | 5 => CA5_5_6I1R5H
  | 6 => CA5_5_6I1R6H
  | 7 => CA5_5_6I1R7H
  | 8 => CA5_5_6I1R8H
  | 9 => CA5_5_6I1R9H
  | 10 => CA5_5_6I1R10H
  | 11 => CA5_5_6I1R11H
  | 12 => CA5_5_6I1R12H
  | 13 => CA5_5_6I1R13H
  | 14 => CA5_5_6I1R14H
  | 15 => CA5_5_6I1R15H
  | 16 => CA5_5_6I1R16H
  | _ => (.exact 0)
lemma CA5_5_6I1ResidualEntropies_sound (k : Fin 17) :
    (CA5_5_6I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CA5_5_6I1R0H_sound
  · exact CA5_5_6I1R1H_sound
  · exact CA5_5_6I1R2H_sound
  · exact CA5_5_6I1R3H_sound
  · exact CA5_5_6I1R4H_sound
  · exact CA5_5_6I1R5H_sound
  · exact CA5_5_6I1R6H_sound
  · exact CA5_5_6I1R7H_sound
  · exact CA5_5_6I1R8H_sound
  · exact CA5_5_6I1R9H_sound
  · exact CA5_5_6I1R10H_sound
  · exact CA5_5_6I1R11H_sound
  · exact CA5_5_6I1R12H_sound
  · exact CA5_5_6I1R13H_sound
  · exact CA5_5_6I1R14H_sound
  · exact CA5_5_6I1R15H_sound
  · exact CA5_5_6I1R16H_sound
def CA5_5_6I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 3, 5, 0 => Z3_5_0H1H
  | 4, 4, 0 => Z4_4_0H1H
  | 5, 3, 0 => Z5_3_0H1H
  | _, _, _ => (.exact 0)
lemma CA5_5_6I1Singles_sound (u : Shape) (hu : u ∈ below (shape 5 5 6))
    (hd : designated (Equiv.refl (Fin 3)) 1 u) :
    (CA5_5_6I1Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) u)) := by
  rw [A5_5_6_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 2 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 3 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 4 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 5 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 2 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 3 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 4 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 5 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 0 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 1 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 2 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 3 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 4 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 5 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 0 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 1 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 2 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 3 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 4 1) by decide +kernel) hd |>.elim
  · exact Z3_5_0H1H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 4 0 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 4 1 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 4 2 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 4 3 1) by decide +kernel) hd |>.elim
  · exact Z4_4_0H1H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 5 0 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 5 1 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 5 2 1) by decide +kernel) hd |>.elim
  · exact Z5_3_0H1H_sound
def CA5_5_6I1Singleton : Ball := ⟨(19127110369820477968402652613 / 100000000000000000000000000000000), (317069 / 2000000000000000000000000000000)⟩
lemma CA5_5_6I1Singleton_sound : CA5_5_6I1Singleton.Encloses
    (singletonEntropy (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1
    CA5_5_6I1Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) CA5_5_6I1Singles_sound) (by decide +kernel)
def CA5_5_6I1Group : Ball := ⟨(24449855014961409946479308512559 / 25000000000000000000000000000000), (20804574119 / 12500000000000000000000000000000)⟩
lemma CA5_5_6I1Group_sound : CA5_5_6I1Group.Encloses
    (groupedEntropy (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA5_5_6I1Singleton_sound
    (finSumBall_sound 17 CA5_5_6I1ResidualEntropies _ CA5_5_6I1ResidualEntropies_sound)) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA5_5_6I1H : Ball := ⟨(5943894429999961068408416286193 / 5000000000000000000000000000000), (96584184323 / 20000000000000000000000000000000)⟩
lemma CA5_5_6I1_sound : CA5_5_6I1H.Encloses (stageACapacity (shape 5 5 6) 1) := by
  have hb := contains_sound (Ball.add_sound CA5_5_6I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA5_5_6I1Group_sound)))
    (show contains (.add CA5_5_6I1PairH (.neg (.mul (.exact 2) CA5_5_6I1Group))) CA5_5_6I1H = true by decide +kernel)
  simp only [stageACapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false]
  change CA5_5_6I1H.Encloses (homogeneousEntropy CA5_5_6I1PairValue - _)
  simpa only [sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
