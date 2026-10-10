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
def CA3_5_8I1PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 3 5 8)) (shape 3 5 8) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) a
def CA3_5_8I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 3 5 8) A3_5_8Law 1 a
lemma CA3_5_8I1PairRaw_sound (a : PairSlot × PairSlot) :
    (CA3_5_8I1PairRaw a).Encloses (CA3_5_8I1PairValue a) := by
  exact stageAPairBall_sound (shape 3 5 8) (by decide +kernel) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (fun u _ => A3_5_8Law_sound u) 1 a
def CA3_5_8I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(5272348913593376577096549739 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(10387001330832544175301137399 / 20000000000000000000000000000000), (714537 / 4000000000000000000000000000000)⟩ ⟨(-492522474378183237630433139810131 / 50000000000000000000000000000000), (169406598947 / 50000000000000000000000000000000)⟩ ⟨-15, 5272348913593376577096549739, 3051757812500000000000000000⟩,
   .log ⟨(122811663494084257624940399343 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(823117354555577221946133592311 / 100000000000000000000000000000000), (143035109 / 50000000000000000000000000000000)⟩ ⟨(-167556836854348558096548849152917 / 25000000000000000000000000000000), (46586812591 / 20000000000000000000000000000000)⟩ ⟨-10, 122811663494084257624940399343, 97656250000000000000000000000⟩,
   .log ⟨(10175855283941391205947279651 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(93545698188119245893217737667 / 100000000000000000000000000000000), (4040291 / 12500000000000000000000000000000)⟩ ⟨(-229822691994609421192137827073081 / 25000000000000000000000000000000), (19852335317 / 6250000000000000000000000000000)⟩ ⟨-14, 10175855283941391205947279651, 6103515625000000000000000000⟩,
   .log ⟨(224235380405963066391746089353 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(2424918168841216184583813792717 / 100000000000000000000000000000000), (34188257 / 4000000000000000000000000000000)⟩ ⟨(-540708197888099777971623643212661 / 100000000000000000000000000000000), (95291207019 / 50000000000000000000000000000000)⟩ ⟨-8, 224235380405963066391746089353, 195312500000000000000000000000⟩,
   .log ⟨(1272000276383149435550995439 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(25150092297347779972067219457 / 50000000000000000000000000000000), (1723883 / 10000000000000000000000000000000)⟩ ⟨(-494302021082504041007144259164429 / 50000000000000000000000000000000), (169406599291 / 50000000000000000000000000000000)⟩ ⟨-15, 1272000276383149435550995439, 762939453125000000000000000⟩,
   .log ⟨(1445038215769510822869447212491 / 50000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩ ⟨(10242104980593555395446867496803 / 100000000000000000000000000000000), (535497813 / 12500000000000000000000000000000)⟩ ⟨(-354388723731414820305031975405399 / 100000000000000000000000000000000), (148230766369 / 100000000000000000000000000000000)⟩ ⟨-6, 1445038215769510822869447212491, 781250000000000000000000000000⟩,
   .log ⟨(56502172949873789302552257373 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(688462253558737918048067279589 / 50000000000000000000000000000000), (119648009 / 25000000000000000000000000000000)⟩ ⟨(-609235200714768048615292950822617 / 100000000000000000000000000000000), (105879118857 / 50000000000000000000000000000000)⟩ ⟨-9, 56502172949873789302552257373, 48828125000000000000000000000⟩,
   .log ⟨(8530870747574296140629522643 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(2960583019633474529337396359 / 2000000000000000000000000000000), (50581511 / 100000000000000000000000000000000)⟩ ⟨(-867608684750996615247901536153503 / 100000000000000000000000000000000), (148230768711 / 50000000000000000000000000000000)⟩ ⟨-13, 8530870747574296140629522643, 6103515625000000000000000000⟩,
   .log ⟨(1543038718015251589792097624553 / 50000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩ ⟨(5367104262804562149060419304719 / 50000000000000000000000000000000), (4574516297 / 100000000000000000000000000000000)⟩ ⟨(-347826933967545006988298984818507 / 100000000000000000000000000000000), (37057691591 / 25000000000000000000000000000000)⟩ ⟨-6, 1543038718015251589792097624553, 781250000000000000000000000000⟩,
   .log ⟨(275427148849361576023785274099 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(6341927758382761730931641897 / 390625000000000000000000000000), (583239689 / 100000000000000000000000000000000)⟩ ⟨(-589460230383440015978482495632837 / 100000000000000000000000000000000), (52939559389 / 25000000000000000000000000000000)⟩ ⟨-9, 275427148849361576023785274099, 195312500000000000000000000000⟩,
   .log ⟨(102611484321130106786776176661 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(706169731946585730314410121159 / 100000000000000000000000000000000), (119508553 / 50000000000000000000000000000000)⟩ ⟨(-344098780277155025456198261537853 / 50000000000000000000000000000000), (232934061487 / 100000000000000000000000000000000)⟩ ⟨-10, 102611484321130106786776176661, 97656250000000000000000000000⟩,
   .log ⟨(14795629024906978949381729251 / 5000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(21538224249032315716749423781 / 1250000000000000000000000000000), (626619277 / 100000000000000000000000000000000)⟩ ⟨(-291143069521070637789728104358841 / 50000000000000000000000000000000), (105879118753 / 50000000000000000000000000000000)⟩ ⟨-9, 14795629024906978949381729251, 9765625000000000000000000000⟩,
   .log ⟨(26166849529392501901217802001 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(215835482673605884932772277959 / 100000000000000000000000000000000), (72033607 / 100000000000000000000000000000000)⟩ ⟨(-824843214048996718391164719348457 / 100000000000000000000000000000000), (2752857117 / 1000000000000000000000000000000)⟩ ⟨-12, 26166849529392501901217802001, 24414062500000000000000000000⟩,
   .log ⟨(1164646818453221352648590511 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(8647331230472012025573359963 / 10000000000000000000000000000000), (14797419 / 50000000000000000000000000000000)⟩ ⟨(-464053302118051969220549102328361 / 50000000000000000000000000000000), (317637365977 / 100000000000000000000000000000000)⟩ ⟨-14, 1164646818453221352648590511, 762939453125000000000000000⟩,
   .log ⟨(11587301268410179668221269739649 / 100000000000000000000000000000000), (1 / 2500000000000000000000000000000)⟩ ⟨(624341290834834164391889313543 / 2500000000000000000000000000000), (6134266279 / 50000000000000000000000000000000)⟩ ⟨(-21552604057579529378221855868007 / 10000000000000000000000000000000), (2646977969 / 2500000000000000000000000000000)⟩ ⟨-4, 11587301268410179668221269739649, 6250000000000000000000000000000⟩,
   .log ⟨(1033841032965526914852789528817 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(2363303306716034923255029059551 / 50000000000000000000000000000000), (875697429 / 50000000000000000000000000000000)⟩ ⟨(-228594458079982059043573057869503 / 50000000000000000000000000000000), (3388131797 / 2000000000000000000000000000000)⟩ ⟨-7, 1033841032965526914852789528817, 781250000000000000000000000000⟩,
   .log ⟨(383299402912290949816397030673 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(2132719676734387834400259703423 / 100000000000000000000000000000000), (405834039 / 50000000000000000000000000000000)⟩ ⟨(-556410905034049988938702852231753 / 100000000000000000000000000000000), (52939559403 / 25000000000000000000000000000000)⟩ ⟨-9, 383299402912290949816397030673, 195312500000000000000000000000⟩]
lemma CA3_5_8I1PairCertificates_valid :
    CA3_5_8I1PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I1PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 0, 0, 1, 5 => 1
  | 0, 0, 2, 4 => 2
  | 0, 0, 3, 4 => 3
  | 0, 0, 4, 2 => 2
  | 0, 0, 4, 3 => 3
  | 0, 0, 5, 1 => 1
  | 1, 0, 4, 1 => 4
  | 1, 0, 5, 0 => 5
  | 1, 0, 2, 2 => 6
  | 1, 0, 2, 3 => 7
  | 1, 0, 3, 2 => 7
  | 1, 0, 3, 3 => 8
  | 1, 0, 1, 4 => 4
  | 1, 0, 0, 5 => 5
  | 0, 1, 4, 1 => 4
  | 0, 1, 5, 0 => 5
  | 0, 1, 2, 2 => 6
  | 0, 1, 2, 3 => 7
  | 0, 1, 3, 2 => 7
  | 0, 1, 3, 3 => 8
  | 0, 1, 1, 4 => 4
  | 0, 1, 0, 5 => 5
  | 2, 0, 2, 1 => 9
  | 2, 0, 3, 1 => 10
  | 2, 0, 4, 0 => 11
  | 2, 0, 1, 2 => 9
  | 2, 0, 1, 3 => 10
  | 2, 0, 0, 4 => 11
  | 3, 0, 2, 1 => 12
  | 3, 0, 3, 1 => 13
  | 3, 0, 4, 0 => 14
  | 3, 0, 1, 2 => 12
  | 3, 0, 1, 3 => 13
  | 3, 0, 0, 4 => 14
  | 1, 1, 2, 1 => 15
  | 1, 1, 3, 1 => 16
  | 1, 1, 4, 0 => 17
  | 1, 1, 1, 2 => 15
  | 1, 1, 1, 3 => 16
  | 1, 1, 0, 4 => 17
  | 0, 2, 2, 1 => 9
  | 0, 2, 3, 1 => 10
  | 0, 2, 4, 0 => 11
  | 0, 2, 1, 2 => 9
  | 0, 2, 1, 3 => 10
  | 0, 2, 0, 4 => 11
  | 0, 3, 2, 1 => 12
  | 0, 3, 3, 1 => 13
  | 0, 3, 4, 0 => 14
  | 0, 3, 1, 2 => 12
  | 0, 3, 1, 3 => 13
  | 0, 3, 0, 4 => 14
  | 4, 0, 1, 1 => 17
  | 4, 0, 2, 0 => 11
  | 4, 0, 3, 0 => 14
  | 4, 0, 0, 2 => 11
  | 4, 0, 0, 3 => 14
  | 2, 1, 1, 1 => 15
  | 2, 1, 2, 0 => 9
  | 2, 1, 3, 0 => 12
  | 2, 1, 0, 2 => 9
  | 2, 1, 0, 3 => 12
  | 3, 1, 1, 1 => 16
  | 3, 1, 2, 0 => 10
  | 3, 1, 3, 0 => 13
  | 3, 1, 0, 2 => 10
  | 3, 1, 0, 3 => 13
  | 1, 2, 1, 1 => 15
  | 1, 2, 2, 0 => 9
  | 1, 2, 3, 0 => 12
  | 1, 2, 0, 2 => 9
  | 1, 2, 0, 3 => 12
  | 1, 3, 1, 1 => 16
  | 1, 3, 2, 0 => 10
  | 1, 3, 3, 0 => 13
  | 1, 3, 0, 2 => 10
  | 1, 3, 0, 3 => 13
  | 0, 4, 1, 1 => 17
  | 0, 4, 2, 0 => 11
  | 0, 4, 3, 0 => 14
  | 0, 4, 0, 2 => 11
  | 0, 4, 0, 3 => 14
  | 0, 5, 0, 1 => 5
  | 0, 5, 1, 0 => 5
  | 1, 4, 0, 1 => 4
  | 1, 4, 1, 0 => 4
  | 2, 2, 0, 1 => 6
  | 2, 2, 1, 0 => 6
  | 2, 3, 0, 1 => 7
  | 2, 3, 1, 0 => 7
  | 3, 2, 0, 1 => 7
  | 3, 2, 1, 0 => 7
  | 3, 3, 0, 1 => 8
  | 3, 3, 1, 0 => 8
  | 4, 1, 0, 1 => 4
  | 4, 1, 1, 0 => 4
  | 5, 0, 0, 1 => 5
  | 5, 0, 1, 0 => 5
  | 1, 5, 0, 0 => 1
  | 2, 4, 0, 0 => 2
  | 3, 4, 0, 0 => 3
  | 4, 2, 0, 0 => 2
  | 4, 3, 0, 0 => 3
  | 5, 1, 0, 0 => 1
  | _, _, _, _ => 0
def CA3_5_8I1PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1PairCertificates (CA3_5_8I1PairCertificateIndex a)).input
lemma CA3_5_8I1PairP_check_0_0 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((0,0),(k,l))) (CA3_5_8I1PairP ((0,0),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_0_1 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((0,1),(k,l))) (CA3_5_8I1PairP ((0,1),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_0_2 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((0,2),(k,l))) (CA3_5_8I1PairP ((0,2),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_0_3 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((0,3),(k,l))) (CA3_5_8I1PairP ((0,3),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_0_4 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((0,4),(k,l))) (CA3_5_8I1PairP ((0,4),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_0_5 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((0,5),(k,l))) (CA3_5_8I1PairP ((0,5),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_1_0 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((1,0),(k,l))) (CA3_5_8I1PairP ((1,0),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_1_1 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((1,1),(k,l))) (CA3_5_8I1PairP ((1,1),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_1_2 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((1,2),(k,l))) (CA3_5_8I1PairP ((1,2),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_1_3 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((1,3),(k,l))) (CA3_5_8I1PairP ((1,3),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_1_4 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((1,4),(k,l))) (CA3_5_8I1PairP ((1,4),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_1_5 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((1,5),(k,l))) (CA3_5_8I1PairP ((1,5),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_2_0 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((2,0),(k,l))) (CA3_5_8I1PairP ((2,0),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_2_1 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((2,1),(k,l))) (CA3_5_8I1PairP ((2,1),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_2_2 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((2,2),(k,l))) (CA3_5_8I1PairP ((2,2),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_2_3 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((2,3),(k,l))) (CA3_5_8I1PairP ((2,3),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_2_4 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((2,4),(k,l))) (CA3_5_8I1PairP ((2,4),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_2_5 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((2,5),(k,l))) (CA3_5_8I1PairP ((2,5),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_3_0 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((3,0),(k,l))) (CA3_5_8I1PairP ((3,0),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_3_1 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((3,1),(k,l))) (CA3_5_8I1PairP ((3,1),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_3_2 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((3,2),(k,l))) (CA3_5_8I1PairP ((3,2),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_3_3 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((3,3),(k,l))) (CA3_5_8I1PairP ((3,3),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_3_4 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((3,4),(k,l))) (CA3_5_8I1PairP ((3,4),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_3_5 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((3,5),(k,l))) (CA3_5_8I1PairP ((3,5),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_4_0 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((4,0),(k,l))) (CA3_5_8I1PairP ((4,0),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_4_1 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((4,1),(k,l))) (CA3_5_8I1PairP ((4,1),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_4_2 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((4,2),(k,l))) (CA3_5_8I1PairP ((4,2),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_4_3 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((4,3),(k,l))) (CA3_5_8I1PairP ((4,3),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_4_4 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((4,4),(k,l))) (CA3_5_8I1PairP ((4,4),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_4_5 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((4,5),(k,l))) (CA3_5_8I1PairP ((4,5),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_5_0 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((5,0),(k,l))) (CA3_5_8I1PairP ((5,0),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_5_1 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((5,1),(k,l))) (CA3_5_8I1PairP ((5,1),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_5_2 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((5,2),(k,l))) (CA3_5_8I1PairP ((5,2),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_5_3 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((5,3),(k,l))) (CA3_5_8I1PairP ((5,3),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_5_4 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((5,4),(k,l))) (CA3_5_8I1PairP ((5,4),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check_5_5 : ∀ k l : Fin 6, contains (CA3_5_8I1PairRaw ((5,5),(k,l))) (CA3_5_8I1PairP ((5,5),(k,l))) = true := by
  decide +kernel
lemma CA3_5_8I1PairP_check (a : PairSlot × PairSlot) : contains (CA3_5_8I1PairRaw a) (CA3_5_8I1PairP a) = true := by
  rcases a with ⟨⟨i,j⟩,⟨k,l⟩⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (CA3_5_8I1PairP_check_0_0 k l) (CA3_5_8I1PairP_check_0_1 k l) (CA3_5_8I1PairP_check_0_2 k l) (CA3_5_8I1PairP_check_0_3 k l) (CA3_5_8I1PairP_check_0_4 k l) (CA3_5_8I1PairP_check_0_5 k l)
  · exact forall_fin6 (CA3_5_8I1PairP_check_1_0 k l) (CA3_5_8I1PairP_check_1_1 k l) (CA3_5_8I1PairP_check_1_2 k l) (CA3_5_8I1PairP_check_1_3 k l) (CA3_5_8I1PairP_check_1_4 k l) (CA3_5_8I1PairP_check_1_5 k l)
  · exact forall_fin6 (CA3_5_8I1PairP_check_2_0 k l) (CA3_5_8I1PairP_check_2_1 k l) (CA3_5_8I1PairP_check_2_2 k l) (CA3_5_8I1PairP_check_2_3 k l) (CA3_5_8I1PairP_check_2_4 k l) (CA3_5_8I1PairP_check_2_5 k l)
  · exact forall_fin6 (CA3_5_8I1PairP_check_3_0 k l) (CA3_5_8I1PairP_check_3_1 k l) (CA3_5_8I1PairP_check_3_2 k l) (CA3_5_8I1PairP_check_3_3 k l) (CA3_5_8I1PairP_check_3_4 k l) (CA3_5_8I1PairP_check_3_5 k l)
  · exact forall_fin6 (CA3_5_8I1PairP_check_4_0 k l) (CA3_5_8I1PairP_check_4_1 k l) (CA3_5_8I1PairP_check_4_2 k l) (CA3_5_8I1PairP_check_4_3 k l) (CA3_5_8I1PairP_check_4_4 k l) (CA3_5_8I1PairP_check_4_5 k l)
  · exact forall_fin6 (CA3_5_8I1PairP_check_5_0 k l) (CA3_5_8I1PairP_check_5_1 k l) (CA3_5_8I1PairP_check_5_2 k l) (CA3_5_8I1PairP_check_5_3 k l) (CA3_5_8I1PairP_check_5_4 k l) (CA3_5_8I1PairP_check_5_5 k l)
lemma CA3_5_8I1PairP_sound (a : PairSlot × PairSlot) :
    (CA3_5_8I1PairP a).Encloses (CA3_5_8I1PairValue a) :=
  contains_sound (CA3_5_8I1PairRaw_sound a) (CA3_5_8I1PairP_check a)
def CA3_5_8I1PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1PairCertificates (CA3_5_8I1PairCertificateIndex a)).output
lemma CA3_5_8I1PairTerms_sound (a : PairSlot × PairSlot) :
    (CA3_5_8I1PairTerms a).Encloses (Foundation.entropyTerm (CA3_5_8I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I1PairCertificates_valid
    (CA3_5_8I1PairCertificateIndex a) (CA3_5_8I1PairP_sound a)
def CA3_5_8I1PairEntropy : Ball := ⟨(16214910566568980863325613590037 / 5000000000000000000000000000000), (3445353169 / 2500000000000000000000000000000)⟩
lemma CA3_5_8I1PairEntropy_sound : CA3_5_8I1PairEntropy.Encloses (Foundation.finiteEntropy CA3_5_8I1PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA3_5_8I1PairValue CA3_5_8I1PairTerms CA3_5_8I1PairTerms_sound) (by decide +kernel)
def CA3_5_8I1PairMass : Ball := ⟨(12499999999999999999999999999999 / 12500000000000000000000000000000), (67 / 12500000000000000000000000000000)⟩
lemma CA3_5_8I1PairMass_sound : CA3_5_8I1PairMass.Encloses (∑ a, CA3_5_8I1PairValue a) := by
  exact contains_sound (doublePairSumBall_sound CA3_5_8I1PairP CA3_5_8I1PairValue CA3_5_8I1PairP_sound) (by decide +kernel)
def CA3_5_8I1PairMassTermLogWitness : LogWitness := ⟨-1, 12499999999999999999999999999999, 6250000000000000000000000000000⟩
def CA3_5_8I1PairMassTermLog : Ball := ⟨(-7 / 100000000000000000000000000000000), (21175823951 / 50000000000000000000000000000000)⟩
lemma CA3_5_8I1PairMassTermLog_sound : CA3_5_8I1PairMassTermLog.Encloses (Real.log ((∑ a, CA3_5_8I1PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_5_8I1PairMass_sound) (w := CA3_5_8I1PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_5_8I1PairMassTerm : Ball := ⟨(7 / 100000000000000000000000000000000), (42351647903 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I1PairMassTerm_sound : CA3_5_8I1PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I1PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA3_5_8I1PairMass_sound) CA3_5_8I1PairMassTermLog_sound) (by decide +kernel)
def CA3_5_8I1PairH : Ball := ⟨(324298211331379617266512271800733 / 100000000000000000000000000000000), (180165774663 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I1PairH_sound : CA3_5_8I1PairH.Encloses (homogeneousEntropy CA3_5_8I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I1PairValue CA3_5_8I1PairMassTerm_sound CA3_5_8I1PairEntropy_sound) (by decide +kernel)

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
def CA3_5_8I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA3_5_8I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
lemma CA3_5_8I1R0Raw_sound (a : PairSlot) :
    (CA3_5_8I1R0Raw a).Encloses (CA3_5_8I1R0Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 0 a
def CA3_5_8I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(138259867691619025407984228733 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(1628879118491678187756967641173 / 100000000000000000000000000000000), (585553351 / 100000000000000000000000000000000)⟩ ⟨(-117812865416941003692582243865407 / 20000000000000000000000000000000), (211758238637 / 100000000000000000000000000000000)⟩ ⟨-9, 138259867691619025407984228733, 97656250000000000000000000000⟩]
lemma CA3_5_8I1R0Certificates_valid :
    CA3_5_8I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA3_5_8I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R0Certificates (CA3_5_8I1R0CertificateIndex a)).input
lemma CA3_5_8I1R0P_check : ∀ a : PairSlot, contains (CA3_5_8I1R0Raw a) (CA3_5_8I1R0P a) = true := by
  decide +kernel
lemma CA3_5_8I1R0P_sound (a : PairSlot) :
    (CA3_5_8I1R0P a).Encloses (CA3_5_8I1R0Value a) :=
  contains_sound (CA3_5_8I1R0Raw_sound a) (CA3_5_8I1R0P_check a)
def CA3_5_8I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R0Certificates (CA3_5_8I1R0CertificateIndex a)).output
lemma CA3_5_8I1R0Terms_sound (a : PairSlot) :
    (CA3_5_8I1R0Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I1R0Certificates_valid
    (CA3_5_8I1R0CertificateIndex a) (CA3_5_8I1R0P_sound a)
def CA3_5_8I1R0Entropy : Ball := ⟨(1628879118491678187756967641173 / 100000000000000000000000000000000), (585553351 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I1R0Entropy_sound : CA3_5_8I1R0Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I1R0Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I1R0Value CA3_5_8I1R0Terms CA3_5_8I1R0Terms_sound) (by decide +kernel)
def CA3_5_8I1R0Mass : Ball := ⟨(138259867691619025407984228733 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
lemma CA3_5_8I1R0Mass_sound : CA3_5_8I1R0Mass.Encloses (∑ a, CA3_5_8I1R0Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I1R0P CA3_5_8I1R0Value CA3_5_8I1R0P_sound) (by decide +kernel)
def CA3_5_8I1R0MassTermLogWitness : LogWitness := ⟨-9, 138259867691619025407984228733, 97656250000000000000000000000⟩
def CA3_5_8I1R0MassTermLog : Ball := ⟨(-117812865416941003692582243865407 / 20000000000000000000000000000000), (211758238637 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I1R0MassTermLog_sound : CA3_5_8I1R0MassTermLog.Encloses (Real.log ((∑ a, CA3_5_8I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_5_8I1R0Mass_sound) (w := CA3_5_8I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_5_8I1R0MassTerm : Ball := ⟨(1628879118491678187756967641173 / 100000000000000000000000000000000), (585553351 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I1R0MassTerm_sound : CA3_5_8I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_5_8I1R0Mass_sound) CA3_5_8I1R0MassTermLog_sound) (by decide +kernel)
def CA3_5_8I1R0H : Ball := ⟨0, (585553351 / 50000000000000000000000000000000)⟩
lemma CA3_5_8I1R0H_sound : CA3_5_8I1R0H.Encloses (homogeneousEntropy CA3_5_8I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I1R0Value CA3_5_8I1R0MassTerm_sound CA3_5_8I1R0Entropy_sound) (by decide +kernel)
def CA3_5_8I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA3_5_8I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
lemma CA3_5_8I1R1Raw_sound (a : PairSlot) :
    (CA3_5_8I1R1Raw a).Encloses (CA3_5_8I1R1Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 1 a
def CA3_5_8I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(4266273080468078013491963850177 / 100000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩ ⟨(13457657893666748061001354681387 / 100000000000000000000000000000000), (1355127719 / 25000000000000000000000000000000)⟩ ⟨(-157721477737545916086942151562357 / 50000000000000000000000000000000), (63527471283 / 50000000000000000000000000000000)⟩ ⟨-5, 4266273080468078013491963850177, 3125000000000000000000000000000⟩]
lemma CA3_5_8I1R1Certificates_valid :
    CA3_5_8I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA3_5_8I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R1Certificates (CA3_5_8I1R1CertificateIndex a)).input
lemma CA3_5_8I1R1P_check : ∀ a : PairSlot, contains (CA3_5_8I1R1Raw a) (CA3_5_8I1R1P a) = true := by
  decide +kernel
lemma CA3_5_8I1R1P_sound (a : PairSlot) :
    (CA3_5_8I1R1P a).Encloses (CA3_5_8I1R1Value a) :=
  contains_sound (CA3_5_8I1R1Raw_sound a) (CA3_5_8I1R1P_check a)
def CA3_5_8I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R1Certificates (CA3_5_8I1R1CertificateIndex a)).output
lemma CA3_5_8I1R1Terms_sound (a : PairSlot) :
    (CA3_5_8I1R1Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I1R1Certificates_valid
    (CA3_5_8I1R1CertificateIndex a) (CA3_5_8I1R1P_sound a)
def CA3_5_8I1R1Entropy : Ball := ⟨(13457657893666748061001354681387 / 50000000000000000000000000000000), (1355127719 / 12500000000000000000000000000000)⟩
lemma CA3_5_8I1R1Entropy_sound : CA3_5_8I1R1Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I1R1Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I1R1Value CA3_5_8I1R1Terms CA3_5_8I1R1Terms_sound) (by decide +kernel)
def CA3_5_8I1R1Mass : Ball := ⟨(4266273080468078013491963850177 / 50000000000000000000000000000000), (1 / 2500000000000000000000000000000)⟩
lemma CA3_5_8I1R1Mass_sound : CA3_5_8I1R1Mass.Encloses (∑ a, CA3_5_8I1R1Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I1R1P CA3_5_8I1R1Value CA3_5_8I1R1P_sound) (by decide +kernel)
def CA3_5_8I1R1MassTermLogWitness : LogWitness := ⟨-4, 4266273080468078013491963850177, 3125000000000000000000000000000⟩
def CA3_5_8I1R1MassTermLog : Ball := ⟨(-15383014838693581327010069379649 / 6250000000000000000000000000000), (105879118883 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I1R1MassTermLog_sound : CA3_5_8I1R1MassTermLog.Encloses (Real.log ((∑ a, CA3_5_8I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_5_8I1R1Mass_sound) (w := CA3_5_8I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_5_8I1R1MassTerm : Ball := ⟨(21001005472883014211656585649313 / 100000000000000000000000000000000), (1129273099 / 12500000000000000000000000000000)⟩
lemma CA3_5_8I1R1MassTerm_sound : CA3_5_8I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_5_8I1R1Mass_sound) CA3_5_8I1R1MassTermLog_sound) (by decide +kernel)
def CA3_5_8I1R1H : Ball := ⟨(5914310314450481910346123713461 / 100000000000000000000000000000000), (1242200409 / 6250000000000000000000000000000)⟩
lemma CA3_5_8I1R1H_sound : CA3_5_8I1R1H.Encloses (homogeneousEntropy CA3_5_8I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I1R1Value CA3_5_8I1R1MassTerm_sound CA3_5_8I1R1Entropy_sound) (by decide +kernel)
def CA3_5_8I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA3_5_8I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
lemma CA3_5_8I1R2Raw_sound (a : PairSlot) :
    (CA3_5_8I1R2Raw a).Encloses (CA3_5_8I1R2Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 2 a
def CA3_5_8I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1732058034600497431197378349933 / 25000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩ ⟨(18495369548193411776424744414103 / 100000000000000000000000000000000), (1467110247 / 20000000000000000000000000000000)⟩ ⟨(-33369568850177494356769160427099 / 12500000000000000000000000000000), (21175823781 / 20000000000000000000000000000000)⟩ ⟨-4, 1732058034600497431197378349933, 1562500000000000000000000000000⟩,
   .log ⟨(662793209150315703420082222219 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(3324877229360328262507473508913 / 100000000000000000000000000000000), (1263167317 / 100000000000000000000000000000000)⟩ ⟨(-501646242516989214412371807145623 / 100000000000000000000000000000000), (152465931 / 80000000000000000000000000000)⟩ ⟨-8, 662793209150315703420082222219, 390625000000000000000000000000⟩,
   .log ⟨(13004441704287997532890456299139 / 50000000000000000000000000000000), (71 / 100000000000000000000000000000000)⟩ ⟨(8756749131682586890617478494347 / 25000000000000000000000000000000), (3304557209 / 20000000000000000000000000000000)⟩ ⟨(-26934640735234931508264669871873 / 20000000000000000000000000000000), (63527471321 / 100000000000000000000000000000000)⟩ ⟨-2, 13004441704287997532890456299139, 12500000000000000000000000000000⟩]
lemma CA3_5_8I1R2Certificates_valid :
    CA3_5_8I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA3_5_8I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R2Certificates (CA3_5_8I1R2CertificateIndex a)).input
lemma CA3_5_8I1R2P_check : ∀ a : PairSlot, contains (CA3_5_8I1R2Raw a) (CA3_5_8I1R2P a) = true := by
  decide +kernel
lemma CA3_5_8I1R2P_sound (a : PairSlot) :
    (CA3_5_8I1R2P a).Encloses (CA3_5_8I1R2Value a) :=
  contains_sound (CA3_5_8I1R2Raw_sound a) (CA3_5_8I1R2P_check a)
def CA3_5_8I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R2Certificates (CA3_5_8I1R2CertificateIndex a)).output
lemma CA3_5_8I1R2Terms_sound (a : PairSlot) :
    (CA3_5_8I1R2Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I1R2Certificates_valid
    (CA3_5_8I1R2CertificateIndex a) (CA3_5_8I1R2P_sound a)
def CA3_5_8I1R2Entropy : Ball := ⟨(3933374504091891382016717491171 / 5000000000000000000000000000000), (33720223149 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I1R2Entropy_sound : CA3_5_8I1R2Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I1R2Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I1R2Value CA3_5_8I1R2Terms CA3_5_8I1R2Terms_sound) (by decide +kernel)
def CA3_5_8I1R2Mass : Ball := ⟨(2059546705184030296110005192109 / 5000000000000000000000000000000), (147 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I1R2Mass_sound : CA3_5_8I1R2Mass.Encloses (∑ a, CA3_5_8I1R2Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I1R2P CA3_5_8I1R2Value CA3_5_8I1R2P_sound) (by decide +kernel)
def CA3_5_8I1R2MassTermLogWitness : LogWitness := ⟨-2, 2059546705184030296110005192109, 1250000000000000000000000000000⟩
def CA3_5_8I1R2MassTermLog : Ball := ⟨(-44347599993672980298295301558257 / 50000000000000000000000000000000), (31763735703 / 50000000000000000000000000000000)⟩
lemma CA3_5_8I1R2MassTermLog_sound : CA3_5_8I1R2MassTermLog.Encloses (Real.log ((∑ a, CA3_5_8I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_5_8I1R2Mass_sound) (w := CA3_5_8I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_5_8I1R2MassTerm : Ball := ⟨(18267190689957701875897541677933 / 50000000000000000000000000000000), (3270944877 / 12500000000000000000000000000000)⟩
lemma CA3_5_8I1R2MassTerm_sound : CA3_5_8I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_5_8I1R2Mass_sound) CA3_5_8I1R2MassTermLog_sound) (by decide +kernel)
def CA3_5_8I1R2H : Ball := ⟨(21066554350961211944269633233777 / 50000000000000000000000000000000), (11977556433 / 20000000000000000000000000000000)⟩
lemma CA3_5_8I1R2H_sound : CA3_5_8I1R2H.Encloses (homogeneousEntropy CA3_5_8I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I1R2Value CA3_5_8I1R2MassTerm_sound CA3_5_8I1R2Entropy_sound) (by decide +kernel)
def CA3_5_8I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA3_5_8I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
lemma CA3_5_8I1R3Raw_sound (a : PairSlot) :
    (CA3_5_8I1R3Raw a).Encloses (CA3_5_8I1R3Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 3 a
def CA3_5_8I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(151789180162450676258081708043 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(309901200454757306092904831649 / 10000000000000000000000000000000), (231426791 / 20000000000000000000000000000000)⟩ ⟨(-255206925917816576652681312921111 / 50000000000000000000000000000000), (38116482761 / 20000000000000000000000000000000)⟩ ⟨-8, 151789180162450676258081708043, 97656250000000000000000000000⟩,
   .log ⟨(18351281301467465185364929407901 / 100000000000000000000000000000000), (43 / 100000000000000000000000000000000)⟩ ⟨(31114061373269187099674069289423 / 100000000000000000000000000000000), (3108828001 / 20000000000000000000000000000000)⟩ ⟨(-84773539411608122276290691627311 / 50000000000000000000000000000000), (42351647483 / 50000000000000000000000000000000)⟩ ⟨-3, 18351281301467465185364929407901, 12500000000000000000000000000000⟩,
   .log ⟨(1637029029723035070702795681017 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(6731933450091206156308259969981 / 100000000000000000000000000000000), (2426580693 / 100000000000000000000000000000000)⟩ ⟨(-205614357713319399022491729032407 / 50000000000000000000000000000000), (29646153217 / 20000000000000000000000000000000)⟩ ⟨-6, 1637029029723035070702795681017, 1562500000000000000000000000000⟩]
lemma CA3_5_8I1R3Certificates_valid :
    CA3_5_8I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA3_5_8I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R3Certificates (CA3_5_8I1R3CertificateIndex a)).input
lemma CA3_5_8I1R3P_check : ∀ a : PairSlot, contains (CA3_5_8I1R3Raw a) (CA3_5_8I1R3P a) = true := by
  decide +kernel
lemma CA3_5_8I1R3P_sound (a : PairSlot) :
    (CA3_5_8I1R3P a).Encloses (CA3_5_8I1R3Value a) :=
  contains_sound (CA3_5_8I1R3Raw_sound a) (CA3_5_8I1R3P_check a)
def CA3_5_8I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R3Certificates (CA3_5_8I1R3CertificateIndex a)).output
lemma CA3_5_8I1R3Terms_sound (a : PairSlot) :
    (CA3_5_8I1R3Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I1R3Certificates_valid
    (CA3_5_8I1R3CertificateIndex a) (CA3_5_8I1R3P_sound a)
def CA3_5_8I1R3Entropy : Ball := ⟨(20472503413953983158455688787947 / 25000000000000000000000000000000), (19127854653 / 50000000000000000000000000000000)⟩
lemma CA3_5_8I1R3Entropy_sound : CA3_5_8I1R3Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I1R3Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I1R3Value CA3_5_8I1R3Terms CA3_5_8I1R3Terms_sound) (by decide +kernel)
def CA3_5_8I1R3Mass : Ball := ⟨(2059546705184030296110005192109 / 5000000000000000000000000000000), (13 / 12500000000000000000000000000000)⟩
lemma CA3_5_8I1R3Mass_sound : CA3_5_8I1R3Mass.Encloses (∑ a, CA3_5_8I1R3Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I1R3P CA3_5_8I1R3Value CA3_5_8I1R3P_sound) (by decide +kernel)
def CA3_5_8I1R3MassTermLogWitness : LogWitness := ⟨-2, 2059546705184030296110005192109, 1250000000000000000000000000000⟩
def CA3_5_8I1R3MassTermLog : Ball := ⟨(-44347599993672980298295301558257 / 50000000000000000000000000000000), (63527471301 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I1R3MassTermLog_sound : CA3_5_8I1R3MassTermLog.Encloses (Real.log ((∑ a, CA3_5_8I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_5_8I1R3Mass_sound) (w := CA3_5_8I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_5_8I1R3MassTerm : Ball := ⟨(18267190689957701875897541677933 / 50000000000000000000000000000000), (13083779467 / 50000000000000000000000000000000)⟩
lemma CA3_5_8I1R3MassTerm_sound : CA3_5_8I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I1R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_5_8I1R3Mass_sound) CA3_5_8I1R3MassTermLog_sound) (by decide +kernel)
def CA3_5_8I1R3H : Ball := ⟨(22677816137950264441013835897961 / 50000000000000000000000000000000), (805290853 / 1250000000000000000000000000000)⟩
lemma CA3_5_8I1R3H_sound : CA3_5_8I1R3H.Encloses (homogeneousEntropy CA3_5_8I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I1R3Value CA3_5_8I1R3MassTerm_sound CA3_5_8I1R3Entropy_sound) (by decide +kernel)
def CA3_5_8I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA3_5_8I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
lemma CA3_5_8I1R4Raw_sound (a : PairSlot) :
    (CA3_5_8I1R4Raw a).Encloses (CA3_5_8I1R4Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 4 a
def CA3_5_8I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1272000276383149435550995439 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(93546901947419510135397426799 / 100000000000000000000000000000000), (6464559 / 20000000000000000000000000000000)⟩ ⟨(-14363895689203336735508833207477 / 1562500000000000000000000000000), (19852335317 / 6250000000000000000000000000000)⟩ ⟨-14, 1272000276383149435550995439, 762939453125000000000000000⟩,
   .log ⟨(224235380405963066391746089353 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(52851548135521399408730381197 / 1250000000000000000000000000000), (379869519 / 25000000000000000000000000000000)⟩ ⟨(-471393479832105247029900450162331 / 100000000000000000000000000000000), (42351647533 / 25000000000000000000000000000000)⟩ ⟨-7, 224235380405963066391746089353, 195312500000000000000000000000⟩,
   .log ⟨(1156030572615608658295557769993 / 20000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩ ⟨(16477713300939069480092853639993 / 100000000000000000000000000000000), (734396999 / 10000000000000000000000000000000)⟩ ⟨(-71268501418855072340827195588763 / 25000000000000000000000000000000), (127054942617 / 100000000000000000000000000000000)⟩ ⟨-5, 1156030572615608658295557769993, 625000000000000000000000000000⟩,
   .log ⟨(56502172949873789302552257373 / 12500000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(97621377569169130847325550283 / 4000000000000000000000000000000), (430732829 / 50000000000000000000000000000000)⟩ ⟨(-539920482658773517673569757772287 / 100000000000000000000000000000000), (19058241381 / 10000000000000000000000000000000)⟩ ⟨-8, 56502172949873789302552257373, 48828125000000000000000000000⟩,
   .log ⟨(8530870747574296140629522643 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(136202852968868853925447540013 / 50000000000000000000000000000000), (93937081 / 100000000000000000000000000000000)⟩ ⟨(-798293966695002084306178343103173 / 100000000000000000000000000000000), (275285710809 / 100000000000000000000000000000000)⟩ ⟨-12, 8530870747574296140629522643, 6103515625000000000000000000⟩]
lemma CA3_5_8I1R4Certificates_valid :
    CA3_5_8I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I1R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA3_5_8I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R4Certificates (CA3_5_8I1R4CertificateIndex a)).input
lemma CA3_5_8I1R4P_check : ∀ a : PairSlot, contains (CA3_5_8I1R4Raw a) (CA3_5_8I1R4P a) = true := by
  decide +kernel
lemma CA3_5_8I1R4P_sound (a : PairSlot) :
    (CA3_5_8I1R4P a).Encloses (CA3_5_8I1R4Value a) :=
  contains_sound (CA3_5_8I1R4Raw_sound a) (CA3_5_8I1R4P_check a)
def CA3_5_8I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R4Certificates (CA3_5_8I1R4CertificateIndex a)).output
lemma CA3_5_8I1R4Terms_sound (a : PairSlot) :
    (CA3_5_8I1R4Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I1R4Certificates_valid
    (CA3_5_8I1R4CertificateIndex a) (CA3_5_8I1R4P_sound a)
def CA3_5_8I1R4Entropy : Ball := ⟨(30274529390913526655977682079287 / 100000000000000000000000000000000), (12264440129 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I1R4Entropy_sound : CA3_5_8I1R4Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I1R4Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I1R4Value CA3_5_8I1R4Terms CA3_5_8I1R4Terms_sound) (by decide +kernel)
def CA3_5_8I1R4Mass : Ball := ⟨(8532546160936156026983927700353 / 100000000000000000000000000000000), (51 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I1R4Mass_sound : CA3_5_8I1R4Mass.Encloses (∑ a, CA3_5_8I1R4Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I1R4P CA3_5_8I1R4Value CA3_5_8I1R4P_sound) (by decide +kernel)
def CA3_5_8I1R4MassTermLogWitness : LogWitness := ⟨-4, 8532546160936156026983927700353, 6250000000000000000000000000000⟩
def CA3_5_8I1R4MassTermLog : Ball := ⟨(-49225647483819460246432222014879 / 20000000000000000000000000000000), (26469779753 / 25000000000000000000000000000000)⟩
lemma CA3_5_8I1R4MassTermLog_sound : CA3_5_8I1R4MassTermLog.Encloses (Real.log ((∑ a, CA3_5_8I1R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_5_8I1R4Mass_sound) (w := CA3_5_8I1R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_5_8I1R4MassTerm : Ball := ⟨(656281421027594194114268301541 / 3125000000000000000000000000000), (9034184831 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I1R4MassTerm_sound : CA3_5_8I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I1R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_5_8I1R4Mass_sound) CA3_5_8I1R4MassTermLog_sound) (by decide +kernel)
def CA3_5_8I1R4H : Ball := ⟨(370940956721220497772843857199 / 4000000000000000000000000000000), (66558203 / 312500000000000000000000000000)⟩
lemma CA3_5_8I1R4H_sound : CA3_5_8I1R4H.Encloses (homogeneousEntropy CA3_5_8I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I1R4Value CA3_5_8I1R4MassTerm_sound CA3_5_8I1R4Entropy_sound) (by decide +kernel)
def CA3_5_8I1R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 5 a
def CA3_5_8I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
lemma CA3_5_8I1R5Raw_sound (a : PairSlot) :
    (CA3_5_8I1R5Raw a).Encloses (CA3_5_8I1R5Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 5 a
def CA3_5_8I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(5272203925092215934029514299 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(51933723438763325915614291737 / 100000000000000000000000000000000), (17862933 / 100000000000000000000000000000000)⟩ ⟨(-39401907950937201261276430437901 / 4000000000000000000000000000000), (67762639579 / 20000000000000000000000000000000)⟩ ⟨-15, 5272203925092215934029514299, 3051757812500000000000000000⟩,
   .log ⟨(61404626659784376348493931181 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(823103611057719379002926802197 / 100000000000000000000000000000000), (71516151 / 25000000000000000000000000000000)⟩ ⟨(-134045861986616909564646490828711 / 20000000000000000000000000000000), (46586812591 / 20000000000000000000000000000000)⟩ ⟨-10, 61404626659784376348493931181, 48828125000000000000000000000⟩,
   .log ⟨(10175601786320755287480586361 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(93543621302358779159912357719 / 100000000000000000000000000000000), (32321523 / 100000000000000000000000000000000)⟩ ⟨(-114911657397146714345255337106347 / 12500000000000000000000000000000), (19852335317 / 6250000000000000000000000000000)⟩ ⟨-14, 10175601786320755287480586361, 6103515625000000000000000000⟩]
lemma CA3_5_8I1R5Certificates_valid :
    CA3_5_8I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 5 => 1
  | 2, 4 => 2
  | 3, 4 => 3
  | 4, 2 => 2
  | 4, 3 => 3
  | 5, 1 => 1
  | _, _ => 0
def CA3_5_8I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R5Certificates (CA3_5_8I1R5CertificateIndex a)).input
lemma CA3_5_8I1R5P_check : ∀ a : PairSlot, contains (CA3_5_8I1R5Raw a) (CA3_5_8I1R5P a) = true := by
  decide +kernel
lemma CA3_5_8I1R5P_sound (a : PairSlot) :
    (CA3_5_8I1R5P a).Encloses (CA3_5_8I1R5Value a) :=
  contains_sound (CA3_5_8I1R5Raw_sound a) (CA3_5_8I1R5P_check a)
def CA3_5_8I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R5Certificates (CA3_5_8I1R5CertificateIndex a)).output
lemma CA3_5_8I1R5Terms_sound (a : PairSlot) :
    (CA3_5_8I1R5Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I1R5Certificates_valid
    (CA3_5_8I1R5CertificateIndex a) (CA3_5_8I1R5P_sound a)
def CA3_5_8I1R5Entropy : Ball := ⟨(968580955798841484078453451653 / 50000000000000000000000000000000), (16812453 / 2500000000000000000000000000000)⟩
lemma CA3_5_8I1R5Entropy_sound : CA3_5_8I1R5Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I1R5Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I1R5Value CA3_5_8I1R5Terms CA3_5_8I1R5Terms_sound) (by decide +kernel)
def CA3_5_8I1R5Mass : Ball := ⟨(69128529515490861959248981511 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
lemma CA3_5_8I1R5Mass_sound : CA3_5_8I1R5Mass.Encloses (∑ a, CA3_5_8I1R5Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I1R5P CA3_5_8I1R5Value CA3_5_8I1R5P_sound) (by decide +kernel)
def CA3_5_8I1R5MassTermLogWitness : LogWitness := ⟨-9, 69128529515490861959248981511, 48828125000000000000000000000⟩
def CA3_5_8I1R5MassTermLog : Ball := ⟨(-147266589635318730006094524319141 / 25000000000000000000000000000000), (105879120223 / 50000000000000000000000000000000)⟩
lemma CA3_5_8I1R5MassTermLog_sound : CA3_5_8I1R5MassTermLog.Encloses (Real.log ((∑ a, CA3_5_8I1R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_5_8I1R5Mass_sound) (w := CA3_5_8I1R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_5_8I1R5MassTerm : Ball := ⟨(1628851646120129836860628761549 / 100000000000000000000000000000000), (585541491 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I1R5MassTerm_sound : CA3_5_8I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I1R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_5_8I1R5Mass_sound) CA3_5_8I1R5MassTermLog_sound) (by decide +kernel)
def CA3_5_8I1R5H : Ball := ⟨(308310265477553131296278141757 / 100000000000000000000000000000000), (1258039611 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I1R5H_sound : CA3_5_8I1R5H.Encloses (homogeneousEntropy CA3_5_8I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I1R5Value CA3_5_8I1R5MassTerm_sound CA3_5_8I1R5Entropy_sound) (by decide +kernel)
def CA3_5_8I1R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 6 a
def CA3_5_8I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
lemma CA3_5_8I1R6Raw_sound (a : PairSlot) :
    (CA3_5_8I1R6Raw a).Encloses (CA3_5_8I1R6Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 6 a
def CA3_5_8I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_5_8I1R6Certificates_valid :
    CA3_5_8I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I1R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_5_8I1R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R6Certificates (CA3_5_8I1R6CertificateIndex a)).input
lemma CA3_5_8I1R6P_check : ∀ a : PairSlot, contains (CA3_5_8I1R6Raw a) (CA3_5_8I1R6P a) = true := by
  decide +kernel
lemma CA3_5_8I1R6P_sound (a : PairSlot) :
    (CA3_5_8I1R6P a).Encloses (CA3_5_8I1R6Value a) :=
  contains_sound (CA3_5_8I1R6Raw_sound a) (CA3_5_8I1R6P_check a)
def CA3_5_8I1R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R6Certificates (CA3_5_8I1R6CertificateIndex a)).output
lemma CA3_5_8I1R6Terms_sound (a : PairSlot) :
    (CA3_5_8I1R6Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I1R6Certificates_valid
    (CA3_5_8I1R6CertificateIndex a) (CA3_5_8I1R6P_sound a)
def CA3_5_8I1R6Entropy : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R6Entropy_sound : CA3_5_8I1R6Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I1R6Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I1R6Value CA3_5_8I1R6Terms CA3_5_8I1R6Terms_sound) (by decide +kernel)
def CA3_5_8I1R6Mass : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R6Mass_sound : CA3_5_8I1R6Mass.Encloses (∑ a, CA3_5_8I1R6Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I1R6P CA3_5_8I1R6Value CA3_5_8I1R6P_sound) (by decide +kernel)
def CA3_5_8I1R6MassTerm : Ball := .exact 0
lemma CA3_5_8I1R6MassTerm_sound : CA3_5_8I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I1R6Value a))) :=
  entropyTerm_zero_ball (CA3_5_8I1R6Mass_sound)
def CA3_5_8I1R6H : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R6H_sound : CA3_5_8I1R6H.Encloses (homogeneousEntropy CA3_5_8I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I1R6Value CA3_5_8I1R6MassTerm_sound CA3_5_8I1R6Entropy_sound) (by decide +kernel)
def CA3_5_8I1R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 7 a
def CA3_5_8I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
lemma CA3_5_8I1R7Raw_sound (a : PairSlot) :
    (CA3_5_8I1R7Raw a).Encloses (CA3_5_8I1R7Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 7 a
def CA3_5_8I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_5_8I1R7Certificates_valid :
    CA3_5_8I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I1R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_5_8I1R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R7Certificates (CA3_5_8I1R7CertificateIndex a)).input
lemma CA3_5_8I1R7P_check : ∀ a : PairSlot, contains (CA3_5_8I1R7Raw a) (CA3_5_8I1R7P a) = true := by
  decide +kernel
lemma CA3_5_8I1R7P_sound (a : PairSlot) :
    (CA3_5_8I1R7P a).Encloses (CA3_5_8I1R7Value a) :=
  contains_sound (CA3_5_8I1R7Raw_sound a) (CA3_5_8I1R7P_check a)
def CA3_5_8I1R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R7Certificates (CA3_5_8I1R7CertificateIndex a)).output
lemma CA3_5_8I1R7Terms_sound (a : PairSlot) :
    (CA3_5_8I1R7Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I1R7Certificates_valid
    (CA3_5_8I1R7CertificateIndex a) (CA3_5_8I1R7P_sound a)
def CA3_5_8I1R7Entropy : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R7Entropy_sound : CA3_5_8I1R7Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I1R7Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I1R7Value CA3_5_8I1R7Terms CA3_5_8I1R7Terms_sound) (by decide +kernel)
def CA3_5_8I1R7Mass : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R7Mass_sound : CA3_5_8I1R7Mass.Encloses (∑ a, CA3_5_8I1R7Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I1R7P CA3_5_8I1R7Value CA3_5_8I1R7P_sound) (by decide +kernel)
def CA3_5_8I1R7MassTerm : Ball := .exact 0
lemma CA3_5_8I1R7MassTerm_sound : CA3_5_8I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I1R7Value a))) :=
  entropyTerm_zero_ball (CA3_5_8I1R7Mass_sound)
def CA3_5_8I1R7H : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R7H_sound : CA3_5_8I1R7H.Encloses (homogeneousEntropy CA3_5_8I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I1R7Value CA3_5_8I1R7MassTerm_sound CA3_5_8I1R7Entropy_sound) (by decide +kernel)
def CA3_5_8I1R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 8 a
def CA3_5_8I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
lemma CA3_5_8I1R8Raw_sound (a : PairSlot) :
    (CA3_5_8I1R8Raw a).Encloses (CA3_5_8I1R8Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 8 a
def CA3_5_8I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_5_8I1R8Certificates_valid :
    CA3_5_8I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_5_8I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R8Certificates (CA3_5_8I1R8CertificateIndex a)).input
lemma CA3_5_8I1R8P_check : ∀ a : PairSlot, contains (CA3_5_8I1R8Raw a) (CA3_5_8I1R8P a) = true := by
  decide +kernel
lemma CA3_5_8I1R8P_sound (a : PairSlot) :
    (CA3_5_8I1R8P a).Encloses (CA3_5_8I1R8Value a) :=
  contains_sound (CA3_5_8I1R8Raw_sound a) (CA3_5_8I1R8P_check a)
def CA3_5_8I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R8Certificates (CA3_5_8I1R8CertificateIndex a)).output
lemma CA3_5_8I1R8Terms_sound (a : PairSlot) :
    (CA3_5_8I1R8Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I1R8Certificates_valid
    (CA3_5_8I1R8CertificateIndex a) (CA3_5_8I1R8P_sound a)
def CA3_5_8I1R8Entropy : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R8Entropy_sound : CA3_5_8I1R8Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I1R8Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I1R8Value CA3_5_8I1R8Terms CA3_5_8I1R8Terms_sound) (by decide +kernel)
def CA3_5_8I1R8Mass : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R8Mass_sound : CA3_5_8I1R8Mass.Encloses (∑ a, CA3_5_8I1R8Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I1R8P CA3_5_8I1R8Value CA3_5_8I1R8P_sound) (by decide +kernel)
def CA3_5_8I1R8MassTerm : Ball := .exact 0
lemma CA3_5_8I1R8MassTerm_sound : CA3_5_8I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I1R8Value a))) :=
  entropyTerm_zero_ball (CA3_5_8I1R8Mass_sound)
def CA3_5_8I1R8H : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R8H_sound : CA3_5_8I1R8H.Encloses (homogeneousEntropy CA3_5_8I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I1R8Value CA3_5_8I1R8MassTerm_sound CA3_5_8I1R8Entropy_sound) (by decide +kernel)
def CA3_5_8I1R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 9 a
def CA3_5_8I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
lemma CA3_5_8I1R9Raw_sound (a : PairSlot) :
    (CA3_5_8I1R9Raw a).Encloses (CA3_5_8I1R9Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 9 a
def CA3_5_8I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_5_8I1R9Certificates_valid :
    CA3_5_8I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_5_8I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R9Certificates (CA3_5_8I1R9CertificateIndex a)).input
lemma CA3_5_8I1R9P_check : ∀ a : PairSlot, contains (CA3_5_8I1R9Raw a) (CA3_5_8I1R9P a) = true := by
  decide +kernel
lemma CA3_5_8I1R9P_sound (a : PairSlot) :
    (CA3_5_8I1R9P a).Encloses (CA3_5_8I1R9Value a) :=
  contains_sound (CA3_5_8I1R9Raw_sound a) (CA3_5_8I1R9P_check a)
def CA3_5_8I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R9Certificates (CA3_5_8I1R9CertificateIndex a)).output
lemma CA3_5_8I1R9Terms_sound (a : PairSlot) :
    (CA3_5_8I1R9Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I1R9Certificates_valid
    (CA3_5_8I1R9CertificateIndex a) (CA3_5_8I1R9P_sound a)
def CA3_5_8I1R9Entropy : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R9Entropy_sound : CA3_5_8I1R9Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I1R9Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I1R9Value CA3_5_8I1R9Terms CA3_5_8I1R9Terms_sound) (by decide +kernel)
def CA3_5_8I1R9Mass : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R9Mass_sound : CA3_5_8I1R9Mass.Encloses (∑ a, CA3_5_8I1R9Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I1R9P CA3_5_8I1R9Value CA3_5_8I1R9P_sound) (by decide +kernel)
def CA3_5_8I1R9MassTerm : Ball := .exact 0
lemma CA3_5_8I1R9MassTerm_sound : CA3_5_8I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I1R9Value a))) :=
  entropyTerm_zero_ball (CA3_5_8I1R9Mass_sound)
def CA3_5_8I1R9H : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R9H_sound : CA3_5_8I1R9H.Encloses (homogeneousEntropy CA3_5_8I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I1R9Value CA3_5_8I1R9MassTerm_sound CA3_5_8I1R9Entropy_sound) (by decide +kernel)
def CA3_5_8I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA3_5_8I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
lemma CA3_5_8I1R10Raw_sound (a : PairSlot) :
    (CA3_5_8I1R10Raw a).Encloses (CA3_5_8I1R10Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 10 a
def CA3_5_8I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_5_8I1R10Certificates_valid :
    CA3_5_8I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_5_8I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R10Certificates (CA3_5_8I1R10CertificateIndex a)).input
lemma CA3_5_8I1R10P_check : ∀ a : PairSlot, contains (CA3_5_8I1R10Raw a) (CA3_5_8I1R10P a) = true := by
  decide +kernel
lemma CA3_5_8I1R10P_sound (a : PairSlot) :
    (CA3_5_8I1R10P a).Encloses (CA3_5_8I1R10Value a) :=
  contains_sound (CA3_5_8I1R10Raw_sound a) (CA3_5_8I1R10P_check a)
def CA3_5_8I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R10Certificates (CA3_5_8I1R10CertificateIndex a)).output
lemma CA3_5_8I1R10Terms_sound (a : PairSlot) :
    (CA3_5_8I1R10Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I1R10Certificates_valid
    (CA3_5_8I1R10CertificateIndex a) (CA3_5_8I1R10P_sound a)
def CA3_5_8I1R10Entropy : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R10Entropy_sound : CA3_5_8I1R10Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I1R10Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I1R10Value CA3_5_8I1R10Terms CA3_5_8I1R10Terms_sound) (by decide +kernel)
def CA3_5_8I1R10Mass : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R10Mass_sound : CA3_5_8I1R10Mass.Encloses (∑ a, CA3_5_8I1R10Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I1R10P CA3_5_8I1R10Value CA3_5_8I1R10P_sound) (by decide +kernel)
def CA3_5_8I1R10MassTerm : Ball := .exact 0
lemma CA3_5_8I1R10MassTerm_sound : CA3_5_8I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I1R10Value a))) :=
  entropyTerm_zero_ball (CA3_5_8I1R10Mass_sound)
def CA3_5_8I1R10H : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R10H_sound : CA3_5_8I1R10H.Encloses (homogeneousEntropy CA3_5_8I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I1R10Value CA3_5_8I1R10MassTerm_sound CA3_5_8I1R10Entropy_sound) (by decide +kernel)
def CA3_5_8I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA3_5_8I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
lemma CA3_5_8I1R11Raw_sound (a : PairSlot) :
    (CA3_5_8I1R11Raw a).Encloses (CA3_5_8I1R11Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 11 a
def CA3_5_8I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_5_8I1R11Certificates_valid :
    CA3_5_8I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_5_8I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R11Certificates (CA3_5_8I1R11CertificateIndex a)).input
lemma CA3_5_8I1R11P_check : ∀ a : PairSlot, contains (CA3_5_8I1R11Raw a) (CA3_5_8I1R11P a) = true := by
  decide +kernel
lemma CA3_5_8I1R11P_sound (a : PairSlot) :
    (CA3_5_8I1R11P a).Encloses (CA3_5_8I1R11Value a) :=
  contains_sound (CA3_5_8I1R11Raw_sound a) (CA3_5_8I1R11P_check a)
def CA3_5_8I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R11Certificates (CA3_5_8I1R11CertificateIndex a)).output
lemma CA3_5_8I1R11Terms_sound (a : PairSlot) :
    (CA3_5_8I1R11Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I1R11Certificates_valid
    (CA3_5_8I1R11CertificateIndex a) (CA3_5_8I1R11P_sound a)
def CA3_5_8I1R11Entropy : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R11Entropy_sound : CA3_5_8I1R11Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I1R11Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I1R11Value CA3_5_8I1R11Terms CA3_5_8I1R11Terms_sound) (by decide +kernel)
def CA3_5_8I1R11Mass : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R11Mass_sound : CA3_5_8I1R11Mass.Encloses (∑ a, CA3_5_8I1R11Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I1R11P CA3_5_8I1R11Value CA3_5_8I1R11P_sound) (by decide +kernel)
def CA3_5_8I1R11MassTerm : Ball := .exact 0
lemma CA3_5_8I1R11MassTerm_sound : CA3_5_8I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I1R11Value a))) :=
  entropyTerm_zero_ball (CA3_5_8I1R11Mass_sound)
def CA3_5_8I1R11H : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R11H_sound : CA3_5_8I1R11H.Encloses (homogeneousEntropy CA3_5_8I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I1R11Value CA3_5_8I1R11MassTerm_sound CA3_5_8I1R11Entropy_sound) (by decide +kernel)
def CA3_5_8I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA3_5_8I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
lemma CA3_5_8I1R12Raw_sound (a : PairSlot) :
    (CA3_5_8I1R12Raw a).Encloses (CA3_5_8I1R12Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 12 a
def CA3_5_8I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_5_8I1R12Certificates_valid :
    CA3_5_8I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_5_8I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R12Certificates (CA3_5_8I1R12CertificateIndex a)).input
lemma CA3_5_8I1R12P_check : ∀ a : PairSlot, contains (CA3_5_8I1R12Raw a) (CA3_5_8I1R12P a) = true := by
  decide +kernel
lemma CA3_5_8I1R12P_sound (a : PairSlot) :
    (CA3_5_8I1R12P a).Encloses (CA3_5_8I1R12Value a) :=
  contains_sound (CA3_5_8I1R12Raw_sound a) (CA3_5_8I1R12P_check a)
def CA3_5_8I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R12Certificates (CA3_5_8I1R12CertificateIndex a)).output
lemma CA3_5_8I1R12Terms_sound (a : PairSlot) :
    (CA3_5_8I1R12Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I1R12Certificates_valid
    (CA3_5_8I1R12CertificateIndex a) (CA3_5_8I1R12P_sound a)
def CA3_5_8I1R12Entropy : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R12Entropy_sound : CA3_5_8I1R12Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I1R12Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I1R12Value CA3_5_8I1R12Terms CA3_5_8I1R12Terms_sound) (by decide +kernel)
def CA3_5_8I1R12Mass : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R12Mass_sound : CA3_5_8I1R12Mass.Encloses (∑ a, CA3_5_8I1R12Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I1R12P CA3_5_8I1R12Value CA3_5_8I1R12P_sound) (by decide +kernel)
def CA3_5_8I1R12MassTerm : Ball := .exact 0
lemma CA3_5_8I1R12MassTerm_sound : CA3_5_8I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I1R12Value a))) :=
  entropyTerm_zero_ball (CA3_5_8I1R12Mass_sound)
def CA3_5_8I1R12H : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R12H_sound : CA3_5_8I1R12H.Encloses (homogeneousEntropy CA3_5_8I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I1R12Value CA3_5_8I1R12MassTerm_sound CA3_5_8I1R12Entropy_sound) (by decide +kernel)
def CA3_5_8I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA3_5_8I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
lemma CA3_5_8I1R13Raw_sound (a : PairSlot) :
    (CA3_5_8I1R13Raw a).Encloses (CA3_5_8I1R13Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 13 a
def CA3_5_8I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_5_8I1R13Certificates_valid :
    CA3_5_8I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_5_8I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R13Certificates (CA3_5_8I1R13CertificateIndex a)).input
lemma CA3_5_8I1R13P_check : ∀ a : PairSlot, contains (CA3_5_8I1R13Raw a) (CA3_5_8I1R13P a) = true := by
  decide +kernel
lemma CA3_5_8I1R13P_sound (a : PairSlot) :
    (CA3_5_8I1R13P a).Encloses (CA3_5_8I1R13Value a) :=
  contains_sound (CA3_5_8I1R13Raw_sound a) (CA3_5_8I1R13P_check a)
def CA3_5_8I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R13Certificates (CA3_5_8I1R13CertificateIndex a)).output
lemma CA3_5_8I1R13Terms_sound (a : PairSlot) :
    (CA3_5_8I1R13Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I1R13Certificates_valid
    (CA3_5_8I1R13CertificateIndex a) (CA3_5_8I1R13P_sound a)
def CA3_5_8I1R13Entropy : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R13Entropy_sound : CA3_5_8I1R13Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I1R13Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I1R13Value CA3_5_8I1R13Terms CA3_5_8I1R13Terms_sound) (by decide +kernel)
def CA3_5_8I1R13Mass : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R13Mass_sound : CA3_5_8I1R13Mass.Encloses (∑ a, CA3_5_8I1R13Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I1R13P CA3_5_8I1R13Value CA3_5_8I1R13P_sound) (by decide +kernel)
def CA3_5_8I1R13MassTerm : Ball := .exact 0
lemma CA3_5_8I1R13MassTerm_sound : CA3_5_8I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I1R13Value a))) :=
  entropyTerm_zero_ball (CA3_5_8I1R13Mass_sound)
def CA3_5_8I1R13H : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R13H_sound : CA3_5_8I1R13H.Encloses (homogeneousEntropy CA3_5_8I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I1R13Value CA3_5_8I1R13MassTerm_sound CA3_5_8I1R13Entropy_sound) (by decide +kernel)
def CA3_5_8I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA3_5_8I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
lemma CA3_5_8I1R14Raw_sound (a : PairSlot) :
    (CA3_5_8I1R14Raw a).Encloses (CA3_5_8I1R14Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 14 a
def CA3_5_8I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_5_8I1R14Certificates_valid :
    CA3_5_8I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_5_8I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R14Certificates (CA3_5_8I1R14CertificateIndex a)).input
lemma CA3_5_8I1R14P_check : ∀ a : PairSlot, contains (CA3_5_8I1R14Raw a) (CA3_5_8I1R14P a) = true := by
  decide +kernel
lemma CA3_5_8I1R14P_sound (a : PairSlot) :
    (CA3_5_8I1R14P a).Encloses (CA3_5_8I1R14Value a) :=
  contains_sound (CA3_5_8I1R14Raw_sound a) (CA3_5_8I1R14P_check a)
def CA3_5_8I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R14Certificates (CA3_5_8I1R14CertificateIndex a)).output
lemma CA3_5_8I1R14Terms_sound (a : PairSlot) :
    (CA3_5_8I1R14Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I1R14Certificates_valid
    (CA3_5_8I1R14CertificateIndex a) (CA3_5_8I1R14P_sound a)
def CA3_5_8I1R14Entropy : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R14Entropy_sound : CA3_5_8I1R14Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I1R14Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I1R14Value CA3_5_8I1R14Terms CA3_5_8I1R14Terms_sound) (by decide +kernel)
def CA3_5_8I1R14Mass : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R14Mass_sound : CA3_5_8I1R14Mass.Encloses (∑ a, CA3_5_8I1R14Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I1R14P CA3_5_8I1R14Value CA3_5_8I1R14P_sound) (by decide +kernel)
def CA3_5_8I1R14MassTerm : Ball := .exact 0
lemma CA3_5_8I1R14MassTerm_sound : CA3_5_8I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I1R14Value a))) :=
  entropyTerm_zero_ball (CA3_5_8I1R14Mass_sound)
def CA3_5_8I1R14H : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R14H_sound : CA3_5_8I1R14H.Encloses (homogeneousEntropy CA3_5_8I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I1R14Value CA3_5_8I1R14MassTerm_sound CA3_5_8I1R14Entropy_sound) (by decide +kernel)
def CA3_5_8I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA3_5_8I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
lemma CA3_5_8I1R15Raw_sound (a : PairSlot) :
    (CA3_5_8I1R15Raw a).Encloses (CA3_5_8I1R15Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 15 a
def CA3_5_8I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_5_8I1R15Certificates_valid :
    CA3_5_8I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_5_8I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R15Certificates (CA3_5_8I1R15CertificateIndex a)).input
lemma CA3_5_8I1R15P_check : ∀ a : PairSlot, contains (CA3_5_8I1R15Raw a) (CA3_5_8I1R15P a) = true := by
  decide +kernel
lemma CA3_5_8I1R15P_sound (a : PairSlot) :
    (CA3_5_8I1R15P a).Encloses (CA3_5_8I1R15Value a) :=
  contains_sound (CA3_5_8I1R15Raw_sound a) (CA3_5_8I1R15P_check a)
def CA3_5_8I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R15Certificates (CA3_5_8I1R15CertificateIndex a)).output
lemma CA3_5_8I1R15Terms_sound (a : PairSlot) :
    (CA3_5_8I1R15Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I1R15Certificates_valid
    (CA3_5_8I1R15CertificateIndex a) (CA3_5_8I1R15P_sound a)
def CA3_5_8I1R15Entropy : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R15Entropy_sound : CA3_5_8I1R15Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I1R15Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I1R15Value CA3_5_8I1R15Terms CA3_5_8I1R15Terms_sound) (by decide +kernel)
def CA3_5_8I1R15Mass : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R15Mass_sound : CA3_5_8I1R15Mass.Encloses (∑ a, CA3_5_8I1R15Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I1R15P CA3_5_8I1R15Value CA3_5_8I1R15P_sound) (by decide +kernel)
def CA3_5_8I1R15MassTerm : Ball := .exact 0
lemma CA3_5_8I1R15MassTerm_sound : CA3_5_8I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I1R15Value a))) :=
  entropyTerm_zero_ball (CA3_5_8I1R15Mass_sound)
def CA3_5_8I1R15H : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R15H_sound : CA3_5_8I1R15H.Encloses (homogeneousEntropy CA3_5_8I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I1R15Value CA3_5_8I1R15MassTerm_sound CA3_5_8I1R15Entropy_sound) (by decide +kernel)
def CA3_5_8I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA3_5_8I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 3 5 8)) A3_5_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
lemma CA3_5_8I1R16Raw_sound (a : PairSlot) :
    (CA3_5_8I1R16Raw a).Encloses (CA3_5_8I1R16Value a) := by
  exact residualBall_sound_on (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_5_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 5 8) (show (shape 3 5 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 16 a
def CA3_5_8I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_5_8I1R16Certificates_valid :
    CA3_5_8I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_5_8I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R16Certificates (CA3_5_8I1R16CertificateIndex a)).input
lemma CA3_5_8I1R16P_check : ∀ a : PairSlot, contains (CA3_5_8I1R16Raw a) (CA3_5_8I1R16P a) = true := by
  decide +kernel
lemma CA3_5_8I1R16P_sound (a : PairSlot) :
    (CA3_5_8I1R16P a).Encloses (CA3_5_8I1R16Value a) :=
  contains_sound (CA3_5_8I1R16Raw_sound a) (CA3_5_8I1R16P_check a)
def CA3_5_8I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I1R16Certificates (CA3_5_8I1R16CertificateIndex a)).output
lemma CA3_5_8I1R16Terms_sound (a : PairSlot) :
    (CA3_5_8I1R16Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I1R16Certificates_valid
    (CA3_5_8I1R16CertificateIndex a) (CA3_5_8I1R16P_sound a)
def CA3_5_8I1R16Entropy : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R16Entropy_sound : CA3_5_8I1R16Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I1R16Value) := by
  exact contains_sound (entropyPair_enclosed CA3_5_8I1R16Value CA3_5_8I1R16Terms CA3_5_8I1R16Terms_sound) (by decide +kernel)
def CA3_5_8I1R16Mass : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R16Mass_sound : CA3_5_8I1R16Mass.Encloses (∑ a, CA3_5_8I1R16Value a) := by
  exact contains_sound (pairSumBall_sound CA3_5_8I1R16P CA3_5_8I1R16Value CA3_5_8I1R16P_sound) (by decide +kernel)
def CA3_5_8I1R16MassTerm : Ball := .exact 0
lemma CA3_5_8I1R16MassTerm_sound : CA3_5_8I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I1R16Value a))) :=
  entropyTerm_zero_ball (CA3_5_8I1R16Mass_sound)
def CA3_5_8I1R16H : Ball := ⟨0, 0⟩
lemma CA3_5_8I1R16H_sound : CA3_5_8I1R16H.Encloses (homogeneousEntropy CA3_5_8I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I1R16Value CA3_5_8I1R16MassTerm_sound CA3_5_8I1R16Entropy_sound) (by decide +kernel)
def CA3_5_8I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA3_5_8I1R0H
  | 1 => CA3_5_8I1R1H
  | 2 => CA3_5_8I1R2H
  | 3 => CA3_5_8I1R3H
  | 4 => CA3_5_8I1R4H
  | 5 => CA3_5_8I1R5H
  | 6 => CA3_5_8I1R6H
  | 7 => CA3_5_8I1R7H
  | 8 => CA3_5_8I1R8H
  | 9 => CA3_5_8I1R9H
  | 10 => CA3_5_8I1R10H
  | 11 => CA3_5_8I1R11H
  | 12 => CA3_5_8I1R12H
  | 13 => CA3_5_8I1R13H
  | 14 => CA3_5_8I1R14H
  | 15 => CA3_5_8I1R15H
  | 16 => CA3_5_8I1R16H
  | _ => (.exact 0)
lemma CA3_5_8I1ResidualEntropies_sound (k : Fin 17) :
    (CA3_5_8I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CA3_5_8I1R0H_sound
  · exact CA3_5_8I1R1H_sound
  · exact CA3_5_8I1R2H_sound
  · exact CA3_5_8I1R3H_sound
  · exact CA3_5_8I1R4H_sound
  · exact CA3_5_8I1R5H_sound
  · exact CA3_5_8I1R6H_sound
  · exact CA3_5_8I1R7H_sound
  · exact CA3_5_8I1R8H_sound
  · exact CA3_5_8I1R9H_sound
  · exact CA3_5_8I1R10H_sound
  · exact CA3_5_8I1R11H_sound
  · exact CA3_5_8I1R12H_sound
  · exact CA3_5_8I1R13H_sound
  · exact CA3_5_8I1R14H_sound
  · exact CA3_5_8I1R15H_sound
  · exact CA3_5_8I1R16H_sound
def CA3_5_8I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 3, 5, 0 => Z3_5_0H1H
  | _, _, _ => (.exact 0)
lemma CA3_5_8I1Singles_sound (u : Shape) (hu : u ∈ below (shape 3 5 8))
    (hd : designated (Equiv.refl (Fin 3)) 1 u) :
    (CA3_5_8I1Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) u)) := by
  rw [A3_5_8_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 0 8) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 1 7) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 2 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 3 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 4 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 5 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 0 7) by decide +kernel) hd |>.elim
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
def CA3_5_8I1Singleton : Ball := ⟨(1677500010387187021113073 / 25000000000000000000000000000000), (333 / 6250000000000000000000000000000)⟩
lemma CA3_5_8I1Singleton_sound : CA3_5_8I1Singleton.Encloses
    (singletonEntropy (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1
    CA3_5_8I1Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_5_8Law_sound u) CA3_5_8I1Singles_sound) (by decide +kernel)
def CA3_5_8I1Group : Ball := ⟨(102984892185781541805278521000961 / 100000000000000000000000000000000), (3358280671 / 2000000000000000000000000000000)⟩
lemma CA3_5_8I1Group_sound : CA3_5_8I1Group.Encloses
    (groupedEntropy (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA3_5_8I1Singleton_sound
    (finSumBall_sound 17 CA3_5_8I1ResidualEntropies _ CA3_5_8I1ResidualEntropies_sound)) (by decide +kernel)

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
def CA3_5_8I1H : Ball := ⟨(118328426959816533655955229798811 / 100000000000000000000000000000000), (515993841763 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I1_sound : CA3_5_8I1H.Encloses (stageACapacity (shape 3 5 8) 1) := by
  have hb := contains_sound (Ball.add_sound CA3_5_8I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA3_5_8I1Group_sound)))
    (show contains (.add CA3_5_8I1PairH (.neg (.mul (.exact 2) CA3_5_8I1Group))) CA3_5_8I1H = true by decide +kernel)
  unfold CA3_5_8I1PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
