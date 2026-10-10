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
def CA2_3_11I2PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 2 3 11)) (shape 2 3 11) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) a
def CA2_3_11I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 2 3 11) A2_3_11Law 2 a
lemma CA2_3_11I2PairRaw_sound (a : PairSlot × PairSlot) :
    (CA2_3_11I2PairRaw a).Encloses (CA2_3_11I2PairValue a) := by
  exact stageAPairBall_sound (shape 2 3 11) (by decide +kernel) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (fun u _ => A2_3_11Law_sound u) 2 a
def CA2_3_11I2PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(514093738669073721436557579 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1565193747281701732814757813 / 25000000000000000000000000000000), (1034211 / 50000000000000000000000000000000)⟩ ⟨(-48713100496693021950406840784137 / 4000000000000000000000000000000), (402340844493 / 100000000000000000000000000000000)⟩ ⟨-18, 514093738669073721436557579, 381469726562500000000000000⟩,
   .log ⟨(18286587627341528161390875447 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(19673528357962647637477614739 / 12500000000000000000000000000000), (13553177 / 25000000000000000000000000000000)⟩ ⟨(-860675759037619878649668929959173 / 100000000000000000000000000000000), (29646153703 / 10000000000000000000000000000000)⟩ ⟨-13, 18286587627341528161390875447, 12207031250000000000000000000⟩,
   .log ⟨(801928436256759907516886059 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(9409556715347487994516686453 / 100000000000000000000000000000000), (3056683 / 100000000000000000000000000000000)⟩ ⟨(-293341534291681925901083085633429 / 25000000000000000000000000000000), (381164950993 / 100000000000000000000000000000000)⟩ ⟨-17, 801928436256759907516886059, 762939453125000000000000000⟩,
   .log ⟨(583174592254490084617031821 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(7028533397709702574684783017 / 100000000000000000000000000000000), (1173181 / 50000000000000000000000000000000)⟩ ⟨(-602609706515003543796694056210721 / 50000000000000000000000000000000), (100585205363 / 25000000000000000000000000000000)⟩ ⟨-18, 583174592254490084617031821, 381469726562500000000000000⟩,
   .log ⟨(210208269304228855913852244341 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(161987193032213530398570841011 / 12500000000000000000000000000000), (22256667 / 5000000000000000000000000000000)⟩ ⟨(-616482666712882774055266418353337 / 100000000000000000000000000000000), (211758237781 / 100000000000000000000000000000000)⟩ ⟨-9, 210208269304228855913852244341, 195312500000000000000000000000⟩,
   .log ⟨(2207128306853625715322313110039 / 100000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩ ⟨(2104208768452590292534838504217 / 25000000000000000000000000000000), (1635821627 / 50000000000000000000000000000000)⟩ ⟨(-381347792408543300578107696854781 / 100000000000000000000000000000000), (14823076637 / 10000000000000000000000000000000)⟩ ⟨-6, 2207128306853625715322313110039, 1562500000000000000000000000000⟩,
   .log ⟨(20158912145541728246885267581 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(347733224962728327799614132443 / 50000000000000000000000000000000), (29348109 / 12500000000000000000000000000000)⟩ ⟨(-86248013397794321004157859741613 / 12500000000000000000000000000000), (3639594711 / 1562500000000000000000000000000)⟩ ⟨-10, 20158912145541728246885267581, 19531250000000000000000000000⟩,
   .log ⟨(5333535771927365604804710433 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(52476184174698319718491385809 / 100000000000000000000000000000000), (9035367 / 50000000000000000000000000000000)⟩ ⟨(-196778221497650669825846684162267 / 20000000000000000000000000000000), (338813197677 / 100000000000000000000000000000000)⟩ ⟨-15, 5333535771927365604804710433, 3051757812500000000000000000⟩,
   .log ⟨(2365505276181939121558097447 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(362215702997453659949968844667 / 100000000000000000000000000000000), (8139873 / 6250000000000000000000000000000)⟩ ⟨(-765620154485748034068444143008119 / 100000000000000000000000000000000), (34410713749 / 12500000000000000000000000000000)⟩ ⟨-12, 2365505276181939121558097447, 1220703125000000000000000000⟩,
   .log ⟨(1114540445710650223683009813289 / 50000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩ ⟨(132476396459504971492683829363 / 1562500000000000000000000000000), (3304183743 / 100000000000000000000000000000000)⟩ ⟨(-38035808417891407357155342318881 / 10000000000000000000000000000000), (148230766409 / 100000000000000000000000000000000)⟩ ⟨-6, 1114540445710650223683009813289, 781250000000000000000000000000⟩,
   .log ⟨(129089442418154761929961893523 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(429378590960183740702475642391 / 50000000000000000000000000000000), (18793331 / 6250000000000000000000000000000)⟩ ⟨(-665241994878734080717191029185119 / 100000000000000000000000000000000), (116467031031 / 50000000000000000000000000000000)⟩ ⟨-10, 129089442418154761929961893523, 97656250000000000000000000000⟩,
   .log ⟨(1925125746460424888734281561 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(39136986306445901610649586803 / 100000000000000000000000000000000), (3261293 / 25000000000000000000000000000000)⟩ ⟨(-1016478699596739478840195903834799 / 100000000000000000000000000000000), (3388132049 / 1000000000000000000000000000000)⟩ ⟨-15, 1925125746460424888734281561, 1525878906250000000000000000⟩,
   .log ⟨(21669445923142634312457989127 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(68882625340195485264181164237 / 6250000000000000000000000000000), (201902089 / 50000000000000000000000000000000)⟩ ⟨(-635758067691337718102920742650059 / 100000000000000000000000000000000), (116467030833 / 50000000000000000000000000000000)⟩ ⟨-10, 21669445923142634312457989127, 12207031250000000000000000000⟩,
   .log ⟨(10220616200711351030348909013 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(46956160972572173983798290413 / 50000000000000000000000000000000), (16232253 / 50000000000000000000000000000000)⟩ ⟨(-918851858840057860722308760889683 / 100000000000000000000000000000000), (317637365029 / 100000000000000000000000000000000)⟩ ⟨-14, 10220616200711351030348909013, 6103515625000000000000000000⟩,
   .log ⟨(34879650284750079838933009761 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(458648394004557632110496105047 / 50000000000000000000000000000000), (324986359 / 100000000000000000000000000000000)⟩ ⟨(-657472753109978530906569512194251 / 100000000000000000000000000000000), (116467030973 / 50000000000000000000000000000000)⟩ ⟨-10, 34879650284750079838933009761, 24414062500000000000000000000⟩,
   .log ⟨(16101925810295116456395922452093 / 100000000000000000000000000000000), (51 / 100000000000000000000000000000000)⟩ ⟨(29405840995286274778640978020233 / 100000000000000000000000000000000), (6819430911 / 50000000000000000000000000000000)⟩ ⟨(-182623130560476255648401857723113 / 100000000000000000000000000000000), (10587911881 / 12500000000000000000000000000000)⟩ ⟨-3, 16101925810295116456395922452093, 12500000000000000000000000000000⟩,
   .log ⟨(71750537800594427299584243279 / 10000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(141697124207935636689177435147 / 4000000000000000000000000000000), (85464943 / 6250000000000000000000000000000)⟩ ⟨(-246857251094293761474724568107779 / 50000000000000000000000000000000), (23822801713 / 12500000000000000000000000000000)⟩ ⟨-8, 71750537800594427299584243279, 39062500000000000000000000000⟩]
lemma CA2_3_11I2PairCertificates_valid :
    CA2_3_11I2PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I2PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 5, 5, 4, 0 => 1
  | 5, 5, 2, 1 => 2
  | 5, 5, 3, 1 => 3
  | 5, 5, 1, 2 => 2
  | 5, 5, 1, 3 => 3
  | 5, 5, 0, 4 => 1
  | 4, 5, 5, 0 => 4
  | 4, 5, 4, 1 => 5
  | 4, 5, 2, 2 => 6
  | 4, 5, 2, 3 => 7
  | 4, 5, 3, 2 => 7
  | 4, 5, 3, 3 => 8
  | 4, 5, 1, 4 => 5
  | 4, 5, 0, 5 => 4
  | 5, 4, 5, 0 => 4
  | 5, 4, 4, 1 => 5
  | 5, 4, 2, 2 => 6
  | 5, 4, 2, 3 => 7
  | 5, 4, 3, 2 => 7
  | 5, 4, 3, 3 => 8
  | 5, 4, 1, 4 => 5
  | 5, 4, 0, 5 => 4
  | 2, 5, 5, 1 => 9
  | 2, 5, 4, 2 => 10
  | 2, 5, 4, 3 => 11
  | 2, 5, 2, 4 => 10
  | 2, 5, 3, 4 => 11
  | 2, 5, 1, 5 => 9
  | 3, 5, 5, 1 => 12
  | 3, 5, 4, 2 => 13
  | 3, 5, 4, 3 => 14
  | 3, 5, 2, 4 => 13
  | 3, 5, 3, 4 => 14
  | 3, 5, 1, 5 => 12
  | 4, 4, 5, 1 => 15
  | 4, 4, 4, 2 => 16
  | 4, 4, 4, 3 => 17
  | 4, 4, 2, 4 => 16
  | 4, 4, 3, 4 => 17
  | 4, 4, 1, 5 => 15
  | 5, 2, 5, 1 => 9
  | 5, 2, 4, 2 => 10
  | 5, 2, 4, 3 => 11
  | 5, 2, 2, 4 => 10
  | 5, 2, 3, 4 => 11
  | 5, 2, 1, 5 => 9
  | 5, 3, 5, 1 => 12
  | 5, 3, 4, 2 => 13
  | 5, 3, 4, 3 => 14
  | 5, 3, 2, 4 => 13
  | 5, 3, 3, 4 => 14
  | 5, 3, 1, 5 => 12
  | 1, 5, 2, 5 => 9
  | 1, 5, 3, 5 => 12
  | 1, 5, 4, 4 => 15
  | 1, 5, 5, 2 => 9
  | 1, 5, 5, 3 => 12
  | 2, 4, 2, 5 => 10
  | 2, 4, 3, 5 => 13
  | 2, 4, 4, 4 => 16
  | 2, 4, 5, 2 => 10
  | 2, 4, 5, 3 => 13
  | 3, 4, 2, 5 => 11
  | 3, 4, 3, 5 => 14
  | 3, 4, 4, 4 => 17
  | 3, 4, 5, 2 => 11
  | 3, 4, 5, 3 => 14
  | 4, 2, 2, 5 => 10
  | 4, 2, 3, 5 => 13
  | 4, 2, 4, 4 => 16
  | 4, 2, 5, 2 => 10
  | 4, 2, 5, 3 => 13
  | 4, 3, 2, 5 => 11
  | 4, 3, 3, 5 => 14
  | 4, 3, 4, 4 => 17
  | 4, 3, 5, 2 => 11
  | 4, 3, 5, 3 => 14
  | 5, 1, 2, 5 => 9
  | 5, 1, 3, 5 => 12
  | 5, 1, 4, 4 => 15
  | 5, 1, 5, 2 => 9
  | 5, 1, 5, 3 => 12
  | 5, 0, 4, 5 => 4
  | 5, 0, 5, 4 => 4
  | 4, 1, 4, 5 => 5
  | 4, 1, 5, 4 => 5
  | 2, 2, 4, 5 => 6
  | 2, 2, 5, 4 => 6
  | 2, 3, 4, 5 => 7
  | 2, 3, 5, 4 => 7
  | 3, 2, 4, 5 => 7
  | 3, 2, 5, 4 => 7
  | 3, 3, 4, 5 => 8
  | 3, 3, 5, 4 => 8
  | 1, 4, 4, 5 => 5
  | 1, 4, 5, 4 => 5
  | 0, 5, 4, 5 => 4
  | 0, 5, 5, 4 => 4
  | 4, 0, 5, 5 => 1
  | 2, 1, 5, 5 => 2
  | 3, 1, 5, 5 => 3
  | 1, 2, 5, 5 => 2
  | 1, 3, 5, 5 => 3
  | 0, 4, 5, 5 => 1
  | _, _, _, _ => 0
def CA2_3_11I2PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2PairCertificates (CA2_3_11I2PairCertificateIndex a)).input
lemma CA2_3_11I2PairP_check_0_0 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((0,0),(k,l))) (CA2_3_11I2PairP ((0,0),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_0_1 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((0,1),(k,l))) (CA2_3_11I2PairP ((0,1),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_0_2 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((0,2),(k,l))) (CA2_3_11I2PairP ((0,2),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_0_3 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((0,3),(k,l))) (CA2_3_11I2PairP ((0,3),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_0_4 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((0,4),(k,l))) (CA2_3_11I2PairP ((0,4),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_0_5 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((0,5),(k,l))) (CA2_3_11I2PairP ((0,5),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_1_0 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((1,0),(k,l))) (CA2_3_11I2PairP ((1,0),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_1_1 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((1,1),(k,l))) (CA2_3_11I2PairP ((1,1),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_1_2 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((1,2),(k,l))) (CA2_3_11I2PairP ((1,2),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_1_3 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((1,3),(k,l))) (CA2_3_11I2PairP ((1,3),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_1_4 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((1,4),(k,l))) (CA2_3_11I2PairP ((1,4),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_1_5 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((1,5),(k,l))) (CA2_3_11I2PairP ((1,5),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_2_0 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((2,0),(k,l))) (CA2_3_11I2PairP ((2,0),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_2_1 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((2,1),(k,l))) (CA2_3_11I2PairP ((2,1),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_2_2 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((2,2),(k,l))) (CA2_3_11I2PairP ((2,2),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_2_3 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((2,3),(k,l))) (CA2_3_11I2PairP ((2,3),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_2_4 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((2,4),(k,l))) (CA2_3_11I2PairP ((2,4),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_2_5 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((2,5),(k,l))) (CA2_3_11I2PairP ((2,5),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_3_0 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((3,0),(k,l))) (CA2_3_11I2PairP ((3,0),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_3_1 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((3,1),(k,l))) (CA2_3_11I2PairP ((3,1),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_3_2 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((3,2),(k,l))) (CA2_3_11I2PairP ((3,2),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_3_3 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((3,3),(k,l))) (CA2_3_11I2PairP ((3,3),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_3_4 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((3,4),(k,l))) (CA2_3_11I2PairP ((3,4),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_3_5 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((3,5),(k,l))) (CA2_3_11I2PairP ((3,5),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_4_0 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((4,0),(k,l))) (CA2_3_11I2PairP ((4,0),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_4_1 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((4,1),(k,l))) (CA2_3_11I2PairP ((4,1),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_4_2 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((4,2),(k,l))) (CA2_3_11I2PairP ((4,2),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_4_3 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((4,3),(k,l))) (CA2_3_11I2PairP ((4,3),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_4_4 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((4,4),(k,l))) (CA2_3_11I2PairP ((4,4),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_4_5 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((4,5),(k,l))) (CA2_3_11I2PairP ((4,5),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_5_0 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((5,0),(k,l))) (CA2_3_11I2PairP ((5,0),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_5_1 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((5,1),(k,l))) (CA2_3_11I2PairP ((5,1),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_5_2 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((5,2),(k,l))) (CA2_3_11I2PairP ((5,2),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_5_3 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((5,3),(k,l))) (CA2_3_11I2PairP ((5,3),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_5_4 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((5,4),(k,l))) (CA2_3_11I2PairP ((5,4),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check_5_5 : ∀ k l : Fin 6, contains (CA2_3_11I2PairRaw ((5,5),(k,l))) (CA2_3_11I2PairP ((5,5),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I2PairP_check (a : PairSlot × PairSlot) : contains (CA2_3_11I2PairRaw a) (CA2_3_11I2PairP a) = true := by
  rcases a with ⟨⟨i,j⟩,⟨k,l⟩⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (CA2_3_11I2PairP_check_0_0 k l) (CA2_3_11I2PairP_check_0_1 k l) (CA2_3_11I2PairP_check_0_2 k l) (CA2_3_11I2PairP_check_0_3 k l) (CA2_3_11I2PairP_check_0_4 k l) (CA2_3_11I2PairP_check_0_5 k l)
  · exact forall_fin6 (CA2_3_11I2PairP_check_1_0 k l) (CA2_3_11I2PairP_check_1_1 k l) (CA2_3_11I2PairP_check_1_2 k l) (CA2_3_11I2PairP_check_1_3 k l) (CA2_3_11I2PairP_check_1_4 k l) (CA2_3_11I2PairP_check_1_5 k l)
  · exact forall_fin6 (CA2_3_11I2PairP_check_2_0 k l) (CA2_3_11I2PairP_check_2_1 k l) (CA2_3_11I2PairP_check_2_2 k l) (CA2_3_11I2PairP_check_2_3 k l) (CA2_3_11I2PairP_check_2_4 k l) (CA2_3_11I2PairP_check_2_5 k l)
  · exact forall_fin6 (CA2_3_11I2PairP_check_3_0 k l) (CA2_3_11I2PairP_check_3_1 k l) (CA2_3_11I2PairP_check_3_2 k l) (CA2_3_11I2PairP_check_3_3 k l) (CA2_3_11I2PairP_check_3_4 k l) (CA2_3_11I2PairP_check_3_5 k l)
  · exact forall_fin6 (CA2_3_11I2PairP_check_4_0 k l) (CA2_3_11I2PairP_check_4_1 k l) (CA2_3_11I2PairP_check_4_2 k l) (CA2_3_11I2PairP_check_4_3 k l) (CA2_3_11I2PairP_check_4_4 k l) (CA2_3_11I2PairP_check_4_5 k l)
  · exact forall_fin6 (CA2_3_11I2PairP_check_5_0 k l) (CA2_3_11I2PairP_check_5_1 k l) (CA2_3_11I2PairP_check_5_2 k l) (CA2_3_11I2PairP_check_5_3 k l) (CA2_3_11I2PairP_check_5_4 k l) (CA2_3_11I2PairP_check_5_5 k l)
lemma CA2_3_11I2PairP_sound (a : PairSlot × PairSlot) :
    (CA2_3_11I2PairP a).Encloses (CA2_3_11I2PairValue a) :=
  contains_sound (CA2_3_11I2PairRaw_sound a) (CA2_3_11I2PairP_check a)
def CA2_3_11I2PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2PairCertificates (CA2_3_11I2PairCertificateIndex a)).output
lemma CA2_3_11I2PairTerms_sound (a : PairSlot × PairSlot) :
    (CA2_3_11I2PairTerms a).Encloses (Foundation.entropyTerm (CA2_3_11I2PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I2PairCertificates_valid
    (CA2_3_11I2PairCertificateIndex a) (CA2_3_11I2PairP_sound a)
def CA2_3_11I2PairEntropy : Ball := ⟨(34186993952125239895041733853741 / 12500000000000000000000000000000), (3551715743 / 3125000000000000000000000000000)⟩
lemma CA2_3_11I2PairEntropy_sound : CA2_3_11I2PairEntropy.Encloses (Foundation.finiteEntropy CA2_3_11I2PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA2_3_11I2PairValue CA2_3_11I2PairTerms CA2_3_11I2PairTerms_sound) (by decide +kernel)
def CA2_3_11I2PairMass : Ball := ⟨(12500000000000000000000000000001 / 12500000000000000000000000000000), (31 / 6250000000000000000000000000000)⟩
lemma CA2_3_11I2PairMass_sound : CA2_3_11I2PairMass.Encloses (∑ a, CA2_3_11I2PairValue a) := by
  exact contains_sound (doublePairSumBall_sound CA2_3_11I2PairP CA2_3_11I2PairValue CA2_3_11I2PairP_sound) (by decide +kernel)
def CA2_3_11I2PairMassTermLogWitness : LogWitness := ⟨0, 12500000000000000000000000000001, 12500000000000000000000000000000⟩
def CA2_3_11I2PairMassTermLog : Ball := ⟨(1 / 12500000000000000000000000000000), (10587912089 / 50000000000000000000000000000000)⟩
lemma CA2_3_11I2PairMassTermLog_sound : CA2_3_11I2PairMassTermLog.Encloses (Real.log ((∑ a, CA2_3_11I2PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_3_11I2PairMass_sound) (w := CA2_3_11I2PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_3_11I2PairMassTerm : Ball := ⟨(-1 / 12500000000000000000000000000000), (21175824179 / 100000000000000000000000000000000)⟩
lemma CA2_3_11I2PairMassTerm_sound : CA2_3_11I2PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I2PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA2_3_11I2PairMass_sound) CA2_3_11I2PairMassTermLog_sound) (by decide +kernel)
def CA2_3_11I2PairH : Ball := ⟨(17093496976062619947520866926871 / 6250000000000000000000000000000), (26966145591 / 20000000000000000000000000000000)⟩
lemma CA2_3_11I2PairH_sound : CA2_3_11I2PairH.Encloses (homogeneousEntropy CA2_3_11I2PairValue) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I2PairValue CA2_3_11I2PairMassTerm_sound CA2_3_11I2PairEntropy_sound) (by decide +kernel)

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
def CA2_3_11I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA2_3_11I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
lemma CA2_3_11I2R0Raw_sound (a : PairSlot) :
    (CA2_3_11I2R0Raw a).Encloses (CA2_3_11I2R0Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 0 a
def CA2_3_11I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I2R0Certificates_valid :
    CA2_3_11I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R0Certificates (CA2_3_11I2R0CertificateIndex a)).input
lemma CA2_3_11I2R0P_check : ∀ a : PairSlot, contains (CA2_3_11I2R0Raw a) (CA2_3_11I2R0P a) = true := by
  decide +kernel
lemma CA2_3_11I2R0P_sound (a : PairSlot) :
    (CA2_3_11I2R0P a).Encloses (CA2_3_11I2R0Value a) :=
  contains_sound (CA2_3_11I2R0Raw_sound a) (CA2_3_11I2R0P_check a)
def CA2_3_11I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R0Certificates (CA2_3_11I2R0CertificateIndex a)).output
lemma CA2_3_11I2R0Terms_sound (a : PairSlot) :
    (CA2_3_11I2R0Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I2R0Certificates_valid
    (CA2_3_11I2R0CertificateIndex a) (CA2_3_11I2R0P_sound a)
def CA2_3_11I2R0Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R0Entropy_sound : CA2_3_11I2R0Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I2R0Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I2R0Value CA2_3_11I2R0Terms CA2_3_11I2R0Terms_sound) (by decide +kernel)
def CA2_3_11I2R0Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R0Mass_sound : CA2_3_11I2R0Mass.Encloses (∑ a, CA2_3_11I2R0Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I2R0P CA2_3_11I2R0Value CA2_3_11I2R0P_sound) (by decide +kernel)
def CA2_3_11I2R0MassTerm : Ball := .exact 0
lemma CA2_3_11I2R0MassTerm_sound : CA2_3_11I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I2R0Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I2R0Mass_sound)
def CA2_3_11I2R0H : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R0H_sound : CA2_3_11I2R0H.Encloses (homogeneousEntropy CA2_3_11I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I2R0Value CA2_3_11I2R0MassTerm_sound CA2_3_11I2R0Entropy_sound) (by decide +kernel)
def CA2_3_11I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA2_3_11I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
lemma CA2_3_11I2R1Raw_sound (a : PairSlot) :
    (CA2_3_11I2R1Raw a).Encloses (CA2_3_11I2R1Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 1 a
def CA2_3_11I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I2R1Certificates_valid :
    CA2_3_11I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R1Certificates (CA2_3_11I2R1CertificateIndex a)).input
lemma CA2_3_11I2R1P_check : ∀ a : PairSlot, contains (CA2_3_11I2R1Raw a) (CA2_3_11I2R1P a) = true := by
  decide +kernel
lemma CA2_3_11I2R1P_sound (a : PairSlot) :
    (CA2_3_11I2R1P a).Encloses (CA2_3_11I2R1Value a) :=
  contains_sound (CA2_3_11I2R1Raw_sound a) (CA2_3_11I2R1P_check a)
def CA2_3_11I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R1Certificates (CA2_3_11I2R1CertificateIndex a)).output
lemma CA2_3_11I2R1Terms_sound (a : PairSlot) :
    (CA2_3_11I2R1Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I2R1Certificates_valid
    (CA2_3_11I2R1CertificateIndex a) (CA2_3_11I2R1P_sound a)
def CA2_3_11I2R1Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R1Entropy_sound : CA2_3_11I2R1Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I2R1Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I2R1Value CA2_3_11I2R1Terms CA2_3_11I2R1Terms_sound) (by decide +kernel)
def CA2_3_11I2R1Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R1Mass_sound : CA2_3_11I2R1Mass.Encloses (∑ a, CA2_3_11I2R1Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I2R1P CA2_3_11I2R1Value CA2_3_11I2R1P_sound) (by decide +kernel)
def CA2_3_11I2R1MassTerm : Ball := .exact 0
lemma CA2_3_11I2R1MassTerm_sound : CA2_3_11I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I2R1Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I2R1Mass_sound)
def CA2_3_11I2R1H : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R1H_sound : CA2_3_11I2R1H.Encloses (homogeneousEntropy CA2_3_11I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I2R1Value CA2_3_11I2R1MassTerm_sound CA2_3_11I2R1Entropy_sound) (by decide +kernel)
def CA2_3_11I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA2_3_11I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
lemma CA2_3_11I2R2Raw_sound (a : PairSlot) :
    (CA2_3_11I2R2Raw a).Encloses (CA2_3_11I2R2Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 2 a
def CA2_3_11I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I2R2Certificates_valid :
    CA2_3_11I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R2Certificates (CA2_3_11I2R2CertificateIndex a)).input
lemma CA2_3_11I2R2P_check : ∀ a : PairSlot, contains (CA2_3_11I2R2Raw a) (CA2_3_11I2R2P a) = true := by
  decide +kernel
lemma CA2_3_11I2R2P_sound (a : PairSlot) :
    (CA2_3_11I2R2P a).Encloses (CA2_3_11I2R2Value a) :=
  contains_sound (CA2_3_11I2R2Raw_sound a) (CA2_3_11I2R2P_check a)
def CA2_3_11I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R2Certificates (CA2_3_11I2R2CertificateIndex a)).output
lemma CA2_3_11I2R2Terms_sound (a : PairSlot) :
    (CA2_3_11I2R2Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I2R2Certificates_valid
    (CA2_3_11I2R2CertificateIndex a) (CA2_3_11I2R2P_sound a)
def CA2_3_11I2R2Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R2Entropy_sound : CA2_3_11I2R2Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I2R2Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I2R2Value CA2_3_11I2R2Terms CA2_3_11I2R2Terms_sound) (by decide +kernel)
def CA2_3_11I2R2Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R2Mass_sound : CA2_3_11I2R2Mass.Encloses (∑ a, CA2_3_11I2R2Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I2R2P CA2_3_11I2R2Value CA2_3_11I2R2P_sound) (by decide +kernel)
def CA2_3_11I2R2MassTerm : Ball := .exact 0
lemma CA2_3_11I2R2MassTerm_sound : CA2_3_11I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I2R2Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I2R2Mass_sound)
def CA2_3_11I2R2H : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R2H_sound : CA2_3_11I2R2H.Encloses (homogeneousEntropy CA2_3_11I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I2R2Value CA2_3_11I2R2MassTerm_sound CA2_3_11I2R2Entropy_sound) (by decide +kernel)
def CA2_3_11I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA2_3_11I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
lemma CA2_3_11I2R3Raw_sound (a : PairSlot) :
    (CA2_3_11I2R3Raw a).Encloses (CA2_3_11I2R3Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 3 a
def CA2_3_11I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(514093738669073721436557579 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1565193747281701732814757813 / 25000000000000000000000000000000), (1034211 / 50000000000000000000000000000000)⟩ ⟨(-48713100496693021950406840784137 / 4000000000000000000000000000000), (402340844493 / 100000000000000000000000000000000)⟩ ⟨-18, 514093738669073721436557579, 381469726562500000000000000⟩,
   .log ⟨(18286587627341528161390875447 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(19673528357962647637477614739 / 12500000000000000000000000000000), (13553177 / 25000000000000000000000000000000)⟩ ⟨(-860675759037619878649668929959173 / 100000000000000000000000000000000), (29646153703 / 10000000000000000000000000000000)⟩ ⟨-13, 18286587627341528161390875447, 12207031250000000000000000000⟩,
   .log ⟨(801928436256759907516886059 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(9409556715347487994516686453 / 100000000000000000000000000000000), (3056683 / 100000000000000000000000000000000)⟩ ⟨(-293341534291681925901083085633429 / 25000000000000000000000000000000), (381164950993 / 100000000000000000000000000000000)⟩ ⟨-17, 801928436256759907516886059, 762939453125000000000000000⟩]
lemma CA2_3_11I2R3Certificates_valid :
    CA2_3_11I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA2_3_11I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R3Certificates (CA2_3_11I2R3CertificateIndex a)).input
lemma CA2_3_11I2R3P_check : ∀ a : PairSlot, contains (CA2_3_11I2R3Raw a) (CA2_3_11I2R3P a) = true := by
  decide +kernel
lemma CA2_3_11I2R3P_sound (a : PairSlot) :
    (CA2_3_11I2R3P a).Encloses (CA2_3_11I2R3Value a) :=
  contains_sound (CA2_3_11I2R3Raw_sound a) (CA2_3_11I2R3P_check a)
def CA2_3_11I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R3Certificates (CA2_3_11I2R3CertificateIndex a)).output
lemma CA2_3_11I2R3Terms_sound (a : PairSlot) :
    (CA2_3_11I2R3Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I2R3Certificates_valid
    (CA2_3_11I2R3CertificateIndex a) (CA2_3_11I2R3P_sound a)
def CA2_3_11I2R3Entropy : Ball := ⟨(173058558568175476025596635617 / 50000000000000000000000000000000), (59337813 / 50000000000000000000000000000000)⟩
lemma CA2_3_11I2R3Entropy_sound : CA2_3_11I2R3Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I2R3Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I2R3Value CA2_3_11I2R3Terms CA2_3_11I2R3Terms_sound) (by decide +kernel)
def CA2_3_11I2R3Mass : Ball := ⟨(3920521960453472358068863817 / 10000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
lemma CA2_3_11I2R3Mass_sound : CA2_3_11I2R3Mass.Encloses (∑ a, CA2_3_11I2R3Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I2R3P CA2_3_11I2R3Value CA2_3_11I2R3P_sound) (by decide +kernel)
def CA2_3_11I2R3MassTermLogWitness : LogWitness := ⟨-12, 3920521960453472358068863817, 2441406250000000000000000000⟩
def CA2_3_11I2R3MassTermLog : Ball := ⟨(-392205778693050138276878830221161 / 50000000000000000000000000000000), (275285723183 / 100000000000000000000000000000000)⟩
lemma CA2_3_11I2R3MassTermLog_sound : CA2_3_11I2R3MassTermLog.Encloses (Real.log ((∑ a, CA2_3_11I2R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_3_11I2R3Mass_sound) (w := CA2_3_11I2R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_3_11I2R3MassTerm : Ball := ⟨(153765136838285764580771240553 / 50000000000000000000000000000000), (5396321 / 5000000000000000000000000000000)⟩
lemma CA2_3_11I2R3MassTerm_sound : CA2_3_11I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I2R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_3_11I2R3Mass_sound) CA2_3_11I2R3MassTermLog_sound) (by decide +kernel)
def CA2_3_11I2R3H : Ball := ⟨(2411677716236213930603174383 / 6250000000000000000000000000000), (113301023 / 50000000000000000000000000000000)⟩
lemma CA2_3_11I2R3H_sound : CA2_3_11I2R3H.Encloses (homogeneousEntropy CA2_3_11I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I2R3Value CA2_3_11I2R3MassTerm_sound CA2_3_11I2R3Entropy_sound) (by decide +kernel)
def CA2_3_11I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA2_3_11I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
lemma CA2_3_11I2R4Raw_sound (a : PairSlot) :
    (CA2_3_11I2R4Raw a).Encloses (CA2_3_11I2R4Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 4 a
def CA2_3_11I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(583174592254490084617031821 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(529944605865144564215225401 / 4000000000000000000000000000000), (2222863 / 50000000000000000000000000000000)⟩ ⟨(-141988086871751569581458114921389 / 12500000000000000000000000000000), (381164912031 / 100000000000000000000000000000000)⟩ ⟨-17, 583174592254490084617031821, 381469726562500000000000000⟩,
   .log ⟨(210208269304228855913852244341 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(575096137529548157619818239123 / 25000000000000000000000000000000), (801240011 / 100000000000000000000000000000000)⟩ ⟨(-547167948656888243113543225303007 / 100000000000000000000000000000000), (95291207049 / 50000000000000000000000000000000)⟩ ⟨-8, 210208269304228855913852244341, 195312500000000000000000000000⟩,
   .log ⟨(4414256613707251430644626220077 / 100000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩ ⟨(6886970310780724690083525220293 / 50000000000000000000000000000000), (701066411 / 12500000000000000000000000000000)⟩ ⟨(-312033074352548769636384503804473 / 100000000000000000000000000000000), (15881867833 / 12500000000000000000000000000000)⟩ ⟨-5, 4414256613707251430644626220077, 3125000000000000000000000000000⟩,
   .log ⟨(20158912145541728246885267581 / 10000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(125120196868253444314340628143 / 10000000000000000000000000000000), (26680099 / 6250000000000000000000000000000)⟩ ⟨(-310334694563180018545769842441287 / 50000000000000000000000000000000), (211758237821 / 100000000000000000000000000000000)⟩ ⟨-9, 20158912145541728246885267581, 19531250000000000000000000000⟩,
   .log ⟨(5333535771927365604804710433 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(97558517783942509493184525271 / 100000000000000000000000000000000), (6776523 / 20000000000000000000000000000000)⟩ ⟨(-182915277886451763637502045552201 / 20000000000000000000000000000000), (317637364619 / 100000000000000000000000000000000)⟩ ⟨-14, 5333535771927365604804710433, 3051757812500000000000000000⟩]
lemma CA2_3_11I2R4Certificates_valid :
    CA2_3_11I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I2R4CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 0 => 1
  | 4, 1 => 2
  | 2, 2 => 3
  | 2, 3 => 4
  | 3, 2 => 4
  | 3, 3 => 5
  | 1, 4 => 2
  | 0, 5 => 1
  | _, _ => 0
def CA2_3_11I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R4Certificates (CA2_3_11I2R4CertificateIndex a)).input
lemma CA2_3_11I2R4P_check : ∀ a : PairSlot, contains (CA2_3_11I2R4Raw a) (CA2_3_11I2R4P a) = true := by
  decide +kernel
lemma CA2_3_11I2R4P_sound (a : PairSlot) :
    (CA2_3_11I2R4P a).Encloses (CA2_3_11I2R4Value a) :=
  contains_sound (CA2_3_11I2R4Raw_sound a) (CA2_3_11I2R4P_check a)
def CA2_3_11I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R4Certificates (CA2_3_11I2R4CertificateIndex a)).output
lemma CA2_3_11I2R4Terms_sound (a : PairSlot) :
    (CA2_3_11I2R4Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I2R4Certificates_valid
    (CA2_3_11I2R4CertificateIndex a) (CA2_3_11I2R4P_sound a)
def CA2_3_11I2R4Entropy : Ball := ⟨(21001169407240103265116354711751 / 100000000000000000000000000000000), (1621509709 / 20000000000000000000000000000000)⟩
lemma CA2_3_11I2R4Entropy_sound : CA2_3_11I2R4Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I2R4Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I2R4Value CA2_3_11I2R4Terms CA2_3_11I2R4Terms_sound) (by decide +kernel)
def CA2_3_11I2R4Mass : Ball := ⟨(5671267703747874110785818097211 / 100000000000000000000000000000000), (1 / 2500000000000000000000000000000)⟩
lemma CA2_3_11I2R4Mass_sound : CA2_3_11I2R4Mass.Encloses (∑ a, CA2_3_11I2R4Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I2R4P CA2_3_11I2R4Value CA2_3_11I2R4P_sound) (by decide +kernel)
def CA2_3_11I2R4MassTermLogWitness : LogWitness := ⟨-5, 5671267703747874110785818097211, 3125000000000000000000000000000⟩
def CA2_3_11I2R4MassTermLog : Ball := ⟨(-286975751233100269100320826215251 / 100000000000000000000000000000000), (127054942803 / 100000000000000000000000000000000)⟩
lemma CA2_3_11I2R4MassTermLog_sound : CA2_3_11I2R4MassTermLog.Encloses (Real.log ((∑ a, CA2_3_11I2R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_3_11I2R4Mass_sound) (w := CA2_3_11I2R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_3_11I2R4MassTerm : Ball := ⟨(16275163097270657154798053737267 / 100000000000000000000000000000000), (7205626053 / 100000000000000000000000000000000)⟩
lemma CA2_3_11I2R4MassTerm_sound : CA2_3_11I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I2R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_3_11I2R4Mass_sound) CA2_3_11I2R4MassTermLog_sound) (by decide +kernel)
def CA2_3_11I2R4H : Ball := ⟨(1181501577492361527579575243621 / 25000000000000000000000000000000), (7656587299 / 50000000000000000000000000000000)⟩
lemma CA2_3_11I2R4H_sound : CA2_3_11I2R4H.Encloses (homogeneousEntropy CA2_3_11I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I2R4Value CA2_3_11I2R4MassTerm_sound CA2_3_11I2R4Entropy_sound) (by decide +kernel)
def CA2_3_11I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA2_3_11I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
lemma CA2_3_11I2R5Raw_sound (a : PairSlot) :
    (CA2_3_11I2R5Raw a).Encloses (CA2_3_11I2R5Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 5 a
def CA2_3_11I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(29084531585862838898352520637 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(236827167739282218665183368477 / 100000000000000000000000000000000), (2502049 / 3125000000000000000000000000000)⟩ ⟨(-407135949637224257156434397556281 / 50000000000000000000000000000000), (275285711317 / 100000000000000000000000000000000)⟩ ⟨-12, 29084531585862838898352520637, 24414062500000000000000000000⟩,
   .log ⟨(4361944975298317792365761385469 / 25000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩ ⟨(6092617383571510721561243858801 / 20000000000000000000000000000000), (3694711141 / 25000000000000000000000000000000)⟩ ⟨(-174595777172625570177586530892981 / 100000000000000000000000000000000), (84703295001 / 100000000000000000000000000000000)⟩ ⟨-3, 4361944975298317792365761385469, 3125000000000000000000000000000⟩,
   .log ⟨(65301921581185389040050134893 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(3285547928556457068689076563159 / 100000000000000000000000000000000), (622269899 / 50000000000000000000000000000000)⟩ ⟨(-251565945457804119779622751462429 / 50000000000000000000000000000000), (95291206803 / 50000000000000000000000000000000)⟩ ⟨-8, 65301921581185389040050134893, 39062500000000000000000000000⟩]
lemma CA2_3_11I2R5Certificates_valid :
    CA2_3_11I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA2_3_11I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R5Certificates (CA2_3_11I2R5CertificateIndex a)).input
lemma CA2_3_11I2R5P_check : ∀ a : PairSlot, contains (CA2_3_11I2R5Raw a) (CA2_3_11I2R5P a) = true := by
  decide +kernel
lemma CA2_3_11I2R5P_sound (a : PairSlot) :
    (CA2_3_11I2R5P a).Encloses (CA2_3_11I2R5Value a) :=
  contains_sound (CA2_3_11I2R5Raw_sound a) (CA2_3_11I2R5P_check a)
def CA2_3_11I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R5Certificates (CA2_3_11I2R5CertificateIndex a)).output
lemma CA2_3_11I2R5Terms_sound (a : PairSlot) :
    (CA2_3_11I2R5Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I2R5Certificates_valid
    (CA2_3_11I2R5CertificateIndex a) (CA2_3_11I2R5P_sound a)
def CA2_3_11I2R5Entropy : Ball := ⟨(33985462014153292895160479225641 / 50000000000000000000000000000000), (1610344993 / 5000000000000000000000000000000)⟩
lemma CA2_3_11I2R5Entropy_sound : CA2_3_11I2R5Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I2R5Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I2R5Value CA2_3_11I2R5Terms CA2_3_11I2R5Terms_sound) (by decide +kernel)
def CA2_3_11I2R5Mass : Ball := ⟨(18129883648590987898761899411443 / 50000000000000000000000000000000), (51 / 50000000000000000000000000000000)⟩
lemma CA2_3_11I2R5Mass_sound : CA2_3_11I2R5Mass.Encloses (∑ a, CA2_3_11I2R5Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I2R5P CA2_3_11I2R5Value CA2_3_11I2R5P_sound) (by decide +kernel)
def CA2_3_11I2R5MassTermLogWitness : LogWitness := ⟨-2, 18129883648590987898761899411443, 12500000000000000000000000000000⟩
def CA2_3_11I2R5MassTermLog : Ball := ⟨(-101446139829968549672529265203349 / 100000000000000000000000000000000), (6352747133 / 10000000000000000000000000000000)⟩
lemma CA2_3_11I2R5MassTermLog_sound : CA2_3_11I2R5MassTermLog.Encloses (Real.log ((∑ a, CA2_3_11I2R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_3_11I2R5Mass_sound) (w := CA2_3_11I2R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_3_11I2R5MassTerm : Ball := ⟨(36784134234320435001557660496367 / 100000000000000000000000000000000), (11517456689 / 50000000000000000000000000000000)⟩
lemma CA2_3_11I2R5MassTerm_sound : CA2_3_11I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I2R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_3_11I2R5Mass_sound) CA2_3_11I2R5MassTermLog_sound) (by decide +kernel)
def CA2_3_11I2R5H : Ball := ⟨(6237357958797230157752659590983 / 20000000000000000000000000000000), (27620906619 / 50000000000000000000000000000000)⟩
lemma CA2_3_11I2R5H_sound : CA2_3_11I2R5H.Encloses (homogeneousEntropy CA2_3_11I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I2R5Value CA2_3_11I2R5MassTerm_sound CA2_3_11I2R5Entropy_sound) (by decide +kernel)
def CA2_3_11I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA2_3_11I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
lemma CA2_3_11I2R6Raw_sound (a : PairSlot) :
    (CA2_3_11I2R6Raw a).Encloses (CA2_3_11I2R6Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 6 a
def CA2_3_11I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(7886314903952997969370681127 / 4000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(122808074855800518959106477219 / 10000000000000000000000000000000), (8349961 / 2000000000000000000000000000000)⟩ ⟨(-622892067341836639191883308106711 / 100000000000000000000000000000000), (52939559461 / 25000000000000000000000000000000)⟩ ⟨-9, 7886314903952997969370681127, 7812500000000000000000000000⟩,
   .log ⟨(12421728542624157123657613 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(24690100758403456975391283 / 12500000000000000000000000000000), (15787 / 25000000000000000000000000000000)⟩ ⟨(-1590123350300652445519249718726277 / 100000000000000000000000000000000), (508227818801 / 100000000000000000000000000000000)⟩ ⟨-23, 12421728542624157123657613, 11920928955078125000000000⟩,
   .log ⟨(4134728977017907334099806971269 / 20000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩ ⟨(32588083316966892151129048132273 / 100000000000000000000000000000000), (8755629213 / 50000000000000000000000000000000)⟩ ⟨(-39407762271845943239079083940257 / 25000000000000000000000000000000), (84703294857 / 100000000000000000000000000000000)⟩ ⟨-3, 4134728977017907334099806971269, 2500000000000000000000000000000⟩]
lemma CA2_3_11I2R6Certificates_valid :
    CA2_3_11I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA2_3_11I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R6Certificates (CA2_3_11I2R6CertificateIndex a)).input
lemma CA2_3_11I2R6P_check : ∀ a : PairSlot, contains (CA2_3_11I2R6Raw a) (CA2_3_11I2R6P a) = true := by
  decide +kernel
lemma CA2_3_11I2R6P_sound (a : PairSlot) :
    (CA2_3_11I2R6P a).Encloses (CA2_3_11I2R6Value a) :=
  contains_sound (CA2_3_11I2R6Raw_sound a) (CA2_3_11I2R6P_check a)
def CA2_3_11I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R6Certificates (CA2_3_11I2R6CertificateIndex a)).output
lemma CA2_3_11I2R6Terms_sound (a : PairSlot) :
    (CA2_3_11I2R6Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I2R6Certificates_valid
    (CA2_3_11I2R6CertificateIndex a) (CA2_3_11I2R6P_sound a)
def CA2_3_11I2R6Entropy : Ball := ⟨(35044639855695036985622783937181 / 100000000000000000000000000000000), (9173190411 / 50000000000000000000000000000000)⟩
lemma CA2_3_11I2R6Entropy_sound : CA2_3_11I2R6Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I2R6Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I2R6Value CA2_3_11I2R6Terms CA2_3_11I2R6Terms_sound) (by decide +kernel)
def CA2_3_11I2R6Mass : Ball := ⟨(21067985473744271817281816227921 / 100000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
lemma CA2_3_11I2R6Mass_sound : CA2_3_11I2R6Mass.Encloses (∑ a, CA2_3_11I2R6Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I2R6P CA2_3_11I2R6Value CA2_3_11I2R6P_sound) (by decide +kernel)
def CA2_3_11I2R6MassTermLogWitness : LogWitness := ⟨-3, 21067985473744271817281816227921, 12500000000000000000000000000000⟩
def CA2_3_11I2R6MassTermLog : Ball := ⟨(-7787077869305013827687891615047 / 5000000000000000000000000000000), (84703294883 / 100000000000000000000000000000000)⟩
lemma CA2_3_11I2R6MassTermLog_sound : CA2_3_11I2R6MassTermLog.Encloses (Real.log ((∑ a, CA2_3_11I2R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_3_11I2R6Mass_sound) (w := CA2_3_11I2R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_3_11I2R6MassTerm : Ball := ⟨(32811608686686705304979056360841 / 100000000000000000000000000000000), (2230659739 / 12500000000000000000000000000000)⟩
lemma CA2_3_11I2R6MassTerm_sound : CA2_3_11I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I2R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_3_11I2R6Mass_sound) CA2_3_11I2R6MassTermLog_sound) (by decide +kernel)
def CA2_3_11I2R6H : Ball := ⟨(111651558450416584032186378817 / 5000000000000000000000000000000), (18095829367 / 50000000000000000000000000000000)⟩
lemma CA2_3_11I2R6H_sound : CA2_3_11I2R6H.Encloses (homogeneousEntropy CA2_3_11I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I2R6Value CA2_3_11I2R6MassTerm_sound CA2_3_11I2R6Entropy_sound) (by decide +kernel)
def CA2_3_11I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA2_3_11I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
lemma CA2_3_11I2R7Raw_sound (a : PairSlot) :
    (CA2_3_11I2R7Raw a).Encloses (CA2_3_11I2R7Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 7 a
def CA2_3_11I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I2R7Certificates_valid :
    CA2_3_11I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R7Certificates (CA2_3_11I2R7CertificateIndex a)).input
lemma CA2_3_11I2R7P_check : ∀ a : PairSlot, contains (CA2_3_11I2R7Raw a) (CA2_3_11I2R7P a) = true := by
  decide +kernel
lemma CA2_3_11I2R7P_sound (a : PairSlot) :
    (CA2_3_11I2R7P a).Encloses (CA2_3_11I2R7Value a) :=
  contains_sound (CA2_3_11I2R7Raw_sound a) (CA2_3_11I2R7P_check a)
def CA2_3_11I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R7Certificates (CA2_3_11I2R7CertificateIndex a)).output
lemma CA2_3_11I2R7Terms_sound (a : PairSlot) :
    (CA2_3_11I2R7Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I2R7Certificates_valid
    (CA2_3_11I2R7CertificateIndex a) (CA2_3_11I2R7P_sound a)
def CA2_3_11I2R7Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R7Entropy_sound : CA2_3_11I2R7Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I2R7Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I2R7Value CA2_3_11I2R7Terms CA2_3_11I2R7Terms_sound) (by decide +kernel)
def CA2_3_11I2R7Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R7Mass_sound : CA2_3_11I2R7Mass.Encloses (∑ a, CA2_3_11I2R7Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I2R7P CA2_3_11I2R7Value CA2_3_11I2R7P_sound) (by decide +kernel)
def CA2_3_11I2R7MassTerm : Ball := .exact 0
lemma CA2_3_11I2R7MassTerm_sound : CA2_3_11I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I2R7Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I2R7Mass_sound)
def CA2_3_11I2R7H : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R7H_sound : CA2_3_11I2R7H.Encloses (homogeneousEntropy CA2_3_11I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I2R7Value CA2_3_11I2R7MassTerm_sound CA2_3_11I2R7Entropy_sound) (by decide +kernel)
def CA2_3_11I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA2_3_11I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
lemma CA2_3_11I2R8Raw_sound (a : PairSlot) :
    (CA2_3_11I2R8Raw a).Encloses (CA2_3_11I2R8Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 8 a
def CA2_3_11I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I2R8Certificates_valid :
    CA2_3_11I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R8Certificates (CA2_3_11I2R8CertificateIndex a)).input
lemma CA2_3_11I2R8P_check : ∀ a : PairSlot, contains (CA2_3_11I2R8Raw a) (CA2_3_11I2R8P a) = true := by
  decide +kernel
lemma CA2_3_11I2R8P_sound (a : PairSlot) :
    (CA2_3_11I2R8P a).Encloses (CA2_3_11I2R8Value a) :=
  contains_sound (CA2_3_11I2R8Raw_sound a) (CA2_3_11I2R8P_check a)
def CA2_3_11I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R8Certificates (CA2_3_11I2R8CertificateIndex a)).output
lemma CA2_3_11I2R8Terms_sound (a : PairSlot) :
    (CA2_3_11I2R8Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I2R8Certificates_valid
    (CA2_3_11I2R8CertificateIndex a) (CA2_3_11I2R8P_sound a)
def CA2_3_11I2R8Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R8Entropy_sound : CA2_3_11I2R8Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I2R8Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I2R8Value CA2_3_11I2R8Terms CA2_3_11I2R8Terms_sound) (by decide +kernel)
def CA2_3_11I2R8Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R8Mass_sound : CA2_3_11I2R8Mass.Encloses (∑ a, CA2_3_11I2R8Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I2R8P CA2_3_11I2R8Value CA2_3_11I2R8P_sound) (by decide +kernel)
def CA2_3_11I2R8MassTerm : Ball := .exact 0
lemma CA2_3_11I2R8MassTerm_sound : CA2_3_11I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I2R8Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I2R8Mass_sound)
def CA2_3_11I2R8H : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R8H_sound : CA2_3_11I2R8H.Encloses (homogeneousEntropy CA2_3_11I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I2R8Value CA2_3_11I2R8MassTerm_sound CA2_3_11I2R8Entropy_sound) (by decide +kernel)
def CA2_3_11I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA2_3_11I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
lemma CA2_3_11I2R9Raw_sound (a : PairSlot) :
    (CA2_3_11I2R9Raw a).Encloses (CA2_3_11I2R9Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 9 a
def CA2_3_11I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I2R9Certificates_valid :
    CA2_3_11I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R9Certificates (CA2_3_11I2R9CertificateIndex a)).input
lemma CA2_3_11I2R9P_check : ∀ a : PairSlot, contains (CA2_3_11I2R9Raw a) (CA2_3_11I2R9P a) = true := by
  decide +kernel
lemma CA2_3_11I2R9P_sound (a : PairSlot) :
    (CA2_3_11I2R9P a).Encloses (CA2_3_11I2R9Value a) :=
  contains_sound (CA2_3_11I2R9Raw_sound a) (CA2_3_11I2R9P_check a)
def CA2_3_11I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R9Certificates (CA2_3_11I2R9CertificateIndex a)).output
lemma CA2_3_11I2R9Terms_sound (a : PairSlot) :
    (CA2_3_11I2R9Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I2R9Certificates_valid
    (CA2_3_11I2R9CertificateIndex a) (CA2_3_11I2R9P_sound a)
def CA2_3_11I2R9Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R9Entropy_sound : CA2_3_11I2R9Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I2R9Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I2R9Value CA2_3_11I2R9Terms CA2_3_11I2R9Terms_sound) (by decide +kernel)
def CA2_3_11I2R9Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R9Mass_sound : CA2_3_11I2R9Mass.Encloses (∑ a, CA2_3_11I2R9Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I2R9P CA2_3_11I2R9Value CA2_3_11I2R9P_sound) (by decide +kernel)
def CA2_3_11I2R9MassTerm : Ball := .exact 0
lemma CA2_3_11I2R9MassTerm_sound : CA2_3_11I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I2R9Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I2R9Mass_sound)
def CA2_3_11I2R9H : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R9H_sound : CA2_3_11I2R9H.Encloses (homogeneousEntropy CA2_3_11I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I2R9Value CA2_3_11I2R9MassTerm_sound CA2_3_11I2R9Entropy_sound) (by decide +kernel)
def CA2_3_11I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA2_3_11I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
lemma CA2_3_11I2R10Raw_sound (a : PairSlot) :
    (CA2_3_11I2R10Raw a).Encloses (CA2_3_11I2R10Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 10 a
def CA2_3_11I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I2R10Certificates_valid :
    CA2_3_11I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R10Certificates (CA2_3_11I2R10CertificateIndex a)).input
lemma CA2_3_11I2R10P_check : ∀ a : PairSlot, contains (CA2_3_11I2R10Raw a) (CA2_3_11I2R10P a) = true := by
  decide +kernel
lemma CA2_3_11I2R10P_sound (a : PairSlot) :
    (CA2_3_11I2R10P a).Encloses (CA2_3_11I2R10Value a) :=
  contains_sound (CA2_3_11I2R10Raw_sound a) (CA2_3_11I2R10P_check a)
def CA2_3_11I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R10Certificates (CA2_3_11I2R10CertificateIndex a)).output
lemma CA2_3_11I2R10Terms_sound (a : PairSlot) :
    (CA2_3_11I2R10Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I2R10Certificates_valid
    (CA2_3_11I2R10CertificateIndex a) (CA2_3_11I2R10P_sound a)
def CA2_3_11I2R10Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R10Entropy_sound : CA2_3_11I2R10Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I2R10Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I2R10Value CA2_3_11I2R10Terms CA2_3_11I2R10Terms_sound) (by decide +kernel)
def CA2_3_11I2R10Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R10Mass_sound : CA2_3_11I2R10Mass.Encloses (∑ a, CA2_3_11I2R10Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I2R10P CA2_3_11I2R10Value CA2_3_11I2R10P_sound) (by decide +kernel)
def CA2_3_11I2R10MassTerm : Ball := .exact 0
lemma CA2_3_11I2R10MassTerm_sound : CA2_3_11I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I2R10Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I2R10Mass_sound)
def CA2_3_11I2R10H : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R10H_sound : CA2_3_11I2R10H.Encloses (homogeneousEntropy CA2_3_11I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I2R10Value CA2_3_11I2R10MassTerm_sound CA2_3_11I2R10Entropy_sound) (by decide +kernel)
def CA2_3_11I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA2_3_11I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
lemma CA2_3_11I2R11Raw_sound (a : PairSlot) :
    (CA2_3_11I2R11Raw a).Encloses (CA2_3_11I2R11Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 11 a
def CA2_3_11I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I2R11Certificates_valid :
    CA2_3_11I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R11Certificates (CA2_3_11I2R11CertificateIndex a)).input
lemma CA2_3_11I2R11P_check : ∀ a : PairSlot, contains (CA2_3_11I2R11Raw a) (CA2_3_11I2R11P a) = true := by
  decide +kernel
lemma CA2_3_11I2R11P_sound (a : PairSlot) :
    (CA2_3_11I2R11P a).Encloses (CA2_3_11I2R11Value a) :=
  contains_sound (CA2_3_11I2R11Raw_sound a) (CA2_3_11I2R11P_check a)
def CA2_3_11I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R11Certificates (CA2_3_11I2R11CertificateIndex a)).output
lemma CA2_3_11I2R11Terms_sound (a : PairSlot) :
    (CA2_3_11I2R11Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I2R11Certificates_valid
    (CA2_3_11I2R11CertificateIndex a) (CA2_3_11I2R11P_sound a)
def CA2_3_11I2R11Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R11Entropy_sound : CA2_3_11I2R11Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I2R11Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I2R11Value CA2_3_11I2R11Terms CA2_3_11I2R11Terms_sound) (by decide +kernel)
def CA2_3_11I2R11Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R11Mass_sound : CA2_3_11I2R11Mass.Encloses (∑ a, CA2_3_11I2R11Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I2R11P CA2_3_11I2R11Value CA2_3_11I2R11P_sound) (by decide +kernel)
def CA2_3_11I2R11MassTerm : Ball := .exact 0
lemma CA2_3_11I2R11MassTerm_sound : CA2_3_11I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I2R11Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I2R11Mass_sound)
def CA2_3_11I2R11H : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R11H_sound : CA2_3_11I2R11H.Encloses (homogeneousEntropy CA2_3_11I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I2R11Value CA2_3_11I2R11MassTerm_sound CA2_3_11I2R11Entropy_sound) (by decide +kernel)
def CA2_3_11I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA2_3_11I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
lemma CA2_3_11I2R12Raw_sound (a : PairSlot) :
    (CA2_3_11I2R12Raw a).Encloses (CA2_3_11I2R12Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 12 a
def CA2_3_11I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I2R12Certificates_valid :
    CA2_3_11I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R12Certificates (CA2_3_11I2R12CertificateIndex a)).input
lemma CA2_3_11I2R12P_check : ∀ a : PairSlot, contains (CA2_3_11I2R12Raw a) (CA2_3_11I2R12P a) = true := by
  decide +kernel
lemma CA2_3_11I2R12P_sound (a : PairSlot) :
    (CA2_3_11I2R12P a).Encloses (CA2_3_11I2R12Value a) :=
  contains_sound (CA2_3_11I2R12Raw_sound a) (CA2_3_11I2R12P_check a)
def CA2_3_11I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R12Certificates (CA2_3_11I2R12CertificateIndex a)).output
lemma CA2_3_11I2R12Terms_sound (a : PairSlot) :
    (CA2_3_11I2R12Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I2R12Certificates_valid
    (CA2_3_11I2R12CertificateIndex a) (CA2_3_11I2R12P_sound a)
def CA2_3_11I2R12Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R12Entropy_sound : CA2_3_11I2R12Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I2R12Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I2R12Value CA2_3_11I2R12Terms CA2_3_11I2R12Terms_sound) (by decide +kernel)
def CA2_3_11I2R12Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R12Mass_sound : CA2_3_11I2R12Mass.Encloses (∑ a, CA2_3_11I2R12Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I2R12P CA2_3_11I2R12Value CA2_3_11I2R12P_sound) (by decide +kernel)
def CA2_3_11I2R12MassTerm : Ball := .exact 0
lemma CA2_3_11I2R12MassTerm_sound : CA2_3_11I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I2R12Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I2R12Mass_sound)
def CA2_3_11I2R12H : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R12H_sound : CA2_3_11I2R12H.Encloses (homogeneousEntropy CA2_3_11I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I2R12Value CA2_3_11I2R12MassTerm_sound CA2_3_11I2R12Entropy_sound) (by decide +kernel)
def CA2_3_11I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA2_3_11I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
lemma CA2_3_11I2R13Raw_sound (a : PairSlot) :
    (CA2_3_11I2R13Raw a).Encloses (CA2_3_11I2R13Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 13 a
def CA2_3_11I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I2R13Certificates_valid :
    CA2_3_11I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R13Certificates (CA2_3_11I2R13CertificateIndex a)).input
lemma CA2_3_11I2R13P_check : ∀ a : PairSlot, contains (CA2_3_11I2R13Raw a) (CA2_3_11I2R13P a) = true := by
  decide +kernel
lemma CA2_3_11I2R13P_sound (a : PairSlot) :
    (CA2_3_11I2R13P a).Encloses (CA2_3_11I2R13Value a) :=
  contains_sound (CA2_3_11I2R13Raw_sound a) (CA2_3_11I2R13P_check a)
def CA2_3_11I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R13Certificates (CA2_3_11I2R13CertificateIndex a)).output
lemma CA2_3_11I2R13Terms_sound (a : PairSlot) :
    (CA2_3_11I2R13Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I2R13Certificates_valid
    (CA2_3_11I2R13CertificateIndex a) (CA2_3_11I2R13P_sound a)
def CA2_3_11I2R13Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R13Entropy_sound : CA2_3_11I2R13Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I2R13Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I2R13Value CA2_3_11I2R13Terms CA2_3_11I2R13Terms_sound) (by decide +kernel)
def CA2_3_11I2R13Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R13Mass_sound : CA2_3_11I2R13Mass.Encloses (∑ a, CA2_3_11I2R13Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I2R13P CA2_3_11I2R13Value CA2_3_11I2R13P_sound) (by decide +kernel)
def CA2_3_11I2R13MassTerm : Ball := .exact 0
lemma CA2_3_11I2R13MassTerm_sound : CA2_3_11I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I2R13Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I2R13Mass_sound)
def CA2_3_11I2R13H : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R13H_sound : CA2_3_11I2R13H.Encloses (homogeneousEntropy CA2_3_11I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I2R13Value CA2_3_11I2R13MassTerm_sound CA2_3_11I2R13Entropy_sound) (by decide +kernel)
def CA2_3_11I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA2_3_11I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
lemma CA2_3_11I2R14Raw_sound (a : PairSlot) :
    (CA2_3_11I2R14Raw a).Encloses (CA2_3_11I2R14Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 14 a
def CA2_3_11I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I2R14Certificates_valid :
    CA2_3_11I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R14Certificates (CA2_3_11I2R14CertificateIndex a)).input
lemma CA2_3_11I2R14P_check : ∀ a : PairSlot, contains (CA2_3_11I2R14Raw a) (CA2_3_11I2R14P a) = true := by
  decide +kernel
lemma CA2_3_11I2R14P_sound (a : PairSlot) :
    (CA2_3_11I2R14P a).Encloses (CA2_3_11I2R14Value a) :=
  contains_sound (CA2_3_11I2R14Raw_sound a) (CA2_3_11I2R14P_check a)
def CA2_3_11I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R14Certificates (CA2_3_11I2R14CertificateIndex a)).output
lemma CA2_3_11I2R14Terms_sound (a : PairSlot) :
    (CA2_3_11I2R14Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I2R14Certificates_valid
    (CA2_3_11I2R14CertificateIndex a) (CA2_3_11I2R14P_sound a)
def CA2_3_11I2R14Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R14Entropy_sound : CA2_3_11I2R14Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I2R14Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I2R14Value CA2_3_11I2R14Terms CA2_3_11I2R14Terms_sound) (by decide +kernel)
def CA2_3_11I2R14Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R14Mass_sound : CA2_3_11I2R14Mass.Encloses (∑ a, CA2_3_11I2R14Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I2R14P CA2_3_11I2R14Value CA2_3_11I2R14P_sound) (by decide +kernel)
def CA2_3_11I2R14MassTerm : Ball := .exact 0
lemma CA2_3_11I2R14MassTerm_sound : CA2_3_11I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I2R14Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I2R14Mass_sound)
def CA2_3_11I2R14H : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R14H_sound : CA2_3_11I2R14H.Encloses (homogeneousEntropy CA2_3_11I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I2R14Value CA2_3_11I2R14MassTerm_sound CA2_3_11I2R14Entropy_sound) (by decide +kernel)
def CA2_3_11I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA2_3_11I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
lemma CA2_3_11I2R15Raw_sound (a : PairSlot) :
    (CA2_3_11I2R15Raw a).Encloses (CA2_3_11I2R15Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 15 a
def CA2_3_11I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I2R15Certificates_valid :
    CA2_3_11I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R15Certificates (CA2_3_11I2R15CertificateIndex a)).input
lemma CA2_3_11I2R15P_check : ∀ a : PairSlot, contains (CA2_3_11I2R15Raw a) (CA2_3_11I2R15P a) = true := by
  decide +kernel
lemma CA2_3_11I2R15P_sound (a : PairSlot) :
    (CA2_3_11I2R15P a).Encloses (CA2_3_11I2R15Value a) :=
  contains_sound (CA2_3_11I2R15Raw_sound a) (CA2_3_11I2R15P_check a)
def CA2_3_11I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R15Certificates (CA2_3_11I2R15CertificateIndex a)).output
lemma CA2_3_11I2R15Terms_sound (a : PairSlot) :
    (CA2_3_11I2R15Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I2R15Certificates_valid
    (CA2_3_11I2R15CertificateIndex a) (CA2_3_11I2R15P_sound a)
def CA2_3_11I2R15Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R15Entropy_sound : CA2_3_11I2R15Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I2R15Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I2R15Value CA2_3_11I2R15Terms CA2_3_11I2R15Terms_sound) (by decide +kernel)
def CA2_3_11I2R15Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R15Mass_sound : CA2_3_11I2R15Mass.Encloses (∑ a, CA2_3_11I2R15Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I2R15P CA2_3_11I2R15Value CA2_3_11I2R15P_sound) (by decide +kernel)
def CA2_3_11I2R15MassTerm : Ball := .exact 0
lemma CA2_3_11I2R15MassTerm_sound : CA2_3_11I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I2R15Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I2R15Mass_sound)
def CA2_3_11I2R15H : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R15H_sound : CA2_3_11I2R15H.Encloses (homogeneousEntropy CA2_3_11I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I2R15Value CA2_3_11I2R15MassTerm_sound CA2_3_11I2R15Entropy_sound) (by decide +kernel)
def CA2_3_11I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA2_3_11I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 2 3 11)) A2_3_11Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
lemma CA2_3_11I2R16Raw_sound (a : PairSlot) :
    (CA2_3_11I2R16Raw a).Encloses (CA2_3_11I2R16Value a) := by
  exact residualBall_sound_on (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_3_11Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 3 11) (show (shape 2 3 11) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 16 a
def CA2_3_11I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_3_11I2R16Certificates_valid :
    CA2_3_11I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_3_11I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R16Certificates (CA2_3_11I2R16CertificateIndex a)).input
lemma CA2_3_11I2R16P_check : ∀ a : PairSlot, contains (CA2_3_11I2R16Raw a) (CA2_3_11I2R16P a) = true := by
  decide +kernel
lemma CA2_3_11I2R16P_sound (a : PairSlot) :
    (CA2_3_11I2R16P a).Encloses (CA2_3_11I2R16Value a) :=
  contains_sound (CA2_3_11I2R16Raw_sound a) (CA2_3_11I2R16P_check a)
def CA2_3_11I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I2R16Certificates (CA2_3_11I2R16CertificateIndex a)).output
lemma CA2_3_11I2R16Terms_sound (a : PairSlot) :
    (CA2_3_11I2R16Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I2R16Certificates_valid
    (CA2_3_11I2R16CertificateIndex a) (CA2_3_11I2R16P_sound a)
def CA2_3_11I2R16Entropy : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R16Entropy_sound : CA2_3_11I2R16Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I2R16Value) := by
  exact contains_sound (entropyPair_enclosed CA2_3_11I2R16Value CA2_3_11I2R16Terms CA2_3_11I2R16Terms_sound) (by decide +kernel)
def CA2_3_11I2R16Mass : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R16Mass_sound : CA2_3_11I2R16Mass.Encloses (∑ a, CA2_3_11I2R16Value a) := by
  exact contains_sound (pairSumBall_sound CA2_3_11I2R16P CA2_3_11I2R16Value CA2_3_11I2R16P_sound) (by decide +kernel)
def CA2_3_11I2R16MassTerm : Ball := .exact 0
lemma CA2_3_11I2R16MassTerm_sound : CA2_3_11I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I2R16Value a))) :=
  entropyTerm_zero_ball (CA2_3_11I2R16Mass_sound)
def CA2_3_11I2R16H : Ball := ⟨0, 0⟩
lemma CA2_3_11I2R16H_sound : CA2_3_11I2R16H.Encloses (homogeneousEntropy CA2_3_11I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I2R16Value CA2_3_11I2R16MassTerm_sound CA2_3_11I2R16Entropy_sound) (by decide +kernel)
def CA2_3_11I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA2_3_11I2R0H
  | 1 => CA2_3_11I2R1H
  | 2 => CA2_3_11I2R2H
  | 3 => CA2_3_11I2R3H
  | 4 => CA2_3_11I2R4H
  | 5 => CA2_3_11I2R5H
  | 6 => CA2_3_11I2R6H
  | 7 => CA2_3_11I2R7H
  | 8 => CA2_3_11I2R8H
  | 9 => CA2_3_11I2R9H
  | 10 => CA2_3_11I2R10H
  | 11 => CA2_3_11I2R11H
  | 12 => CA2_3_11I2R12H
  | 13 => CA2_3_11I2R13H
  | 14 => CA2_3_11I2R14H
  | 15 => CA2_3_11I2R15H
  | 16 => CA2_3_11I2R16H
  | _ => (.exact 0)
lemma CA2_3_11I2ResidualEntropies_sound (k : Fin 17) :
    (CA2_3_11I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CA2_3_11I2R0H_sound
  · exact CA2_3_11I2R1H_sound
  · exact CA2_3_11I2R2H_sound
  · exact CA2_3_11I2R3H_sound
  · exact CA2_3_11I2R4H_sound
  · exact CA2_3_11I2R5H_sound
  · exact CA2_3_11I2R6H_sound
  · exact CA2_3_11I2R7H_sound
  · exact CA2_3_11I2R8H_sound
  · exact CA2_3_11I2R9H_sound
  · exact CA2_3_11I2R10H_sound
  · exact CA2_3_11I2R11H_sound
  · exact CA2_3_11I2R12H_sound
  · exact CA2_3_11I2R13H_sound
  · exact CA2_3_11I2R14H_sound
  · exact CA2_3_11I2R15H_sound
  · exact CA2_3_11I2R16H_sound
def CA2_3_11I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8H2H
  | 0, 1, 7 => Z0_1_7H2H
  | 0, 2, 6 => Z0_2_6H2H
  | 0, 3, 5 => Z0_3_5H2H
  | 1, 0, 7 => Z1_0_7H2H
  | 2, 0, 6 => Z2_0_6H2H
  | _, _, _ => (.exact 0)
lemma CA2_3_11I2Singles_sound (u : Shape) (hu : u ∈ below (shape 2 3 11))
    (hd : designated (Equiv.refl (Fin 3)) 2 u) :
    (CA2_3_11I2Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) u)) := by
  rw [A2_3_11_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0_0_8H2H_sound
  · exact Z0_1_7H2H_sound
  · exact Z0_2_6H2H_sound
  · exact Z0_3_5H2H_sound
  · exact Z1_0_7H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 2 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 3 4) by decide +kernel) hd |>.elim
  · exact Z2_0_6H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 1 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 2 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 3 3) by decide +kernel) hd |>.elim
def CA2_3_11I2Singleton : Ball := ⟨(38894992084717347555582283408189 / 100000000000000000000000000000000), (16335271253 / 50000000000000000000000000000000)⟩
lemma CA2_3_11I2Singleton_sound : CA2_3_11I2Singleton.Encloses
    (singletonEntropy (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2
    CA2_3_11I2Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_3_11Law_sound u) CA2_3_11I2Singles_sound) (by decide +kernel)
def CA2_3_11I2Group : Ball := ⟨(9634925775142631944774657588007 / 12500000000000000000000000000000), (69821895561 / 50000000000000000000000000000000)⟩
lemma CA2_3_11I2Group_sound : CA2_3_11I2Group.Encloses
    (groupedEntropy (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA2_3_11I2Singleton_sound
    (finSumBall_sound 17 CA2_3_11I2ResidualEntropies _ CA2_3_11I2ResidualEntropies_sound)) (by decide +kernel)

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
def CA2_3_11I2H : Ball := ⟨(466160700057499250171638083679 / 390625000000000000000000000000), (414118310199 / 100000000000000000000000000000000)⟩
lemma CA2_3_11I2_sound : CA2_3_11I2H.Encloses (stageACapacity (shape 2 3 11) 2) := by
  have hb := contains_sound (Ball.add_sound CA2_3_11I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA2_3_11I2Group_sound)))
    (show contains (.add CA2_3_11I2PairH (.neg (.mul (.exact 2) CA2_3_11I2Group))) CA2_3_11I2H = true by decide +kernel)
  simp only [stageACapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false]
  change CA2_3_11I2H.Encloses (homogeneousEntropy CA2_3_11I2PairValue - _)
  simpa only [sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
