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
def CA1_5_10I1PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 1 5 10)) (shape 1 5 10) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) a
def CA1_5_10I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 1 5 10) A1_5_10Law 1 a
lemma CA1_5_10I1PairRaw_sound (a : PairSlot × PairSlot) :
    (CA1_5_10I1PairRaw a).Encloses (CA1_5_10I1PairValue a) := by
  exact stageAPairBall_sound (shape 1 5 10) (by decide +kernel) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (fun u _ => A1_5_10Law_sound u) 1 a
def CA1_5_10I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(22268884945206414182146674039 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(47323448329967572271861989909 / 6250000000000000000000000000000), (129679553 / 50000000000000000000000000000000)⟩ ⟨(-170007428558399866366735946547719 / 25000000000000000000000000000000), (232934062309 / 100000000000000000000000000000000)⟩ ⟨-10, 22268884945206414182146674039, 19531250000000000000000000000⟩,
   .log ⟨(5073240300123497419871639527 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(93304991677621678275312218259 / 100000000000000000000000000000000), (1007157 / 3125000000000000000000000000000)⟩ ⟨(-91957985585021828636861036394861 / 10000000000000000000000000000000), (3176373651 / 1000000000000000000000000000000)⟩ ⟨-14, 5073240300123497419871639527, 3051757812500000000000000000⟩,
   .log ⟨(5438635077537771407403874419 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(53404118816045124414143044197 / 100000000000000000000000000000000), (2303353 / 12500000000000000000000000000000)⟩ ⟨(-122742466755608112311191459318267 / 12500000000000000000000000000000), (67762639463 / 20000000000000000000000000000000)⟩ ⟨-15, 5438635077537771407403874419, 3051757812500000000000000000⟩,
   .log ⟨(503707182470066923959310737177 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1332539810352274052911456223889 / 50000000000000000000000000000000), (959977323 / 100000000000000000000000000000000)⟩ ⟨(-21163721411599461767867524868173 / 4000000000000000000000000000000), (95291206871 / 50000000000000000000000000000000)⟩ ⟨-8, 503707182470066923959310737177, 390625000000000000000000000000⟩,
   .log ⟨(255193173092274822371952880777 / 10000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩ ⟨(9361301115128316629100104983021 / 100000000000000000000000000000000), (3782748013 / 100000000000000000000000000000000)⟩ ⟨(-73366391441383749399422062155569 / 20000000000000000000000000000000), (148230766329 / 100000000000000000000000000000000)⟩ ⟨-6, 255193173092274822371952880777, 156250000000000000000000000000⟩,
   .log ⟨(125699728194725478810433817933 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(60193902562488651779210685601 / 4000000000000000000000000000000), (532359071 / 100000000000000000000000000000000)⟩ ⟨(-74823529139369373198258005927601 / 12500000000000000000000000000000), (1694065901 / 800000000000000000000000000000)⟩ ⟨-9, 125699728194725478810433817933, 97656250000000000000000000000⟩,
   .log ⟨(12924529061909621010619436253 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(106765027808725347330636653301 / 50000000000000000000000000000000), (71158773 / 100000000000000000000000000000000)⟩ ⟨(-413032565044774768934775549269317 / 50000000000000000000000000000000), (275285711747 / 100000000000000000000000000000000)⟩ ⟨-12, 12924529061909621010619436253, 12207031250000000000000000000⟩,
   .log ⟨(7241760128070376296042527833 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1380722846529755478347343081 / 2000000000000000000000000000000), (23002547 / 100000000000000000000000000000000)⟩ ⟨(-119163264706343902913200946417513 / 12500000000000000000000000000000), (317637369053 / 100000000000000000000000000000000)⟩ ⟨-14, 7241760128070376296042527833, 6103515625000000000000000000⟩,
   .log ⟨(78309427042427579441955721699 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1011618452372932438045376250439 / 100000000000000000000000000000000), (22801167 / 6250000000000000000000000000000)⟩ ⟨(-161477757305139585549445375081577 / 25000000000000000000000000000000), (23293406179 / 10000000000000000000000000000000)⟩ ⟨-10, 78309427042427579441955721699, 48828125000000000000000000000⟩,
   .log ⟨(3154898529883487505530600990651 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩ ⟨(5452002000629977185954074050957 / 50000000000000000000000000000000), (501056821 / 12500000000000000000000000000000)⟩ ⟨(-345621385219721994331378287963377 / 100000000000000000000000000000000), (127054942573 / 100000000000000000000000000000000)⟩ ⟨-5, 3154898529883487505530600990651, 3125000000000000000000000000000⟩,
   .log ⟨(7698603852803860679159811007 / 2500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1780843203845114424029959940873 / 100000000000000000000000000000000), (5216777 / 800000000000000000000000000000)⟩ ⟨(-144575175406359929211606310492157 / 25000000000000000000000000000000), (211758237479 / 100000000000000000000000000000000)⟩ ⟨-9, 7698603852803860679159811007, 4882812500000000000000000000⟩,
   .log ⟨(15955597746132917085758812853 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(34875409454573142592713603831 / 25000000000000000000000000000000), (2365111 / 5000000000000000000000000000000)⟩ ⟨(-874311574143957871285697078124269 / 100000000000000000000000000000000), (296461537829 / 100000000000000000000000000000000)⟩ ⟨-13, 15955597746132917085758812853, 12207031250000000000000000000⟩,
   .log ⟨(308702927519657890792613245011 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(356894297667234668311633767527 / 20000000000000000000000000000000), (653703891 / 100000000000000000000000000000000)⟩ ⟨(-289027302506313290239710288398163 / 50000000000000000000000000000000), (105879118739 / 50000000000000000000000000000000)⟩ ⟨-9, 308702927519657890792613245011, 195312500000000000000000000000⟩,
   .log ⟨(30216127494741087159206101773 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(244888105817775592438390103263 / 100000000000000000000000000000000), (8318069 / 10000000000000000000000000000000)⟩ ⟨(-810454966012427346008748038820529 / 100000000000000000000000000000000), (68821427797 / 25000000000000000000000000000000)⟩ ⟨-12, 30216127494741087159206101773, 24414062500000000000000000000⟩,
   .log ⟨(573369051292370077537550288831 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(2959384663076721829910329755453 / 100000000000000000000000000000000), (546370297 / 50000000000000000000000000000000)⟩ ⟨(-516139588700556513683282065940681 / 100000000000000000000000000000000), (19058241367 / 10000000000000000000000000000000)⟩ ⟨-8, 573369051292370077537550288831, 390625000000000000000000000000⟩,
   .log ⟨(5578469393746635659764022855967 / 50000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩ ⟨(3058547257135294209203379630207 / 12500000000000000000000000000000), (1476608569 / 12500000000000000000000000000000)⟩ ⟨(-219310856885859833802796074616251 / 100000000000000000000000000000000), (21175823751 / 20000000000000000000000000000000)⟩ ⟨-4, 5578469393746635659764022855967, 3125000000000000000000000000000⟩,
   .log ⟨(136451581513342476380793490701 / 12500000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(1232843883026774969871488768507 / 25000000000000000000000000000000), (1849263787 / 100000000000000000000000000000000)⟩ ⟨(-451751408577930377411076121778643 / 100000000000000000000000000000000), (16940658983 / 10000000000000000000000000000000)⟩ ⟨-7, 136451581513342476380793490701, 97656250000000000000000000000⟩]
lemma CA1_5_10I1PairCertificates_valid :
    CA1_5_10I1PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I1PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 0, 0, 2, 4 => 1
  | 0, 0, 3, 4 => 2
  | 0, 0, 4, 2 => 1
  | 0, 0, 4, 3 => 2
  | 0, 0, 5, 1 => 3
  | 0, 0, 1, 5 => 3
  | 1, 0, 1, 4 => 4
  | 1, 0, 2, 2 => 5
  | 1, 0, 2, 3 => 6
  | 1, 0, 3, 2 => 6
  | 1, 0, 3, 3 => 7
  | 1, 0, 4, 1 => 4
  | 1, 0, 5, 0 => 8
  | 1, 0, 0, 5 => 8
  | 0, 1, 1, 4 => 4
  | 0, 1, 2, 2 => 5
  | 0, 1, 2, 3 => 6
  | 0, 1, 3, 2 => 6
  | 0, 1, 3, 3 => 7
  | 0, 1, 4, 1 => 4
  | 0, 1, 5, 0 => 8
  | 0, 1, 0, 5 => 8
  | 2, 0, 0, 4 => 9
  | 2, 0, 1, 2 => 10
  | 2, 0, 1, 3 => 11
  | 2, 0, 2, 1 => 10
  | 2, 0, 3, 1 => 11
  | 2, 0, 4, 0 => 9
  | 3, 0, 0, 4 => 12
  | 3, 0, 1, 2 => 13
  | 3, 0, 1, 3 => 14
  | 3, 0, 2, 1 => 13
  | 3, 0, 3, 1 => 14
  | 3, 0, 4, 0 => 12
  | 1, 1, 0, 4 => 15
  | 1, 1, 1, 2 => 16
  | 1, 1, 1, 3 => 17
  | 1, 1, 2, 1 => 16
  | 1, 1, 3, 1 => 17
  | 1, 1, 4, 0 => 15
  | 0, 2, 0, 4 => 9
  | 0, 2, 1, 2 => 10
  | 0, 2, 1, 3 => 11
  | 0, 2, 2, 1 => 10
  | 0, 2, 3, 1 => 11
  | 0, 2, 4, 0 => 9
  | 0, 3, 0, 4 => 12
  | 0, 3, 1, 2 => 13
  | 0, 3, 1, 3 => 14
  | 0, 3, 2, 1 => 13
  | 0, 3, 3, 1 => 14
  | 0, 3, 4, 0 => 12
  | 4, 0, 0, 2 => 9
  | 4, 0, 0, 3 => 12
  | 4, 0, 1, 1 => 15
  | 4, 0, 2, 0 => 9
  | 4, 0, 3, 0 => 12
  | 2, 1, 0, 2 => 10
  | 2, 1, 0, 3 => 13
  | 2, 1, 1, 1 => 16
  | 2, 1, 2, 0 => 10
  | 2, 1, 3, 0 => 13
  | 3, 1, 0, 2 => 11
  | 3, 1, 0, 3 => 14
  | 3, 1, 1, 1 => 17
  | 3, 1, 2, 0 => 11
  | 3, 1, 3, 0 => 14
  | 1, 2, 0, 2 => 10
  | 1, 2, 0, 3 => 13
  | 1, 2, 1, 1 => 16
  | 1, 2, 2, 0 => 10
  | 1, 2, 3, 0 => 13
  | 1, 3, 0, 2 => 11
  | 1, 3, 0, 3 => 14
  | 1, 3, 1, 1 => 17
  | 1, 3, 2, 0 => 11
  | 1, 3, 3, 0 => 14
  | 0, 4, 0, 2 => 9
  | 0, 4, 0, 3 => 12
  | 0, 4, 1, 1 => 15
  | 0, 4, 2, 0 => 9
  | 0, 4, 3, 0 => 12
  | 0, 5, 0, 1 => 8
  | 0, 5, 1, 0 => 8
  | 1, 4, 0, 1 => 4
  | 1, 4, 1, 0 => 4
  | 2, 2, 0, 1 => 5
  | 2, 2, 1, 0 => 5
  | 2, 3, 0, 1 => 6
  | 2, 3, 1, 0 => 6
  | 3, 2, 0, 1 => 6
  | 3, 2, 1, 0 => 6
  | 3, 3, 0, 1 => 7
  | 3, 3, 1, 0 => 7
  | 4, 1, 0, 1 => 4
  | 4, 1, 1, 0 => 4
  | 5, 0, 0, 1 => 8
  | 5, 0, 1, 0 => 8
  | 1, 5, 0, 0 => 3
  | 2, 4, 0, 0 => 1
  | 3, 4, 0, 0 => 2
  | 4, 2, 0, 0 => 1
  | 4, 3, 0, 0 => 2
  | 5, 1, 0, 0 => 3
  | _, _, _, _ => 0
def CA1_5_10I1PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1PairCertificates (CA1_5_10I1PairCertificateIndex a)).input
lemma CA1_5_10I1PairP_check_0_0 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((0,0),(k,l))) (CA1_5_10I1PairP ((0,0),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_0_1 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((0,1),(k,l))) (CA1_5_10I1PairP ((0,1),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_0_2 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((0,2),(k,l))) (CA1_5_10I1PairP ((0,2),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_0_3 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((0,3),(k,l))) (CA1_5_10I1PairP ((0,3),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_0_4 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((0,4),(k,l))) (CA1_5_10I1PairP ((0,4),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_0_5 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((0,5),(k,l))) (CA1_5_10I1PairP ((0,5),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_1_0 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((1,0),(k,l))) (CA1_5_10I1PairP ((1,0),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_1_1 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((1,1),(k,l))) (CA1_5_10I1PairP ((1,1),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_1_2 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((1,2),(k,l))) (CA1_5_10I1PairP ((1,2),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_1_3 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((1,3),(k,l))) (CA1_5_10I1PairP ((1,3),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_1_4 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((1,4),(k,l))) (CA1_5_10I1PairP ((1,4),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_1_5 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((1,5),(k,l))) (CA1_5_10I1PairP ((1,5),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_2_0 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((2,0),(k,l))) (CA1_5_10I1PairP ((2,0),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_2_1 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((2,1),(k,l))) (CA1_5_10I1PairP ((2,1),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_2_2 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((2,2),(k,l))) (CA1_5_10I1PairP ((2,2),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_2_3 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((2,3),(k,l))) (CA1_5_10I1PairP ((2,3),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_2_4 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((2,4),(k,l))) (CA1_5_10I1PairP ((2,4),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_2_5 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((2,5),(k,l))) (CA1_5_10I1PairP ((2,5),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_3_0 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((3,0),(k,l))) (CA1_5_10I1PairP ((3,0),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_3_1 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((3,1),(k,l))) (CA1_5_10I1PairP ((3,1),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_3_2 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((3,2),(k,l))) (CA1_5_10I1PairP ((3,2),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_3_3 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((3,3),(k,l))) (CA1_5_10I1PairP ((3,3),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_3_4 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((3,4),(k,l))) (CA1_5_10I1PairP ((3,4),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_3_5 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((3,5),(k,l))) (CA1_5_10I1PairP ((3,5),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_4_0 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((4,0),(k,l))) (CA1_5_10I1PairP ((4,0),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_4_1 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((4,1),(k,l))) (CA1_5_10I1PairP ((4,1),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_4_2 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((4,2),(k,l))) (CA1_5_10I1PairP ((4,2),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_4_3 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((4,3),(k,l))) (CA1_5_10I1PairP ((4,3),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_4_4 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((4,4),(k,l))) (CA1_5_10I1PairP ((4,4),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_4_5 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((4,5),(k,l))) (CA1_5_10I1PairP ((4,5),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_5_0 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((5,0),(k,l))) (CA1_5_10I1PairP ((5,0),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_5_1 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((5,1),(k,l))) (CA1_5_10I1PairP ((5,1),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_5_2 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((5,2),(k,l))) (CA1_5_10I1PairP ((5,2),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_5_3 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((5,3),(k,l))) (CA1_5_10I1PairP ((5,3),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_5_4 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((5,4),(k,l))) (CA1_5_10I1PairP ((5,4),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check_5_5 : ∀ k l : Fin 6, contains (CA1_5_10I1PairRaw ((5,5),(k,l))) (CA1_5_10I1PairP ((5,5),(k,l))) = true := by
  decide +kernel
lemma CA1_5_10I1PairP_check (a : PairSlot × PairSlot) : contains (CA1_5_10I1PairRaw a) (CA1_5_10I1PairP a) = true := by
  rcases a with ⟨⟨i,j⟩,⟨k,l⟩⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (CA1_5_10I1PairP_check_0_0 k l) (CA1_5_10I1PairP_check_0_1 k l) (CA1_5_10I1PairP_check_0_2 k l) (CA1_5_10I1PairP_check_0_3 k l) (CA1_5_10I1PairP_check_0_4 k l) (CA1_5_10I1PairP_check_0_5 k l)
  · exact forall_fin6 (CA1_5_10I1PairP_check_1_0 k l) (CA1_5_10I1PairP_check_1_1 k l) (CA1_5_10I1PairP_check_1_2 k l) (CA1_5_10I1PairP_check_1_3 k l) (CA1_5_10I1PairP_check_1_4 k l) (CA1_5_10I1PairP_check_1_5 k l)
  · exact forall_fin6 (CA1_5_10I1PairP_check_2_0 k l) (CA1_5_10I1PairP_check_2_1 k l) (CA1_5_10I1PairP_check_2_2 k l) (CA1_5_10I1PairP_check_2_3 k l) (CA1_5_10I1PairP_check_2_4 k l) (CA1_5_10I1PairP_check_2_5 k l)
  · exact forall_fin6 (CA1_5_10I1PairP_check_3_0 k l) (CA1_5_10I1PairP_check_3_1 k l) (CA1_5_10I1PairP_check_3_2 k l) (CA1_5_10I1PairP_check_3_3 k l) (CA1_5_10I1PairP_check_3_4 k l) (CA1_5_10I1PairP_check_3_5 k l)
  · exact forall_fin6 (CA1_5_10I1PairP_check_4_0 k l) (CA1_5_10I1PairP_check_4_1 k l) (CA1_5_10I1PairP_check_4_2 k l) (CA1_5_10I1PairP_check_4_3 k l) (CA1_5_10I1PairP_check_4_4 k l) (CA1_5_10I1PairP_check_4_5 k l)
  · exact forall_fin6 (CA1_5_10I1PairP_check_5_0 k l) (CA1_5_10I1PairP_check_5_1 k l) (CA1_5_10I1PairP_check_5_2 k l) (CA1_5_10I1PairP_check_5_3 k l) (CA1_5_10I1PairP_check_5_4 k l) (CA1_5_10I1PairP_check_5_5 k l)
lemma CA1_5_10I1PairP_sound (a : PairSlot × PairSlot) :
    (CA1_5_10I1PairP a).Encloses (CA1_5_10I1PairValue a) :=
  contains_sound (CA1_5_10I1PairRaw_sound a) (CA1_5_10I1PairP_check a)
def CA1_5_10I1PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1PairCertificates (CA1_5_10I1PairCertificateIndex a)).output
lemma CA1_5_10I1PairTerms_sound (a : PairSlot × PairSlot) :
    (CA1_5_10I1PairTerms a).Encloses (Foundation.entropyTerm (CA1_5_10I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I1PairCertificates_valid
    (CA1_5_10I1PairCertificateIndex a) (CA1_5_10I1PairP_sound a)
def CA1_5_10I1PairEntropy : Ball := ⟨(41523217069936040245483418022181 / 12500000000000000000000000000000), (33568586887 / 25000000000000000000000000000000)⟩
lemma CA1_5_10I1PairEntropy_sound : CA1_5_10I1PairEntropy.Encloses (Foundation.finiteEntropy CA1_5_10I1PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA1_5_10I1PairValue CA1_5_10I1PairTerms CA1_5_10I1PairTerms_sound) (by decide +kernel)
def CA1_5_10I1PairMass : Ball := ⟨(25000000000000000000000000000001 / 25000000000000000000000000000000), (61 / 12500000000000000000000000000000)⟩
lemma CA1_5_10I1PairMass_sound : CA1_5_10I1PairMass.Encloses (∑ a, CA1_5_10I1PairValue a) := by
  exact contains_sound (doublePairSumBall_sound CA1_5_10I1PairP CA1_5_10I1PairValue CA1_5_10I1PairP_sound) (by decide +kernel)
def CA1_5_10I1PairMassTermLogWitness : LogWitness := ⟨0, 25000000000000000000000000000001, 25000000000000000000000000000000⟩
def CA1_5_10I1PairMassTermLog : Ball := ⟨(1 / 25000000000000000000000000000000), (2117582417 / 10000000000000000000000000000000)⟩
lemma CA1_5_10I1PairMassTermLog_sound : CA1_5_10I1PairMassTermLog.Encloses (Real.log ((∑ a, CA1_5_10I1PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_5_10I1PairMass_sound) (w := CA1_5_10I1PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_5_10I1PairMassTerm : Ball := ⟨(-1 / 25000000000000000000000000000000), (21175824171 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I1PairMassTerm_sound : CA1_5_10I1PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I1PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA1_5_10I1PairMass_sound) CA1_5_10I1PairMassTermLog_sound) (by decide +kernel)
def CA1_5_10I1PairH : Ball := ⟨(83046434139872080490966836044363 / 25000000000000000000000000000000), (155450171719 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I1PairH_sound : CA1_5_10I1PairH.Encloses (homogeneousEntropy CA1_5_10I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I1PairValue CA1_5_10I1PairMassTerm_sound CA1_5_10I1PairEntropy_sound) (by decide +kernel)

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
def CA1_5_10I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA1_5_10I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
lemma CA1_5_10I1R0Raw_sound (a : PairSlot) :
    (CA1_5_10I1R0Raw a).Encloses (CA1_5_10I1R0Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 0 a
def CA1_5_10I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(50771816161526734863152209467 / 20000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(758549484444178149680679190387 / 50000000000000000000000000000000), (107513507 / 20000000000000000000000000000000)⟩ ⟨(-59761461518800880570056690030777 / 10000000000000000000000000000000), (211758238011 / 100000000000000000000000000000000)⟩ ⟨-9, 50771816161526734863152209467, 39062500000000000000000000000⟩]
lemma CA1_5_10I1R0Certificates_valid :
    CA1_5_10I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA1_5_10I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R0Certificates (CA1_5_10I1R0CertificateIndex a)).input
lemma CA1_5_10I1R0P_check : ∀ a : PairSlot, contains (CA1_5_10I1R0Raw a) (CA1_5_10I1R0P a) = true := by
  decide +kernel
lemma CA1_5_10I1R0P_sound (a : PairSlot) :
    (CA1_5_10I1R0P a).Encloses (CA1_5_10I1R0Value a) :=
  contains_sound (CA1_5_10I1R0Raw_sound a) (CA1_5_10I1R0P_check a)
def CA1_5_10I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R0Certificates (CA1_5_10I1R0CertificateIndex a)).output
lemma CA1_5_10I1R0Terms_sound (a : PairSlot) :
    (CA1_5_10I1R0Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I1R0Certificates_valid
    (CA1_5_10I1R0CertificateIndex a) (CA1_5_10I1R0P_sound a)
def CA1_5_10I1R0Entropy : Ball := ⟨(758549484444178149680679190387 / 50000000000000000000000000000000), (107513507 / 20000000000000000000000000000000)⟩
lemma CA1_5_10I1R0Entropy_sound : CA1_5_10I1R0Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I1R0Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I1R0Value CA1_5_10I1R0Terms CA1_5_10I1R0Terms_sound) (by decide +kernel)
def CA1_5_10I1R0Mass : Ball := ⟨(50771816161526734863152209467 / 20000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I1R0Mass_sound : CA1_5_10I1R0Mass.Encloses (∑ a, CA1_5_10I1R0Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I1R0P CA1_5_10I1R0Value CA1_5_10I1R0P_sound) (by decide +kernel)
def CA1_5_10I1R0MassTermLogWitness : LogWitness := ⟨-9, 50771816161526734863152209467, 39062500000000000000000000000⟩
def CA1_5_10I1R0MassTermLog : Ball := ⟨(-59761461518800880570056690030777 / 10000000000000000000000000000000), (211758238011 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I1R0MassTermLog_sound : CA1_5_10I1R0MassTermLog.Encloses (Real.log ((∑ a, CA1_5_10I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_5_10I1R0Mass_sound) (w := CA1_5_10I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_5_10I1R0MassTerm : Ball := ⟨(758549484444178149680679190387 / 50000000000000000000000000000000), (107513507 / 20000000000000000000000000000000)⟩
lemma CA1_5_10I1R0MassTerm_sound : CA1_5_10I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_5_10I1R0Mass_sound) CA1_5_10I1R0MassTermLog_sound) (by decide +kernel)
def CA1_5_10I1R0H : Ball := ⟨0, (107513507 / 10000000000000000000000000000000)⟩
lemma CA1_5_10I1R0H_sound : CA1_5_10I1R0H.Encloses (homogeneousEntropy CA1_5_10I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I1R0Value CA1_5_10I1R0MassTerm_sound CA1_5_10I1R0Entropy_sound) (by decide +kernel)
def CA1_5_10I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA1_5_10I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
lemma CA1_5_10I1R1Raw_sound (a : PairSlot) :
    (CA1_5_10I1R1Raw a).Encloses (CA1_5_10I1R1Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 1 a
def CA1_5_10I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1025619396755435995373302370507 / 25000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩ ⟨(13101586701749977828114928045673 / 100000000000000000000000000000000), (5212400591 / 100000000000000000000000000000000)⟩ ⟨(-319357910526971922324675037272351 / 100000000000000000000000000000000), (127054942487 / 100000000000000000000000000000000)⟩ ⟨-5, 1025619396755435995373302370507, 781250000000000000000000000000⟩]
lemma CA1_5_10I1R1Certificates_valid :
    CA1_5_10I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA1_5_10I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R1Certificates (CA1_5_10I1R1CertificateIndex a)).input
lemma CA1_5_10I1R1P_check : ∀ a : PairSlot, contains (CA1_5_10I1R1Raw a) (CA1_5_10I1R1P a) = true := by
  decide +kernel
lemma CA1_5_10I1R1P_sound (a : PairSlot) :
    (CA1_5_10I1R1P a).Encloses (CA1_5_10I1R1Value a) :=
  contains_sound (CA1_5_10I1R1Raw_sound a) (CA1_5_10I1R1P_check a)
def CA1_5_10I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R1Certificates (CA1_5_10I1R1CertificateIndex a)).output
lemma CA1_5_10I1R1Terms_sound (a : PairSlot) :
    (CA1_5_10I1R1Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I1R1Certificates_valid
    (CA1_5_10I1R1CertificateIndex a) (CA1_5_10I1R1P_sound a)
def CA1_5_10I1R1Entropy : Ball := ⟨(13101586701749977828114928045673 / 50000000000000000000000000000000), (5212400591 / 50000000000000000000000000000000)⟩
lemma CA1_5_10I1R1Entropy_sound : CA1_5_10I1R1Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I1R1Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I1R1Value CA1_5_10I1R1Terms CA1_5_10I1R1Terms_sound) (by decide +kernel)
def CA1_5_10I1R1Mass : Ball := ⟨(1025619396755435995373302370507 / 12500000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
lemma CA1_5_10I1R1Mass_sound : CA1_5_10I1R1Mass.Encloses (∑ a, CA1_5_10I1R1Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I1R1P CA1_5_10I1R1Value CA1_5_10I1R1P_sound) (by decide +kernel)
def CA1_5_10I1R1MassTermLogWitness : LogWitness := ⟨-4, 1025619396755435995373302370507, 781250000000000000000000000000⟩
def CA1_5_10I1R1MassTermLog : Ball := ⟨(-250043192470977391382951844222021 / 100000000000000000000000000000000), (26469779701 / 25000000000000000000000000000000)⟩
lemma CA1_5_10I1R1MassTermLog_sound : CA1_5_10I1R1MassTermLog.Encloses (Real.log ((∑ a, CA1_5_10I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_5_10I1R1Mass_sound) (w := CA1_5_10I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_5_10I1R1MassTerm : Ball := ⟨(20515931857990976613637576474281 / 100000000000000000000000000000000), (8687334317 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I1R1MassTerm_sound : CA1_5_10I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_5_10I1R1Mass_sound) CA1_5_10I1R1MassTermLog_sound) (by decide +kernel)
def CA1_5_10I1R1H : Ball := ⟨(1137448309101795808518455923413 / 20000000000000000000000000000000), (19112135499 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I1R1H_sound : CA1_5_10I1R1H.Encloses (homogeneousEntropy CA1_5_10I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I1R1Value CA1_5_10I1R1MassTerm_sound CA1_5_10I1R1Entropy_sound) (by decide +kernel)
def CA1_5_10I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA1_5_10I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
lemma CA1_5_10I1R2Raw_sound (a : PairSlot) :
    (CA1_5_10I1R2Raw a).Encloses (CA1_5_10I1R2Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 2 a
def CA1_5_10I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(3619461538080497091580904874329 / 50000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩ ⟨(19007223939689147579515642461891 / 100000000000000000000000000000000), (7664508023 / 100000000000000000000000000000000)⟩ ⟨(-262569773704091029867312389988677 / 100000000000000000000000000000000), (52939559373 / 50000000000000000000000000000000)⟩ ⟨-4, 3619461538080497091580904874329, 3125000000000000000000000000000⟩,
   .log ⟨(354874652760531895037578159637 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1755924625224395990092778958639 / 50000000000000000000000000000000), (338164343 / 25000000000000000000000000000000)⟩ ⟨(-247400682405075496013496227375001 / 50000000000000000000000000000000), (19058241357 / 10000000000000000000000000000000)⟩ ⟨-8, 354874652760531895037578159637, 195312500000000000000000000000⟩,
   .log ⟨(5128768196356952483244777570549 / 20000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩ ⟨(34897850813233620737731844437989 / 100000000000000000000000000000000), (4072720941 / 25000000000000000000000000000000)⟩ ⟨(-136086676087338601525818244277431 / 100000000000000000000000000000000), (63527471227 / 100000000000000000000000000000000)⟩ ⟨-2, 5128768196356952483244777570549, 5000000000000000000000000000000⟩]
lemma CA1_5_10I1R2Certificates_valid :
    CA1_5_10I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA1_5_10I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R2Certificates (CA1_5_10I1R2CertificateIndex a)).input
lemma CA1_5_10I1R2P_check : ∀ a : PairSlot, contains (CA1_5_10I1R2Raw a) (CA1_5_10I1R2P a) = true := by
  decide +kernel
lemma CA1_5_10I1R2P_sound (a : PairSlot) :
    (CA1_5_10I1R2P a).Encloses (CA1_5_10I1R2Value a) :=
  contains_sound (CA1_5_10I1R2Raw_sound a) (CA1_5_10I1R2P_check a)
def CA1_5_10I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R2Certificates (CA1_5_10I1R2CertificateIndex a)).output
lemma CA1_5_10I1R2Terms_sound (a : PairSlot) :
    (CA1_5_10I1R2Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I1R2Certificates_valid
    (CA1_5_10I1R2CertificateIndex a) (CA1_5_10I1R2P_sound a)
def CA1_5_10I1R2Entropy : Ball := ⟨(79935997193509499857134245196327 / 100000000000000000000000000000000), (17162607277 / 50000000000000000000000000000000)⟩
lemma CA1_5_10I1R2Entropy_sound : CA1_5_10I1R2Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I1R2Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I1R2Value CA1_5_10I1R2Terms CA1_5_10I1R2Terms_sound) (by decide +kernel)
def CA1_5_10I1R2Mass : Ball := ⟨(41541185745148878362697819988609 / 100000000000000000000000000000000), (1 / 1000000000000000000000000000000)⟩
lemma CA1_5_10I1R2Mass_sound : CA1_5_10I1R2Mass.Encloses (∑ a, CA1_5_10I1R2Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I1R2P CA1_5_10I1R2Value CA1_5_10I1R2P_sound) (by decide +kernel)
def CA1_5_10I1R2MassTermLogWitness : LogWitness := ⟨-2, 41541185745148878362697819988609, 25000000000000000000000000000000⟩
def CA1_5_10I1R2MassTermLog : Ball := ⟨(-43924241164408934512891830914001 / 50000000000000000000000000000000), (6352747129 / 10000000000000000000000000000000)⟩
lemma CA1_5_10I1R2MassTermLog_sound : CA1_5_10I1R2MassTermLog.Encloses (Real.log ((∑ a, CA1_5_10I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_5_10I1R2Mass_sound) (w := CA1_5_10I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_5_10I1R2MassTerm : Ball := ⟨(18246650609254260008448820334291 / 50000000000000000000000000000000), (3298758117 / 12500000000000000000000000000000)⟩
lemma CA1_5_10I1R2MassTerm_sound : CA1_5_10I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_5_10I1R2Mass_sound) CA1_5_10I1R2MassTermLog_sound) (by decide +kernel)
def CA1_5_10I1R2H : Ball := ⟨(8688539195000195968047320905549 / 20000000000000000000000000000000), (6071527949 / 10000000000000000000000000000000)⟩
lemma CA1_5_10I1R2H_sound : CA1_5_10I1R2H.Encloses (homogeneousEntropy CA1_5_10I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I1R2Value CA1_5_10I1R2MassTerm_sound CA1_5_10I1R2Entropy_sound) (by decide +kernel)
def CA1_5_10I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA1_5_10I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
lemma CA1_5_10I1R3Raw_sound (a : PairSlot) :
    (CA1_5_10I1R3Raw a).Encloses (CA1_5_10I1R3Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 3 a
def CA1_5_10I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(459258977477173114738445400667 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(134624995532851081425096845973 / 3125000000000000000000000000000), (155602997 / 10000000000000000000000000000000)⟩ ⟨(-469016401237944039661153399430267 / 100000000000000000000000000000000), (169406590007 / 100000000000000000000000000000000)⟩ ⟨-7, 459258977477173114738445400667, 390625000000000000000000000000⟩,
   .log ⟨(9042070851149781056087237091629 / 50000000000000000000000000000000), (51 / 100000000000000000000000000000000)⟩ ⟨(3092631970608047946983192993897 / 10000000000000000000000000000000), (3063572797 / 20000000000000000000000000000000)⟩ ⟨(-171013478080344384390576475007727 / 100000000000000000000000000000000), (84703295013 / 100000000000000000000000000000000)⟩ ⟨-3, 9042070851149781056087237091629, 6250000000000000000000000000000⟩,
   .log ⟨(1767933215320530839697545009713 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(142684904117555242456412765777 / 2000000000000000000000000000000), (262062097 / 10000000000000000000000000000000)⟩ ⟨(-403535899662607171230223242518487 / 100000000000000000000000000000000), (148230766063 / 100000000000000000000000000000000)⟩ ⟨-6, 1767933215320530839697545009713, 1562500000000000000000000000000⟩]
lemma CA1_5_10I1R3Certificates_valid :
    CA1_5_10I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA1_5_10I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R3Certificates (CA1_5_10I1R3CertificateIndex a)).input
lemma CA1_5_10I1R3P_check : ∀ a : PairSlot, contains (CA1_5_10I1R3Raw a) (CA1_5_10I1R3P a) = true := by
  decide +kernel
lemma CA1_5_10I1R3P_sound (a : PairSlot) :
    (CA1_5_10I1R3P a).Encloses (CA1_5_10I1R3Value a) :=
  contains_sound (CA1_5_10I1R3Raw_sound a) (CA1_5_10I1R3P_check a)
def CA1_5_10I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R3Certificates (CA1_5_10I1R3CertificateIndex a)).output
lemma CA1_5_10I1R3Terms_sound (a : PairSlot) :
    (CA1_5_10I1R3Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I1R3Certificates_valid
    (CA1_5_10I1R3CertificateIndex a) (CA1_5_10I1R3P_sound a)
def CA1_5_10I1R3Entropy : Ball := ⟨(10592141192252369049563916824739 / 12500000000000000000000000000000), (779780597 / 2000000000000000000000000000000)⟩
lemma CA1_5_10I1R3Entropy_sound : CA1_5_10I1R3Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I1R3Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I1R3Value CA1_5_10I1R3Terms CA1_5_10I1R3Terms_sound) (by decide +kernel)
def CA1_5_10I1R3Mass : Ball := ⟨(4154118574514887836269781998861 / 10000000000000000000000000000000), (61 / 50000000000000000000000000000000)⟩
lemma CA1_5_10I1R3Mass_sound : CA1_5_10I1R3Mass.Encloses (∑ a, CA1_5_10I1R3Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I1R3P CA1_5_10I1R3Value CA1_5_10I1R3P_sound) (by decide +kernel)
def CA1_5_10I1R3MassTermLogWitness : LogWitness := ⟨-2, 4154118574514887836269781998861, 2500000000000000000000000000000⟩
def CA1_5_10I1R3MassTermLog : Ball := ⟨(-87848482328817869025783661827999 / 100000000000000000000000000000000), (31763735671 / 50000000000000000000000000000000)⟩
lemma CA1_5_10I1R3MassTermLog_sound : CA1_5_10I1R3MassTermLog.Encloses (Real.log ((∑ a, CA1_5_10I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_5_10I1R3Mass_sound) (w := CA1_5_10I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_5_10I1R3MassTerm : Ball := ⟨(18246650609254260008448820334291 / 50000000000000000000000000000000), (26390064977 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I1R3MassTerm_sound : CA1_5_10I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I1R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_5_10I1R3Mass_sound) CA1_5_10I1R3MassTermLog_sound) (by decide +kernel)
def CA1_5_10I1R3H : Ball := ⟨(4824382831951043237961369392933 / 10000000000000000000000000000000), (65379094827 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I1R3H_sound : CA1_5_10I1R3H.Encloses (homogeneousEntropy CA1_5_10I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I1R3Value CA1_5_10I1R3MassTerm_sound CA1_5_10I1R3Entropy_sound) (by decide +kernel)
def CA1_5_10I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA1_5_10I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
lemma CA1_5_10I1R4Raw_sound (a : PairSlot) :
    (CA1_5_10I1R4Raw a).Encloses (CA1_5_10I1R4Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 4 a
def CA1_5_10I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(2896704051228150518417011133 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(128033073422848728261177381463 / 100000000000000000000000000000000), (10734519 / 25000000000000000000000000000000)⟩ ⟨(-883991399594756692363884378296679 / 100000000000000000000000000000000), (148230769233 / 50000000000000000000000000000000)⟩ ⟨-13, 2896704051228150518417011133, 2441406250000000000000000000⟩,
   .log ⟨(503707182470066923959310737177 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(1157968203673813654462679024211 / 25000000000000000000000000000000), (106664147 / 6250000000000000000000000000000)⟩ ⟨(-91955663446798402650992985730799 / 20000000000000000000000000000000), (169406590059 / 100000000000000000000000000000000)⟩ ⟨-7, 503707182470066923959310737177, 390625000000000000000000000000⟩,
   .log ⟨(255193173092274822371952880777 / 5000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩ ⟨(15184873661715505394591427934243 / 100000000000000000000000000000000), (3242355439 / 50000000000000000000000000000000)⟩ ⟨(-59503447830184843211077423545503 / 20000000000000000000000000000000), (63527471323 / 50000000000000000000000000000000)⟩ ⟨-5, 255193173092274822371952880777, 156250000000000000000000000000⟩,
   .log ⟨(502798912778901915241735271733 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(2661181479343130870123496415501 / 100000000000000000000000000000000), (958246327 / 100000000000000000000000000000000)⟩ ⟨(-529273515058960454644340854370279 / 100000000000000000000000000000000), (95291206971 / 50000000000000000000000000000000)⟩ ⟨-8, 502798912778901915241735271733, 390625000000000000000000000000⟩,
   .log ⟨(51698116247638484042477745011 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(97806426929397618687614051929 / 25000000000000000000000000000000), (131370033 / 100000000000000000000000000000000)⟩ ⟨(-756750412033555006927827905490239 / 100000000000000000000000000000000), (25410988613 / 10000000000000000000000000000000)⟩ ⟨-11, 51698116247638484042477745011, 48828125000000000000000000000⟩]
lemma CA1_5_10I1R4Certificates_valid :
    CA1_5_10I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I1R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA1_5_10I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R4Certificates (CA1_5_10I1R4CertificateIndex a)).input
lemma CA1_5_10I1R4P_check : ∀ a : PairSlot, contains (CA1_5_10I1R4Raw a) (CA1_5_10I1R4P a) = true := by
  decide +kernel
lemma CA1_5_10I1R4P_sound (a : PairSlot) :
    (CA1_5_10I1R4P a).Encloses (CA1_5_10I1R4Value a) :=
  contains_sound (CA1_5_10I1R4Raw_sound a) (CA1_5_10I1R4P_check a)
def CA1_5_10I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R4Certificates (CA1_5_10I1R4CertificateIndex a)).output
lemma CA1_5_10I1R4Terms_sound (a : PairSlot) :
    (CA1_5_10I1R4Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I1R4Certificates_valid
    (CA1_5_10I1R4CertificateIndex a) (CA1_5_10I1R4P_sound a)
def CA1_5_10I1R4Entropy : Ball := ⟨(1216730964174222572072506557183 / 4000000000000000000000000000000), (12031702421 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I1R4Entropy_sound : CA1_5_10I1R4Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I1R4Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I1R4Value CA1_5_10I1R4Terms CA1_5_10I1R4Terms_sound) (by decide +kernel)
def CA1_5_10I1R4Mass : Ball := ⟨(1640991034808697592597283792811 / 20000000000000000000000000000000), (51 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I1R4Mass_sound : CA1_5_10I1R4Mass.Encloses (∑ a, CA1_5_10I1R4Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I1R4P CA1_5_10I1R4Value CA1_5_10I1R4P_sound) (by decide +kernel)
def CA1_5_10I1R4MassTermLogWitness : LogWitness := ⟨-4, 1640991034808697592597283792811, 1250000000000000000000000000000⟩
def CA1_5_10I1R4MassTermLog : Ball := ⟨(-250043192470977391382951844222033 / 100000000000000000000000000000000), (26469779759 / 25000000000000000000000000000000)⟩
lemma CA1_5_10I1R4MassTermLog_sound : CA1_5_10I1R4MassTermLog.Encloses (Real.log ((∑ a, CA1_5_10I1R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_5_10I1R4Mass_sound) (w := CA1_5_10I1R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_5_10I1R4MassTerm : Ball := ⟨(512898296449774415340939411857 / 2500000000000000000000000000000), (542958399 / 6250000000000000000000000000000)⟩
lemma CA1_5_10I1R4MassTerm_sound : CA1_5_10I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I1R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_5_10I1R4Mass_sound) CA1_5_10I1R4MassTermLog_sound) (by decide +kernel)
def CA1_5_10I1R4H : Ball := ⟨(1980468449272917537635017491059 / 20000000000000000000000000000000), (4143807361 / 20000000000000000000000000000000)⟩
lemma CA1_5_10I1R4H_sound : CA1_5_10I1R4H.Encloses (homogeneousEntropy CA1_5_10I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I1R4Value CA1_5_10I1R4MassTerm_sound CA1_5_10I1R4Entropy_sound) (by decide +kernel)
def CA1_5_10I1R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 5 a
def CA1_5_10I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
lemma CA1_5_10I1R5Raw_sound (a : PairSlot) :
    (CA1_5_10I1R5Raw a).Encloses (CA1_5_10I1R5Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 5 a
def CA1_5_10I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(5438635077537771407403874419 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(53404118816045124414143044197 / 100000000000000000000000000000000), (2303353 / 12500000000000000000000000000000)⟩ ⟨(-122742466755608112311191459318267 / 12500000000000000000000000000000), (67762639463 / 20000000000000000000000000000000)⟩ ⟨-15, 5438635077537771407403874419, 3051757812500000000000000000⟩,
   .log ⟨(22268884945206414182146674039 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(47323448329967572271861989909 / 6250000000000000000000000000000), (129679553 / 50000000000000000000000000000000)⟩ ⟨(-170007428558399866366735946547719 / 25000000000000000000000000000000), (232934062309 / 100000000000000000000000000000000)⟩ ⟨-10, 22268884945206414182146674039, 19531250000000000000000000000⟩,
   .log ⟨(5073240300123497419871639527 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(93304991677621678275312218259 / 100000000000000000000000000000000), (1007157 / 3125000000000000000000000000000)⟩ ⟨(-91957985585021828636861036394861 / 10000000000000000000000000000000), (3176373651 / 1000000000000000000000000000000)⟩ ⟨-14, 5073240300123497419871639527, 3051757812500000000000000000⟩]
lemma CA1_5_10I1R5Certificates_valid :
    CA1_5_10I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 5 => 1
  | 2, 4 => 2
  | 3, 4 => 3
  | 4, 2 => 2
  | 4, 3 => 3
  | 5, 1 => 1
  | _, _ => 0
def CA1_5_10I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R5Certificates (CA1_5_10I1R5CertificateIndex a)).input
lemma CA1_5_10I1R5P_check : ∀ a : PairSlot, contains (CA1_5_10I1R5Raw a) (CA1_5_10I1R5P a) = true := by
  decide +kernel
lemma CA1_5_10I1R5P_sound (a : PairSlot) :
    (CA1_5_10I1R5P a).Encloses (CA1_5_10I1R5Value a) :=
  contains_sound (CA1_5_10I1R5Raw_sound a) (CA1_5_10I1R5P_check a)
def CA1_5_10I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R5Certificates (CA1_5_10I1R5CertificateIndex a)).output
lemma CA1_5_10I1R5Terms_sound (a : PairSlot) :
    (CA1_5_10I1R5Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I1R5Certificates_valid
    (CA1_5_10I1R5CertificateIndex a) (CA1_5_10I1R5P_sound a)
def CA1_5_10I1R5Entropy : Ball := ⟨(903884283773147959039247101 / 50000000000000000000000000000), (155007477 / 25000000000000000000000000000000)⟩
lemma CA1_5_10I1R5Entropy_sound : CA1_5_10I1R5Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I1R5Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I1R5Value CA1_5_10I1R5Terms CA1_5_10I1R5Terms_sound) (by decide +kernel)
def CA1_5_10I1R5Mass : Ball := ⟨(31732385100954209289470130917 / 12500000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
lemma CA1_5_10I1R5Mass_sound : CA1_5_10I1R5Mass.Encloses (∑ a, CA1_5_10I1R5Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I1R5P CA1_5_10I1R5Value CA1_5_10I1R5P_sound) (by decide +kernel)
def CA1_5_10I1R5MassTermLogWitness : LogWitness := ⟨-9, 31732385100954209289470130917, 24414062500000000000000000000⟩
def CA1_5_10I1R5MassTermLog : Ball := ⟨(-37350913449250550356285431269211 / 6250000000000000000000000000000), (211758239981 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I1R5MassTermLog_sound : CA1_5_10I1R5MassTermLog.Encloses (Real.log ((∑ a, CA1_5_10I1R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_5_10I1R5Mass_sound) (w := CA1_5_10I1R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_5_10I1R5MassTerm : Ball := ⟨(758549484444178149680679190389 / 50000000000000000000000000000000), (53756757 / 10000000000000000000000000000000)⟩
lemma CA1_5_10I1R5MassTerm_sound : CA1_5_10I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I1R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_5_10I1R5Mass_sound) CA1_5_10I1R5MassTermLog_sound) (by decide +kernel)
def CA1_5_10I1R5H : Ball := ⟨(145334799328969809358567910611 / 50000000000000000000000000000000), (578798739 / 50000000000000000000000000000000)⟩
lemma CA1_5_10I1R5H_sound : CA1_5_10I1R5H.Encloses (homogeneousEntropy CA1_5_10I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I1R5Value CA1_5_10I1R5MassTerm_sound CA1_5_10I1R5Entropy_sound) (by decide +kernel)
def CA1_5_10I1R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 6 a
def CA1_5_10I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
lemma CA1_5_10I1R6Raw_sound (a : PairSlot) :
    (CA1_5_10I1R6Raw a).Encloses (CA1_5_10I1R6Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 6 a
def CA1_5_10I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_5_10I1R6Certificates_valid :
    CA1_5_10I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I1R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I1R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R6Certificates (CA1_5_10I1R6CertificateIndex a)).input
lemma CA1_5_10I1R6P_check : ∀ a : PairSlot, contains (CA1_5_10I1R6Raw a) (CA1_5_10I1R6P a) = true := by
  decide +kernel
lemma CA1_5_10I1R6P_sound (a : PairSlot) :
    (CA1_5_10I1R6P a).Encloses (CA1_5_10I1R6Value a) :=
  contains_sound (CA1_5_10I1R6Raw_sound a) (CA1_5_10I1R6P_check a)
def CA1_5_10I1R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R6Certificates (CA1_5_10I1R6CertificateIndex a)).output
lemma CA1_5_10I1R6Terms_sound (a : PairSlot) :
    (CA1_5_10I1R6Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I1R6Certificates_valid
    (CA1_5_10I1R6CertificateIndex a) (CA1_5_10I1R6P_sound a)
def CA1_5_10I1R6Entropy : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R6Entropy_sound : CA1_5_10I1R6Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I1R6Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I1R6Value CA1_5_10I1R6Terms CA1_5_10I1R6Terms_sound) (by decide +kernel)
def CA1_5_10I1R6Mass : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R6Mass_sound : CA1_5_10I1R6Mass.Encloses (∑ a, CA1_5_10I1R6Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I1R6P CA1_5_10I1R6Value CA1_5_10I1R6P_sound) (by decide +kernel)
def CA1_5_10I1R6MassTerm : Ball := .exact 0
lemma CA1_5_10I1R6MassTerm_sound : CA1_5_10I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I1R6Value a))) :=
  entropyTerm_zero_ball (CA1_5_10I1R6Mass_sound)
def CA1_5_10I1R6H : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R6H_sound : CA1_5_10I1R6H.Encloses (homogeneousEntropy CA1_5_10I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I1R6Value CA1_5_10I1R6MassTerm_sound CA1_5_10I1R6Entropy_sound) (by decide +kernel)
def CA1_5_10I1R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 7 a
def CA1_5_10I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
lemma CA1_5_10I1R7Raw_sound (a : PairSlot) :
    (CA1_5_10I1R7Raw a).Encloses (CA1_5_10I1R7Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 7 a
def CA1_5_10I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_5_10I1R7Certificates_valid :
    CA1_5_10I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I1R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I1R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R7Certificates (CA1_5_10I1R7CertificateIndex a)).input
lemma CA1_5_10I1R7P_check : ∀ a : PairSlot, contains (CA1_5_10I1R7Raw a) (CA1_5_10I1R7P a) = true := by
  decide +kernel
lemma CA1_5_10I1R7P_sound (a : PairSlot) :
    (CA1_5_10I1R7P a).Encloses (CA1_5_10I1R7Value a) :=
  contains_sound (CA1_5_10I1R7Raw_sound a) (CA1_5_10I1R7P_check a)
def CA1_5_10I1R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R7Certificates (CA1_5_10I1R7CertificateIndex a)).output
lemma CA1_5_10I1R7Terms_sound (a : PairSlot) :
    (CA1_5_10I1R7Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I1R7Certificates_valid
    (CA1_5_10I1R7CertificateIndex a) (CA1_5_10I1R7P_sound a)
def CA1_5_10I1R7Entropy : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R7Entropy_sound : CA1_5_10I1R7Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I1R7Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I1R7Value CA1_5_10I1R7Terms CA1_5_10I1R7Terms_sound) (by decide +kernel)
def CA1_5_10I1R7Mass : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R7Mass_sound : CA1_5_10I1R7Mass.Encloses (∑ a, CA1_5_10I1R7Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I1R7P CA1_5_10I1R7Value CA1_5_10I1R7P_sound) (by decide +kernel)
def CA1_5_10I1R7MassTerm : Ball := .exact 0
lemma CA1_5_10I1R7MassTerm_sound : CA1_5_10I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I1R7Value a))) :=
  entropyTerm_zero_ball (CA1_5_10I1R7Mass_sound)
def CA1_5_10I1R7H : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R7H_sound : CA1_5_10I1R7H.Encloses (homogeneousEntropy CA1_5_10I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I1R7Value CA1_5_10I1R7MassTerm_sound CA1_5_10I1R7Entropy_sound) (by decide +kernel)
def CA1_5_10I1R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 8 a
def CA1_5_10I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
lemma CA1_5_10I1R8Raw_sound (a : PairSlot) :
    (CA1_5_10I1R8Raw a).Encloses (CA1_5_10I1R8Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 8 a
def CA1_5_10I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_5_10I1R8Certificates_valid :
    CA1_5_10I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R8Certificates (CA1_5_10I1R8CertificateIndex a)).input
lemma CA1_5_10I1R8P_check : ∀ a : PairSlot, contains (CA1_5_10I1R8Raw a) (CA1_5_10I1R8P a) = true := by
  decide +kernel
lemma CA1_5_10I1R8P_sound (a : PairSlot) :
    (CA1_5_10I1R8P a).Encloses (CA1_5_10I1R8Value a) :=
  contains_sound (CA1_5_10I1R8Raw_sound a) (CA1_5_10I1R8P_check a)
def CA1_5_10I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R8Certificates (CA1_5_10I1R8CertificateIndex a)).output
lemma CA1_5_10I1R8Terms_sound (a : PairSlot) :
    (CA1_5_10I1R8Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I1R8Certificates_valid
    (CA1_5_10I1R8CertificateIndex a) (CA1_5_10I1R8P_sound a)
def CA1_5_10I1R8Entropy : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R8Entropy_sound : CA1_5_10I1R8Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I1R8Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I1R8Value CA1_5_10I1R8Terms CA1_5_10I1R8Terms_sound) (by decide +kernel)
def CA1_5_10I1R8Mass : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R8Mass_sound : CA1_5_10I1R8Mass.Encloses (∑ a, CA1_5_10I1R8Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I1R8P CA1_5_10I1R8Value CA1_5_10I1R8P_sound) (by decide +kernel)
def CA1_5_10I1R8MassTerm : Ball := .exact 0
lemma CA1_5_10I1R8MassTerm_sound : CA1_5_10I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I1R8Value a))) :=
  entropyTerm_zero_ball (CA1_5_10I1R8Mass_sound)
def CA1_5_10I1R8H : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R8H_sound : CA1_5_10I1R8H.Encloses (homogeneousEntropy CA1_5_10I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I1R8Value CA1_5_10I1R8MassTerm_sound CA1_5_10I1R8Entropy_sound) (by decide +kernel)
def CA1_5_10I1R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 9 a
def CA1_5_10I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
lemma CA1_5_10I1R9Raw_sound (a : PairSlot) :
    (CA1_5_10I1R9Raw a).Encloses (CA1_5_10I1R9Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 9 a
def CA1_5_10I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_5_10I1R9Certificates_valid :
    CA1_5_10I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R9Certificates (CA1_5_10I1R9CertificateIndex a)).input
lemma CA1_5_10I1R9P_check : ∀ a : PairSlot, contains (CA1_5_10I1R9Raw a) (CA1_5_10I1R9P a) = true := by
  decide +kernel
lemma CA1_5_10I1R9P_sound (a : PairSlot) :
    (CA1_5_10I1R9P a).Encloses (CA1_5_10I1R9Value a) :=
  contains_sound (CA1_5_10I1R9Raw_sound a) (CA1_5_10I1R9P_check a)
def CA1_5_10I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R9Certificates (CA1_5_10I1R9CertificateIndex a)).output
lemma CA1_5_10I1R9Terms_sound (a : PairSlot) :
    (CA1_5_10I1R9Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I1R9Certificates_valid
    (CA1_5_10I1R9CertificateIndex a) (CA1_5_10I1R9P_sound a)
def CA1_5_10I1R9Entropy : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R9Entropy_sound : CA1_5_10I1R9Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I1R9Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I1R9Value CA1_5_10I1R9Terms CA1_5_10I1R9Terms_sound) (by decide +kernel)
def CA1_5_10I1R9Mass : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R9Mass_sound : CA1_5_10I1R9Mass.Encloses (∑ a, CA1_5_10I1R9Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I1R9P CA1_5_10I1R9Value CA1_5_10I1R9P_sound) (by decide +kernel)
def CA1_5_10I1R9MassTerm : Ball := .exact 0
lemma CA1_5_10I1R9MassTerm_sound : CA1_5_10I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I1R9Value a))) :=
  entropyTerm_zero_ball (CA1_5_10I1R9Mass_sound)
def CA1_5_10I1R9H : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R9H_sound : CA1_5_10I1R9H.Encloses (homogeneousEntropy CA1_5_10I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I1R9Value CA1_5_10I1R9MassTerm_sound CA1_5_10I1R9Entropy_sound) (by decide +kernel)
def CA1_5_10I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA1_5_10I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
lemma CA1_5_10I1R10Raw_sound (a : PairSlot) :
    (CA1_5_10I1R10Raw a).Encloses (CA1_5_10I1R10Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 10 a
def CA1_5_10I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_5_10I1R10Certificates_valid :
    CA1_5_10I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R10Certificates (CA1_5_10I1R10CertificateIndex a)).input
lemma CA1_5_10I1R10P_check : ∀ a : PairSlot, contains (CA1_5_10I1R10Raw a) (CA1_5_10I1R10P a) = true := by
  decide +kernel
lemma CA1_5_10I1R10P_sound (a : PairSlot) :
    (CA1_5_10I1R10P a).Encloses (CA1_5_10I1R10Value a) :=
  contains_sound (CA1_5_10I1R10Raw_sound a) (CA1_5_10I1R10P_check a)
def CA1_5_10I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R10Certificates (CA1_5_10I1R10CertificateIndex a)).output
lemma CA1_5_10I1R10Terms_sound (a : PairSlot) :
    (CA1_5_10I1R10Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I1R10Certificates_valid
    (CA1_5_10I1R10CertificateIndex a) (CA1_5_10I1R10P_sound a)
def CA1_5_10I1R10Entropy : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R10Entropy_sound : CA1_5_10I1R10Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I1R10Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I1R10Value CA1_5_10I1R10Terms CA1_5_10I1R10Terms_sound) (by decide +kernel)
def CA1_5_10I1R10Mass : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R10Mass_sound : CA1_5_10I1R10Mass.Encloses (∑ a, CA1_5_10I1R10Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I1R10P CA1_5_10I1R10Value CA1_5_10I1R10P_sound) (by decide +kernel)
def CA1_5_10I1R10MassTerm : Ball := .exact 0
lemma CA1_5_10I1R10MassTerm_sound : CA1_5_10I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I1R10Value a))) :=
  entropyTerm_zero_ball (CA1_5_10I1R10Mass_sound)
def CA1_5_10I1R10H : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R10H_sound : CA1_5_10I1R10H.Encloses (homogeneousEntropy CA1_5_10I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I1R10Value CA1_5_10I1R10MassTerm_sound CA1_5_10I1R10Entropy_sound) (by decide +kernel)
def CA1_5_10I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA1_5_10I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
lemma CA1_5_10I1R11Raw_sound (a : PairSlot) :
    (CA1_5_10I1R11Raw a).Encloses (CA1_5_10I1R11Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 11 a
def CA1_5_10I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_5_10I1R11Certificates_valid :
    CA1_5_10I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R11Certificates (CA1_5_10I1R11CertificateIndex a)).input
lemma CA1_5_10I1R11P_check : ∀ a : PairSlot, contains (CA1_5_10I1R11Raw a) (CA1_5_10I1R11P a) = true := by
  decide +kernel
lemma CA1_5_10I1R11P_sound (a : PairSlot) :
    (CA1_5_10I1R11P a).Encloses (CA1_5_10I1R11Value a) :=
  contains_sound (CA1_5_10I1R11Raw_sound a) (CA1_5_10I1R11P_check a)
def CA1_5_10I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R11Certificates (CA1_5_10I1R11CertificateIndex a)).output
lemma CA1_5_10I1R11Terms_sound (a : PairSlot) :
    (CA1_5_10I1R11Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I1R11Certificates_valid
    (CA1_5_10I1R11CertificateIndex a) (CA1_5_10I1R11P_sound a)
def CA1_5_10I1R11Entropy : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R11Entropy_sound : CA1_5_10I1R11Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I1R11Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I1R11Value CA1_5_10I1R11Terms CA1_5_10I1R11Terms_sound) (by decide +kernel)
def CA1_5_10I1R11Mass : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R11Mass_sound : CA1_5_10I1R11Mass.Encloses (∑ a, CA1_5_10I1R11Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I1R11P CA1_5_10I1R11Value CA1_5_10I1R11P_sound) (by decide +kernel)
def CA1_5_10I1R11MassTerm : Ball := .exact 0
lemma CA1_5_10I1R11MassTerm_sound : CA1_5_10I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I1R11Value a))) :=
  entropyTerm_zero_ball (CA1_5_10I1R11Mass_sound)
def CA1_5_10I1R11H : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R11H_sound : CA1_5_10I1R11H.Encloses (homogeneousEntropy CA1_5_10I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I1R11Value CA1_5_10I1R11MassTerm_sound CA1_5_10I1R11Entropy_sound) (by decide +kernel)
def CA1_5_10I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA1_5_10I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
lemma CA1_5_10I1R12Raw_sound (a : PairSlot) :
    (CA1_5_10I1R12Raw a).Encloses (CA1_5_10I1R12Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 12 a
def CA1_5_10I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_5_10I1R12Certificates_valid :
    CA1_5_10I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R12Certificates (CA1_5_10I1R12CertificateIndex a)).input
lemma CA1_5_10I1R12P_check : ∀ a : PairSlot, contains (CA1_5_10I1R12Raw a) (CA1_5_10I1R12P a) = true := by
  decide +kernel
lemma CA1_5_10I1R12P_sound (a : PairSlot) :
    (CA1_5_10I1R12P a).Encloses (CA1_5_10I1R12Value a) :=
  contains_sound (CA1_5_10I1R12Raw_sound a) (CA1_5_10I1R12P_check a)
def CA1_5_10I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R12Certificates (CA1_5_10I1R12CertificateIndex a)).output
lemma CA1_5_10I1R12Terms_sound (a : PairSlot) :
    (CA1_5_10I1R12Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I1R12Certificates_valid
    (CA1_5_10I1R12CertificateIndex a) (CA1_5_10I1R12P_sound a)
def CA1_5_10I1R12Entropy : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R12Entropy_sound : CA1_5_10I1R12Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I1R12Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I1R12Value CA1_5_10I1R12Terms CA1_5_10I1R12Terms_sound) (by decide +kernel)
def CA1_5_10I1R12Mass : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R12Mass_sound : CA1_5_10I1R12Mass.Encloses (∑ a, CA1_5_10I1R12Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I1R12P CA1_5_10I1R12Value CA1_5_10I1R12P_sound) (by decide +kernel)
def CA1_5_10I1R12MassTerm : Ball := .exact 0
lemma CA1_5_10I1R12MassTerm_sound : CA1_5_10I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I1R12Value a))) :=
  entropyTerm_zero_ball (CA1_5_10I1R12Mass_sound)
def CA1_5_10I1R12H : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R12H_sound : CA1_5_10I1R12H.Encloses (homogeneousEntropy CA1_5_10I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I1R12Value CA1_5_10I1R12MassTerm_sound CA1_5_10I1R12Entropy_sound) (by decide +kernel)
def CA1_5_10I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA1_5_10I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
lemma CA1_5_10I1R13Raw_sound (a : PairSlot) :
    (CA1_5_10I1R13Raw a).Encloses (CA1_5_10I1R13Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 13 a
def CA1_5_10I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_5_10I1R13Certificates_valid :
    CA1_5_10I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R13Certificates (CA1_5_10I1R13CertificateIndex a)).input
lemma CA1_5_10I1R13P_check : ∀ a : PairSlot, contains (CA1_5_10I1R13Raw a) (CA1_5_10I1R13P a) = true := by
  decide +kernel
lemma CA1_5_10I1R13P_sound (a : PairSlot) :
    (CA1_5_10I1R13P a).Encloses (CA1_5_10I1R13Value a) :=
  contains_sound (CA1_5_10I1R13Raw_sound a) (CA1_5_10I1R13P_check a)
def CA1_5_10I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R13Certificates (CA1_5_10I1R13CertificateIndex a)).output
lemma CA1_5_10I1R13Terms_sound (a : PairSlot) :
    (CA1_5_10I1R13Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I1R13Certificates_valid
    (CA1_5_10I1R13CertificateIndex a) (CA1_5_10I1R13P_sound a)
def CA1_5_10I1R13Entropy : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R13Entropy_sound : CA1_5_10I1R13Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I1R13Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I1R13Value CA1_5_10I1R13Terms CA1_5_10I1R13Terms_sound) (by decide +kernel)
def CA1_5_10I1R13Mass : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R13Mass_sound : CA1_5_10I1R13Mass.Encloses (∑ a, CA1_5_10I1R13Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I1R13P CA1_5_10I1R13Value CA1_5_10I1R13P_sound) (by decide +kernel)
def CA1_5_10I1R13MassTerm : Ball := .exact 0
lemma CA1_5_10I1R13MassTerm_sound : CA1_5_10I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I1R13Value a))) :=
  entropyTerm_zero_ball (CA1_5_10I1R13Mass_sound)
def CA1_5_10I1R13H : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R13H_sound : CA1_5_10I1R13H.Encloses (homogeneousEntropy CA1_5_10I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I1R13Value CA1_5_10I1R13MassTerm_sound CA1_5_10I1R13Entropy_sound) (by decide +kernel)
def CA1_5_10I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA1_5_10I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
lemma CA1_5_10I1R14Raw_sound (a : PairSlot) :
    (CA1_5_10I1R14Raw a).Encloses (CA1_5_10I1R14Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 14 a
def CA1_5_10I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_5_10I1R14Certificates_valid :
    CA1_5_10I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R14Certificates (CA1_5_10I1R14CertificateIndex a)).input
lemma CA1_5_10I1R14P_check : ∀ a : PairSlot, contains (CA1_5_10I1R14Raw a) (CA1_5_10I1R14P a) = true := by
  decide +kernel
lemma CA1_5_10I1R14P_sound (a : PairSlot) :
    (CA1_5_10I1R14P a).Encloses (CA1_5_10I1R14Value a) :=
  contains_sound (CA1_5_10I1R14Raw_sound a) (CA1_5_10I1R14P_check a)
def CA1_5_10I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R14Certificates (CA1_5_10I1R14CertificateIndex a)).output
lemma CA1_5_10I1R14Terms_sound (a : PairSlot) :
    (CA1_5_10I1R14Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I1R14Certificates_valid
    (CA1_5_10I1R14CertificateIndex a) (CA1_5_10I1R14P_sound a)
def CA1_5_10I1R14Entropy : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R14Entropy_sound : CA1_5_10I1R14Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I1R14Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I1R14Value CA1_5_10I1R14Terms CA1_5_10I1R14Terms_sound) (by decide +kernel)
def CA1_5_10I1R14Mass : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R14Mass_sound : CA1_5_10I1R14Mass.Encloses (∑ a, CA1_5_10I1R14Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I1R14P CA1_5_10I1R14Value CA1_5_10I1R14P_sound) (by decide +kernel)
def CA1_5_10I1R14MassTerm : Ball := .exact 0
lemma CA1_5_10I1R14MassTerm_sound : CA1_5_10I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I1R14Value a))) :=
  entropyTerm_zero_ball (CA1_5_10I1R14Mass_sound)
def CA1_5_10I1R14H : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R14H_sound : CA1_5_10I1R14H.Encloses (homogeneousEntropy CA1_5_10I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I1R14Value CA1_5_10I1R14MassTerm_sound CA1_5_10I1R14Entropy_sound) (by decide +kernel)
def CA1_5_10I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA1_5_10I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
lemma CA1_5_10I1R15Raw_sound (a : PairSlot) :
    (CA1_5_10I1R15Raw a).Encloses (CA1_5_10I1R15Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 15 a
def CA1_5_10I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_5_10I1R15Certificates_valid :
    CA1_5_10I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R15Certificates (CA1_5_10I1R15CertificateIndex a)).input
lemma CA1_5_10I1R15P_check : ∀ a : PairSlot, contains (CA1_5_10I1R15Raw a) (CA1_5_10I1R15P a) = true := by
  decide +kernel
lemma CA1_5_10I1R15P_sound (a : PairSlot) :
    (CA1_5_10I1R15P a).Encloses (CA1_5_10I1R15Value a) :=
  contains_sound (CA1_5_10I1R15Raw_sound a) (CA1_5_10I1R15P_check a)
def CA1_5_10I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R15Certificates (CA1_5_10I1R15CertificateIndex a)).output
lemma CA1_5_10I1R15Terms_sound (a : PairSlot) :
    (CA1_5_10I1R15Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I1R15Certificates_valid
    (CA1_5_10I1R15CertificateIndex a) (CA1_5_10I1R15P_sound a)
def CA1_5_10I1R15Entropy : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R15Entropy_sound : CA1_5_10I1R15Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I1R15Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I1R15Value CA1_5_10I1R15Terms CA1_5_10I1R15Terms_sound) (by decide +kernel)
def CA1_5_10I1R15Mass : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R15Mass_sound : CA1_5_10I1R15Mass.Encloses (∑ a, CA1_5_10I1R15Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I1R15P CA1_5_10I1R15Value CA1_5_10I1R15P_sound) (by decide +kernel)
def CA1_5_10I1R15MassTerm : Ball := .exact 0
lemma CA1_5_10I1R15MassTerm_sound : CA1_5_10I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I1R15Value a))) :=
  entropyTerm_zero_ball (CA1_5_10I1R15Mass_sound)
def CA1_5_10I1R15H : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R15H_sound : CA1_5_10I1R15H.Encloses (homogeneousEntropy CA1_5_10I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I1R15Value CA1_5_10I1R15MassTerm_sound CA1_5_10I1R15Entropy_sound) (by decide +kernel)
def CA1_5_10I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA1_5_10I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 1 5 10)) A1_5_10Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
lemma CA1_5_10I1R16Raw_sound (a : PairSlot) :
    (CA1_5_10I1R16Raw a).Encloses (CA1_5_10I1R16Value a) := by
  exact residualBall_sound_on (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_5_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 5 10) (show (shape 1 5 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 16 a
def CA1_5_10I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_5_10I1R16Certificates_valid :
    CA1_5_10I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_5_10I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R16Certificates (CA1_5_10I1R16CertificateIndex a)).input
lemma CA1_5_10I1R16P_check : ∀ a : PairSlot, contains (CA1_5_10I1R16Raw a) (CA1_5_10I1R16P a) = true := by
  decide +kernel
lemma CA1_5_10I1R16P_sound (a : PairSlot) :
    (CA1_5_10I1R16P a).Encloses (CA1_5_10I1R16Value a) :=
  contains_sound (CA1_5_10I1R16Raw_sound a) (CA1_5_10I1R16P_check a)
def CA1_5_10I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I1R16Certificates (CA1_5_10I1R16CertificateIndex a)).output
lemma CA1_5_10I1R16Terms_sound (a : PairSlot) :
    (CA1_5_10I1R16Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I1R16Certificates_valid
    (CA1_5_10I1R16CertificateIndex a) (CA1_5_10I1R16P_sound a)
def CA1_5_10I1R16Entropy : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R16Entropy_sound : CA1_5_10I1R16Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I1R16Value) := by
  exact contains_sound (entropyPair_enclosed CA1_5_10I1R16Value CA1_5_10I1R16Terms CA1_5_10I1R16Terms_sound) (by decide +kernel)
def CA1_5_10I1R16Mass : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R16Mass_sound : CA1_5_10I1R16Mass.Encloses (∑ a, CA1_5_10I1R16Value a) := by
  exact contains_sound (pairSumBall_sound CA1_5_10I1R16P CA1_5_10I1R16Value CA1_5_10I1R16P_sound) (by decide +kernel)
def CA1_5_10I1R16MassTerm : Ball := .exact 0
lemma CA1_5_10I1R16MassTerm_sound : CA1_5_10I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I1R16Value a))) :=
  entropyTerm_zero_ball (CA1_5_10I1R16Mass_sound)
def CA1_5_10I1R16H : Ball := ⟨0, 0⟩
lemma CA1_5_10I1R16H_sound : CA1_5_10I1R16H.Encloses (homogeneousEntropy CA1_5_10I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I1R16Value CA1_5_10I1R16MassTerm_sound CA1_5_10I1R16Entropy_sound) (by decide +kernel)
def CA1_5_10I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA1_5_10I1R0H
  | 1 => CA1_5_10I1R1H
  | 2 => CA1_5_10I1R2H
  | 3 => CA1_5_10I1R3H
  | 4 => CA1_5_10I1R4H
  | 5 => CA1_5_10I1R5H
  | 6 => CA1_5_10I1R6H
  | 7 => CA1_5_10I1R7H
  | 8 => CA1_5_10I1R8H
  | 9 => CA1_5_10I1R9H
  | 10 => CA1_5_10I1R10H
  | 11 => CA1_5_10I1R11H
  | 12 => CA1_5_10I1R12H
  | 13 => CA1_5_10I1R13H
  | 14 => CA1_5_10I1R14H
  | 15 => CA1_5_10I1R15H
  | 16 => CA1_5_10I1R16H
  | _ => (.exact 0)
lemma CA1_5_10I1ResidualEntropies_sound (k : Fin 17) :
    (CA1_5_10I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CA1_5_10I1R0H_sound
  · exact CA1_5_10I1R1H_sound
  · exact CA1_5_10I1R2H_sound
  · exact CA1_5_10I1R3H_sound
  · exact CA1_5_10I1R4H_sound
  · exact CA1_5_10I1R5H_sound
  · exact CA1_5_10I1R6H_sound
  · exact CA1_5_10I1R7H_sound
  · exact CA1_5_10I1R8H_sound
  · exact CA1_5_10I1R9H_sound
  · exact CA1_5_10I1R10H_sound
  · exact CA1_5_10I1R11H_sound
  · exact CA1_5_10I1R12H_sound
  · exact CA1_5_10I1R13H_sound
  · exact CA1_5_10I1R14H_sound
  · exact CA1_5_10I1R15H_sound
  · exact CA1_5_10I1R16H_sound
def CA1_5_10I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
lemma CA1_5_10I1Singles_sound (u : Shape) (hu : u ∈ below (shape 1 5 10))
    (hd : designated (Equiv.refl (Fin 3)) 1 u) :
    (CA1_5_10I1Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) u)) := by
  rw [A1_5_10_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
def CA1_5_10I1Singleton : Ball := ⟨0, 0⟩
lemma CA1_5_10I1Singleton_sound : CA1_5_10I1Singleton.Encloses
    (singletonEntropy (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1
    CA1_5_10I1Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_5_10Law_sound u) CA1_5_10I1Singles_sound) (by decide +kernel)
def CA1_5_10I1Group : Ball := ⟨(107566777685042918569334801350657 / 100000000000000000000000000000000), (168158279169 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I1Group_sound : CA1_5_10I1Group.Encloses
    (groupedEntropy (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA1_5_10I1Singleton_sound
    (finSumBall_sound 17 CA1_5_10I1ResidualEntropies _ CA1_5_10I1ResidualEntropies_sound)) (by decide +kernel)

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
def CA1_5_10I1H : Ball := ⟨(58526090594701242412598870738069 / 50000000000000000000000000000000), (491766730057 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I1_sound : CA1_5_10I1H.Encloses (stageACapacity (shape 1 5 10) 1) := by
  have hb := contains_sound (Ball.add_sound CA1_5_10I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA1_5_10I1Group_sound)))
    (show contains (.add CA1_5_10I1PairH (.neg (.mul (.exact 2) CA1_5_10I1Group))) CA1_5_10I1H = true by decide +kernel)
  simp only [stageACapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg]
  exact hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
