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
def CA4_4_8I1PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 4 4 8)) (shape 4 4 8) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) a
def CA4_4_8I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 4 4 8) A4_4_8Law 1 a
lemma CA4_4_8I1PairRaw_sound (a : PairSlot × PairSlot) :
    (CA4_4_8I1PairRaw a).Encloses (CA4_4_8I1PairValue a) := by
  exact stageAPairBall_sound (shape 4 4 8) (by decide +kernel) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (fun u _ => A4_4_8Law_sound u) 1 a
def CA4_4_8I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(314423290018372900986627649 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(6659799119036077092390487787 / 25000000000000000000000000000000), (9055127 / 100000000000000000000000000000000)⟩ ⟨(-1059049906679451244035407109899287 / 100000000000000000000000000000000), (179994521183 / 50000000000000000000000000000000)⟩ ⟨-16, 314423290018372900986627649, 190734863281250000000000000⟩,
   .log ⟨(64018459366040132597127547007 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(191013786064334317565099687427 / 12500000000000000000000000000000), (108451493 / 20000000000000000000000000000000)⟩ ⟨(-119349192689670621173759081237297 / 20000000000000000000000000000000), (211758238001 / 100000000000000000000000000000000)⟩ ⟨-9, 64018459366040132597127547007, 48828125000000000000000000000⟩,
   .log ⟨(1827992080296839459972808997061 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩ ⟨(7315536644731865385667081595021 / 100000000000000000000000000000000), (541929347 / 20000000000000000000000000000000)⟩ ⟨(-400195204540707206000113957516591 / 100000000000000000000000000000000), (148230766601 / 100000000000000000000000000000000)⟩ ⟨-6, 1827992080296839459972808997061, 1562500000000000000000000000000⟩,
   .log ⟨(129314048175672016811555022893 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(172005310539915519284643644567 / 20000000000000000000000000000000), (301216479 / 100000000000000000000000000000000)⟩ ⟨(-665068153717714379814276957392311 / 100000000000000000000000000000000), (232934062059 / 100000000000000000000000000000000)⟩ ⟨-10, 129314048175672016811555022893, 97656250000000000000000000000⟩,
   .log ⟨(4090207334626568283712673773 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1924684409518868914061399987 / 2500000000000000000000000000000), (406001 / 1562500000000000000000000000000)⟩ ⟨(-941118262257769198398609961793723 / 100000000000000000000000000000000), (317637367469 / 100000000000000000000000000000000)⟩ ⟨-14, 4090207334626568283712673773, 3051757812500000000000000000⟩,
   .log ⟨(81098031324791547309636513431 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1041966904825690353657890236951 / 100000000000000000000000000000000), (37780989 / 10000000000000000000000000000000)⟩ ⟨(-321205979912351652786817210073577 / 50000000000000000000000000000000), (116467030873 / 50000000000000000000000000000000)⟩ ⟨-10, 81098031324791547309636513431, 48828125000000000000000000000⟩,
   .log ⟨(5178381185616060007566540177167 / 100000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩ ⟨(15331517651686582559443927751529 / 100000000000000000000000000000000), (6579389337 / 100000000000000000000000000000000)⟩ ⟨(-74016942274705427265353197585151 / 25000000000000000000000000000000), (127054942677 / 100000000000000000000000000000000)⟩ ⟨-5, 5178381185616060007566540177167, 3125000000000000000000000000000⟩,
   .log ⟨(4467386521082530682319624261 / 1000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(2417281274549881012946303494831 / 100000000000000000000000000000000), (212851331 / 25000000000000000000000000000000)⟩ ⟨(-541095171224210276759554985805347 / 100000000000000000000000000000000), (95291206909 / 50000000000000000000000000000000)⟩ ⟨-8, 4467386521082530682319624261, 3906250000000000000000000000⟩,
   .log ⟨(688606063331092941255649109809 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩ ⟨(2950751990021937892152415086987 / 50000000000000000000000000000000), (2333088163 / 100000000000000000000000000000000)⟩ ⟨(-214255446412121452196666689159527 / 50000000000000000000000000000000), (21175823801 / 12500000000000000000000000000000)⟩ ⟨-7, 688606063331092941255649109809, 390625000000000000000000000000⟩,
   .log ⟨(25690597409828756485476917179 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(855158097339175378689003325641 / 100000000000000000000000000000000), (11968431 / 4000000000000000000000000000000)⟩ ⟨(-665736248711762074541608793931601 / 100000000000000000000000000000000), (232934062069 / 100000000000000000000000000000000)⟩ ⟨-10, 25690597409828756485476917179, 19531250000000000000000000000⟩,
   .log ⟨(645094128905276122471516286389 / 12500000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩ ⟨(15296924483840307384308119307967 / 100000000000000000000000000000000), (6556991919 / 100000000000000000000000000000000)⟩ ⟨(-296408768085503426043971095985503 / 100000000000000000000000000000000), (25410988559 / 20000000000000000000000000000000)⟩ ⟨-5, 645094128905276122471516286389, 390625000000000000000000000000⟩,
   .log ⟨(11743603988387563260835747113 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(106275114935926281010073224109 / 100000000000000000000000000000000), (9325521 / 25000000000000000000000000000000)⟩ ⟨(-904961671400145837811787937931693 / 100000000000000000000000000000000), (3970467047 / 1250000000000000000000000000000)⟩ ⟨-14, 11743603988387563260835747113, 6103515625000000000000000000⟩,
   .log ⟨(119982861643270677730165523631 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(2562489425544086214279198000591 / 100000000000000000000000000000000), (457332479 / 50000000000000000000000000000000)⟩ ⟨(-266964109545369934140924564386159 / 50000000000000000000000000000000), (9529120699 / 5000000000000000000000000000000)⟩ ⟨-8, 119982861643270677730165523631, 97656250000000000000000000000⟩,
   .log ⟨(773253199559204660666668449787 / 4000000000000000000000000000000), (47 / 50000000000000000000000000000000)⟩ ⟨(31769940705175036122458851321023 / 100000000000000000000000000000000), (8187136833 / 50000000000000000000000000000000)⟩ ⟨(-164344309073848449609447916900417 / 100000000000000000000000000000000), (42351647609 / 50000000000000000000000000000000)⟩ ⟨-3, 773253199559204660666668449787, 500000000000000000000000000000⟩]
lemma CA4_4_8I1PairCertificates_valid :
    CA4_4_8I1PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I1PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 0, 0, 5, 0 => 1
  | 0, 0, 4, 1 => 2
  | 0, 0, 2, 2 => 3
  | 0, 0, 2, 3 => 4
  | 0, 0, 3, 2 => 4
  | 0, 0, 3, 3 => 5
  | 0, 0, 1, 4 => 2
  | 0, 0, 0, 5 => 1
  | 1, 0, 4, 0 => 6
  | 1, 0, 2, 1 => 7
  | 1, 0, 3, 1 => 8
  | 1, 0, 1, 2 => 7
  | 1, 0, 1, 3 => 8
  | 1, 0, 0, 4 => 6
  | 0, 1, 4, 0 => 6
  | 0, 1, 2, 1 => 7
  | 0, 1, 3, 1 => 8
  | 0, 1, 1, 2 => 7
  | 0, 1, 1, 3 => 8
  | 0, 1, 0, 4 => 6
  | 2, 0, 2, 0 => 9
  | 2, 0, 3, 0 => 10
  | 2, 0, 1, 1 => 11
  | 2, 0, 0, 2 => 9
  | 2, 0, 0, 3 => 10
  | 3, 0, 2, 0 => 10
  | 3, 0, 3, 0 => 12
  | 3, 0, 1, 1 => 13
  | 3, 0, 0, 2 => 10
  | 3, 0, 0, 3 => 12
  | 1, 1, 2, 0 => 11
  | 1, 1, 3, 0 => 13
  | 1, 1, 1, 1 => 14
  | 1, 1, 0, 2 => 11
  | 1, 1, 0, 3 => 13
  | 0, 2, 2, 0 => 9
  | 0, 2, 3, 0 => 10
  | 0, 2, 1, 1 => 11
  | 0, 2, 0, 2 => 9
  | 0, 2, 0, 3 => 10
  | 0, 3, 2, 0 => 10
  | 0, 3, 3, 0 => 12
  | 0, 3, 1, 1 => 13
  | 0, 3, 0, 2 => 10
  | 0, 3, 0, 3 => 12
  | 4, 0, 1, 0 => 6
  | 4, 0, 0, 1 => 6
  | 2, 1, 1, 0 => 7
  | 2, 1, 0, 1 => 7
  | 3, 1, 1, 0 => 8
  | 3, 1, 0, 1 => 8
  | 1, 2, 1, 0 => 7
  | 1, 2, 0, 1 => 7
  | 1, 3, 1, 0 => 8
  | 1, 3, 0, 1 => 8
  | 0, 4, 1, 0 => 6
  | 0, 4, 0, 1 => 6
  | 0, 5, 0, 0 => 1
  | 1, 4, 0, 0 => 2
  | 2, 2, 0, 0 => 3
  | 2, 3, 0, 0 => 4
  | 3, 2, 0, 0 => 4
  | 3, 3, 0, 0 => 5
  | 4, 1, 0, 0 => 2
  | 5, 0, 0, 0 => 1
  | _, _, _, _ => 0
def CA4_4_8I1PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1PairCertificates (CA4_4_8I1PairCertificateIndex a)).input
lemma CA4_4_8I1PairP_check_0_0 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((0,0),(k,l))) (CA4_4_8I1PairP ((0,0),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_0_1 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((0,1),(k,l))) (CA4_4_8I1PairP ((0,1),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_0_2 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((0,2),(k,l))) (CA4_4_8I1PairP ((0,2),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_0_3 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((0,3),(k,l))) (CA4_4_8I1PairP ((0,3),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_0_4 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((0,4),(k,l))) (CA4_4_8I1PairP ((0,4),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_0_5 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((0,5),(k,l))) (CA4_4_8I1PairP ((0,5),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_1_0 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((1,0),(k,l))) (CA4_4_8I1PairP ((1,0),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_1_1 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((1,1),(k,l))) (CA4_4_8I1PairP ((1,1),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_1_2 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((1,2),(k,l))) (CA4_4_8I1PairP ((1,2),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_1_3 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((1,3),(k,l))) (CA4_4_8I1PairP ((1,3),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_1_4 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((1,4),(k,l))) (CA4_4_8I1PairP ((1,4),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_1_5 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((1,5),(k,l))) (CA4_4_8I1PairP ((1,5),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_2_0 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((2,0),(k,l))) (CA4_4_8I1PairP ((2,0),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_2_1 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((2,1),(k,l))) (CA4_4_8I1PairP ((2,1),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_2_2 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((2,2),(k,l))) (CA4_4_8I1PairP ((2,2),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_2_3 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((2,3),(k,l))) (CA4_4_8I1PairP ((2,3),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_2_4 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((2,4),(k,l))) (CA4_4_8I1PairP ((2,4),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_2_5 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((2,5),(k,l))) (CA4_4_8I1PairP ((2,5),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_3_0 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((3,0),(k,l))) (CA4_4_8I1PairP ((3,0),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_3_1 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((3,1),(k,l))) (CA4_4_8I1PairP ((3,1),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_3_2 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((3,2),(k,l))) (CA4_4_8I1PairP ((3,2),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_3_3 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((3,3),(k,l))) (CA4_4_8I1PairP ((3,3),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_3_4 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((3,4),(k,l))) (CA4_4_8I1PairP ((3,4),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_3_5 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((3,5),(k,l))) (CA4_4_8I1PairP ((3,5),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_4_0 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((4,0),(k,l))) (CA4_4_8I1PairP ((4,0),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_4_1 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((4,1),(k,l))) (CA4_4_8I1PairP ((4,1),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_4_2 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((4,2),(k,l))) (CA4_4_8I1PairP ((4,2),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_4_3 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((4,3),(k,l))) (CA4_4_8I1PairP ((4,3),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_4_4 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((4,4),(k,l))) (CA4_4_8I1PairP ((4,4),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_4_5 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((4,5),(k,l))) (CA4_4_8I1PairP ((4,5),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_5_0 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((5,0),(k,l))) (CA4_4_8I1PairP ((5,0),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_5_1 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((5,1),(k,l))) (CA4_4_8I1PairP ((5,1),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_5_2 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((5,2),(k,l))) (CA4_4_8I1PairP ((5,2),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_5_3 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((5,3),(k,l))) (CA4_4_8I1PairP ((5,3),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_5_4 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((5,4),(k,l))) (CA4_4_8I1PairP ((5,4),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_5_5 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((5,5),(k,l))) (CA4_4_8I1PairP ((5,5),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check (a : PairSlot × PairSlot) : contains (CA4_4_8I1PairRaw a) (CA4_4_8I1PairP a) = true := by
  rcases a with ⟨⟨i,j⟩,⟨k,l⟩⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (CA4_4_8I1PairP_check_0_0 k l) (CA4_4_8I1PairP_check_0_1 k l) (CA4_4_8I1PairP_check_0_2 k l) (CA4_4_8I1PairP_check_0_3 k l) (CA4_4_8I1PairP_check_0_4 k l) (CA4_4_8I1PairP_check_0_5 k l)
  · exact forall_fin6 (CA4_4_8I1PairP_check_1_0 k l) (CA4_4_8I1PairP_check_1_1 k l) (CA4_4_8I1PairP_check_1_2 k l) (CA4_4_8I1PairP_check_1_3 k l) (CA4_4_8I1PairP_check_1_4 k l) (CA4_4_8I1PairP_check_1_5 k l)
  · exact forall_fin6 (CA4_4_8I1PairP_check_2_0 k l) (CA4_4_8I1PairP_check_2_1 k l) (CA4_4_8I1PairP_check_2_2 k l) (CA4_4_8I1PairP_check_2_3 k l) (CA4_4_8I1PairP_check_2_4 k l) (CA4_4_8I1PairP_check_2_5 k l)
  · exact forall_fin6 (CA4_4_8I1PairP_check_3_0 k l) (CA4_4_8I1PairP_check_3_1 k l) (CA4_4_8I1PairP_check_3_2 k l) (CA4_4_8I1PairP_check_3_3 k l) (CA4_4_8I1PairP_check_3_4 k l) (CA4_4_8I1PairP_check_3_5 k l)
  · exact forall_fin6 (CA4_4_8I1PairP_check_4_0 k l) (CA4_4_8I1PairP_check_4_1 k l) (CA4_4_8I1PairP_check_4_2 k l) (CA4_4_8I1PairP_check_4_3 k l) (CA4_4_8I1PairP_check_4_4 k l) (CA4_4_8I1PairP_check_4_5 k l)
  · exact forall_fin6 (CA4_4_8I1PairP_check_5_0 k l) (CA4_4_8I1PairP_check_5_1 k l) (CA4_4_8I1PairP_check_5_2 k l) (CA4_4_8I1PairP_check_5_3 k l) (CA4_4_8I1PairP_check_5_4 k l) (CA4_4_8I1PairP_check_5_5 k l)
lemma CA4_4_8I1PairP_sound (a : PairSlot × PairSlot) :
    (CA4_4_8I1PairP a).Encloses (CA4_4_8I1PairValue a) :=
  contains_sound (CA4_4_8I1PairRaw_sound a) (CA4_4_8I1PairP_check a)
def CA4_4_8I1PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1PairCertificates (CA4_4_8I1PairCertificateIndex a)).output
lemma CA4_4_8I1PairTerms_sound (a : PairSlot × PairSlot) :
    (CA4_4_8I1PairTerms a).Encloses (Foundation.entropyTerm (CA4_4_8I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I1PairCertificates_valid
    (CA4_4_8I1PairCertificateIndex a) (CA4_4_8I1PairP_sound a)
def CA4_4_8I1PairEntropy : Ball := ⟨(308850256342829279281678118501801 / 100000000000000000000000000000000), (32371590663 / 25000000000000000000000000000000)⟩
lemma CA4_4_8I1PairEntropy_sound : CA4_4_8I1PairEntropy.Encloses (Foundation.finiteEntropy CA4_4_8I1PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA4_4_8I1PairValue CA4_4_8I1PairTerms CA4_4_8I1PairTerms_sound) (by decide +kernel)
def CA4_4_8I1PairMass : Ball := ⟨(100000000000000000000000000000001 / 100000000000000000000000000000000), (331 / 50000000000000000000000000000000)⟩
lemma CA4_4_8I1PairMass_sound : CA4_4_8I1PairMass.Encloses (∑ a, CA4_4_8I1PairValue a) := by
  exact contains_sound (doublePairSumBall_sound CA4_4_8I1PairP CA4_4_8I1PairValue CA4_4_8I1PairP_sound) (by decide +kernel)
def CA4_4_8I1PairMassTermLogWitness : LogWitness := ⟨0, 100000000000000000000000000000001, 100000000000000000000000000000000⟩
def CA4_4_8I1PairMassTermLog : Ball := ⟨(1 / 100000000000000000000000000000000), (2646978043 / 12500000000000000000000000000000)⟩
lemma CA4_4_8I1PairMassTermLog_sound : CA4_4_8I1PairMassTermLog.Encloses (Real.log ((∑ a, CA4_4_8I1PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_4_8I1PairMass_sound) (w := CA4_4_8I1PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_4_8I1PairMassTerm : Ball := ⟨(-1 / 100000000000000000000000000000000), (4235164869 / 20000000000000000000000000000000)⟩
lemma CA4_4_8I1PairMassTerm_sound : CA4_4_8I1PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I1PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA4_4_8I1PairMass_sound) CA4_4_8I1PairMassTermLog_sound) (by decide +kernel)
def CA4_4_8I1PairH : Ball := ⟨(154425128171414639640839059250901 / 50000000000000000000000000000000), (150662186997 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I1PairH_sound : CA4_4_8I1PairH.Encloses (homogeneousEntropy CA4_4_8I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I1PairValue CA4_4_8I1PairMassTerm_sound CA4_4_8I1PairEntropy_sound) (by decide +kernel)

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
def CA4_4_8I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA4_4_8I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
lemma CA4_4_8I1R0Raw_sound (a : PairSlot) :
    (CA4_4_8I1R0Raw a).Encloses (CA4_4_8I1R0Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 0 a
def CA4_4_8I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(10203043120648639286547464097 / 390625000000000000000000000000), (9 / 50000000000000000000000000000000)⟩ ⟨(4760412769112588948014764417159 / 50000000000000000000000000000000), (483969577 / 12500000000000000000000000000000)⟩ ⟨(-91126549988371926878531538134997 / 25000000000000000000000000000000), (14823076647 / 10000000000000000000000000000000)⟩ ⟨-6, 10203043120648639286547464097, 6103515625000000000000000000⟩]
lemma CA4_4_8I1R0Certificates_valid :
    CA4_4_8I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA4_4_8I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R0Certificates (CA4_4_8I1R0CertificateIndex a)).input
lemma CA4_4_8I1R0P_check : ∀ a : PairSlot, contains (CA4_4_8I1R0Raw a) (CA4_4_8I1R0P a) = true := by
  decide +kernel
lemma CA4_4_8I1R0P_sound (a : PairSlot) :
    (CA4_4_8I1R0P a).Encloses (CA4_4_8I1R0Value a) :=
  contains_sound (CA4_4_8I1R0Raw_sound a) (CA4_4_8I1R0P_check a)
def CA4_4_8I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R0Certificates (CA4_4_8I1R0CertificateIndex a)).output
lemma CA4_4_8I1R0Terms_sound (a : PairSlot) :
    (CA4_4_8I1R0Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I1R0Certificates_valid
    (CA4_4_8I1R0CertificateIndex a) (CA4_4_8I1R0P_sound a)
def CA4_4_8I1R0Entropy : Ball := ⟨(4760412769112588948014764417159 / 50000000000000000000000000000000), (483969577 / 12500000000000000000000000000000)⟩
lemma CA4_4_8I1R0Entropy_sound : CA4_4_8I1R0Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I1R0Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I1R0Value CA4_4_8I1R0Terms CA4_4_8I1R0Terms_sound) (by decide +kernel)
def CA4_4_8I1R0Mass : Ball := ⟨(10203043120648639286547464097 / 390625000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
lemma CA4_4_8I1R0Mass_sound : CA4_4_8I1R0Mass.Encloses (∑ a, CA4_4_8I1R0Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I1R0P CA4_4_8I1R0Value CA4_4_8I1R0P_sound) (by decide +kernel)
def CA4_4_8I1R0MassTermLogWitness : LogWitness := ⟨-6, 10203043120648639286547464097, 6103515625000000000000000000⟩
def CA4_4_8I1R0MassTermLog : Ball := ⟨(-91126549988371926878531538134997 / 25000000000000000000000000000000), (14823076647 / 10000000000000000000000000000000)⟩
lemma CA4_4_8I1R0MassTermLog_sound : CA4_4_8I1R0MassTermLog.Encloses (Real.log ((∑ a, CA4_4_8I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_4_8I1R0Mass_sound) (w := CA4_4_8I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_4_8I1R0MassTerm : Ball := ⟨(4760412769112588948014764417159 / 50000000000000000000000000000000), (483969577 / 12500000000000000000000000000000)⟩
lemma CA4_4_8I1R0MassTerm_sound : CA4_4_8I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_4_8I1R0Mass_sound) CA4_4_8I1R0MassTermLog_sound) (by decide +kernel)
def CA4_4_8I1R0H : Ball := ⟨0, (483969577 / 6250000000000000000000000000000)⟩
lemma CA4_4_8I1R0H_sound : CA4_4_8I1R0H.Encloses (homogeneousEntropy CA4_4_8I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I1R0Value CA4_4_8I1R0MassTerm_sound CA4_4_8I1R0Entropy_sound) (by decide +kernel)
def CA4_4_8I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA4_4_8I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
lemma CA4_4_8I1R1Raw_sound (a : PairSlot) :
    (CA4_4_8I1R1Raw a).Encloses (CA4_4_8I1R1Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 1 a
def CA4_4_8I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(11574631800747792340835551260257 / 100000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩ ⟨(4991801634033016332264529747017 / 20000000000000000000000000000000), (6127559147 / 50000000000000000000000000000000)⟩ ⟨(-215635439639233935368668825372491 / 100000000000000000000000000000000), (26469779729 / 25000000000000000000000000000000)⟩ ⟨-4, 11574631800747792340835551260257, 6250000000000000000000000000000⟩]
lemma CA4_4_8I1R1Certificates_valid :
    CA4_4_8I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA4_4_8I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R1Certificates (CA4_4_8I1R1CertificateIndex a)).input
lemma CA4_4_8I1R1P_check : ∀ a : PairSlot, contains (CA4_4_8I1R1Raw a) (CA4_4_8I1R1P a) = true := by
  decide +kernel
lemma CA4_4_8I1R1P_sound (a : PairSlot) :
    (CA4_4_8I1R1P a).Encloses (CA4_4_8I1R1Value a) :=
  contains_sound (CA4_4_8I1R1Raw_sound a) (CA4_4_8I1R1P_check a)
def CA4_4_8I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R1Certificates (CA4_4_8I1R1CertificateIndex a)).output
lemma CA4_4_8I1R1Terms_sound (a : PairSlot) :
    (CA4_4_8I1R1Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I1R1Certificates_valid
    (CA4_4_8I1R1CertificateIndex a) (CA4_4_8I1R1P_sound a)
def CA4_4_8I1R1Entropy : Ball := ⟨(4991801634033016332264529747017 / 10000000000000000000000000000000), (6127559147 / 25000000000000000000000000000000)⟩
lemma CA4_4_8I1R1Entropy_sound : CA4_4_8I1R1Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I1R1Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I1R1Value CA4_4_8I1R1Terms CA4_4_8I1R1Terms_sound) (by decide +kernel)
def CA4_4_8I1R1Mass : Ball := ⟨(11574631800747792340835551260257 / 50000000000000000000000000000000), (29 / 25000000000000000000000000000000)⟩
lemma CA4_4_8I1R1Mass_sound : CA4_4_8I1R1Mass.Encloses (∑ a, CA4_4_8I1R1Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I1R1P CA4_4_8I1R1Value CA4_4_8I1R1P_sound) (by decide +kernel)
def CA4_4_8I1R1MassTermLogWitness : LogWitness := ⟨-3, 11574631800747792340835551260257, 6250000000000000000000000000000⟩
def CA4_4_8I1R1MassTermLog : Ball := ⟨(-146320721583239404426945632322161 / 100000000000000000000000000000000), (84703295233 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I1R1MassTermLog_sound : CA4_4_8I1R1MassTermLog.Encloses (Real.log ((∑ a, CA4_4_8I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_4_8I1R1Mass_sound) (w := CA4_4_8I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_4_8I1R1MassTerm : Ball := ⟨(4234021192864316680996658137711 / 12500000000000000000000000000000), (19608189263 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I1R1MassTerm_sound : CA4_4_8I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_4_8I1R1Mass_sound) CA4_4_8I1R1MassTermLog_sound) (by decide +kernel)
def CA4_4_8I1R1H : Ball := ⟨(8022923398707814937336016184241 / 50000000000000000000000000000000), (44118425851 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I1R1H_sound : CA4_4_8I1R1H.Encloses (homogeneousEntropy CA4_4_8I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I1R1Value CA4_4_8I1R1MassTerm_sound CA4_4_8I1R1Entropy_sound) (by decide +kernel)
def CA4_4_8I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA4_4_8I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
lemma CA4_4_8I1R2Raw_sound (a : PairSlot) :
    (CA4_4_8I1R2Raw a).Encloses (CA4_4_8I1R2Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 2 a
def CA4_4_8I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(8172083258664868309649495902139 / 100000000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩ ⟨(20466543850431517495393125747353 / 100000000000000000000000000000000), (8652529879 / 100000000000000000000000000000000)⟩ ⟨(-250444632079963452857361644712163 / 100000000000000000000000000000000), (52939559501 / 50000000000000000000000000000000)⟩ ⟨-4, 8172083258664868309649495902139, 6250000000000000000000000000000⟩,
   .log ⟨(760324628648145402297102760541 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(1854880353174384488552949121649 / 50000000000000000000000000000000), (1449045061 / 100000000000000000000000000000000)⟩ ⟨(-97583599598626993472407258008041 / 20000000000000000000000000000000), (11911400871 / 6250000000000000000000000000000)⟩ ⟨-8, 760324628648145402297102760541, 390625000000000000000000000000⟩,
   .log ⟨(15306349472305349949026148007973 / 50000000000000000000000000000000), (113 / 100000000000000000000000000000000)⟩ ⟨(9059485887333126540248566425779 / 25000000000000000000000000000000), (9723736853 / 50000000000000000000000000000000)⟩ ⟨(-29593881623194904978274358505653 / 25000000000000000000000000000000), (63527471417 / 100000000000000000000000000000000)⟩ ⟨-2, 15306349472305349949026148007973, 12500000000000000000000000000000⟩]
lemma CA4_4_8I1R2Certificates_valid :
    CA4_4_8I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA4_4_8I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R2Certificates (CA4_4_8I1R2CertificateIndex a)).input
lemma CA4_4_8I1R2P_check : ∀ a : PairSlot, contains (CA4_4_8I1R2Raw a) (CA4_4_8I1R2P a) = true := by
  decide +kernel
lemma CA4_4_8I1R2P_sound (a : PairSlot) :
    (CA4_4_8I1R2P a).Encloses (CA4_4_8I1R2Value a) :=
  contains_sound (CA4_4_8I1R2Raw_sound a) (CA4_4_8I1R2P_check a)
def CA4_4_8I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R2Certificates (CA4_4_8I1R2CertificateIndex a)).output
lemma CA4_4_8I1R2Terms_sound (a : PairSlot) :
    (CA4_4_8I1R2Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I1R2Certificates_valid
    (CA4_4_8I1R2CertificateIndex a) (CA4_4_8I1R2P_sound a)
def CA4_4_8I1R2Entropy : Ball := ⟨(42295276331446539552996156842209 / 50000000000000000000000000000000), (19825311793 / 50000000000000000000000000000000)⟩
lemma CA4_4_8I1R2Entropy_sound : CA4_4_8I1R2Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I1R2Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I1R2Value CA4_4_8I1R2Terms CA4_4_8I1R2Terms_sound) (by decide +kernel)
def CA4_4_8I1R2Mass : Ball := ⟨(24238757359618363660972746670653 / 50000000000000000000000000000000), (221 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I1R2Mass_sound : CA4_4_8I1R2Mass.Encloses (∑ a, CA4_4_8I1R2Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I1R2P CA4_4_8I1R2Value CA4_4_8I1R2P_sound) (by decide +kernel)
def CA4_4_8I1R2MassTermLogWitness : LogWitness := ⟨-2, 24238757359618363660972746670653, 12500000000000000000000000000000⟩
def CA4_4_8I1R2MassTermLog : Ball := ⟨(-7240701095832249874519106100029 / 10000000000000000000000000000000), (3970466969 / 6250000000000000000000000000000)⟩
lemma CA4_4_8I1R2MassTermLog_sound : CA4_4_8I1R2MassTermLog.Encloses (Real.log ((∑ a, CA4_4_8I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_4_8I1R2Mass_sound) (w := CA4_4_8I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_4_8I1R2MassTerm : Ball := ⟨(35101119395080139462631003646157 / 100000000000000000000000000000000), (3079653951 / 10000000000000000000000000000000)⟩
lemma CA4_4_8I1R2MassTerm_sound : CA4_4_8I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_4_8I1R2Mass_sound) CA4_4_8I1R2MassTermLog_sound) (by decide +kernel)
def CA4_4_8I1R2H : Ball := ⟨(49489433267812939643361310038261 / 100000000000000000000000000000000), (8805895387 / 12500000000000000000000000000000)⟩
lemma CA4_4_8I1R2H_sound : CA4_4_8I1R2H.Encloses (homogeneousEntropy CA4_4_8I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I1R2Value CA4_4_8I1R2MassTerm_sound CA4_4_8I1R2Entropy_sound) (by decide +kernel)
def CA4_4_8I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA4_4_8I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
lemma CA4_4_8I1R3Raw_sound (a : PairSlot) :
    (CA4_4_8I1R3Raw a).Encloses (CA4_4_8I1R3Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 3 a
def CA4_4_8I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(324392125299166189238546053723 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(1859082322604415157920580847503 / 100000000000000000000000000000000), (686927073 / 100000000000000000000000000000000)⟩ ⟨(-143274310442177193657977806774283 / 25000000000000000000000000000000), (105879119031 / 50000000000000000000000000000000)⟩ ⟨-9, 324392125299166189238546053723, 195312500000000000000000000000⟩,
   .log ⟨(5178381185616060007566540177167 / 50000000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩ ⟨(23484274666024287494456489420227 / 100000000000000000000000000000000), (2193129773 / 20000000000000000000000000000000)⟩ ⟨(-113376525521413589059844798645137 / 50000000000000000000000000000000), (105879118917 / 100000000000000000000000000000000)⟩ ⟨-4, 5178381185616060007566540177167, 3125000000000000000000000000000⟩,
   .log ⟨(4467386521082530682319624261 / 500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(843050254957558052476631302929 / 20000000000000000000000000000000), (756804729 / 50000000000000000000000000000000)⟩ ⟨(-471780453168215745817831792755017 / 100000000000000000000000000000000), (169406590023 / 100000000000000000000000000000000)⟩ ⟨-7, 4467386521082530682319624261, 3906250000000000000000000000⟩]
lemma CA4_4_8I1R3Certificates_valid :
    CA4_4_8I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA4_4_8I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R3Certificates (CA4_4_8I1R3CertificateIndex a)).input
lemma CA4_4_8I1R3P_check : ∀ a : PairSlot, contains (CA4_4_8I1R3Raw a) (CA4_4_8I1R3P a) = true := by
  decide +kernel
lemma CA4_4_8I1R3P_sound (a : PairSlot) :
    (CA4_4_8I1R3P a).Encloses (CA4_4_8I1R3Value a) :=
  contains_sound (CA4_4_8I1R3Raw_sound a) (CA4_4_8I1R3P_check a)
def CA4_4_8I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R3Certificates (CA4_4_8I1R3CertificateIndex a)).output
lemma CA4_4_8I1R3Terms_sound (a : PairSlot) :
    (CA4_4_8I1R3Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I1R3Certificates_valid
    (CA4_4_8I1R3CertificateIndex a) (CA4_4_8I1R3P_sound a)
def CA4_4_8I1R3Entropy : Ball := ⟨(236468866107331943318081814259 / 400000000000000000000000000000), (3291546349 / 12500000000000000000000000000000)⟩
lemma CA4_4_8I1R3Entropy_sound : CA4_4_8I1R3Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I1R3Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I1R3Value CA4_4_8I1R3Terms CA4_4_8I1R3Terms_sound) (by decide +kernel)
def CA4_4_8I1R3Mass : Ball := ⟨(11574631800747792340835551260257 / 50000000000000000000000000000000), (61 / 50000000000000000000000000000000)⟩
lemma CA4_4_8I1R3Mass_sound : CA4_4_8I1R3Mass.Encloses (∑ a, CA4_4_8I1R3Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I1R3P CA4_4_8I1R3Value CA4_4_8I1R3P_sound) (by decide +kernel)
def CA4_4_8I1R3MassTermLogWitness : LogWitness := ⟨-3, 11574631800747792340835551260257, 6250000000000000000000000000000⟩
def CA4_4_8I1R3MassTermLog : Ball := ⟨(-146320721583239404426945632322161 / 100000000000000000000000000000000), (84703295259 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I1R3MassTermLog_sound : CA4_4_8I1R3MassTermLog.Encloses (Real.log ((∑ a, CA4_4_8I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_4_8I1R3Mass_sound) (w := CA4_4_8I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_4_8I1R3MassTerm : Ball := ⟨(4234021192864316680996658137711 / 12500000000000000000000000000000), (9804094639 / 50000000000000000000000000000000)⟩
lemma CA4_4_8I1R3MassTerm_sound : CA4_4_8I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I1R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_4_8I1R3Mass_sound) CA4_4_8I1R3MassTermLog_sound) (by decide +kernel)
def CA4_4_8I1R3H : Ball := ⟨(12622523491959226190773594231531 / 50000000000000000000000000000000), (4594056007 / 10000000000000000000000000000000)⟩
lemma CA4_4_8I1R3H_sound : CA4_4_8I1R3H.Encloses (homogeneousEntropy CA4_4_8I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I1R3Value CA4_4_8I1R3MassTerm_sound CA4_4_8I1R3Entropy_sound) (by decide +kernel)
def CA4_4_8I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA4_4_8I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
lemma CA4_4_8I1R4Raw_sound (a : PairSlot) :
    (CA4_4_8I1R4Raw a).Encloses (CA4_4_8I1R4Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 4 a
def CA4_4_8I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(314421671024778164888076367 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(2663907226045848723925104267 / 10000000000000000000000000000000), (226377 / 2500000000000000000000000000000)⟩ ⟨(-1059050421589705769739076007325759 / 100000000000000000000000000000000), (179994521183 / 50000000000000000000000000000000)⟩ ⟨-16, 314421671024778164888076367, 190734863281250000000000000⟩,
   .log ⟨(25607305640862147463658339143 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1528106408651620834127544871883 / 100000000000000000000000000000000), (542255811 / 100000000000000000000000000000000)⟩ ⟨(-596746268460664378568900799927563 / 100000000000000000000000000000000), (211758238001 / 100000000000000000000000000000000)⟩ ⟨-9, 25607305640862147463658339143, 19531250000000000000000000000⟩,
   .log ⟨(1827988448269525491278423848813 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩ ⟨(7315525741556433013150138476611 / 100000000000000000000000000000000), (2709641351 / 100000000000000000000000000000000)⟩ ⟨(-200097701615174659640952779378689 / 50000000000000000000000000000000), (148230766601 / 100000000000000000000000000000000)⟩ ⟨-6, 1827988448269525491278423848813, 1562500000000000000000000000000⟩,
   .log ⟨(129313644566804189993550425661 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(860024272033770063379074775041 / 100000000000000000000000000000000), (301215539 / 100000000000000000000000000000000)⟩ ⟨(-332534232916726920443613076237221 / 50000000000000000000000000000000), (232934062059 / 100000000000000000000000000000000)⟩ ⟨-10, 129313644566804189993550425661, 97656250000000000000000000000⟩,
   .log ⟨(8180370728321901785755684313 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(38493503392719760282224224857 / 50000000000000000000000000000000), (6495981 / 25000000000000000000000000000000)⟩ ⟨(-941118799407180636802482562160497 / 100000000000000000000000000000000), (317637367469 / 100000000000000000000000000000000)⟩ ⟨-14, 8180370728321901785755684313, 6103515625000000000000000000⟩]
lemma CA4_4_8I1R4Certificates_valid :
    CA4_4_8I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I1R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA4_4_8I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R4Certificates (CA4_4_8I1R4CertificateIndex a)).input
lemma CA4_4_8I1R4P_check : ∀ a : PairSlot, contains (CA4_4_8I1R4Raw a) (CA4_4_8I1R4P a) = true := by
  decide +kernel
lemma CA4_4_8I1R4P_sound (a : PairSlot) :
    (CA4_4_8I1R4P a).Encloses (CA4_4_8I1R4Value a) :=
  contains_sound (CA4_4_8I1R4Raw_sound a) (CA4_4_8I1R4P_check a)
def CA4_4_8I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R4Certificates (CA4_4_8I1R4CertificateIndex a)).output
lemma CA4_4_8I1R4Terms_sound (a : PairSlot) :
    (CA4_4_8I1R4Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I1R4Certificates_valid
    (CA4_4_8I1R4CertificateIndex a) (CA4_4_8I1R4P_sound a)
def CA4_4_8I1R4Entropy : Ball := ⟨(12222052254233571303206328305513 / 100000000000000000000000000000000), (888135627 / 20000000000000000000000000000000)⟩
lemma CA4_4_8I1R4Entropy_sound : CA4_4_8I1R4Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I1R4Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I1R4Value CA4_4_8I1R4Terms CA4_4_8I1R4Terms_sound) (by decide +kernel)
def CA4_4_8I1R4Mass : Ball := ⟨(130598648384254758648132819459 / 5000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
lemma CA4_4_8I1R4Mass_sound : CA4_4_8I1R4Mass.Encloses (∑ a, CA4_4_8I1R4Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I1R4P CA4_4_8I1R4Value CA4_4_8I1R4P_sound) (by decide +kernel)
def CA4_4_8I1R4MassTermLogWitness : LogWitness := ⟨-6, 130598648384254758648132819459, 78125000000000000000000000000⟩
def CA4_4_8I1R4MassTermLog : Ball := ⟨(-91126608097643880853565541221611 / 25000000000000000000000000000000), (148230766853 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I1R4MassTermLog_sound : CA4_4_8I1R4MassTermLog.Encloses (Real.log ((∑ a, CA4_4_8I1R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_4_8I1R4Mass_sound) (w := CA4_4_8I1R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_4_8I1R4MassTerm : Ball := ⟨(148762648117424695324148511307 / 1562500000000000000000000000000), (3871747663 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I1R4MassTerm_sound : CA4_4_8I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I1R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_4_8I1R4Mass_sound) CA4_4_8I1R4MassTermLog_sound) (by decide +kernel)
def CA4_4_8I1R4H : Ball := ⟨(540248554943678160492164716373 / 20000000000000000000000000000000), (4156212899 / 50000000000000000000000000000000)⟩
lemma CA4_4_8I1R4H_sound : CA4_4_8I1R4H.Encloses (homogeneousEntropy CA4_4_8I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I1R4Value CA4_4_8I1R4MassTerm_sound CA4_4_8I1R4Entropy_sound) (by decide +kernel)
def CA4_4_8I1R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 5 a
def CA4_4_8I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
lemma CA4_4_8I1R5Raw_sound (a : PairSlot) :
    (CA4_4_8I1R5Raw a).Encloses (CA4_4_8I1R5Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 5 a
def CA4_4_8I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_4_8I1R5Certificates_valid :
    CA4_4_8I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_4_8I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R5Certificates (CA4_4_8I1R5CertificateIndex a)).input
lemma CA4_4_8I1R5P_check : ∀ a : PairSlot, contains (CA4_4_8I1R5Raw a) (CA4_4_8I1R5P a) = true := by
  decide +kernel
lemma CA4_4_8I1R5P_sound (a : PairSlot) :
    (CA4_4_8I1R5P a).Encloses (CA4_4_8I1R5Value a) :=
  contains_sound (CA4_4_8I1R5Raw_sound a) (CA4_4_8I1R5P_check a)
def CA4_4_8I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R5Certificates (CA4_4_8I1R5CertificateIndex a)).output
lemma CA4_4_8I1R5Terms_sound (a : PairSlot) :
    (CA4_4_8I1R5Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I1R5Certificates_valid
    (CA4_4_8I1R5CertificateIndex a) (CA4_4_8I1R5P_sound a)
def CA4_4_8I1R5Entropy : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R5Entropy_sound : CA4_4_8I1R5Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I1R5Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I1R5Value CA4_4_8I1R5Terms CA4_4_8I1R5Terms_sound) (by decide +kernel)
def CA4_4_8I1R5Mass : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R5Mass_sound : CA4_4_8I1R5Mass.Encloses (∑ a, CA4_4_8I1R5Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I1R5P CA4_4_8I1R5Value CA4_4_8I1R5P_sound) (by decide +kernel)
def CA4_4_8I1R5MassTerm : Ball := .exact 0
lemma CA4_4_8I1R5MassTerm_sound : CA4_4_8I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I1R5Value a))) :=
  entropyTerm_zero_ball (CA4_4_8I1R5Mass_sound)
def CA4_4_8I1R5H : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R5H_sound : CA4_4_8I1R5H.Encloses (homogeneousEntropy CA4_4_8I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I1R5Value CA4_4_8I1R5MassTerm_sound CA4_4_8I1R5Entropy_sound) (by decide +kernel)
def CA4_4_8I1R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 6 a
def CA4_4_8I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
lemma CA4_4_8I1R6Raw_sound (a : PairSlot) :
    (CA4_4_8I1R6Raw a).Encloses (CA4_4_8I1R6Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 6 a
def CA4_4_8I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_4_8I1R6Certificates_valid :
    CA4_4_8I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I1R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_4_8I1R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R6Certificates (CA4_4_8I1R6CertificateIndex a)).input
lemma CA4_4_8I1R6P_check : ∀ a : PairSlot, contains (CA4_4_8I1R6Raw a) (CA4_4_8I1R6P a) = true := by
  decide +kernel
lemma CA4_4_8I1R6P_sound (a : PairSlot) :
    (CA4_4_8I1R6P a).Encloses (CA4_4_8I1R6Value a) :=
  contains_sound (CA4_4_8I1R6Raw_sound a) (CA4_4_8I1R6P_check a)
def CA4_4_8I1R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R6Certificates (CA4_4_8I1R6CertificateIndex a)).output
lemma CA4_4_8I1R6Terms_sound (a : PairSlot) :
    (CA4_4_8I1R6Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I1R6Certificates_valid
    (CA4_4_8I1R6CertificateIndex a) (CA4_4_8I1R6P_sound a)
def CA4_4_8I1R6Entropy : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R6Entropy_sound : CA4_4_8I1R6Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I1R6Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I1R6Value CA4_4_8I1R6Terms CA4_4_8I1R6Terms_sound) (by decide +kernel)
def CA4_4_8I1R6Mass : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R6Mass_sound : CA4_4_8I1R6Mass.Encloses (∑ a, CA4_4_8I1R6Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I1R6P CA4_4_8I1R6Value CA4_4_8I1R6P_sound) (by decide +kernel)
def CA4_4_8I1R6MassTerm : Ball := .exact 0
lemma CA4_4_8I1R6MassTerm_sound : CA4_4_8I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I1R6Value a))) :=
  entropyTerm_zero_ball (CA4_4_8I1R6Mass_sound)
def CA4_4_8I1R6H : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R6H_sound : CA4_4_8I1R6H.Encloses (homogeneousEntropy CA4_4_8I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I1R6Value CA4_4_8I1R6MassTerm_sound CA4_4_8I1R6Entropy_sound) (by decide +kernel)
def CA4_4_8I1R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 7 a
def CA4_4_8I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
lemma CA4_4_8I1R7Raw_sound (a : PairSlot) :
    (CA4_4_8I1R7Raw a).Encloses (CA4_4_8I1R7Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 7 a
def CA4_4_8I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_4_8I1R7Certificates_valid :
    CA4_4_8I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I1R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_4_8I1R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R7Certificates (CA4_4_8I1R7CertificateIndex a)).input
lemma CA4_4_8I1R7P_check : ∀ a : PairSlot, contains (CA4_4_8I1R7Raw a) (CA4_4_8I1R7P a) = true := by
  decide +kernel
lemma CA4_4_8I1R7P_sound (a : PairSlot) :
    (CA4_4_8I1R7P a).Encloses (CA4_4_8I1R7Value a) :=
  contains_sound (CA4_4_8I1R7Raw_sound a) (CA4_4_8I1R7P_check a)
def CA4_4_8I1R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R7Certificates (CA4_4_8I1R7CertificateIndex a)).output
lemma CA4_4_8I1R7Terms_sound (a : PairSlot) :
    (CA4_4_8I1R7Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I1R7Certificates_valid
    (CA4_4_8I1R7CertificateIndex a) (CA4_4_8I1R7P_sound a)
def CA4_4_8I1R7Entropy : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R7Entropy_sound : CA4_4_8I1R7Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I1R7Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I1R7Value CA4_4_8I1R7Terms CA4_4_8I1R7Terms_sound) (by decide +kernel)
def CA4_4_8I1R7Mass : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R7Mass_sound : CA4_4_8I1R7Mass.Encloses (∑ a, CA4_4_8I1R7Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I1R7P CA4_4_8I1R7Value CA4_4_8I1R7P_sound) (by decide +kernel)
def CA4_4_8I1R7MassTerm : Ball := .exact 0
lemma CA4_4_8I1R7MassTerm_sound : CA4_4_8I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I1R7Value a))) :=
  entropyTerm_zero_ball (CA4_4_8I1R7Mass_sound)
def CA4_4_8I1R7H : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R7H_sound : CA4_4_8I1R7H.Encloses (homogeneousEntropy CA4_4_8I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I1R7Value CA4_4_8I1R7MassTerm_sound CA4_4_8I1R7Entropy_sound) (by decide +kernel)
def CA4_4_8I1R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 8 a
def CA4_4_8I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
lemma CA4_4_8I1R8Raw_sound (a : PairSlot) :
    (CA4_4_8I1R8Raw a).Encloses (CA4_4_8I1R8Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 8 a
def CA4_4_8I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_4_8I1R8Certificates_valid :
    CA4_4_8I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_4_8I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R8Certificates (CA4_4_8I1R8CertificateIndex a)).input
lemma CA4_4_8I1R8P_check : ∀ a : PairSlot, contains (CA4_4_8I1R8Raw a) (CA4_4_8I1R8P a) = true := by
  decide +kernel
lemma CA4_4_8I1R8P_sound (a : PairSlot) :
    (CA4_4_8I1R8P a).Encloses (CA4_4_8I1R8Value a) :=
  contains_sound (CA4_4_8I1R8Raw_sound a) (CA4_4_8I1R8P_check a)
def CA4_4_8I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R8Certificates (CA4_4_8I1R8CertificateIndex a)).output
lemma CA4_4_8I1R8Terms_sound (a : PairSlot) :
    (CA4_4_8I1R8Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I1R8Certificates_valid
    (CA4_4_8I1R8CertificateIndex a) (CA4_4_8I1R8P_sound a)
def CA4_4_8I1R8Entropy : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R8Entropy_sound : CA4_4_8I1R8Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I1R8Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I1R8Value CA4_4_8I1R8Terms CA4_4_8I1R8Terms_sound) (by decide +kernel)
def CA4_4_8I1R8Mass : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R8Mass_sound : CA4_4_8I1R8Mass.Encloses (∑ a, CA4_4_8I1R8Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I1R8P CA4_4_8I1R8Value CA4_4_8I1R8P_sound) (by decide +kernel)
def CA4_4_8I1R8MassTerm : Ball := .exact 0
lemma CA4_4_8I1R8MassTerm_sound : CA4_4_8I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I1R8Value a))) :=
  entropyTerm_zero_ball (CA4_4_8I1R8Mass_sound)
def CA4_4_8I1R8H : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R8H_sound : CA4_4_8I1R8H.Encloses (homogeneousEntropy CA4_4_8I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I1R8Value CA4_4_8I1R8MassTerm_sound CA4_4_8I1R8Entropy_sound) (by decide +kernel)
def CA4_4_8I1R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 9 a
def CA4_4_8I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
lemma CA4_4_8I1R9Raw_sound (a : PairSlot) :
    (CA4_4_8I1R9Raw a).Encloses (CA4_4_8I1R9Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 9 a
def CA4_4_8I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_4_8I1R9Certificates_valid :
    CA4_4_8I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_4_8I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R9Certificates (CA4_4_8I1R9CertificateIndex a)).input
lemma CA4_4_8I1R9P_check : ∀ a : PairSlot, contains (CA4_4_8I1R9Raw a) (CA4_4_8I1R9P a) = true := by
  decide +kernel
lemma CA4_4_8I1R9P_sound (a : PairSlot) :
    (CA4_4_8I1R9P a).Encloses (CA4_4_8I1R9Value a) :=
  contains_sound (CA4_4_8I1R9Raw_sound a) (CA4_4_8I1R9P_check a)
def CA4_4_8I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R9Certificates (CA4_4_8I1R9CertificateIndex a)).output
lemma CA4_4_8I1R9Terms_sound (a : PairSlot) :
    (CA4_4_8I1R9Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I1R9Certificates_valid
    (CA4_4_8I1R9CertificateIndex a) (CA4_4_8I1R9P_sound a)
def CA4_4_8I1R9Entropy : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R9Entropy_sound : CA4_4_8I1R9Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I1R9Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I1R9Value CA4_4_8I1R9Terms CA4_4_8I1R9Terms_sound) (by decide +kernel)
def CA4_4_8I1R9Mass : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R9Mass_sound : CA4_4_8I1R9Mass.Encloses (∑ a, CA4_4_8I1R9Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I1R9P CA4_4_8I1R9Value CA4_4_8I1R9P_sound) (by decide +kernel)
def CA4_4_8I1R9MassTerm : Ball := .exact 0
lemma CA4_4_8I1R9MassTerm_sound : CA4_4_8I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I1R9Value a))) :=
  entropyTerm_zero_ball (CA4_4_8I1R9Mass_sound)
def CA4_4_8I1R9H : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R9H_sound : CA4_4_8I1R9H.Encloses (homogeneousEntropy CA4_4_8I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I1R9Value CA4_4_8I1R9MassTerm_sound CA4_4_8I1R9Entropy_sound) (by decide +kernel)
def CA4_4_8I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA4_4_8I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
lemma CA4_4_8I1R10Raw_sound (a : PairSlot) :
    (CA4_4_8I1R10Raw a).Encloses (CA4_4_8I1R10Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 10 a
def CA4_4_8I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_4_8I1R10Certificates_valid :
    CA4_4_8I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_4_8I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R10Certificates (CA4_4_8I1R10CertificateIndex a)).input
lemma CA4_4_8I1R10P_check : ∀ a : PairSlot, contains (CA4_4_8I1R10Raw a) (CA4_4_8I1R10P a) = true := by
  decide +kernel
lemma CA4_4_8I1R10P_sound (a : PairSlot) :
    (CA4_4_8I1R10P a).Encloses (CA4_4_8I1R10Value a) :=
  contains_sound (CA4_4_8I1R10Raw_sound a) (CA4_4_8I1R10P_check a)
def CA4_4_8I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R10Certificates (CA4_4_8I1R10CertificateIndex a)).output
lemma CA4_4_8I1R10Terms_sound (a : PairSlot) :
    (CA4_4_8I1R10Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I1R10Certificates_valid
    (CA4_4_8I1R10CertificateIndex a) (CA4_4_8I1R10P_sound a)
def CA4_4_8I1R10Entropy : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R10Entropy_sound : CA4_4_8I1R10Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I1R10Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I1R10Value CA4_4_8I1R10Terms CA4_4_8I1R10Terms_sound) (by decide +kernel)
def CA4_4_8I1R10Mass : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R10Mass_sound : CA4_4_8I1R10Mass.Encloses (∑ a, CA4_4_8I1R10Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I1R10P CA4_4_8I1R10Value CA4_4_8I1R10P_sound) (by decide +kernel)
def CA4_4_8I1R10MassTerm : Ball := .exact 0
lemma CA4_4_8I1R10MassTerm_sound : CA4_4_8I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I1R10Value a))) :=
  entropyTerm_zero_ball (CA4_4_8I1R10Mass_sound)
def CA4_4_8I1R10H : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R10H_sound : CA4_4_8I1R10H.Encloses (homogeneousEntropy CA4_4_8I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I1R10Value CA4_4_8I1R10MassTerm_sound CA4_4_8I1R10Entropy_sound) (by decide +kernel)
def CA4_4_8I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA4_4_8I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
lemma CA4_4_8I1R11Raw_sound (a : PairSlot) :
    (CA4_4_8I1R11Raw a).Encloses (CA4_4_8I1R11Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 11 a
def CA4_4_8I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_4_8I1R11Certificates_valid :
    CA4_4_8I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_4_8I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R11Certificates (CA4_4_8I1R11CertificateIndex a)).input
lemma CA4_4_8I1R11P_check : ∀ a : PairSlot, contains (CA4_4_8I1R11Raw a) (CA4_4_8I1R11P a) = true := by
  decide +kernel
lemma CA4_4_8I1R11P_sound (a : PairSlot) :
    (CA4_4_8I1R11P a).Encloses (CA4_4_8I1R11Value a) :=
  contains_sound (CA4_4_8I1R11Raw_sound a) (CA4_4_8I1R11P_check a)
def CA4_4_8I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R11Certificates (CA4_4_8I1R11CertificateIndex a)).output
lemma CA4_4_8I1R11Terms_sound (a : PairSlot) :
    (CA4_4_8I1R11Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I1R11Certificates_valid
    (CA4_4_8I1R11CertificateIndex a) (CA4_4_8I1R11P_sound a)
def CA4_4_8I1R11Entropy : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R11Entropy_sound : CA4_4_8I1R11Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I1R11Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I1R11Value CA4_4_8I1R11Terms CA4_4_8I1R11Terms_sound) (by decide +kernel)
def CA4_4_8I1R11Mass : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R11Mass_sound : CA4_4_8I1R11Mass.Encloses (∑ a, CA4_4_8I1R11Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I1R11P CA4_4_8I1R11Value CA4_4_8I1R11P_sound) (by decide +kernel)
def CA4_4_8I1R11MassTerm : Ball := .exact 0
lemma CA4_4_8I1R11MassTerm_sound : CA4_4_8I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I1R11Value a))) :=
  entropyTerm_zero_ball (CA4_4_8I1R11Mass_sound)
def CA4_4_8I1R11H : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R11H_sound : CA4_4_8I1R11H.Encloses (homogeneousEntropy CA4_4_8I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I1R11Value CA4_4_8I1R11MassTerm_sound CA4_4_8I1R11Entropy_sound) (by decide +kernel)
def CA4_4_8I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA4_4_8I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
lemma CA4_4_8I1R12Raw_sound (a : PairSlot) :
    (CA4_4_8I1R12Raw a).Encloses (CA4_4_8I1R12Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 12 a
def CA4_4_8I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_4_8I1R12Certificates_valid :
    CA4_4_8I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_4_8I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R12Certificates (CA4_4_8I1R12CertificateIndex a)).input
lemma CA4_4_8I1R12P_check : ∀ a : PairSlot, contains (CA4_4_8I1R12Raw a) (CA4_4_8I1R12P a) = true := by
  decide +kernel
lemma CA4_4_8I1R12P_sound (a : PairSlot) :
    (CA4_4_8I1R12P a).Encloses (CA4_4_8I1R12Value a) :=
  contains_sound (CA4_4_8I1R12Raw_sound a) (CA4_4_8I1R12P_check a)
def CA4_4_8I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R12Certificates (CA4_4_8I1R12CertificateIndex a)).output
lemma CA4_4_8I1R12Terms_sound (a : PairSlot) :
    (CA4_4_8I1R12Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I1R12Certificates_valid
    (CA4_4_8I1R12CertificateIndex a) (CA4_4_8I1R12P_sound a)
def CA4_4_8I1R12Entropy : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R12Entropy_sound : CA4_4_8I1R12Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I1R12Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I1R12Value CA4_4_8I1R12Terms CA4_4_8I1R12Terms_sound) (by decide +kernel)
def CA4_4_8I1R12Mass : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R12Mass_sound : CA4_4_8I1R12Mass.Encloses (∑ a, CA4_4_8I1R12Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I1R12P CA4_4_8I1R12Value CA4_4_8I1R12P_sound) (by decide +kernel)
def CA4_4_8I1R12MassTerm : Ball := .exact 0
lemma CA4_4_8I1R12MassTerm_sound : CA4_4_8I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I1R12Value a))) :=
  entropyTerm_zero_ball (CA4_4_8I1R12Mass_sound)
def CA4_4_8I1R12H : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R12H_sound : CA4_4_8I1R12H.Encloses (homogeneousEntropy CA4_4_8I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I1R12Value CA4_4_8I1R12MassTerm_sound CA4_4_8I1R12Entropy_sound) (by decide +kernel)
def CA4_4_8I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA4_4_8I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
lemma CA4_4_8I1R13Raw_sound (a : PairSlot) :
    (CA4_4_8I1R13Raw a).Encloses (CA4_4_8I1R13Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 13 a
def CA4_4_8I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_4_8I1R13Certificates_valid :
    CA4_4_8I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_4_8I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R13Certificates (CA4_4_8I1R13CertificateIndex a)).input
lemma CA4_4_8I1R13P_check : ∀ a : PairSlot, contains (CA4_4_8I1R13Raw a) (CA4_4_8I1R13P a) = true := by
  decide +kernel
lemma CA4_4_8I1R13P_sound (a : PairSlot) :
    (CA4_4_8I1R13P a).Encloses (CA4_4_8I1R13Value a) :=
  contains_sound (CA4_4_8I1R13Raw_sound a) (CA4_4_8I1R13P_check a)
def CA4_4_8I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R13Certificates (CA4_4_8I1R13CertificateIndex a)).output
lemma CA4_4_8I1R13Terms_sound (a : PairSlot) :
    (CA4_4_8I1R13Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I1R13Certificates_valid
    (CA4_4_8I1R13CertificateIndex a) (CA4_4_8I1R13P_sound a)
def CA4_4_8I1R13Entropy : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R13Entropy_sound : CA4_4_8I1R13Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I1R13Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I1R13Value CA4_4_8I1R13Terms CA4_4_8I1R13Terms_sound) (by decide +kernel)
def CA4_4_8I1R13Mass : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R13Mass_sound : CA4_4_8I1R13Mass.Encloses (∑ a, CA4_4_8I1R13Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I1R13P CA4_4_8I1R13Value CA4_4_8I1R13P_sound) (by decide +kernel)
def CA4_4_8I1R13MassTerm : Ball := .exact 0
lemma CA4_4_8I1R13MassTerm_sound : CA4_4_8I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I1R13Value a))) :=
  entropyTerm_zero_ball (CA4_4_8I1R13Mass_sound)
def CA4_4_8I1R13H : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R13H_sound : CA4_4_8I1R13H.Encloses (homogeneousEntropy CA4_4_8I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I1R13Value CA4_4_8I1R13MassTerm_sound CA4_4_8I1R13Entropy_sound) (by decide +kernel)
def CA4_4_8I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA4_4_8I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
lemma CA4_4_8I1R14Raw_sound (a : PairSlot) :
    (CA4_4_8I1R14Raw a).Encloses (CA4_4_8I1R14Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 14 a
def CA4_4_8I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_4_8I1R14Certificates_valid :
    CA4_4_8I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_4_8I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R14Certificates (CA4_4_8I1R14CertificateIndex a)).input
lemma CA4_4_8I1R14P_check : ∀ a : PairSlot, contains (CA4_4_8I1R14Raw a) (CA4_4_8I1R14P a) = true := by
  decide +kernel
lemma CA4_4_8I1R14P_sound (a : PairSlot) :
    (CA4_4_8I1R14P a).Encloses (CA4_4_8I1R14Value a) :=
  contains_sound (CA4_4_8I1R14Raw_sound a) (CA4_4_8I1R14P_check a)
def CA4_4_8I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R14Certificates (CA4_4_8I1R14CertificateIndex a)).output
lemma CA4_4_8I1R14Terms_sound (a : PairSlot) :
    (CA4_4_8I1R14Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I1R14Certificates_valid
    (CA4_4_8I1R14CertificateIndex a) (CA4_4_8I1R14P_sound a)
def CA4_4_8I1R14Entropy : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R14Entropy_sound : CA4_4_8I1R14Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I1R14Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I1R14Value CA4_4_8I1R14Terms CA4_4_8I1R14Terms_sound) (by decide +kernel)
def CA4_4_8I1R14Mass : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R14Mass_sound : CA4_4_8I1R14Mass.Encloses (∑ a, CA4_4_8I1R14Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I1R14P CA4_4_8I1R14Value CA4_4_8I1R14P_sound) (by decide +kernel)
def CA4_4_8I1R14MassTerm : Ball := .exact 0
lemma CA4_4_8I1R14MassTerm_sound : CA4_4_8I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I1R14Value a))) :=
  entropyTerm_zero_ball (CA4_4_8I1R14Mass_sound)
def CA4_4_8I1R14H : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R14H_sound : CA4_4_8I1R14H.Encloses (homogeneousEntropy CA4_4_8I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I1R14Value CA4_4_8I1R14MassTerm_sound CA4_4_8I1R14Entropy_sound) (by decide +kernel)
def CA4_4_8I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA4_4_8I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
lemma CA4_4_8I1R15Raw_sound (a : PairSlot) :
    (CA4_4_8I1R15Raw a).Encloses (CA4_4_8I1R15Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 15 a
def CA4_4_8I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_4_8I1R15Certificates_valid :
    CA4_4_8I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_4_8I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R15Certificates (CA4_4_8I1R15CertificateIndex a)).input
lemma CA4_4_8I1R15P_check : ∀ a : PairSlot, contains (CA4_4_8I1R15Raw a) (CA4_4_8I1R15P a) = true := by
  decide +kernel
lemma CA4_4_8I1R15P_sound (a : PairSlot) :
    (CA4_4_8I1R15P a).Encloses (CA4_4_8I1R15Value a) :=
  contains_sound (CA4_4_8I1R15Raw_sound a) (CA4_4_8I1R15P_check a)
def CA4_4_8I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R15Certificates (CA4_4_8I1R15CertificateIndex a)).output
lemma CA4_4_8I1R15Terms_sound (a : PairSlot) :
    (CA4_4_8I1R15Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I1R15Certificates_valid
    (CA4_4_8I1R15CertificateIndex a) (CA4_4_8I1R15P_sound a)
def CA4_4_8I1R15Entropy : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R15Entropy_sound : CA4_4_8I1R15Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I1R15Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I1R15Value CA4_4_8I1R15Terms CA4_4_8I1R15Terms_sound) (by decide +kernel)
def CA4_4_8I1R15Mass : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R15Mass_sound : CA4_4_8I1R15Mass.Encloses (∑ a, CA4_4_8I1R15Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I1R15P CA4_4_8I1R15Value CA4_4_8I1R15P_sound) (by decide +kernel)
def CA4_4_8I1R15MassTerm : Ball := .exact 0
lemma CA4_4_8I1R15MassTerm_sound : CA4_4_8I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I1R15Value a))) :=
  entropyTerm_zero_ball (CA4_4_8I1R15Mass_sound)
def CA4_4_8I1R15H : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R15H_sound : CA4_4_8I1R15H.Encloses (homogeneousEntropy CA4_4_8I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I1R15Value CA4_4_8I1R15MassTerm_sound CA4_4_8I1R15Entropy_sound) (by decide +kernel)
def CA4_4_8I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA4_4_8I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
lemma CA4_4_8I1R16Raw_sound (a : PairSlot) :
    (CA4_4_8I1R16Raw a).Encloses (CA4_4_8I1R16Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 16 a
def CA4_4_8I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_4_8I1R16Certificates_valid :
    CA4_4_8I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_4_8I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R16Certificates (CA4_4_8I1R16CertificateIndex a)).input
lemma CA4_4_8I1R16P_check : ∀ a : PairSlot, contains (CA4_4_8I1R16Raw a) (CA4_4_8I1R16P a) = true := by
  decide +kernel
lemma CA4_4_8I1R16P_sound (a : PairSlot) :
    (CA4_4_8I1R16P a).Encloses (CA4_4_8I1R16Value a) :=
  contains_sound (CA4_4_8I1R16Raw_sound a) (CA4_4_8I1R16P_check a)
def CA4_4_8I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I1R16Certificates (CA4_4_8I1R16CertificateIndex a)).output
lemma CA4_4_8I1R16Terms_sound (a : PairSlot) :
    (CA4_4_8I1R16Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I1R16Certificates_valid
    (CA4_4_8I1R16CertificateIndex a) (CA4_4_8I1R16P_sound a)
def CA4_4_8I1R16Entropy : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R16Entropy_sound : CA4_4_8I1R16Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I1R16Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I1R16Value CA4_4_8I1R16Terms CA4_4_8I1R16Terms_sound) (by decide +kernel)
def CA4_4_8I1R16Mass : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R16Mass_sound : CA4_4_8I1R16Mass.Encloses (∑ a, CA4_4_8I1R16Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I1R16P CA4_4_8I1R16Value CA4_4_8I1R16P_sound) (by decide +kernel)
def CA4_4_8I1R16MassTerm : Ball := .exact 0
lemma CA4_4_8I1R16MassTerm_sound : CA4_4_8I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I1R16Value a))) :=
  entropyTerm_zero_ball (CA4_4_8I1R16Mass_sound)
def CA4_4_8I1R16H : Ball := ⟨0, 0⟩
lemma CA4_4_8I1R16H_sound : CA4_4_8I1R16H.Encloses (homogeneousEntropy CA4_4_8I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I1R16Value CA4_4_8I1R16MassTerm_sound CA4_4_8I1R16Entropy_sound) (by decide +kernel)
def CA4_4_8I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA4_4_8I1R0H
  | 1 => CA4_4_8I1R1H
  | 2 => CA4_4_8I1R2H
  | 3 => CA4_4_8I1R3H
  | 4 => CA4_4_8I1R4H
  | 5 => CA4_4_8I1R5H
  | 6 => CA4_4_8I1R6H
  | 7 => CA4_4_8I1R7H
  | 8 => CA4_4_8I1R8H
  | 9 => CA4_4_8I1R9H
  | 10 => CA4_4_8I1R10H
  | 11 => CA4_4_8I1R11H
  | 12 => CA4_4_8I1R12H
  | 13 => CA4_4_8I1R13H
  | 14 => CA4_4_8I1R14H
  | 15 => CA4_4_8I1R15H
  | 16 => CA4_4_8I1R16H
  | _ => (.exact 0)
lemma CA4_4_8I1ResidualEntropies_sound (k : Fin 17) :
    (CA4_4_8I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CA4_4_8I1R0H_sound
  · exact CA4_4_8I1R1H_sound
  · exact CA4_4_8I1R2H_sound
  · exact CA4_4_8I1R3H_sound
  · exact CA4_4_8I1R4H_sound
  · exact CA4_4_8I1R5H_sound
  · exact CA4_4_8I1R6H_sound
  · exact CA4_4_8I1R7H_sound
  · exact CA4_4_8I1R8H_sound
  · exact CA4_4_8I1R9H_sound
  · exact CA4_4_8I1R10H_sound
  · exact CA4_4_8I1R11H_sound
  · exact CA4_4_8I1R12H_sound
  · exact CA4_4_8I1R13H_sound
  · exact CA4_4_8I1R14H_sound
  · exact CA4_4_8I1R15H_sound
  · exact CA4_4_8I1R16H_sound
def CA4_4_8I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 4, 4, 0 => Z4_4_0H1H
  | _, _, _ => (.exact 0)
lemma CA4_4_8I1Singles_sound (u : Shape) (hu : u ∈ below (shape 4 4 8))
    (hd : designated (Equiv.refl (Fin 3)) 1 u) :
    (CA4_4_8I1Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) u)) := by
  rw [A4_4_8_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 0 8) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 1 7) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 2 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 3 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 4 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 0 7) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 2 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 3 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 4 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 0 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 1 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 2 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 3 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 4 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 0 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 1 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 2 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 3 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 4 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 4 0 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 4 1 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 4 2 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 4 3 1) by decide +kernel) hd |>.elim
  · exact Z4_4_0H1H_sound
def CA4_4_8I1Singleton : Ball := ⟨(119273563983486045807973 / 1562500000000000000000000000000), (1607 / 25000000000000000000000000000000)⟩
lemma CA4_4_8I1Singleton_sound : CA4_4_8I1Singleton.Encloses
    (singletonEntropy (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1
    CA4_4_8I1Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_4_8Law_sound u) CA4_4_8I1Singles_sound) (by decide +kernel)
def CA4_4_8I1Group : Ball := ⟨(46740788728686753822574143080971 / 50000000000000000000000000000000), (7062483779 / 4000000000000000000000000000000)⟩
lemma CA4_4_8I1Group_sound : CA4_4_8I1Group.Encloses
    (groupedEntropy (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA4_4_8I1Singleton_sound
    (finSumBall_sound 17 CA4_4_8I1ResidualEntropies _ CA4_4_8I1ResidualEntropies_sound)) (by decide +kernel)

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
def CA4_4_8I1H : Ball := ⟨(60943550714041131995690773088959 / 50000000000000000000000000000000), (503786375947 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I1_sound : CA4_4_8I1H.Encloses (stageACapacity (shape 4 4 8) 1) := by
  have hb := contains_sound (Ball.add_sound CA4_4_8I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA4_4_8I1Group_sound)))
    (show contains (.add CA4_4_8I1PairH (.neg (.mul (.exact 2) CA4_4_8I1Group))) CA4_4_8I1H = true by decide +kernel)
  unfold CA4_4_8I1PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
