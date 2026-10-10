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
def CA4_5_7I1PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 4 5 7)) (shape 4 5 7) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) a
def CA4_5_7I1PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 4 5 7) A4_5_7Law 1 a
lemma CA4_5_7I1PairRaw_sound (a : PairSlot × PairSlot) :
    (CA4_5_7I1PairRaw a).Encloses (CA4_5_7I1PairValue a) := by
  exact stageAPairBall_sound (shape 4 5 7) (by decide +kernel) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (fun u _ => A4_5_7Law_sound u) 1 a
def CA4_5_7I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(131794220390007136329424907 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(27791992092679985132458046441 / 100000000000000000000000000000000), (4744453 / 50000000000000000000000000000000)⟩ ⟨(-1054370670065711834708874697388963 / 100000000000000000000000000000000), (359989040549 / 100000000000000000000000000000000)⟩ ⟨-16, 131794220390007136329424907, 76293945312500000000000000⟩,
   .log ⟨(377411862302807953596773654799 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(1052901424630535930823425080789 / 50000000000000000000000000000000), (199800183 / 25000000000000000000000000000000)⟩ ⟨(-278979420044239112450397027748341 / 50000000000000000000000000000000), (21175823789 / 10000000000000000000000000000000)⟩ ⟨-9, 377411862302807953596773654799, 195312500000000000000000000000⟩,
   .log ⟨(3186169705805219561965232708489 / 100000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩ ⟨(10980658227194429059378781851311 / 100000000000000000000000000000000), (50602327 / 1250000000000000000000000000000)⟩ ⟨(-86158767745387247431964584064633 / 25000000000000000000000000000000), (63527471347 / 50000000000000000000000000000000)⟩ ⟨-5, 3186169705805219561965232708489, 3125000000000000000000000000000⟩,
   .log ⟨(47312519104068208707250512221 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1186570759077300075585801004589 / 100000000000000000000000000000000), (440827903 / 100000000000000000000000000000000)⟩ ⟨(-125397123377359095401476223498831 / 20000000000000000000000000000000), (232934061569 / 100000000000000000000000000000000)⟩ ⟨-10, 47312519104068208707250512221, 24414062500000000000000000000⟩,
   .log ⟨(67172672180169755099908137 / 781250000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(16098026935998894697178381407 / 20000000000000000000000000000000), (5462159 / 20000000000000000000000000000000)⟩ ⟨(-936138397919943641932190124581857 / 100000000000000000000000000000000), (508219787 / 160000000000000000000000000000)⟩ ⟨-14, 67172672180169755099908137, 47683715820312500000000000⟩,
   .log ⟨(94528763353595906667120753367 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(658300321709569515053402382199 / 100000000000000000000000000000000), (12010347 / 5000000000000000000000000000000)⟩ ⟨(-696402130267080812732495637082817 / 100000000000000000000000000000000), (127054942627 / 50000000000000000000000000000000)⟩ ⟨-11, 94528763353595906667120753367, 48828125000000000000000000000⟩,
   .log ⟨(3158204452479637785265735441619 / 100000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩ ⟨(136401529033144056411712257561 / 1250000000000000000000000000000), (1003163731 / 25000000000000000000000000000000)⟩ ⟨(-172758326556153814360857194562627 / 50000000000000000000000000000000), (127054942699 / 100000000000000000000000000000000)⟩ ⟨-5, 3158204452479637785265735441619, 3125000000000000000000000000000⟩,
   .log ⟨(123646948969556226163537835817 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(296868805033987460946432267897 / 20000000000000000000000000000000), (523665213 / 100000000000000000000000000000000)⟩ ⟨(-600234796547792518774433674099017 / 100000000000000000000000000000000), (105879118819 / 50000000000000000000000000000000)⟩ ⟨-9, 123646948969556226163537835817, 97656250000000000000000000000⟩,
   .log ⟨(7768582797325641064715771043 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(7351283825861274033650453433 / 10000000000000000000000000000000), (6168983 / 25000000000000000000000000000000)⟩ ⟨(-473141885569654769741999935881977 / 50000000000000000000000000000000), (317637368117 / 100000000000000000000000000000000)⟩ ⟨-14, 7768582797325641064715771043, 6103515625000000000000000000⟩,
   .log ⟨(259468022630881803478559515433 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(308989674116005551405011691349 / 20000000000000000000000000000000), (137361231 / 25000000000000000000000000000000)⟩ ⟨(-595429199681328469693864648972639 / 100000000000000000000000000000000), (264697797 / 125000000000000000000000000000)⟩ ⟨-9, 259468022630881803478559515433, 195312500000000000000000000000⟩,
   .log ⟨(9641049911379663411659830799 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(82467113998031999808550973423 / 50000000000000000000000000000000), (57164019 / 100000000000000000000000000000000)⟩ ⟨(-8553748269749461994874068234803 / 1000000000000000000000000000000), (74115384187 / 25000000000000000000000000000000)⟩ ⟨-13, 9641049911379663411659830799, 6103515625000000000000000000⟩,
   .log ⟨(87507066082348384129744274031 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(395875775553028340174026009333 / 20000000000000000000000000000000), (370606851 / 50000000000000000000000000000000)⟩ ⟨(-113098231170409163524408178659583 / 20000000000000000000000000000000), (211758237687 / 100000000000000000000000000000000)⟩ ⟨-9, 87507066082348384129744274031, 48828125000000000000000000000⟩,
   .log ⟨(5847500774950566418128630911669 / 50000000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩ ⟨(25097574527908256672553315379171 / 100000000000000000000000000000000), (12382564679 / 100000000000000000000000000000000)⟩ ⟨(-107300432671257005782461105230159 / 50000000000000000000000000000000), (105879118791 / 100000000000000000000000000000000)⟩ ⟨-4, 5847500774950566418128630911669, 3125000000000000000000000000000⟩,
   .log ⟨(911391632325853421721799278929 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(171266993647321960926644457731 / 4000000000000000000000000000000), (1507771 / 97656250000000000000000000000)⟩ ⟨(-234897638365205279767845880759631 / 50000000000000000000000000000000), (84703294951 / 50000000000000000000000000000000)⟩ ⟨-7, 911391632325853421721799278929, 781250000000000000000000000000⟩,
   .log ⟨(841560374014546517764872623 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(10599437210091078121584854003 / 25000000000000000000000000000000), (14256599 / 100000000000000000000000000000000)⟩ ⟨(-503799253737575101259426639421981 / 50000000000000000000000000000000), (338813202693 / 100000000000000000000000000000000)⟩ ⟨-15, 841560374014546517764872623, 610351562500000000000000000⟩,
   .log ⟨(4967864196250324691748968943 / 4000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(415503444731472158054937260161 / 50000000000000000000000000000000), (289296219 / 100000000000000000000000000000000)⟩ ⟨(-669105963154288189496535891004513 / 100000000000000000000000000000000), (14558378933 / 6250000000000000000000000000000)⟩ ⟨-10, 4967864196250324691748968943, 3906250000000000000000000000⟩,
   .log ⟨(4359527261310185721805115931 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1018757725742407205414154101 / 1250000000000000000000000000000), (5538997 / 20000000000000000000000000000000)⟩ ⟨(-93474146592329001732741510517769 / 10000000000000000000000000000000), (158818683357 / 50000000000000000000000000000000)⟩ ⟨-14, 4359527261310185721805115931, 3051757812500000000000000000⟩]
lemma CA4_5_7I1PairCertificates_valid :
    CA4_5_7I1PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I1PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 1, 0, 5, 0 => 1
  | 1, 0, 4, 1 => 2
  | 1, 0, 2, 2 => 3
  | 1, 0, 2, 3 => 4
  | 1, 0, 3, 2 => 4
  | 1, 0, 3, 3 => 5
  | 1, 0, 1, 4 => 2
  | 1, 0, 0, 5 => 1
  | 0, 1, 5, 0 => 1
  | 0, 1, 4, 1 => 2
  | 0, 1, 2, 2 => 3
  | 0, 1, 2, 3 => 4
  | 0, 1, 3, 2 => 4
  | 0, 1, 3, 3 => 5
  | 0, 1, 1, 4 => 2
  | 0, 1, 0, 5 => 1
  | 2, 0, 4, 0 => 6
  | 2, 0, 2, 1 => 7
  | 2, 0, 3, 1 => 8
  | 2, 0, 1, 2 => 7
  | 2, 0, 1, 3 => 8
  | 2, 0, 0, 4 => 6
  | 3, 0, 4, 0 => 9
  | 3, 0, 2, 1 => 10
  | 3, 0, 3, 1 => 11
  | 3, 0, 1, 2 => 10
  | 3, 0, 1, 3 => 11
  | 3, 0, 0, 4 => 9
  | 1, 1, 4, 0 => 12
  | 1, 1, 2, 1 => 13
  | 1, 1, 3, 1 => 14
  | 1, 1, 1, 2 => 13
  | 1, 1, 1, 3 => 14
  | 1, 1, 0, 4 => 12
  | 0, 2, 4, 0 => 6
  | 0, 2, 2, 1 => 7
  | 0, 2, 3, 1 => 8
  | 0, 2, 1, 2 => 7
  | 0, 2, 1, 3 => 8
  | 0, 2, 0, 4 => 6
  | 0, 3, 4, 0 => 9
  | 0, 3, 2, 1 => 10
  | 0, 3, 3, 1 => 11
  | 0, 3, 1, 2 => 10
  | 0, 3, 1, 3 => 11
  | 0, 3, 0, 4 => 9
  | 4, 0, 2, 0 => 6
  | 4, 0, 3, 0 => 9
  | 4, 0, 1, 1 => 12
  | 4, 0, 0, 2 => 6
  | 4, 0, 0, 3 => 9
  | 2, 1, 2, 0 => 7
  | 2, 1, 3, 0 => 10
  | 2, 1, 1, 1 => 13
  | 2, 1, 0, 2 => 7
  | 2, 1, 0, 3 => 10
  | 3, 1, 2, 0 => 8
  | 3, 1, 3, 0 => 11
  | 3, 1, 1, 1 => 14
  | 3, 1, 0, 2 => 8
  | 3, 1, 0, 3 => 11
  | 1, 2, 2, 0 => 7
  | 1, 2, 3, 0 => 10
  | 1, 2, 1, 1 => 13
  | 1, 2, 0, 2 => 7
  | 1, 2, 0, 3 => 10
  | 1, 3, 2, 0 => 8
  | 1, 3, 3, 0 => 11
  | 1, 3, 1, 1 => 14
  | 1, 3, 0, 2 => 8
  | 1, 3, 0, 3 => 11
  | 0, 4, 2, 0 => 6
  | 0, 4, 3, 0 => 9
  | 0, 4, 1, 1 => 12
  | 0, 4, 0, 2 => 6
  | 0, 4, 0, 3 => 9
  | 0, 5, 1, 0 => 1
  | 0, 5, 0, 1 => 1
  | 1, 4, 1, 0 => 2
  | 1, 4, 0, 1 => 2
  | 2, 2, 1, 0 => 3
  | 2, 2, 0, 1 => 3
  | 2, 3, 1, 0 => 4
  | 2, 3, 0, 1 => 4
  | 3, 2, 1, 0 => 4
  | 3, 2, 0, 1 => 4
  | 3, 3, 1, 0 => 5
  | 3, 3, 0, 1 => 5
  | 4, 1, 1, 0 => 2
  | 4, 1, 0, 1 => 2
  | 5, 0, 1, 0 => 1
  | 5, 0, 0, 1 => 1
  | 1, 5, 0, 0 => 15
  | 2, 4, 0, 0 => 16
  | 3, 4, 0, 0 => 17
  | 4, 2, 0, 0 => 16
  | 4, 3, 0, 0 => 17
  | 5, 1, 0, 0 => 15
  | 0, 0, 1, 5 => 15
  | 0, 0, 2, 4 => 16
  | 0, 0, 3, 4 => 17
  | 0, 0, 4, 2 => 16
  | 0, 0, 4, 3 => 17
  | 0, 0, 5, 1 => 15
  | _, _, _, _ => 0
def CA4_5_7I1PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1PairCertificates (CA4_5_7I1PairCertificateIndex a)).input
lemma CA4_5_7I1PairP_check_0_0 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((0,0),(k,l))) (CA4_5_7I1PairP ((0,0),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_0_1 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((0,1),(k,l))) (CA4_5_7I1PairP ((0,1),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_0_2 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((0,2),(k,l))) (CA4_5_7I1PairP ((0,2),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_0_3 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((0,3),(k,l))) (CA4_5_7I1PairP ((0,3),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_0_4 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((0,4),(k,l))) (CA4_5_7I1PairP ((0,4),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_0_5 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((0,5),(k,l))) (CA4_5_7I1PairP ((0,5),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_1_0 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((1,0),(k,l))) (CA4_5_7I1PairP ((1,0),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_1_1 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((1,1),(k,l))) (CA4_5_7I1PairP ((1,1),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_1_2 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((1,2),(k,l))) (CA4_5_7I1PairP ((1,2),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_1_3 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((1,3),(k,l))) (CA4_5_7I1PairP ((1,3),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_1_4 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((1,4),(k,l))) (CA4_5_7I1PairP ((1,4),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_1_5 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((1,5),(k,l))) (CA4_5_7I1PairP ((1,5),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_2_0 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((2,0),(k,l))) (CA4_5_7I1PairP ((2,0),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_2_1 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((2,1),(k,l))) (CA4_5_7I1PairP ((2,1),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_2_2 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((2,2),(k,l))) (CA4_5_7I1PairP ((2,2),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_2_3 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((2,3),(k,l))) (CA4_5_7I1PairP ((2,3),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_2_4 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((2,4),(k,l))) (CA4_5_7I1PairP ((2,4),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_2_5 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((2,5),(k,l))) (CA4_5_7I1PairP ((2,5),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_3_0 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((3,0),(k,l))) (CA4_5_7I1PairP ((3,0),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_3_1 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((3,1),(k,l))) (CA4_5_7I1PairP ((3,1),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_3_2 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((3,2),(k,l))) (CA4_5_7I1PairP ((3,2),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_3_3 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((3,3),(k,l))) (CA4_5_7I1PairP ((3,3),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_3_4 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((3,4),(k,l))) (CA4_5_7I1PairP ((3,4),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_3_5 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((3,5),(k,l))) (CA4_5_7I1PairP ((3,5),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_4_0 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((4,0),(k,l))) (CA4_5_7I1PairP ((4,0),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_4_1 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((4,1),(k,l))) (CA4_5_7I1PairP ((4,1),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_4_2 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((4,2),(k,l))) (CA4_5_7I1PairP ((4,2),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_4_3 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((4,3),(k,l))) (CA4_5_7I1PairP ((4,3),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_4_4 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((4,4),(k,l))) (CA4_5_7I1PairP ((4,4),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_4_5 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((4,5),(k,l))) (CA4_5_7I1PairP ((4,5),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_5_0 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((5,0),(k,l))) (CA4_5_7I1PairP ((5,0),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_5_1 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((5,1),(k,l))) (CA4_5_7I1PairP ((5,1),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_5_2 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((5,2),(k,l))) (CA4_5_7I1PairP ((5,2),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_5_3 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((5,3),(k,l))) (CA4_5_7I1PairP ((5,3),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_5_4 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((5,4),(k,l))) (CA4_5_7I1PairP ((5,4),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_5_5 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((5,5),(k,l))) (CA4_5_7I1PairP ((5,5),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check (a : PairSlot × PairSlot) : contains (CA4_5_7I1PairRaw a) (CA4_5_7I1PairP a) = true := by
  rcases a with ⟨⟨i,j⟩,⟨k,l⟩⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (CA4_5_7I1PairP_check_0_0 k l) (CA4_5_7I1PairP_check_0_1 k l) (CA4_5_7I1PairP_check_0_2 k l) (CA4_5_7I1PairP_check_0_3 k l) (CA4_5_7I1PairP_check_0_4 k l) (CA4_5_7I1PairP_check_0_5 k l)
  · exact forall_fin6 (CA4_5_7I1PairP_check_1_0 k l) (CA4_5_7I1PairP_check_1_1 k l) (CA4_5_7I1PairP_check_1_2 k l) (CA4_5_7I1PairP_check_1_3 k l) (CA4_5_7I1PairP_check_1_4 k l) (CA4_5_7I1PairP_check_1_5 k l)
  · exact forall_fin6 (CA4_5_7I1PairP_check_2_0 k l) (CA4_5_7I1PairP_check_2_1 k l) (CA4_5_7I1PairP_check_2_2 k l) (CA4_5_7I1PairP_check_2_3 k l) (CA4_5_7I1PairP_check_2_4 k l) (CA4_5_7I1PairP_check_2_5 k l)
  · exact forall_fin6 (CA4_5_7I1PairP_check_3_0 k l) (CA4_5_7I1PairP_check_3_1 k l) (CA4_5_7I1PairP_check_3_2 k l) (CA4_5_7I1PairP_check_3_3 k l) (CA4_5_7I1PairP_check_3_4 k l) (CA4_5_7I1PairP_check_3_5 k l)
  · exact forall_fin6 (CA4_5_7I1PairP_check_4_0 k l) (CA4_5_7I1PairP_check_4_1 k l) (CA4_5_7I1PairP_check_4_2 k l) (CA4_5_7I1PairP_check_4_3 k l) (CA4_5_7I1PairP_check_4_4 k l) (CA4_5_7I1PairP_check_4_5 k l)
  · exact forall_fin6 (CA4_5_7I1PairP_check_5_0 k l) (CA4_5_7I1PairP_check_5_1 k l) (CA4_5_7I1PairP_check_5_2 k l) (CA4_5_7I1PairP_check_5_3 k l) (CA4_5_7I1PairP_check_5_4 k l) (CA4_5_7I1PairP_check_5_5 k l)
lemma CA4_5_7I1PairP_sound (a : PairSlot × PairSlot) :
    (CA4_5_7I1PairP a).Encloses (CA4_5_7I1PairValue a) :=
  contains_sound (CA4_5_7I1PairRaw_sound a) (CA4_5_7I1PairP_check a)
def CA4_5_7I1PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1PairCertificates (CA4_5_7I1PairCertificateIndex a)).output
lemma CA4_5_7I1PairTerms_sound (a : PairSlot × PairSlot) :
    (CA4_5_7I1PairTerms a).Encloses (Foundation.entropyTerm (CA4_5_7I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I1PairCertificates_valid
    (CA4_5_7I1PairCertificateIndex a) (CA4_5_7I1PairP_sound a)
def CA4_5_7I1PairEntropy : Ball := ⟨(79691337278687147638616213846057 / 25000000000000000000000000000000), (32389139629 / 25000000000000000000000000000000)⟩
lemma CA4_5_7I1PairEntropy_sound : CA4_5_7I1PairEntropy.Encloses (Foundation.finiteEntropy CA4_5_7I1PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA4_5_7I1PairValue CA4_5_7I1PairTerms CA4_5_7I1PairTerms_sound) (by decide +kernel)
def CA4_5_7I1PairMass : Ball := ⟨(12500000000000000000000000000001 / 12500000000000000000000000000000), (71 / 12500000000000000000000000000000)⟩
lemma CA4_5_7I1PairMass_sound : CA4_5_7I1PairMass.Encloses (∑ a, CA4_5_7I1PairValue a) := by
  exact contains_sound (doublePairSumBall_sound CA4_5_7I1PairP CA4_5_7I1PairValue CA4_5_7I1PairP_sound) (by decide +kernel)
def CA4_5_7I1PairMassTermLogWitness : LogWitness := ⟨0, 12500000000000000000000000000001, 12500000000000000000000000000000⟩
def CA4_5_7I1PairMassTermLog : Ball := ⟨(1 / 12500000000000000000000000000000), (84703297 / 400000000000000000000000000000)⟩
lemma CA4_5_7I1PairMassTermLog_sound : CA4_5_7I1PairMassTermLog.Encloses (Real.log ((∑ a, CA4_5_7I1PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_5_7I1PairMass_sound) (w := CA4_5_7I1PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_5_7I1PairMassTerm : Ball := ⟨(-1 / 12500000000000000000000000000000), (21175824251 / 100000000000000000000000000000000)⟩
lemma CA4_5_7I1PairMassTerm_sound : CA4_5_7I1PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I1PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA4_5_7I1PairMass_sound) CA4_5_7I1PairMassTermLog_sound) (by decide +kernel)
def CA4_5_7I1PairH : Ball := ⟨(79691337278687147638616213846059 / 25000000000000000000000000000000), (150732382767 / 100000000000000000000000000000000)⟩
lemma CA4_5_7I1PairH_sound : CA4_5_7I1PairH.Encloses (homogeneousEntropy CA4_5_7I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I1PairValue CA4_5_7I1PairMassTerm_sound CA4_5_7I1PairEntropy_sound) (by decide +kernel)

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
def CA4_5_7I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA4_5_7I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
lemma CA4_5_7I1R0Raw_sound (a : PairSlot) :
    (CA4_5_7I1R0Raw a).Encloses (CA4_5_7I1R0Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 0 a
def CA4_5_7I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(274246922597902442652317637103 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(1617754235717366730301305147667 / 100000000000000000000000000000000), (580740483 / 100000000000000000000000000000000)⟩ ⟨(-147472414675852045839935424960033 / 25000000000000000000000000000000), (211758238653 / 100000000000000000000000000000000)⟩ ⟨-9, 274246922597902442652317637103, 195312500000000000000000000000⟩]
lemma CA4_5_7I1R0Certificates_valid :
    CA4_5_7I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA4_5_7I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R0Certificates (CA4_5_7I1R0CertificateIndex a)).input
lemma CA4_5_7I1R0P_check : ∀ a : PairSlot, contains (CA4_5_7I1R0Raw a) (CA4_5_7I1R0P a) = true := by
  decide +kernel
lemma CA4_5_7I1R0P_sound (a : PairSlot) :
    (CA4_5_7I1R0P a).Encloses (CA4_5_7I1R0Value a) :=
  contains_sound (CA4_5_7I1R0Raw_sound a) (CA4_5_7I1R0P_check a)
def CA4_5_7I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R0Certificates (CA4_5_7I1R0CertificateIndex a)).output
lemma CA4_5_7I1R0Terms_sound (a : PairSlot) :
    (CA4_5_7I1R0Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I1R0Certificates_valid
    (CA4_5_7I1R0CertificateIndex a) (CA4_5_7I1R0P_sound a)
def CA4_5_7I1R0Entropy : Ball := ⟨(1617754235717366730301305147667 / 100000000000000000000000000000000), (580740483 / 100000000000000000000000000000000)⟩
lemma CA4_5_7I1R0Entropy_sound : CA4_5_7I1R0Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I1R0Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I1R0Value CA4_5_7I1R0Terms CA4_5_7I1R0Terms_sound) (by decide +kernel)
def CA4_5_7I1R0Mass : Ball := ⟨(274246922597902442652317637103 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
lemma CA4_5_7I1R0Mass_sound : CA4_5_7I1R0Mass.Encloses (∑ a, CA4_5_7I1R0Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I1R0P CA4_5_7I1R0Value CA4_5_7I1R0P_sound) (by decide +kernel)
def CA4_5_7I1R0MassTermLogWitness : LogWitness := ⟨-9, 274246922597902442652317637103, 195312500000000000000000000000⟩
def CA4_5_7I1R0MassTermLog : Ball := ⟨(-147472414675852045839935424960033 / 25000000000000000000000000000000), (211758238653 / 100000000000000000000000000000000)⟩
lemma CA4_5_7I1R0MassTermLog_sound : CA4_5_7I1R0MassTermLog.Encloses (Real.log ((∑ a, CA4_5_7I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_5_7I1R0Mass_sound) (w := CA4_5_7I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_5_7I1R0MassTerm : Ball := ⟨(1617754235717366730301305147667 / 100000000000000000000000000000000), (580740483 / 100000000000000000000000000000000)⟩
lemma CA4_5_7I1R0MassTerm_sound : CA4_5_7I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_5_7I1R0Mass_sound) CA4_5_7I1R0MassTermLog_sound) (by decide +kernel)
def CA4_5_7I1R0H : Ball := ⟨0, (580740483 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I1R0H_sound : CA4_5_7I1R0H.Encloses (homogeneousEntropy CA4_5_7I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I1R0Value CA4_5_7I1R0MassTerm_sound CA4_5_7I1R0Entropy_sound) (by decide +kernel)
def CA4_5_7I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA4_5_7I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
lemma CA4_5_7I1R1Raw_sound (a : PairSlot) :
    (CA4_5_7I1R1Raw a).Encloses (CA4_5_7I1R1Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 1 a
def CA4_5_7I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(433336345409804315292274935367 / 10000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩ ⟨(13601674597694605000986940575089 / 100000000000000000000000000000000), (5505752523 / 100000000000000000000000000000000)⟩ ⟨(-78470654156827994211266879368857 / 25000000000000000000000000000000), (31763735657 / 25000000000000000000000000000000)⟩ ⟨-5, 433336345409804315292274935367, 312500000000000000000000000000⟩]
lemma CA4_5_7I1R1Certificates_valid :
    CA4_5_7I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA4_5_7I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R1Certificates (CA4_5_7I1R1CertificateIndex a)).input
lemma CA4_5_7I1R1P_check : ∀ a : PairSlot, contains (CA4_5_7I1R1Raw a) (CA4_5_7I1R1P a) = true := by
  decide +kernel
lemma CA4_5_7I1R1P_sound (a : PairSlot) :
    (CA4_5_7I1R1P a).Encloses (CA4_5_7I1R1Value a) :=
  contains_sound (CA4_5_7I1R1Raw_sound a) (CA4_5_7I1R1P_check a)
def CA4_5_7I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R1Certificates (CA4_5_7I1R1CertificateIndex a)).output
lemma CA4_5_7I1R1Terms_sound (a : PairSlot) :
    (CA4_5_7I1R1Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I1R1Certificates_valid
    (CA4_5_7I1R1CertificateIndex a) (CA4_5_7I1R1P_sound a)
def CA4_5_7I1R1Entropy : Ball := ⟨(13601674597694605000986940575089 / 50000000000000000000000000000000), (5505752523 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I1R1Entropy_sound : CA4_5_7I1R1Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I1R1Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I1R1Value CA4_5_7I1R1Terms CA4_5_7I1R1Terms_sound) (by decide +kernel)
def CA4_5_7I1R1Mass : Ball := ⟨(433336345409804315292274935367 / 5000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I1R1Mass_sound : CA4_5_7I1R1Mass.Encloses (∑ a, CA4_5_7I1R1Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I1R1P CA4_5_7I1R1Value CA4_5_7I1R1P_sound) (by decide +kernel)
def CA4_5_7I1R1MassTermLogWitness : LogWitness := ⟨-4, 433336345409804315292274935367, 312500000000000000000000000000⟩
def CA4_5_7I1R1MassTermLog : Ball := ⟨(-122283949285658722951672162212549 / 50000000000000000000000000000000), (21175823789 / 20000000000000000000000000000000)⟩
lemma CA4_5_7I1R1MassTermLog_sound : CA4_5_7I1R1MassTermLog.Encloses (Real.log ((∑ a, CA4_5_7I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_5_7I1R1Mass_sound) (w := CA4_5_7I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_5_7I1R1MassTerm : Ball := ⟨(10598015937145040405897974413661 / 50000000000000000000000000000000), (1835250841 / 20000000000000000000000000000000)⟩
lemma CA4_5_7I1R1MassTerm_sound : CA4_5_7I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_5_7I1R1Mass_sound) CA4_5_7I1R1MassTermLog_sound) (by decide +kernel)
def CA4_5_7I1R1H : Ball := ⟨(750914665137391148772241540357 / 12500000000000000000000000000000), (20187759251 / 100000000000000000000000000000000)⟩
lemma CA4_5_7I1R1H_sound : CA4_5_7I1R1H.Encloses (homogeneousEntropy CA4_5_7I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I1R1Value CA4_5_7I1R1MassTerm_sound CA4_5_7I1R1Entropy_sound) (by decide +kernel)
def CA4_5_7I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA4_5_7I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
lemma CA4_5_7I1R2Raw_sound (a : PairSlot) :
    (CA4_5_7I1R2Raw a).Encloses (CA4_5_7I1R2Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 2 a
def CA4_5_7I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(175001355688617307212996593331 / 2500000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩ ⟨(18614910235917211126043375071177 / 100000000000000000000000000000000), (7411595833 / 100000000000000000000000000000000)⟩ ⟨(-6648130725426713508786156902229 / 2500000000000000000000000000000), (52939559457 / 50000000000000000000000000000000)⟩ ⟨-4, 175001355688617307212996593331, 156250000000000000000000000000⟩,
   .log ⟨(573037410501933542733189896149 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(92437639953913351815423558279 / 3125000000000000000000000000000), (1092108551 / 100000000000000000000000000000000)⟩ ⟨(-516197446155262206896439087820737 / 100000000000000000000000000000000), (47645603461 / 25000000000000000000000000000000)⟩ ⟨-8, 573037410501933542733189896149, 390625000000000000000000000000⟩,
   .log ⟨(25912842893112759588996076396781 / 100000000000000000000000000000000), (39 / 50000000000000000000000000000000)⟩ ⟨(174967593323596970613469417049 / 500000000000000000000000000000), (16461773951 / 100000000000000000000000000000000)⟩ ⟨(-67521573779193753290625642121891 / 50000000000000000000000000000000), (63527471349 / 100000000000000000000000000000000)⟩ ⟨-2, 25912842893112759588996076396781, 25000000000000000000000000000000⟩]
lemma CA4_5_7I1R2Certificates_valid :
    CA4_5_7I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA4_5_7I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R2Certificates (CA4_5_7I1R2CertificateIndex a)).input
lemma CA4_5_7I1R2P_check : ∀ a : PairSlot, contains (CA4_5_7I1R2Raw a) (CA4_5_7I1R2P a) = true := by
  decide +kernel
lemma CA4_5_7I1R2P_sound (a : PairSlot) :
    (CA4_5_7I1R2P a).Encloses (CA4_5_7I1R2Value a) :=
  contains_sound (CA4_5_7I1R2Raw_sound a) (CA4_5_7I1R2P_check a)
def CA4_5_7I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R2Certificates (CA4_5_7I1R2CertificateIndex a)).output
lemma CA4_5_7I1R2Terms_sound (a : PairSlot) :
    (CA4_5_7I1R2Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I1R2Certificates_valid
    (CA4_5_7I1R2CertificateIndex a) (CA4_5_7I1R2P_sound a)
def CA4_5_7I1R2Entropy : Ball := ⟨(7813934809360427089096774128201 / 10000000000000000000000000000000), (33469182719 / 100000000000000000000000000000000)⟩
lemma CA4_5_7I1R2Entropy_sound : CA4_5_7I1R2Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I1R2Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I1R2Value CA4_5_7I1R2Terms CA4_5_7I1R2Terms_sound) (by decide +kernel)
def CA4_5_7I1R2Mass : Ball := ⟨(41059026169206011251502183655559 / 100000000000000000000000000000000), (39 / 25000000000000000000000000000000)⟩
lemma CA4_5_7I1R2Mass_sound : CA4_5_7I1R2Mass.Encloses (∑ a, CA4_5_7I1R2Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I1R2P CA4_5_7I1R2Value CA4_5_7I1R2P_sound) (by decide +kernel)
def CA4_5_7I1R2MassTermLogWitness : LogWitness := ⟨-2, 41059026169206011251502183655559, 25000000000000000000000000000000⟩
def CA4_5_7I1R2MassTermLog : Ball := ⟨(-44507974597047939457626321697919 / 50000000000000000000000000000000), (15881867857 / 25000000000000000000000000000000)⟩
lemma CA4_5_7I1R2MassTermLog_sound : CA4_5_7I1R2MassTermLog.Encloses (Real.log ((∑ a, CA4_5_7I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_5_7I1R2Mass_sound) (w := CA4_5_7I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_5_7I1R2MassTerm : Ball := ⟨(9137270468592738599433860267587 / 25000000000000000000000000000000), (13041880629 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I1R2MassTerm_sound : CA4_5_7I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_5_7I1R2Mass_sound) CA4_5_7I1R2MassTermLog_sound) (by decide +kernel)
def CA4_5_7I1R2H : Ball := ⟨(20795133109616658246616150105831 / 50000000000000000000000000000000), (59552943977 / 100000000000000000000000000000000)⟩
lemma CA4_5_7I1R2H_sound : CA4_5_7I1R2H.Encloses (homogeneousEntropy CA4_5_7I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I1R2Value CA4_5_7I1R2MassTerm_sound CA4_5_7I1R2Entropy_sound) (by decide +kernel)
def CA4_5_7I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA4_5_7I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
lemma CA4_5_7I1R3Raw_sound (a : PairSlot) :
    (CA4_5_7I1R3Raw a).Encloses (CA4_5_7I1R3Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 3 a
def CA4_5_7I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(34663934789452289498915634059 / 6250000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(2881064898018432527557952332239 / 100000000000000000000000000000000), (13212673 / 1250000000000000000000000000000)⟩ ⟨(-51946369395128091335029867965229 / 10000000000000000000000000000000), (47645603467 / 25000000000000000000000000000000)⟩ ⟨-8, 34663934789452289498915634059, 24414062500000000000000000000⟩,
   .log ⟨(9265173250061086006872925868721 / 50000000000000000000000000000000), (1 / 2000000000000000000000000000000)⟩ ⟨(6247545037793812001820879868087 / 20000000000000000000000000000000), (7847907073 / 50000000000000000000000000000000)⟩ ⟨(-21072005580658669321609938394017 / 12500000000000000000000000000000), (84703295001 / 100000000000000000000000000000000)⟩ ⟨-3, 9265173250061086006872925868721, 6250000000000000000000000000000⟩,
   .log ⟨(722271813924798490011294972697 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(47820902910853977069879978091 / 781250000000000000000000000000), (61178803 / 2500000000000000000000000000000)⟩ ⟨(-423737674278580066800285156911857 / 100000000000000000000000000000000), (16940658981 / 10000000000000000000000000000000)⟩ ⟨-7, 722271813924798490011294972697, 390625000000000000000000000000⟩]
lemma CA4_5_7I1R3Certificates_valid :
    CA4_5_7I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA4_5_7I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R3Certificates (CA4_5_7I1R3CertificateIndex a)).input
lemma CA4_5_7I1R3P_check : ∀ a : PairSlot, contains (CA4_5_7I1R3Raw a) (CA4_5_7I1R3P a) = true := by
  decide +kernel
lemma CA4_5_7I1R3P_sound (a : PairSlot) :
    (CA4_5_7I1R3P a).Encloses (CA4_5_7I1R3Value a) :=
  contains_sound (CA4_5_7I1R3Raw_sound a) (CA4_5_7I1R3P_check a)
def CA4_5_7I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R3Certificates (CA4_5_7I1R3CertificateIndex a)).output
lemma CA4_5_7I1R3Terms_sound (a : PairSlot) :
    (CA4_5_7I1R3Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I1R3Certificates_valid
    (CA4_5_7I1R3CertificateIndex a) (CA4_5_7I1R3P_sound a)
def CA4_5_7I1R3Entropy : Ball := ⟨(20119932829788400800803494434161 / 25000000000000000000000000000000), (9599990053 / 25000000000000000000000000000000)⟩
lemma CA4_5_7I1R3Entropy_sound : CA4_5_7I1R3Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I1R3Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I1R3Value CA4_5_7I1R3Terms CA4_5_7I1R3Terms_sound) (by decide +kernel)
def CA4_5_7I1R3Mass : Ball := ⟨(1026475654230150281287554591389 / 2500000000000000000000000000000), (59 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I1R3Mass_sound : CA4_5_7I1R3Mass.Encloses (∑ a, CA4_5_7I1R3Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I1R3P CA4_5_7I1R3Value CA4_5_7I1R3P_sound) (by decide +kernel)
def CA4_5_7I1R3MassTermLogWitness : LogWitness := ⟨-2, 1026475654230150281287554591389, 625000000000000000000000000000⟩
def CA4_5_7I1R3MassTermLog : Ball := ⟨(-22253987298523969728813160848959 / 25000000000000000000000000000000), (7940933917 / 12500000000000000000000000000000)⟩
lemma CA4_5_7I1R3MassTermLog_sound : CA4_5_7I1R3MassTermLog.Encloses (Real.log ((∑ a, CA4_5_7I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_5_7I1R3Mass_sound) (w := CA4_5_7I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_5_7I1R3MassTerm : Ball := ⟨(9137270468592738599433860267587 / 25000000000000000000000000000000), (13041880593 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I1R3MassTerm_sound : CA4_5_7I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I1R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_5_7I1R3Mass_sound) CA4_5_7I1R3MassTermLog_sound) (by decide +kernel)
def CA4_5_7I1R3H : Ball := ⟨(5491331180597831100684817083287 / 12500000000000000000000000000000), (32241860699 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I1R3H_sound : CA4_5_7I1R3H.Encloses (homogeneousEntropy CA4_5_7I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I1R3Value CA4_5_7I1R3MassTerm_sound CA4_5_7I1R3Entropy_sound) (by decide +kernel)
def CA4_5_7I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA4_5_7I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
lemma CA4_5_7I1R4Raw_sound (a : PairSlot) :
    (CA4_5_7I1R4Raw a).Encloses (CA4_5_7I1R4Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 4 a
def CA4_5_7I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(658874712842399214977204153 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(12980761914397518637762388271 / 25000000000000000000000000000000), (8929423 / 50000000000000000000000000000000)⟩ ⟨(-985070580292741980894805713655271 / 100000000000000000000000000000000), (338813197899 / 100000000000000000000000000000000)⟩ ⟨-15, 658874712842399214977204153, 381469726562500000000000000⟩,
   .log ⟨(754777223342937116225266002401 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(184411051806776859203012729963 / 5000000000000000000000000000000), (719236341 / 50000000000000000000000000000000)⟩ ⟨(-488650282768240609177503271384849 / 100000000000000000000000000000000), (95291206971 / 50000000000000000000000000000000)⟩ ⟨-8, 754777223342937116225266002401, 390625000000000000000000000000⟩,
   .log ⟨(6372123173650731951081423713949 / 100000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩ ⟨(8771984122418504944039848966003 / 50000000000000000000000000000000), (1349349593 / 20000000000000000000000000000000)⟩ ⟨(-275323746367345845113860573948821 / 100000000000000000000000000000000), (26469779733 / 25000000000000000000000000000000)⟩ ⟨-4, 6372123173650731951081423713949, 6250000000000000000000000000000⟩,
   .log ⟨(378476123399241868964196248359 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(2110675227891045696596471406763 / 100000000000000000000000000000000), (400727193 / 50000000000000000000000000000000)⟩ ⟨(-139419311906273452710645510129687 / 25000000000000000000000000000000), (105879118811 / 50000000000000000000000000000000)⟩ ⟨-9, 378476123399241868964196248359, 195312500000000000000000000000⟩,
   .log ⟨(8596793995853834942853549759 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(149040708017777450506454299703 / 100000000000000000000000000000000), (10194477 / 20000000000000000000000000000000)⟩ ⟨(-216709723545862843129706562076591 / 25000000000000000000000000000000), (296461537377 / 100000000000000000000000000000000)⟩ ⟨-13, 8596793995853834942853549759, 6103515625000000000000000000⟩]
lemma CA4_5_7I1R4Certificates_valid :
    CA4_5_7I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I1R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA4_5_7I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R4Certificates (CA4_5_7I1R4CertificateIndex a)).input
lemma CA4_5_7I1R4P_check : ∀ a : PairSlot, contains (CA4_5_7I1R4Raw a) (CA4_5_7I1R4P a) = true := by
  decide +kernel
lemma CA4_5_7I1R4P_sound (a : PairSlot) :
    (CA4_5_7I1R4P a).Encloses (CA4_5_7I1R4Value a) :=
  contains_sound (CA4_5_7I1R4Raw_sound a) (CA4_5_7I1R4P_check a)
def CA4_5_7I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R4Certificates (CA4_5_7I1R4CertificateIndex a)).output
lemma CA4_5_7I1R4Terms_sound (a : PairSlot) :
    (CA4_5_7I1R4Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I1R4Certificates_valid
    (CA4_5_7I1R4CertificateIndex a) (CA4_5_7I1R4P_sound a)
def CA4_5_7I1R4Entropy : Ball := ⟨(29394647576223133249001703349923 / 100000000000000000000000000000000), (5656646089 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I1R4Entropy_sound : CA4_5_7I1R4Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I1R4Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I1R4Value CA4_5_7I1R4Terms CA4_5_7I1R4Terms_sound) (by decide +kernel)
def CA4_5_7I1R4Mass : Ball := ⟨(1733273090106455195757138116287 / 20000000000000000000000000000000), (27 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I1R4Mass_sound : CA4_5_7I1R4Mass.Encloses (∑ a, CA4_5_7I1R4Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I1R4P CA4_5_7I1R4Value CA4_5_7I1R4P_sound) (by decide +kernel)
def CA4_5_7I1R4MassTermLogWitness : LogWitness := ⟨-4, 1733273090106455195757138116287, 1250000000000000000000000000000⟩
def CA4_5_7I1R4MassTermLog : Ball := ⟨(-122286034647326346589745223372571 / 50000000000000000000000000000000), (52939559519 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I1R4MassTermLog_sound : CA4_5_7I1R4MassTermLog.Encloses (Real.log ((∑ a, CA4_5_7I1R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_5_7I1R4Mass_sound) (w := CA4_5_7I1R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_5_7I1R4MassTerm : Ball := ⟨(4239101863000727614975279320073 / 20000000000000000000000000000000), (2293967881 / 25000000000000000000000000000000)⟩
lemma CA4_5_7I1R4MassTerm_sound : CA4_5_7I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I1R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_5_7I1R4Mass_sound) CA4_5_7I1R4MassTermLog_sound) (by decide +kernel)
def CA4_5_7I1R4H : Ball := ⟨(4099569130609747587062653374779 / 50000000000000000000000000000000), (10244581851 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I1R4H_sound : CA4_5_7I1R4H.Encloses (homogeneousEntropy CA4_5_7I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I1R4Value CA4_5_7I1R4MassTerm_sound CA4_5_7I1R4Entropy_sound) (by decide +kernel)
def CA4_5_7I1R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 5 a
def CA4_5_7I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
lemma CA4_5_7I1R5Raw_sound (a : PairSlot) :
    (CA4_5_7I1R5Raw a).Encloses (CA4_5_7I1R5Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 5 a
def CA4_5_7I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(2102259875666009394668516601 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(21183979549643899692768589869 / 50000000000000000000000000000000), (14245479 / 100000000000000000000000000000000)⟩ ⟨(-100767653870255594718702589503333 / 10000000000000000000000000000000), (338813202711 / 100000000000000000000000000000000)⟩ ⟨-15, 2102259875666009394668516601, 1525878906250000000000000000⟩,
   .log ⟨(124142045552361735235235821983 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(830696376940791392993809008323 / 100000000000000000000000000000000), (289169131 / 100000000000000000000000000000000)⟩ ⟨(-669149902633441699371747479833533 / 100000000000000000000000000000000), (232934062929 / 100000000000000000000000000000000)⟩ ⟨-10, 124142045552361735235235821983, 97656250000000000000000000000⟩,
   .log ⟨(8713316072434631107206395521 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(81452714947394473747296396707 / 100000000000000000000000000000000), (13838379 / 50000000000000000000000000000000)⟩ ⟨(-934807302641959186552706162933163 / 100000000000000000000000000000000), (317637366721 / 100000000000000000000000000000000)⟩ ⟨-14, 8713316072434631107206395521, 6103515625000000000000000000⟩]
lemma CA4_5_7I1R5Certificates_valid :
    CA4_5_7I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 5 => 1
  | 2, 4 => 2
  | 3, 4 => 3
  | 4, 2 => 2
  | 4, 3 => 3
  | 5, 1 => 1
  | _, _ => 0
def CA4_5_7I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R5Certificates (CA4_5_7I1R5CertificateIndex a)).input
lemma CA4_5_7I1R5P_check : ∀ a : PairSlot, contains (CA4_5_7I1R5Raw a) (CA4_5_7I1R5P a) = true := by
  decide +kernel
lemma CA4_5_7I1R5P_sound (a : PairSlot) :
    (CA4_5_7I1R5P a).Encloses (CA4_5_7I1R5Value a) :=
  contains_sound (CA4_5_7I1R5Raw_sound a) (CA4_5_7I1R5P_check a)
def CA4_5_7I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R5Certificates (CA4_5_7I1R5CertificateIndex a)).output
lemma CA4_5_7I1R5Terms_sound (a : PairSlot) :
    (CA4_5_7I1R5Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I1R5Certificates_valid
    (CA4_5_7I1R5CertificateIndex a) (CA4_5_7I1R5P_sound a)
def CA4_5_7I1R5Entropy : Ball := ⟨(14914328921679276033228790387 / 781250000000000000000000000000), (41386421 / 6250000000000000000000000000000)⟩
lemma CA4_5_7I1R5Entropy_sound : CA4_5_7I1R5Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I1R5Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I1R5Value CA4_5_7I1R5Terms CA4_5_7I1R5Terms_sound) (by decide +kernel)
def CA4_5_7I1R5Mass : Ball := ⟨(68529940688064192565889625353 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
lemma CA4_5_7I1R5Mass_sound : CA4_5_7I1R5Mass.Encloses (∑ a, CA4_5_7I1R5Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I1R5P CA4_5_7I1R5Value CA4_5_7I1R5P_sound) (by decide +kernel)
def CA4_5_7I1R5MassTermLogWitness : LogWitness := ⟨-9, 68529940688064192565889625353, 48828125000000000000000000000⟩
def CA4_5_7I1R5MassTermLog : Ball := ⟨(-294968018187080496147774346415151 / 50000000000000000000000000000000), (211758240477 / 100000000000000000000000000000000)⟩
lemma CA4_5_7I1R5MassTermLog_sound : CA4_5_7I1R5MassTermLog.Encloses (Real.log ((∑ a, CA4_5_7I1R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_5_7I1R5Mass_sound) (w := CA4_5_7I1R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_5_7I1R5MassTerm : Ball := ⟨(80856563164945865771325579269 / 5000000000000000000000000000000), (290235623 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I1R5MassTerm_sound : CA4_5_7I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I1R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_5_7I1R5Mass_sound) CA4_5_7I1R5MassTermLog_sound) (by decide +kernel)
def CA4_5_7I1R5H : Ball := ⟨(72975709669007504206693396039 / 25000000000000000000000000000000), (621326991 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I1R5H_sound : CA4_5_7I1R5H.Encloses (homogeneousEntropy CA4_5_7I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I1R5Value CA4_5_7I1R5MassTerm_sound CA4_5_7I1R5Entropy_sound) (by decide +kernel)
def CA4_5_7I1R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 6 a
def CA4_5_7I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
lemma CA4_5_7I1R6Raw_sound (a : PairSlot) :
    (CA4_5_7I1R6Raw a).Encloses (CA4_5_7I1R6Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 6 a
def CA4_5_7I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_5_7I1R6Certificates_valid :
    CA4_5_7I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I1R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_5_7I1R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R6Certificates (CA4_5_7I1R6CertificateIndex a)).input
lemma CA4_5_7I1R6P_check : ∀ a : PairSlot, contains (CA4_5_7I1R6Raw a) (CA4_5_7I1R6P a) = true := by
  decide +kernel
lemma CA4_5_7I1R6P_sound (a : PairSlot) :
    (CA4_5_7I1R6P a).Encloses (CA4_5_7I1R6Value a) :=
  contains_sound (CA4_5_7I1R6Raw_sound a) (CA4_5_7I1R6P_check a)
def CA4_5_7I1R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R6Certificates (CA4_5_7I1R6CertificateIndex a)).output
lemma CA4_5_7I1R6Terms_sound (a : PairSlot) :
    (CA4_5_7I1R6Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I1R6Certificates_valid
    (CA4_5_7I1R6CertificateIndex a) (CA4_5_7I1R6P_sound a)
def CA4_5_7I1R6Entropy : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R6Entropy_sound : CA4_5_7I1R6Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I1R6Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I1R6Value CA4_5_7I1R6Terms CA4_5_7I1R6Terms_sound) (by decide +kernel)
def CA4_5_7I1R6Mass : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R6Mass_sound : CA4_5_7I1R6Mass.Encloses (∑ a, CA4_5_7I1R6Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I1R6P CA4_5_7I1R6Value CA4_5_7I1R6P_sound) (by decide +kernel)
def CA4_5_7I1R6MassTerm : Ball := .exact 0
lemma CA4_5_7I1R6MassTerm_sound : CA4_5_7I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I1R6Value a))) :=
  entropyTerm_zero_ball (CA4_5_7I1R6Mass_sound)
def CA4_5_7I1R6H : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R6H_sound : CA4_5_7I1R6H.Encloses (homogeneousEntropy CA4_5_7I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I1R6Value CA4_5_7I1R6MassTerm_sound CA4_5_7I1R6Entropy_sound) (by decide +kernel)
def CA4_5_7I1R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 7 a
def CA4_5_7I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
lemma CA4_5_7I1R7Raw_sound (a : PairSlot) :
    (CA4_5_7I1R7Raw a).Encloses (CA4_5_7I1R7Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 7 a
def CA4_5_7I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_5_7I1R7Certificates_valid :
    CA4_5_7I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I1R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_5_7I1R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R7Certificates (CA4_5_7I1R7CertificateIndex a)).input
lemma CA4_5_7I1R7P_check : ∀ a : PairSlot, contains (CA4_5_7I1R7Raw a) (CA4_5_7I1R7P a) = true := by
  decide +kernel
lemma CA4_5_7I1R7P_sound (a : PairSlot) :
    (CA4_5_7I1R7P a).Encloses (CA4_5_7I1R7Value a) :=
  contains_sound (CA4_5_7I1R7Raw_sound a) (CA4_5_7I1R7P_check a)
def CA4_5_7I1R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R7Certificates (CA4_5_7I1R7CertificateIndex a)).output
lemma CA4_5_7I1R7Terms_sound (a : PairSlot) :
    (CA4_5_7I1R7Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I1R7Certificates_valid
    (CA4_5_7I1R7CertificateIndex a) (CA4_5_7I1R7P_sound a)
def CA4_5_7I1R7Entropy : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R7Entropy_sound : CA4_5_7I1R7Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I1R7Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I1R7Value CA4_5_7I1R7Terms CA4_5_7I1R7Terms_sound) (by decide +kernel)
def CA4_5_7I1R7Mass : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R7Mass_sound : CA4_5_7I1R7Mass.Encloses (∑ a, CA4_5_7I1R7Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I1R7P CA4_5_7I1R7Value CA4_5_7I1R7P_sound) (by decide +kernel)
def CA4_5_7I1R7MassTerm : Ball := .exact 0
lemma CA4_5_7I1R7MassTerm_sound : CA4_5_7I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I1R7Value a))) :=
  entropyTerm_zero_ball (CA4_5_7I1R7Mass_sound)
def CA4_5_7I1R7H : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R7H_sound : CA4_5_7I1R7H.Encloses (homogeneousEntropy CA4_5_7I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I1R7Value CA4_5_7I1R7MassTerm_sound CA4_5_7I1R7Entropy_sound) (by decide +kernel)
def CA4_5_7I1R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 8 a
def CA4_5_7I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
lemma CA4_5_7I1R8Raw_sound (a : PairSlot) :
    (CA4_5_7I1R8Raw a).Encloses (CA4_5_7I1R8Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 8 a
def CA4_5_7I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_5_7I1R8Certificates_valid :
    CA4_5_7I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_5_7I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R8Certificates (CA4_5_7I1R8CertificateIndex a)).input
lemma CA4_5_7I1R8P_check : ∀ a : PairSlot, contains (CA4_5_7I1R8Raw a) (CA4_5_7I1R8P a) = true := by
  decide +kernel
lemma CA4_5_7I1R8P_sound (a : PairSlot) :
    (CA4_5_7I1R8P a).Encloses (CA4_5_7I1R8Value a) :=
  contains_sound (CA4_5_7I1R8Raw_sound a) (CA4_5_7I1R8P_check a)
def CA4_5_7I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R8Certificates (CA4_5_7I1R8CertificateIndex a)).output
lemma CA4_5_7I1R8Terms_sound (a : PairSlot) :
    (CA4_5_7I1R8Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I1R8Certificates_valid
    (CA4_5_7I1R8CertificateIndex a) (CA4_5_7I1R8P_sound a)
def CA4_5_7I1R8Entropy : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R8Entropy_sound : CA4_5_7I1R8Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I1R8Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I1R8Value CA4_5_7I1R8Terms CA4_5_7I1R8Terms_sound) (by decide +kernel)
def CA4_5_7I1R8Mass : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R8Mass_sound : CA4_5_7I1R8Mass.Encloses (∑ a, CA4_5_7I1R8Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I1R8P CA4_5_7I1R8Value CA4_5_7I1R8P_sound) (by decide +kernel)
def CA4_5_7I1R8MassTerm : Ball := .exact 0
lemma CA4_5_7I1R8MassTerm_sound : CA4_5_7I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I1R8Value a))) :=
  entropyTerm_zero_ball (CA4_5_7I1R8Mass_sound)
def CA4_5_7I1R8H : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R8H_sound : CA4_5_7I1R8H.Encloses (homogeneousEntropy CA4_5_7I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I1R8Value CA4_5_7I1R8MassTerm_sound CA4_5_7I1R8Entropy_sound) (by decide +kernel)
def CA4_5_7I1R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 9 a
def CA4_5_7I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
lemma CA4_5_7I1R9Raw_sound (a : PairSlot) :
    (CA4_5_7I1R9Raw a).Encloses (CA4_5_7I1R9Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 9 a
def CA4_5_7I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_5_7I1R9Certificates_valid :
    CA4_5_7I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_5_7I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R9Certificates (CA4_5_7I1R9CertificateIndex a)).input
lemma CA4_5_7I1R9P_check : ∀ a : PairSlot, contains (CA4_5_7I1R9Raw a) (CA4_5_7I1R9P a) = true := by
  decide +kernel
lemma CA4_5_7I1R9P_sound (a : PairSlot) :
    (CA4_5_7I1R9P a).Encloses (CA4_5_7I1R9Value a) :=
  contains_sound (CA4_5_7I1R9Raw_sound a) (CA4_5_7I1R9P_check a)
def CA4_5_7I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R9Certificates (CA4_5_7I1R9CertificateIndex a)).output
lemma CA4_5_7I1R9Terms_sound (a : PairSlot) :
    (CA4_5_7I1R9Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I1R9Certificates_valid
    (CA4_5_7I1R9CertificateIndex a) (CA4_5_7I1R9P_sound a)
def CA4_5_7I1R9Entropy : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R9Entropy_sound : CA4_5_7I1R9Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I1R9Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I1R9Value CA4_5_7I1R9Terms CA4_5_7I1R9Terms_sound) (by decide +kernel)
def CA4_5_7I1R9Mass : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R9Mass_sound : CA4_5_7I1R9Mass.Encloses (∑ a, CA4_5_7I1R9Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I1R9P CA4_5_7I1R9Value CA4_5_7I1R9P_sound) (by decide +kernel)
def CA4_5_7I1R9MassTerm : Ball := .exact 0
lemma CA4_5_7I1R9MassTerm_sound : CA4_5_7I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I1R9Value a))) :=
  entropyTerm_zero_ball (CA4_5_7I1R9Mass_sound)
def CA4_5_7I1R9H : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R9H_sound : CA4_5_7I1R9H.Encloses (homogeneousEntropy CA4_5_7I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I1R9Value CA4_5_7I1R9MassTerm_sound CA4_5_7I1R9Entropy_sound) (by decide +kernel)
def CA4_5_7I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA4_5_7I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
lemma CA4_5_7I1R10Raw_sound (a : PairSlot) :
    (CA4_5_7I1R10Raw a).Encloses (CA4_5_7I1R10Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 10 a
def CA4_5_7I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_5_7I1R10Certificates_valid :
    CA4_5_7I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_5_7I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R10Certificates (CA4_5_7I1R10CertificateIndex a)).input
lemma CA4_5_7I1R10P_check : ∀ a : PairSlot, contains (CA4_5_7I1R10Raw a) (CA4_5_7I1R10P a) = true := by
  decide +kernel
lemma CA4_5_7I1R10P_sound (a : PairSlot) :
    (CA4_5_7I1R10P a).Encloses (CA4_5_7I1R10Value a) :=
  contains_sound (CA4_5_7I1R10Raw_sound a) (CA4_5_7I1R10P_check a)
def CA4_5_7I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R10Certificates (CA4_5_7I1R10CertificateIndex a)).output
lemma CA4_5_7I1R10Terms_sound (a : PairSlot) :
    (CA4_5_7I1R10Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I1R10Certificates_valid
    (CA4_5_7I1R10CertificateIndex a) (CA4_5_7I1R10P_sound a)
def CA4_5_7I1R10Entropy : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R10Entropy_sound : CA4_5_7I1R10Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I1R10Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I1R10Value CA4_5_7I1R10Terms CA4_5_7I1R10Terms_sound) (by decide +kernel)
def CA4_5_7I1R10Mass : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R10Mass_sound : CA4_5_7I1R10Mass.Encloses (∑ a, CA4_5_7I1R10Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I1R10P CA4_5_7I1R10Value CA4_5_7I1R10P_sound) (by decide +kernel)
def CA4_5_7I1R10MassTerm : Ball := .exact 0
lemma CA4_5_7I1R10MassTerm_sound : CA4_5_7I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I1R10Value a))) :=
  entropyTerm_zero_ball (CA4_5_7I1R10Mass_sound)
def CA4_5_7I1R10H : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R10H_sound : CA4_5_7I1R10H.Encloses (homogeneousEntropy CA4_5_7I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I1R10Value CA4_5_7I1R10MassTerm_sound CA4_5_7I1R10Entropy_sound) (by decide +kernel)
def CA4_5_7I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA4_5_7I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
lemma CA4_5_7I1R11Raw_sound (a : PairSlot) :
    (CA4_5_7I1R11Raw a).Encloses (CA4_5_7I1R11Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 11 a
def CA4_5_7I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_5_7I1R11Certificates_valid :
    CA4_5_7I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_5_7I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R11Certificates (CA4_5_7I1R11CertificateIndex a)).input
lemma CA4_5_7I1R11P_check : ∀ a : PairSlot, contains (CA4_5_7I1R11Raw a) (CA4_5_7I1R11P a) = true := by
  decide +kernel
lemma CA4_5_7I1R11P_sound (a : PairSlot) :
    (CA4_5_7I1R11P a).Encloses (CA4_5_7I1R11Value a) :=
  contains_sound (CA4_5_7I1R11Raw_sound a) (CA4_5_7I1R11P_check a)
def CA4_5_7I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R11Certificates (CA4_5_7I1R11CertificateIndex a)).output
lemma CA4_5_7I1R11Terms_sound (a : PairSlot) :
    (CA4_5_7I1R11Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I1R11Certificates_valid
    (CA4_5_7I1R11CertificateIndex a) (CA4_5_7I1R11P_sound a)
def CA4_5_7I1R11Entropy : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R11Entropy_sound : CA4_5_7I1R11Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I1R11Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I1R11Value CA4_5_7I1R11Terms CA4_5_7I1R11Terms_sound) (by decide +kernel)
def CA4_5_7I1R11Mass : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R11Mass_sound : CA4_5_7I1R11Mass.Encloses (∑ a, CA4_5_7I1R11Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I1R11P CA4_5_7I1R11Value CA4_5_7I1R11P_sound) (by decide +kernel)
def CA4_5_7I1R11MassTerm : Ball := .exact 0
lemma CA4_5_7I1R11MassTerm_sound : CA4_5_7I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I1R11Value a))) :=
  entropyTerm_zero_ball (CA4_5_7I1R11Mass_sound)
def CA4_5_7I1R11H : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R11H_sound : CA4_5_7I1R11H.Encloses (homogeneousEntropy CA4_5_7I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I1R11Value CA4_5_7I1R11MassTerm_sound CA4_5_7I1R11Entropy_sound) (by decide +kernel)
def CA4_5_7I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA4_5_7I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
lemma CA4_5_7I1R12Raw_sound (a : PairSlot) :
    (CA4_5_7I1R12Raw a).Encloses (CA4_5_7I1R12Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 12 a
def CA4_5_7I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_5_7I1R12Certificates_valid :
    CA4_5_7I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_5_7I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R12Certificates (CA4_5_7I1R12CertificateIndex a)).input
lemma CA4_5_7I1R12P_check : ∀ a : PairSlot, contains (CA4_5_7I1R12Raw a) (CA4_5_7I1R12P a) = true := by
  decide +kernel
lemma CA4_5_7I1R12P_sound (a : PairSlot) :
    (CA4_5_7I1R12P a).Encloses (CA4_5_7I1R12Value a) :=
  contains_sound (CA4_5_7I1R12Raw_sound a) (CA4_5_7I1R12P_check a)
def CA4_5_7I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R12Certificates (CA4_5_7I1R12CertificateIndex a)).output
lemma CA4_5_7I1R12Terms_sound (a : PairSlot) :
    (CA4_5_7I1R12Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I1R12Certificates_valid
    (CA4_5_7I1R12CertificateIndex a) (CA4_5_7I1R12P_sound a)
def CA4_5_7I1R12Entropy : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R12Entropy_sound : CA4_5_7I1R12Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I1R12Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I1R12Value CA4_5_7I1R12Terms CA4_5_7I1R12Terms_sound) (by decide +kernel)
def CA4_5_7I1R12Mass : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R12Mass_sound : CA4_5_7I1R12Mass.Encloses (∑ a, CA4_5_7I1R12Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I1R12P CA4_5_7I1R12Value CA4_5_7I1R12P_sound) (by decide +kernel)
def CA4_5_7I1R12MassTerm : Ball := .exact 0
lemma CA4_5_7I1R12MassTerm_sound : CA4_5_7I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I1R12Value a))) :=
  entropyTerm_zero_ball (CA4_5_7I1R12Mass_sound)
def CA4_5_7I1R12H : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R12H_sound : CA4_5_7I1R12H.Encloses (homogeneousEntropy CA4_5_7I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I1R12Value CA4_5_7I1R12MassTerm_sound CA4_5_7I1R12Entropy_sound) (by decide +kernel)
def CA4_5_7I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA4_5_7I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
lemma CA4_5_7I1R13Raw_sound (a : PairSlot) :
    (CA4_5_7I1R13Raw a).Encloses (CA4_5_7I1R13Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 13 a
def CA4_5_7I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_5_7I1R13Certificates_valid :
    CA4_5_7I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_5_7I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R13Certificates (CA4_5_7I1R13CertificateIndex a)).input
lemma CA4_5_7I1R13P_check : ∀ a : PairSlot, contains (CA4_5_7I1R13Raw a) (CA4_5_7I1R13P a) = true := by
  decide +kernel
lemma CA4_5_7I1R13P_sound (a : PairSlot) :
    (CA4_5_7I1R13P a).Encloses (CA4_5_7I1R13Value a) :=
  contains_sound (CA4_5_7I1R13Raw_sound a) (CA4_5_7I1R13P_check a)
def CA4_5_7I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R13Certificates (CA4_5_7I1R13CertificateIndex a)).output
lemma CA4_5_7I1R13Terms_sound (a : PairSlot) :
    (CA4_5_7I1R13Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I1R13Certificates_valid
    (CA4_5_7I1R13CertificateIndex a) (CA4_5_7I1R13P_sound a)
def CA4_5_7I1R13Entropy : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R13Entropy_sound : CA4_5_7I1R13Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I1R13Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I1R13Value CA4_5_7I1R13Terms CA4_5_7I1R13Terms_sound) (by decide +kernel)
def CA4_5_7I1R13Mass : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R13Mass_sound : CA4_5_7I1R13Mass.Encloses (∑ a, CA4_5_7I1R13Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I1R13P CA4_5_7I1R13Value CA4_5_7I1R13P_sound) (by decide +kernel)
def CA4_5_7I1R13MassTerm : Ball := .exact 0
lemma CA4_5_7I1R13MassTerm_sound : CA4_5_7I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I1R13Value a))) :=
  entropyTerm_zero_ball (CA4_5_7I1R13Mass_sound)
def CA4_5_7I1R13H : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R13H_sound : CA4_5_7I1R13H.Encloses (homogeneousEntropy CA4_5_7I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I1R13Value CA4_5_7I1R13MassTerm_sound CA4_5_7I1R13Entropy_sound) (by decide +kernel)
def CA4_5_7I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA4_5_7I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
lemma CA4_5_7I1R14Raw_sound (a : PairSlot) :
    (CA4_5_7I1R14Raw a).Encloses (CA4_5_7I1R14Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 14 a
def CA4_5_7I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_5_7I1R14Certificates_valid :
    CA4_5_7I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_5_7I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R14Certificates (CA4_5_7I1R14CertificateIndex a)).input
lemma CA4_5_7I1R14P_check : ∀ a : PairSlot, contains (CA4_5_7I1R14Raw a) (CA4_5_7I1R14P a) = true := by
  decide +kernel
lemma CA4_5_7I1R14P_sound (a : PairSlot) :
    (CA4_5_7I1R14P a).Encloses (CA4_5_7I1R14Value a) :=
  contains_sound (CA4_5_7I1R14Raw_sound a) (CA4_5_7I1R14P_check a)
def CA4_5_7I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R14Certificates (CA4_5_7I1R14CertificateIndex a)).output
lemma CA4_5_7I1R14Terms_sound (a : PairSlot) :
    (CA4_5_7I1R14Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I1R14Certificates_valid
    (CA4_5_7I1R14CertificateIndex a) (CA4_5_7I1R14P_sound a)
def CA4_5_7I1R14Entropy : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R14Entropy_sound : CA4_5_7I1R14Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I1R14Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I1R14Value CA4_5_7I1R14Terms CA4_5_7I1R14Terms_sound) (by decide +kernel)
def CA4_5_7I1R14Mass : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R14Mass_sound : CA4_5_7I1R14Mass.Encloses (∑ a, CA4_5_7I1R14Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I1R14P CA4_5_7I1R14Value CA4_5_7I1R14P_sound) (by decide +kernel)
def CA4_5_7I1R14MassTerm : Ball := .exact 0
lemma CA4_5_7I1R14MassTerm_sound : CA4_5_7I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I1R14Value a))) :=
  entropyTerm_zero_ball (CA4_5_7I1R14Mass_sound)
def CA4_5_7I1R14H : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R14H_sound : CA4_5_7I1R14H.Encloses (homogeneousEntropy CA4_5_7I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I1R14Value CA4_5_7I1R14MassTerm_sound CA4_5_7I1R14Entropy_sound) (by decide +kernel)
def CA4_5_7I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA4_5_7I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
lemma CA4_5_7I1R15Raw_sound (a : PairSlot) :
    (CA4_5_7I1R15Raw a).Encloses (CA4_5_7I1R15Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 15 a
def CA4_5_7I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_5_7I1R15Certificates_valid :
    CA4_5_7I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_5_7I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R15Certificates (CA4_5_7I1R15CertificateIndex a)).input
lemma CA4_5_7I1R15P_check : ∀ a : PairSlot, contains (CA4_5_7I1R15Raw a) (CA4_5_7I1R15P a) = true := by
  decide +kernel
lemma CA4_5_7I1R15P_sound (a : PairSlot) :
    (CA4_5_7I1R15P a).Encloses (CA4_5_7I1R15Value a) :=
  contains_sound (CA4_5_7I1R15Raw_sound a) (CA4_5_7I1R15P_check a)
def CA4_5_7I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R15Certificates (CA4_5_7I1R15CertificateIndex a)).output
lemma CA4_5_7I1R15Terms_sound (a : PairSlot) :
    (CA4_5_7I1R15Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I1R15Certificates_valid
    (CA4_5_7I1R15CertificateIndex a) (CA4_5_7I1R15P_sound a)
def CA4_5_7I1R15Entropy : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R15Entropy_sound : CA4_5_7I1R15Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I1R15Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I1R15Value CA4_5_7I1R15Terms CA4_5_7I1R15Terms_sound) (by decide +kernel)
def CA4_5_7I1R15Mass : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R15Mass_sound : CA4_5_7I1R15Mass.Encloses (∑ a, CA4_5_7I1R15Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I1R15P CA4_5_7I1R15Value CA4_5_7I1R15P_sound) (by decide +kernel)
def CA4_5_7I1R15MassTerm : Ball := .exact 0
lemma CA4_5_7I1R15MassTerm_sound : CA4_5_7I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I1R15Value a))) :=
  entropyTerm_zero_ball (CA4_5_7I1R15Mass_sound)
def CA4_5_7I1R15H : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R15H_sound : CA4_5_7I1R15H.Encloses (homogeneousEntropy CA4_5_7I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I1R15Value CA4_5_7I1R15MassTerm_sound CA4_5_7I1R15Entropy_sound) (by decide +kernel)
def CA4_5_7I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA4_5_7I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
lemma CA4_5_7I1R16Raw_sound (a : PairSlot) :
    (CA4_5_7I1R16Raw a).Encloses (CA4_5_7I1R16Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 16 a
def CA4_5_7I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_5_7I1R16Certificates_valid :
    CA4_5_7I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_5_7I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R16Certificates (CA4_5_7I1R16CertificateIndex a)).input
lemma CA4_5_7I1R16P_check : ∀ a : PairSlot, contains (CA4_5_7I1R16Raw a) (CA4_5_7I1R16P a) = true := by
  decide +kernel
lemma CA4_5_7I1R16P_sound (a : PairSlot) :
    (CA4_5_7I1R16P a).Encloses (CA4_5_7I1R16Value a) :=
  contains_sound (CA4_5_7I1R16Raw_sound a) (CA4_5_7I1R16P_check a)
def CA4_5_7I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I1R16Certificates (CA4_5_7I1R16CertificateIndex a)).output
lemma CA4_5_7I1R16Terms_sound (a : PairSlot) :
    (CA4_5_7I1R16Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I1R16Certificates_valid
    (CA4_5_7I1R16CertificateIndex a) (CA4_5_7I1R16P_sound a)
def CA4_5_7I1R16Entropy : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R16Entropy_sound : CA4_5_7I1R16Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I1R16Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I1R16Value CA4_5_7I1R16Terms CA4_5_7I1R16Terms_sound) (by decide +kernel)
def CA4_5_7I1R16Mass : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R16Mass_sound : CA4_5_7I1R16Mass.Encloses (∑ a, CA4_5_7I1R16Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I1R16P CA4_5_7I1R16Value CA4_5_7I1R16P_sound) (by decide +kernel)
def CA4_5_7I1R16MassTerm : Ball := .exact 0
lemma CA4_5_7I1R16MassTerm_sound : CA4_5_7I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I1R16Value a))) :=
  entropyTerm_zero_ball (CA4_5_7I1R16Mass_sound)
def CA4_5_7I1R16H : Ball := ⟨0, 0⟩
lemma CA4_5_7I1R16H_sound : CA4_5_7I1R16H.Encloses (homogeneousEntropy CA4_5_7I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I1R16Value CA4_5_7I1R16MassTerm_sound CA4_5_7I1R16Entropy_sound) (by decide +kernel)
def CA4_5_7I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA4_5_7I1R0H
  | 1 => CA4_5_7I1R1H
  | 2 => CA4_5_7I1R2H
  | 3 => CA4_5_7I1R3H
  | 4 => CA4_5_7I1R4H
  | 5 => CA4_5_7I1R5H
  | 6 => CA4_5_7I1R6H
  | 7 => CA4_5_7I1R7H
  | 8 => CA4_5_7I1R8H
  | 9 => CA4_5_7I1R9H
  | 10 => CA4_5_7I1R10H
  | 11 => CA4_5_7I1R11H
  | 12 => CA4_5_7I1R12H
  | 13 => CA4_5_7I1R13H
  | 14 => CA4_5_7I1R14H
  | 15 => CA4_5_7I1R15H
  | 16 => CA4_5_7I1R16H
  | _ => (.exact 0)
lemma CA4_5_7I1ResidualEntropies_sound (k : Fin 17) :
    (CA4_5_7I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CA4_5_7I1R0H_sound
  · exact CA4_5_7I1R1H_sound
  · exact CA4_5_7I1R2H_sound
  · exact CA4_5_7I1R3H_sound
  · exact CA4_5_7I1R4H_sound
  · exact CA4_5_7I1R5H_sound
  · exact CA4_5_7I1R6H_sound
  · exact CA4_5_7I1R7H_sound
  · exact CA4_5_7I1R8H_sound
  · exact CA4_5_7I1R9H_sound
  · exact CA4_5_7I1R10H_sound
  · exact CA4_5_7I1R11H_sound
  · exact CA4_5_7I1R12H_sound
  · exact CA4_5_7I1R13H_sound
  · exact CA4_5_7I1R14H_sound
  · exact CA4_5_7I1R15H_sound
  · exact CA4_5_7I1R16H_sound
def CA4_5_7I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 3, 5, 0 => Z3_5_0H1H
  | 4, 4, 0 => Z4_4_0H1H
  | _, _, _ => (.exact 0)
lemma CA4_5_7I1Singles_sound (u : Shape) (hu : u ∈ below (shape 4 5 7))
    (hd : designated (Equiv.refl (Fin 3)) 1 u) :
    (CA4_5_7I1Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) u)) := by
  rw [A4_5_7_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 4 0 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 4 1 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 4 2 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 4 3 1) by decide +kernel) hd |>.elim
  · exact Z4_4_0H1H_sound
def CA4_5_7I1Singleton : Ball := ⟨(303183391302263079046188083 / 50000000000000000000000000000000), (251569 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I1Singleton_sound : CA4_5_7I1Singleton.Encloses
    (singletonEntropy (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1
    CA4_5_7I1Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_5_7Law_sound u) CA4_5_7I1Singles_sound) (by decide +kernel)
def CA4_5_7I1Group : Ball := ⟨(50009940225896612102999470955347 / 50000000000000000000000000000000), (83559113207 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I1Group_sound : CA4_5_7I1Group.Encloses
    (groupedEntropy (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA4_5_7I1Singleton_sound
    (finSumBall_sound 17 CA4_5_7I1ResidualEntropies _ CA4_5_7I1ResidualEntropies_sound)) (by decide +kernel)

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
def CA4_5_7I1H : Ball := ⟨(3710174631598816941952092861339 / 3125000000000000000000000000000), (96993767119 / 20000000000000000000000000000000)⟩
lemma CA4_5_7I1_sound : CA4_5_7I1H.Encloses (stageACapacity (shape 4 5 7) 1) := by
  have hb := contains_sound (Ball.add_sound CA4_5_7I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA4_5_7I1Group_sound)))
    (show contains (.add CA4_5_7I1PairH (.neg (.mul (.exact 2) CA4_5_7I1Group))) CA4_5_7I1H = true by decide +kernel)
  unfold CA4_5_7I1PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
