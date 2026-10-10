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
def CA2_2_12I2PairValue (a : PairSlot × PairSlot) : ℝ := pairLaw (below (shape 2 2 12)) (shape 2 2 12) (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) a
def CA2_2_12I2PairRaw (a : PairSlot × PairSlot) : Ball := stageAPairBall (shape 2 2 12) A2_2_12Law 2 a
lemma CA2_2_12I2PairRaw_sound (a : PairSlot × PairSlot) :
    (CA2_2_12I2PairRaw a).Encloses (CA2_2_12I2PairValue a) := by
  exact stageAPairBall_sound (shape 2 2 12) (by decide +kernel) A2_2_12Law (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (fun u _ => A2_2_12Law_sound u) 2 a
def CA2_2_12I2PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(110546059455540355306581711 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(47380208567494042334297599 / 3125000000000000000000000000000), (98321 / 20000000000000000000000000000000)⟩ ⟨(-685762424109556084673323391669271 / 50000000000000000000000000000000), (444693201943 / 100000000000000000000000000000000)⟩ ⟨-20, 110546059455540355306581711, 95367431640625000000000000⟩,
   .log ⟨(37446908756512204496871500049 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(295456158830945190165451277953 / 100000000000000000000000000000000), (103085997 / 100000000000000000000000000000000)⟩ ⟨(-394500065081558819202461862021939 / 50000000000000000000000000000000), (275285710549 / 100000000000000000000000000000000)⟩ ⟨-12, 37446908756512204496871500049, 24414062500000000000000000000⟩,
   .log ⟨(389801076500725599121299973679 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(2162339191205464455787627598227 / 100000000000000000000000000000000), (412717957 / 50000000000000000000000000000000)⟩ ⟨(-554728891622606729210614912321173 / 100000000000000000000000000000000), (6617444933 / 3125000000000000000000000000000)⟩ ⟨-9, 389801076500725599121299973679, 195312500000000000000000000000⟩,
   .log ⟨(8026577649666181438563019887 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(70128369800682554750220086371 / 50000000000000000000000000000000), (47591441 / 100000000000000000000000000000000)⟩ ⟨(-873702004285713652968556505794723 / 100000000000000000000000000000000), (296461537791 / 100000000000000000000000000000000)⟩ ⟨-13, 8026577649666181438563019887, 6103515625000000000000000000⟩,
   .log ⟨(1590344396020470775076345577 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(4392918816935459876190947519 / 25000000000000000000000000000000), (2862539 / 50000000000000000000000000000000)⟩ ⟨(-220979497418440407109869188274747 / 20000000000000000000000000000000), (35998906549 / 10000000000000000000000000000000)⟩ ⟨-16, 1590344396020470775076345577, 1525878906250000000000000000⟩,
   .log ⟨(4110672278428271414847386989 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(38665771458076961788731966569 / 50000000000000000000000000000000), (26114073 / 100000000000000000000000000000000)⟩ ⟨(-58788698111779635346110901689581 / 6250000000000000000000000000000), (19852335463 / 6250000000000000000000000000000)⟩ ⟨-14, 4110672278428271414847386989, 3051757812500000000000000000⟩,
   .log ⟨(4840897131347966399403049539407 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩ ⟨(732928799013791158931189995359 / 5000000000000000000000000000000), (6150599157 / 100000000000000000000000000000000)⟩ ⟨(-302807012471964806975055731973201 / 100000000000000000000000000000000), (25410988531 / 20000000000000000000000000000000)⟩ ⟨-5, 4840897131347966399403049539407, 3125000000000000000000000000000⟩,
   .log ⟨(45418278816314022048019714781 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1146487519340282309425416626921 / 100000000000000000000000000000000), (21158929 / 5000000000000000000000000000000)⟩ ⟨(-631071646273212383038481202529713 / 100000000000000000000000000000000), (232934061613 / 100000000000000000000000000000000)⟩ ⟨-10, 45418278816314022048019714781, 24414062500000000000000000000⟩,
   .log ⟨(649229789077578320289369905301 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩ ⟨(5640497453697866229522802590111 / 100000000000000000000000000000000), (1099838073 / 50000000000000000000000000000000)⟩ ⟨(-217199578199879360886448447234481 / 50000000000000000000000000000000), (169406590311 / 100000000000000000000000000000000)⟩ ⟨-7, 649229789077578320289369905301, 390625000000000000000000000000⟩,
   .log ⟨(105419018849959486327554935579 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(722645518909666967360976101907 / 100000000000000000000000000000000), (122778409 / 50000000000000000000000000000000)⟩ ⟨(-685498240064434718339794611312457 / 100000000000000000000000000000000), (232934062409 / 100000000000000000000000000000000)⟩ ⟨-10, 105419018849959486327554935579, 97656250000000000000000000000⟩,
   .log ⟨(3895484149800359315890583610359 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩ ⟨(12642218110375323571676249971519 / 100000000000000000000000000000000), (2474702623 / 50000000000000000000000000000000)⟩ ⟨(-324535221405617268597189220326917 / 100000000000000000000000000000000), (12705494279 / 10000000000000000000000000000000)⟩ ⟨-5, 3895484149800359315890583610359, 3125000000000000000000000000000⟩,
   .log ⟨(133968602120849285361327349 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(40144247651491939790634595767 / 50000000000000000000000000000000), (851069 / 3125000000000000000000000000000)⟩ ⟨(-936419220062822767252056947869411 / 100000000000000000000000000000000), (79409341727 / 25000000000000000000000000000000)⟩ ⟨-14, 133968602120849285361327349, 95367431640625000000000000⟩,
   .log ⟨(37126782027156281050057118179 / 12500000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1728369120996635891968983074791 / 100000000000000000000000000000000), (314476087 / 50000000000000000000000000000000)⟩ ⟨(-145478633164701118276404567650121 / 25000000000000000000000000000000), (2646977973 / 1250000000000000000000000000000)⟩ ⟨-9, 37126782027156281050057118179, 24414062500000000000000000000⟩,
   .log ⟨(17957480969375498529369692371871 / 50000000000000000000000000000000), (11 / 10000000000000000000000000000000)⟩ ⟨(7355500642950349931271796463037 / 20000000000000000000000000000000), (22815867271 / 100000000000000000000000000000000)⟩ ⟨(-102401621022101378049862349468687 / 100000000000000000000000000000000), (12705494271 / 20000000000000000000000000000000)⟩ ⟨-2, 17957480969375498529369692371871, 12500000000000000000000000000000⟩]
lemma CA2_2_12I2PairCertificates_valid :
    CA2_2_12I2PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_2_12I2PairCertificateIndex (a : PairSlot × PairSlot) : ℕ :=
  match a.1.1.val, a.1.2.val, a.2.1.val, a.2.2.val with
  | 5, 5, 5, 0 => 1
  | 5, 5, 4, 1 => 2
  | 5, 5, 2, 2 => 3
  | 5, 5, 2, 3 => 4
  | 5, 5, 3, 2 => 4
  | 5, 5, 3, 3 => 5
  | 5, 5, 1, 4 => 2
  | 5, 5, 0, 5 => 1
  | 4, 5, 5, 1 => 6
  | 4, 5, 4, 2 => 7
  | 4, 5, 4, 3 => 8
  | 4, 5, 2, 4 => 7
  | 4, 5, 3, 4 => 8
  | 4, 5, 1, 5 => 6
  | 5, 4, 5, 1 => 6
  | 5, 4, 4, 2 => 7
  | 5, 4, 4, 3 => 8
  | 5, 4, 2, 4 => 7
  | 5, 4, 3, 4 => 8
  | 5, 4, 1, 5 => 6
  | 2, 5, 2, 5 => 9
  | 2, 5, 3, 5 => 10
  | 2, 5, 4, 4 => 11
  | 2, 5, 5, 2 => 9
  | 2, 5, 5, 3 => 10
  | 3, 5, 2, 5 => 10
  | 3, 5, 3, 5 => 12
  | 3, 5, 4, 4 => 13
  | 3, 5, 5, 2 => 10
  | 3, 5, 5, 3 => 12
  | 4, 4, 2, 5 => 11
  | 4, 4, 3, 5 => 13
  | 4, 4, 4, 4 => 14
  | 4, 4, 5, 2 => 11
  | 4, 4, 5, 3 => 13
  | 5, 2, 2, 5 => 9
  | 5, 2, 3, 5 => 10
  | 5, 2, 4, 4 => 11
  | 5, 2, 5, 2 => 9
  | 5, 2, 5, 3 => 10
  | 5, 3, 2, 5 => 10
  | 5, 3, 3, 5 => 12
  | 5, 3, 4, 4 => 13
  | 5, 3, 5, 2 => 10
  | 5, 3, 5, 3 => 12
  | 5, 1, 4, 5 => 6
  | 5, 1, 5, 4 => 6
  | 4, 2, 4, 5 => 7
  | 4, 2, 5, 4 => 7
  | 4, 3, 4, 5 => 8
  | 4, 3, 5, 4 => 8
  | 2, 4, 4, 5 => 7
  | 2, 4, 5, 4 => 7
  | 3, 4, 4, 5 => 8
  | 3, 4, 5, 4 => 8
  | 1, 5, 4, 5 => 6
  | 1, 5, 5, 4 => 6
  | 5, 0, 5, 5 => 1
  | 4, 1, 5, 5 => 2
  | 2, 2, 5, 5 => 3
  | 2, 3, 5, 5 => 4
  | 3, 2, 5, 5 => 4
  | 3, 3, 5, 5 => 5
  | 1, 4, 5, 5 => 2
  | 0, 5, 5, 5 => 1
  | _, _, _, _ => 0
def CA2_2_12I2PairP (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2PairCertificates (CA2_2_12I2PairCertificateIndex a)).input
lemma CA2_2_12I2PairP_check_0_0 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((0,0),(k,l))) (CA2_2_12I2PairP ((0,0),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_0_1 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((0,1),(k,l))) (CA2_2_12I2PairP ((0,1),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_0_2 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((0,2),(k,l))) (CA2_2_12I2PairP ((0,2),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_0_3 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((0,3),(k,l))) (CA2_2_12I2PairP ((0,3),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_0_4 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((0,4),(k,l))) (CA2_2_12I2PairP ((0,4),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_0_5 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((0,5),(k,l))) (CA2_2_12I2PairP ((0,5),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_1_0 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((1,0),(k,l))) (CA2_2_12I2PairP ((1,0),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_1_1 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((1,1),(k,l))) (CA2_2_12I2PairP ((1,1),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_1_2 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((1,2),(k,l))) (CA2_2_12I2PairP ((1,2),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_1_3 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((1,3),(k,l))) (CA2_2_12I2PairP ((1,3),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_1_4 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((1,4),(k,l))) (CA2_2_12I2PairP ((1,4),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_1_5 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((1,5),(k,l))) (CA2_2_12I2PairP ((1,5),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_2_0 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((2,0),(k,l))) (CA2_2_12I2PairP ((2,0),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_2_1 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((2,1),(k,l))) (CA2_2_12I2PairP ((2,1),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_2_2 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((2,2),(k,l))) (CA2_2_12I2PairP ((2,2),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_2_3 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((2,3),(k,l))) (CA2_2_12I2PairP ((2,3),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_2_4 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((2,4),(k,l))) (CA2_2_12I2PairP ((2,4),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_2_5 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((2,5),(k,l))) (CA2_2_12I2PairP ((2,5),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_3_0 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((3,0),(k,l))) (CA2_2_12I2PairP ((3,0),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_3_1 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((3,1),(k,l))) (CA2_2_12I2PairP ((3,1),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_3_2 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((3,2),(k,l))) (CA2_2_12I2PairP ((3,2),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_3_3 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((3,3),(k,l))) (CA2_2_12I2PairP ((3,3),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_3_4 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((3,4),(k,l))) (CA2_2_12I2PairP ((3,4),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_3_5 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((3,5),(k,l))) (CA2_2_12I2PairP ((3,5),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_4_0 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((4,0),(k,l))) (CA2_2_12I2PairP ((4,0),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_4_1 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((4,1),(k,l))) (CA2_2_12I2PairP ((4,1),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_4_2 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((4,2),(k,l))) (CA2_2_12I2PairP ((4,2),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_4_3 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((4,3),(k,l))) (CA2_2_12I2PairP ((4,3),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_4_4 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((4,4),(k,l))) (CA2_2_12I2PairP ((4,4),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_4_5 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((4,5),(k,l))) (CA2_2_12I2PairP ((4,5),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_5_0 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((5,0),(k,l))) (CA2_2_12I2PairP ((5,0),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_5_1 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((5,1),(k,l))) (CA2_2_12I2PairP ((5,1),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_5_2 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((5,2),(k,l))) (CA2_2_12I2PairP ((5,2),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_5_3 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((5,3),(k,l))) (CA2_2_12I2PairP ((5,3),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_5_4 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((5,4),(k,l))) (CA2_2_12I2PairP ((5,4),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check_5_5 : ∀ k l : Fin 6, contains (CA2_2_12I2PairRaw ((5,5),(k,l))) (CA2_2_12I2PairP ((5,5),(k,l))) = true := by
  decide +kernel
lemma CA2_2_12I2PairP_check (a : PairSlot × PairSlot) : contains (CA2_2_12I2PairRaw a) (CA2_2_12I2PairP a) = true := by
  rcases a with ⟨⟨i,j⟩,⟨k,l⟩⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (CA2_2_12I2PairP_check_0_0 k l) (CA2_2_12I2PairP_check_0_1 k l) (CA2_2_12I2PairP_check_0_2 k l) (CA2_2_12I2PairP_check_0_3 k l) (CA2_2_12I2PairP_check_0_4 k l) (CA2_2_12I2PairP_check_0_5 k l)
  · exact forall_fin6 (CA2_2_12I2PairP_check_1_0 k l) (CA2_2_12I2PairP_check_1_1 k l) (CA2_2_12I2PairP_check_1_2 k l) (CA2_2_12I2PairP_check_1_3 k l) (CA2_2_12I2PairP_check_1_4 k l) (CA2_2_12I2PairP_check_1_5 k l)
  · exact forall_fin6 (CA2_2_12I2PairP_check_2_0 k l) (CA2_2_12I2PairP_check_2_1 k l) (CA2_2_12I2PairP_check_2_2 k l) (CA2_2_12I2PairP_check_2_3 k l) (CA2_2_12I2PairP_check_2_4 k l) (CA2_2_12I2PairP_check_2_5 k l)
  · exact forall_fin6 (CA2_2_12I2PairP_check_3_0 k l) (CA2_2_12I2PairP_check_3_1 k l) (CA2_2_12I2PairP_check_3_2 k l) (CA2_2_12I2PairP_check_3_3 k l) (CA2_2_12I2PairP_check_3_4 k l) (CA2_2_12I2PairP_check_3_5 k l)
  · exact forall_fin6 (CA2_2_12I2PairP_check_4_0 k l) (CA2_2_12I2PairP_check_4_1 k l) (CA2_2_12I2PairP_check_4_2 k l) (CA2_2_12I2PairP_check_4_3 k l) (CA2_2_12I2PairP_check_4_4 k l) (CA2_2_12I2PairP_check_4_5 k l)
  · exact forall_fin6 (CA2_2_12I2PairP_check_5_0 k l) (CA2_2_12I2PairP_check_5_1 k l) (CA2_2_12I2PairP_check_5_2 k l) (CA2_2_12I2PairP_check_5_3 k l) (CA2_2_12I2PairP_check_5_4 k l) (CA2_2_12I2PairP_check_5_5 k l)
lemma CA2_2_12I2PairP_sound (a : PairSlot × PairSlot) :
    (CA2_2_12I2PairP a).Encloses (CA2_2_12I2PairValue a) :=
  contains_sound (CA2_2_12I2PairRaw_sound a) (CA2_2_12I2PairP_check a)
def CA2_2_12I2PairTerms (a : PairSlot × PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2PairCertificates (CA2_2_12I2PairCertificateIndex a)).output
lemma CA2_2_12I2PairTerms_sound (a : PairSlot × PairSlot) :
    (CA2_2_12I2PairTerms a).Encloses (Foundation.entropyTerm (CA2_2_12I2PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_2_12I2PairCertificates_valid
    (CA2_2_12I2PairCertificateIndex a) (CA2_2_12I2PairP_sound a)
def CA2_2_12I2PairEntropy : Ball := ⟨(256092058421150692005924592852231 / 100000000000000000000000000000000), (111067525547 / 100000000000000000000000000000000)⟩
lemma CA2_2_12I2PairEntropy_sound : CA2_2_12I2PairEntropy.Encloses (Foundation.finiteEntropy CA2_2_12I2PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA2_2_12I2PairValue CA2_2_12I2PairTerms CA2_2_12I2PairTerms_sound) (by decide +kernel)
def CA2_2_12I2PairMass : Ball := ⟨(10000000000000000000000000000001 / 10000000000000000000000000000000), (139 / 25000000000000000000000000000000)⟩
lemma CA2_2_12I2PairMass_sound : CA2_2_12I2PairMass.Encloses (∑ a, CA2_2_12I2PairValue a) := by
  exact contains_sound (doublePairSumBall_sound CA2_2_12I2PairP CA2_2_12I2PairValue CA2_2_12I2PairP_sound) (by decide +kernel)
def CA2_2_12I2PairMassTermLogWitness : LogWitness := ⟨0, 10000000000000000000000000000001, 10000000000000000000000000000000⟩
def CA2_2_12I2PairMassTermLog : Ball := ⟨(1 / 10000000000000000000000000000000), (10587912119 / 50000000000000000000000000000000)⟩
lemma CA2_2_12I2PairMassTermLog_sound : CA2_2_12I2PairMassTermLog.Encloses (Real.log ((∑ a, CA2_2_12I2PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_2_12I2PairMass_sound) (w := CA2_2_12I2PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_2_12I2PairMassTerm : Ball := ⟨(-1 / 10000000000000000000000000000000), (21175824239 / 100000000000000000000000000000000)⟩
lemma CA2_2_12I2PairMassTerm_sound : CA2_2_12I2PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_2_12I2PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA2_2_12I2PairMass_sound) CA2_2_12I2PairMassTermLog_sound) (by decide +kernel)
def CA2_2_12I2PairH : Ball := ⟨(256092058421150692005924592852241 / 100000000000000000000000000000000), (66121674893 / 50000000000000000000000000000000)⟩
lemma CA2_2_12I2PairH_sound : CA2_2_12I2PairH.Encloses (homogeneousEntropy CA2_2_12I2PairValue) := by
  exact contains_sound (homogeneous_enclosed CA2_2_12I2PairValue CA2_2_12I2PairMassTerm_sound CA2_2_12I2PairEntropy_sound) (by decide +kernel)

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
def CA2_2_12I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 2 12)) (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA2_2_12I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
lemma CA2_2_12I2R0Raw_sound (a : PairSlot) :
    (CA2_2_12I2R0Raw a).Encloses (CA2_2_12I2R0Value a) := by
  exact residualBall_sound_on (below (shape 2 2 12)) A2_2_12Law (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_2_12Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 2 12) (show (shape 2 2 12) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 0 a
def CA2_2_12I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_2_12I2R0Certificates_valid :
    CA2_2_12I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_2_12I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_2_12I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R0Certificates (CA2_2_12I2R0CertificateIndex a)).input
lemma CA2_2_12I2R0P_check : ∀ a : PairSlot, contains (CA2_2_12I2R0Raw a) (CA2_2_12I2R0P a) = true := by
  decide +kernel
lemma CA2_2_12I2R0P_sound (a : PairSlot) :
    (CA2_2_12I2R0P a).Encloses (CA2_2_12I2R0Value a) :=
  contains_sound (CA2_2_12I2R0Raw_sound a) (CA2_2_12I2R0P_check a)
def CA2_2_12I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R0Certificates (CA2_2_12I2R0CertificateIndex a)).output
lemma CA2_2_12I2R0Terms_sound (a : PairSlot) :
    (CA2_2_12I2R0Terms a).Encloses (Foundation.entropyTerm (CA2_2_12I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_2_12I2R0Certificates_valid
    (CA2_2_12I2R0CertificateIndex a) (CA2_2_12I2R0P_sound a)
def CA2_2_12I2R0Entropy : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R0Entropy_sound : CA2_2_12I2R0Entropy.Encloses (Foundation.finiteEntropy CA2_2_12I2R0Value) := by
  exact contains_sound (entropyPair_enclosed CA2_2_12I2R0Value CA2_2_12I2R0Terms CA2_2_12I2R0Terms_sound) (by decide +kernel)
def CA2_2_12I2R0Mass : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R0Mass_sound : CA2_2_12I2R0Mass.Encloses (∑ a, CA2_2_12I2R0Value a) := by
  exact contains_sound (pairSumBall_sound CA2_2_12I2R0P CA2_2_12I2R0Value CA2_2_12I2R0P_sound) (by decide +kernel)
def CA2_2_12I2R0MassTerm : Ball := .exact 0
lemma CA2_2_12I2R0MassTerm_sound : CA2_2_12I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_2_12I2R0Value a))) :=
  entropyTerm_zero_ball (CA2_2_12I2R0Mass_sound)
def CA2_2_12I2R0H : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R0H_sound : CA2_2_12I2R0H.Encloses (homogeneousEntropy CA2_2_12I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CA2_2_12I2R0Value CA2_2_12I2R0MassTerm_sound CA2_2_12I2R0Entropy_sound) (by decide +kernel)
def CA2_2_12I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 2 12)) (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA2_2_12I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
lemma CA2_2_12I2R1Raw_sound (a : PairSlot) :
    (CA2_2_12I2R1Raw a).Encloses (CA2_2_12I2R1Value a) := by
  exact residualBall_sound_on (below (shape 2 2 12)) A2_2_12Law (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_2_12Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 2 12) (show (shape 2 2 12) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 1 a
def CA2_2_12I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_2_12I2R1Certificates_valid :
    CA2_2_12I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_2_12I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_2_12I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R1Certificates (CA2_2_12I2R1CertificateIndex a)).input
lemma CA2_2_12I2R1P_check : ∀ a : PairSlot, contains (CA2_2_12I2R1Raw a) (CA2_2_12I2R1P a) = true := by
  decide +kernel
lemma CA2_2_12I2R1P_sound (a : PairSlot) :
    (CA2_2_12I2R1P a).Encloses (CA2_2_12I2R1Value a) :=
  contains_sound (CA2_2_12I2R1Raw_sound a) (CA2_2_12I2R1P_check a)
def CA2_2_12I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R1Certificates (CA2_2_12I2R1CertificateIndex a)).output
lemma CA2_2_12I2R1Terms_sound (a : PairSlot) :
    (CA2_2_12I2R1Terms a).Encloses (Foundation.entropyTerm (CA2_2_12I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_2_12I2R1Certificates_valid
    (CA2_2_12I2R1CertificateIndex a) (CA2_2_12I2R1P_sound a)
def CA2_2_12I2R1Entropy : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R1Entropy_sound : CA2_2_12I2R1Entropy.Encloses (Foundation.finiteEntropy CA2_2_12I2R1Value) := by
  exact contains_sound (entropyPair_enclosed CA2_2_12I2R1Value CA2_2_12I2R1Terms CA2_2_12I2R1Terms_sound) (by decide +kernel)
def CA2_2_12I2R1Mass : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R1Mass_sound : CA2_2_12I2R1Mass.Encloses (∑ a, CA2_2_12I2R1Value a) := by
  exact contains_sound (pairSumBall_sound CA2_2_12I2R1P CA2_2_12I2R1Value CA2_2_12I2R1P_sound) (by decide +kernel)
def CA2_2_12I2R1MassTerm : Ball := .exact 0
lemma CA2_2_12I2R1MassTerm_sound : CA2_2_12I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_2_12I2R1Value a))) :=
  entropyTerm_zero_ball (CA2_2_12I2R1Mass_sound)
def CA2_2_12I2R1H : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R1H_sound : CA2_2_12I2R1H.Encloses (homogeneousEntropy CA2_2_12I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CA2_2_12I2R1Value CA2_2_12I2R1MassTerm_sound CA2_2_12I2R1Entropy_sound) (by decide +kernel)
def CA2_2_12I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 2 12)) (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA2_2_12I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
lemma CA2_2_12I2R2Raw_sound (a : PairSlot) :
    (CA2_2_12I2R2Raw a).Encloses (CA2_2_12I2R2Value a) := by
  exact residualBall_sound_on (below (shape 2 2 12)) A2_2_12Law (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_2_12Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 2 12) (show (shape 2 2 12) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 2 a
def CA2_2_12I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_2_12I2R2Certificates_valid :
    CA2_2_12I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_2_12I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_2_12I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R2Certificates (CA2_2_12I2R2CertificateIndex a)).input
lemma CA2_2_12I2R2P_check : ∀ a : PairSlot, contains (CA2_2_12I2R2Raw a) (CA2_2_12I2R2P a) = true := by
  decide +kernel
lemma CA2_2_12I2R2P_sound (a : PairSlot) :
    (CA2_2_12I2R2P a).Encloses (CA2_2_12I2R2Value a) :=
  contains_sound (CA2_2_12I2R2Raw_sound a) (CA2_2_12I2R2P_check a)
def CA2_2_12I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R2Certificates (CA2_2_12I2R2CertificateIndex a)).output
lemma CA2_2_12I2R2Terms_sound (a : PairSlot) :
    (CA2_2_12I2R2Terms a).Encloses (Foundation.entropyTerm (CA2_2_12I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_2_12I2R2Certificates_valid
    (CA2_2_12I2R2CertificateIndex a) (CA2_2_12I2R2P_sound a)
def CA2_2_12I2R2Entropy : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R2Entropy_sound : CA2_2_12I2R2Entropy.Encloses (Foundation.finiteEntropy CA2_2_12I2R2Value) := by
  exact contains_sound (entropyPair_enclosed CA2_2_12I2R2Value CA2_2_12I2R2Terms CA2_2_12I2R2Terms_sound) (by decide +kernel)
def CA2_2_12I2R2Mass : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R2Mass_sound : CA2_2_12I2R2Mass.Encloses (∑ a, CA2_2_12I2R2Value a) := by
  exact contains_sound (pairSumBall_sound CA2_2_12I2R2P CA2_2_12I2R2Value CA2_2_12I2R2P_sound) (by decide +kernel)
def CA2_2_12I2R2MassTerm : Ball := .exact 0
lemma CA2_2_12I2R2MassTerm_sound : CA2_2_12I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_2_12I2R2Value a))) :=
  entropyTerm_zero_ball (CA2_2_12I2R2Mass_sound)
def CA2_2_12I2R2H : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R2H_sound : CA2_2_12I2R2H.Encloses (homogeneousEntropy CA2_2_12I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CA2_2_12I2R2Value CA2_2_12I2R2MassTerm_sound CA2_2_12I2R2Entropy_sound) (by decide +kernel)
def CA2_2_12I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 2 12)) (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA2_2_12I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
lemma CA2_2_12I2R3Raw_sound (a : PairSlot) :
    (CA2_2_12I2R3Raw a).Encloses (CA2_2_12I2R3Value a) := by
  exact residualBall_sound_on (below (shape 2 2 12)) A2_2_12Law (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_2_12Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 2 12) (show (shape 2 2 12) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 3 a
def CA2_2_12I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_2_12I2R3Certificates_valid :
    CA2_2_12I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_2_12I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_2_12I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R3Certificates (CA2_2_12I2R3CertificateIndex a)).input
lemma CA2_2_12I2R3P_check : ∀ a : PairSlot, contains (CA2_2_12I2R3Raw a) (CA2_2_12I2R3P a) = true := by
  decide +kernel
lemma CA2_2_12I2R3P_sound (a : PairSlot) :
    (CA2_2_12I2R3P a).Encloses (CA2_2_12I2R3Value a) :=
  contains_sound (CA2_2_12I2R3Raw_sound a) (CA2_2_12I2R3P_check a)
def CA2_2_12I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R3Certificates (CA2_2_12I2R3CertificateIndex a)).output
lemma CA2_2_12I2R3Terms_sound (a : PairSlot) :
    (CA2_2_12I2R3Terms a).Encloses (Foundation.entropyTerm (CA2_2_12I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_2_12I2R3Certificates_valid
    (CA2_2_12I2R3CertificateIndex a) (CA2_2_12I2R3P_sound a)
def CA2_2_12I2R3Entropy : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R3Entropy_sound : CA2_2_12I2R3Entropy.Encloses (Foundation.finiteEntropy CA2_2_12I2R3Value) := by
  exact contains_sound (entropyPair_enclosed CA2_2_12I2R3Value CA2_2_12I2R3Terms CA2_2_12I2R3Terms_sound) (by decide +kernel)
def CA2_2_12I2R3Mass : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R3Mass_sound : CA2_2_12I2R3Mass.Encloses (∑ a, CA2_2_12I2R3Value a) := by
  exact contains_sound (pairSumBall_sound CA2_2_12I2R3P CA2_2_12I2R3Value CA2_2_12I2R3P_sound) (by decide +kernel)
def CA2_2_12I2R3MassTerm : Ball := .exact 0
lemma CA2_2_12I2R3MassTerm_sound : CA2_2_12I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_2_12I2R3Value a))) :=
  entropyTerm_zero_ball (CA2_2_12I2R3Mass_sound)
def CA2_2_12I2R3H : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R3H_sound : CA2_2_12I2R3H.Encloses (homogeneousEntropy CA2_2_12I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CA2_2_12I2R3Value CA2_2_12I2R3MassTerm_sound CA2_2_12I2R3Entropy_sound) (by decide +kernel)
def CA2_2_12I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 2 12)) (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA2_2_12I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
lemma CA2_2_12I2R4Raw_sound (a : PairSlot) :
    (CA2_2_12I2R4Raw a).Encloses (CA2_2_12I2R4Value a) := by
  exact residualBall_sound_on (below (shape 2 2 12)) A2_2_12Law (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_2_12Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 2 12) (show (shape 2 2 12) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 4 a
def CA2_2_12I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(110546059455540355306581711 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(47380208567494042334297599 / 3125000000000000000000000000000), (98321 / 20000000000000000000000000000000)⟩ ⟨(-685762424109556084673323391669271 / 50000000000000000000000000000000), (444693201943 / 100000000000000000000000000000000)⟩ ⟨-20, 110546059455540355306581711, 95367431640625000000000000⟩,
   .log ⟨(37446908756512204496871500049 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(295456158830945190165451277953 / 100000000000000000000000000000000), (103085997 / 100000000000000000000000000000000)⟩ ⟨(-394500065081558819202461862021939 / 50000000000000000000000000000000), (275285710549 / 100000000000000000000000000000000)⟩ ⟨-12, 37446908756512204496871500049, 24414062500000000000000000000⟩,
   .log ⟨(389801076500725599121299973679 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(2162339191205464455787627598227 / 100000000000000000000000000000000), (412717957 / 50000000000000000000000000000000)⟩ ⟨(-554728891622606729210614912321173 / 100000000000000000000000000000000), (6617444933 / 3125000000000000000000000000000)⟩ ⟨-9, 389801076500725599121299973679, 195312500000000000000000000000⟩,
   .log ⟨(8026577649666181438563019887 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(70128369800682554750220086371 / 50000000000000000000000000000000), (47591441 / 100000000000000000000000000000000)⟩ ⟨(-873702004285713652968556505794723 / 100000000000000000000000000000000), (296461537791 / 100000000000000000000000000000000)⟩ ⟨-13, 8026577649666181438563019887, 6103515625000000000000000000⟩,
   .log ⟨(1590344396020470775076345577 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(4392918816935459876190947519 / 25000000000000000000000000000000), (2862539 / 50000000000000000000000000000000)⟩ ⟨(-220979497418440407109869188274747 / 20000000000000000000000000000000), (35998906549 / 10000000000000000000000000000000)⟩ ⟨-16, 1590344396020470775076345577, 1525878906250000000000000000⟩]
lemma CA2_2_12I2R4Certificates_valid :
    CA2_2_12I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_2_12I2R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA2_2_12I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R4Certificates (CA2_2_12I2R4CertificateIndex a)).input
lemma CA2_2_12I2R4P_check : ∀ a : PairSlot, contains (CA2_2_12I2R4Raw a) (CA2_2_12I2R4P a) = true := by
  decide +kernel
lemma CA2_2_12I2R4P_sound (a : PairSlot) :
    (CA2_2_12I2R4P a).Encloses (CA2_2_12I2R4Value a) :=
  contains_sound (CA2_2_12I2R4Raw_sound a) (CA2_2_12I2R4P_check a)
def CA2_2_12I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R4Certificates (CA2_2_12I2R4CertificateIndex a)).output
lemma CA2_2_12I2R4Terms_sound (a : PairSlot) :
    (CA2_2_12I2R4Terms a).Encloses (Foundation.entropyTerm (CA2_2_12I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_2_12I2R4Certificates_valid
    (CA2_2_12I2R4CertificateIndex a) (CA2_2_12I2R4P_sound a)
def CA2_2_12I2R4Entropy : Ball := ⟨(3054368996686146513333569336029 / 100000000000000000000000000000000), (566749539 / 50000000000000000000000000000000)⟩
lemma CA2_2_12I2R4Entropy_sound : CA2_2_12I2R4Entropy.Encloses (Foundation.finiteEntropy CA2_2_12I2R4Value) := by
  exact contains_sound (entropyPair_enclosed CA2_2_12I2R4Value CA2_2_12I2R4Terms CA2_2_12I2R4Terms_sound) (by decide +kernel)
def CA2_2_12I2R4Mass : Ball := ⟨(124653160281836571338746140581 / 25000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
lemma CA2_2_12I2R4Mass_sound : CA2_2_12I2R4Mass.Encloses (∑ a, CA2_2_12I2R4Value a) := by
  exact contains_sound (pairSumBall_sound CA2_2_12I2R4P CA2_2_12I2R4Value CA2_2_12I2R4P_sound) (by decide +kernel)
def CA2_2_12I2R4MassTermLogWitness : LogWitness := ⟨-8, 124653160281836571338746140581, 97656250000000000000000000000⟩
def CA2_2_12I2R4MassTermLog : Ball := ⟨(-530109594095838382374500639063209 / 100000000000000000000000000000000), (190582415353 / 100000000000000000000000000000000)⟩
lemma CA2_2_12I2R4MassTermLog_sound : CA2_2_12I2R4MassTermLog.Encloses (Real.log ((∑ a, CA2_2_12I2R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_2_12I2R4Mass_sound) (w := CA2_2_12I2R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_2_12I2R4MassTerm : Ball := ⟨(82599795249709834557519152781 / 3125000000000000000000000000000), (475134037 / 50000000000000000000000000000000)⟩
lemma CA2_2_12I2R4MassTerm_sound : CA2_2_12I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_2_12I2R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_2_12I2R4Mass_sound) CA2_2_12I2R4MassTermLog_sound) (by decide +kernel)
def CA2_2_12I2R4H : Ball := ⟨(411175548695431807492956447037 / 100000000000000000000000000000000), (130235447 / 6250000000000000000000000000000)⟩
lemma CA2_2_12I2R4H_sound : CA2_2_12I2R4H.Encloses (homogeneousEntropy CA2_2_12I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CA2_2_12I2R4Value CA2_2_12I2R4MassTerm_sound CA2_2_12I2R4Entropy_sound) (by decide +kernel)
def CA2_2_12I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 2 12)) (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA2_2_12I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
lemma CA2_2_12I2R5Raw_sound (a : PairSlot) :
    (CA2_2_12I2R5Raw a).Encloses (CA2_2_12I2R5Value a) := by
  exact residualBall_sound_on (below (shape 2 2 12)) A2_2_12Law (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_2_12Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 2 12) (show (shape 2 2 12) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 5 a
def CA2_2_12I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(4110672278428271414847386989 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(7163294111615695792879706789 / 5000000000000000000000000000000), (48746259 / 100000000000000000000000000000000)⟩ ⟨(-435652225866239817298025616991483 / 50000000000000000000000000000000), (296461537643 / 100000000000000000000000000000000)⟩ ⟨-13, 4110672278428271414847386989, 3051757812500000000000000000⟩,
   .log ⟨(4840897131347966399403049539407 / 50000000000000000000000000000000), (27 / 50000000000000000000000000000000)⟩ ⟨(22606243564602506056146389896049 / 100000000000000000000000000000000), (10250998593 / 100000000000000000000000000000000)⟩ ⟨(-233492294415970276033332538922871 / 100000000000000000000000000000000), (26469779743 / 25000000000000000000000000000000)⟩ ⟨-4, 4840897131347966399403049539407, 3125000000000000000000000000000⟩,
   .log ⟨(363346230530512176384157718247 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(102056131171062809117724960551 / 5000000000000000000000000000000), (96176949 / 12500000000000000000000000000000)⟩ ⟨(-280878464108608926048379004739829 / 50000000000000000000000000000000), (42351647531 / 20000000000000000000000000000000)⟩ ⟨-9, 363346230530512176384157718247, 195312500000000000000000000000⟩]
lemma CA2_2_12I2R5Certificates_valid :
    CA2_2_12I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_2_12I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA2_2_12I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R5Certificates (CA2_2_12I2R5CertificateIndex a)).input
lemma CA2_2_12I2R5P_check : ∀ a : PairSlot, contains (CA2_2_12I2R5Raw a) (CA2_2_12I2R5P a) = true := by
  decide +kernel
lemma CA2_2_12I2R5P_sound (a : PairSlot) :
    (CA2_2_12I2R5P a).Encloses (CA2_2_12I2R5Value a) :=
  contains_sound (CA2_2_12I2R5Raw_sound a) (CA2_2_12I2R5P_check a)
def CA2_2_12I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R5Certificates (CA2_2_12I2R5CertificateIndex a)).output
lemma CA2_2_12I2R5Terms_sound (a : PairSlot) :
    (CA2_2_12I2R5Terms a).Encloses (Foundation.entropyTerm (CA2_2_12I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_2_12I2R5Certificates_valid
    (CA2_2_12I2R5CertificateIndex a) (CA2_2_12I2R5P_sound a)
def CA2_2_12I2R5Entropy : Ball := ⟨(24790632070256076154358483242849 / 50000000000000000000000000000000), (2767290111 / 12500000000000000000000000000000)⟩
lemma CA2_2_12I2R5Entropy_sound : CA2_2_12I2R5Entropy.Encloses (Foundation.finiteEntropy CA2_2_12I2R5Value) := by
  exact contains_sound (entropyPair_enclosed CA2_2_12I2R5Value CA2_2_12I2R5Terms CA2_2_12I2R5Terms_sound) (by decide +kernel)
def CA2_2_12I2R5Mass : Ball := ⟨(10061583182340158060849646345017 / 50000000000000000000000000000000), (29 / 25000000000000000000000000000000)⟩
lemma CA2_2_12I2R5Mass_sound : CA2_2_12I2R5Mass.Encloses (∑ a, CA2_2_12I2R5Value a) := by
  exact contains_sound (pairSumBall_sound CA2_2_12I2R5P CA2_2_12I2R5Value CA2_2_12I2R5P_sound) (by decide +kernel)
def CA2_2_12I2R5MassTermLogWitness : LogWitness := ⟨-3, 10061583182340158060849646345017, 6250000000000000000000000000000⟩
def CA2_2_12I2R5MassTermLog : Ball := ⟨(-16032984791484648815113201465007 / 10000000000000000000000000000000), (21175823827 / 25000000000000000000000000000000)⟩
lemma CA2_2_12I2R5MassTermLog_sound : CA2_2_12I2R5MassTermLog.Encloses (Real.log ((∑ a, CA2_2_12I2R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_2_12I2R5Mass_sound) (w := CA2_2_12I2R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_2_12I2R5MassTerm : Ball := ⟨(8065860507035873417281125243751 / 25000000000000000000000000000000), (8522492609 / 50000000000000000000000000000000)⟩
lemma CA2_2_12I2R5MassTerm_sound : CA2_2_12I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_2_12I2R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_2_12I2R5Mass_sound) CA2_2_12I2R5MassTermLog_sound) (by decide +kernel)
def CA2_2_12I2R5H : Ball := ⟨(8658911056184329319796232755347 / 50000000000000000000000000000000), (19591653053 / 50000000000000000000000000000000)⟩
lemma CA2_2_12I2R5H_sound : CA2_2_12I2R5H.Encloses (homogeneousEntropy CA2_2_12I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CA2_2_12I2R5Value CA2_2_12I2R5MassTerm_sound CA2_2_12I2R5Entropy_sound) (by decide +kernel)
def CA2_2_12I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 2 12)) (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA2_2_12I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
lemma CA2_2_12I2R6Raw_sound (a : PairSlot) :
    (CA2_2_12I2R6Raw a).Encloses (CA2_2_12I2R6Value a) := by
  exact residualBall_sound_on (below (shape 2 2 12)) A2_2_12Law (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_2_12Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 2 12) (show (shape 2 2 12) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 6 a
def CA2_2_12I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(24961617159847518366857742807 / 10000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(299189995223843828430433720899 / 20000000000000000000000000000000), (264291409 / 50000000000000000000000000000000)⟩ ⟨(-599300104051574745012626210346839 / 100000000000000000000000000000000), (211758237631 / 100000000000000000000000000000000)⟩ ⟨-9, 24961617159847518366857742807, 19531250000000000000000000000⟩,
   .log ⟨(15726809599708718220368261 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(123182704277400116861528629 / 50000000000000000000000000000000), (9993 / 12500000000000000000000000000000)⟩ ⟨(-1566531387010390551339992620392563 / 100000000000000000000000000000000), (6352826587 / 1250000000000000000000000000000)⟩ ⟨-23, 15726809599708718220368261, 11920928955078125000000000⟩,
   .log ⟨(6543583602800049597473436325463 / 25000000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩ ⟨(35083838558254229655947660945703 / 100000000000000000000000000000000), (8313946419 / 50000000000000000000000000000000)⟩ ⟨(-33509771449280469694264814274123 / 25000000000000000000000000000000), (63527471247 / 100000000000000000000000000000000)⟩ ⟨-2, 6543583602800049597473436325463, 6250000000000000000000000000000⟩]
lemma CA2_2_12I2R6Certificates_valid :
    CA2_2_12I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_2_12I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA2_2_12I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R6Certificates (CA2_2_12I2R6CertificateIndex a)).input
lemma CA2_2_12I2R6P_check : ∀ a : PairSlot, contains (CA2_2_12I2R6Raw a) (CA2_2_12I2R6P a) = true := by
  decide +kernel
lemma CA2_2_12I2R6P_sound (a : PairSlot) :
    (CA2_2_12I2R6P a).Encloses (CA2_2_12I2R6Value a) :=
  contains_sound (CA2_2_12I2R6Raw_sound a) (CA2_2_12I2R6P_check a)
def CA2_2_12I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R6Certificates (CA2_2_12I2R6CertificateIndex a)).output
lemma CA2_2_12I2R6Terms_sound (a : PairSlot) :
    (CA2_2_12I2R6Terms a).Encloses (Foundation.entropyTerm (CA2_2_12I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_2_12I2R6Certificates_valid
    (CA2_2_12I2R6CertificateIndex a) (CA2_2_12I2R6P_sound a)
def CA2_2_12I2R6Entropy : Ball := ⟨(38076231241309777540719444269209 / 100000000000000000000000000000000), (8842609181 / 50000000000000000000000000000000)⟩
lemma CA2_2_12I2R6Entropy_sound : CA2_2_12I2R6Entropy.Encloses (Foundation.finiteEntropy CA2_2_12I2R6Value) := by
  exact contains_sound (entropyPair_enclosed CA2_2_12I2R6Value CA2_2_12I2R6Terms CA2_2_12I2R6Terms_sound) (by decide +kernel)
def CA2_2_12I2R6Mass : Ball := ⟨(13336799104008174087333670447257 / 50000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
lemma CA2_2_12I2R6Mass_sound : CA2_2_12I2R6Mass.Encloses (∑ a, CA2_2_12I2R6Value a) := by
  exact contains_sound (pairSumBall_sound CA2_2_12I2R6P CA2_2_12I2R6Value CA2_2_12I2R6P_sound) (by decide +kernel)
def CA2_2_12I2R6MassTermLogWitness : LogWitness := ⟨-2, 13336799104008174087333670447257, 12500000000000000000000000000000⟩
def CA2_2_12I2R6MassTermLog : Ball := ⟨(-66074797047919191187250376818187 / 50000000000000000000000000000000), (31763735633 / 50000000000000000000000000000000)⟩
lemma CA2_2_12I2R6MassTermLog_sound : CA2_2_12I2R6MassTermLog.Encloses (Real.log ((∑ a, CA2_2_12I2R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_2_12I2R6Mass_sound) (w := CA2_2_12I2R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_2_12I2R6MassTerm : Ball := ⟨(1101532867582763269065187204367 / 3125000000000000000000000000000), (3389012503 / 20000000000000000000000000000000)⟩
lemma CA2_2_12I2R6MassTerm_sound : CA2_2_12I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_2_12I2R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_2_12I2R6Mass_sound) CA2_2_12I2R6MassTermLog_sound) (by decide +kernel)
def CA2_2_12I2R6H : Ball := ⟨(565435895732270586126690745893 / 20000000000000000000000000000000), (34630280877 / 100000000000000000000000000000000)⟩
lemma CA2_2_12I2R6H_sound : CA2_2_12I2R6H.Encloses (homogeneousEntropy CA2_2_12I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CA2_2_12I2R6Value CA2_2_12I2R6MassTerm_sound CA2_2_12I2R6Entropy_sound) (by decide +kernel)
def CA2_2_12I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 2 12)) (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA2_2_12I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
lemma CA2_2_12I2R7Raw_sound (a : PairSlot) :
    (CA2_2_12I2R7Raw a).Encloses (CA2_2_12I2R7Value a) := by
  exact residualBall_sound_on (below (shape 2 2 12)) A2_2_12Law (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_2_12Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 2 12) (show (shape 2 2 12) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 7 a
def CA2_2_12I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_2_12I2R7Certificates_valid :
    CA2_2_12I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_2_12I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_2_12I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R7Certificates (CA2_2_12I2R7CertificateIndex a)).input
lemma CA2_2_12I2R7P_check : ∀ a : PairSlot, contains (CA2_2_12I2R7Raw a) (CA2_2_12I2R7P a) = true := by
  decide +kernel
lemma CA2_2_12I2R7P_sound (a : PairSlot) :
    (CA2_2_12I2R7P a).Encloses (CA2_2_12I2R7Value a) :=
  contains_sound (CA2_2_12I2R7Raw_sound a) (CA2_2_12I2R7P_check a)
def CA2_2_12I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R7Certificates (CA2_2_12I2R7CertificateIndex a)).output
lemma CA2_2_12I2R7Terms_sound (a : PairSlot) :
    (CA2_2_12I2R7Terms a).Encloses (Foundation.entropyTerm (CA2_2_12I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_2_12I2R7Certificates_valid
    (CA2_2_12I2R7CertificateIndex a) (CA2_2_12I2R7P_sound a)
def CA2_2_12I2R7Entropy : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R7Entropy_sound : CA2_2_12I2R7Entropy.Encloses (Foundation.finiteEntropy CA2_2_12I2R7Value) := by
  exact contains_sound (entropyPair_enclosed CA2_2_12I2R7Value CA2_2_12I2R7Terms CA2_2_12I2R7Terms_sound) (by decide +kernel)
def CA2_2_12I2R7Mass : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R7Mass_sound : CA2_2_12I2R7Mass.Encloses (∑ a, CA2_2_12I2R7Value a) := by
  exact contains_sound (pairSumBall_sound CA2_2_12I2R7P CA2_2_12I2R7Value CA2_2_12I2R7P_sound) (by decide +kernel)
def CA2_2_12I2R7MassTerm : Ball := .exact 0
lemma CA2_2_12I2R7MassTerm_sound : CA2_2_12I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_2_12I2R7Value a))) :=
  entropyTerm_zero_ball (CA2_2_12I2R7Mass_sound)
def CA2_2_12I2R7H : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R7H_sound : CA2_2_12I2R7H.Encloses (homogeneousEntropy CA2_2_12I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CA2_2_12I2R7Value CA2_2_12I2R7MassTerm_sound CA2_2_12I2R7Entropy_sound) (by decide +kernel)
def CA2_2_12I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 2 12)) (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA2_2_12I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
lemma CA2_2_12I2R8Raw_sound (a : PairSlot) :
    (CA2_2_12I2R8Raw a).Encloses (CA2_2_12I2R8Value a) := by
  exact residualBall_sound_on (below (shape 2 2 12)) A2_2_12Law (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_2_12Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 2 12) (show (shape 2 2 12) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 8 a
def CA2_2_12I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_2_12I2R8Certificates_valid :
    CA2_2_12I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_2_12I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_2_12I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R8Certificates (CA2_2_12I2R8CertificateIndex a)).input
lemma CA2_2_12I2R8P_check : ∀ a : PairSlot, contains (CA2_2_12I2R8Raw a) (CA2_2_12I2R8P a) = true := by
  decide +kernel
lemma CA2_2_12I2R8P_sound (a : PairSlot) :
    (CA2_2_12I2R8P a).Encloses (CA2_2_12I2R8Value a) :=
  contains_sound (CA2_2_12I2R8Raw_sound a) (CA2_2_12I2R8P_check a)
def CA2_2_12I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R8Certificates (CA2_2_12I2R8CertificateIndex a)).output
lemma CA2_2_12I2R8Terms_sound (a : PairSlot) :
    (CA2_2_12I2R8Terms a).Encloses (Foundation.entropyTerm (CA2_2_12I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_2_12I2R8Certificates_valid
    (CA2_2_12I2R8CertificateIndex a) (CA2_2_12I2R8P_sound a)
def CA2_2_12I2R8Entropy : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R8Entropy_sound : CA2_2_12I2R8Entropy.Encloses (Foundation.finiteEntropy CA2_2_12I2R8Value) := by
  exact contains_sound (entropyPair_enclosed CA2_2_12I2R8Value CA2_2_12I2R8Terms CA2_2_12I2R8Terms_sound) (by decide +kernel)
def CA2_2_12I2R8Mass : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R8Mass_sound : CA2_2_12I2R8Mass.Encloses (∑ a, CA2_2_12I2R8Value a) := by
  exact contains_sound (pairSumBall_sound CA2_2_12I2R8P CA2_2_12I2R8Value CA2_2_12I2R8P_sound) (by decide +kernel)
def CA2_2_12I2R8MassTerm : Ball := .exact 0
lemma CA2_2_12I2R8MassTerm_sound : CA2_2_12I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_2_12I2R8Value a))) :=
  entropyTerm_zero_ball (CA2_2_12I2R8Mass_sound)
def CA2_2_12I2R8H : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R8H_sound : CA2_2_12I2R8H.Encloses (homogeneousEntropy CA2_2_12I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CA2_2_12I2R8Value CA2_2_12I2R8MassTerm_sound CA2_2_12I2R8Entropy_sound) (by decide +kernel)
def CA2_2_12I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 2 12)) (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA2_2_12I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
lemma CA2_2_12I2R9Raw_sound (a : PairSlot) :
    (CA2_2_12I2R9Raw a).Encloses (CA2_2_12I2R9Value a) := by
  exact residualBall_sound_on (below (shape 2 2 12)) A2_2_12Law (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_2_12Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 2 12) (show (shape 2 2 12) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 9 a
def CA2_2_12I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_2_12I2R9Certificates_valid :
    CA2_2_12I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_2_12I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_2_12I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R9Certificates (CA2_2_12I2R9CertificateIndex a)).input
lemma CA2_2_12I2R9P_check : ∀ a : PairSlot, contains (CA2_2_12I2R9Raw a) (CA2_2_12I2R9P a) = true := by
  decide +kernel
lemma CA2_2_12I2R9P_sound (a : PairSlot) :
    (CA2_2_12I2R9P a).Encloses (CA2_2_12I2R9Value a) :=
  contains_sound (CA2_2_12I2R9Raw_sound a) (CA2_2_12I2R9P_check a)
def CA2_2_12I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R9Certificates (CA2_2_12I2R9CertificateIndex a)).output
lemma CA2_2_12I2R9Terms_sound (a : PairSlot) :
    (CA2_2_12I2R9Terms a).Encloses (Foundation.entropyTerm (CA2_2_12I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_2_12I2R9Certificates_valid
    (CA2_2_12I2R9CertificateIndex a) (CA2_2_12I2R9P_sound a)
def CA2_2_12I2R9Entropy : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R9Entropy_sound : CA2_2_12I2R9Entropy.Encloses (Foundation.finiteEntropy CA2_2_12I2R9Value) := by
  exact contains_sound (entropyPair_enclosed CA2_2_12I2R9Value CA2_2_12I2R9Terms CA2_2_12I2R9Terms_sound) (by decide +kernel)
def CA2_2_12I2R9Mass : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R9Mass_sound : CA2_2_12I2R9Mass.Encloses (∑ a, CA2_2_12I2R9Value a) := by
  exact contains_sound (pairSumBall_sound CA2_2_12I2R9P CA2_2_12I2R9Value CA2_2_12I2R9P_sound) (by decide +kernel)
def CA2_2_12I2R9MassTerm : Ball := .exact 0
lemma CA2_2_12I2R9MassTerm_sound : CA2_2_12I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_2_12I2R9Value a))) :=
  entropyTerm_zero_ball (CA2_2_12I2R9Mass_sound)
def CA2_2_12I2R9H : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R9H_sound : CA2_2_12I2R9H.Encloses (homogeneousEntropy CA2_2_12I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CA2_2_12I2R9Value CA2_2_12I2R9MassTerm_sound CA2_2_12I2R9Entropy_sound) (by decide +kernel)
def CA2_2_12I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 2 12)) (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA2_2_12I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
lemma CA2_2_12I2R10Raw_sound (a : PairSlot) :
    (CA2_2_12I2R10Raw a).Encloses (CA2_2_12I2R10Value a) := by
  exact residualBall_sound_on (below (shape 2 2 12)) A2_2_12Law (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_2_12Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 2 12) (show (shape 2 2 12) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 10 a
def CA2_2_12I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_2_12I2R10Certificates_valid :
    CA2_2_12I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_2_12I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_2_12I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R10Certificates (CA2_2_12I2R10CertificateIndex a)).input
lemma CA2_2_12I2R10P_check : ∀ a : PairSlot, contains (CA2_2_12I2R10Raw a) (CA2_2_12I2R10P a) = true := by
  decide +kernel
lemma CA2_2_12I2R10P_sound (a : PairSlot) :
    (CA2_2_12I2R10P a).Encloses (CA2_2_12I2R10Value a) :=
  contains_sound (CA2_2_12I2R10Raw_sound a) (CA2_2_12I2R10P_check a)
def CA2_2_12I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R10Certificates (CA2_2_12I2R10CertificateIndex a)).output
lemma CA2_2_12I2R10Terms_sound (a : PairSlot) :
    (CA2_2_12I2R10Terms a).Encloses (Foundation.entropyTerm (CA2_2_12I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_2_12I2R10Certificates_valid
    (CA2_2_12I2R10CertificateIndex a) (CA2_2_12I2R10P_sound a)
def CA2_2_12I2R10Entropy : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R10Entropy_sound : CA2_2_12I2R10Entropy.Encloses (Foundation.finiteEntropy CA2_2_12I2R10Value) := by
  exact contains_sound (entropyPair_enclosed CA2_2_12I2R10Value CA2_2_12I2R10Terms CA2_2_12I2R10Terms_sound) (by decide +kernel)
def CA2_2_12I2R10Mass : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R10Mass_sound : CA2_2_12I2R10Mass.Encloses (∑ a, CA2_2_12I2R10Value a) := by
  exact contains_sound (pairSumBall_sound CA2_2_12I2R10P CA2_2_12I2R10Value CA2_2_12I2R10P_sound) (by decide +kernel)
def CA2_2_12I2R10MassTerm : Ball := .exact 0
lemma CA2_2_12I2R10MassTerm_sound : CA2_2_12I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_2_12I2R10Value a))) :=
  entropyTerm_zero_ball (CA2_2_12I2R10Mass_sound)
def CA2_2_12I2R10H : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R10H_sound : CA2_2_12I2R10H.Encloses (homogeneousEntropy CA2_2_12I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CA2_2_12I2R10Value CA2_2_12I2R10MassTerm_sound CA2_2_12I2R10Entropy_sound) (by decide +kernel)
def CA2_2_12I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 2 12)) (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA2_2_12I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
lemma CA2_2_12I2R11Raw_sound (a : PairSlot) :
    (CA2_2_12I2R11Raw a).Encloses (CA2_2_12I2R11Value a) := by
  exact residualBall_sound_on (below (shape 2 2 12)) A2_2_12Law (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_2_12Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 2 12) (show (shape 2 2 12) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 11 a
def CA2_2_12I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_2_12I2R11Certificates_valid :
    CA2_2_12I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_2_12I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_2_12I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R11Certificates (CA2_2_12I2R11CertificateIndex a)).input
lemma CA2_2_12I2R11P_check : ∀ a : PairSlot, contains (CA2_2_12I2R11Raw a) (CA2_2_12I2R11P a) = true := by
  decide +kernel
lemma CA2_2_12I2R11P_sound (a : PairSlot) :
    (CA2_2_12I2R11P a).Encloses (CA2_2_12I2R11Value a) :=
  contains_sound (CA2_2_12I2R11Raw_sound a) (CA2_2_12I2R11P_check a)
def CA2_2_12I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R11Certificates (CA2_2_12I2R11CertificateIndex a)).output
lemma CA2_2_12I2R11Terms_sound (a : PairSlot) :
    (CA2_2_12I2R11Terms a).Encloses (Foundation.entropyTerm (CA2_2_12I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_2_12I2R11Certificates_valid
    (CA2_2_12I2R11CertificateIndex a) (CA2_2_12I2R11P_sound a)
def CA2_2_12I2R11Entropy : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R11Entropy_sound : CA2_2_12I2R11Entropy.Encloses (Foundation.finiteEntropy CA2_2_12I2R11Value) := by
  exact contains_sound (entropyPair_enclosed CA2_2_12I2R11Value CA2_2_12I2R11Terms CA2_2_12I2R11Terms_sound) (by decide +kernel)
def CA2_2_12I2R11Mass : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R11Mass_sound : CA2_2_12I2R11Mass.Encloses (∑ a, CA2_2_12I2R11Value a) := by
  exact contains_sound (pairSumBall_sound CA2_2_12I2R11P CA2_2_12I2R11Value CA2_2_12I2R11P_sound) (by decide +kernel)
def CA2_2_12I2R11MassTerm : Ball := .exact 0
lemma CA2_2_12I2R11MassTerm_sound : CA2_2_12I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_2_12I2R11Value a))) :=
  entropyTerm_zero_ball (CA2_2_12I2R11Mass_sound)
def CA2_2_12I2R11H : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R11H_sound : CA2_2_12I2R11H.Encloses (homogeneousEntropy CA2_2_12I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CA2_2_12I2R11Value CA2_2_12I2R11MassTerm_sound CA2_2_12I2R11Entropy_sound) (by decide +kernel)
def CA2_2_12I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 2 12)) (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA2_2_12I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
lemma CA2_2_12I2R12Raw_sound (a : PairSlot) :
    (CA2_2_12I2R12Raw a).Encloses (CA2_2_12I2R12Value a) := by
  exact residualBall_sound_on (below (shape 2 2 12)) A2_2_12Law (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_2_12Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 2 12) (show (shape 2 2 12) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 12 a
def CA2_2_12I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_2_12I2R12Certificates_valid :
    CA2_2_12I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_2_12I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_2_12I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R12Certificates (CA2_2_12I2R12CertificateIndex a)).input
lemma CA2_2_12I2R12P_check : ∀ a : PairSlot, contains (CA2_2_12I2R12Raw a) (CA2_2_12I2R12P a) = true := by
  decide +kernel
lemma CA2_2_12I2R12P_sound (a : PairSlot) :
    (CA2_2_12I2R12P a).Encloses (CA2_2_12I2R12Value a) :=
  contains_sound (CA2_2_12I2R12Raw_sound a) (CA2_2_12I2R12P_check a)
def CA2_2_12I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R12Certificates (CA2_2_12I2R12CertificateIndex a)).output
lemma CA2_2_12I2R12Terms_sound (a : PairSlot) :
    (CA2_2_12I2R12Terms a).Encloses (Foundation.entropyTerm (CA2_2_12I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_2_12I2R12Certificates_valid
    (CA2_2_12I2R12CertificateIndex a) (CA2_2_12I2R12P_sound a)
def CA2_2_12I2R12Entropy : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R12Entropy_sound : CA2_2_12I2R12Entropy.Encloses (Foundation.finiteEntropy CA2_2_12I2R12Value) := by
  exact contains_sound (entropyPair_enclosed CA2_2_12I2R12Value CA2_2_12I2R12Terms CA2_2_12I2R12Terms_sound) (by decide +kernel)
def CA2_2_12I2R12Mass : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R12Mass_sound : CA2_2_12I2R12Mass.Encloses (∑ a, CA2_2_12I2R12Value a) := by
  exact contains_sound (pairSumBall_sound CA2_2_12I2R12P CA2_2_12I2R12Value CA2_2_12I2R12P_sound) (by decide +kernel)
def CA2_2_12I2R12MassTerm : Ball := .exact 0
lemma CA2_2_12I2R12MassTerm_sound : CA2_2_12I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_2_12I2R12Value a))) :=
  entropyTerm_zero_ball (CA2_2_12I2R12Mass_sound)
def CA2_2_12I2R12H : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R12H_sound : CA2_2_12I2R12H.Encloses (homogeneousEntropy CA2_2_12I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CA2_2_12I2R12Value CA2_2_12I2R12MassTerm_sound CA2_2_12I2R12Entropy_sound) (by decide +kernel)
def CA2_2_12I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 2 12)) (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA2_2_12I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
lemma CA2_2_12I2R13Raw_sound (a : PairSlot) :
    (CA2_2_12I2R13Raw a).Encloses (CA2_2_12I2R13Value a) := by
  exact residualBall_sound_on (below (shape 2 2 12)) A2_2_12Law (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_2_12Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 2 12) (show (shape 2 2 12) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 13 a
def CA2_2_12I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_2_12I2R13Certificates_valid :
    CA2_2_12I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_2_12I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_2_12I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R13Certificates (CA2_2_12I2R13CertificateIndex a)).input
lemma CA2_2_12I2R13P_check : ∀ a : PairSlot, contains (CA2_2_12I2R13Raw a) (CA2_2_12I2R13P a) = true := by
  decide +kernel
lemma CA2_2_12I2R13P_sound (a : PairSlot) :
    (CA2_2_12I2R13P a).Encloses (CA2_2_12I2R13Value a) :=
  contains_sound (CA2_2_12I2R13Raw_sound a) (CA2_2_12I2R13P_check a)
def CA2_2_12I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R13Certificates (CA2_2_12I2R13CertificateIndex a)).output
lemma CA2_2_12I2R13Terms_sound (a : PairSlot) :
    (CA2_2_12I2R13Terms a).Encloses (Foundation.entropyTerm (CA2_2_12I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_2_12I2R13Certificates_valid
    (CA2_2_12I2R13CertificateIndex a) (CA2_2_12I2R13P_sound a)
def CA2_2_12I2R13Entropy : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R13Entropy_sound : CA2_2_12I2R13Entropy.Encloses (Foundation.finiteEntropy CA2_2_12I2R13Value) := by
  exact contains_sound (entropyPair_enclosed CA2_2_12I2R13Value CA2_2_12I2R13Terms CA2_2_12I2R13Terms_sound) (by decide +kernel)
def CA2_2_12I2R13Mass : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R13Mass_sound : CA2_2_12I2R13Mass.Encloses (∑ a, CA2_2_12I2R13Value a) := by
  exact contains_sound (pairSumBall_sound CA2_2_12I2R13P CA2_2_12I2R13Value CA2_2_12I2R13P_sound) (by decide +kernel)
def CA2_2_12I2R13MassTerm : Ball := .exact 0
lemma CA2_2_12I2R13MassTerm_sound : CA2_2_12I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_2_12I2R13Value a))) :=
  entropyTerm_zero_ball (CA2_2_12I2R13Mass_sound)
def CA2_2_12I2R13H : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R13H_sound : CA2_2_12I2R13H.Encloses (homogeneousEntropy CA2_2_12I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CA2_2_12I2R13Value CA2_2_12I2R13MassTerm_sound CA2_2_12I2R13Entropy_sound) (by decide +kernel)
def CA2_2_12I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 2 12)) (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA2_2_12I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
lemma CA2_2_12I2R14Raw_sound (a : PairSlot) :
    (CA2_2_12I2R14Raw a).Encloses (CA2_2_12I2R14Value a) := by
  exact residualBall_sound_on (below (shape 2 2 12)) A2_2_12Law (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_2_12Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 2 12) (show (shape 2 2 12) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 14 a
def CA2_2_12I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_2_12I2R14Certificates_valid :
    CA2_2_12I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_2_12I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_2_12I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R14Certificates (CA2_2_12I2R14CertificateIndex a)).input
lemma CA2_2_12I2R14P_check : ∀ a : PairSlot, contains (CA2_2_12I2R14Raw a) (CA2_2_12I2R14P a) = true := by
  decide +kernel
lemma CA2_2_12I2R14P_sound (a : PairSlot) :
    (CA2_2_12I2R14P a).Encloses (CA2_2_12I2R14Value a) :=
  contains_sound (CA2_2_12I2R14Raw_sound a) (CA2_2_12I2R14P_check a)
def CA2_2_12I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R14Certificates (CA2_2_12I2R14CertificateIndex a)).output
lemma CA2_2_12I2R14Terms_sound (a : PairSlot) :
    (CA2_2_12I2R14Terms a).Encloses (Foundation.entropyTerm (CA2_2_12I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_2_12I2R14Certificates_valid
    (CA2_2_12I2R14CertificateIndex a) (CA2_2_12I2R14P_sound a)
def CA2_2_12I2R14Entropy : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R14Entropy_sound : CA2_2_12I2R14Entropy.Encloses (Foundation.finiteEntropy CA2_2_12I2R14Value) := by
  exact contains_sound (entropyPair_enclosed CA2_2_12I2R14Value CA2_2_12I2R14Terms CA2_2_12I2R14Terms_sound) (by decide +kernel)
def CA2_2_12I2R14Mass : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R14Mass_sound : CA2_2_12I2R14Mass.Encloses (∑ a, CA2_2_12I2R14Value a) := by
  exact contains_sound (pairSumBall_sound CA2_2_12I2R14P CA2_2_12I2R14Value CA2_2_12I2R14P_sound) (by decide +kernel)
def CA2_2_12I2R14MassTerm : Ball := .exact 0
lemma CA2_2_12I2R14MassTerm_sound : CA2_2_12I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_2_12I2R14Value a))) :=
  entropyTerm_zero_ball (CA2_2_12I2R14Mass_sound)
def CA2_2_12I2R14H : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R14H_sound : CA2_2_12I2R14H.Encloses (homogeneousEntropy CA2_2_12I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CA2_2_12I2R14Value CA2_2_12I2R14MassTerm_sound CA2_2_12I2R14Entropy_sound) (by decide +kernel)
def CA2_2_12I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 2 12)) (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA2_2_12I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
lemma CA2_2_12I2R15Raw_sound (a : PairSlot) :
    (CA2_2_12I2R15Raw a).Encloses (CA2_2_12I2R15Value a) := by
  exact residualBall_sound_on (below (shape 2 2 12)) A2_2_12Law (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_2_12Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 2 12) (show (shape 2 2 12) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 15 a
def CA2_2_12I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_2_12I2R15Certificates_valid :
    CA2_2_12I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_2_12I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_2_12I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R15Certificates (CA2_2_12I2R15CertificateIndex a)).input
lemma CA2_2_12I2R15P_check : ∀ a : PairSlot, contains (CA2_2_12I2R15Raw a) (CA2_2_12I2R15P a) = true := by
  decide +kernel
lemma CA2_2_12I2R15P_sound (a : PairSlot) :
    (CA2_2_12I2R15P a).Encloses (CA2_2_12I2R15Value a) :=
  contains_sound (CA2_2_12I2R15Raw_sound a) (CA2_2_12I2R15P_check a)
def CA2_2_12I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R15Certificates (CA2_2_12I2R15CertificateIndex a)).output
lemma CA2_2_12I2R15Terms_sound (a : PairSlot) :
    (CA2_2_12I2R15Terms a).Encloses (Foundation.entropyTerm (CA2_2_12I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_2_12I2R15Certificates_valid
    (CA2_2_12I2R15CertificateIndex a) (CA2_2_12I2R15P_sound a)
def CA2_2_12I2R15Entropy : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R15Entropy_sound : CA2_2_12I2R15Entropy.Encloses (Foundation.finiteEntropy CA2_2_12I2R15Value) := by
  exact contains_sound (entropyPair_enclosed CA2_2_12I2R15Value CA2_2_12I2R15Terms CA2_2_12I2R15Terms_sound) (by decide +kernel)
def CA2_2_12I2R15Mass : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R15Mass_sound : CA2_2_12I2R15Mass.Encloses (∑ a, CA2_2_12I2R15Value a) := by
  exact contains_sound (pairSumBall_sound CA2_2_12I2R15P CA2_2_12I2R15Value CA2_2_12I2R15P_sound) (by decide +kernel)
def CA2_2_12I2R15MassTerm : Ball := .exact 0
lemma CA2_2_12I2R15MassTerm_sound : CA2_2_12I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_2_12I2R15Value a))) :=
  entropyTerm_zero_ball (CA2_2_12I2R15Mass_sound)
def CA2_2_12I2R15H : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R15H_sound : CA2_2_12I2R15H.Encloses (homogeneousEntropy CA2_2_12I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CA2_2_12I2R15Value CA2_2_12I2R15MassTerm_sound CA2_2_12I2R15Entropy_sound) (by decide +kernel)
def CA2_2_12I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 2 12)) (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA2_2_12I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 2 2 12)) A2_2_12Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
lemma CA2_2_12I2R16Raw_sound (a : PairSlot) :
    (CA2_2_12I2R16Raw a).Encloses (CA2_2_12I2R16Value a) := by
  exact residualBall_sound_on (below (shape 2 2 12)) A2_2_12Law (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_2_12Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 2 12) (show (shape 2 2 12) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 16 a
def CA2_2_12I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_2_12I2R16Certificates_valid :
    CA2_2_12I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_2_12I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_2_12I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R16Certificates (CA2_2_12I2R16CertificateIndex a)).input
lemma CA2_2_12I2R16P_check : ∀ a : PairSlot, contains (CA2_2_12I2R16Raw a) (CA2_2_12I2R16P a) = true := by
  decide +kernel
lemma CA2_2_12I2R16P_sound (a : PairSlot) :
    (CA2_2_12I2R16P a).Encloses (CA2_2_12I2R16Value a) :=
  contains_sound (CA2_2_12I2R16Raw_sound a) (CA2_2_12I2R16P_check a)
def CA2_2_12I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I2R16Certificates (CA2_2_12I2R16CertificateIndex a)).output
lemma CA2_2_12I2R16Terms_sound (a : PairSlot) :
    (CA2_2_12I2R16Terms a).Encloses (Foundation.entropyTerm (CA2_2_12I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_2_12I2R16Certificates_valid
    (CA2_2_12I2R16CertificateIndex a) (CA2_2_12I2R16P_sound a)
def CA2_2_12I2R16Entropy : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R16Entropy_sound : CA2_2_12I2R16Entropy.Encloses (Foundation.finiteEntropy CA2_2_12I2R16Value) := by
  exact contains_sound (entropyPair_enclosed CA2_2_12I2R16Value CA2_2_12I2R16Terms CA2_2_12I2R16Terms_sound) (by decide +kernel)
def CA2_2_12I2R16Mass : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R16Mass_sound : CA2_2_12I2R16Mass.Encloses (∑ a, CA2_2_12I2R16Value a) := by
  exact contains_sound (pairSumBall_sound CA2_2_12I2R16P CA2_2_12I2R16Value CA2_2_12I2R16P_sound) (by decide +kernel)
def CA2_2_12I2R16MassTerm : Ball := .exact 0
lemma CA2_2_12I2R16MassTerm_sound : CA2_2_12I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_2_12I2R16Value a))) :=
  entropyTerm_zero_ball (CA2_2_12I2R16Mass_sound)
def CA2_2_12I2R16H : Ball := ⟨0, 0⟩
lemma CA2_2_12I2R16H_sound : CA2_2_12I2R16H.Encloses (homogeneousEntropy CA2_2_12I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CA2_2_12I2R16Value CA2_2_12I2R16MassTerm_sound CA2_2_12I2R16Entropy_sound) (by decide +kernel)
def CA2_2_12I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA2_2_12I2R0H
  | 1 => CA2_2_12I2R1H
  | 2 => CA2_2_12I2R2H
  | 3 => CA2_2_12I2R3H
  | 4 => CA2_2_12I2R4H
  | 5 => CA2_2_12I2R5H
  | 6 => CA2_2_12I2R6H
  | 7 => CA2_2_12I2R7H
  | 8 => CA2_2_12I2R8H
  | 9 => CA2_2_12I2R9H
  | 10 => CA2_2_12I2R10H
  | 11 => CA2_2_12I2R11H
  | 12 => CA2_2_12I2R12H
  | 13 => CA2_2_12I2R13H
  | 14 => CA2_2_12I2R14H
  | 15 => CA2_2_12I2R15H
  | 16 => CA2_2_12I2R16H
  | _ => (.exact 0)
lemma CA2_2_12I2ResidualEntropies_sound (k : Fin 17) :
    (CA2_2_12I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 2 2 12)) (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CA2_2_12I2R0H_sound
  · exact CA2_2_12I2R1H_sound
  · exact CA2_2_12I2R2H_sound
  · exact CA2_2_12I2R3H_sound
  · exact CA2_2_12I2R4H_sound
  · exact CA2_2_12I2R5H_sound
  · exact CA2_2_12I2R6H_sound
  · exact CA2_2_12I2R7H_sound
  · exact CA2_2_12I2R8H_sound
  · exact CA2_2_12I2R9H_sound
  · exact CA2_2_12I2R10H_sound
  · exact CA2_2_12I2R11H_sound
  · exact CA2_2_12I2R12H_sound
  · exact CA2_2_12I2R13H_sound
  · exact CA2_2_12I2R14H_sound
  · exact CA2_2_12I2R15H_sound
  · exact CA2_2_12I2R16H_sound
def CA2_2_12I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8H2H
  | 0, 1, 7 => Z0_1_7H2H
  | 0, 2, 6 => Z0_2_6H2H
  | 1, 0, 7 => Z1_0_7H2H
  | 2, 0, 6 => Z2_0_6H2H
  | _, _, _ => (.exact 0)
lemma CA2_2_12I2Singles_sound (u : Shape) (hu : u ∈ below (shape 2 2 12))
    (hd : designated (Equiv.refl (Fin 3)) 2 u) :
    (CA2_2_12I2Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) u)) := by
  rw [A2_2_12_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0_0_8H2H_sound
  · exact Z0_1_7H2H_sound
  · exact Z0_2_6H2H_sound
  · exact Z1_0_7H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 2 5) by decide +kernel) hd |>.elim
  · exact Z2_0_6H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 1 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 2 4) by decide +kernel) hd |>.elim
def CA2_2_12I2Singleton : Ball := ⟨(49295386069855886010487108668437 / 100000000000000000000000000000000), (9719736623 / 25000000000000000000000000000000)⟩
lemma CA2_2_12I2Singleton_sound : CA2_2_12I2Singleton.Encloses
    (singletonEntropy (below (shape 2 2 12)) (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 2 2 12)) A2_2_12Law (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2
    CA2_2_12I2Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_2_12Law_sound u) CA2_2_12I2Singles_sound) (by decide +kernel)
def CA2_2_12I2Group : Ball := ⟨(69851563209581329388205984355633 / 100000000000000000000000000000000), (114776300627 / 100000000000000000000000000000000)⟩
lemma CA2_2_12I2Group_sound : CA2_2_12I2Group.Encloses
    (groupedEntropy (below (shape 2 2 12)) (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA2_2_12I2Singleton_sound
    (finSumBall_sound 17 CA2_2_12I2ResidualEntropies _ CA2_2_12I2ResidualEntropies_sound)) (by decide +kernel)

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
def CA2_2_12I2H : Ball := ⟨(4655557280079521329180504965639 / 4000000000000000000000000000000), (1130612347 / 312500000000000000000000000000)⟩
lemma CA2_2_12I2_sound : CA2_2_12I2H.Encloses (stageACapacity (shape 2 2 12) 2) := by
  have hb := contains_sound (Ball.add_sound CA2_2_12I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA2_2_12I2Group_sound)))
    (show contains (.add CA2_2_12I2PairH (.neg (.mul (.exact 2) CA2_2_12I2Group))) CA2_2_12I2H = true by decide +kernel)
  unfold CA2_2_12I2PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
