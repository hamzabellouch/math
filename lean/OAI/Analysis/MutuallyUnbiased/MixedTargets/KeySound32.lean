import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical316

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1024 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1024) =
      Integer.Sparse.eval keyMomentRow1024 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1024).leftCharge (GramAssembly.key 1024).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3164) := by
    have ha : gramCharges (GramAssembly.key 1024).leftCharge (GramAssembly.key 1024).rightCharge = raw40463 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40463Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40463 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1024).leftCharge (GramAssembly.key 1024).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1024, Integer.Sparse.eval]

theorem keyMoment1025 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1025) =
      Integer.Sparse.eval keyMomentRow1025 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1025).leftCharge (GramAssembly.key 1025).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2423) := by
    have ha : gramCharges (GramAssembly.key 1025).leftCharge (GramAssembly.key 1025).rightCharge = raw40464 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40464Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40464 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1025).leftCharge (GramAssembly.key 1025).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1025, Integer.Sparse.eval]

theorem keyMoment1026 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1026) =
      Integer.Sparse.eval keyMomentRow1026 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1026).leftCharge (GramAssembly.key 1026).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 621) := by
    have ha : gramCharges (GramAssembly.key 1026).leftCharge (GramAssembly.key 1026).rightCharge = raw40465 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40465Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40465 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1026).leftCharge (GramAssembly.key 1026).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1026, Integer.Sparse.eval]

theorem keyMoment1027 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1027) =
      Integer.Sparse.eval keyMomentRow1027 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1027).leftCharge (GramAssembly.key 1027).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1061) := by
    have ha : gramCharges (GramAssembly.key 1027).leftCharge (GramAssembly.key 1027).rightCharge = raw40466 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40466Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40466 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1027).leftCharge (GramAssembly.key 1027).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1027, Integer.Sparse.eval]

theorem keyMoment1028 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1028) =
      Integer.Sparse.eval keyMomentRow1028 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1028).leftCharge (GramAssembly.key 1028).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 612) := by
    have ha : gramCharges (GramAssembly.key 1028).leftCharge (GramAssembly.key 1028).rightCharge = raw40467 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40467Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40467 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1028).leftCharge (GramAssembly.key 1028).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1028, Integer.Sparse.eval]

theorem keyMoment1029 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1029) =
      Integer.Sparse.eval keyMomentRow1029 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1029).leftCharge (GramAssembly.key 1029).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 954) := by
    have ha : gramCharges (GramAssembly.key 1029).leftCharge (GramAssembly.key 1029).rightCharge = raw40468 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40468Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40468 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1029).leftCharge (GramAssembly.key 1029).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1029, Integer.Sparse.eval]

theorem keyMoment1030 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1030) =
      Integer.Sparse.eval keyMomentRow1030 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1030).leftCharge (GramAssembly.key 1030).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 590) := by
    have ha : gramCharges (GramAssembly.key 1030).leftCharge (GramAssembly.key 1030).rightCharge = raw40469 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40469Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40469 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1030).leftCharge (GramAssembly.key 1030).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1030, Integer.Sparse.eval]

theorem keyMoment1031 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1031) =
      Integer.Sparse.eval keyMomentRow1031 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1031).leftCharge (GramAssembly.key 1031).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 940) := by
    have ha : gramCharges (GramAssembly.key 1031).leftCharge (GramAssembly.key 1031).rightCharge = raw40470 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40470Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40470 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1031).leftCharge (GramAssembly.key 1031).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1031, Integer.Sparse.eval]

theorem keyMoment1032 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1032) =
      Integer.Sparse.eval keyMomentRow1032 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1032).leftCharge (GramAssembly.key 1032).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1047) := by
    have ha : gramCharges (GramAssembly.key 1032).leftCharge (GramAssembly.key 1032).rightCharge = raw40471 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40471Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40471 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1032).leftCharge (GramAssembly.key 1032).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1032, Integer.Sparse.eval]

theorem keyMoment1033 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1033) =
      Integer.Sparse.eval keyMomentRow1033 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1033).leftCharge (GramAssembly.key 1033).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2346) := by
    have ha : gramCharges (GramAssembly.key 1033).leftCharge (GramAssembly.key 1033).rightCharge = raw40472 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40472Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40472 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1033).leftCharge (GramAssembly.key 1033).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1033, Integer.Sparse.eval]

theorem keyMoment1034 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1034) =
      Integer.Sparse.eval keyMomentRow1034 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1034).leftCharge (GramAssembly.key 1034).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 949) := by
    have ha : gramCharges (GramAssembly.key 1034).leftCharge (GramAssembly.key 1034).rightCharge = raw40473 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40473Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40473 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1034).leftCharge (GramAssembly.key 1034).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1034, Integer.Sparse.eval]

theorem keyMoment1035 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1035) =
      Integer.Sparse.eval keyMomentRow1035 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1035).leftCharge (GramAssembly.key 1035).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 585) := by
    have ha : gramCharges (GramAssembly.key 1035).leftCharge (GramAssembly.key 1035).rightCharge = raw40474 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40474Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40474 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1035).leftCharge (GramAssembly.key 1035).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1035, Integer.Sparse.eval]

theorem keyMoment1036 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1036) =
      Integer.Sparse.eval keyMomentRow1036 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1036).leftCharge (GramAssembly.key 1036).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 931) := by
    have ha : gramCharges (GramAssembly.key 1036).leftCharge (GramAssembly.key 1036).rightCharge = raw40475 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40475Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40475 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1036).leftCharge (GramAssembly.key 1036).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1036, Integer.Sparse.eval]

theorem keyMoment1037 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1037) =
      Integer.Sparse.eval keyMomentRow1037 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1037).leftCharge (GramAssembly.key 1037).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1024) := by
    have ha : gramCharges (GramAssembly.key 1037).leftCharge (GramAssembly.key 1037).rightCharge = raw40476 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40476Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40476 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1037).leftCharge (GramAssembly.key 1037).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1037, Integer.Sparse.eval]

theorem keyMoment1038 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1038) =
      Integer.Sparse.eval keyMomentRow1038 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1038).leftCharge (GramAssembly.key 1038).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2340) := by
    have ha : gramCharges (GramAssembly.key 1038).leftCharge (GramAssembly.key 1038).rightCharge = raw40477 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40477Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40477 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1038).leftCharge (GramAssembly.key 1038).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1038, Integer.Sparse.eval]

theorem keyMoment1039 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1039) =
      Integer.Sparse.eval keyMomentRow1039 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1039).leftCharge (GramAssembly.key 1039).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 914) := by
    have ha : gramCharges (GramAssembly.key 1039).leftCharge (GramAssembly.key 1039).rightCharge = raw40478 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40478Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40478 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1039).leftCharge (GramAssembly.key 1039).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1039, Integer.Sparse.eval]

theorem keyMoment1040 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1040) =
      Integer.Sparse.eval keyMomentRow1040 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1040).leftCharge (GramAssembly.key 1040).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2327) := by
    have ha : gramCharges (GramAssembly.key 1040).leftCharge (GramAssembly.key 1040).rightCharge = raw40479 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40479Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40479 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1040).leftCharge (GramAssembly.key 1040).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1040, Integer.Sparse.eval]

theorem keyMoment1041 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1041) =
      Integer.Sparse.eval keyMomentRow1041 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1041).leftCharge (GramAssembly.key 1041).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 909) := by
    have ha : gramCharges (GramAssembly.key 1041).leftCharge (GramAssembly.key 1041).rightCharge = raw40480 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40480Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40480 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1041).leftCharge (GramAssembly.key 1041).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1041, Integer.Sparse.eval]

theorem keyMoment1042 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1042) =
      Integer.Sparse.eval keyMomentRow1042 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1042).leftCharge (GramAssembly.key 1042).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2323) := by
    have ha : gramCharges (GramAssembly.key 1042).leftCharge (GramAssembly.key 1042).rightCharge = raw40481 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40481Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40481 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1042).leftCharge (GramAssembly.key 1042).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1042, Integer.Sparse.eval]

theorem keyMoment1043 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1043) =
      Integer.Sparse.eval keyMomentRow1043 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1043).leftCharge (GramAssembly.key 1043).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1438) := by
    have ha : gramCharges (GramAssembly.key 1043).leftCharge (GramAssembly.key 1043).rightCharge = raw40482 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40482Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40482 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1043).leftCharge (GramAssembly.key 1043).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1043, Integer.Sparse.eval]

theorem keyMoment1044 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1044) =
      Integer.Sparse.eval keyMomentRow1044 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1044).leftCharge (GramAssembly.key 1044).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1348) := by
    have ha : gramCharges (GramAssembly.key 1044).leftCharge (GramAssembly.key 1044).rightCharge = raw40483 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40483Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40483 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1044).leftCharge (GramAssembly.key 1044).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1044, Integer.Sparse.eval]

theorem keyMoment1045 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1045) =
      Integer.Sparse.eval keyMomentRow1045 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1045).leftCharge (GramAssembly.key 1045).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1369) := by
    have ha : gramCharges (GramAssembly.key 1045).leftCharge (GramAssembly.key 1045).rightCharge = raw40484 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40484Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40484 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1045).leftCharge (GramAssembly.key 1045).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1045, Integer.Sparse.eval]

theorem keyMoment1046 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1046) =
      Integer.Sparse.eval keyMomentRow1046 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1046).leftCharge (GramAssembly.key 1046).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1408) := by
    have ha : gramCharges (GramAssembly.key 1046).leftCharge (GramAssembly.key 1046).rightCharge = raw40485 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40485Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40485 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1046).leftCharge (GramAssembly.key 1046).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1046, Integer.Sparse.eval]

theorem keyMoment1047 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1047) =
      Integer.Sparse.eval keyMomentRow1047 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1047).leftCharge (GramAssembly.key 1047).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1323) := by
    have ha : gramCharges (GramAssembly.key 1047).leftCharge (GramAssembly.key 1047).rightCharge = raw40486 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40486Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40486 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1047).leftCharge (GramAssembly.key 1047).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1047, Integer.Sparse.eval]

theorem keyMoment1048 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1048) =
      Integer.Sparse.eval keyMomentRow1048 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1048).leftCharge (GramAssembly.key 1048).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1336) := by
    have ha : gramCharges (GramAssembly.key 1048).leftCharge (GramAssembly.key 1048).rightCharge = raw40487 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40487Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40487 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1048).leftCharge (GramAssembly.key 1048).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1048, Integer.Sparse.eval]

theorem keyMoment1049 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1049) =
      Integer.Sparse.eval keyMomentRow1049 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1049).leftCharge (GramAssembly.key 1049).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1332) := by
    have ha : gramCharges (GramAssembly.key 1049).leftCharge (GramAssembly.key 1049).rightCharge = raw40488 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40488Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40488 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1049).leftCharge (GramAssembly.key 1049).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1049, Integer.Sparse.eval]

theorem keyMoment1050 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1050) =
      Integer.Sparse.eval keyMomentRow1050 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1050).leftCharge (GramAssembly.key 1050).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1315) := by
    have ha : gramCharges (GramAssembly.key 1050).leftCharge (GramAssembly.key 1050).rightCharge = raw40489 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40489Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40489 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1050).leftCharge (GramAssembly.key 1050).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1050, Integer.Sparse.eval]

theorem keyMoment1051 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1051) =
      Integer.Sparse.eval keyMomentRow1051 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1051).leftCharge (GramAssembly.key 1051).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1385) := by
    have ha : gramCharges (GramAssembly.key 1051).leftCharge (GramAssembly.key 1051).rightCharge = raw40490 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40490Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40490 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1051).leftCharge (GramAssembly.key 1051).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1051, Integer.Sparse.eval]

theorem keyMoment1052 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1052) =
      Integer.Sparse.eval keyMomentRow1052 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1052).leftCharge (GramAssembly.key 1052).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1326) := by
    have ha : gramCharges (GramAssembly.key 1052).leftCharge (GramAssembly.key 1052).rightCharge = raw40491 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40491Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40491 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1052).leftCharge (GramAssembly.key 1052).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1052, Integer.Sparse.eval]

theorem keyMoment1053 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1053) =
      Integer.Sparse.eval keyMomentRow1053 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1053).leftCharge (GramAssembly.key 1053).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1436) := by
    have ha : gramCharges (GramAssembly.key 1053).leftCharge (GramAssembly.key 1053).rightCharge = raw40492 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40492Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40492 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1053).leftCharge (GramAssembly.key 1053).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1053, Integer.Sparse.eval]

theorem keyMoment1054 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1054) =
      Integer.Sparse.eval keyMomentRow1054 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1054).leftCharge (GramAssembly.key 1054).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1367) := by
    have ha : gramCharges (GramAssembly.key 1054).leftCharge (GramAssembly.key 1054).rightCharge = raw40493 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40493Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40493 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1054).leftCharge (GramAssembly.key 1054).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1054, Integer.Sparse.eval]

theorem keyMoment1055 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1055) =
      Integer.Sparse.eval keyMomentRow1055 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1055).leftCharge (GramAssembly.key 1055).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1406) := by
    have ha : gramCharges (GramAssembly.key 1055).leftCharge (GramAssembly.key 1055).rightCharge = raw40494 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40494Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40494 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1055).leftCharge (GramAssembly.key 1055).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1055, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
