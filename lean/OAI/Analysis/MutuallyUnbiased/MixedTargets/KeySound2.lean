import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical308

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment64 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 64) =
      Integer.Sparse.eval keyMomentRow64 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 64).leftCharge (GramAssembly.key 64).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 159) := by
    have ha : gramCharges (GramAssembly.key 64).leftCharge (GramAssembly.key 64).rightCharge = raw39514 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39514Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39514 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 64).leftCharge (GramAssembly.key 64).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow64, Integer.Sparse.eval]

theorem keyMoment65 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 65) =
      Integer.Sparse.eval keyMomentRow65 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 65).leftCharge (GramAssembly.key 65).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 388) := by
    have ha : gramCharges (GramAssembly.key 65).leftCharge (GramAssembly.key 65).rightCharge = raw39515 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39515Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39515 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 65).leftCharge (GramAssembly.key 65).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow65, Integer.Sparse.eval]

theorem keyMoment66 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 66) =
      Integer.Sparse.eval keyMomentRow66 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 66).leftCharge (GramAssembly.key 66).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 148) := by
    have ha : gramCharges (GramAssembly.key 66).leftCharge (GramAssembly.key 66).rightCharge = raw39516 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39516Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39516 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 66).leftCharge (GramAssembly.key 66).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow66, Integer.Sparse.eval]

theorem keyMoment67 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 67) =
      Integer.Sparse.eval keyMomentRow67 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 67).leftCharge (GramAssembly.key 67).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 342) := by
    have ha : gramCharges (GramAssembly.key 67).leftCharge (GramAssembly.key 67).rightCharge = raw39517 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39517Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39517 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 67).leftCharge (GramAssembly.key 67).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow67, Integer.Sparse.eval]

theorem keyMoment68 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 68) =
      Integer.Sparse.eval keyMomentRow68 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 68).leftCharge (GramAssembly.key 68).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 406) := by
    have ha : gramCharges (GramAssembly.key 68).leftCharge (GramAssembly.key 68).rightCharge = raw39518 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39518Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39518 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 68).leftCharge (GramAssembly.key 68).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow68, Integer.Sparse.eval]

theorem keyMoment69 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 69) =
      Integer.Sparse.eval keyMomentRow69 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 69).leftCharge (GramAssembly.key 69).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 413) := by
    have ha : gramCharges (GramAssembly.key 69).leftCharge (GramAssembly.key 69).rightCharge = raw39519 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39519Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39519 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 69).leftCharge (GramAssembly.key 69).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow69, Integer.Sparse.eval]

theorem keyMoment70 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 70) =
      Integer.Sparse.eval keyMomentRow70 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 70).leftCharge (GramAssembly.key 70).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 416) := by
    have ha : gramCharges (GramAssembly.key 70).leftCharge (GramAssembly.key 70).rightCharge = raw39520 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39520Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39520 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 70).leftCharge (GramAssembly.key 70).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow70, Integer.Sparse.eval]

theorem keyMoment71 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 71) =
      Integer.Sparse.eval keyMomentRow71 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 71).leftCharge (GramAssembly.key 71).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 340) := by
    have ha : gramCharges (GramAssembly.key 71).leftCharge (GramAssembly.key 71).rightCharge = raw39521 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39521Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39521 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 71).leftCharge (GramAssembly.key 71).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow71, Integer.Sparse.eval]

theorem keyMoment72 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 72) =
      Integer.Sparse.eval keyMomentRow72 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 72).leftCharge (GramAssembly.key 72).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 387) := by
    have ha : gramCharges (GramAssembly.key 72).leftCharge (GramAssembly.key 72).rightCharge = raw39522 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39522Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39522 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 72).leftCharge (GramAssembly.key 72).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow72, Integer.Sparse.eval]

theorem keyMoment73 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 73) =
      Integer.Sparse.eval keyMomentRow73 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 73).leftCharge (GramAssembly.key 73).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 328) := by
    have ha : gramCharges (GramAssembly.key 73).leftCharge (GramAssembly.key 73).rightCharge = raw39523 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39523Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39523 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 73).leftCharge (GramAssembly.key 73).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow73, Integer.Sparse.eval]

theorem keyMoment74 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 74) =
      Integer.Sparse.eval keyMomentRow74 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 74).leftCharge (GramAssembly.key 74).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 367) := by
    have ha : gramCharges (GramAssembly.key 74).leftCharge (GramAssembly.key 74).rightCharge = raw39524 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39524Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39524 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 74).leftCharge (GramAssembly.key 74).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow74, Integer.Sparse.eval]

theorem keyMoment75 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 75) =
      Integer.Sparse.eval keyMomentRow75 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 75).leftCharge (GramAssembly.key 75).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 271) := by
    have ha : gramCharges (GramAssembly.key 75).leftCharge (GramAssembly.key 75).rightCharge = raw39525 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39525Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39525 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 75).leftCharge (GramAssembly.key 75).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow75, Integer.Sparse.eval]

theorem keyMoment76 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 76) =
      Integer.Sparse.eval keyMomentRow76 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 76).leftCharge (GramAssembly.key 76).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 264) := by
    have ha : gramCharges (GramAssembly.key 76).leftCharge (GramAssembly.key 76).rightCharge = raw39526 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39526Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39526 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 76).leftCharge (GramAssembly.key 76).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow76, Integer.Sparse.eval]

theorem keyMoment77 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 77) =
      Integer.Sparse.eval keyMomentRow77 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 77).leftCharge (GramAssembly.key 77).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 250) := by
    have ha : gramCharges (GramAssembly.key 77).leftCharge (GramAssembly.key 77).rightCharge = raw39527 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39527Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39527 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 77).leftCharge (GramAssembly.key 77).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow77, Integer.Sparse.eval]

theorem keyMoment78 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 78) =
      Integer.Sparse.eval keyMomentRow78 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 78).leftCharge (GramAssembly.key 78).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 188) := by
    have ha : gramCharges (GramAssembly.key 78).leftCharge (GramAssembly.key 78).rightCharge = raw39528 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39528Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39528 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 78).leftCharge (GramAssembly.key 78).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow78, Integer.Sparse.eval]

theorem keyMoment79 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 79) =
      Integer.Sparse.eval keyMomentRow79 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 79).leftCharge (GramAssembly.key 79).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 228) := by
    have ha : gramCharges (GramAssembly.key 79).leftCharge (GramAssembly.key 79).rightCharge = raw39529 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39529Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39529 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 79).leftCharge (GramAssembly.key 79).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow79, Integer.Sparse.eval]

theorem keyMoment80 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 80) =
      Integer.Sparse.eval keyMomentRow80 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 80).leftCharge (GramAssembly.key 80).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 225) := by
    have ha : gramCharges (GramAssembly.key 80).leftCharge (GramAssembly.key 80).rightCharge = raw39530 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39530Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39530 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 80).leftCharge (GramAssembly.key 80).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow80, Integer.Sparse.eval]

theorem keyMoment81 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 81) =
      Integer.Sparse.eval keyMomentRow81 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 81).leftCharge (GramAssembly.key 81).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 181) := by
    have ha : gramCharges (GramAssembly.key 81).leftCharge (GramAssembly.key 81).rightCharge = raw39531 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39531Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39531 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 81).leftCharge (GramAssembly.key 81).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow81, Integer.Sparse.eval]

theorem keyMoment82 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 82) =
      Integer.Sparse.eval keyMomentRow82 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 82).leftCharge (GramAssembly.key 82).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 170) := by
    have ha : gramCharges (GramAssembly.key 82).leftCharge (GramAssembly.key 82).rightCharge = raw39532 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39532Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39532 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 82).leftCharge (GramAssembly.key 82).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow82, Integer.Sparse.eval]

theorem keyMoment83 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 83) =
      Integer.Sparse.eval keyMomentRow83 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 83).leftCharge (GramAssembly.key 83).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 194) := by
    have ha : gramCharges (GramAssembly.key 83).leftCharge (GramAssembly.key 83).rightCharge = raw39533 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39533Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39533 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 83).leftCharge (GramAssembly.key 83).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow83, Integer.Sparse.eval]

theorem keyMoment84 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 84) =
      Integer.Sparse.eval keyMomentRow84 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 84).leftCharge (GramAssembly.key 84).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 225) := by
    have ha : gramCharges (GramAssembly.key 84).leftCharge (GramAssembly.key 84).rightCharge = raw39534 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39534Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39534 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 84).leftCharge (GramAssembly.key 84).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow84, Integer.Sparse.eval]

theorem keyMoment85 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 85) =
      Integer.Sparse.eval keyMomentRow85 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 85).leftCharge (GramAssembly.key 85).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 258) := by
    have ha : gramCharges (GramAssembly.key 85).leftCharge (GramAssembly.key 85).rightCharge = raw39535 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39535Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39535 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 85).leftCharge (GramAssembly.key 85).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow85, Integer.Sparse.eval]

theorem keyMoment86 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 86) =
      Integer.Sparse.eval keyMomentRow86 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 86).leftCharge (GramAssembly.key 86).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 166) := by
    have ha : gramCharges (GramAssembly.key 86).leftCharge (GramAssembly.key 86).rightCharge = raw39536 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39536Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39536 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 86).leftCharge (GramAssembly.key 86).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow86, Integer.Sparse.eval]

theorem keyMoment87 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 87) =
      Integer.Sparse.eval keyMomentRow87 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 87).leftCharge (GramAssembly.key 87).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 208) := by
    have ha : gramCharges (GramAssembly.key 87).leftCharge (GramAssembly.key 87).rightCharge = raw39537 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39537Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39537 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 87).leftCharge (GramAssembly.key 87).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow87, Integer.Sparse.eval]

theorem keyMoment88 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 88) =
      Integer.Sparse.eval keyMomentRow88 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 88).leftCharge (GramAssembly.key 88).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 218) := by
    have ha : gramCharges (GramAssembly.key 88).leftCharge (GramAssembly.key 88).rightCharge = raw39538 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39538Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39538 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 88).leftCharge (GramAssembly.key 88).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow88, Integer.Sparse.eval]

theorem keyMoment89 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 89) =
      Integer.Sparse.eval keyMomentRow89 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 89).leftCharge (GramAssembly.key 89).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 166) := by
    have ha : gramCharges (GramAssembly.key 89).leftCharge (GramAssembly.key 89).rightCharge = raw39539 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39539Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39539 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 89).leftCharge (GramAssembly.key 89).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow89, Integer.Sparse.eval]

theorem keyMoment90 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 90) =
      Integer.Sparse.eval keyMomentRow90 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 90).leftCharge (GramAssembly.key 90).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 264) := by
    have ha : gramCharges (GramAssembly.key 90).leftCharge (GramAssembly.key 90).rightCharge = raw39540 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39540Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39540 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 90).leftCharge (GramAssembly.key 90).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow90, Integer.Sparse.eval]

theorem keyMoment91 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 91) =
      Integer.Sparse.eval keyMomentRow91 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 91).leftCharge (GramAssembly.key 91).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 263) := by
    have ha : gramCharges (GramAssembly.key 91).leftCharge (GramAssembly.key 91).rightCharge = raw39541 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39541Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39541 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 91).leftCharge (GramAssembly.key 91).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow91, Integer.Sparse.eval]

theorem keyMoment92 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 92) =
      Integer.Sparse.eval keyMomentRow92 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 92).leftCharge (GramAssembly.key 92).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 246) := by
    have ha : gramCharges (GramAssembly.key 92).leftCharge (GramAssembly.key 92).rightCharge = raw39542 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39542Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39542 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 92).leftCharge (GramAssembly.key 92).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow92, Integer.Sparse.eval]

theorem keyMoment93 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 93) =
      Integer.Sparse.eval keyMomentRow93 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 93).leftCharge (GramAssembly.key 93).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 193) := by
    have ha : gramCharges (GramAssembly.key 93).leftCharge (GramAssembly.key 93).rightCharge = raw39543 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39543Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39543 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 93).leftCharge (GramAssembly.key 93).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow93, Integer.Sparse.eval]

theorem keyMoment94 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 94) =
      Integer.Sparse.eval keyMomentRow94 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 94).leftCharge (GramAssembly.key 94).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 165) := by
    have ha : gramCharges (GramAssembly.key 94).leftCharge (GramAssembly.key 94).rightCharge = raw39544 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39544Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39544 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 94).leftCharge (GramAssembly.key 94).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow94, Integer.Sparse.eval]

theorem keyMoment95 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 95) =
      Integer.Sparse.eval keyMomentRow95 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 95).leftCharge (GramAssembly.key 95).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 191) := by
    have ha : gramCharges (GramAssembly.key 95).leftCharge (GramAssembly.key 95).rightCharge = raw39545 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39545Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39545 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 95).leftCharge (GramAssembly.key 95).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow95, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
