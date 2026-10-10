import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical310

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment256 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 256) =
      Integer.Sparse.eval keyMomentRow256 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 256).leftCharge (GramAssembly.key 256).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 496) := by
    have ha : gramCharges (GramAssembly.key 256).leftCharge (GramAssembly.key 256).rightCharge = raw39706 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39706Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39706 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 256).leftCharge (GramAssembly.key 256).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow256, Integer.Sparse.eval]

theorem keyMoment257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 257) =
      Integer.Sparse.eval keyMomentRow257 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 257).leftCharge (GramAssembly.key 257).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 268) := by
    have ha : gramCharges (GramAssembly.key 257).leftCharge (GramAssembly.key 257).rightCharge = raw39707 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39707Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39707 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 257).leftCharge (GramAssembly.key 257).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow257, Integer.Sparse.eval]

theorem keyMoment258 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 258) =
      Integer.Sparse.eval keyMomentRow258 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 258).leftCharge (GramAssembly.key 258).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 504) := by
    have ha : gramCharges (GramAssembly.key 258).leftCharge (GramAssembly.key 258).rightCharge = raw39708 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39708Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39708 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 258).leftCharge (GramAssembly.key 258).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow258, Integer.Sparse.eval]

theorem keyMoment259 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 259) =
      Integer.Sparse.eval keyMomentRow259 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 259).leftCharge (GramAssembly.key 259).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 467) := by
    have ha : gramCharges (GramAssembly.key 259).leftCharge (GramAssembly.key 259).rightCharge = raw39709 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39709Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39709 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 259).leftCharge (GramAssembly.key 259).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow259, Integer.Sparse.eval]

theorem keyMoment260 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 260) =
      Integer.Sparse.eval keyMomentRow260 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 260).leftCharge (GramAssembly.key 260).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 272) := by
    have ha : gramCharges (GramAssembly.key 260).leftCharge (GramAssembly.key 260).rightCharge = raw39710 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39710Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39710 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 260).leftCharge (GramAssembly.key 260).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow260, Integer.Sparse.eval]

theorem keyMoment261 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 261) =
      Integer.Sparse.eval keyMomentRow261 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 261).leftCharge (GramAssembly.key 261).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 469) := by
    have ha : gramCharges (GramAssembly.key 261).leftCharge (GramAssembly.key 261).rightCharge = raw39711 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39711Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39711 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 261).leftCharge (GramAssembly.key 261).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow261, Integer.Sparse.eval]

theorem keyMoment262 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 262) =
      Integer.Sparse.eval keyMomentRow262 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 262).leftCharge (GramAssembly.key 262).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 516) := by
    have ha : gramCharges (GramAssembly.key 262).leftCharge (GramAssembly.key 262).rightCharge = raw39712 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39712Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39712 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 262).leftCharge (GramAssembly.key 262).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow262, Integer.Sparse.eval]

theorem keyMoment263 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 263) =
      Integer.Sparse.eval keyMomentRow263 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 263).leftCharge (GramAssembly.key 263).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 410) := by
    have ha : gramCharges (GramAssembly.key 263).leftCharge (GramAssembly.key 263).rightCharge = raw39713 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39713Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39713 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 263).leftCharge (GramAssembly.key 263).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow263, Integer.Sparse.eval]

theorem keyMoment264 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 264) =
      Integer.Sparse.eval keyMomentRow264 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 264).leftCharge (GramAssembly.key 264).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 483) := by
    have ha : gramCharges (GramAssembly.key 264).leftCharge (GramAssembly.key 264).rightCharge = raw39714 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39714Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39714 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 264).leftCharge (GramAssembly.key 264).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow264, Integer.Sparse.eval]

theorem keyMoment265 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 265) =
      Integer.Sparse.eval keyMomentRow265 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 265).leftCharge (GramAssembly.key 265).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 498) := by
    have ha : gramCharges (GramAssembly.key 265).leftCharge (GramAssembly.key 265).rightCharge = raw39715 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39715Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39715 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 265).leftCharge (GramAssembly.key 265).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow265, Integer.Sparse.eval]

theorem keyMoment266 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 266) =
      Integer.Sparse.eval keyMomentRow266 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 266).leftCharge (GramAssembly.key 266).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 491) := by
    have ha : gramCharges (GramAssembly.key 266).leftCharge (GramAssembly.key 266).rightCharge = raw39716 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39716Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39716 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 266).leftCharge (GramAssembly.key 266).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow266, Integer.Sparse.eval]

theorem keyMoment267 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 267) =
      Integer.Sparse.eval keyMomentRow267 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 267).leftCharge (GramAssembly.key 267).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 514) := by
    have ha : gramCharges (GramAssembly.key 267).leftCharge (GramAssembly.key 267).rightCharge = raw39717 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39717Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39717 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 267).leftCharge (GramAssembly.key 267).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow267, Integer.Sparse.eval]

theorem keyMoment268 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 268) =
      Integer.Sparse.eval keyMomentRow268 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 268).leftCharge (GramAssembly.key 268).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 515) := by
    have ha : gramCharges (GramAssembly.key 268).leftCharge (GramAssembly.key 268).rightCharge = raw39718 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39718Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39718 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 268).leftCharge (GramAssembly.key 268).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow268, Integer.Sparse.eval]

theorem keyMoment269 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 269) =
      Integer.Sparse.eval keyMomentRow269 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 269).leftCharge (GramAssembly.key 269).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 512) := by
    have ha : gramCharges (GramAssembly.key 269).leftCharge (GramAssembly.key 269).rightCharge = raw39719 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39719Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39719 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 269).leftCharge (GramAssembly.key 269).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow269, Integer.Sparse.eval]

theorem keyMoment270 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 270) =
      Integer.Sparse.eval keyMomentRow270 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 270).leftCharge (GramAssembly.key 270).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 513) := by
    have ha : gramCharges (GramAssembly.key 270).leftCharge (GramAssembly.key 270).rightCharge = raw39720 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39720Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39720 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 270).leftCharge (GramAssembly.key 270).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow270, Integer.Sparse.eval]

theorem keyMoment271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 271) =
      Integer.Sparse.eval keyMomentRow271 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 271).leftCharge (GramAssembly.key 271).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 4) := by
    have ha : gramCharges (GramAssembly.key 271).leftCharge (GramAssembly.key 271).rightCharge = raw39721 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39721Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39721 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 271).leftCharge (GramAssembly.key 271).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow271, Integer.Sparse.eval]

theorem keyMoment272 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 272) =
      Integer.Sparse.eval keyMomentRow272 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 272).leftCharge (GramAssembly.key 272).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 489) := by
    have ha : gramCharges (GramAssembly.key 272).leftCharge (GramAssembly.key 272).rightCharge = raw39722 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39722Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39722 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 272).leftCharge (GramAssembly.key 272).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow272, Integer.Sparse.eval]

theorem keyMoment273 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 273) =
      Integer.Sparse.eval keyMomentRow273 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 273).leftCharge (GramAssembly.key 273).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 268) := by
    have ha : gramCharges (GramAssembly.key 273).leftCharge (GramAssembly.key 273).rightCharge = raw39723 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39723Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39723 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 273).leftCharge (GramAssembly.key 273).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow273, Integer.Sparse.eval]

theorem keyMoment274 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 274) =
      Integer.Sparse.eval keyMomentRow274 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 274).leftCharge (GramAssembly.key 274).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 467) := by
    have ha : gramCharges (GramAssembly.key 274).leftCharge (GramAssembly.key 274).rightCharge = raw39724 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39724Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39724 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 274).leftCharge (GramAssembly.key 274).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow274, Integer.Sparse.eval]

theorem keyMoment275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 275) =
      Integer.Sparse.eval keyMomentRow275 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 275).leftCharge (GramAssembly.key 275).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 498) := by
    have ha : gramCharges (GramAssembly.key 275).leftCharge (GramAssembly.key 275).rightCharge = raw39725 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39725Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39725 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 275).leftCharge (GramAssembly.key 275).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow275, Integer.Sparse.eval]

theorem keyMoment276 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 276) =
      Integer.Sparse.eval keyMomentRow276 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 276).leftCharge (GramAssembly.key 276).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 381) := by
    have ha : gramCharges (GramAssembly.key 276).leftCharge (GramAssembly.key 276).rightCharge = raw39726 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39726Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39726 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 276).leftCharge (GramAssembly.key 276).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow276, Integer.Sparse.eval]

theorem keyMoment277 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 277) =
      Integer.Sparse.eval keyMomentRow277 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 277).leftCharge (GramAssembly.key 277).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 480) := by
    have ha : gramCharges (GramAssembly.key 277).leftCharge (GramAssembly.key 277).rightCharge = raw39727 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39727Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39727 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 277).leftCharge (GramAssembly.key 277).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow277, Integer.Sparse.eval]

theorem keyMoment278 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 278) =
      Integer.Sparse.eval keyMomentRow278 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 278).leftCharge (GramAssembly.key 278).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 444) := by
    have ha : gramCharges (GramAssembly.key 278).leftCharge (GramAssembly.key 278).rightCharge = raw39728 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39728Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39728 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 278).leftCharge (GramAssembly.key 278).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow278, Integer.Sparse.eval]

theorem keyMoment279 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 279) =
      Integer.Sparse.eval keyMomentRow279 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 279).leftCharge (GramAssembly.key 279).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 443) := by
    have ha : gramCharges (GramAssembly.key 279).leftCharge (GramAssembly.key 279).rightCharge = raw39729 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39729Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39729 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 279).leftCharge (GramAssembly.key 279).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow279, Integer.Sparse.eval]

theorem keyMoment280 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 280) =
      Integer.Sparse.eval keyMomentRow280 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 280).leftCharge (GramAssembly.key 280).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 485) := by
    have ha : gramCharges (GramAssembly.key 280).leftCharge (GramAssembly.key 280).rightCharge = raw39730 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39730Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39730 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 280).leftCharge (GramAssembly.key 280).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow280, Integer.Sparse.eval]

theorem keyMoment281 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 281) =
      Integer.Sparse.eval keyMomentRow281 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 281).leftCharge (GramAssembly.key 281).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 499) := by
    have ha : gramCharges (GramAssembly.key 281).leftCharge (GramAssembly.key 281).rightCharge = raw39731 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39731Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39731 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 281).leftCharge (GramAssembly.key 281).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow281, Integer.Sparse.eval]

theorem keyMoment282 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 282) =
      Integer.Sparse.eval keyMomentRow282 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 282).leftCharge (GramAssembly.key 282).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 521) := by
    have ha : gramCharges (GramAssembly.key 282).leftCharge (GramAssembly.key 282).rightCharge = raw39732 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39732Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39732 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 282).leftCharge (GramAssembly.key 282).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow282, Integer.Sparse.eval]

theorem keyMoment283 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 283) =
      Integer.Sparse.eval keyMomentRow283 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 283).leftCharge (GramAssembly.key 283).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 479) := by
    have ha : gramCharges (GramAssembly.key 283).leftCharge (GramAssembly.key 283).rightCharge = raw39733 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39733Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39733 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 283).leftCharge (GramAssembly.key 283).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow283, Integer.Sparse.eval]

theorem keyMoment284 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 284) =
      Integer.Sparse.eval keyMomentRow284 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 284).leftCharge (GramAssembly.key 284).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 409) := by
    have ha : gramCharges (GramAssembly.key 284).leftCharge (GramAssembly.key 284).rightCharge = raw39734 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39734Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39734 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 284).leftCharge (GramAssembly.key 284).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow284, Integer.Sparse.eval]

theorem keyMoment285 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 285) =
      Integer.Sparse.eval keyMomentRow285 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 285).leftCharge (GramAssembly.key 285).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 387) := by
    have ha : gramCharges (GramAssembly.key 285).leftCharge (GramAssembly.key 285).rightCharge = raw39735 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39735Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39735 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 285).leftCharge (GramAssembly.key 285).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow285, Integer.Sparse.eval]

theorem keyMoment286 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 286) =
      Integer.Sparse.eval keyMomentRow286 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 286).leftCharge (GramAssembly.key 286).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 150) := by
    have ha : gramCharges (GramAssembly.key 286).leftCharge (GramAssembly.key 286).rightCharge = raw39736 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39736Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39736 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 286).leftCharge (GramAssembly.key 286).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow286, Integer.Sparse.eval]

theorem keyMoment287 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 287) =
      Integer.Sparse.eval keyMomentRow287 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 287).leftCharge (GramAssembly.key 287).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 145) := by
    have ha : gramCharges (GramAssembly.key 287).leftCharge (GramAssembly.key 287).rightCharge = raw39737 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39737Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39737 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 287).leftCharge (GramAssembly.key 287).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow287, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
