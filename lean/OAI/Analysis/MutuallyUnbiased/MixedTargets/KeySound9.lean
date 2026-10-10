import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical310

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment288 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 288) =
      Integer.Sparse.eval keyMomentRow288 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 288).leftCharge (GramAssembly.key 288).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 330) := by
    have ha : gramCharges (GramAssembly.key 288).leftCharge (GramAssembly.key 288).rightCharge = raw39738 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39738Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39738 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 288).leftCharge (GramAssembly.key 288).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow288, Integer.Sparse.eval]

theorem keyMoment289 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 289) =
      Integer.Sparse.eval keyMomentRow289 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 289).leftCharge (GramAssembly.key 289).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 394) := by
    have ha : gramCharges (GramAssembly.key 289).leftCharge (GramAssembly.key 289).rightCharge = raw39739 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39739Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39739 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 289).leftCharge (GramAssembly.key 289).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow289, Integer.Sparse.eval]

theorem keyMoment290 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 290) =
      Integer.Sparse.eval keyMomentRow290 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 290).leftCharge (GramAssembly.key 290).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 491) := by
    have ha : gramCharges (GramAssembly.key 290).leftCharge (GramAssembly.key 290).rightCharge = raw39740 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39740Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39740 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 290).leftCharge (GramAssembly.key 290).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow290, Integer.Sparse.eval]

theorem keyMoment291 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 291) =
      Integer.Sparse.eval keyMomentRow291 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 291).leftCharge (GramAssembly.key 291).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 447) := by
    have ha : gramCharges (GramAssembly.key 291).leftCharge (GramAssembly.key 291).rightCharge = raw39741 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39741Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39741 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 291).leftCharge (GramAssembly.key 291).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow291, Integer.Sparse.eval]

theorem keyMoment292 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 292) =
      Integer.Sparse.eval keyMomentRow292 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 292).leftCharge (GramAssembly.key 292).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 470) := by
    have ha : gramCharges (GramAssembly.key 292).leftCharge (GramAssembly.key 292).rightCharge = raw39742 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39742Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39742 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 292).leftCharge (GramAssembly.key 292).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow292, Integer.Sparse.eval]

theorem keyMoment293 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 293) =
      Integer.Sparse.eval keyMomentRow293 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 293).leftCharge (GramAssembly.key 293).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 484) := by
    have ha : gramCharges (GramAssembly.key 293).leftCharge (GramAssembly.key 293).rightCharge = raw39743 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39743Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39743 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 293).leftCharge (GramAssembly.key 293).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow293, Integer.Sparse.eval]

theorem keyMoment294 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 294) =
      Integer.Sparse.eval keyMomentRow294 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 294).leftCharge (GramAssembly.key 294).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 483) := by
    have ha : gramCharges (GramAssembly.key 294).leftCharge (GramAssembly.key 294).rightCharge = raw39744 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39744Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39744 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 294).leftCharge (GramAssembly.key 294).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow294, Integer.Sparse.eval]

theorem keyMoment295 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 295) =
      Integer.Sparse.eval keyMomentRow295 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 295).leftCharge (GramAssembly.key 295).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 410) := by
    have ha : gramCharges (GramAssembly.key 295).leftCharge (GramAssembly.key 295).rightCharge = raw39745 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39745Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39745 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 295).leftCharge (GramAssembly.key 295).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow295, Integer.Sparse.eval]

theorem keyMoment296 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 296) =
      Integer.Sparse.eval keyMomentRow296 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 296).leftCharge (GramAssembly.key 296).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 390) := by
    have ha : gramCharges (GramAssembly.key 296).leftCharge (GramAssembly.key 296).rightCharge = raw39746 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39746Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39746 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 296).leftCharge (GramAssembly.key 296).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow296, Integer.Sparse.eval]

theorem keyMoment297 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 297) =
      Integer.Sparse.eval keyMomentRow297 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 297).leftCharge (GramAssembly.key 297).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 153) := by
    have ha : gramCharges (GramAssembly.key 297).leftCharge (GramAssembly.key 297).rightCharge = raw39747 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39747Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39747 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 297).leftCharge (GramAssembly.key 297).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow297, Integer.Sparse.eval]

theorem keyMoment298 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 298) =
      Integer.Sparse.eval keyMomentRow298 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 298).leftCharge (GramAssembly.key 298).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 333) := by
    have ha : gramCharges (GramAssembly.key 298).leftCharge (GramAssembly.key 298).rightCharge = raw39748 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39748Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39748 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 298).leftCharge (GramAssembly.key 298).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow298, Integer.Sparse.eval]

theorem keyMoment299 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 299) =
      Integer.Sparse.eval keyMomentRow299 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 299).leftCharge (GramAssembly.key 299).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 395) := by
    have ha : gramCharges (GramAssembly.key 299).leftCharge (GramAssembly.key 299).rightCharge = raw39749 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39749Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39749 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 299).leftCharge (GramAssembly.key 299).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow299, Integer.Sparse.eval]

theorem keyMoment300 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 300) =
      Integer.Sparse.eval keyMomentRow300 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 300).leftCharge (GramAssembly.key 300).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 346) := by
    have ha : gramCharges (GramAssembly.key 300).leftCharge (GramAssembly.key 300).rightCharge = raw39750 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39750Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39750 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 300).leftCharge (GramAssembly.key 300).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow300, Integer.Sparse.eval]

theorem keyMoment301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 301) =
      Integer.Sparse.eval keyMomentRow301 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 301).leftCharge (GramAssembly.key 301).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 147) := by
    have ha : gramCharges (GramAssembly.key 301).leftCharge (GramAssembly.key 301).rightCharge = raw39751 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39751Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39751 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 301).leftCharge (GramAssembly.key 301).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow301, Integer.Sparse.eval]

theorem keyMoment302 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 302) =
      Integer.Sparse.eval keyMomentRow302 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 302).leftCharge (GramAssembly.key 302).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 420) := by
    have ha : gramCharges (GramAssembly.key 302).leftCharge (GramAssembly.key 302).rightCharge = raw39752 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39752Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39752 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 302).leftCharge (GramAssembly.key 302).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow302, Integer.Sparse.eval]

theorem keyMoment303 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 303) =
      Integer.Sparse.eval keyMomentRow303 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 303).leftCharge (GramAssembly.key 303).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 496) := by
    have ha : gramCharges (GramAssembly.key 303).leftCharge (GramAssembly.key 303).rightCharge = raw39753 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39753Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39753 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 303).leftCharge (GramAssembly.key 303).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow303, Integer.Sparse.eval]

theorem keyMoment304 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 304) =
      Integer.Sparse.eval keyMomentRow304 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 304).leftCharge (GramAssembly.key 304).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 402) := by
    have ha : gramCharges (GramAssembly.key 304).leftCharge (GramAssembly.key 304).rightCharge = raw39754 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39754Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39754 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 304).leftCharge (GramAssembly.key 304).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow304, Integer.Sparse.eval]

theorem keyMoment305 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 305) =
      Integer.Sparse.eval keyMomentRow305 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 305).leftCharge (GramAssembly.key 305).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 503) := by
    have ha : gramCharges (GramAssembly.key 305).leftCharge (GramAssembly.key 305).rightCharge = raw39755 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39755Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39755 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 305).leftCharge (GramAssembly.key 305).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow305, Integer.Sparse.eval]

theorem keyMoment306 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 306) =
      Integer.Sparse.eval keyMomentRow306 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 306).leftCharge (GramAssembly.key 306).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 446) := by
    have ha : gramCharges (GramAssembly.key 306).leftCharge (GramAssembly.key 306).rightCharge = raw39756 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39756Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39756 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 306).leftCharge (GramAssembly.key 306).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow306, Integer.Sparse.eval]

theorem keyMoment307 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 307) =
      Integer.Sparse.eval keyMomentRow307 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 307).leftCharge (GramAssembly.key 307).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 493) := by
    have ha : gramCharges (GramAssembly.key 307).leftCharge (GramAssembly.key 307).rightCharge = raw39757 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39757Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39757 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 307).leftCharge (GramAssembly.key 307).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow307, Integer.Sparse.eval]

theorem keyMoment308 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 308) =
      Integer.Sparse.eval keyMomentRow308 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 308).leftCharge (GramAssembly.key 308).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 487) := by
    have ha : gramCharges (GramAssembly.key 308).leftCharge (GramAssembly.key 308).rightCharge = raw39758 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39758Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39758 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 308).leftCharge (GramAssembly.key 308).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow308, Integer.Sparse.eval]

theorem keyMoment309 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 309) =
      Integer.Sparse.eval keyMomentRow309 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 309).leftCharge (GramAssembly.key 309).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 244) := by
    have ha : gramCharges (GramAssembly.key 309).leftCharge (GramAssembly.key 309).rightCharge = raw39759 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39759Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39759 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 309).leftCharge (GramAssembly.key 309).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow309, Integer.Sparse.eval]

theorem keyMoment310 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 310) =
      Integer.Sparse.eval keyMomentRow310 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 310).leftCharge (GramAssembly.key 310).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 456) := by
    have ha : gramCharges (GramAssembly.key 310).leftCharge (GramAssembly.key 310).rightCharge = raw39760 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39760Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39760 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 310).leftCharge (GramAssembly.key 310).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow310, Integer.Sparse.eval]

theorem keyMoment311 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 311) =
      Integer.Sparse.eval keyMomentRow311 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 311).leftCharge (GramAssembly.key 311).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 494) := by
    have ha : gramCharges (GramAssembly.key 311).leftCharge (GramAssembly.key 311).rightCharge = raw39761 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39761Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39761 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 311).leftCharge (GramAssembly.key 311).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow311, Integer.Sparse.eval]

theorem keyMoment312 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 312) =
      Integer.Sparse.eval keyMomentRow312 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 312).leftCharge (GramAssembly.key 312).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 248) := by
    have ha : gramCharges (GramAssembly.key 312).leftCharge (GramAssembly.key 312).rightCharge = raw39762 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39762Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39762 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 312).leftCharge (GramAssembly.key 312).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow312, Integer.Sparse.eval]

theorem keyMoment313 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 313) =
      Integer.Sparse.eval keyMomentRow313 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 313).leftCharge (GramAssembly.key 313).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 459) := by
    have ha : gramCharges (GramAssembly.key 313).leftCharge (GramAssembly.key 313).rightCharge = raw39763 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39763Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39763 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 313).leftCharge (GramAssembly.key 313).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow313, Integer.Sparse.eval]

theorem keyMoment314 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 314) =
      Integer.Sparse.eval keyMomentRow314 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 314).leftCharge (GramAssembly.key 314).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 5) := by
    have ha : gramCharges (GramAssembly.key 314).leftCharge (GramAssembly.key 314).rightCharge = raw39764 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39764Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39764 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 314).leftCharge (GramAssembly.key 314).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow314, Integer.Sparse.eval]

theorem keyMoment315 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 315) =
      Integer.Sparse.eval keyMomentRow315 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 315).leftCharge (GramAssembly.key 315).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 496) := by
    have ha : gramCharges (GramAssembly.key 315).leftCharge (GramAssembly.key 315).rightCharge = raw39765 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39765Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39765 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 315).leftCharge (GramAssembly.key 315).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow315, Integer.Sparse.eval]

theorem keyMoment316 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 316) =
      Integer.Sparse.eval keyMomentRow316 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 316).leftCharge (GramAssembly.key 316).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 249) := by
    have ha : gramCharges (GramAssembly.key 316).leftCharge (GramAssembly.key 316).rightCharge = raw39766 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39766Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39766 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 316).leftCharge (GramAssembly.key 316).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow316, Integer.Sparse.eval]

theorem keyMoment317 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 317) =
      Integer.Sparse.eval keyMomentRow317 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 317).leftCharge (GramAssembly.key 317).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 494) := by
    have ha : gramCharges (GramAssembly.key 317).leftCharge (GramAssembly.key 317).rightCharge = raw39767 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39767Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39767 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 317).leftCharge (GramAssembly.key 317).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow317, Integer.Sparse.eval]

theorem keyMoment318 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 318) =
      Integer.Sparse.eval keyMomentRow318 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 318).leftCharge (GramAssembly.key 318).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 337) := by
    have ha : gramCharges (GramAssembly.key 318).leftCharge (GramAssembly.key 318).rightCharge = raw39768 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39768Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39768 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 318).leftCharge (GramAssembly.key 318).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow318, Integer.Sparse.eval]

theorem keyMoment319 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 319) =
      Integer.Sparse.eval keyMomentRow319 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 319).leftCharge (GramAssembly.key 319).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 420) := by
    have ha : gramCharges (GramAssembly.key 319).leftCharge (GramAssembly.key 319).rightCharge = raw39769 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39769Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39769 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 319).leftCharge (GramAssembly.key 319).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow319, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
