import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical309
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical310

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment224 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 224) =
      Integer.Sparse.eval keyMomentRow224 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 224).leftCharge (GramAssembly.key 224).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 487) := by
    have ha : gramCharges (GramAssembly.key 224).leftCharge (GramAssembly.key 224).rightCharge = raw39674 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39674Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39674 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 224).leftCharge (GramAssembly.key 224).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow224, Integer.Sparse.eval]

theorem keyMoment225 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 225) =
      Integer.Sparse.eval keyMomentRow225 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 225).leftCharge (GramAssembly.key 225).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 490) := by
    have ha : gramCharges (GramAssembly.key 225).leftCharge (GramAssembly.key 225).rightCharge = raw39675 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39675Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39675 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 225).leftCharge (GramAssembly.key 225).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow225, Integer.Sparse.eval]

theorem keyMoment226 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 226) =
      Integer.Sparse.eval keyMomentRow226 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 226).leftCharge (GramAssembly.key 226).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 409) := by
    have ha : gramCharges (GramAssembly.key 226).leftCharge (GramAssembly.key 226).rightCharge = raw39676 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39676Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39676 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 226).leftCharge (GramAssembly.key 226).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow226, Integer.Sparse.eval]

theorem keyMoment227 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 227) =
      Integer.Sparse.eval keyMomentRow227 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 227).leftCharge (GramAssembly.key 227).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 384) := by
    have ha : gramCharges (GramAssembly.key 227).leftCharge (GramAssembly.key 227).rightCharge = raw39677 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39677Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39677 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 227).leftCharge (GramAssembly.key 227).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow227, Integer.Sparse.eval]

theorem keyMoment228 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 228) =
      Integer.Sparse.eval keyMomentRow228 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 228).leftCharge (GramAssembly.key 228).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 485) := by
    have ha : gramCharges (GramAssembly.key 228).leftCharge (GramAssembly.key 228).rightCharge = raw39678 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39678Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39678 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 228).leftCharge (GramAssembly.key 228).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow228, Integer.Sparse.eval]

theorem keyMoment229 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 229) =
      Integer.Sparse.eval keyMomentRow229 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 229).leftCharge (GramAssembly.key 229).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 486) := by
    have ha : gramCharges (GramAssembly.key 229).leftCharge (GramAssembly.key 229).rightCharge = raw39679 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39679Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39679 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 229).leftCharge (GramAssembly.key 229).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow229, Integer.Sparse.eval]

theorem keyMoment230 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 230) =
      Integer.Sparse.eval keyMomentRow230 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 230).leftCharge (GramAssembly.key 230).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 487) := by
    have ha : gramCharges (GramAssembly.key 230).leftCharge (GramAssembly.key 230).rightCharge = raw39680 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39680Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39680 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 230).leftCharge (GramAssembly.key 230).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow230, Integer.Sparse.eval]

theorem keyMoment231 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 231) =
      Integer.Sparse.eval keyMomentRow231 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 231).leftCharge (GramAssembly.key 231).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 491) := by
    have ha : gramCharges (GramAssembly.key 231).leftCharge (GramAssembly.key 231).rightCharge = raw39681 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39681Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39681 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 231).leftCharge (GramAssembly.key 231).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow231, Integer.Sparse.eval]

theorem keyMoment232 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 232) =
      Integer.Sparse.eval keyMomentRow232 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 232).leftCharge (GramAssembly.key 232).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 484) := by
    have ha : gramCharges (GramAssembly.key 232).leftCharge (GramAssembly.key 232).rightCharge = raw39682 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39682Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39682 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 232).leftCharge (GramAssembly.key 232).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow232, Integer.Sparse.eval]

theorem keyMoment233 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 233) =
      Integer.Sparse.eval keyMomentRow233 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 233).leftCharge (GramAssembly.key 233).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 486) := by
    have ha : gramCharges (GramAssembly.key 233).leftCharge (GramAssembly.key 233).rightCharge = raw39683 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39683Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39683 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 233).leftCharge (GramAssembly.key 233).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow233, Integer.Sparse.eval]

theorem keyMoment234 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 234) =
      Integer.Sparse.eval keyMomentRow234 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 234).leftCharge (GramAssembly.key 234).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 501) := by
    have ha : gramCharges (GramAssembly.key 234).leftCharge (GramAssembly.key 234).rightCharge = raw39684 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39684Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39684 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 234).leftCharge (GramAssembly.key 234).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow234, Integer.Sparse.eval]

theorem keyMoment235 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 235) =
      Integer.Sparse.eval keyMomentRow235 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 235).leftCharge (GramAssembly.key 235).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 496) := by
    have ha : gramCharges (GramAssembly.key 235).leftCharge (GramAssembly.key 235).rightCharge = raw39685 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39685Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39685 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 235).leftCharge (GramAssembly.key 235).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow235, Integer.Sparse.eval]

theorem keyMoment236 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 236) =
      Integer.Sparse.eval keyMomentRow236 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 236).leftCharge (GramAssembly.key 236).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 410) := by
    have ha : gramCharges (GramAssembly.key 236).leftCharge (GramAssembly.key 236).rightCharge = raw39686 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39686Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39686 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 236).leftCharge (GramAssembly.key 236).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow236, Integer.Sparse.eval]

theorem keyMoment237 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 237) =
      Integer.Sparse.eval keyMomentRow237 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 237).leftCharge (GramAssembly.key 237).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 498) := by
    have ha : gramCharges (GramAssembly.key 237).leftCharge (GramAssembly.key 237).rightCharge = raw39687 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39687Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39687 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 237).leftCharge (GramAssembly.key 237).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow237, Integer.Sparse.eval]

theorem keyMoment238 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 238) =
      Integer.Sparse.eval keyMomentRow238 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 238).leftCharge (GramAssembly.key 238).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 500) := by
    have ha : gramCharges (GramAssembly.key 238).leftCharge (GramAssembly.key 238).rightCharge = raw39688 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39688Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39688 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 238).leftCharge (GramAssembly.key 238).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow238, Integer.Sparse.eval]

theorem keyMoment239 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 239) =
      Integer.Sparse.eval keyMomentRow239 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 239).leftCharge (GramAssembly.key 239).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 384) := by
    have ha : gramCharges (GramAssembly.key 239).leftCharge (GramAssembly.key 239).rightCharge = raw39689 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39689Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39689 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 239).leftCharge (GramAssembly.key 239).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow239, Integer.Sparse.eval]

theorem keyMoment240 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 240) =
      Integer.Sparse.eval keyMomentRow240 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 240).leftCharge (GramAssembly.key 240).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 385) := by
    have ha : gramCharges (GramAssembly.key 240).leftCharge (GramAssembly.key 240).rightCharge = raw39690 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39690Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39690 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 240).leftCharge (GramAssembly.key 240).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow240, Integer.Sparse.eval]

theorem keyMoment241 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 241) =
      Integer.Sparse.eval keyMomentRow241 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 241).leftCharge (GramAssembly.key 241).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 495) := by
    have ha : gramCharges (GramAssembly.key 241).leftCharge (GramAssembly.key 241).rightCharge = raw39691 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39691Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39691 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 241).leftCharge (GramAssembly.key 241).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow241, Integer.Sparse.eval]

theorem keyMoment242 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 242) =
      Integer.Sparse.eval keyMomentRow242 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 242).leftCharge (GramAssembly.key 242).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 405) := by
    have ha : gramCharges (GramAssembly.key 242).leftCharge (GramAssembly.key 242).rightCharge = raw39692 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39692Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39692 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 242).leftCharge (GramAssembly.key 242).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow242, Integer.Sparse.eval]

theorem keyMoment243 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 243) =
      Integer.Sparse.eval keyMomentRow243 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 243).leftCharge (GramAssembly.key 243).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 3) := by
    have ha : gramCharges (GramAssembly.key 243).leftCharge (GramAssembly.key 243).rightCharge = raw39693 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39693Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39693 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 243).leftCharge (GramAssembly.key 243).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow243, Integer.Sparse.eval]

theorem keyMoment244 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 244) =
      Integer.Sparse.eval keyMomentRow244 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 244).leftCharge (GramAssembly.key 244).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 468) := by
    have ha : gramCharges (GramAssembly.key 244).leftCharge (GramAssembly.key 244).rightCharge = raw39694 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39694Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39694 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 244).leftCharge (GramAssembly.key 244).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow244, Integer.Sparse.eval]

theorem keyMoment245 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 245) =
      Integer.Sparse.eval keyMomentRow245 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 245).leftCharge (GramAssembly.key 245).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 489) := by
    have ha : gramCharges (GramAssembly.key 245).leftCharge (GramAssembly.key 245).rightCharge = raw39695 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39695Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39695 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 245).leftCharge (GramAssembly.key 245).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow245, Integer.Sparse.eval]

theorem keyMoment246 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 246) =
      Integer.Sparse.eval keyMomentRow246 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 246).leftCharge (GramAssembly.key 246).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 490) := by
    have ha : gramCharges (GramAssembly.key 246).leftCharge (GramAssembly.key 246).rightCharge = raw39696 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39696Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39696 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 246).leftCharge (GramAssembly.key 246).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow246, Integer.Sparse.eval]

theorem keyMoment247 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 247) =
      Integer.Sparse.eval keyMomentRow247 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 247).leftCharge (GramAssembly.key 247).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 261) := by
    have ha : gramCharges (GramAssembly.key 247).leftCharge (GramAssembly.key 247).rightCharge = raw39697 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39697Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39697 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 247).leftCharge (GramAssembly.key 247).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow247, Integer.Sparse.eval]

theorem keyMoment248 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 248) =
      Integer.Sparse.eval keyMomentRow248 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 248).leftCharge (GramAssembly.key 248).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 462) := by
    have ha : gramCharges (GramAssembly.key 248).leftCharge (GramAssembly.key 248).rightCharge = raw39698 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39698Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39698 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 248).leftCharge (GramAssembly.key 248).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow248, Integer.Sparse.eval]

theorem keyMoment249 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 249) =
      Integer.Sparse.eval keyMomentRow249 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 249).leftCharge (GramAssembly.key 249).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 6) := by
    have ha : gramCharges (GramAssembly.key 249).leftCharge (GramAssembly.key 249).rightCharge = raw39699 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39699Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39699 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 249).leftCharge (GramAssembly.key 249).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow249, Integer.Sparse.eval]

theorem keyMoment250 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 250) =
      Integer.Sparse.eval keyMomentRow250 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 250).leftCharge (GramAssembly.key 250).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 507) := by
    have ha : gramCharges (GramAssembly.key 250).leftCharge (GramAssembly.key 250).rightCharge = raw39700 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39700Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39700 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 250).leftCharge (GramAssembly.key 250).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow250, Integer.Sparse.eval]

theorem keyMoment251 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 251) =
      Integer.Sparse.eval keyMomentRow251 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 251).leftCharge (GramAssembly.key 251).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 420) := by
    have ha : gramCharges (GramAssembly.key 251).leftCharge (GramAssembly.key 251).rightCharge = raw39701 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39701Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39701 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 251).leftCharge (GramAssembly.key 251).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow251, Integer.Sparse.eval]

theorem keyMoment252 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 252) =
      Integer.Sparse.eval keyMomentRow252 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 252).leftCharge (GramAssembly.key 252).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 5) := by
    have ha : gramCharges (GramAssembly.key 252).leftCharge (GramAssembly.key 252).rightCharge = raw39702 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39702Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39702 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 252).leftCharge (GramAssembly.key 252).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow252, Integer.Sparse.eval]

theorem keyMoment253 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 253) =
      Integer.Sparse.eval keyMomentRow253 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 253).leftCharge (GramAssembly.key 253).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 412) := by
    have ha : gramCharges (GramAssembly.key 253).leftCharge (GramAssembly.key 253).rightCharge = raw39703 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39703Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39703 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 253).leftCharge (GramAssembly.key 253).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow253, Integer.Sparse.eval]

theorem keyMoment254 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 254) =
      Integer.Sparse.eval keyMomentRow254 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 254).leftCharge (GramAssembly.key 254).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 503) := by
    have ha : gramCharges (GramAssembly.key 254).leftCharge (GramAssembly.key 254).rightCharge = raw39704 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39704Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39704 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 254).leftCharge (GramAssembly.key 254).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow254, Integer.Sparse.eval]

theorem keyMoment255 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 255) =
      Integer.Sparse.eval keyMomentRow255 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 255).leftCharge (GramAssembly.key 255).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 506) := by
    have ha : gramCharges (GramAssembly.key 255).leftCharge (GramAssembly.key 255).rightCharge = raw39705 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39705Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39705 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 255).leftCharge (GramAssembly.key 255).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow255, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
