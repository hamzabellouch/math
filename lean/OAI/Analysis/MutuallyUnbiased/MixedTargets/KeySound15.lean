import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical311
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical312

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment480 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 480) =
      Integer.Sparse.eval keyMomentRow480 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 480).leftCharge (GramAssembly.key 480).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 420) := by
    have ha : gramCharges (GramAssembly.key 480).leftCharge (GramAssembly.key 480).rightCharge = raw39928 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39928Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39928 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 480).leftCharge (GramAssembly.key 480).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow480, Integer.Sparse.eval]

theorem keyMoment481 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 481) =
      Integer.Sparse.eval keyMomentRow481 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 481).leftCharge (GramAssembly.key 481).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 33) := by
    have ha : gramCharges (GramAssembly.key 481).leftCharge (GramAssembly.key 481).rightCharge = raw39929 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39929Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39929 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 481).leftCharge (GramAssembly.key 481).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow481, Integer.Sparse.eval]

theorem keyMoment482 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 482) =
      Integer.Sparse.eval keyMomentRow482 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 482).leftCharge (GramAssembly.key 482).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 111) := by
    have ha : gramCharges (GramAssembly.key 482).leftCharge (GramAssembly.key 482).rightCharge = raw39930 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39930Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39930 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 482).leftCharge (GramAssembly.key 482).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow482, Integer.Sparse.eval]

theorem keyMoment483 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 483) =
      Integer.Sparse.eval keyMomentRow483 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 483).leftCharge (GramAssembly.key 483).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 405) := by
    have ha : gramCharges (GramAssembly.key 483).leftCharge (GramAssembly.key 483).rightCharge = raw39931 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39931Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39931 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 483).leftCharge (GramAssembly.key 483).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow483, Integer.Sparse.eval]

theorem keyMoment484 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 484) =
      Integer.Sparse.eval keyMomentRow484 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 484).leftCharge (GramAssembly.key 484).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 98) := by
    have ha : gramCharges (GramAssembly.key 484).leftCharge (GramAssembly.key 484).rightCharge = raw39932 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39932Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39932 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 484).leftCharge (GramAssembly.key 484).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow484, Integer.Sparse.eval]

theorem keyMoment485 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 485) =
      Integer.Sparse.eval keyMomentRow485 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 485).leftCharge (GramAssembly.key 485).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 343) := by
    have ha : gramCharges (GramAssembly.key 485).leftCharge (GramAssembly.key 485).rightCharge = raw39933 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39933Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39933 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 485).leftCharge (GramAssembly.key 485).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow485, Integer.Sparse.eval]

theorem keyMoment486 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 486) =
      Integer.Sparse.eval keyMomentRow486 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 486).leftCharge (GramAssembly.key 486).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 452) := by
    have ha : gramCharges (GramAssembly.key 486).leftCharge (GramAssembly.key 486).rightCharge = raw39934 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39934Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39934 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 486).leftCharge (GramAssembly.key 486).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow486, Integer.Sparse.eval]

theorem keyMoment487 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 487) =
      Integer.Sparse.eval keyMomentRow487 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 487).leftCharge (GramAssembly.key 487).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 71) := by
    have ha : gramCharges (GramAssembly.key 487).leftCharge (GramAssembly.key 487).rightCharge = raw39935 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39935Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39935 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 487).leftCharge (GramAssembly.key 487).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow487, Integer.Sparse.eval]

theorem keyMoment488 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 488) =
      Integer.Sparse.eval keyMomentRow488 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 488).leftCharge (GramAssembly.key 488).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 186) := by
    have ha : gramCharges (GramAssembly.key 488).leftCharge (GramAssembly.key 488).rightCharge = raw39936 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39936Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39936 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 488).leftCharge (GramAssembly.key 488).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow488, Integer.Sparse.eval]

theorem keyMoment489 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 489) =
      Integer.Sparse.eval keyMomentRow489 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 489).leftCharge (GramAssembly.key 489).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 95) := by
    have ha : gramCharges (GramAssembly.key 489).leftCharge (GramAssembly.key 489).rightCharge = raw39937 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39937Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39937 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 489).leftCharge (GramAssembly.key 489).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow489, Integer.Sparse.eval]

theorem keyMoment490 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 490) =
      Integer.Sparse.eval keyMomentRow490 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 490).leftCharge (GramAssembly.key 490).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 339) := by
    have ha : gramCharges (GramAssembly.key 490).leftCharge (GramAssembly.key 490).rightCharge = raw39938 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39938Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39938 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 490).leftCharge (GramAssembly.key 490).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow490, Integer.Sparse.eval]

theorem keyMoment491 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 491) =
      Integer.Sparse.eval keyMomentRow491 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 491).leftCharge (GramAssembly.key 491).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 68) := by
    have ha : gramCharges (GramAssembly.key 491).leftCharge (GramAssembly.key 491).rightCharge = raw39939 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39939Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39939 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 491).leftCharge (GramAssembly.key 491).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow491, Integer.Sparse.eval]

theorem keyMoment492 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 492) =
      Integer.Sparse.eval keyMomentRow492 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 492).leftCharge (GramAssembly.key 492).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 275) := by
    have ha : gramCharges (GramAssembly.key 492).leftCharge (GramAssembly.key 492).rightCharge = raw39940 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39940Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39940 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 492).leftCharge (GramAssembly.key 492).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow492, Integer.Sparse.eval]

theorem keyMoment493 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 493) =
      Integer.Sparse.eval keyMomentRow493 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 493).leftCharge (GramAssembly.key 493).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 65) := by
    have ha : gramCharges (GramAssembly.key 493).leftCharge (GramAssembly.key 493).rightCharge = raw39941 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39941Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39941 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 493).leftCharge (GramAssembly.key 493).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow493, Integer.Sparse.eval]

theorem keyMoment494 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 494) =
      Integer.Sparse.eval keyMomentRow494 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 494).leftCharge (GramAssembly.key 494).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 406) := by
    have ha : gramCharges (GramAssembly.key 494).leftCharge (GramAssembly.key 494).rightCharge = raw39942 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39942Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39942 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 494).leftCharge (GramAssembly.key 494).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow494, Integer.Sparse.eval]

theorem keyMoment495 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 495) =
      Integer.Sparse.eval keyMomentRow495 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 495).leftCharge (GramAssembly.key 495).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 354) := by
    have ha : gramCharges (GramAssembly.key 495).leftCharge (GramAssembly.key 495).rightCharge = raw39943 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39943Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39943 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 495).leftCharge (GramAssembly.key 495).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow495, Integer.Sparse.eval]

theorem keyMoment496 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 496) =
      Integer.Sparse.eval keyMomentRow496 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 496).leftCharge (GramAssembly.key 496).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 328) := by
    have ha : gramCharges (GramAssembly.key 496).leftCharge (GramAssembly.key 496).rightCharge = raw39944 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39944Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39944 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 496).leftCharge (GramAssembly.key 496).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow496, Integer.Sparse.eval]

theorem keyMoment497 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 497) =
      Integer.Sparse.eval keyMomentRow497 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 497).leftCharge (GramAssembly.key 497).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 409) := by
    have ha : gramCharges (GramAssembly.key 497).leftCharge (GramAssembly.key 497).rightCharge = raw39945 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39945Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39945 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 497).leftCharge (GramAssembly.key 497).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow497, Integer.Sparse.eval]

theorem keyMoment498 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 498) =
      Integer.Sparse.eval keyMomentRow498 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 498).leftCharge (GramAssembly.key 498).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 348) := by
    have ha : gramCharges (GramAssembly.key 498).leftCharge (GramAssembly.key 498).rightCharge = raw39946 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39946Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39946 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 498).leftCharge (GramAssembly.key 498).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow498, Integer.Sparse.eval]

theorem keyMoment499 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 499) =
      Integer.Sparse.eval keyMomentRow499 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 499).leftCharge (GramAssembly.key 499).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 347) := by
    have ha : gramCharges (GramAssembly.key 499).leftCharge (GramAssembly.key 499).rightCharge = raw39947 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39947Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39947 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 499).leftCharge (GramAssembly.key 499).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow499, Integer.Sparse.eval]

theorem keyMoment500 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 500) =
      Integer.Sparse.eval keyMomentRow500 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 500).leftCharge (GramAssembly.key 500).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 394) := by
    have ha : gramCharges (GramAssembly.key 500).leftCharge (GramAssembly.key 500).rightCharge = raw39948 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39948Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39948 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 500).leftCharge (GramAssembly.key 500).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow500, Integer.Sparse.eval]

theorem keyMoment501 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 501) =
      Integer.Sparse.eval keyMomentRow501 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 501).leftCharge (GramAssembly.key 501).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 410) := by
    have ha : gramCharges (GramAssembly.key 501).leftCharge (GramAssembly.key 501).rightCharge = raw39949 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39949Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39949 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 501).leftCharge (GramAssembly.key 501).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow501, Integer.Sparse.eval]

theorem keyMoment502 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 502) =
      Integer.Sparse.eval keyMomentRow502 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 502).leftCharge (GramAssembly.key 502).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 402) := by
    have ha : gramCharges (GramAssembly.key 502).leftCharge (GramAssembly.key 502).rightCharge = raw39950 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39950Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39950 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 502).leftCharge (GramAssembly.key 502).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow502, Integer.Sparse.eval]

theorem keyMoment503 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 503) =
      Integer.Sparse.eval keyMomentRow503 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 503).leftCharge (GramAssembly.key 503).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 350) := by
    have ha : gramCharges (GramAssembly.key 503).leftCharge (GramAssembly.key 503).rightCharge = raw39951 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39951Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39951 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 503).leftCharge (GramAssembly.key 503).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow503, Integer.Sparse.eval]

theorem keyMoment504 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 504) =
      Integer.Sparse.eval keyMomentRow504 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 504).leftCharge (GramAssembly.key 504).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 349) := by
    have ha : gramCharges (GramAssembly.key 504).leftCharge (GramAssembly.key 504).rightCharge = raw39952 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39952Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39952 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 504).leftCharge (GramAssembly.key 504).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow504, Integer.Sparse.eval]

theorem keyMoment505 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 505) =
      Integer.Sparse.eval keyMomentRow505 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 505).leftCharge (GramAssembly.key 505).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 395) := by
    have ha : gramCharges (GramAssembly.key 505).leftCharge (GramAssembly.key 505).rightCharge = raw39953 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39953Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39953 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 505).leftCharge (GramAssembly.key 505).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow505, Integer.Sparse.eval]

theorem keyMoment506 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 506) =
      Integer.Sparse.eval keyMomentRow506 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 506).leftCharge (GramAssembly.key 506).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 384) := by
    have ha : gramCharges (GramAssembly.key 506).leftCharge (GramAssembly.key 506).rightCharge = raw39954 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39954Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39954 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 506).leftCharge (GramAssembly.key 506).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow506, Integer.Sparse.eval]

theorem keyMoment507 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 507) =
      Integer.Sparse.eval keyMomentRow507 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 507).leftCharge (GramAssembly.key 507).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 346) := by
    have ha : gramCharges (GramAssembly.key 507).leftCharge (GramAssembly.key 507).rightCharge = raw39955 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39955Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39955 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 507).leftCharge (GramAssembly.key 507).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow507, Integer.Sparse.eval]

theorem keyMoment508 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 508) =
      Integer.Sparse.eval keyMomentRow508 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 508).leftCharge (GramAssembly.key 508).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 345) := by
    have ha : gramCharges (GramAssembly.key 508).leftCharge (GramAssembly.key 508).rightCharge = raw39956 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39956Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39956 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 508).leftCharge (GramAssembly.key 508).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow508, Integer.Sparse.eval]

theorem keyMoment509 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 509) =
      Integer.Sparse.eval keyMomentRow509 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 509).leftCharge (GramAssembly.key 509).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 373) := by
    have ha : gramCharges (GramAssembly.key 509).leftCharge (GramAssembly.key 509).rightCharge = raw39957 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39957Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39957 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 509).leftCharge (GramAssembly.key 509).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow509, Integer.Sparse.eval]

theorem keyMoment510 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 510) =
      Integer.Sparse.eval keyMomentRow510 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 510).leftCharge (GramAssembly.key 510).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 377) := by
    have ha : gramCharges (GramAssembly.key 510).leftCharge (GramAssembly.key 510).rightCharge = raw39958 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39958Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39958 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 510).leftCharge (GramAssembly.key 510).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow510, Integer.Sparse.eval]

theorem keyMoment511 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 511) =
      Integer.Sparse.eval keyMomentRow511 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 511).leftCharge (GramAssembly.key 511).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 385) := by
    have ha : gramCharges (GramAssembly.key 511).leftCharge (GramAssembly.key 511).rightCharge = raw39959 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39959Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39959 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 511).leftCharge (GramAssembly.key 511).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow511, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
