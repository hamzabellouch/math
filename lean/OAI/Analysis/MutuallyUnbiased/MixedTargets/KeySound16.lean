import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical312

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment512 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 512) =
      Integer.Sparse.eval keyMomentRow512 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 512).leftCharge (GramAssembly.key 512).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 379) := by
    have ha : gramCharges (GramAssembly.key 512).leftCharge (GramAssembly.key 512).rightCharge = raw39960 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39960Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39960 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 512).leftCharge (GramAssembly.key 512).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow512, Integer.Sparse.eval]

theorem keyMoment513 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 513) =
      Integer.Sparse.eval keyMomentRow513 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 513).leftCharge (GramAssembly.key 513).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 147) := by
    have ha : gramCharges (GramAssembly.key 513).leftCharge (GramAssembly.key 513).rightCharge = raw39961 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39961Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39961 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 513).leftCharge (GramAssembly.key 513).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow513, Integer.Sparse.eval]

theorem keyMoment514 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 514) =
      Integer.Sparse.eval keyMomentRow514 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 514).leftCharge (GramAssembly.key 514).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 323) := by
    have ha : gramCharges (GramAssembly.key 514).leftCharge (GramAssembly.key 514).rightCharge = raw39962 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39962Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39962 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 514).leftCharge (GramAssembly.key 514).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow514, Integer.Sparse.eval]

theorem keyMoment515 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 515) =
      Integer.Sparse.eval keyMomentRow515 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 515).leftCharge (GramAssembly.key 515).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 374) := by
    have ha : gramCharges (GramAssembly.key 515).leftCharge (GramAssembly.key 515).rightCharge = raw39963 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39963Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39963 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 515).leftCharge (GramAssembly.key 515).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow515, Integer.Sparse.eval]

theorem keyMoment516 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 516) =
      Integer.Sparse.eval keyMomentRow516 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 516).leftCharge (GramAssembly.key 516).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 1) := by
    have ha : gramCharges (GramAssembly.key 516).leftCharge (GramAssembly.key 516).rightCharge = raw39964 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39964Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39964 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 516).leftCharge (GramAssembly.key 516).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow516, Integer.Sparse.eval]

theorem keyMoment517 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 517) =
      Integer.Sparse.eval keyMomentRow517 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 517).leftCharge (GramAssembly.key 517).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 239) := by
    have ha : gramCharges (GramAssembly.key 517).leftCharge (GramAssembly.key 517).rightCharge = raw39965 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39965Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39965 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 517).leftCharge (GramAssembly.key 517).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow517, Integer.Sparse.eval]

theorem keyMoment518 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 518) =
      Integer.Sparse.eval keyMomentRow518 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 518).leftCharge (GramAssembly.key 518).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 176) := by
    have ha : gramCharges (GramAssembly.key 518).leftCharge (GramAssembly.key 518).rightCharge = raw39966 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39966Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39966 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 518).leftCharge (GramAssembly.key 518).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow518, Integer.Sparse.eval]

theorem keyMoment519 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 519) =
      Integer.Sparse.eval keyMomentRow519 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 519).leftCharge (GramAssembly.key 519).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 164) := by
    have ha : gramCharges (GramAssembly.key 519).leftCharge (GramAssembly.key 519).rightCharge = raw39967 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39967Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39967 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 519).leftCharge (GramAssembly.key 519).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow519, Integer.Sparse.eval]

theorem keyMoment520 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 520) =
      Integer.Sparse.eval keyMomentRow520 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 520).leftCharge (GramAssembly.key 520).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 6) := by
    have ha : gramCharges (GramAssembly.key 520).leftCharge (GramAssembly.key 520).rightCharge = raw39968 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39968Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39968 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 520).leftCharge (GramAssembly.key 520).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow520, Integer.Sparse.eval]

theorem keyMoment521 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 521) =
      Integer.Sparse.eval keyMomentRow521 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 521).leftCharge (GramAssembly.key 521).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 297) := by
    have ha : gramCharges (GramAssembly.key 521).leftCharge (GramAssembly.key 521).rightCharge = raw39969 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39969Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39969 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 521).leftCharge (GramAssembly.key 521).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow521, Integer.Sparse.eval]

theorem keyMoment522 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 522) =
      Integer.Sparse.eval keyMomentRow522 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 522).leftCharge (GramAssembly.key 522).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 309) := by
    have ha : gramCharges (GramAssembly.key 522).leftCharge (GramAssembly.key 522).rightCharge = raw39970 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39970Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39970 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 522).leftCharge (GramAssembly.key 522).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow522, Integer.Sparse.eval]

theorem keyMoment523 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 523) =
      Integer.Sparse.eval keyMomentRow523 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 523).leftCharge (GramAssembly.key 523).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 306) := by
    have ha : gramCharges (GramAssembly.key 523).leftCharge (GramAssembly.key 523).rightCharge = raw39971 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39971Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39971 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 523).leftCharge (GramAssembly.key 523).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow523, Integer.Sparse.eval]

theorem keyMoment524 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 524) =
      Integer.Sparse.eval keyMomentRow524 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 524).leftCharge (GramAssembly.key 524).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 281) := by
    have ha : gramCharges (GramAssembly.key 524).leftCharge (GramAssembly.key 524).rightCharge = raw39972 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39972Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39972 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 524).leftCharge (GramAssembly.key 524).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow524, Integer.Sparse.eval]

theorem keyMoment525 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 525) =
      Integer.Sparse.eval keyMomentRow525 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 525).leftCharge (GramAssembly.key 525).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 298) := by
    have ha : gramCharges (GramAssembly.key 525).leftCharge (GramAssembly.key 525).rightCharge = raw39973 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39973Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39973 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 525).leftCharge (GramAssembly.key 525).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow525, Integer.Sparse.eval]

theorem keyMoment526 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 526) =
      Integer.Sparse.eval keyMomentRow526 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 526).leftCharge (GramAssembly.key 526).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 300) := by
    have ha : gramCharges (GramAssembly.key 526).leftCharge (GramAssembly.key 526).rightCharge = raw39974 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39974Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39974 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 526).leftCharge (GramAssembly.key 526).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow526, Integer.Sparse.eval]

theorem keyMoment527 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 527) =
      Integer.Sparse.eval keyMomentRow527 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 527).leftCharge (GramAssembly.key 527).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 301) := by
    have ha : gramCharges (GramAssembly.key 527).leftCharge (GramAssembly.key 527).rightCharge = raw39975 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39975Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39975 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 527).leftCharge (GramAssembly.key 527).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow527, Integer.Sparse.eval]

theorem keyMoment528 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 528) =
      Integer.Sparse.eval keyMomentRow528 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 528).leftCharge (GramAssembly.key 528).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 308) := by
    have ha : gramCharges (GramAssembly.key 528).leftCharge (GramAssembly.key 528).rightCharge = raw39976 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39976Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39976 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 528).leftCharge (GramAssembly.key 528).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow528, Integer.Sparse.eval]

theorem keyMoment529 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 529) =
      Integer.Sparse.eval keyMomentRow529 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 529).leftCharge (GramAssembly.key 529).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 303) := by
    have ha : gramCharges (GramAssembly.key 529).leftCharge (GramAssembly.key 529).rightCharge = raw39977 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39977Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39977 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 529).leftCharge (GramAssembly.key 529).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow529, Integer.Sparse.eval]

theorem keyMoment530 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 530) =
      Integer.Sparse.eval keyMomentRow530 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 530).leftCharge (GramAssembly.key 530).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 122) := by
    have ha : gramCharges (GramAssembly.key 530).leftCharge (GramAssembly.key 530).rightCharge = raw39978 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39978Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39978 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 530).leftCharge (GramAssembly.key 530).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow530, Integer.Sparse.eval]

theorem keyMoment531 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 531) =
      Integer.Sparse.eval keyMomentRow531 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 531).leftCharge (GramAssembly.key 531).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 292) := by
    have ha : gramCharges (GramAssembly.key 531).leftCharge (GramAssembly.key 531).rightCharge = raw39979 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39979Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39979 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 531).leftCharge (GramAssembly.key 531).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow531, Integer.Sparse.eval]

theorem keyMoment532 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 532) =
      Integer.Sparse.eval keyMomentRow532 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 532).leftCharge (GramAssembly.key 532).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 299) := by
    have ha : gramCharges (GramAssembly.key 532).leftCharge (GramAssembly.key 532).rightCharge = raw39980 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39980Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39980 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 532).leftCharge (GramAssembly.key 532).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow532, Integer.Sparse.eval]

theorem keyMoment533 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 533) =
      Integer.Sparse.eval keyMomentRow533 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 533).leftCharge (GramAssembly.key 533).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 2) := by
    have ha : gramCharges (GramAssembly.key 533).leftCharge (GramAssembly.key 533).rightCharge = raw39981 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39981Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39981 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 533).leftCharge (GramAssembly.key 533).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow533, Integer.Sparse.eval]

theorem keyMoment534 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 534) =
      Integer.Sparse.eval keyMomentRow534 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 534).leftCharge (GramAssembly.key 534).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 146) := by
    have ha : gramCharges (GramAssembly.key 534).leftCharge (GramAssembly.key 534).rightCharge = raw39982 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39982Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39982 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 534).leftCharge (GramAssembly.key 534).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow534, Integer.Sparse.eval]

theorem keyMoment535 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 535) =
      Integer.Sparse.eval keyMomentRow535 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 535).leftCharge (GramAssembly.key 535).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 11) := by
    have ha : gramCharges (GramAssembly.key 535).leftCharge (GramAssembly.key 535).rightCharge = raw39983 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39983Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39983 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 535).leftCharge (GramAssembly.key 535).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow535, Integer.Sparse.eval]

theorem keyMoment536 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 536) =
      Integer.Sparse.eval keyMomentRow536 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 536).leftCharge (GramAssembly.key 536).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 169) := by
    have ha : gramCharges (GramAssembly.key 536).leftCharge (GramAssembly.key 536).rightCharge = raw39984 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39984Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39984 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 536).leftCharge (GramAssembly.key 536).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow536, Integer.Sparse.eval]

theorem keyMoment537 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 537) =
      Integer.Sparse.eval keyMomentRow537 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 537).leftCharge (GramAssembly.key 537).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 18) := by
    have ha : gramCharges (GramAssembly.key 537).leftCharge (GramAssembly.key 537).rightCharge = raw39985 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39985Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39985 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 537).leftCharge (GramAssembly.key 537).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow537, Integer.Sparse.eval]

theorem keyMoment538 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 538) =
      Integer.Sparse.eval keyMomentRow538 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 538).leftCharge (GramAssembly.key 538).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 270) := by
    have ha : gramCharges (GramAssembly.key 538).leftCharge (GramAssembly.key 538).rightCharge = raw39986 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39986Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39986 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 538).leftCharge (GramAssembly.key 538).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow538, Integer.Sparse.eval]

theorem keyMoment539 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 539) =
      Integer.Sparse.eval keyMomentRow539 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 539).leftCharge (GramAssembly.key 539).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 249) := by
    have ha : gramCharges (GramAssembly.key 539).leftCharge (GramAssembly.key 539).rightCharge = raw39987 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39987Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39987 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 539).leftCharge (GramAssembly.key 539).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow539, Integer.Sparse.eval]

theorem keyMoment540 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 540) =
      Integer.Sparse.eval keyMomentRow540 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 540).leftCharge (GramAssembly.key 540).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 187) := by
    have ha : gramCharges (GramAssembly.key 540).leftCharge (GramAssembly.key 540).rightCharge = raw39988 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39988Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39988 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 540).leftCharge (GramAssembly.key 540).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow540, Integer.Sparse.eval]

theorem keyMoment541 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 541) =
      Integer.Sparse.eval keyMomentRow541 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 541).leftCharge (GramAssembly.key 541).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 236) := by
    have ha : gramCharges (GramAssembly.key 541).leftCharge (GramAssembly.key 541).rightCharge = raw39989 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39989Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39989 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 541).leftCharge (GramAssembly.key 541).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow541, Integer.Sparse.eval]

theorem keyMoment542 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 542) =
      Integer.Sparse.eval keyMomentRow542 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 542).leftCharge (GramAssembly.key 542).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 262) := by
    have ha : gramCharges (GramAssembly.key 542).leftCharge (GramAssembly.key 542).rightCharge = raw39990 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39990Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39990 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 542).leftCharge (GramAssembly.key 542).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow542, Integer.Sparse.eval]

theorem keyMoment543 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 543) =
      Integer.Sparse.eval keyMomentRow543 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 543).leftCharge (GramAssembly.key 543).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 180) := by
    have ha : gramCharges (GramAssembly.key 543).leftCharge (GramAssembly.key 543).rightCharge = raw39991 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39991Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39991 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 543).leftCharge (GramAssembly.key 543).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow543, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
