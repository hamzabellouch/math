import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical323
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical324

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2048 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2048) =
      Integer.Sparse.eval keyMomentRow2048 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2048).leftCharge (GramAssembly.key 2048).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 603) := by
    have ha : gramCharges (GramAssembly.key 2048).leftCharge (GramAssembly.key 2048).rightCharge = raw41461 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41461Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41461 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2048).leftCharge (GramAssembly.key 2048).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2048, Integer.Sparse.eval]

theorem keyMoment2049 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2049) =
      Integer.Sparse.eval keyMomentRow2049 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2049).leftCharge (GramAssembly.key 2049).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1041) := by
    have ha : gramCharges (GramAssembly.key 2049).leftCharge (GramAssembly.key 2049).rightCharge = raw41462 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41462Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41462 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2049).leftCharge (GramAssembly.key 2049).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2049, Integer.Sparse.eval]

theorem keyMoment2050 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2050) =
      Integer.Sparse.eval keyMomentRow2050 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2050).leftCharge (GramAssembly.key 2050).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2337) := by
    have ha : gramCharges (GramAssembly.key 2050).leftCharge (GramAssembly.key 2050).rightCharge = raw41463 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41463Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41463 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2050).leftCharge (GramAssembly.key 2050).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2050, Integer.Sparse.eval]

theorem keyMoment2051 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2051) =
      Integer.Sparse.eval keyMomentRow2051 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2051).leftCharge (GramAssembly.key 2051).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 922) := by
    have ha : gramCharges (GramAssembly.key 2051).leftCharge (GramAssembly.key 2051).rightCharge = raw41464 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41464Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41464 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2051).leftCharge (GramAssembly.key 2051).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2051, Integer.Sparse.eval]

theorem keyMoment2052 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2052) =
      Integer.Sparse.eval keyMomentRow2052 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2052).leftCharge (GramAssembly.key 2052).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2332) := by
    have ha : gramCharges (GramAssembly.key 2052).leftCharge (GramAssembly.key 2052).rightCharge = raw41465 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41465Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41465 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2052).leftCharge (GramAssembly.key 2052).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2052, Integer.Sparse.eval]

theorem keyMoment2053 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2053) =
      Integer.Sparse.eval keyMomentRow2053 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2053).leftCharge (GramAssembly.key 2053).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2109) := by
    have ha : gramCharges (GramAssembly.key 2053).leftCharge (GramAssembly.key 2053).rightCharge = raw41466 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41466Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41466 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2053).leftCharge (GramAssembly.key 2053).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2053, Integer.Sparse.eval]

theorem keyMoment2054 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2054) =
      Integer.Sparse.eval keyMomentRow2054 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2054).leftCharge (GramAssembly.key 2054).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1807) := by
    have ha : gramCharges (GramAssembly.key 2054).leftCharge (GramAssembly.key 2054).rightCharge = raw41467 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41467Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41467 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2054).leftCharge (GramAssembly.key 2054).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2054, Integer.Sparse.eval]

theorem keyMoment2055 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2055) =
      Integer.Sparse.eval keyMomentRow2055 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2055).leftCharge (GramAssembly.key 2055).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2022) := by
    have ha : gramCharges (GramAssembly.key 2055).leftCharge (GramAssembly.key 2055).rightCharge = raw41468 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41468Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41468 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2055).leftCharge (GramAssembly.key 2055).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2055, Integer.Sparse.eval]

theorem keyMoment2056 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2056) =
      Integer.Sparse.eval keyMomentRow2056 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2056).leftCharge (GramAssembly.key 2056).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2590) := by
    have ha : gramCharges (GramAssembly.key 2056).leftCharge (GramAssembly.key 2056).rightCharge = raw41469 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41469Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41469 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2056).leftCharge (GramAssembly.key 2056).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2056, Integer.Sparse.eval]

theorem keyMoment2057 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2057) =
      Integer.Sparse.eval keyMomentRow2057 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2057).leftCharge (GramAssembly.key 2057).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2431) := by
    have ha : gramCharges (GramAssembly.key 2057).leftCharge (GramAssembly.key 2057).rightCharge = raw41470 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41470Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41470 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2057).leftCharge (GramAssembly.key 2057).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2057, Integer.Sparse.eval]

theorem keyMoment2058 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2058) =
      Integer.Sparse.eval keyMomentRow2058 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2058).leftCharge (GramAssembly.key 2058).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2553) := by
    have ha : gramCharges (GramAssembly.key 2058).leftCharge (GramAssembly.key 2058).rightCharge = raw41471 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41471Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41471 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2058).leftCharge (GramAssembly.key 2058).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2058, Integer.Sparse.eval]

theorem keyMoment2059 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2059) =
      Integer.Sparse.eval keyMomentRow2059 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2059).leftCharge (GramAssembly.key 2059).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2434) := by
    have ha : gramCharges (GramAssembly.key 2059).leftCharge (GramAssembly.key 2059).rightCharge = raw41472 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41472Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41472 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2059).leftCharge (GramAssembly.key 2059).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2059, Integer.Sparse.eval]

theorem keyMoment2060 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2060) =
      Integer.Sparse.eval keyMomentRow2060 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2060).leftCharge (GramAssembly.key 2060).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2561) := by
    have ha : gramCharges (GramAssembly.key 2060).leftCharge (GramAssembly.key 2060).rightCharge = raw41473 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41473Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41473 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2060).leftCharge (GramAssembly.key 2060).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2060, Integer.Sparse.eval]

theorem keyMoment2061 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2061) =
      Integer.Sparse.eval keyMomentRow2061 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2061).leftCharge (GramAssembly.key 2061).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2428) := by
    have ha : gramCharges (GramAssembly.key 2061).leftCharge (GramAssembly.key 2061).rightCharge = raw41474 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41474Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41474 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2061).leftCharge (GramAssembly.key 2061).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2061, Integer.Sparse.eval]

theorem keyMoment2062 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2062) =
      Integer.Sparse.eval keyMomentRow2062 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2062).leftCharge (GramAssembly.key 2062).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2589) := by
    have ha : gramCharges (GramAssembly.key 2062).leftCharge (GramAssembly.key 2062).rightCharge = raw41475 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41475Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41475 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2062).leftCharge (GramAssembly.key 2062).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2062, Integer.Sparse.eval]

theorem keyMoment2063 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2063) =
      Integer.Sparse.eval keyMomentRow2063 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2063).leftCharge (GramAssembly.key 2063).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2429) := by
    have ha : gramCharges (GramAssembly.key 2063).leftCharge (GramAssembly.key 2063).rightCharge = raw41476 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41476Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41476 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2063).leftCharge (GramAssembly.key 2063).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2063, Integer.Sparse.eval]

theorem keyMoment2064 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2064) =
      Integer.Sparse.eval keyMomentRow2064 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2064).leftCharge (GramAssembly.key 2064).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1131) := by
    have ha : gramCharges (GramAssembly.key 2064).leftCharge (GramAssembly.key 2064).rightCharge = raw41477 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41477Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41477 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2064).leftCharge (GramAssembly.key 2064).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2064, Integer.Sparse.eval]

theorem keyMoment2065 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2065) =
      Integer.Sparse.eval keyMomentRow2065 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2065).leftCharge (GramAssembly.key 2065).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2482) := by
    have ha : gramCharges (GramAssembly.key 2065).leftCharge (GramAssembly.key 2065).rightCharge = raw41478 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41478Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41478 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2065).leftCharge (GramAssembly.key 2065).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2065, Integer.Sparse.eval]

theorem keyMoment2066 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2066) =
      Integer.Sparse.eval keyMomentRow2066 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2066).leftCharge (GramAssembly.key 2066).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2425) := by
    have ha : gramCharges (GramAssembly.key 2066).leftCharge (GramAssembly.key 2066).rightCharge = raw41479 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41479Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41479 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2066).leftCharge (GramAssembly.key 2066).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2066, Integer.Sparse.eval]

theorem keyMoment2067 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2067) =
      Integer.Sparse.eval keyMomentRow2067 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2067).leftCharge (GramAssembly.key 2067).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 605) := by
    have ha : gramCharges (GramAssembly.key 2067).leftCharge (GramAssembly.key 2067).rightCharge = raw41480 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41480Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41480 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2067).leftCharge (GramAssembly.key 2067).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2067, Integer.Sparse.eval]

theorem keyMoment2068 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2068) =
      Integer.Sparse.eval keyMomentRow2068 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2068).leftCharge (GramAssembly.key 2068).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 937) := by
    have ha : gramCharges (GramAssembly.key 2068).leftCharge (GramAssembly.key 2068).rightCharge = raw41481 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41481Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41481 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2068).leftCharge (GramAssembly.key 2068).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2068, Integer.Sparse.eval]

theorem keyMoment2069 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2069) =
      Integer.Sparse.eval keyMomentRow2069 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2069).leftCharge (GramAssembly.key 2069).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 932) := by
    have ha : gramCharges (GramAssembly.key 2069).leftCharge (GramAssembly.key 2069).rightCharge = raw41482 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41482Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41482 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2069).leftCharge (GramAssembly.key 2069).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2069, Integer.Sparse.eval]

theorem keyMoment2070 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2070) =
      Integer.Sparse.eval keyMomentRow2070 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2070).leftCharge (GramAssembly.key 2070).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 939) := by
    have ha : gramCharges (GramAssembly.key 2070).leftCharge (GramAssembly.key 2070).rightCharge = raw41483 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41483Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41483 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2070).leftCharge (GramAssembly.key 2070).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2070, Integer.Sparse.eval]

theorem keyMoment2071 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2071) =
      Integer.Sparse.eval keyMomentRow2071 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2071).leftCharge (GramAssembly.key 2071).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 929) := by
    have ha : gramCharges (GramAssembly.key 2071).leftCharge (GramAssembly.key 2071).rightCharge = raw41484 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41484Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41484 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2071).leftCharge (GramAssembly.key 2071).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2071, Integer.Sparse.eval]

theorem keyMoment2072 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2072) =
      Integer.Sparse.eval keyMomentRow2072 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2072).leftCharge (GramAssembly.key 2072).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 930) := by
    have ha : gramCharges (GramAssembly.key 2072).leftCharge (GramAssembly.key 2072).rightCharge = raw41485 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41485Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41485 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2072).leftCharge (GramAssembly.key 2072).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2072, Integer.Sparse.eval]

theorem keyMoment2073 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2073) =
      Integer.Sparse.eval keyMomentRow2073 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2073).leftCharge (GramAssembly.key 2073).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 934) := by
    have ha : gramCharges (GramAssembly.key 2073).leftCharge (GramAssembly.key 2073).rightCharge = raw41486 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41486Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41486 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2073).leftCharge (GramAssembly.key 2073).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2073, Integer.Sparse.eval]

theorem keyMoment2074 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2074) =
      Integer.Sparse.eval keyMomentRow2074 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2074).leftCharge (GramAssembly.key 2074).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2116) := by
    have ha : gramCharges (GramAssembly.key 2074).leftCharge (GramAssembly.key 2074).rightCharge = raw41487 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41487Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41487 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2074).leftCharge (GramAssembly.key 2074).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2074, Integer.Sparse.eval]

theorem keyMoment2075 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2075) =
      Integer.Sparse.eval keyMomentRow2075 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2075).leftCharge (GramAssembly.key 2075).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1815) := by
    have ha : gramCharges (GramAssembly.key 2075).leftCharge (GramAssembly.key 2075).rightCharge = raw41488 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41488Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41488 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2075).leftCharge (GramAssembly.key 2075).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2075, Integer.Sparse.eval]

theorem keyMoment2076 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2076) =
      Integer.Sparse.eval keyMomentRow2076 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2076).leftCharge (GramAssembly.key 2076).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2029) := by
    have ha : gramCharges (GramAssembly.key 2076).leftCharge (GramAssembly.key 2076).rightCharge = raw41489 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41489Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41489 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2076).leftCharge (GramAssembly.key 2076).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2076, Integer.Sparse.eval]

theorem keyMoment2077 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2077) =
      Integer.Sparse.eval keyMomentRow2077 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2077).leftCharge (GramAssembly.key 2077).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1967) := by
    have ha : gramCharges (GramAssembly.key 2077).leftCharge (GramAssembly.key 2077).rightCharge = raw41490 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41490Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41490 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2077).leftCharge (GramAssembly.key 2077).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2077, Integer.Sparse.eval]

theorem keyMoment2078 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2078) =
      Integer.Sparse.eval keyMomentRow2078 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2078).leftCharge (GramAssembly.key 2078).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3709) := by
    have ha : gramCharges (GramAssembly.key 2078).leftCharge (GramAssembly.key 2078).rightCharge = raw41491 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41491Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41491 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2078).leftCharge (GramAssembly.key 2078).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2078, Integer.Sparse.eval]

theorem keyMoment2079 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2079) =
      Integer.Sparse.eval keyMomentRow2079 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2079).leftCharge (GramAssembly.key 2079).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3779) := by
    have ha : gramCharges (GramAssembly.key 2079).leftCharge (GramAssembly.key 2079).rightCharge = raw41492 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41492Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41492 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2079).leftCharge (GramAssembly.key 2079).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2079, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
