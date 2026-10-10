import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical324

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2080 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2080) =
      Integer.Sparse.eval keyMomentRow2080 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2080).leftCharge (GramAssembly.key 2080).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2818) := by
    have ha : gramCharges (GramAssembly.key 2080).leftCharge (GramAssembly.key 2080).rightCharge = raw41493 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41493Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41493 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2080).leftCharge (GramAssembly.key 2080).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2080, Integer.Sparse.eval]

theorem keyMoment2081 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2081) =
      Integer.Sparse.eval keyMomentRow2081 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2081).leftCharge (GramAssembly.key 2081).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3694) := by
    have ha : gramCharges (GramAssembly.key 2081).leftCharge (GramAssembly.key 2081).rightCharge = raw41494 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41494Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41494 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2081).leftCharge (GramAssembly.key 2081).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2081, Integer.Sparse.eval]

theorem keyMoment2082 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2082) =
      Integer.Sparse.eval keyMomentRow2082 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2082).leftCharge (GramAssembly.key 2082).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3672) := by
    have ha : gramCharges (GramAssembly.key 2082).leftCharge (GramAssembly.key 2082).rightCharge = raw41495 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41495Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41495 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2082).leftCharge (GramAssembly.key 2082).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2082, Integer.Sparse.eval]

theorem keyMoment2083 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2083) =
      Integer.Sparse.eval keyMomentRow2083 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2083).leftCharge (GramAssembly.key 2083).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1139) := by
    have ha : gramCharges (GramAssembly.key 2083).leftCharge (GramAssembly.key 2083).rightCharge = raw41496 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41496Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41496 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2083).leftCharge (GramAssembly.key 2083).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2083, Integer.Sparse.eval]

theorem keyMoment2084 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2084) =
      Integer.Sparse.eval keyMomentRow2084 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2084).leftCharge (GramAssembly.key 2084).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2489) := by
    have ha : gramCharges (GramAssembly.key 2084).leftCharge (GramAssembly.key 2084).rightCharge = raw41497 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41497Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41497 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2084).leftCharge (GramAssembly.key 2084).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2084, Integer.Sparse.eval]

theorem keyMoment2085 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2085) =
      Integer.Sparse.eval keyMomentRow2085 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2085).leftCharge (GramAssembly.key 2085).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2432) := by
    have ha : gramCharges (GramAssembly.key 2085).leftCharge (GramAssembly.key 2085).rightCharge = raw41498 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41498Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41498 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2085).leftCharge (GramAssembly.key 2085).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2085, Integer.Sparse.eval]

theorem keyMoment2086 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2086) =
      Integer.Sparse.eval keyMomentRow2086 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2086).leftCharge (GramAssembly.key 2086).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 614) := by
    have ha : gramCharges (GramAssembly.key 2086).leftCharge (GramAssembly.key 2086).rightCharge = raw41499 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41499Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41499 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2086).leftCharge (GramAssembly.key 2086).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2086, Integer.Sparse.eval]

theorem keyMoment2087 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2087) =
      Integer.Sparse.eval keyMomentRow2087 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2087).leftCharge (GramAssembly.key 2087).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1050) := by
    have ha : gramCharges (GramAssembly.key 2087).leftCharge (GramAssembly.key 2087).rightCharge = raw41500 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41500Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41500 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2087).leftCharge (GramAssembly.key 2087).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2087, Integer.Sparse.eval]

theorem keyMoment2088 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2088) =
      Integer.Sparse.eval keyMomentRow2088 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2088).leftCharge (GramAssembly.key 2088).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 933) := by
    have ha : gramCharges (GramAssembly.key 2088).leftCharge (GramAssembly.key 2088).rightCharge = raw41501 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41501Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41501 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2088).leftCharge (GramAssembly.key 2088).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2088, Integer.Sparse.eval]

theorem keyMoment2089 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2089) =
      Integer.Sparse.eval keyMomentRow2089 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2089).leftCharge (GramAssembly.key 2089).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2342) := by
    have ha : gramCharges (GramAssembly.key 2089).leftCharge (GramAssembly.key 2089).rightCharge = raw41502 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41502Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41502 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2089).leftCharge (GramAssembly.key 2089).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2089, Integer.Sparse.eval]

theorem keyMoment2090 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2090) =
      Integer.Sparse.eval keyMomentRow2090 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2090).leftCharge (GramAssembly.key 2090).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1818) := by
    have ha : gramCharges (GramAssembly.key 2090).leftCharge (GramAssembly.key 2090).rightCharge = raw41503 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41503Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41503 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2090).leftCharge (GramAssembly.key 2090).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2090, Integer.Sparse.eval]

theorem keyMoment2091 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2091) =
      Integer.Sparse.eval keyMomentRow2091 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2091).leftCharge (GramAssembly.key 2091).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2341) := by
    have ha : gramCharges (GramAssembly.key 2091).leftCharge (GramAssembly.key 2091).rightCharge = raw41504 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41504Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41504 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2091).leftCharge (GramAssembly.key 2091).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2091, Integer.Sparse.eval]

theorem keyMoment2092 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2092) =
      Integer.Sparse.eval keyMomentRow2092 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2092).leftCharge (GramAssembly.key 2092).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2330) := by
    have ha : gramCharges (GramAssembly.key 2092).leftCharge (GramAssembly.key 2092).rightCharge = raw41505 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41505Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41505 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2092).leftCharge (GramAssembly.key 2092).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2092, Integer.Sparse.eval]

theorem keyMoment2093 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2093) =
      Integer.Sparse.eval keyMomentRow2093 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2093).leftCharge (GramAssembly.key 2093).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2345) := by
    have ha : gramCharges (GramAssembly.key 2093).leftCharge (GramAssembly.key 2093).rightCharge = raw41506 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41506Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41506 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2093).leftCharge (GramAssembly.key 2093).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2093, Integer.Sparse.eval]

theorem keyMoment2094 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2094) =
      Integer.Sparse.eval keyMomentRow2094 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2094).leftCharge (GramAssembly.key 2094).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2337) := by
    have ha : gramCharges (GramAssembly.key 2094).leftCharge (GramAssembly.key 2094).rightCharge = raw41507 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41507Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41507 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2094).leftCharge (GramAssembly.key 2094).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2094, Integer.Sparse.eval]

theorem keyMoment2095 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2095) =
      Integer.Sparse.eval keyMomentRow2095 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2095).leftCharge (GramAssembly.key 2095).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2338) := by
    have ha : gramCharges (GramAssembly.key 2095).leftCharge (GramAssembly.key 2095).rightCharge = raw41508 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41508Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41508 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2095).leftCharge (GramAssembly.key 2095).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2095, Integer.Sparse.eval]

theorem keyMoment2096 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2096) =
      Integer.Sparse.eval keyMomentRow2096 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2096).leftCharge (GramAssembly.key 2096).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2339) := by
    have ha : gramCharges (GramAssembly.key 2096).leftCharge (GramAssembly.key 2096).rightCharge = raw41509 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41509Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41509 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2096).leftCharge (GramAssembly.key 2096).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2096, Integer.Sparse.eval]

theorem keyMoment2097 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2097) =
      Integer.Sparse.eval keyMomentRow2097 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2097).leftCharge (GramAssembly.key 2097).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1144) := by
    have ha : gramCharges (GramAssembly.key 2097).leftCharge (GramAssembly.key 2097).rightCharge = raw41510 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41510Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41510 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2097).leftCharge (GramAssembly.key 2097).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2097, Integer.Sparse.eval]

theorem keyMoment2098 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2098) =
      Integer.Sparse.eval keyMomentRow2098 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2098).leftCharge (GramAssembly.key 2098).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2334) := by
    have ha : gramCharges (GramAssembly.key 2098).leftCharge (GramAssembly.key 2098).rightCharge = raw41511 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41511Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41511 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2098).leftCharge (GramAssembly.key 2098).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2098, Integer.Sparse.eval]

theorem keyMoment2099 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2099) =
      Integer.Sparse.eval keyMomentRow2099 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2099).leftCharge (GramAssembly.key 2099).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 619) := by
    have ha : gramCharges (GramAssembly.key 2099).leftCharge (GramAssembly.key 2099).rightCharge = raw41512 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41512Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41512 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2099).leftCharge (GramAssembly.key 2099).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2099, Integer.Sparse.eval]

theorem keyMoment2100 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2100) =
      Integer.Sparse.eval keyMomentRow2100 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2100).leftCharge (GramAssembly.key 2100).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2344) := by
    have ha : gramCharges (GramAssembly.key 2100).leftCharge (GramAssembly.key 2100).rightCharge = raw41513 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41513Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41513 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2100).leftCharge (GramAssembly.key 2100).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2100, Integer.Sparse.eval]

theorem keyMoment2101 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2101) =
      Integer.Sparse.eval keyMomentRow2101 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2101).leftCharge (GramAssembly.key 2101).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2) := by
    have ha : gramCharges (GramAssembly.key 2101).leftCharge (GramAssembly.key 2101).rightCharge = raw41514 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41514Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41514 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2101).leftCharge (GramAssembly.key 2101).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4085) := by
    have ha : gramCharges (GramAssembly.key 2101).leftCharge (GramAssembly.key 2101).rightCharge = raw41515 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41515Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41515 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2101).leftCharge (GramAssembly.key 2101).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2101).leftCharge (GramAssembly.key 2101).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2101, Integer.Sparse.eval]
  ring

theorem keyMoment2102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2102) =
      Integer.Sparse.eval keyMomentRow2102 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2102).leftCharge (GramAssembly.key 2102).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3114) := by
    have ha : gramCharges (GramAssembly.key 2102).leftCharge (GramAssembly.key 2102).rightCharge = raw41516 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41516Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41516 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2102).leftCharge (GramAssembly.key 2102).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4897) := by
    have ha : gramCharges (GramAssembly.key 2102).leftCharge (GramAssembly.key 2102).rightCharge = raw41517 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41517Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41517 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2102).leftCharge (GramAssembly.key 2102).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2102).leftCharge (GramAssembly.key 2102).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2102, Integer.Sparse.eval]
  ring

theorem keyMoment2103 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2103) =
      Integer.Sparse.eval keyMomentRow2103 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2103).leftCharge (GramAssembly.key 2103).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1) := by
    have ha : gramCharges (GramAssembly.key 2103).leftCharge (GramAssembly.key 2103).rightCharge = raw41518 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41518Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41518 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2103).leftCharge (GramAssembly.key 2103).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4084) := by
    have ha : gramCharges (GramAssembly.key 2103).leftCharge (GramAssembly.key 2103).rightCharge = raw41519 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41519Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41519 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2103).leftCharge (GramAssembly.key 2103).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2103).leftCharge (GramAssembly.key 2103).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2103, Integer.Sparse.eval]
  ring

theorem keyMoment2104 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2104) =
      Integer.Sparse.eval keyMomentRow2104 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2104).leftCharge (GramAssembly.key 2104).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3231) := by
    have ha : gramCharges (GramAssembly.key 2104).leftCharge (GramAssembly.key 2104).rightCharge = raw41520 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41520Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41520 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2104).leftCharge (GramAssembly.key 2104).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4901) := by
    have ha : gramCharges (GramAssembly.key 2104).leftCharge (GramAssembly.key 2104).rightCharge = raw41521 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41521Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41521 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2104).leftCharge (GramAssembly.key 2104).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2104).leftCharge (GramAssembly.key 2104).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2104, Integer.Sparse.eval]
  ring

theorem keyMoment2105 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2105) =
      Integer.Sparse.eval keyMomentRow2105 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2105).leftCharge (GramAssembly.key 2105).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2778) := by
    have ha : gramCharges (GramAssembly.key 2105).leftCharge (GramAssembly.key 2105).rightCharge = raw41522 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41522Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41522 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2105).leftCharge (GramAssembly.key 2105).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4899) := by
    have ha : gramCharges (GramAssembly.key 2105).leftCharge (GramAssembly.key 2105).rightCharge = raw41523 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41523Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41523 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2105).leftCharge (GramAssembly.key 2105).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2105).leftCharge (GramAssembly.key 2105).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2105, Integer.Sparse.eval]
  ring

theorem keyMoment2106 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2106) =
      Integer.Sparse.eval keyMomentRow2106 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2106).leftCharge (GramAssembly.key 2106).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3230) := by
    have ha : gramCharges (GramAssembly.key 2106).leftCharge (GramAssembly.key 2106).rightCharge = raw41524 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41524Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41524 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2106).leftCharge (GramAssembly.key 2106).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4894) := by
    have ha : gramCharges (GramAssembly.key 2106).leftCharge (GramAssembly.key 2106).rightCharge = raw41525 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41525Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41525 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2106).leftCharge (GramAssembly.key 2106).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2106).leftCharge (GramAssembly.key 2106).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2106, Integer.Sparse.eval]
  ring

theorem keyMoment2107 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2107) =
      Integer.Sparse.eval keyMomentRow2107 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2107).leftCharge (GramAssembly.key 2107).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3229) := by
    have ha : gramCharges (GramAssembly.key 2107).leftCharge (GramAssembly.key 2107).rightCharge = raw41526 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41526Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41526 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2107).leftCharge (GramAssembly.key 2107).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4895) := by
    have ha : gramCharges (GramAssembly.key 2107).leftCharge (GramAssembly.key 2107).rightCharge = raw41527 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41527Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41527 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2107).leftCharge (GramAssembly.key 2107).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2107).leftCharge (GramAssembly.key 2107).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2107, Integer.Sparse.eval]
  ring

theorem keyMoment2108 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2108) =
      Integer.Sparse.eval keyMomentRow2108 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2108).leftCharge (GramAssembly.key 2108).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3225) := by
    have ha : gramCharges (GramAssembly.key 2108).leftCharge (GramAssembly.key 2108).rightCharge = raw41528 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41528Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41528 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2108).leftCharge (GramAssembly.key 2108).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4896) := by
    have ha : gramCharges (GramAssembly.key 2108).leftCharge (GramAssembly.key 2108).rightCharge = raw41529 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41529Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41529 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2108).leftCharge (GramAssembly.key 2108).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2108).leftCharge (GramAssembly.key 2108).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2108, Integer.Sparse.eval]
  ring

theorem keyMoment2109 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2109) =
      Integer.Sparse.eval keyMomentRow2109 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2109).leftCharge (GramAssembly.key 2109).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3224) := by
    have ha : gramCharges (GramAssembly.key 2109).leftCharge (GramAssembly.key 2109).rightCharge = raw41530 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41530Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41530 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2109).leftCharge (GramAssembly.key 2109).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4898) := by
    have ha : gramCharges (GramAssembly.key 2109).leftCharge (GramAssembly.key 2109).rightCharge = raw41531 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41531Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41531 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2109).leftCharge (GramAssembly.key 2109).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2109).leftCharge (GramAssembly.key 2109).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2109, Integer.Sparse.eval]
  ring

theorem keyMoment2110 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2110) =
      Integer.Sparse.eval keyMomentRow2110 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2110).leftCharge (GramAssembly.key 2110).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2755) := by
    have ha : gramCharges (GramAssembly.key 2110).leftCharge (GramAssembly.key 2110).rightCharge = raw41532 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41532Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41532 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2110).leftCharge (GramAssembly.key 2110).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4890) := by
    have ha : gramCharges (GramAssembly.key 2110).leftCharge (GramAssembly.key 2110).rightCharge = raw41533 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41533Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41533 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2110).leftCharge (GramAssembly.key 2110).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2110).leftCharge (GramAssembly.key 2110).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2110, Integer.Sparse.eval]
  ring

theorem keyMoment2111 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2111) =
      Integer.Sparse.eval keyMomentRow2111 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2111).leftCharge (GramAssembly.key 2111).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3229) := by
    have ha : gramCharges (GramAssembly.key 2111).leftCharge (GramAssembly.key 2111).rightCharge = raw41534 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41534Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41534 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2111).leftCharge (GramAssembly.key 2111).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4895) := by
    have ha : gramCharges (GramAssembly.key 2111).leftCharge (GramAssembly.key 2111).rightCharge = raw41535 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41535Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41535 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2111).leftCharge (GramAssembly.key 2111).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2111).leftCharge (GramAssembly.key 2111).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2111, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
